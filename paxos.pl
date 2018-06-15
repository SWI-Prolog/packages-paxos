/*  Part of SWI-Prolog

    Author:        Jeffrey Rosenwald, Jan Wielemaker
    E-mail:        jeffrose@acm.org
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2009-2018, Jeffrey Rosenwald
                   CWI, Amsterdam
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(paxos,
          [ paxos_get/1,                        % ?Term
            paxos_get/2,                        % +Key, -Value
            paxos_get/3,                        % +Key, -Value, +Options
            paxos_set/1,                        % ?Term
            paxos_set/2,                        % +Key, +Value
            paxos_set/3,                        % +Key, +Value, +Options
            paxos_on_change/2,                  % ?Term, +Goal
            paxos_on_change/3,                  % ?Key, ?Value, +Goal

            paxos_initialize/1,			% +Options
                                                % Hook support
            paxos_replicate_key/3               % +Nodes, ?Key, +Options
          ]).
:- use_module(library(broadcast)).
:- use_module(library(debug)).
:- use_module(library(lists)).
:- use_module(library(settings)).
:- use_module(library(option)).
:- use_module(library(error)).
:- use_module(library(solution_sequences)).

/** <module> A Replicated Data Store

This module provides a replicated data store that is coordinated using a
variation on Lamport's Paxos concensus protocol.  The original method is
described in his paper entitled, "The   Part-time Parliament", which was
published in 1998. The algorithm is   tolerant of non-Byzantine failure.
That is late or lost delivery or   reply,  but not senseless delivery or
reply. The present algorithm takes advantage  of the convenience offered
by multicast to the quorum's membership,   who  can remain anonymous and
who can come and go as they  please without effecting Liveness or Safety
properties.

Paxos' quorum is a set of one or more attentive members, whose processes
respond to queries within some known time limit (< 20ms), which includes
roundtrip delivery delay. This property is   easy  to satisfy given that
every coordinator is necessarily a member of   the quorum as well, and a
quorum of one is  permitted.  An   inattentive  member  (e.g.  one whose
actions are late or lost) is deemed to be "not-present" for the purposes
of the present transaction and consistency   cannot  be assured for that
member. As long as there is at least one attentive member of the quorum,
then persistence of the database is assured.

Each member maintains a ledger  of   terms  along with information about
when  they  were   originally   recorded.    The   member's   ledger  is
deterministic. That is to say  that  there   can  only  be one entry per
functor/arity combination. No member will  accept   a  new term proposal
that has a line number that is equal-to   or  lower-than the one that is
already recorded in the ledger.

Paxos is a three-phase protocol:

   1: A coordinator first prepares the quorum for a new proposal by
   broadcasting a proposed term. The quorum responds by returning the
   last known line number for that functor/arity combination that is
   recorded in their respective ledgers.

   2: The coordinator selects the highest line number it receives,
   increments it by one, and then asks the quorum to finally accept the
   new term with the new line number. The quorum checks their respective
   ledgers once again and if there is still no other ledger entry for
   that functor/arity combination that is equal-to or higher than the
   specified line, then each member records the term in the ledger at
   the specified line. The member indicates consent by returning the
   specified line number back to the coordinator. If consent is withheld
   by a member, then the member returns a =nack= instead. The
   coordinator requires unanimous consent. If it isn't achieved then the
   proposal fails and the coordinator must start over from the
   beginning.

   3: Finally, the coordinator concludes the successful negotiation by
   broadcasting the agreement to the quorum in the form of a
   paxos(changed(Key,Value) event. This is the only event that
   should be of interest to user programs.

For practical reasons, we rely  on   the  partially synchronous behavior
(e.g. limited upper time bound for  replies) of broadcast_request/1 over
TIPC to ensure Progress. Perhaps more importantly,   we rely on the fact
that the TIPC broadcast listener state  machine guarantees the atomicity
of broadcast_request/1 at the process level, thus obviating the need for
external mutual exclusion mechanisms.

_|Note that this algorithm does not guarantee the rightness of the value
proposed. It only guarantees that if   successful, the value proposed is
identical for all attentive members of the quorum.|_

@author    Jeffrey Rosenwald (JeffRose@acm.org)
@license   BSD-2
@see       tipc_broadcast.pl, udp_broadcast.pl
*/

:- meta_predicate
    paxos_on_change(?, 0),
    paxos_on_change(?, ?, 0).

:- multifile
    paxos_message_hook/3,               % +PaxOS, +TimeOut, -Message
    node/1,                             % NodeID
    quorum/1.                           % Quorum bitmask

:- setting(max_sets, nonneg, 20,
           "Max Retries to get to an agreement").
:- setting(max_gets, nonneg, 5,
           "Max Retries to get a value from the forum").
:- setting(response_timeout, float, 0.020,
           "Max time to wait for a response").


%!  c_element(+NewList, +Old, -Value)
%
%   A Muller c-element is a logic block  used in asynchronous logic. Its
%   output assumes the value of its  input   iff  all  of its inputs are
%   identical. Otherwise, the output retains its original value.

c_element([New | More], _Old, New) :-
    forall(member(N, More), N == New),
    !.
c_element(_List, Old, Old).

%!  paxos_initialize(+Options) is det.
%
%   Initialize this Prolog process as a   paxos node. The initialization
%   requires an initialized and configured TIPC,  UDP or other broadcast
%   protocol. Calling this initialization may be  omitted, in which case
%   the equivant of paxos_initialize([]) is executed   lazily as part of
%   the first paxos operation.  Defined options:
%
%     - node(?NodeID)
%     When instantiated, this node rejoins the network with the given
%     node id. A fixed node idea should be used if the node is
%     configured for persistency and causes the new node to receive
%     updates for keys that have been created or modified since the
%     node left the network.  If NodeID is a variable it is unified
%     with the discovered NodeID.
%
%     NodeID must be a small non-negative integer as these identifiers
%     are used in bitmaps.

paxos_initialize(Options) :-
    option(node(Node), Options, Node),
    node(Node).

%!  paxos_initialize is det.
%
%   causes any required runtime initialization to occur. It is called as
%   a side-effect of initialize/0, which is now required as part of
%   an applications initialization directive.

:- dynamic  paxos_initialized/0.
:- volatile paxos_initialized/0.

paxos_initialize :-
    paxos_initialized,
    !.
paxos_initialize :-
    with_mutex(paxos, paxos_initialize_sync).

paxos_initialize_sync :-
    paxos_initialized,
    !.
paxos_initialize_sync :-
    listen(paxos, paxos(X), paxos_message(X)),
    node(_Node),
    asserta(paxos_initialized).


%!  paxos_message(?Message)
%
%   Handle inbound actions from our peers.   Defines  values for Message
%   are:
%
%     - prepare(+Key,-Node,-Gen,+Value)
%     A request message to set Key to Value. Returns the current
%     generation at which we have a value or `0` for Gen and the
%     our node id for Node.
%     - accept(+Key,-Node,+Gen,-GenA,+Value)
%     A request message to set Key to Value if Gen is newer than
%     the generation we have for Key.  In that case GenA is Gen.
%     Otherwise we reject using GenA = `nack`.
%     - changed(+Key,+Gen,+Value,+Acceptors)
%     The leader got enough accepts for setting Key to Value at Gen.
%     Acceptors is the set of nodes that accepted this value.
%     - learn(+Key,-Node,+Gen,-GenA,+Value)
%     Request message peforming phase one for replication to learner
%     nodes.
%     - learned(+Key,+Gen,+Value,+Acceptors)
%     Phase two of the replication. Confirm the newly learned knowledge.
%     - retrieve(+Key,-Node,-Gen,-Value)
%     A request message to retrieve our value for Key.  Also provides
%     our node id and the generation.
%     - forget(+Nodes)
%     Forget the existence of Nodes.
%     - node(-Node)
%     Get the node id.
%
%   @tbd: originally the changed was  handled  by   a  get  and when not
%   successful with a new set, named   _paxos_audit_. I don't really see
%   why we need this.

paxos_message(prepare(Key,Node,Gen,Value)) :-
    node(Node),
    (   ledger(Key, Gen, _)
    ->  true
    ;   Gen = 0,
        ledger_create(Key, Gen, Value)
    ),
    debug(paxos, 'Prepared ~p-~p@~d', [Key,Value,Gen]).
paxos_message(accept(Key,Node,Gen,GenA,Value)) :-
    node(Node),
    debug(paxos, 'Accept ~p-~p@~p?', [Key, Value, Gen]),
    (   ledger_update(Key, Gen, Value)
    ->  debug(paxos, 'Accepted ~p-~p@~d', [Key,Value,Gen]),
        GenA = Gen
    ;   debug(paxos, 'Rejected ~p@~d', [Key, Gen]),
        GenA = nack
    ).
paxos_message(changed(Key,Gen,Value,Acceptors)) :-
    ledger_update_holders(Key,Gen,Acceptors),
    broadcast(paxos_changed(Key,Value)).
paxos_message(learn(Key,Node,Gen,GenA,Value)) :-
    node(Node),
    debug(paxos, 'Learn ~p-~p@~p?', [Key, Value, Gen]),
    (   ledger_learn(Key,Gen,Value)
    ->  debug(paxos, 'Learned ~p-~p@~d', [Key,Value,Gen]),
        GenA = Gen
    ;   debug(paxos, 'Rejected ~p@~d', [Key, Gen]),
        GenA = nack
    ).
paxos_message(learned(Key,Gen,_Value,Acceptors)) :-
    ledger_update_holders(Key,Gen,Acceptors).
paxos_message(retrieve(Key,Node,K,Value)) :-
    node(Node),
    debug(paxos, 'Retrieving ~p', [Key]),
    ledger(Key,K,Value),
    debug(paxos, 'Retrieved ~p-~p@~d', [Key,Value,K]),
    !.
paxos_message(forget(Nodes)) :-
    ledger_forget(Nodes).
paxos_message(node(Node)) :-
    node(Node).

%%  paxos_set(+Term) is semidet.
%
%   Equivalent to paxos_key(Term,Key), pasox_set(Key,Term).   I.e., Term
%   is a ground compound term and its   key is the name/arity pair. This
%   version provides compatibility with older versions of this library.

%%  paxos_set(+Key, +Value) is semidet.
%%  paxos_set(+Key, +Value, +Options) is semidet.
%
%   negotiates to have Key-Value recorded in the  ledger for each of the
%   quorum's members. This predicate succeeds  if the quorum unanimously
%   accepts the proposed term. If no such   entry  exists in the Paxon's
%   ledger, then one is silently  created.   paxos_set/1  will retry the
%   transaction several times (default: 20)   before failing. Failure is
%   rare and is usually the result of a collision of two or more writers
%   writing to the same term at precisely  the same time. On failure, it
%   may be useful to wait some random period of time, and then retry the
%   transaction. By specifying a retry count   of zero, paxos_set/2 will
%   succeed iff the first ballot succeeds.
%
%   On   success,   paxos_set/1   will   also     broadcast   the   term
%   paxos(changed(Key,Value), to the quorum.
%
%   Options processed:
%
%     - retry(Retries)
%     is a non-negative integer specifying the number of retries that
%     will be performed before a set is abandoned.  Defaults to the
%     _setting_ `max_sets` (20).
%     - timeout(+Seconds)
%     Max time to wait for the forum to reply.  Defaults to the
%     _setting_ `response_timeout` (0.020, 20ms).
%
%   @arg Term is a compound  that   may  have  unbound variables.
%   @tbd If the Value is already current, should we simply do nothing?

paxos_set(Term) :-
    paxos_key(Term, Key),
    paxos_set(Key, Term, []).

paxos_set(Key, Value) :-
    paxos_set(Key, Value, []).

paxos_set(Key, Value, Options) :-
    must_be(ground, Key-Value),
    paxos_initialize,
    option(retry(Retries), Options, Retries),
    option(timeout(TMO), Options, TMO),
    apply_default(Retries, max_sets),
    apply_default(TMO, response_timeout),
    paxos_message(prepare(Key,Np,Rp,Value), TMO, Prepare),
    between(0, Retries, _),
      life_quorum(Quorum, Alive),
      collect(Quorum, false, Np, Rp, Prepare, Rps, PrepNodes),
      majority(PrepNodes, Quorum),
      debug(paxos, 'Prepare: ~p', [Rps]),
      max_list(Rps, K),
      succ(K, K1),
      paxos_message(accept(Key,Na,K1,Ra,Value), TMO, Accept),
      collect(Alive, Ra == nack, Na, Ra, Accept, Ras, AcceptNodes),
      majority(AcceptNodes, Quorum),
      intersecting(PrepNodes, AcceptNodes),
      c_element(Ras, K, K1),
      broadcast(paxos(log(Key,Value,AcceptNodes,K1))),
      paxos_message(changed(Key,K1,Value,AcceptNodes), -, Changed),
      broadcast(Changed),
      update_failed(Quorum, AcceptNodes),
    !.

apply_default(Var, Setting) :-
    var(Var),
    !,
    setting(Setting, Var).
apply_default(_, _).

majority(SubSet, Set) :-
    popcount(SubSet) >= (popcount(Set)+2)//2.

intersecting(Set1, Set2) :-
    Set1 /\ Set2 =\= 0.


%!  collect(+Quorum, :Stop, ?Node, ?Template, ?Message,
%!          -Result, -NodeSet) is semidet.
%
%   Perform a broadcast request using Message.   Node and Template share
%   with Message and extract the replying node and the result value from
%   Message. Result is the list of  instantiations for Template received
%   and NodeSet is the set (bitmask) of   Node values that replies, i.e.
%   |NodeSet| is length(Result). The transfer stops   if  all members of
%   the set Quorum responded or the configured timeout passed.
%
%   @tbd If we get a `nack` we can stop

collect(Quorum, Stop, Node, Template, Message, Result, NodeSet) :-
    State = state(0),
    L0 = [dummy|_],
    Answers = list(L0),
    (   broadcast_request(Message),
        (   Stop
        ->  !,
            fail
        ;   true
        ),
        duplicate_term(Template, Copy),
        NewLastCell = [Copy|_],
        arg(1, Answers, LastCell),
        nb_linkarg(2, LastCell, NewLastCell),
        nb_linkarg(1, Answers, NewLastCell),
        arg(1, State, Replied0),
        Replied is Replied0 \/ (1<<Node),
        nb_setarg(1, State, Replied),
        Quorum /\ Replied =:= Quorum
    ->  true
    ;   true
    ),
    arg(1, State, NodeSet),
    arg(1, Answers, [_]),               % close the answer list
    L0 = [_|Result].

%!  paxos_get(?Term) is semidet.
%
%   Equivalent to paxos_key(Term,Key), pasox_get(Key,Term).   I.e., Term
%   is a compound term and its key  is the name/arity pair. This version
%   provides compatibility with older versions of this library.

%!  paxos_get(+Key, +Value) is semidet.
%!  paxos_get(+Key, +Value, +Options) is semidet.
%
%   unifies Term with the entry retrieved from the Paxon's ledger. If no
%   such entry exists in the member's local   cache,  then the quorum is
%   asked to provide a value,  which   is  verified  for consistency. An
%   implied paxos_set/1 follows. This predicate  succeeds if a term
%   with the same functor and arity exists   in  the Paxon's ledger, and
%   fails otherwise.
%
%   Options processed:
%
%     - retry(Retries)
%     is a non-negative integer specifying the number of retries that
%     will be performed before a set is abandoned.  Defaults to the
%     _setting_ `max_gets` (5).
%     - timeout(+Seconds)
%     Max time to wait for the forum to reply.  Defaults to the
%     _setting_ `response_timeout` (0.020, 20ms).
%
%   @arg Term is a compound. Any unbound variables are unified with
%   those provided in the ledger entry.

paxos_get(Term) :-
    paxos_key(Term, Key),
    paxos_get(Key, Term, []).
paxos_get(Key, Value) :-
    paxos_get(Key, Value, []).

paxos_get(Key, Value, _) :-
    ledger(Key, _Line, Value),
    !.
paxos_get(Key, Value, Options) :-
    paxos_initialize,
    option(retry(Retries), Options, Retries),
    option(timeout(TMO), Options, TMO),
    apply_default(Retries, max_gets),
    apply_default(TMO, response_timeout),
    Msg = Line-Value,
    paxos_message(retrieve(Key,Nr,Line,Value), TMO, Retrieve),
    node(Node),
    between(0, Retries, _),
      life_quorum(Quorum, Alive),
      QuorumA is Alive /\ \(1<<Node),
      collect(QuorumA, false, Nr, Msg, Retrieve, Terms, RetrievedNodes),
      debug(paxos, 'Retrieved: ~p from 0x~16r', [Terms, RetrievedNodes]),
      highest_vote(Terms, _Line-MajorityValue, Count),
      debug(paxos, 'Best: ~p with ~d votes', [MajorityValue, Count]),
      Count >= (popcount(QuorumA)+2)//2,
      debug(paxos, 'Retrieve: accept ~p', [MajorityValue]),
      update_failed(Quorum, RetrievedNodes),
      paxos_set(Key, MajorityValue),    % Is this needed?
    !.

highest_vote(Terms, Term, Count) :-
    msort(Terms, Sorted),
    count_votes(Sorted, Counted),
    sort(1, >, Counted, [Count-Term|_]).

count_votes([], []).
count_votes([H|T0], [N-H|T]) :-
    count_same(H, T0, 1, N, R),
    count_votes(R, T).

count_same(H, [Hc|T0], C0, C, R) :-
    H == Hc,
    !,
    C1 is C0+1,
    count_same(H, T0, C1, C, R).
count_same(_, R, C, C, R).

%!  paxos_key(+Term, -Key) is det.
%
%   Compatibility to allow for paxos_get/1, paxos_set/1, etc. The key of
%   a compound term is a term `'$c'(Name,Arity)`.   Note  that we do not
%   use `Name/Arity` and `X/Y` is  naturally   used  to organize keys as
%   hierachical _paths_.

paxos_key(Compound, '$c'(Name,Arity)) :-
    compound(Compound), !,
    compound_name_arity(Compound, Name, Arity).
paxos_key(Compound, _) :-
    must_be(compound, Compound).


		 /*******************************
		 *          REPLICATION		*
		 *******************************/

%!  paxos_replicate_key(+Nodes:bitmap, ?Key, +Options) is det.
%
%   Replicate a Key to Nodes.  If Key is unbound, a random key is
%   selected.
%
%     - timeout(+Seconds)
%     Max time to wait for the forum to reply.  Defaults to the
%     _setting_ `response_timeout` (0.020, 20ms).

paxos_replicate_key(Nodes, Key, Options) :-
    replication_key(Nodes, Key),
    option(timeout(TMO), Options, TMO),
    apply_default(TMO, response_timeout),
    ledger_current(Key, Gen, Value, Holders),
    paxos_message(learn(Key,Na,Gen,Ga,Value), TMO, Learn),
    collect(Nodes, Ga == nack, Na, Ga, Learn, _Gas, LearnedNodes),
    NewHolders is Holders \/ LearnedNodes,
    paxos_message(learned(Key,Gen,Value,NewHolders), -, Learned),
    broadcast(Learned),
    update_failed(Nodes, LearnedNodes).

replication_key(_Nodes, Key) :-
    ground(Key),
    !.
replication_key(Nodes, Key) :-
    (   Nth is 1+random(popcount(Nodes))
    ;   Nth = 1
    ),
    call_nth(needs_replicate(Nodes, Key), Nth),
    !.

needs_replicate(Nodes, Key) :-
    ledger_current(Key, _Gen, _Value, Holders),
    Nodes /\ \Holders =\= 0.


		 /*******************************
		 *          NODE STATUS		*
		 *******************************/

%!  update_failed(+Quorum, +Alive) is det.
%
%   We just sent the Quorum a  message  and   got  a  reply from the set
%   Alive.

:- dynamic failed/1, failed/3.
:- volatile failed/1, failed/3.

update_failed(Quorum, Alive) :-
    Failed is Quorum /\ \Alive,
    alive(Alive),
    consider_dead(Failed),
    (   failed(Failed)
    ->  true
    ;   clause(failed(_Old), true, Ref)
    ->  asserta(failed(Failed)),
        erase(Ref),
        debug(paxos(node), 'Updated failed quorum to 0x~16r', [Failed])
    ;   asserta(failed(Failed))
    ).

consider_dead(0) :-
    !.
consider_dead(Failed) :-
    Node is lsb(Failed),
    consider_dead1(Node),
    Rest is Failed /\ \(1<<Node),
    consider_dead(Rest).

consider_dead1(Node) :-
    clause(failed(Node, Last, Score), true, Ref),
    !,
    get_time(Now),
    Passed is Now-Last,
    NewScore is Score*(2**(-Passed/60)) + 10,
    asserta(failed(Node, Now, NewScore)),
    erase(Ref).
consider_dead1(Node) :-
    get_time(Now),
    asserta(failed(Node, Now, 10)).

alive(Bitmap) :-
    (   clause(failed(Node, _Last, _Score), true, Ref),
        Bitmap /\ (1<<Node) =\= 0,
        erase(Ref),
        fail
    ;   true
    ).


%!  life_quorum(-Quorum, -LifeQuorum) is det.
%
%   Find the Quorum and the living nodes   from  the Quorum. This is the
%   set for which we wait.  If  the   LifeQuorum  is  not  a majority we
%   address the whole Quorum.
%
%   @tbd At some point in time we must remove a node from the quorum.

life_quorum(Quorum, LifeQuorum) :-
    quorum(Quorum),
    (   failed(Failed),
        Failed \== 0,
        LifeQuorum is Quorum /\ \Failed,
        majority(LifeQuorum, Quorum)
    ->  true
    ;   LifeQuorum = Quorum
    ).


		 /*******************************
		 *      KEY CHANGE EVENTS	*
		 *******************************/

%!  paxos_on_change(?Term, :Goal) is det.
%!  paxos_on_change(?Key, ?Value, :Goal) is det.
%
%   executes the specified Goal  when   Key  changes.  paxos_on_change/2
%   listens for paxos(changed(Key,Value) notifications   for  Key, which
%   are emitted as the result   of  successful paxos_set/3 transactions.
%   When one is received for Key, then   Goal  is executed in a separate
%   thread of execution.
%
%   @arg Term is a compound, identical to that used for
%   paxos_get/1.
%   @arg Goal is one of:
%     - a callable atom or term, or
%     - the atom =ignore=, which causes monitoring for Term to be
%       discontinued.

paxos_on_change(Term, Goal) :-
    paxos_key(Term, Key),
    paxos_on_change(Key, Term, Goal).

paxos_on_change(Key, Value, Goal) :-
    Goal = _:Plain,
    must_be(callable, Plain),
    (   Plain == ignore
    ->  unlisten(paxos_user, paxos_changed(Key,Value))
    ;   listen(paxos_user, paxos(changed(Key,Value)),
               thread_create(Goal, _, [detached(true)])),
        paxos_initialize
    ).


		 /*******************************
		 *            HOOKS		*
		 *******************************/

%!  node(-Node) is det.
%
%   Get the node ID for this paxos node.

%!  quorum(-Quorum) is det.
%
%   Get the current quorum as a bitmask

%!  paxos_message(+PaxOS, +TimeOut, -BroadcastMessage) is det.
%
%   Transform a basic PaxOS message in   a  message for the broadcasting
%   service. This predicate is hooked   by paxos_message_hook/3 with the
%   same signature.
%
%   @arg TimeOut is one of `-` or a time in seconds.

paxos_message(Paxos, TMO, Message) :-
    paxos_message_hook(paxos(Paxos), TMO, Message),
    !.
paxos_message(Paxos, TMO, Message) :-
    throw(error(mode_error(det, fail,
                           paxos:paxos_message_hook(Paxos, TMO, Message)), _)).


		 /*******************************
		 *           STORAGE		*
		 *******************************/

:- dynamic
    paxons_ledger/4.                    % Key, Gen, Value, Holders

%!  ledger_current(?Key, ?Gen, ?Value, ?Holders) is nondet.
%
%   True when Key is a known key in my ledger.

ledger_current(Key, Gen, Value, Holders) :-
    paxons_ledger(Key, Gen, Value, Holders),
    valid(Holders).


%!  ledger(+Key, -Gen, -Value) is semidet.
%
%   True if the ledger has Value associated  with Key at generation Gen.
%   Note that if the value is  not   yet  acknowledged  by the leader we
%   should not use it.

ledger(Key, Gen, Value) :-
    paxons_ledger(Key, Gen, Value0, Holders),
    valid(Holders),
    !,
    Value = Value0.

%!  ledger_create(+Key, +Gen, +Value) is det.
%
%   Create a new Key-Value pair  at   generation  Gen.  This is executed
%   during the preparation phase.

ledger_create(Key, Gen, Value) :-
    get_time(Now),
    asserta(paxons_ledger(Key, Gen, Value, created(Now))).

%!  ledger_update(+Key, +Gen, +Value) is semidet.
%
%   Update Key to Value if the  current   generation  is older than Gen.
%   This reflects the accept phase of the protocol.

ledger_update(Key, Gen, Value) :-
    paxons_ledger(Key, Gen0, _Value, _Holders),
    !,
    Gen > Gen0,
    get_time(Now),
    asserta(paxons_ledger(Key, Gen, Value, accepted(Now))),
    (   Gen0 == 0
    ->  retractall(paxons_ledger(Key, Gen0, _, _))
    ;   true
    ).

%!  ledger_update_holders(+Key, +Gen, +Holders) is det.
%
%   The leader acknowledged that Key@Gen represents a valid new

ledger_update_holders(Key, Gen, Holders) :-
    clause(paxons_ledger(Key, Gen, Value, Holders0), true, Ref),
    !,
    (   Holders0 == Holders
    ->  true
    ;   asserta(paxons_ledger(Key, Gen, Value, Holders)),
        erase(Ref)
    ),
    clean_key(Holders0, Key, Gen).

clean_key(Holders, _Key, _Gen) :-
    valid(Holders),
    !.
clean_key(_, Key, Gen) :-
    (   clause(paxons_ledger(Key, Gen0, _Value, _Holders0), true, Ref),
        Gen0 < Gen,
        erase(Ref),
        fail
    ;   true
    ).


%!  ledger_learn(+Key,+Gen,+Value) is semidet.
%
%   We received a learn event.

ledger_learn(Key,Gen,Value) :-
    paxons_ledger(Key, Gen0, Value0, _Holders),
    !,
    (   Gen == Gen0,
        Value == Value0
    ->  true
    ;   Gen > Gen0
    ->  get_time(Now),
        asserta(paxons_ledger(Key, Gen, Value, learned(Now)))
    ).
ledger_learn(Key,Gen,Value) :-
    get_time(Now),
    asserta(paxons_ledger(Key, Gen, Value, learned(Now))).

%!  ledger_forget(+Nodes) is det.
%
%   Remove Nodes from all ledgers.  This is executed in a background
%   thread.

ledger_forget(Nodes) :-
    thread_create(ledger_forget_threaded(Nodes), _,
                  [ detached(true)
                  ]).

ledger_forget_threaded(Nodes) :-
    debug(paxos(node), 'Forgetting 0x~16r', [Nodes]),
    forall(ledger_current(Key, Gen, _Value, Holders),
           ledger_forget(Nodes, Key, Gen, Holders)),
    debug(paxos(node), 'Forgotten 0x~16r', [Nodes]).

ledger_forget(Nodes, Key, Gen, Holders) :-
    NewHolders is Holders /\ \Nodes,
    (   NewHolders \== Holders,
        ledger_update_holders(Key, Gen, NewHolders)
    ->  true
    ;   true
    ).

valid(Holders) :-
    integer(Holders).
