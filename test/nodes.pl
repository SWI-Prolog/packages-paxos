/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2018, VU University Amsterdam
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

:- module(test_nodes,
          [ node_create/3,              % +Address, ?Id, +Options
            run_on/2,                   % +Node, ?Goal

            run_node/0                  % Run a client node
          ]).
:- use_module(library(lists)).
:- use_module(library(debug)).
:- use_module(library(error)).
:- use_module(library(option)).
:- use_module(library(unix)).
:- use_module(library(process)).

:- debug(nodes(connect)).

/** <module> Test interacting processes

This module provides a test  framework   that  manages multiple _nodes_,
either on the same or on different  machines   on  which  we can start a
program, e.g., using `ssh`.

The nodes are connected to the controller using sockets.
*/

%!  node(?Id, ?StreamPair)
%
%   Identifies a node in our network.

:- dynamic
    self_channel/1,                     % Pipe
    node/2,                             % NodeID, Stream
    node_pid/2,                         % NodeID, PID
    client/2,                           % NodeID, Stream
    queue/3,                            % Id, Node, Queue
    gate/1,                             % Host:Port
    pending/4,                          % Passwd, Id, Queue, Options
    proxy_message_kind/1.

%!  node_create(+Launcher, ?Id, +Options)
%
%   Create a new node at address and connect it.   Options
%
%     - alias(Name:atom)
%     Name of the node.
%     - proxy_messages(+Kinds)
%     Kinds is either a list of message kinds (see print_message/2)
%     or one of the constants `none` or `all`.  Default is not to
%     proxy any messages.
%     - async(Bool)
%     If `true` (default `false`), do not wait for the node to become
%     online.

node_create(Launcher, Id, Options) :-
    option(alias(Id), Options, Id),
    default_id(Id),
    launcher(Launcher, Id, Prog, Args),
    controller,
    node_gate(_Port),
    PasswdNum is random(1<<63),
    number_string(PasswdNum, Passwd),
    format(atom(PasswdOption), '--password=~w', [Passwd]),
    connect_option(ConnectOption),
    append(Args,
           [ '-g', 'run_node', file('nodes.pl'),
             ConnectOption,
             PasswdOption
           ], ProgArgs),
    (   option(async(true), Options, false)
    ->  Q = []
    ;   message_queue_create(Q)
    ),
    asserta(pending(Passwd, Id, Q, Options)),
    process_create(Prog, ProgArgs,
                   [ process(Pid)
                   ]),
    asserta(node_pid(Id, Pid)),
    (   Q == []
    ->  true
    ;   thread_get_message(Q, Started),
        (   Started == true
        ->  true
        ;   throw(Started)
        )
    ).

launcher(background, _,  path(swipl), []).
launcher(terminator, Id, path(terminator), ['--title', Title, '-x', 'swipl']) :-
    format(string(Title), 'Node ~w', [Id]).

default_id(Id) :-
    var(Id),
    !,
    gensym(n, Id).
default_id(Id) :-
    node(Id, _),
    !,
    permission_error(alias, node, Id).
default_id(_).

:- on_signal(chld, _, child_changed).

child_changed(_Sig) :-
    (   node_pid(Node, PID),
        catch(process_wait(PID, Status,
                           [ timeout(0)
                           ]),
              E,
              (   print_message(warning, E),
                  fail
              )),
        Status \== timeout,
        retractall(node_pid(Node, PID)),
        debug(nodes(pid), 'Process ~p for node ~p: stopped with ~p',
              [PID, Node, Status]),
        fail
    ;   true
    ).

		 /*******************************
		 *          CONTROLLER		*
		 *******************************/

%!  run_on(+Nodes:list, +Goal) is nondet.
%!  run_on(+Node, +Goal) is semidet.
%
%   Run once(Goal) on  Node.  The  binding,   failure  or  exception  is
%   propagated to the caller. If  the  first   argument  is  a list, the
%   message is sent to each member of the  list and the replies from the
%   nodes is enumerated on backtracking.

run_on(Nodes, Goal) :-
    is_list(Nodes),
    !,
    length(Nodes, NodeCount),
    term_variables(Goal, Vars),
    Template =.. [v|Vars],
    call_id(Id),
    message_queue_create(Q),
    State = nodes(NodeCount),
    setup_call_cleanup(
        asserta(queue(Id, Nodes, Q), Ref),
        ( forall(( member(Node, Nodes),
                   node(Node, Stream)
                 ),
                 ( fast_write(Stream, call(Id, Goal, Template)),
                   flush_output(Stream)
                 )),
          collect_replies(State, Nodes, Q, Goal, Template)
        ),
        erase(Ref)).
run_on(Node, Goal) :-
    term_variables(Goal, Vars),
    Template =.. [v|Vars],
    node(Node, Stream),
    call_id(Id),
    message_queue_create(Q),
    setup_call_cleanup(
        asserta(queue(Id, Node, Q), Ref),
        ( fast_write(Stream, call(Id, Goal, Template)),
          flush_output(Stream),
          thread_get_message(Q, Reply)
        ),
        erase(Ref)),
    query_reply(Reply, Node, Goal, Template).

:- dynamic
    current_query_id/1.

call_id(Id) :-
    with_mutex(test_nodes, call_id_sync(Id0)),
    Id = Id0.

call_id_sync(Id) :-
    retract(current_query_id(Id0)),
    Id is Id0+1,
    asserta(current_query_id(Id)).
call_id_sync(1) :-
    asserta(current_query_id(1)).

%!  query_reply(+Reply, +Node, +Goal, +Template)

query_reply(true(Template), _, _, Template).
query_reply(error(E), _, _, _) :-
    throw(E).
query_reply(false, _, _, _) :-
    fail.
query_reply(end_of_file, _, halt, _) :-
    !.
query_reply(end_of_file, Node, _, _) :-
    throw(error(node_error(Node, halted), _)).

collect_replies(State, Nodes, Queue, Goal, Template) :-
    repeat,
      thread_get_message(Queue, Reply),
      arg(1, State, Left),
      Left1 is Left - 1,
      nb_setarg(1, State, Left1),
      (   Left1 == 0
      ->  !
      ;   true
      ),
      query_reply(Reply, Nodes, Goal, Template).


		 /*******************************
		 *              GATE		*
		 *******************************/

%!  node_gate(?Port, -Password) is det.
%
%   Create the gate keeper that accepts new nodes.

node_gate(Port) :-
    gate(localhost:Port),
    !.
node_gate(Port) :-
    tcp_socket(Socket),
    tcp_bind(Socket, Port),
    tcp_listen(Socket, 5),
    thread_create(gate_keeper(Socket), _,
                  [ alias(node_gate)
                  ]),
    asserta(gate(localhost:Port)).      % TBD: find our hostname

gate_keeper(S) :-
    repeat,
    tcp_accept(S, S2, Peer),
    debug(nodes(connect), 'Accept from ~p', [Peer]),
    tcp_open_socket(S2, Pair),
    catch(accept_node(Pair, Peer), E,
          print_message(warning, E)),
    fail.

accept_node(Pair, Peer) :-
    fast_read(Pair, node(Passwd)),
    debug(nodes(connect), 'Got passwd = ~p', [Passwd]),
    passwd_pass(Passwd, Peer, Id, Queue, Options),
    asserta(node(Id, Pair)),
    self_channel(Self),
    debug(nodes(connect), 'Informing self', []),
    fast_write(Self, join(Id)),
    flush_output(Self),
    debug(nodes(connect), 'Confirming ~p to client', [Id]),
    fast_write(Pair, id(Id, Options)),
    flush_output(Pair),
    (   Queue == []
    ->  true
    ;   thread_send_message(Queue, true)
    ).

passwd_pass(Passwd, _, Id, Queue, Options) :-
    retract(pending(Passwd, Id, Queue, Options)),
    !.
passwd_pass(_, Peer, _, Queue, _) :-
    (   Queue == []
    ->  true
    ;   thread_send_message(Queue,
                            error(permission_error(connect, node, Peer),_))
    ),
    permission_error(connect, node, Peer).

connect_option(Connect) :-
    gate(Gate),
    format(atom(Connect), '--connect=~w', [Gate]).


		 /*******************************
		 *            CONNECT		*
		 *******************************/

%!  run_node
%
%   Run a node.

run_node :-
    current_prolog_flag(argv, Argv),
    argv_options(Argv, _Rest, Options),
    debug(nodes(client), 'Running ~p', [node(Options)]),
    node(Options).

node(Options) :-
    option(password(Password), Options),
    option(connect(Address), Options),
    atomic_list_concat([Host,PortAtom], :, Address),
    atom_number(PortAtom, Port),
    tcp_connect(Host:Port, Stream, []),
    fast_write(Stream, node(Password)),
    flush_output(Stream),
    fast_read(Stream, id(Id, NodeOptions)),
    run_node(Id, Stream, NodeOptions).

%!  run_node(+Id, +Stream, +Options)
%
%   Control a node.
%
%   @arg Options is passed down  from   node_create/3  that created this
%   node.  See node_create/3 for the processed options.

run_node(Id, Stream, Options) :-
    option(proxy_messages(Proxy), Options, []),
    asserta(client(Id, Stream)),
    init_message_proxy(Proxy),
    node_loop(Stream).

node_loop(Stream) :-
    fast_read(Stream, Command),
    debug(nodes(command), 'Client got ~p', [Command]),
    execute(Command, Stream),
    node_loop(Stream).

execute(call(Id, Call, Template), Stream) :-
    (   catch(user:Call, E, true)
    ->  (   var(E)
        ->  Reply = true(Template)
        ;   Reply = error(E)
        )
    ;   Reply = false
    ),
    fast_write(Stream, reply(Id, Reply)),
    flush_output(Stream).

init_message_proxy(none) :-
    !.
init_message_proxy([]) :-
    !.
init_message_proxy(List) :-
    is_list(List),
    !,
    forall(member(Kind, List),
           assertz(proxy_message_kind(Kind))),
    link_messages.
init_message_proxy(all) :-
    assertz(proxy_message_kind(_)),
    link_messages.

link_messages :-
    asserta(user:message_hook(Term, Kind, Lines) :-
               message_proxy_hook(Term, Kind, Lines)).

message_proxy_hook(Term, Kind, Lines) :-
    Kind \== silent,
    client(_Node, Stream),
    proxy_message_kind(Kind),
    !,
    fast_write(Stream, message(Term, Kind, Lines)),
    flush_output(Stream).




		 /*******************************
		 *            DISPATCH		*
		 *******************************/

:- dynamic
    controller/1.

controller :-
    controller(_Id),
    !.
controller :-
    with_mutex(test_nodes, controller_sync).

controller_sync :-
    controller(_),
    !.
controller_sync :-
    thread_create(dispatch, Id,
                  [ alias(node_message_handler)
                  ]),
    asserta(controller(Id)).

dispatch :-
    init_node_controller,
    self_channel(Self),
    findall(S, node(_, S), Streams),
    dispatch([Self|Streams]).

dispatch(Streams) :-
    wait_for_input(Streams, Available, infinite),
    maplist(dispatch_available(Streams, Streams1), Available),
    dispatch(Streams1).

dispatch_available(Set0, Set, Stream) :-
    node(Node, Stream),
    !,
    fast_read(Stream, Term),
    (   dispatch_term(Term, Node, Set0, Set)
    ->  true
    ;   print_message(warning, dispatch_failed(Node, Term)),
        Set = Set0
    ).
dispatch_available(Set0, Set, Stream) :-
    self_channel(Stream),
    fast_read(Stream, Term),
    dispatch_admin(Term, Set0, Set).

dispatch_term(end_of_file, Node, Set0, Set) :-
    !,
    debug(nodes(connect), 'EOF for ~p', [Node]),
    node(Node, Stream),
    delete(Set0, Stream, Set),
    lost(Node).
dispatch_term(reply(Magic,Term), _Node, Set, Set) :-
    queue(Magic, _, Queue),
    thread_send_message(Queue, Term).
dispatch_term(message(Term, Kind, Lines), Node, Set, Set) :-
    proxy_message(Node, Term, Kind, Lines).

%!  proxy_message(+Node, +Term, +Kind, +Lines)
%
%   Handle a message sent to us from  a node. Forwarding messages allows
%   us to examine the flow of events in the nodes as one stream.

proxy_message(Node, _Term, Kind, Lines) :-
    current_prolog_flag(message_context, Ctx0),
    setup_call_cleanup(
        ( nb_setval(message_node, Node),
          set_prolog_flag(message_context, [node,time])
        ),
        print_message_lines(user_error, kind(Kind), Lines),
        ( set_prolog_flag(message_context, Ctx0),
          nb_delete(message_node)
        )).

:- multifile
    prolog:message_prefix_hook/2.

prolog:message_prefix_hook(node, Prefix) :-
    nb_current(message_node, Node),
    format(string(Prefix), '[node ~w]', [Node]).

dispatch_admin(join(Id), Set, [Stream|Set]) :-
    node(Id, Stream).


%!  lost(+Node)
%
%   Close the communication to Node.

lost(Node) :-
    retract(node(Node, Stream)),
    close(Stream, [force(true)]),
    forall(retract(queue(_, Node, Queue)),
           thread_send_message(Queue, end_of_file)).


		 /*******************************
		 *        INITIALIZATION	*
		 *******************************/

init_node_controller :-
    self_channel(_),
    !.
init_node_controller :-
    pipe(R, W),
    set_stream(R, encoding(octet)),
    set_stream(W, encoding(octet)),
    stream_pair(Pipe, R, W),
    asserta(self_channel(Pipe)).
