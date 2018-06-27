/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (c)  2018, VU University Amsterdam
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

:- module(scenario,
          [ play/2,                             % +Scenario, +Options

            op(800, xfx, <-),
            op(990, xfy, &&)
          ]).
:- use_module(library(option)).
:- use_module(library(apply)).
:- use_module(library(error)).
:- use_module(library(debug)).
:- use_module(nodes).

/** <module> Describe and run concurrent test scnearios

Describe and run a concurrent scenario.
*/

scenario(1,
         [ start_node(a) && start_node(b),
           on(b, k := 1) && on(a, K <- k) && K == 1
         ]).
scenario(2,
         [ start_node(a) && start_node(b),
           on(b, k := 1) && on(a, ledger(k,_,K,_)) && K == 1
         ]).

%!  play(+Steps, +Options)
%
%   Play all Steps.  Options:
%
%     - speed(ActionsPerSec)
%     Time between actions

play(Steps, Options) :-
    is_list(Steps),
    !,
    play(Steps, _{}, State, 0, Tick, Options),
    played(State, Tick).
play(Scenario, Options) :-
    scenario(Scenario, Steps),
    play(Steps, _{}, State, 0, Tick, Options),
    played(State, Tick).

play([], State0, State, Tick, Tick, Options) :-
    close_nodes(State0, State, Options).
play([H|T], State0, State, Tick0, Tick, Options) :-
    (   step(H, State0, State1, Tick0, Options)
    ->  true
    ;   update_state(failed(H), State0, State1, Tick)
    ),
    Tick1 is Tick0+1,
    delay(Options),
    play(T, State1, State, Tick1, Tick, Options).

step(Var, _, _, _, _) :-
    var(Var),
    !,
    instantiation_error(Var).
step(A&&B, State0, State, Tick, Options) :-
    !,
    (   step(A, State0, State1, Tick, Options)
    ->  step(B, State1, State, Tick,  Options)
    ;   update_state(failed(A), State0, State, Tick)
    ).
step(Goal, _, _, Tick, _) :-
    debug(scenario(step), '[Step ~D] ~p ...', [Tick, Goal]),
    fail.
step(start_node(Id), State0, State, Tick, Options) :-
    option(launcher(Launcher), Options, background),
    node_create(Launcher, Id, Options),
    call_on(Id, (load_files(paxos_node),start_node([]))),
    update_state(add_node(Id), State0, State, Tick).
step(on(Node, Action), State, State, _Tick, _Options) :-
    call_on(Node, Action).
step(X==Y, State, State, _Tick, _Options) :-
    X==Y.

update_state(add_node(Id), State0, State, _Tick) :-
    add_state_list(nodes, Id, State0, State).
update_state(failed(Test), State0, State, Tick) :-
    add_state_list(failures, failed(Test, Tick), State0, State).

add_state_list(Field, Value, State0, State) :-
    (   get_dict(Field, State0, List)
    ->  put_dict(Field, State0, [Value|List], State)
    ;   put_dict(Field, State0, [Value], State)
    ).

delay(Options) :-
    option(speed(Speed), Options, 1),
    Delay is 1/Speed,
    sleep(Delay).

close_nodes(State0, State, _Options) :-
    del_dict(nodes, State0, Nodes, State),
    !,
    maplist(close_node, Nodes).
close_nodes(State, State, _).

close_node(Node) :-
    call_on(Node, halt).

%!  played(+State, +Tick) is det.
%
%   We finished playing the scenario with final state State at Tick

played(State, _) :-
    Failures = State.get(failures),
    Failures \== [],
    !,
    print_message(error, scenario(failed(Failures))),
    fail.
played(_, _).

		 /*******************************
		 *            MESSAGES		*
		 *******************************/

:- multifile prolog:message//1.

prolog:message(scenario(Msg)) -->
    message(Msg).

message(failed(Failures)) -->
    [ 'Scenario failed: ~p'-[Failures] ].
