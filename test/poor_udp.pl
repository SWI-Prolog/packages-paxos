:- module(poor_udp,
          [ drop/1,                             % +Rate
            late/2,                             % +Rate, +Decay
            duplicate/2,                        % +Rate, +Decay
            delay/2,                            % +Rate, +Decay
            profile/1                           % +ListOrName
          ]).
:- use_module(library(random)).
:- use_module(library(debug)).
:- use_module(library(apply)).
:- use_module(library(socket), []).
:- use_module(library(udp_broadcast), []).

:- debug(udp(qos)).

/** <module> Emulate a unreliable UDP network
*/

:- dynamic
    drop_rate/1,
    late_rate/2,
    dupl_rate/2,
    delay_rate/2,
    delayed/5.

drop_rate(0.02).
late_rate(0.02, 0.5).
dupl_rate(0.02, 0.5).
delay_rate(0.02, 0.5).

%!  drop(+Rate)
%
%   Rate is the probability that  a  package   is  dropped.  `0` means a
%   perfect network, `1` a completely broken network.

drop(Rate) :-
    retractall(drop_rate(_)),
    asserta(drop_rate(Rate)).

%!  late(+Rate, +Decay)
%
%   Rate is the probability that the package will arrive late, i.e., out
%   of order. Decay is the probability it will arrive after the next.

late(Rate, Decay) :-
    retractall(late_rate(_, _)),
    asserta(late_rate(Rate, Decay)).

%!  duplicate(+Rate, +Decay)
%
%   Rate is the probability the package  is duplicated. This accepts the
%   package immediately as is and stores  a   copy  in the queue that is
%   also used by late/2.

duplicate(Rate, Decay) :-
    retractall(dupl_rate(_, _)),
    asserta(dupl_rate(Rate, Decay)).

%!  delay(+Rate, +Decay)
%
%   Rate is the probability to delay the message. This introduces random
%   sleeps of 10ms. After each sleep there  is a probability of Decay to
%   wake up. Thus, with a Decay  of   0.5  we wait 10ms with probability
%   0.5, 20ms with probability 0.25, 30ms with probability 0.125, etc.

delay(Rate, Decay) :-
    retractall(delay_rate(_, _)),
    asserta(delay_rate(Rate, Decay)).

profile(Actions) :-
    is_list(Actions),
    !,
    maplist(call, Actions).
profile(Name) :-
    profile(Name, Actions),
    profile(Actions).

profile(perfect,
        [ drop(0),
          late_rate(0,0),
          dupl_rate(0,0),
          delay_rate(0,0)
        ]).


:- abolish(udp_broadcast:udp_receive/4).

udp_broadcast:udp_receive(Socket, Data, From, Options) :-
    udp_receive(Socket, Data, From, Options),
    (   dupl_rate(Rate, Decay),
        maybe(Rate)
    ->  assertz(delayed(Socket, Data, From, Decay, duplicate))
    ;   true
    ),
    delay.

udp_receive(Socket, Data, From, _Options) :-
    clause(delayed(Socket, Data1, From1, Rate, Why), true, Ref),
    maybe(Rate),
    !,
    Data = Data1,
    From = From1,
    erase(Ref),
    debug(udp(qos), 'Re-inserting ~w package', [Why]).
udp_receive(Socket, Data, From, Options) :-
    socket:udp_receive(Socket, Data0, From0, Options),
    (   drop_rate(Drop),
        maybe(Drop)
    ->  debug(udp(qos), 'Dropped package', []),
        udp_receive(Socket, Data, From, Options)
    ;   late_rate(Rate, Decay),
        maybe(Rate)
    ->  assertz(delayed(Socket, Data0, From0, Decay, reorder)),
        udp_receive(Socket, Data, From, Options),
        debug(udp(qos), 'Taking package out of order', [])
    ;   Data = Data0,
        From = From0
    ).

delay :-
    delay_rate(Rate, Decay),
    maybe(Rate),
    !,
    get_time(Now),
    repeat,
        sleep(0.010),
        maybe(Decay),
    !,
    get_time(End),
    Delay is round((End-Now)*1000),
    debug(udp(qos), 'Delayed with ~Dms', [Delay]).
delay.
