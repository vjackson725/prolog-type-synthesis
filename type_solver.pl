
% Unit
context(Env, unit, unit, unit, N).

% Var
context(Env, X, T, var, N) :-
    N >= 0,
    member((X, T), Env),
    not(compound(X)).

% App
context(Env, app(A0, A1), T1, app(Proof1, Proof2), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, A0, arr(T0, T1), Proof1, N1),
    context(Env, A1, T0, Proof2, N1),
    acyclic_term(T0).

% Abs
context(Env, lam(X, A), arr(T0, T1), abs(Proof, [(X, T0) | Env]), N) :-
    N >= 0,
    N1 is N-1,
    context([(X, T0) | Env], A, T1, Proof, N1),
    not(compound(X)).

% prod
%% const
context(Env, prod(A, B), prod(Ta, Tb), and(Proof1, Proof2), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, A, Ta, Proof1, N1),
    context(Env, B, Tb, Proof2, N1).

%% destr
context(Env, fst(C), Ta, fst(P), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, C, prod(Ta, _), P, N1).

context(Env, snd(C), Tb, snd(P), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, C, prod(_, Tb), P, N1).

% disj
%% const
context(Env, inl(A), disj(Ta,_), disjA(P), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, A, Ta, P, N1).

context(Env, inr(B), disj(_,Tb), disjB(P), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, B, Tb, P, N1).

%% destr
context(Env, disjE(Fac,Fbc,Inj), Tc, disjE(P1, P2, P3), N) :-
    N >= 0,
    N1 is N-1,
    context(Env, Inj, disj(Ta, Tb), P3, N1),
    context(Env, Fac, arr(Ta, Tc), P1, N1),
    context(Env, Fbc, arr(Tb, Tc), P2, N1).
