:- ensure_loaded(normalize).
:- ensure_loaded(lists).

% Returns true iff given expression is a function of X.
% isFunc(+Expression, +Variable)
isFunc(A+B, X) :- once(isFunc(A, X); isFunc(B, X)), !.
isFunc(A-B, X) :- once(isFunc(A, X); isFunc(B, X)), !.
isFunc(A*B, X) :- once(isFunc(A, X); isFunc(B, X)), !.
isFunc(A/B, X) :- once(isFunc(A, X); isFunc(B, X)), !.
isFunc(A^B, X) :- once(isFunc(A, X); isFunc(B, X)), !.

isFunc(A, X) :- A =.. [_, Arg], isFunc(Arg, X), !.

isFunc(X, X) :- atom(X). 

% syntactic sugar
isConst(F, X) :- not(isFunc(F, X)).


% -- Tools for terms manipulation --
% --- signs ---
not(plus, minus).
not(minus, plus).
mul(minus, X, NX) :- not(X, NX).
mul(plus, X, X).
apply(plus, X, X).
apply(minus, -X, X) :- !.
apply(minus, X, -X).



% --- products ---
% factors(+Term, -Factors, -Inverse factors)
factors(A*B, FS, IFS) :- factors(A, FA, IFA), factors(B, FB, IFB), conc(FA, FB, FS), conc(IFA, IFB, IFS), !.
factors(A/B, FS, IFS) :- factors(A, FA, IFA), factors(B, FB, IFB), conc(FA, IFB, FS), conc(IFA, FB, IFS), !.
factors(-A, FS, IFS) :- factors(A, TmpFS, IFS), conc(TmpFS, [-1], FS), !.
factors(A, [A], []) :- A \= _*_, A \= _/_, A \= -_.

% factGroups(+factor list, -constant factor, -sign, -rest of factors)
factGroups([], 1, plus, []).
factGroups([H|T], RC, RNeg, RRest) :- number(H), H >= 0, factGroups(T, C, RNeg, RRest), RC is C*H, !.
factGroups([H|T], RC, RNeg, RRest) :- number(H), H < 0, factGroups(T, C, Neg, RRest), RC is C* -H, not(Neg, RNeg), !.
factGroups([H|T], RC, RNeg, [H|Rest]) :- H \= -_, factGroups(T, RC, RNeg, Rest), !.
factGroups([-H|T], RC, RNeg, [H|Rest]) :- factGroups(T, RC, Neg, Rest), not(Neg, RNeg), !.


% product(+constant factor, +sign, +factors, -resulting term)
product(C, minus, Factors, -Result) :- prod(Factors, C, Result).
product(C, plus, Factors, Result) :- prod(Factors, C, Result).

%product(C, minus, Factors, -Result) :- product(C, plus, Factors, Result).

%prod(+List, +Acc, -Product)
prod([], Acc, Acc).
prod([H|T], Acc, R) :- number(Acc), Acc =:= 1, prod(T, H, R), !.
prod([H|T], Acc, R) :- prod(T, Acc*H, R).

% product(+constant factor, +sign, +factors, +inverse factors, -resulting term)
product(C, Sign, FS, [], R) :- product(C, Sign, FS, R), !. 
product(C, Sign, [], IFS, R) :- apply(Sign, C, SC), R = SC/IP, product(1, plus, IFS, IP), !. 
product(C, Sign, FS, IFS, R) :- R = P/IP, product(C, Sign, FS, P), product(1, plus, IFS, IP). 

% product(+factors, -resulting term)
product(Factors, R) :- product(1, plus, Factors, R).

% factorize(+Term, -Constant factor, -Factors)
factorize(T, C, R) :-
	factors(T, FS, IFS),
	inverse(IFS, IIFS), conc(FS, IIFS, Factors),
	factGroups(Factors, UC, Sign, R), apply(Sign, UC, C)
.

% --- sums ---
addends(A+B, FS, IFS) :- addends(A, FA, IFA), addends(B, FB, IFB), conc(FA, FB, FS), conc(IFA, IFB, IFS), !.
addends(A-B, FS, IFS) :- addends(A, FA, IFA), addends(B, FB, IFB), conc(FA, IFB, FS), conc(IFA, FB, IFS), !.
addends(-B, IFB, FB) :- addends(B, FB, IFB), !.
addends(A, [A], []) :- A \= _+_, A \= _-_, A \= -_, !.

% sumGroups(+addends list, -absoulte addend, -rest of addends)
sumGroups([], 0, []).
sumGroups([H|T], RC, RRest) :- number(H), sumGroups(T, C, RRest), RC is C+H, !.
sumGroups([-H|T], RC, RRest) :- number(H), sumGroups(T, C, RRest), RC is C-H, !.
sumGroups([H|T], RC, [H|Rest]) :- sumGroups(T, RC, Rest), !.

% prod(+List, +Acc, -Sum)
sumAcc([], Acc, Acc).
sumAcc([H|T], Acc, R) :- number(Acc), Acc =:= 0, sumAcc(T, H, R), !.
sumAcc([H|T], Acc, R) :- sumAcc(T, Acc+H, R).

% sum(+absolute addend, +addends, -resulting term)
sum(C, Addends, R) :- sumAcc(Addends, C, R).

% sum(+absolute addend, +addends, +inverse addends, -resulting term)
sum(C, FS, [], R) :- sum(C, FS, R), !. 
sum(C, [], IFS, R) :- C =:= 0, R = -IP, sum(0, IFS, IP), !. 
sum(C, [], IFS, R) :- R = C-IP, sum(0, IFS, IP), !. 
sum(C, FS, IFS, R) :- R = P-IP, sum(C, FS, P), sum(0, IFS, IP). 

% sum(+Addends list, -Resulting term)
sum(Addends, R) :- sum(0, Addends, R).

% addends(+Term, -Addends)
addends(T, R) :-
	addends(T, FS, IFS),
	negate(IFS, IIFS), conc(FS, IIFS, Addends),
	sumGroups(Addends, C, RR),
	once((C \= 0, R = [C|RR]) ; (C = 0, R = RR))
.

% --- powers ---
powers(A^B, [B|FA], Base) :- powers(A, FA, Base), !.
powers(A, [], A) :- A \= _^_, !.

% --- reducing ---
% reduce(+factor list, +inverse factor list, -reduced factor list, -reduced inverse factor list)
reduce([], IA, [], IA).
reduce(A, [], A, []).
reduce([H|T], IA, DA, DIA) :- member(H, IA), delete(IA, H, TIA), reduce(T, TIA, DA, DIA). % reduce first element
reduce([H|T], IA, [H|DA], DIA) :- not(member(H, IA)), reduce(T, IA, DA, DIA). % reduce another element

% improved reducing
% reduce(+factor list, +inverse factor list, -reduced factor list, -reduced inverse factor list, +type)
reduce([], IA, [], IA, _).
reduce(A, [], A, [], _).

%reduce([H^N|T], IA, DA, DIA) :- member).

% reduce(+List, +Term, +Amount, -New list, +Type)
reduce(L, _, A, L, pow) :- A =< 0, !.
reduce([Term|T], Term, _, T, pow).
reduce([Term^N|T], Term, A, [Term^NE|TR], pow) :-
	number(N),
	NE is min(N, A),
	Diff is A - NE,
	reduce(T, Term, Diff, TR, pow)
.
reduce([H|T], Term, A, [H|TR], pow) :-
	H \= Term^_, H \= Term,
	reduce(T, Term, A, TR, pow)
.

% swapNeg(+addend list, +alternate addend list, -rest, -alternate addend list)
swapNeg([], IA, [], IA).
swapNeg([-H|T], IA, DA, [H|DIA]) :- swapNeg(T, IA, DA, DIA), !.
swapNeg([H|T], IA, [H|DA], DIA) :- swapNeg(T, IA, DA, DIA).

% removeEqual(+List, +Term, -List) % removes all equal terms from list
removeEqual([], _, []).
removeEqual([H|T], Term, R) :- equal(H, Term), removeEqual(T, Term, R), !.
removeEqual([H|T], Term, [H|R]) :- removeEqual(T, Term, R).

% --- substitutions ---

% substitutes occurencies of What with What in Term
% substitued term must unify
%   subst(+Term, +What, +Replacement, -Result)
subst(T, T, R, R) :- !.
subst(T, W, V, R) :- T =.. [Name, Arg], subst(Arg, W, V, SR), R =..[Name, SR], !.
subst(T, W, V, R) :-
	T =.. [Name, Arg1, Arg2],
	subst(Arg1, W, V, SR1),
	subst(Arg2, W, V, SR2),
	R =..[Name, SR1, SR2], !
.
subst(T, _, _, T).

% Tries substitution, when impossible, fails.
% subst2(+Term, +What, +Replacement, -Result)
subst2(T, T, R, R) :- !.
subst2(T, W, V, R) :- T =.. [Name, Arg], subst2(Arg, W, V, SR), R =..[Name, SR], !.
subst2(T, W, V, R) :-
	T =.. [Name, Arg1, Arg2],
	subst2(Arg1, W, V, SR1), 
	subst2(Arg2, W, V, SR2),
	R =..[Name, SR1, SR2], !
.
subst2(T, W, V, R) :-
	T =.. [Name, Arg1, Arg2],
	subst2(Arg1, W, V, SR1),
	R =..[Name, SR1, Arg2], !
.
subst2(T, W, V, R) :-
	T =.. [Name, Arg1, Arg2],
	subst2(Arg2, W, V, SR2),
	R =..[Name, Arg1, SR2], !
.
%subst2(T, _, _, T).

% --- equality of expressions ---
equal(X, X).
equal(A*B, CA*CB) :- equal(A, CA), equal(B, CB).
equal(A*B, CB*CA) :- equal(A, CA), equal(B, CB).
equal(A+B, CA+CB) :- equal(A, CA), equal(B, CB).
equal(A+B, CB+CA) :- equal(A, CA), equal(B, CB).
equal(A, CA) :- A =.. [Un, Arg1], CA =.. [Un, Arg2], equal(Arg1, Arg2).

