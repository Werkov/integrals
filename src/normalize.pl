% -- Term simplification --
% nulary
norm(N, -NN) :- number(N), N < 0, NN is -N, !.
norm(A, A) :- atomic(A), !.
% unary
norm(ln(e), 1) :- !.
norm(exp(X), e^X) :- !.
norm(A, R) :- functor(A, Name, 1), arg(1, A, Arg), norm(Arg, SArg), R =..[Name, SArg], !.
% binary
norm(A*B, R) :-
	norm(A, SA), norm(B, SB),
	factors(SA*SB, FS, IFS),
	muldiv(FS, IFS, R)
.
norm(A/B, R) :-
	factors(A/B, FS, IFS),
	muldiv(FS, IFS, R)
.
norm(A+B, R) :-
	addends(A+B, FS, IFS),
	adddif(FS, IFS, R)
.
norm(A-B, R) :-
	addends(A-B, FS, IFS),
	adddif(FS, IFS, R)
.
norm(A^B, R) :-
	powers(A^B, FS, TBase),
	norm(TBase, Base),
	muldiv(FS, [], T),
	once(
	(number(T), T =:= 0, R = 1);
	(number(T), T =:= 1, R = Base);
	(number(T), number(Base), R is Base^T);
	R = Base^T	
	)
.
% lists of nodes
norm([], []).
norm([H|T], [SH|NT]) :- norm(T, NT), norm(H, SH).

muldiv(FS, IFS, R) :-
	norm(FS, SFS), factGroups(SFS, C, Neg, Rest), % normalize members, collapse numbers
	norm(IFS, SIFS), factGroups(SIFS, IC, INeg, IRest),
	RC is C / IC,
	mul(Neg, INeg, RNeg),
	inverse(IRest, IIRest), conc(Rest, IIRest, Factors), % merge into one list
	norm(Factors, FF), collapse(FF, ColFS), norm(ColFS, FinFS), % actually does reducing
	(
		(RC =:= 0, R = 0) ; invElems(FinFS, PosFS, NegFS), % to rewrite as a fraction
		unElems(PosFS, TmpPosFS), unElems(NegFS, TmpNegFS), % first power is "no" power
		removeEqual(TmpPosFS, 1, FinPosFS), removeEqual(TmpNegFS, 1, FinNegFS),
		(RC =\= 0, product(RC, RNeg, FinPosFS, FinNegFS, R))
	), !
.
adddif(FS, IFS, R) :-
	norm(FS, SFS0), norm(IFS, SIFS0),
	swapNeg(SFS0, SIFS0, SFS1, SIFS1), % correct lists after normalization (we could've got some negative members)
	swapNeg(SIFS1, SFS1, SIFS, SFS),
	sumGroups(SFS, C, Rest),
	sumGroups(SIFS, IC, IRest),
	RC is C - IC,
	reduce(Rest, IRest, RRest, RIRest),
	sum(RC, RRest, RIRest, R), !
.

% expanding/collapsing

% remove(+List, +Term, +Count, -List) % removes muls/pows of Term from list, returns sum of pows/muls and filtered list
remove([], _, 0, []).
remove([Term|T], Term, Cnt, FL) :- remove(T, Term, FC, FL), Cnt = FC + 1.
remove([Term^N|T], Term, Cnt, FL) :- remove(T, Term, FC, FL), Cnt = FC + N.
remove([H|T], Term, Cnt, [H|FL]) :- H \= Term, H \= Term^_, remove(T, Term, Cnt, FL).

% collapse(+List, -List) % collapses all occurencies of same terms
collapse([H^N|T], [H^M|List]) :- remove(T, H, Cnt, TList), M = N+Cnt, collapse(TList, List).
collapse([H|T], [H^M|List]) :- H \= _^_, remove(T, H, Cnt, TList), M = 1+Cnt, collapse(TList, List).
collapse([], []).

% invElems(+List, -List, -List) % splits list into positive and negative elements
invElems([], [], []).
invElems([H^ -Exp|T], Pos, [H^Exp|Neg]) :- invElems(T, Pos, Neg).
invElems([H^ Exp|T], [H^Exp| Pos], Neg) :- Exp \= -_, invElems(T, Pos, Neg).
invElems([H|T], [H|Pos], Neg) :- H \= _^_, invElems(T, Pos, Neg).

% unElems(+List, -List)
unElems([], []).
unElems([H^1|T], [H|UT]) :- unElems(T, UT), !.
unElems([H|T], [H|UT]) :- unElems(T, UT).
