:- ensure_loaded(support).
:- ensure_loaded(lists).
:- ensure_loaded(debug).

% int(+Function, +Variable , -Primitive function w/respect to Variable) (initializes Info)
int(F, X, PF) :- norm(F, SF),
	createInfo(SF, 3, 3, Info),
	i(SF, X, PF, Info)
.


% int(+Function, +Variable , -Primitive function w/respect to Variable, +Info)
% transfers Info w/out change
int(F, X, PF, Info) :- norm(F, SF), i(SF, X, PF, Info).

% utility for integrating whole lists of functions
intList([F|T], X, [IF|IT], Info) :-
	int(F, X, IF, Info),
	intList(T, X, IT, Info)
.
intList([], _, [], _).

% -- Choosing method --
% i(+Function, +Variable, -Primitive function, +Info)  basic switch to integrating methods

% linearity
i(A+B, X, IA+IB, OInfo) :-
	updatePpInfo(OInfo, NInfo),
	int(A, X, IA, NInfo),
	int(B, X, IB, NInfo), !
.
i(A-B, X, IA-IB, OInfo) :-
	updatePpInfo(OInfo, NInfo),
	int(A, X, IA, NInfo),
	int(B, X, IB, NInfo), !
.

i(A*B, X, A*IB, OInfo) :- updatePpInfo(OInfo, NInfo), isConst(A, X), int(B, X, IB, NInfo), !.
i(A*B, X, B*IA, OInfo) :- updatePpInfo(OInfo, NInfo), isConst(B, X), int(A, X, IA, NInfo), !.

%table
i(F, X, R, Info) :- iTable(F, X, R, Info), !.

% 2nd type substitution
i(F, X, R, OInfo) :-
	updatePpInfo(OInfo, NInfo),
	poss2ndSubst(F, Subs),
	((X = alternate, T = x) ; T = alternate), % switching variables not to collide
	isFunc(Subs, X), % not to substitute for compound constants
	iSubst(F, X, T, Subs, R, NInfo)
.

% per partes
i(F, X, IF, OInfo) :- 
	ipp(F, X, IF, OInfo)
.

% 1st type substitution
i(F, X, R, Info) :-
	updatePpInfo(Info, NInfo),
	((X = alternate, T = x) ; T = alternate), % switching variables not to collide
	smartSubst(F, X, T, SF, Type),
	norm(SF, NSF), setInitPpInfo(NSF, NInfo, NewInfo),
	int(SF, T, Tmp, NewInfo),
	smartSubstInv(Tmp, X, T, R, Type)
.

% - Integrating methods -

% -- Table integrals --
iTable(F, X, F*X, _) :- isConst(F, X).
iTable(X, X, X^2/2, _) :- not(number(X)).

iTable(-A, X, Result, OInfo) :-
	flipSignPpInfo(OInfo, TmpInfo),
	clearFinalPpInfo(TmpInfo, NewInfo),
	int(A, X, PreResult, NewInfo),
	intInfo(_, _, _, _, _, Final, _) = NewInfo,
	once(
		((var(Final); Final = false),
			Result = -PreResult);
		(Final = true,
			Result = PreResult)
	),
	setFinalPpInfo(Final, OInfo)
.


iTable(sin(X), X, -cos(X), _).
iTable(cos(X), X, sin(X), _).
%iTable(tan(X), X, -ln(cos(X)), _).

iTable(A/X, X, A*ln(X), _) :- isConst(A, X).

% iTable(asin(X), X, (1-X^2)^0.5 + X*asin(X)). % should know by per partes
iTable(exp(X), X, IE, Info) :- iTable(e^X, X, IE, Info).
iTable(B^X, X, (B^X)/ln(B), _) :- isConst(B, X).
iTable(X^E, X, (X^(E+1))/(E+1), _) :- isConst(E, X), not(equal(E, -(1))).

% -- Subst of 2nd type --

% iSubst(+Function, +Variable, +Substituent variable, +Substituted term, -Primitive function, +intInfo)
iSubst(F, X, T, TW, IF, Info) :-
	norm(TW, W), der(W, X, TDW), norm(TDW, DW),
	norm(F/DW, TSF), % possibly reduce derivative of substituted expression
	subst(TSF, W, T, SF),
	isConst(SF, X),% check correctness of substitution
	int(SF, T, TIF, Info),
	subst(TIF, T, W, IF)
.

% find possible terms for 2nd type substitution
%  poss2ndSubst(+Function, -Possible term)
%poss2ndSubst(F, R).
myCompound(X) :- compound(X), not((X = -N, number(N))).

poss2ndSubst(F, R) :-
	F =.. [_, R],
	myCompound(R)
.
poss2ndSubst(F, R) :-
	(F =.. [Name, Arg, _]; F =.. [Name, _, Arg]),
	myCompound(Arg),
	(Name = (*); Name = (/); Name = (^)),
	(Arg = R; poss2ndSubst(Arg, R))
.

% -- Per partes integration --

% ipp(+Function, +Variable, -Primitive function, +intInfo)
ipp(F, X, IF, OInfo) :-
	updatePpInfo(OInfo, NInfo),
	identSubst(F, SubF, NInfo, TmpInfo, prod), % expand into product
	ippPrepare(SubF, X, TmpInfo, NNInfo, Outer, Inner),
	identSubst(Inner, SubInner, NNInfo, FinInfo, sum), % expand into sum
	addends(SubInner, Addends), % decompose inner integral into sum of integrals
	ippBody(Outer, Addends, X, FinInfo, IF)
.

% ippPrepare(+Function, +X, +Info, -Info, -Outer, -Inner)
ippPrepare(F, X, Info, NInfo, Outer, Inner) :-
	% split into two factors (and numeric const C), prepare U', V for per partes
	factorize(F, C, Factors), Factors \= [],
	split(Factors, DUF, VF), 
	VF \= [], % this would'nt help with per partes
	once(
		(DUF = [], canDoTrickPpInfo(Info), setTrickPpInfo(Info, NInfo)); % tricky factorization is done only once
		(DUF \= [], NInfo = Info)
	),
	product(DUF, DU), product(VF, V),
	clearFinalPpInfo(NInfo, TmpInfo), % prepare temporary intInfo for this integral
	int(DU, X, TU, TmpInfo), norm(TU, U),
	der(V, X, TV), norm(TV, DV),
	norm(C*U*V, Outer), norm(C*U*DV, Inner) % Inner is new integral, Outer is the outer part
.

% ippBody(+Outer, +Addends, +Variable, ?Info, -IF)
ippBody(Outer, Addends, X, Info, IF) :-
	intInfo(Initial, _, Sign, PrevSum, _, true, _) = Info,
	apply(Sign, Initial, SInitial),
	findInitial(Addends, SInitial, NewAddends, CC), % we're cycling
	apply(Sign, CC, C),
	C =\= -1, % this isn't cyclic per partes
	intList(NewAddends, X, IntNewAddends, Info),
	sum(IntNewAddends, IntPartInner),
	apply(Sign, Outer - IntPartInner, SumChng),
	NewSum = PrevSum + SumChng,
	IF = NewSum / (C+1)
.
ippBody(Outer, Addends, X, Info, IF) :-
	intInfo(Initial, _, Sign, PrevSum, _, true, _) = Info,
	apply(Sign, Initial, SInitial),
	not(findInitial(Addends, SInitial, _, _)), % we're not cycling
	sum(Addends, Inner),
	apply(Sign, Outer, SumChng),
	NewSum = PrevSum + SumChng,
		setSumPpInfo(NewSum, Info, TmpInfo),
		clearFinalPpInfo(TmpInfo, TmpInfo2),
		flipSignPpInfo(TmpInfo2, NewInfo),
	int(Inner, X, IInner, NewInfo),
	intInfo(_, _, _, _, _, Final, _) = NewInfo,
	once(
		((var(Final); Final = false),
			apply(Sign, IInner, SIInner),
			IF = NewSum - SIInner);
		(Final = true, % return obtained result
			IF = IInner)
	)	
.


% findInitial(+List, +Term, -List, -Factor) % tries to find initial Term in List, returns Factor of found term and
%                                             reduced list or fails when not found
findInitial([], _, [], 0) :- fail.
findInitial([H|T], Term, T, N) :-
	factorize(H, N, Factors),
	product(Factors, TmpH),
	norm(TmpH, NewH),
	factorize(Term, _, TFactors),	
	product(TFactors, NewTerm), % process term in the same way to find equality easier
	equal(NewH, NewTerm), !	
.
findInitial([H|T], Term, [H|R], C) :- findInitial(T, Term, R, C).

% -- 1st type substitution --
% smartSubst(+Function, +Variable, +New variable, -New function, -Identifier) % identifier is to match inverse substitution
smartSubst(F, X, T, SF, sin) :-
	subst2(F, X, sin(T), Tmp),
	norm(Tmp * cos(T), Tmp2),
	identSubst(Tmp2, Tmp3, prod),
	identSubst(Tmp3, SF, invSum), % possibly rewrite 1-s^2 to c^2 and similarily for c/s
	norm(Tmp3, NTmp3), % prod does not only expand powers
	norm(SF, NSF), not(equal(NTmp3, NSF)) % use this substitution only if it helps us
.
% smartSubstInv(+Function, +Original variable, +Subs. variable, +New function, +Type)
smartSubstInv(F, X, T, SF, sin) :-
	subst(F, T, asin(X), SF)
.

% - Info utils -
% Info is structure for
%	Initial function, per partes maxdepth, PP sign, sum of previous PP terms, did PP trick, final result by PP
%	subst counter
%	NOTE: PP trick is factorization into 1 and original function
% createInfo(+Function, +Maxdepth, +Maxsubst, -intInfo)
createInfo(Integral, Maxdepth, Maxsubst, Info) :-
	createList(Maxdepth, DepthList),
	createList(Maxsubst, SubstList),
	Info = intInfo(Integral, DepthList, plus, 0, false, _,  SubstList)
.

% createList(+Length, -List) % creates list of anonymous variables of given length 
createList(0, []) :- !.
createList(N, [_|T]) :- NN is N-1, createList(NN, T).

% updatePpInfo(+Old info, -New info)
updatePpInfo(intInfo(Integral, [_|T], Sign, Sum, Trick, Final, Subst), intInfo(Integral, T, Sign, Sum, Trick, Final, Subst)).

% updateSubInfo(+Old info, -New info)
updateSubInfo(intInfo(Integral, PpDepth, Sign, Sum, Trick, Final, [_|T]), intInfo(Integral, PpDepth, Sign, Sum, Trick, Final, T)).

% setSumPpInfo(+Sum, +Old info, -New info)
setSumPpInfo(Sum, intInfo(Integral, Cnt, Sign, _, Trick, Final, Subst), intInfo(Integral, Cnt, Sign, Sum, Trick, Final, Subst)).

% flipSignPpInfo(+Old info, -New info)
flipSignPpInfo(intInfo(Integral, Cnt, OldSign, Sum, Trick, Final, Subst), intInfo(Integral, Cnt, NewSign, Sum, Trick, Final, Subst)) :-
	not(OldSign, NewSign)
.

% setInitPpInfo(+Init, +Info, -Info)
setInitPpInfo(Init, intInfo(_, Cnt, Sign, Sum, Trick, Final, Subst), intInfo(Init, Cnt, Sign, Sum, Trick, Final, Subst)).

% canDoTrickPpInfo(+Info)
canDoTrickPpInfo(intInfo(_, _, _, _, false, _, _)).

% setTrickPpInfo(+Info, -Info)
setTrickPpInfo(intInfo(Integral, Cnt, Sign, Sum, _, Final, Subst), intInfo(Integral, Cnt, Sign, Sum, true, Final, Subst)).

% clearFinalPpInfo(+Old info, -New info)
clearFinalPpInfo(intInfo(Integral, Cnt, Sign, Sum, Trick, _, Subst), intInfo(Integral, Cnt, Sign, Sum, Trick, _, Subst)).

% setFinalPpInfo(+Value, ?Info to update)
setFinalPpInfo(Final, intInfo(_, _, _, _, _, Final, _)).

% updateSubInfo(+OldInfo, -New info)
%updateSubInfo(subInfo([H|T]), subInfo(T)).

% - Ident subst utils -
% if we can do a product substitution we'll do it, leaving expression is last possiblity
% identSubst(+Expression, -Substitued expression, +Old info, -New info, +Type)


% NOTE: invSum because sum types can't be used in reverse direction
% 1-cos(x)*cos(X) = sin(x)*sin(X)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = invSum),
	updateSubInfo(OInfo, TmpInfo),
	subst2(F, 1-cos(X)*cos(X), sin(X)*sin(X), Tmp),
	identSubst(Tmp, G, TmpInfo, NInfo, Type), !
.
% 1-sin(x)*sin(X) = cos(x)*cos(X)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = invSum),
	updateSubInfo(OInfo, TmpInfo),
	subst2(F, 1-sin(X)*sin(X), cos(X)*cos(X), Tmp),	
	identSubst(Tmp, G, TmpInfo, NInfo, Type), !
.

% A^2 = A*A
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = prod),
	updateSubInfo(OInfo, TmpInfo),
	subst2(F, A^2, A*A, Tmp),
	identSubst(Tmp, G, TmpInfo, NInfo, Type), !
.
% A^N = A*A^(N-1)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = prod),
	updateSubInfo(OInfo, TmpInfo),
	subst2(F, A^N, A^NN *A, Tmp), number(N), N > 2,  NN is N-1,
	identSubst(Tmp, G, TmpInfo, NInfo, Type), !
.
% tan(A) = sin(A)/cos(A)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = prod),
	updateSubInfo(OInfo, TmpInfo),
	subst2(F, tan(A), sin(A)/cos(A), Tmp),
	identSubst(Tmp, G, TmpInfo, NInfo, Type), !
.

identSubst(F, F, Info, Info, _). % pure identity isn't counted

% cos(x)*cos(X) = 1 - sin(x)*sin(X)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = sum),
	updateSubInfo(OInfo, TmpInfo),
	identSubst(F, FF, prod),
	subst2(FF, cos(X)*cos(X), 1-sin(X)*sin(X), Tmp),
	identSubst(Tmp, G, TmpInfo, NInfo, Type)
.
% sin(x)*sin(X) = 1 - cos(x)*cos(X)
identSubst(F, G, OInfo, NInfo, Type) :-
	once(var(Type) ; Type = sum),
	updateSubInfo(OInfo, TmpInfo),
	identSubst(F, FF, prod),
	subst2(FF, sin(X)*sin(X), 1-cos(X)*cos(X), Tmp),	
	identSubst(Tmp, G, TmpInfo, NInfo, Type)
.

% identSubst(+Expression, -Substitued expression, +Type) % tries only one ident substitution
identSubst(F, G, Type) :-
	createInfo(_, 0, 1, Info),
	identSubst(F, G, Info, _, Type)
.

