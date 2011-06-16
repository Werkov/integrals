:- ensure_loaded(support).
:- ensure_loaded(debug).

% der(+Function, +Variable , -Derivative w/respect to X)
% -- Simple cases --
der(F, X, 0) :- isConst(F, X), !.
der(X, X, 1) :- not(number(X)).

% -- General rules --
% sum/difference
der(A+B, X, DA+DB) :-
%info(['der: ', 'Sum rule on ', A, ' + ', B]),
	der(A, X, DA), der(B, X, DB)
.
der(A-B, X, DA-DB) :-
%info(['der: ', 'Diff rule on ', A, ' - ', B]),
	der(A, X, DA), der(B, X, DB)
.
% product
der(A*B, X, DA*B + A*DB) :-
%info(['der: ', 'Product rule on ', A, '*', B]),
	der(A, X, DA), der(B, X, DB)
.
% ratio
der(A/B, X, (DA*B - A*DB) / (B^2)) :-
%info(['der: ', 'Ratio rule on ', A, '/', B]),
	der(A, X, DA), der(B, X, DB)
.

% -- Concrete rules --
% --- Binary functions ---
% power
der(F^E, X, E*(F^EE)*DF) :-
	isConst(E, X),
%info(['der: ', 'Const exponent power ', F, '^', E]),
	EE = E - 1,
	der(F, X, DF)
.
der(B^F, X, ln(B)*(B^F)*DF) :- 
	isConst(B, X),
%info(['der: ', 'Const base power ', B, '^', F]),
	der(F, X, DF)
.
der(F^G, X, DGL*(F^G)) :-
	isFunc(F, X),
	isFunc(G, X),
%info(['der: ', 'f(x)^g(x) trick with ln ', F, '^', G]),
	der(G*ln(F), X,  DGL)
.

% --- Unary functions ---
der(-A, X, -DA) :- der(A, X, DA).
% trig
der(sin(F), X, cos(F)*DF) :- der(F, X, DF).
der(cos(F), X, -sin(F)*DF) :- der(F, X, DF).
der(tan(F), X, DF/sin(F)^2) :- der(F, X, DF).
% inverse trig
der(asin(F), X, DF/(1-F^2)^0.5) :- der(F, X, DF).
der(acos(F), X, -DF/(1-F^2)^0.5) :- der(F, X, DF).
der(atan(F), X, DF/(1+F^2)) :- der(F, X, DF).
% hyperbolic
der(sinh(F), X, cosh(F)*DF) :- der(F, X, DF).
der(cosh(F), X, sinh(F)*DF) :- der(F, X, DF).
% cyclometric
der(asinh(F), X, DF/(1+F^2)^0.5) :- der(F, X, DF).
der(acosh(F), X, DF/(1-F^2)^0.5) :- der(F, X, DF).

% logarithm
der(ln(F), X, DF/F) :- der(F, X, DF).
der(exp(F), X, D) :- der(e^F, X, D).


