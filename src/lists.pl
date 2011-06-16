% conc(+List, +List, -List)
conc([], A, A).
conc([H|T], B, [H|C]) :- conc(T, B, C).

% delete(+List, +What, -Result) deletes first occurence
delete([], _, []).
delete([H|T], H, T).
delete([H|T], E, [H|DT]) :- H \= E, delete(T, E, DT).

% anonym(+N, -List) creates list of N anonymous variables (main use is for coutning)
create(0, []).
create(N, [_|T]) :- NN is N-1, create(NN, T).

% inverse(+List, -List) inverts (numerically) elements in a list
inverse([], []).
inverse([H|T], [H^ -1| IT]) :- inverse(T, IT).

% negate(+List, -List) inverts (numerically) elements in a list
negate([], []).
negate([H|T], [-H| IT]) :- negate(T, IT).

% split(+List, -List, -List) splits list into two disjoint lists
split([], [], []).
split([H|T], [H|STA], STB) :- split(T, STA, STB).
split([H|T], STA, [H|STB]) :- split(T, STA, STB).
