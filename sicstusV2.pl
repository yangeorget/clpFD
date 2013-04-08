% Francois FAGES
% April 96

% Portability file for Sicstus Version 2

'.=\='(X,Y) :- noteq(X,Y).  %'.=\\=' in Sicstus 3

create_mutable(X,f(X)).
get_mutable(X,f(X)).
update_mutable(V,A):-setarg(1,A,V).

:- nogc.
