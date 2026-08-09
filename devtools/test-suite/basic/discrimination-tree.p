% Exercises the discrimination tree index instead of the code trees.
% args: -dt
% result: VALID

fof(a1, axiom, p(a)).
fof(a2, axiom, ! [X] : ( p(X) => q(f(X)) )).
fof(a3, axiom, ! [Y] : ( q(f(Y)) => r(Y) )).
fof(goal, conjecture, r(a)).
