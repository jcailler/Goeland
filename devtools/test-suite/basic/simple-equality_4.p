% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = f(a)).

fof(eq, axiom, a = b).

fof(eq, axiom, p(b)).

fof(test, conjecture, 
    p(f(f(f(f(a)))))).


