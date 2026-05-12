% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = f(a)).

fof(eq, axiom, p(a)).

fof(test, conjecture, 
    p(f(f(f(f(a)))))).


