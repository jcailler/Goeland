% Trivial equality test to check that we don't loop-rewrite
% result: VALID

fof(eq, axiom, a = b).

fof(eq, axiom, c = d).

fof(eq, axiom, p(a, c)).

fof(test, conjecture, 
    p(b, d)).


