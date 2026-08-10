% result: NOT VALID
%
% Rigid basic superposition instantiates the two sides of an equation
% independently.
%
% From ! [X] : g(X) = h(X) and p(g(a)), Goeland derives p(h(b)).
% It is not a consequence: take the domain {1, 2} with a = 1, b = 2,
% g and h the identity and p = {1}. Both axioms hold and p(h(b)) is false.
%
% applyEQRule replaces the matched subterm by the equation's right-hand side
% *as it stands*, without applying the matcher's substitution to it, so the
% variables of that side stay free and can be bound to something else later.
% Rewriting g(a) yields h(X) rather than h(a), and h(X) then unifies with h(b).
%
% Runs with the equality reasoner only: -noeq finds no proof.

fof(a1, axiom,
    ! [X] : g(X) = h(X) ).

fof(a2, axiom,
    p(g(a)) ).

fof(c1, conjecture,
    p(h(b)) ).
