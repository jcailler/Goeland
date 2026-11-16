% args: -l 4
% result: NOT VALID
%
% A chain of metavariable-to-metavariable bindings that must reach the father.
%
% The axioms give a witness for left and a witness for right, so
% ? [W, X] : left(W) & right(X) holds and the conjecture denying it does not.
% The axioms are consistent: two elements, goal on the right one only.
%
% The tableau closes its branches with
%
%   ~left(U15)         against left(skolem@W11@0)    -> U15 |-> skolem@W11@0
%   ~right(U17)        against right(skolem@X13@1)   -> U17 |-> skolem@X13@1
%   ~rightbis(U19)     against rightbis(U17)         -> U19 |-> U17
%   rightbisbis(U19)   against ~rightbisbis(U21)     -> U21 |-> U19
%   goal(U21)          against ~goal(U15)            -> U21 |-> U15
%
% so U21 reaches the right witness one way and the left witness the other, and
% the two Skolem constants would have to be the same. The chain crosses two
% metavariable-to-metavariable bindings, which RemoveElementWithoutMM used to
% drop: the constraint never reached the father, and nothing noticed the two
% branches disagreed. The rightbis/rightbisbis steps are there to lengthen the
% chain, and -l 4 sets how many reintroductions it gets.
%
% Refs: #76

fof(two_elements, axiom,
    a != b ).

fof(a_left, axiom,
    ? [W] : left(W) ).

fof(a_right, axiom,
    ? [X] : right(X) ).

fof(left_has_no_goal, axiom,
    ! [U] : ( left(U) => ~ goal(U) ) ).

fof(right_is_rightbis, axiom,
    ! [U] : ( right(U) => rightbis(U) ) ).

fof(rightbis_is_rightbisbis, axiom,
    ! [U] : ( rightbis(U) => rightbisbis(U) ) ).

fof(rightbisbis_has_goal, axiom,
    ! [U] : ( rightbisbis(U) => goal(U) ) ).

fof(no_left_and_right, conjecture,
    ~ ? [W, X] : ( left(W) & right(X) ) ).
