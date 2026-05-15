% Bug all proof output
%------------------------------------------------------------------------------
% File     : SET874+1 : TPTP v9.2.1. Released v3.2.0.
% Domain   : Set theory
% Problem  : union(singleton(A),unordered_pair(A,B)) = unordered_pair(A,B)
% Version  : [Urb06] axioms : Especial.
% English  :
% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t14_zfmisc_1 [Urb06]
% Status   : Theorem
% Rating   : 0.09 v9.1.0, 0.03 v9.0.0, 0.08 v7.5.0, 0.09 v7.4.0, 0.03 v7.1.0, 0.04 v7.0.0, 0.03 v6.4.0, 0.08 v6.2.0, 0.20 v6.1.0, 0.23 v6.0.0, 0.13 v5.5.0, 0.11 v5.4.0, 0.18 v5.3.0, 0.26 v5.2.0, 0.05 v5.0.0, 0.21 v4.1.0, 0.22 v4.0.0, 0.21 v3.7.0, 0.10 v3.5.0, 0.11 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :   11 (   6 unt;   0 def)
%            Number of atoms       :   18 (   8 equ)
%            Maximal formula atoms :    4 (   1 avg)
%            Number of connectives :   13 (   6   ~;   1   |;   0   &)
%                                         (   2 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    8 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    3 (   2 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   0 con; 1-2 aty)
%            Number of variables   :   22 (  20   !;   2   ?)
% SPC      : FOF_THM_RFO_SEQ
% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden, axiom, 
    ! [A, B] :
    (in_p(A, B)
     => ~ in_p(B, A))).

fof(commutativity_k2_tarski, axiom, 
    ! [A, B] :
    unordered_pair(A, B) = unordered_pair(B, A)).

fof(commutativity_k2_xboole_0, axiom, 
    ! [A, B] :
    set_union2(A, B) = set_union2(B, A)).

fof(d2_tarski, axiom, 
    ! [A, B, C] :
    (C = unordered_pair(A, B) <= >! [D] :
    (in_p(D, C) <= >(D = A
    | D = B)))).

fof(fc2_xboole_0, axiom, 
    ! [A, B] :
    (~ empty(A)
     => ~ empty(set_union2(A, B)))).

fof(fc3_xboole_0, axiom, 
    ! [A, B] :
    (~ empty(A)
     => ~ empty(set_union2(B, A)))).

fof(idempotence_k2_xboole_0, axiom, 
    ! [A, B] :
    set_union2(A, A) = A).

fof(l23_zfmisc_1, axiom, 
    ! [A, B] :
    (in_p(A, B)
     => set_union2(singleton(A), B) = B)).

fof(rc1_xboole_0, axiom, 
    ? [A] :
    empty(A)).

fof(rc2_xboole_0, axiom, 
    ? [A] :
    ~ empty(A)).

fof(t14_zfmisc_1, conjecture, 
    ! [A, B] :
    set_union2(singleton(A), unordered_pair(A, B)) = unordered_pair(A, B)).

%------------------------------------------------------------------------------
