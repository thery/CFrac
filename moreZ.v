From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype.
From mathcomp Require Import  bigop.
Require Import ZArith Znumtheory Lia.
Delimit Scope ring_scope with RR.
Open Scope Z_scope.

(******************************************************************************)

Import Monoid.

HB.instance Definition _ := 
  isComLaw.Build Z 0 Zplus Zplus_assoc Zplus_comm Zplus_0_l.

Lemma prime_5 : prime 5.
Proof.
apply: prime_intro => [|[]]; try by lia.
case => /=; try lia; last by move=> _; apply: rel_prime_1.
  case => /=; try lia.
  move=> _; apply/rel_prime_sym/rel_prime_mod_rev; try by lia.
  apply: rel_prime_le_prime; first by apply: prime_3.
  have -> : (5 mod 3 = 2)%Z by [].
  by lia.
case => /=; try by lia.
  case => /=; try by lia.
  move=> _; apply/rel_prime_sym/rel_prime_mod_rev; try by lia.
  by apply: rel_prime_1.
move=> _; apply/rel_prime_sym/rel_prime_mod_rev; try by lia.
by apply: rel_prime_1.
Qed.
