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

Lemma divZ_le z1 z2 : 0 <= z1 -> z1 / z2 <= z1.
Proof.
move=> z1_pos.
have [[z2_spos|z2_neg]|<-] := Z_dec 0 z2; last 2 first.
- suff : z1 / z2 <= 0 by lia.
  suff : z2 * (z1 / z2) >= z1 by nia.
  by apply: Z_mult_div_ge_neg; lia.
- by rewrite Zdiv_0_r; lia.
apply: Zdiv_le_upper_bound; [lia | nia].
Qed.

Lemma eqzP : Equality.axiom Zeq_bool.
Proof.
by move=> z1 z2; case: Zeq_bool (Zeq_bool_if z1 z2) => ?; apply: (iffP idP).
Qed.

HB.instance Definition _ := hasDecEq.Build Z eqzP.
