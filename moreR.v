From HB Require Import structures.
Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype bigop.
Require Import Zpower.
Delimit Scope ring_scope with RR.

Open Scope R_scope.

(*******************************************************************************)

Coercion IZR : Z >-> R.

Definition nsINR := nosimpl INR.
Coercion nsINR : nat >-> R.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Import Monoid.

HB.instance Definition _ := 
  isComLaw.Build R 0 Rplus RplusA Rplus_comm Rplus_0_l.

(* Some auxillary facts                                                       *)

Fact INR0 : 0%N = 0 :> R.
Proof. by rewrite /nsINR. Qed.

Fact S_INR m : (m.+1)%N = m + 1 :> R.
Proof. by exact: S_INR. Qed.

Fact plus_INR m n : (m + n)%N = m + n :> R.
Proof. by exact: plus_INR. Qed.

Fact minus_INR m n : (n <= m)%N -> (m - n)%N = m - n :> R.
Proof. by move=> nLm; apply/minus_INR/leP. Qed.

Lemma iterR_cons n v : iter n (Rplus v) 0 = n * v.
Proof.
elim: n=> [/=|n IH]; first by rewrite INR0; lra.
rewrite iterS IH -addn1 !plus_INR S_INR INR0; lra.
Qed.

Lemma big_const_R m n r : \big[Rplus/0]_(m <= i < n) r =  (n - m)%N * r.
Proof. by rewrite big_const_nat iterR_cons. Qed.

(******************************************************************************)
(* Borrowed to flocq                                                          *)
(******************************************************************************)

(* Floor function                                                             *)
Definition Zfloor (x : R) := (up x - 1)%Z.

Notation "`[ x ]" := (Zfloor x).

Lemma Zfloor_bound x : `[x] <= x < `[x] + 1.
Proof.
rewrite /Zfloor minus_IZR /=.
have [] := archimed x; lra.
Qed.

Lemma Zfloor_lub (z : Z) x : z <= x -> (z <= `[x])%Z.
Proof.
move=> H.
suff: (z < Zfloor x + 1)%Z by lia.
apply: lt_IZR; rewrite plus_IZR /=.
have [] := Zfloor_bound x; lra.
Qed.

Lemma Zfloor_eq (z : Z) x :  z <= x < z + 1 -> `[x] = z.
Proof.
move=> xB.
have ZxB := Zfloor_bound x.
suff : (Zfloor x < z + 1 /\ z <= Zfloor x)%Z by lia.
split; last by apply: Zfloor_lub; lra.
apply : lt_IZR; rewrite plus_IZR /=; lra.
Qed.

Lemma ZfloorZ (z : Z) : `[z] = z.
Proof. apply: Zfloor_eq; lra. Qed.

Lemma Zfloor_le x y : x <= y -> (`[x] <= `[y])%Z.
Proof.
move=> H; apply: Zfloor_lub.
have := Zfloor_bound x; lra.
Qed.

Lemma Zfloor_addz (z: Z) x : `[x + z] = (`[x] + z)%Z.
Proof.
have ZB := Zfloor_bound x.
by apply: Zfloor_eq; rewrite plus_IZR; lra.
Qed.

Lemma ZfloorD_cond r1 r2 : 
  if Rle_dec (`[r1] + `[r2] + 1) (r1 + r2)
  then `[r1 + r2] = (`[r1] + `[r2] + 1)%Z
  else  `[r1 + r2] = (`[r1] + `[r2])%Z.  
Proof.
have [Zr1 Zr2] := (Zfloor_bound r1, Zfloor_bound r2).
case: Rle_dec => H /=.
  apply: Zfloor_eq; rewrite plus_IZR plus_IZR /=; lra.
apply: Zfloor_eq; rewrite plus_IZR; lra.
Qed.

(******************************************************************************)


(* Fractional part                                                            *)
Definition frac_part x := x - Zfloor x.

Notation "`{ r }" := (frac_part r).

Lemma frac_bound x : 0 <= `{x} < 1.
Proof. rewrite /frac_part; have := Zfloor_bound x; lra. Qed.

Lemma frac_inv r : (0 <= r < 1) -> `{r} = r.
Proof.
move=> [/Zfloor_le rP rL1]; rewrite (ZfloorZ 0) in rP.
rewrite /frac_part.
suff -> : `[r] = 0%Z by rewrite /=; lra.
suff /(lt_IZR _ 1) F : `[r] < 1 by lia.
have H1 := Zfloor_bound r; lra.
Qed.

Lemma frac_addz (z : Z) x :  `{x + z} = `{x}.
Proof. rewrite /frac_part; rewrite Zfloor_addz plus_IZR; lra. Qed.

Lemma fracB_eq0 r1 r2 : `{r1} = `{r2} -> `{r1 - r2} = 0.
Proof.
rewrite /frac_part => H1.
have->: r1 - r2 = (`[r1] - `[r2])%Z by rewrite minus_IZR; lra.
rewrite ZfloorZ; lra.
Qed.

Lemma fracZ (z: Z) : `{z} = 0.
Proof. rewrite /frac_part ZfloorZ; lra. Qed.

Lemma frac_eq r1 r2 : `{r1 - r2} = 0 -> `{r1} = `{r2}.
Proof. 
rewrite /frac_part=> H1.
have {2}-> : r1 = r2 + (r1 - r2) by lra.
have DE : r1 - r2 = `[r1 - r2] by lra.
rewrite DE Zfloor_addz plus_IZR -DE; lra.
Qed.

Lemma fracD r1 r2 : `{r1 + r2} = `{`{r1} + `{r2}}.
Proof.
rewrite -(frac_addz ((- `[r1] - `[r2])%Z)) minus_IZR opp_IZR.
congr (`{_}); rewrite /frac_part; lra.
Qed.

Lemma fracD_cond r1 r2 :
  if Rle_dec 1 (`{r1} + `{r2})  then `{r1 + r2} = `{r1} + `{r2} - 1
  else  `{r1 + r2} = `{r1} + `{r2}.
Proof.
rewrite /frac_part.
have:= ZfloorD_cond r1 r2.
(do 2 case: Rle_dec) => /= H1 H2 ->; rewrite ?plus_IZR /=; lra.
Qed.

Lemma fracB r1 r2 : `{r1} <= `{r2} -> `{r2 - r1} = `{r2} - `{r1}.
Proof.
move=> r1Lr2.
have := fracD_cond (r2 - r1) r1.
have->: r2 - r1 + r1 = r2 by ring.
case: Rle_dec => U /=; try lra.
case: (frac_bound (r2 - r1)); lra.
Qed.

Lemma fracK r : `{`{r}} = `{r}.
Proof.
have {1}->: `{r} = `{r} + `{0} by rewrite (fracZ 0); lra.
rewrite -fracD; congr `{_}; lra.
Qed.

Lemma fracN r : `{r} <> 0 -> `{-r} = 1 - `{r}.
Proof.
rewrite /frac_part => rD0.
suff->: `[-r] = (- `[r] - 1)%Z.
  rewrite minus_IZR opp_IZR /=; lra.
apply: Zfloor_eq; rewrite minus_IZR !opp_IZR /=.
have := Zfloor_bound r; lra.
Qed.

Lemma fracN_NZ r : `{r} <> 0 -> `{-r} <> 0.
Proof. move=> rNZ; rewrite fracN //; have := frac_bound r; lra. Qed.

Lemma fracNZ_N r : `{-r} <> 0 -> `{r} <> 0.
Proof. rewrite -{2}[r]Ropp_involutive; exact: fracN_NZ. Qed.
  
Lemma frac_inv_gt_1 r : `{r} <> 0 -> 1 < 1 / `{r}.
Proof.
have F1 := frac_bound r => Dr.
rewrite -{1}Rinv_1 /Rdiv Rmult_1_l.
apply: Rinv_lt_contravar; lra.
Qed.

Lemma frac_inv_floor_ge_1 r : `{r} <> 0 -> (1 <= `[1 / `{r}])%Z.
Proof.
move=> Dr.
rewrite -{1}(ZfloorZ 1); apply: Zfloor_le => /=.
by have := frac_inv_gt_1 _ Dr; lra.
Qed.

(**********************************************************)
(* Sign *)

Notation "a ^+ b"  := (Zpower_nat a b) : Z_scope.
Notation Zpower_natS := Zpower_nat_succ_r.

Lemma Zpower_nat_signE n : ((-1)^+ n = 1 \/ (-1)^+ n = -1)%Z.
Proof. by (elim: n => [|n IH]); [left | rewrite Zpower_natS; lia]. Qed.

Lemma Zpower_nat_IZR (a : Z) n : (a ^+ n)%Z = a ^ n :> R.
Proof. by elim: n => //= n IH; rewrite -Zpower_natS mult_IZR IH. Qed.

Lemma Rpower_signE n : (-1)^ n = 1 \/ (-1)^ n = -1.
Proof. by (elim: n => [|n IH]); [left | rewrite /=; lra]. Qed.

Lemma Zpower_nat_sign_odd n : ((-1)^+ n = if odd n then -1 else 1)%Z.
Proof.
elim: n => [//| n IH].
rewrite Zpower_natS IH [odd _.+1]/=; case: odd => /=; lia.
Qed.

Lemma Rpower_sign_odd n : (-1)^  n = if odd n then -1 else 1.
Proof. by elim: n => //= n ->; case: odd=> /=; lra. Qed.


(**********************************************************)

Definition Rmod1 r := Rmin `{r} (1 - `{r}).

Notation "`| r |" := (Rmod1 r) : R_scope.

Lemma Rmod1_pos r : 0 <= `|r| < 1.
Proof.
by rewrite /Rmod1 /Rmin; case: Rle_dec; have := frac_bound r; lra.
Qed.

Lemma Rmod1_def r : 
  `|r| = Rabs (r - (1 + `[r])%Z) \/ `|r| = Rabs (r - `[r]).
Proof.
have := Zfloor_bound r.
rewrite /Rmod1 /Rmin /frac_part plus_IZR /=.
case: Rle_dec; split_Rabs; try lra.
Qed.

Lemma Rmod1_min r (p : Z) : `|r| <= Rabs (r - p).
Proof.
have Br := Zfloor_bound r.
have [/IZR_le|/IZR_le] : (p <= `[r] \/ 1 + `[r] <= p)%Z by lia.
  rewrite /Rmod1 /Rmin /frac_part plus_IZR /=.
  case: Rle_dec; split_Rabs; try lra.
rewrite /Rmod1 /Rmin /frac_part !plus_IZR /=.
case: Rle_dec; split_Rabs; try lra.
Qed.


(******************************************************************************)
(*                               Comparison                                   *)
(******************************************************************************)



Lemma ler_Rdivr a b c : 0 < c -> a * c <= b -> a <= b / c.
Proof.
move=> cP abLc.
apply: Rmult_le_reg_r (cP) _.
rewrite Rmult_assoc Rinv_l; nra.
Qed.

Lemma ltr_Rdivl a b c : 0 < b -> a < b * c -> a / b  < c.
Proof.
move=> bP aLbc.
apply: Rmult_lt_reg_r (bP) _.
rewrite Rmult_assoc Rinv_l; nra.
Qed.
