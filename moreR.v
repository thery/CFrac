From HB Require Import structures.
Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype.
From mathcomp Require Import bigop.
Require Import Zpower Znumtheory moreZ.
Delimit Scope ring_scope with RR.

Open Scope R_scope.

(******************************************************************************)

Coercion IZR : Z >-> R.

Definition nsINR := nosimpl INR.
Coercion nsINR : nat >-> R.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Import Monoid.

HB.instance Definition _ := 
  isComLaw.Build R 0 Rplus RplusA Rplus_comm Rplus_0_l.

HB.instance Definition _ := 
  isAddLaw.Build R Rmult Rplus Rmult_plus_distr_r Rmult_plus_distr_l.

HB.instance Definition _ := isMulLaw.Build R 0 Rmult Rmult_0_l Rmult_0_r.

Lemma IZR_sum (A : Type) (l : list A) (f : A -> Z) : 
  \big[Zplus/0%Z]_(i <- l) (f i) = \big[Rplus/0%R]_(i <- l) IZR (f i) :> R.
Proof.
elim: l => /= [|a l IH]; first by rewrite !big_nil.
by rewrite !big_cons plus_IZR IH.
Qed.

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

Lemma Zfloor_pos r : 0 <= r -> (0 <= `[r])%Z.
Proof. by move=> r_ge_0; rewrite -(ZfloorZ 0); apply: Zfloor_le. Qed.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Notation "`ceil[ x ]" := (Zceil x).

Theorem Zceil_bound x : (`ceil[x] - 1 < x <= `ceil[x])%R.
Proof.
rewrite /Zceil; have := Zfloor_bound (- x).
by rewrite !opp_IZR; lra.
Qed.

Theorem Zfloor_ceil_bound x : (`[x] <= x <= `ceil[x])%R.
Proof.
by have := Zfloor_bound x; have := Zceil_bound x; lra.
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
  
Lemma frac_inv_gt_1 r : `{r} <> 0 -> 1 < / `{r}.
Proof.
have F1 := frac_bound r => Dr.
by rewrite -{1}Rinv_1; apply: Rinv_lt_contravar; lra.
Qed.

Lemma frac_inv_floor_ge_1 r : `{r} <> 0 -> (1 <= `[/ `{r}])%Z.
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

Lemma Rmod1_addz r z : `|r + IZR z| = `|r|.
Proof. by rewrite /Rmod1 frac_addz. Qed.

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

(******************************************************************************)
(*                               Irrational                                   *)
(******************************************************************************)

Definition irrational r := forall p q : Z, IZR p / IZR q <> r.

Lemma irrational_inv r : irrational r -> irrational (/ r).
Proof.
move=> rI p q pqE; have [] := rI q p.
by rewrite -[RHS]Rinv_inv -pqE Rinv_div.
Qed.

Lemma irrational_frac r : irrational r -> irrational `{ r}.
Proof.
move=> rI p q pqE.
have rE : r = `[r] + `{r} by rewrite /frac_part; lra.
have [q_eq0| q_neq0] := Req_dec q 0.
  have [] := rI `[r] 1%Z.
  by rewrite {2}rE -pqE q_eq0 Rdiv_0_r; lra.
have [] := rI (`[r] * q + p)%Z q.
rewrite {2}rE plus_IZR mult_IZR Rdiv_plus_distr pqE.
by field.
Qed.

Lemma irrational_frac_rev r : irrational `{ r} -> irrational r.
Proof.
move=> rI p q pqE.
have rE : r = `[r] + `{r} by rewrite /frac_part; lra.
have [q_eq0| q_neq0] := Req_dec q 0.
  have [] := rI 0%Z 1%Z.
  by rewrite -pqE q_eq0 Rdiv_0_r Rdiv_0_l fracZ.
have [] := rI (- `[r] * q + p)%Z q.
rewrite plus_IZR mult_IZR opp_IZR Rdiv_plus_distr pqE {2}rE.
by field.
Qed.

Lemma sqrt2_irr : irrational (sqrt 2).
Proof.
move=> x y.
have s2G : 1 < sqrt 2.
  by rewrite -sqrt_1; apply: sqrt_lt_1_alt; lra.
elim/Zcomplements.Z_lt_abs_induction: x y => x IH y xyE.
have xxE : (x * x = 2 * y * y)%Z.
  apply: eq_IZR; rewrite !mult_IZR.
  have -> : 2 = sqrt 2 * sqrt 2.
    by have /sqrt_sqrt Hf : 0 <= 2 by lra.
  rewrite -xyE; field => yE.
  by rewrite yE Rdiv_0_r in xyE; lra.
have Ex : Z.even x.
  have := Z.even_mul x x.
  rewrite xxE.
  by rewrite -Zmult_assoc Z.even_mul /=; case: Z.even.
have Ex1 : Zeven x by apply/Zeven_bool_iff.
case: (Zeven_ex x Ex1) => x1 xE.
have Ey : Z.even y.
  have := Z.even_mul y y.
  have -> : (y * y = 2 * x1 * x1)%Z by lia.
  by rewrite -Zmult_assoc Z.even_mul /=; case: Z.even.
have Ey1 : Zeven y by apply/Zeven_bool_iff.
case: (Zeven_ex y Ey1) => y1 yE.
have [x_eq0|x_neq0] := Z.eq_dec x 0.
  have y_eq0 : y = 0%Z by lia.
  suff : sqrt 2 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
have [y_eq0|y_neq0] := Z.eq_dec y 0.
  have x_eq0 : x = 0%Z by lia.
  suff : sqrt 2 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
case: (IH x1 _ y1); first by lia.
rewrite -xyE xE yE !mult_IZR; field.
apply: not_0_IZR; lia.
Qed.

Lemma sqrt5_irr : irrational (sqrt 5).
Proof.
move=> x y.
have s5G : 1 < sqrt 5.
  by rewrite -sqrt_1; apply: sqrt_lt_1_alt; lra.
elim/Zcomplements.Z_lt_abs_induction: x y => x IH y xyE.
have xxE : (x * x = 5 * y * y)%Z.
  apply: eq_IZR; rewrite !mult_IZR.
  have -> : 5 = sqrt 5 * sqrt 5.
    by have /sqrt_sqrt Hf : 0 <= 5 by lra.
  rewrite -xyE; field => yE.
  by rewrite yE Rdiv_0_r in xyE; lra.
have Ex : (5 | x)%Z.
  have /prime_mult[]// : (5 | x * x)%Z by rewrite xxE; exists (y * y)%Z; lia.
  by apply: prime_5.
case: Ex => x1 xE.
have Ey : (5 | y)%Z.
  have /prime_mult[]// : (5 | y * y)%Z.
    have-> : (y * y = 5 * x1 * x1)%Z by lia.
    by exists (x1 * x1)%Z; lia.
  by apply: prime_5.
case: Ey => y1 yE.
have [x_eq0|x_neq0] := Z.eq_dec x 0.
  have y_eq0 : y = 0%Z by lia.
  suff : sqrt 5 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
have [y_eq0|y_neq0] := Z.eq_dec y 0.
  have x_eq0 : x = 0%Z by lia.
  suff : sqrt 5 = 0 by lra.
  by rewrite -xyE x_eq0 y_eq0; lra.
case: (IH x1 _ y1); first by lia.
rewrite -xyE xE yE !mult_IZR; field.
apply: not_0_IZR; lia.
Qed.

Lemma irrational_IZR z : ~ (irrational (IZR z)).
Proof. by move=> /(_ z 1%Z) []; field. Qed.

Lemma frac_neq_0_irrational z : irrational z -> `{z} <> 0.
Proof.
move=> iR fz_eq0; case: (irrational_IZR 0).
by rewrite -fz_eq0; apply: irrational_frac.
Qed.
 
(* Golden Ratio                                                         *)
Definition gr := (1 + sqrt 5) / 2.

Lemma gr_irr : irrational gr.
Proof.
move=> x y grE.
have y_neq_0 : y <> 0%Z.
  move=> y_eq_0; rewrite y_eq_0 /Rdiv Rinv_0 Rmult_0_r in grE.
  have [] := sqrt5_irr (- 1)%Z 1%Z.
  by rewrite /gr in grE; lra.
have yR_neq_0 : IZR y <> 0 by move=> hR; case: y_neq_0; apply: eq_IZR.
case: (sqrt5_irr (2 * x - y)%Z y).
rewrite minus_IZR mult_IZR Rdiv_plus_distr.
have -> : 2 * x / y = 2 * (x / y) by field.
by rewrite grE /gr; field.
Qed.

Lemma sqrt5B : 2 <  sqrt 5 < 3.
Proof.
have -> : 2 = sqrt (2 * 2) by rewrite sqrt_square; lra.
have -> : 3 = sqrt (3 * 3) by rewrite sqrt_square; lra.
by split; apply: sqrt_lt_1; lra.
Qed.

Lemma grB : 1 <  gr < 2.
Proof. by rewrite /gr; have := sqrt5B; lra. Qed.

Lemma floor_grE : `[gr] = 1%Z.
Proof. by apply: Zfloor_eq; have := grB; lra. Qed.

Lemma fract_grE : `{gr} = (sqrt 5 - 1) / 2.
Proof. by rewrite /frac_part floor_grE /gr; lra. Qed.

Lemma fract_gr_revE : / `{gr} = gr.
Proof.
rewrite fract_grE /gr Rinv_div -(Rdiv_mult_r_r gr); last by have := grB; lra.
rewrite -/gr.
suff -> : (sqrt 5 - 1) * gr = 2 by lra.
suff -> : 2 = ((sqrt 5 * sqrt 5) - 1) / 2 by rewrite /gr; lra.
by rewrite sqrt_sqrt; lra.
Qed.

