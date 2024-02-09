Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype bigop.
Require Import Zpower moreR.

Open Scope R_scope.

(**********************************************************)

(* The approximation process *)
Fixpoint approx (n : nat) (r : R) :=
if n is n1.+1 then
   if n1 is _.+1 then
       let d := `{r} in
       if Req_EM_T d 0 then (0%Z, `[r], 1%Z)
       else let: (a,p,q) := approx n1 (/ d) in
            (a,`[r] * p + q, p)%Z
    else (`[r], `[r], 1%Z)
else (0%Z, 1%Z , 0%Z).

(* The recursive process *)
Lemma approxE n r : approx n.+2 r =
       let d := `{r} in
       if Req_EM_T d 0 then (0%Z, `[r], 1%Z)
       else let: (a,p,q) := approx n.+1 (/ d) in
            (a,`[r] * p + q, p)%Z.
Proof. by []. Qed.

(* Elements of the continued fraction *)

Definition elt r n := 
  let: (a, p, q) := approx n r in a.

Local Notation " 'a[ r ]_ n" := (elt r n) (at level 10, format " ''a[' r ]_ n").

Lemma elt_0 r : 'a[r]_ 0 = 0%Z.
Proof. by []. Qed.

Lemma elt_1 r : 'a[r]_ 1 = `[r].
Proof. by []. Qed.

Lemma eltE_z r n : `{r} = 0 -> 'a[r]_ n.+2 = 0%Z.
Proof. by rewrite /elt approxE; lazy zeta; case: Req_EM_T. Qed.

Lemma eltE n r : `{r} <> 0 ->  ('a[r]_n.+2 = 'a[/ `{r}]_n.+1)%Z.
Proof.
rewrite /elt approxE.
by lazy zeta; case: approx => [[a p] q]; case: Req_EM_T => //=.
Qed.

Lemma elt_pos r n : (0 <= 'a[r]_ n.+2)%Z.
Proof.
elim: n r => [r|n IH r].
  case: (Req_EM_T `{r} 0) => H; first by rewrite !eltE_z.
  rewrite eltE // elt_1.
  by have := frac_inv_floor_ge_1 _ H; lia.
by case: (Req_EM_T `{r} 0) => H; [rewrite !eltE_z|rewrite eltE].
Qed.

Lemma elt_ppos n r : 0 <= r -> (0 <= 'a[r]_ n)%Z.
Proof.
move=> rP.
have F : (0 <= `[r])%Z.
  rewrite -(ZfloorZ 0); apply: Zfloor_le => /=; lra.
by case: n=> [|[|n]]; [rewrite elt_0 | rewrite elt_1 | apply: elt_pos].
Qed.

Lemma elt_eq_0_prevN1  n r : 'a[r]_ n.+3 = 0%Z -> 'a[r]_ n.+2 <> 1%Z.
Proof.
elim: n r => [r|n IH r].
  case: (Req_EM_T `{r} 0) => H; first by rewrite !eltE_z.
  rewrite !(eltE _ r) // elt_1.
  case: (Req_EM_T `{/ `{r}} 0) => H1.
    have F1 := frac_inv_gt_1 _ H => _ HH.
    rewrite {1}/frac_part HH /= in H1; lra.
  rewrite eltE // elt_1.
  by have := frac_inv_floor_ge_1 _ H1; lia.
case: (Req_EM_T `{r} 0) => H; first by rewrite !eltE_z.
by rewrite eltE // => /IH; rewrite -eltE.
Qed.

Lemma elt_eq_0_next  n r : 'a[r]_ n.+2 = 0%Z -> 'a[r]_ n.+3 = 0%Z.
Proof.
elim: n r => [r|n IH r]; last first.
  case: (Req_EM_T `{r} 0) => H.
  rewrite !eltE_z //.
  by rewrite !(eltE _ _ H); exact: IH.
case: (Req_EM_T `{r} 0) => H; first by rewrite !eltE_z.
rewrite !(eltE _ _ H) elt_1 => HH.
by have :=  frac_inv_floor_ge_1 _ H; lia.
Qed.

Lemma elt_neq_0_prev  n r : 'a[r]_ n.+3 <> 0%Z -> 'a[r]_ n.+2 <> 0%Z.
Proof. by have := elt_eq_0_next n r; lia. Qed.

Lemma elt_eq_0 r m n : (1 < m <= n)%N -> 'a[r]_ m = 0%Z -> 'a[r]_ n = 0%Z.
Proof.
case: m => // [[|m]] // /andP[_]; case: n => // [[|n]] //=.
rewrite !ltnS => /subnKC<-; rewrite addnC.
elim: (n - m)%N {-2}m => // k IH m1 /elt_eq_0_next.
by rewrite addSnnS; exact: IH.
Qed.

Lemma irrational_IZR z : ~ (irrational (IZR z)).
Proof. by move=> /(_ z 1%Z) []; field. Qed.

Lemma irrational_elt_neq_0 r n : irrational r -> 'a[r]_ n.+2 <> 0%Z.
Proof.
move=> Hr.
have fr_neq_0 : `{r} <> 0.
  move=> frE.
  by case: (irrational_IZR 0); rewrite -frE; apply: irrational_frac.
elim: n r Hr fr_neq_0 => [|n IH] r Hr fr_neq_0; rewrite eltE //.
  rewrite elt_1.
  have frB : 0 < `{r} <= 1 by have := frac_bound r; lra.
  have ifrB : 1 <= / `{r}.
    by rewrite -Rinv_1; apply: Rinv_le_contravar; lra.
  suff : (1 <= `[ / `{ r}])%Z by lia.
  by apply: Zfloor_lub.
apply: IH; first by apply/irrational_inv/irrational_frac.
move=> ir_eq0.
case: (irrational_IZR 0); rewrite -ir_eq0.
by apply/irrational_frac/irrational_inv/irrational_frac.
Qed.

(* Numerator of the convergent *)

Definition num r n := 
  let: (a, p, q) := approx n r in p.

Local Notation " 'p[ r ]_ n" := (num r n) (at level 10, format " ''p[' r ]_ n").

Lemma num_0 r : 'p[r]_ 0 = 1%Z.
Proof. by []. Qed.

Lemma num_1 r : 'p[r]_ 1 = `[r].
Proof. by []. Qed.

Lemma numE_z r n : `{r} = 0 -> 'p[r]_ n.+1 = `[r].
Proof.
case: n => [|n] Dr; first by rewrite num_1.
by rewrite /num approxE; lazy zeta; case: Req_EM_T.
Qed.
 
(* Denominator of the convergent *)

Definition denom r n := 
  let: (a, p, q) := approx n r in q.

Local Notation " 'q[ r ]_ n" := (denom r n) 
  (at level 10, format " ''q[' r ]_ n").

Lemma denom_0 r : 'q[r]_ 0 = 0%Z.
Proof. by []. Qed.

Lemma denom_1 r : 'q[r]_ 1 = 1%Z.
Proof. by []. Qed.

Lemma denomE_z r n : `{r} = 0 -> 'q[r]_ n.+1 = 1%Z.
Proof. 
case: n => [|n] Dr; first by rewrite denom_1.
by rewrite /denom approxE; lazy zeta; case: Req_EM_T.
Qed.

Lemma denomE n r : `{r} <> 0 -> 'q[r]_n.+1 = 'p[/ `{r}]_n.
Proof.
case: n => [|n]; first by rewrite denom_1 num_0.
rewrite /denom /num approxE.
lazy zeta; case: approx => [[a p] q].
by case: Req_EM_T => //=.
Qed.

Lemma numE n r : `{r} <> 0 -> 
  ('p[r]_n.+1 = `[r] * 'p[/ `{r}]_n + 'q[/ `{r}]_n)%Z.
Proof.
case: n => [|n] Dr; first by rewrite num_1 num_0 denom_0; lia.
rewrite /denom /num /elt approxE.
lazy zeta; case: approx => [[a p] q].
case: Req_EM_T => //=.
Qed.

Lemma approx_pos n r : 0 <= r -> (0 <= 'p[r]_n /\ 0 <= 'q[r]_ n)%Z.
Proof.
elim: n r => [r rP |[|n] IH r rP]; first by rewrite num_0 denom_0; lia.
  rewrite num_1 denom_1.
  by have := Zfloor_le _ _ rP; rewrite (ZfloorZ 0); lia.
have F : (0 <= `[r])%Z by rewrite -(ZfloorZ 0); exact: Zfloor_le.
case: (Req_EM_T `{r} 0) => H; first by rewrite numE_z // denomE_z //; lia.
rewrite denomE // numE //.
suff /IH : 0 <= / `{r} by nia.
have /frac_inv_gt_1 := H; by lra.
Qed.

Lemma approx_spos n r : 1 <= r -> (0 < 'p[r]_n.+1 /\ 0 < 'q[r]_ n.+1)%Z.
Proof.
elim: n r => [r rP |[|n] IH r rP].
- have F : (1 <= `[r])%Z by rewrite -(ZfloorZ 1); apply: Zfloor_le => /=; lra.
  by rewrite num_1 denom_1; lia.
- have F : (1 <= `[r])%Z by rewrite -(ZfloorZ 1); apply: Zfloor_le => /=; lra.
  case: (Req_EM_T `{r} 0) => H; first by rewrite numE_z // denomE_z //; lia.
  rewrite denomE // numE // num_1 denom_1.
  have /frac_inv_floor_ge_1 := H; by nia.
have F : (1 <= `[r])%Z by rewrite -(ZfloorZ 1); apply: Zfloor_le => /=; lra.
case: (Req_EM_T `{r} 0) => H; first by rewrite numE_z // denomE_z //; lia.
rewrite denomE // numE //.
suff /IH : 1 <= / `{r} by nia.
have /frac_inv_gt_1 := H; by lra.
Qed.

Lemma num_pos n r : 0 <= r -> (0 <= 'p[r]_ n)%Z.
Proof. by move/(approx_pos n); lia. Qed.

Lemma num_spos n r : 
  0 <= r -> (n <> 0%N ->'a[r]_n <> 0%Z) -> (0 < 'p[r]_ n)%Z.
Proof.
move=> rP.
have rrP : (0 <= `[r])%Z.
  by rewrite -(ZfloorZ 0); apply: Zfloor_le => /=; lra.
case: n => [|[|n eP]]; first by rewrite num_0.
  by rewrite elt_1 num_1; lia.
case: (Req_EM_T `{r} 0) => H; first by move: eP; rewrite eltE_z // => [[]].
rewrite numE //.
have /(approx_spos n) : 1 <= / `{r}.
  by have /frac_inv_gt_1 := H; by lra.
suff : (0 <= `[r])%Z by nia.
by rewrite -(ZfloorZ 0); apply: Zfloor_le => /=; lra.
Qed.

Lemma num_spos1 n r :  0 <= r -> `{r} <> 0 -> (0 < 'p[r]_ n.+2)%Z.
Proof.
move=> rP rD.
have rrP : (0 <= `[r])%Z.
  by rewrite -(ZfloorZ 0); apply: Zfloor_le => /=; lra.
rewrite numE //.
suff /(approx_spos n) : 1 <= / `{r} by nia.
by have /frac_inv_gt_1 := rD; by lra.
Qed.

Lemma denom_spos n r : (0 < 'q[r]_ n.+1)%Z.
Proof.
case: n => [|n]; first by rewrite denom_1.
case: (Req_EM_T `{r} 0) => H; first by rewrite denomE_z.
rewrite denomE //.
suff /(approx_spos n) : 1 <= / `{r} by nia.
have /frac_inv_gt_1 := H; by lra.
Qed.

Lemma denom_pos n r : (0 <= 'q[r]_ n)%Z.
Proof.  
by case: n; [rewrite denom_0 | move=> n; have := denom_spos n r]; lia.
Qed.

Lemma num_denom_id n r : 
  'a[r]_ n.+2 = 0%Z -> 'p[r]_ n.+2 ='p[r]_ n.+1 /\ 'q[r]_ n.+2 ='q[r]_ n.+1.
Proof.
elim: n r => [r|n IH r]; case: (Req_EM_T `{r} 0) => H;
         try by rewrite !(numE_z, denomE_z).
  rewrite eltE // elt_1.
  by have := frac_inv_floor_ge_1 _ H; lia.
rewrite eltE // => /IH [IH1 IH2].
rewrite !(numE _ _ H, denomE _ _ H) IH1 IH2.
split; lia.
Qed.

Lemma num_id n r : 'a[r]_ n.+2 = 0%Z -> 'p[r]_ n.+2 ='p[r]_ n.+1.
Proof. by move=> /num_denom_id[]. Qed.

Lemma denom_id n r : 'a[r]_ n.+2 = 0%Z -> 'q[r]_ n.+2 ='q[r]_ n.+1.
Proof. by move=> /num_denom_id[]. Qed.

Lemma num_denom_rec n r : 'a[r]_ n.+2 <> 0%Z ->
  ('p[r]_n.+2 = 'a[r]_ n.+2 * 'p[r]_n.+1 + 'p[r]_n)%Z /\
  ('q[r]_n.+2 = 'a[r]_ n.+2 * 'q[r]_n.+1 + 'q[r]_n)%Z.
Proof.
elim: n r => [r |n IH r].
  case: (Req_EM_T `{r} 0) => [H|H _]; first by rewrite !eltE_z.
  rewrite numE // (denomE _ r) // (eltE _ r) //.
  by rewrite !num_1 num_0 !denom_1 denom_0 elt_1; nia.
case: (Req_EM_T `{r} 0) => H; first by rewrite eltE_z.
rewrite eltE // !(numE _ r) // !(denomE _ r) // => /IH [-> ->].
split; ring.
Qed.

Lemma num_rec n r : ('a[r]_ n.+2 <> 0 ->
 'p[r]_n.+2 = 'a[r]_ n.+2 * 'p[r]_n.+1 + 'p[r]_n)%Z.
Proof. by move=> H; have [] := num_denom_rec n r H. Qed.

Lemma denom_rec n r : ('a[r]_ n.+2 <> 0 ->
 'q[r]_n.+2 = 'a[r]_ n.+2 * 'q[r]_n.+1 + 'q[r]_n)%Z.
Proof. by move=> H; have [] := num_denom_rec n r H. Qed.

Lemma num_lt n r : 
  0 <= r -> 'a[r]_n.+1 <> 0%Z ->
  (n = 0%N -> ('a[r]_1 <> 1%Z)) ->
  (n = 2%N -> ('a[r]_1 <> 0%Z \/ 'a[r]_3 <> 1%Z)) -> 
  ('p[r]_n < 'p[r]_n.+1)%Z.
Proof.
move=> rP; have/Zfloor_le := rP.
rewrite elt_1 (ZfloorZ 0) => rrP.
case: n => [|[aR _ _ |[aR _|n]]]; first by rewrite elt_1 num_1 num_0; nia.
- case: (Req_EM_T `{r} 0) => H; first by move: aR; rewrite eltE_z.
  rewrite num_1 numE // num_1 denom_1.
  by have F1 := frac_inv_floor_ge_1 _ H; nia.
- have aRR := elt_neq_0_prev 0 r aR.
  rewrite !num_rec // ?num_0 ?num_1; try lia.
  have F1 := elt_pos r 0; have F2 := elt_pos r 1.
  by case=> //; psatz Z 5.
move=> aR _ _.
have /num_rec-> := aR.
case: (Req_EM_T `{r} 0) => H; first by move: aR; rewrite eltE_z.
have := elt_pos r n.+2.
have := num_spos1 n.+1 r rP H; have := num_spos1 n _ rP H.
by nia.
Qed.

Lemma denom_lt n r : 'a[r]_ n.+1 <> 0%Z ->
   (n = 1%N -> 'a[r]_ 2 <> 1%Z) -> ('q[r]_n < 'q[r]_n.+1)%Z.
Proof.
case: n => [|[aR|n aR]]; first by rewrite denom_1 denom_0; lia.
  case: (Req_EM_T `{r} 0) => H; first by move: aR; rewrite eltE_z.
  rewrite denom_1 denomE // num_1.
  move: aR; rewrite eltE // elt_1.
  by have := frac_inv_floor_ge_1 _ H; nia.
have /denom_rec-> := aR.
case: (Req_EM_T `{r} 0) => H; first by move: aR; rewrite eltE_z.
have := denom_spos n r; have := denom_spos n.+1 r; have := elt_pos r n.+1.
by nia.
Qed.

Lemma irrational_denom_lt n r : irrational r -> ('q[r]_n.+2 < 'q[r]_n.+3)%Z.
Proof.
move=> rI; apply: denom_lt; first by apply: irrational_elt_neq_0.
by lia.

Lemma denom_le n r : ('q[r]_n <= 'q[r]_n.+1)%Z.
Proof.
case: n => [|n]; first by rewrite denom_0 denom_1.
have [aZ|] := (Z.eq_dec ('a[r]_n.+2) 0%Z); first by rewrite denom_id; lia.
case: n => [aD|n aD]; last by apply/Z.lt_le_incl/denom_lt; lia.
by rewrite denom_rec // denom_1 denom_0; have := elt_pos r 0; lia.
Qed.

Lemma denom_2_eq_1 r : ('a[r]_ 2 <= 1 -> 'q[r]_2 = 1)%Z.
Proof.
move=> aD.
have [aZ|aDD] := (Z.eq_dec ('a[r]_2) 0%Z); first by rewrite denom_id.
by have := elt_pos r 0; rewrite denom_rec // denom_0 denom_1; lia.
Qed.

Lemma denom_2_gt_1 r : (1 < 'a[r]_ 2)%Z -> (1 < 'q[r]_2)%Z.
Proof.
move=> aD.
suff : ('q[r]_1 < 'q[r]_2)%Z by rewrite denom_1; lia.
by apply: denom_lt; lia.
Qed.

Lemma denom_3_gt_1 r n : ('a[r]_ n.+3 <> 0 -> 1 < 'q[r]_n.+3)%Z.
Proof.
move=> aD.
have := elt_neq_0_prev _ _ aD.
have : ('q[r]_n.+2 < 'q[r]_n.+3)%Z by apply: denom_lt; lia.
case: n aD => [aD|n aD] F1 F2.
  by have := denom_2_eq_1 r; have := denom_2_gt_1 r; lia.
have : ('q[r]_n.+2 < 'q[r]_n.+3)%Z by apply: denom_lt; lia.
by have := denom_pos n.+2 r; lia.
Qed.

Lemma bezout_num n r : 'a[r]_ n.+1 <> 0%Z ->
  ('q[r]_ n.+1 * 'p[r]_ n - 'p[r]_n.+1 * 'q[r]_n = (-1)^+ n)%Z.
Proof.
case: n => [|n].
  by rewrite num_1 num_0 denom_1 denom_0 Zpower_nat_0_r; lia.
elim: n => [Dr|n IH Dr].
  by rewrite num_rec // denom_rec // num_1 num_0 denom_1 denom_0
             Zpower_nat_succ_r Zpower_nat_0_r; lia.
rewrite (num_rec _ _ Dr) // (denom_rec _ _ Dr) //.
have /elt_neq_0_prev/IH {}IH := Dr.
rewrite moreR.Zpower_natS; nia.
Qed.

(* Distance *)

Definition halton r n := (-1) ^ n.+1 * ('q[r]_ n * r - 'p[r]_ n).

Local Notation " 't[ r ]_ n " := (halton r n)
  (at level 10, format " ''t[' r ]_ n").

Lemma halton_0 r : 't[r]_ 0 = 1.
Proof. by rewrite /halton denom_0 num_0 /=; lra. Qed.

Lemma halton_1 r : 't[r]_ 1 = `{r}.
Proof.
by rewrite /halton /= num_1 denom_1 /frac_part; lra.
Qed.

Lemma haltonE_z r n : `{r} = 0 -> 't[r]_ n.+1 = 0%Z.
Proof.
rewrite /frac_part => fR.
by rewrite /halton numE_z // denomE_z //=; psatz R 3.
Qed.

Lemma haltonE r n : `{r} <> 0 -> 't[r]_ n.+1 = `{r} * 't[/ `{r} ]_ n.
Proof.
move=> Dr.
rewrite /halton numE // denomE //= plus_IZR mult_IZR.
by move: Dr; rewrite /frac_part => HH; field.
Qed.

Lemma halton_rec r n : 'a[r]_n.+2 <> 0%Z -> 
  't[r]_ n.+2 = 't[r]_ n - 'a[r]_ n.+2* 't[r]_ n.+1.
Proof.
move=> nLs.
rewrite /halton {1}(num_rec _ _ nLs) {1}(denom_rec _ _ nLs) /=.
rewrite !(plus_IZR, mult_IZR); nra.
Qed.

Lemma halton_eq_0 r n : 'a[r]_n.+2 = 0%Z -> 't[r]_ n.+1 = 0.
Proof.
elim: n r => [r|n IH r].
  case: (Req_EM_T `{r} 0) => [H /=|H]; first by rewrite haltonE_z.
  rewrite eltE // elt_1.
  by have F1 := frac_inv_floor_ge_1 _ H; lia.
case: (Req_EM_T `{r} 0) => [H _ /=|H]; first by rewrite haltonE_z.
by rewrite haltonE // eltE // => /IH ->; lra.
Qed.

Lemma halton_eq_0_ge r n m : 'a[r]_n.+2 = 0%Z -> (n < m)%N -> 't[r]_ m = 0.
Proof.
move=> aZ nLm.
rewrite -(subnK nLm).
elim: (_ - _)%N => [|k H]; first by apply: halton_eq_0.
have F : 'a[r ]_ (k + n).+2 = 0%Z.
  by apply: elt_eq_0 _ aZ; rewrite -!addnS !leq_addl.
rewrite /halton !addnS !addSn num_id // denom_id //.
move: H; rewrite /halton !addnS /=; nra.
Qed.

Lemma halton_bound r n : 'a[r]_n.+2 <> 0%Z -> 0 < 't[r]_ n.+1 < 1.
Proof.
elim: n r => [r|n IH r].
  case: (Req_EM_T `{r} 0) => [H /=|H]; first by rewrite eltE_z.
  rewrite halton_1.
  by have := frac_bound r; lra.
case: (Req_EM_T `{r} 0) => [H /=|H]; first by rewrite eltE_z.
rewrite eltE // => /IH; rewrite (haltonE _ _ H).
have := frac_bound r; nra.
Qed.

Lemma halton_gt_0 r n : 'a[r]_n.+1 <> 0%Z -> 0 < 't[r]_ n.
Proof. by case: n => [|n /halton_bound]; [rewrite halton_0|]; lra. Qed.

Lemma halton_pos n r : 0 <= 't[r]_ n.
Proof.
case: n => [|n]; first by rewrite halton_0; lra.
by have [/halton_eq_0|/halton_gt_0] := (Z.eq_dec ('a[r]_n.+2) 0%Z); lra.
Qed.

Lemma halton_ltS n r : 'a[r]_ n.+1 <> 0%Z -> 't[r]_ n.+1 < 't[r]_ n.
Proof.
move=> aD.
have [/halton_eq_0->|aD1] := (Z.eq_dec ('a[r]_n.+2) 0%Z).
  by apply: halton_gt_0.
have tn_pos := halton_gt_0 _ _ aD1.
have el_pos := elt_pos r n.
have [/elt_eq_0_prevN1 F4 |/halton_gt_0] : 'a[r]_n.+3  = 0%Z \/ 'a[r]_n.+3  <> 0%Z by lia.
  have := halton_pos n.+2 r.
  rewrite halton_rec //.
  suff : (2%Z <= 'a[r ]_ n.+2)%R by rewrite /=; nra.
  by apply IZR_le; lia.
rewrite halton_rec //.
suff : (1%Z <= 'a[r ]_ n.+2)%R by rewrite /=; nra.
by apply IZR_le; lia.
Qed.

Lemma halton_lt m n r : 'a[r]_ n.+1 <> 0%Z -> (n < m)%N  -> 't[r]_ m < 't[r]_ n.
Proof.
move=> aD nLm.
rewrite -(subnK nLm).
elim: (_ - _)%N => [|k IH]; first by exact: halton_ltS.
apply: Rle_lt_trans IH.
rewrite !addnS /=.
have [aD1|/halton_ltS] := (Z.eq_dec ('a[r]_(k + n).+2) 0%Z).
  by rewrite !(halton_eq_0_ge _ _ _ aD1) //; lra.
by rewrite addSn; lra.
Qed.

Lemma frac_denom_neq0 n r : 'a[r]_n.+2 <> 0%Z -> `{'q[r]_n.+1 * r} <> 0.
Proof.
case: n=> [|n] aD qrE.
  by rewrite eltE_z // in aD; rewrite Rmult_1_l in qrE.
have := halton_bound _ _ aD.
rewrite /halton.
have->: 'q[r]_n.+2 * r = `['q[r]_n.+2 * r] :> R.
  by rewrite /frac_part in qrE; lra.
by rewrite -minus_IZR -(Zpower_nat_IZR (-1)) -mult_IZR => 
  [[/(lt_IZR 0) H /(lt_IZR _ 1)]]; nia.
Qed.

Lemma frac_denom_eq0 n r : 'a[r]_n.+2 = 0%Z -> `{'q[r]_n.+1 * r} = 0.
Proof.
move=> aD.
suff ->: 'q[r ]_ n.+1 * r = 'p[r ]_ n.+1 by rewrite fracZ.
have /halton_eq_0 := aD.
by rewrite /halton; case: (Rpower_signE n.+2) => ->; nra.
Qed.

Lemma halton_frac1 r :  `{'q[r]_1 * r} = 't[r]_1.
Proof. by rewrite denom_1 halton_1 Rmult_1_l. Qed.

Lemma halton_frac r n : 'a[r]_n.+1 <> 0%Z ->
  `{'q[r]_n * r} = if odd n then 't[r]_n else 1 - 't[r ]_n.
Proof.
case: n => [|n aD].
  by rewrite denom_0 // Rmult_0_l (fracZ 0) halton_0 /=; lra.
have F := frac_denom_neq0 _ _ aD.
have := halton_bound _ _ aD.
rewrite /halton Rpower_sign_odd /=; case: odd => /=; last first.
  rewrite Rmult_1_l => qD.
  rewrite -[X in _ = X]frac_inv; try lra.
  by rewrite /Rminus -opp_IZR frac_addz.
move=> HH.
rewrite -[X in _ = _ - X]frac_inv; try lra.
have->:  -1 * ('q[r ]_ n.+1 * r - 'p[r ]_ n.+1) = 
               -('q[r ]_ n.+1 * r) + 'p[r ]_ n.+1 by lra.
by rewrite frac_addz fracN; lra.
Qed.

Lemma halton_min (n : nat) (p q : Z) (r : R) :
   (0 < q < 'q[r ]_ n.+1)%Z ->  Rabs (q * r - p) >= 't[r]_ n.
Proof.
case: n => [|n]; first by rewrite denom_1; lia.
have [/halton_eq_0->|aD] := (Z.eq_dec ('a[r]_n.+2) 0%Z).
  by split_Rabs; lra.
have /bezout_num := aD; rewrite moreR.Zpower_natS => aE qB.
pose mu := ((- 1)^+ n.+1 * (p * 'q[r]_ n.+2 - q * 'p[r]_ n.+2))%Z.
pose nu := ((- 1)^+ n * (p * 'q[r]_ n.+1 - q * 'p[r]_ n.+1))%Z.
have F1 := Zpower_nat_signE n.
have F2 := Rpower_signE n.
have pE : (p = mu * 'p[r]_n.+1 + nu * 'p[r]_n.+2)%Z.
  clear aD qB.
  by rewrite /mu /nu moreR.Zpower_natS; psatz Z 4.
have qE : (q = mu * 'q[r]_n.+1 + nu * 'q[r]_n.+2)%Z.
  clear aD qB.
  by rewrite /mu /nu moreR.Zpower_natS; psatz Z 4.
have dE : q * r - p = (-1) ^ n * (mu * 't[r]_n.+1 - nu * 't[r]_n.+2).
  by rewrite /halton pE qE /= !(plus_IZR) 4!mult_IZR; psatz R 5.
have F3 : (0 < 'q[r]_ n.+1  <= 'q[r ]_ n.+2)%Z.
  by split; [apply: denom_spos | apply: denom_le].
have F4:  mu * nu <= 0.
  rewrite -mult_IZR; apply: (IZR_le _ 0).
  have : ~(mu < 0 /\ nu < 0)%Z by nia.
  by have : ~(mu > 0 /\ nu > 0)%Z; nia.
have : 0 <=   't[r ]_ n.+1 by exact: halton_pos.
have : 0 <=   't[r ]_ n.+2 by exact: halton_pos.
have : 1 <= Rabs mu.
  have F5 : mu <> 0%Z by move=> HH; suff : (nu <> 0%Z); nia.
  by (have [/IZR_le|/IZR_le] /= : (1 <= mu \/ mu <= -1)%Z by lia);
     split_Rabs; lra.
by rewrite dE /=; case: F2 => ->; split_Rabs; psatz R 5.
Qed.

Lemma halton_floor r n : 'a[r]_n.+2 <> 0%Z -> `['t[r]_n / 't[r]_n.+1] = 'a[r]_n.+2 .
Proof.
move=> aDZ.
apply: Zfloor_eq; split.
  apply: ler_Rdivr (halton_gt_0 _ _ aDZ) _.
  have := halton_pos n.+2 r.
  by rewrite halton_rec //; nra.
apply: ltr_Rdivl (halton_gt_0 _ _ aDZ) _.
have := halton_ltS _ _ aDZ.
rewrite halton_rec //.
nra.
Qed.

Lemma Rmod1_denom_lt (n : nat) (q : Z) (r : R) :
   (0 < q < 'q[r ]_ n.+1)%Z ->  `|q * r| >= `|'q[r]_n * r|.
Proof.
move=> qL; apply: Rge_trans (_ : 't[r]_n >= _).
  by case: (Rmod1_def (q * r)) => ->; apply: halton_min.
suff->: 't[r]_n = Rabs ('q[r]_ n * r - 'p[r]_ n) by apply/Rle_ge/Rmod1_min.
have := halton_pos n r; have := Rpower_signE n.+1.
rewrite /halton => [] [|]->; split_Rabs; lra.
Qed.

Lemma Rmod1_denom (n : nat) (q : Z) (r : R) :
   (0 < q <= 'q[r ]_ n)%Z ->  `|q * r| >= `|'q[r]_n * r|.
Proof.
move=> Lq.
have [qE|qL] : 'q[r ]_ n.+1 = 'q[r]_n \/ ('q[r ]_ n.+1 > 'q[r]_n)%Z.
- by have := denom_le n r; lia.
- have [->//|qqL] : (q = 'q[r]_n \/ q < 'q[r]_n)%Z by lia.
    by lra.
  apply: Rmod1_denom_lt; lia.
apply: Rmod1_denom_lt; lia.
Qed.

Lemma Rmod1_halton_1 (n : nat) (r : R) : 'a[r]_2 = 1%Z -> `|'q[r]_1 * r| = 't[r]_2.
Proof.
move=> aD.
rewrite halton_rec ?aD // halton_0 halton_1 denom_1 !Rmult_1_l.
case: (Req_EM_T `{r} 0) => H; first by move: aD; rewrite eltE_z.
suff: 1 - `{r} < `{r} by rewrite /Rmod1 /Rmin; case: Rle_dec; lra.
move: aD; rewrite eltE // elt_1 => aD.
have := Zfloor_bound (/ `{r}); rewrite aD /= => [[_ aF]].
have /Rmult_lt_compat_r/(_ aF) : 0 < `{r} by have := frac_bound r; lra.
have ->: / `{r} * `{r} = 1 by field.
by lra.
Qed.

Lemma Rmod1_halton (n : nat) (r : R) : 
  (n = 0%N -> 'a[r]_2 <> 1%Z) -> `|'q[r]_n.+1 * r| = 't[r]_n.+1.
Proof.
move=> aD.
case: (Z.eq_dec ('a[r]_ n.+2) 0) => H.
  rewrite halton_eq_0 // /Rmod1.
  suff->: 'q[r ]_ n.+1 * r = 'p[r ]_ n.+1.
    by rewrite fracZ /Rmin; case: Rle_dec; lra.
  have := halton_eq_0 _ _ H; rewrite /halton.
  by have [->|->] := Rpower_signE n.+2; lra.
have F : 't[r]_n.+1 = Rabs ('q[r ]_ n.+1 * r - 'p[r ]_ n.+1).
  have := halton_pos n.+1 r; have :=  Rpower_signE n.+2.
  by rewrite /halton; split_Rabs; nra.
suff: `|IZR ('q[r ]_ n.+1) * r| >= 't[r ]_ n.+1.
  by have F1 := Rmod1_min  ('q[r ]_ n.+1 * r)  ('p[r ]_ n.+1); lra.
have F1 : (0 < 'q[r]_n.+1 < 'q[r]_n.+2)%Z.
  by split; [apply: denom_spos | apply: denom_lt]; lia.
by have [->|->]:= Rmod1_def  ('q[r ]_ n.+1 * r); apply: halton_min.
Qed.

Lemma denom_min n r q : 
  (0 < q < 'q[r ]_ n.+1)%Z -> odd n -> `{q * r} >= `{'q[r]_n * r}.
Proof.
case: n => [|n /=]; first by rewrite denom_1.
case: (Req_EM_T `{'q[r]_n.+1 * r} 0)=> [->|qrD  qD nO].
  by have := frac_bound (q * r); lra.
have F :=  Rmod1_denom_lt _ _ _ qD.
have F1 : `{q * r} >=  `|q * r|.
  rewrite /Rmod1 /Rmin; case: Rle_dec; try lra.
suff: `|q * r| >= `{'q[r ]_ n.+1 * r} by lra.
suff :  `|'q[r ]_ n.+1 * r| = `{'q[r ]_ n.+1 * r} by lra.
have aD : 'a[r ]_ n.+2 <> 0%Z by move/frac_denom_eq0; lra.
rewrite  Rmod1_halton ?(halton_frac _ _ aD) /= ?nO => // H.
by rewrite H in qD; have := denom_2_eq_1 r; lia.
Qed.

Lemma denom_max n r q : 'a[r]_n.+1 <> 0%Z -> 
  (0 < q < 'q[r ]_ n.+1)%Z -> ~~ odd n -> `{q * r} <= `{'q[r]_n * r}.
Proof.
case: n => [|n /=]; first by rewrite denom_1; lia.
rewrite negbK => aD qD nO.
have F1 :=  Rmod1_denom_lt _ _ _ qD.
have F2 : 1 - `{q * r} >=  `|q * r|.
  rewrite /Rmod1 /Rmin; case: Rle_dec; try lra.
suff: `|q * r| >= 1 - `{'q[r ]_ n.+1 * r} by lra.
suff :  `|'q[r ]_ n.+1 * r| = 1 -  `{'q[r ]_ n.+1 * r} by lra.
rewrite  Rmod1_halton ?(halton_frac _ _ aD) /= ?nO /= => [|H]; try lra.
by rewrite H in nO.
Qed.

Lemma halton_sum n r : 1 >= 't[r ]_ n.+1 + 't[r ]_ n.+2.
Proof.
case: (Z.eq_dec ('a[r]_ n.+2) 0) => H.
  rewrite !halton_eq_0 //; try lra.
  by apply: elt_eq_0_next; lia.
have /halton_frac /= F1 := H; have /halton_bound F2 := H.
case: (Z.eq_dec ('a[r]_ n.+3) 0) => [H1| H2].
  rewrite (halton_eq_0 _ _ H1) //; try lra.
have /halton_frac /= F3 := H; have /halton_bound F4 := H.
have F5 : (0 < 'q[r ]_ n.+1 < 'q[r ]_ n.+3)%Z.
      rewrite denom_rec //=; try lia.
      have := elt_pos r n.+1.
      have [] := (denom_spos n r, denom_spos n.+1 r); nia.
have [nO|nE] : odd n \/ ~~ odd n by case: odd; [left|right].
  have nnO : odd n.+2 by rewrite /= nO.
  have /denom_min/(_ nnO) := F5.
  by rewrite !halton_frac //= nO /=; lra.
have nnE : ~~ odd n.+2 by rewrite /= nE.
have :=  denom_max _ _ _ H2 F5 nnE.
rewrite !halton_frac //= nE /=; lra.
Qed.

Definition inum r n i := (i * 'p[r ]_ n.+1 + 'p[r ]_ n)%Z.

Local Notation " 'p[ r , i ]_ n" := (inum r n i) 
  (at level 10, format " ''p[' r ,  i ]_ n").

Lemma inum_0r r n : 'p[r , 0]_ n = 'p[r]_ n.
Proof. by rewrite /inum; lia. Qed.

Lemma inum_ar r n :
  'a[r ]_ n.+2 <> 0%Z -> 'p[r , 'a[r]_n.+2]_ n = 'p[r]_ n.+2.
Proof. by move=> aD; rewrite /inum num_rec. Qed.

Lemma inum_0 r i : 'p[r, i]_ 0 = (i * 'a[r]_ 1 + 1)%Z.
Proof. by rewrite /inum num_0 num_1. Qed.

Lemma inum_1 r i : 'a[r ]_ 2 <> 0%Z ->
  'p[r, i]_ 1 = (i * ('a[r ]_ 2 * 'a[r ]_ 1 + 1) + 'a[r ]_ 1)%Z.
Proof.
case: (Req_EM_T `{r} 0) => [H|H H1]; first by  rewrite eltE_z.
by rewrite /inum num_rec.
Qed.

Lemma inum_1z r i : 'a[r ]_ 2 = 0%Z ->
  'p[r, i]_ 1 = ((i + 1) * 'a[r ]_ 1)%Z.
Proof.
case: (Req_EM_T `{r} 0) => H.
  by rewrite /inum !numE_z // elt_1; lia.
rewrite eltE // elt_1.
by have := frac_inv_floor_ge_1 r H; lia.
Qed.

Definition idenom r n i := (i * 'q[r ]_ n.+1 + 'q[r ]_ n)%Z.

Local Notation " 'q[ r , i ]_ n" := (idenom r n i) 
  (at level 10, format " ''q[' r ,  i ]_ n").

Lemma idenom_0r r n : 'q[r , 0]_ n = 'q[r]_ n.
Proof. by rewrite /idenom; lia. Qed.

Lemma idenom_ar r n :
  'a[r ]_ n.+2 <> 0%Z -> 'q[r , 'a[r]_n.+2]_ n = 'q[r]_ n.+2.
Proof. by move=> aD; rewrite /idenom denom_rec. Qed.

Lemma idenom_0 r i : 'q[r, i]_ 0 = i.
Proof. by rewrite /idenom denom_0 denom_1; lia. Qed.

Lemma idenom_1 r i : 'a[r ]_ 2 <> 0%Z ->
  'q[r, i]_ 1 = (i * 'a[r ]_ 2 + 1)%Z.
Proof.
case: (Req_EM_T `{r} 0) => [H|H H1]; first by  rewrite eltE_z.
by rewrite /idenom denom_rec // denom_1 denom_0; lia.
Qed.

Lemma idenom_1z r i : 'a[r ]_ 2 = 0%Z -> 'q[r, i]_ 1 = (i + 1)%Z.
Proof.
case: (Req_EM_T `{r} 0) => H; first by rewrite /idenom !denomE_z //; lia.
rewrite eltE // elt_1.
by have := frac_inv_floor_ge_1 r H; lia.
Qed.

Lemma ibezout_num n r i : 'a[r]_ n.+1 <> 0%Z ->
  ('q[r, i]_ n * 'p[r]_ n.+1 - 'p[r, i]_n * 'q[r]_n.+1 = (-1)^+ n.+1)%Z.
Proof.
move=> aD.
rewrite /idenom /inum moreR.Zpower_natS.
by have := bezout_num _ _ aD; nia.
Qed.

Lemma iibezout_num n r i : 'a[r]_ n.+1 <> 0%Z ->
  ('q[r, i]_ n * 'p[r, i+1]_ n - 'p[r, i]_n * 'q[r, i+1]_n = (-1)^+ n.+1)%Z.
Proof.
move=> aD.
rewrite /idenom /inum moreR.Zpower_natS.
have := bezout_num _ _ aD.
nia.
Qed.

Definition ihalton r n i := (-1) ^ n.+1 * ('q[r, i]_ n * r - 'p[r, i]_ n).

(* t for theta *)
Local Notation " 't[ r , i ]_ n " := (ihalton r n i) 
  (at level 10, format  " ''t[' r ,  i ]_ n ").

Lemma ihalton_0 r i : 't[r, i]_ 0 = 1 - i * `{r}.
Proof.
by rewrite /ihalton inum_0 idenom_0 elt_1 plus_IZR mult_IZR /= /frac_part; lra.
Qed.

Lemma ihalton_1 r i :  'a[r ]_ 2 <> 0%Z -> 
  't[r, i]_ 1 = i * ('a[r]_2 * `{r} - 1) + `{r}. 
Proof.
move=> aD.
rewrite /ihalton /= inum_1 // idenom_1 // elt_1.
rewrite /frac_part !(plus_IZR, mult_IZR) /=; lra.
Qed.

Lemma ihaltonE r n i :  't[r, i]_ n = 't[r]_n - i * 't[r]_n.+1.
Proof.
rewrite /ihalton /halton /inum /idenom.
rewrite !plus_IZR !mult_IZR /=; nra.
Qed.

Lemma halton_0r r n : 't[r, 0]_n = 't[r]_n.
Proof. by rewrite ihaltonE /=; lra. Qed.

Lemma halton_ar r n :
  'a[r]_n.+2 <> 0%Z -> 't[r, 'a[r]_n.+2]_n = 't[r]_n.+2.
Proof. by move=> aD; rewrite ihaltonE halton_rec. Qed.

Lemma ihalton_halton_bound r n i : 
    (0 <= i < 'a[r]_ n.+2)%Z -> 't[r]_n.+2 < 't[r, i]_n <= 't[r]_n.
Proof.
move=> iaD.
have aD : 'a[r]_ n.+2 <> 0%Z by lia.
rewrite -(halton_0r _ n) -halton_ar; try lia.
case: iaD => /IZR_le /= H /IZR_lt /= H1.
have := halton_bound r n aD.
by rewrite !ihaltonE /=; nra.
Qed.

Lemma ihalton_bound r n i : 
 (0 <= i < 'a[r]_ n.+3)%Z -> 0 < 't[r, i]_ n.+1 < 1.
Proof.
move=> iaD.
have := ihalton_halton_bound _ _ _ iaD.
have := halton_pos n.+3 r.
suff /halton_bound : 'a[r ]_ n.+2 <> 0%Z by lra.
by apply: elt_neq_0_prev; lia.
Qed.

Lemma ihalton_pos r n i : 'a[r]_ n.+2 <> 0%Z ->
  (0 <= i <= 'a[r]_ n.+2)%Z -> 0 <= 't[r, i]_ n.
Proof.
move=> aD iaD.
have := halton_pos n.+2 r; have := halton_pos n.+1 r.
rewrite -halton_ar // !ihaltonE.
case: iaD => _ /IZR_le; nra.
Qed.

Lemma frac_idenom_neq0 n r i : 
  (0 <= i < 'a[r]_ n.+3)%Z -> `{'q[r, i]_n.+1 * r} <> 0.
Proof.
move=> iaD qrE.
have := ihalton_bound _ _ _ iaD.
rewrite /ihalton.
have->: 'q[r, i]_n.+1 * r = `['q[r, i]_n.+1 * r] :> R.
  rewrite /frac_part in qrE; lra.
rewrite -minus_IZR -(Zpower_nat_IZR (-1)) -mult_IZR.
by move=> [/(lt_IZR 0) H /(lt_IZR _ 1)]; lia.
Qed.

Lemma ihalton_frac r n i :  (0 <= i < 'a[r]_n.+3)%Z ->
  `{'q[r, i]_n.+1 * r} = if odd n.+1 then 't[r, i]_n.+1 else 1 - 't[r, i ]_n.+1.
Proof.
move=> iaD.
have F := frac_idenom_neq0 _ _ _ iaD.
have := ihalton_bound _ _ _ iaD.
rewrite /ihalton Rpower_sign_odd /=; case: odd => /=; last first.
  rewrite Rmult_1_l => qD.
  rewrite -[X in _ = X]frac_inv; try lra.
  by rewrite /Rminus -opp_IZR frac_addz.
move=> HH.
rewrite -[X in _ = _ - X]frac_inv; try lra.
have->:  -1 * ('q[r, i]_ n.+1 * r - 'p[r, i]_ n.+1) = 
               -('q[r, i]_ n.+1 * r) + 'p[r, i]_ n.+1 by lra.
by rewrite frac_addz fracN //; lra.
Qed.

Lemma ihalton_min (n : nat) (p q : Z) (r : R) i :
  (0 <= i < 'a[r]_ n.+3)%Z -> 
   ~(exists alpha, q = alpha * 'q[r]_n.+2 /\ p = alpha * 'p[r]_n.+2)%Z ->
  (0 < q < 'q[r, i + 1 ]_ n.+1)%Z ->  Rabs (q * r - p) >= 't[r, i]_ n.+1.
Proof.
move=> iP zD.
have aD : 'a[r]_ n.+3 <> 0%Z by lia.
have aDD : 'a[r]_ n.+2 <> 0%Z by exact: elt_neq_0_prev.
have /(ibezout_num _ _ (i + 1)) := aDD; rewrite !moreR.Zpower_natS => aE qB.
pose mu := ((- 1)^+ n * (p * 'q[r,i+1]_ n.+1 - q * 'p[r,i+1]_ n.+1))%Z.
pose nu := ((- 1)^+ n.+1 * (p * 'q[r]_ n.+2 - q * 'p[r]_ n.+2))%Z.
have F1 := Zpower_nat_signE n.
have F2 := Rpower_signE n.
have pE : (p = mu * 'p[r]_n.+2 + nu * 'p[r,i+1]_n.+1)%Z.
  clear aD qB F2.
  by move: aE; rewrite /mu /nu moreR.Zpower_natS;
     case: F1 => ->; psatz Z 4.
have qE : (q = mu * 'q[r]_n.+2 + nu * 'q[r, i+1]_n.+1)%Z.
  clear aD qB F2.
  by move: aE; rewrite /mu /nu moreR.Zpower_natS;
     case: F1 => ->; psatz Z 4.
have dE : q * r - p = (-1) ^ n.+1 * (mu * 't[r]_n.+2 - nu * 't[r,i+1]_n.+1).
  rewrite /halton /ihalton pE qE /= 2!plus_IZR.
  rewrite ![IZR (mu * _)]mult_IZR ![IZR (nu * _)]mult_IZR.
  case: F2 => ->; nra.
have F3 : (0 < 'q[r]_ n.+2  <= 'q[r, i + 1 ]_ n.+1)%Z.
  split; first apply: denom_spos.
  rewrite /idenom.
  have := denom_pos n.+2 r;   have := denom_pos n.+1 r; nia.
have F4:  mu * nu <= 0.
  rewrite -mult_IZR; apply: (IZR_le _ 0).
  have : ~(mu < 0 /\ nu < 0)%Z by nia.
  have : ~(mu > 0 /\ nu > 0)%Z by nia.
  clear; case: (Z_le_dec 0 mu); case : (Z_le_dec 0 nu); nia.
have F5 : 1 <= Rabs mu.
  have F5 : mu <> 0%Z by move=> HH; suff : (nu <> 0%Z); nia.
  by (have [/IZR_le|/IZR_le] /= : (1 <= mu \/ mu <= -1)%Z by lia);
     split_Rabs; lra.
have F6 : 1 <= Rabs nu.
  suff F6 : nu <> 0%Z.
    by (have [/IZR_le|/IZR_le] /= : (1 <= nu \/ nu <= -1)%Z by lia);
     split_Rabs; lra.
  by contradict zD; rewrite qE pE zD; exists mu; lia.
have : Rabs (q * r - p) >= 't[r, i +  1]_ n.+1 + 't[r]_ n.+2.
  have : 0 <= 't[r]_ n.+2 by exact: halton_pos.
  have : 0 <= 't[r, i + 1]_ n.+1 by apply: ihalton_pos; lia.
  by rewrite dE /=; case: F2 => ->; split_Rabs; nra.
by rewrite !ihaltonE plus_IZR /=; lra.
Qed.

Lemma Rmod1_idenom (n : nat) (q : Z) (r : R) i :
  (0 <= i < 'a[r]_ n.+3)%Z -> 
   (forall k, 0 < k <= i + 1 -> q <>  k * 'q[r]_n.+2)%Z ->
  (0 < q < 'q[r, i + 1 ]_ n.+1)%Z ->  `|q * r|  >= `|'q[r, i]_n.+1 * r|.
Proof.
move=> iL kL qL; apply: Rge_trans (_ : 't[r, i]_n.+1 >= _); last first.
  suff->: 't[r, i]_n.+1 = Rabs ('q[r, i]_ n.+1 * r - 'p[r, i]_ n.+1) 
    by apply/Rle_ge/Rmod1_min.
  have /ihalton_bound := iL.
  by have := Rpower_signE n.+2; rewrite /ihalton => [] [|]->; split_Rabs; lra.
by case: (Rmod1_def (q * r)) => ->;  apply: ihalton_min => // [[a [aH _]]];
   case: (kL a) => //; move: qL; rewrite {}aH /idenom;
   have := denom_pos n.+1 r;have := denom_spos n.+1 r; have := denom_le n.+1 r; nia.
Qed.


(* Instead of using ihalton_min, we could use a more direct proof knowing that
   Rabs (r - 'p[r,i]_n.+1/'q[r, i]_n.+1) < 1 / ('q[r, i]_n.+1 'q[r]_n.+2)
   Rabs ('q[r, i]_n.+1 r - 'p[r,i]_n.+1) < 1 / 'q[r]_n.+2 so if 'q[r]_n.+2 >=2
   we are ok
*)

Lemma Rmod1_ihalton (n : nat) (r : R) i : (1 < 'q[r]_n.+2)%Z ->
  (0 <= i < 'a[r]_ n.+3)%Z -> `|'q[r, i]_n.+1 * r| = 't[r, i]_n.+1.
Proof.
move=> nD aD.
have aDD : 'a[r]_ n.+3 <> 0%Z by lia.
have F : (0 < 'q[r, i ]_ n.+1 < 'q[r, i + 1 ]_ n.+1)%Z.
  have F1 := denom_spos n.+1 r; have F2 := denom_pos n.+1 r.
  rewrite /idenom;  split; last lia.
  by have := denom_spos n r; nia.
suff F1 : `|'q[r, i ]_ n.+1 * r| <= 't[r, i ]_ n.+1.
  have dP := denom_pos n.+2 r.
  suff: `|'q[r, i ]_ n.+1 * r| >= 't[r, i ]_ n.+1 by lra.
  have F2 : ~('q[r ]_ n.+2 | 'q[r, i ]_ n.+1)%Z.
    move=> [a aH].
    suff /(Z.divide_1_r_nonneg _ dP): ('q[r ]_ n.+2 | 1)%Z by lia.
    exists ((-1) ^+ n.+2 * (a * 'p[r ]_ n.+2 - 'p[r, i ]_ n.+1))%Z.
    have /(ibezout_num _ _ i) : 'a[r]_ n.+2 <> 0%Z.
      by exact: elt_neq_0_prev.
    rewrite aH.
    by have [->|->] := Zpower_nat_signE n.+2; lia.
  by (case: (Rmod1_def ('q[r, i ]_ n.+1 * r))=> ->;
        apply: ihalton_min) => // [] [a [aH _]]; case: F2; exists a.
have := ihalton_frac _ _ _ aD.
rewrite /Rmod1 /Rmin; case: Rle_dec; case: odd; lra.
Qed.

(* There should be an easier way to prove all this *)
Lemma mul_qrE n r k : 
  (0 < k <= 'a[r]_ n.+3)%Z -> (1 < 'q[r ]_ n.+2)%Z ->
  `{(k * 'q[r ]_ n.+2)%Z * r} =
        if odd n then k * 't[r ]_n.+2 else 1 - k * 't[r ]_n.+2.
Proof.
move=> kaD qD.
have aD : 'a[r]_ n.+3 <> 0%Z by lia.
set kr := _ * r ; pose qar := 'q[r, 'a[r]_ n.+3]_n.+1 * r.
have [nO|nE] : odd n \/ odd n = false by case: odd; [left|right].
  case: (Z.eq_dec ('a[r ]_ n.+4) 0) => FF0.
    have F1 :  `{kr} >= `{qar}.
      rewrite /qar idenom_ar ?frac_denom_eq0 //; try lia.
      by have := frac_bound kr; lra.
    have F2 : `{kr} - `{qar} = 't[r]_n.+1 - ('a[r ]_ n.+3 - k) * 't[r]_n.+2.
      rewrite -fracB //; last by lra.
      have -> : kr - qar = - ('q[r , 'a[r ]_ n.+3 - k]_n.+1  * r).
        by rewrite /kr /qar /idenom !plus_IZR !mult_IZR minus_IZR; nra.
      (rewrite fracN ihalton_frac //= ?nO //=; try by lia); last first.
        have /ihalton_bound : (0 <= 'a[r ]_ n.+3 - k < 'a[r ]_ n.+3)%Z by lia.
        by lra.
      by rewrite ihaltonE minus_IZR; nra.
    have : `{qar} = 0.
       rewrite /qar idenom_ar; last by lia.
       by rewrite frac_denom_eq0 // halton_eq_0.
    have : `{qar} = 't[r ]_ n.+3.
      rewrite /qar idenom_ar; last by lia.
      by rewrite frac_denom_eq0 // halton_eq_0.
    rewrite halton_rec // => FF.
    by rewrite nO; nra.
  have F1 :  `{kr} <= `{qar}.
    rewrite /qar idenom_ar; last by lia.
    apply: denom_max; rewrite /= ?nO //=.
    rewrite ['q[r ]_ n.+4]denom_rec // ['q[r ]_ n.+3]denom_rec //.
    have [[]] := (elt_pos r n.+2, denom_spos n.+1 r, denom_spos n r).
    by psatz Z 4.
  have F2 : `{qar} - `{kr} = 1 - 't[r]_n.+1 + ('a[r ]_ n.+3 - k) * 't[r]_n.+2.
    rewrite -fracB //.
    have -> : qar - kr = 'q[r , 'a[r ]_ n.+3 - k]_n.+1  * r.
      by rewrite /kr /qar /idenom !plus_IZR !mult_IZR minus_IZR; nra.
    (rewrite ihalton_frac //= ?nO //=; try by lia); last first.
      have /ihalton_bound : (0 <= 'a[r ]_ n.+3 - k < 'a[r ]_ n.+3)%Z by lia.
    by rewrite ihaltonE minus_IZR; nra.
  suff : `{qar} = 1 - 't[r ]_ n.+3 by rewrite nO halton_rec // => FF; nra.
  rewrite /qar idenom_ar; last by lia.
  by rewrite halton_frac //= nO.
have F1 :  `{kr}  >= `{qar}.
  rewrite /qar idenom_ar; last by lia.
  apply: denom_min; rewrite /= ?nE //=.
  case: (Z.eq_dec ('a[r ]_ n.+4) 0) => a4D.
    rewrite (denom_id _ _ a4D) ['q[r ]_ n.+3]denom_rec //.
    by have := denom_spos n r; nia. 
  rewrite ['q[r ]_ n.+4]denom_rec // ['q[r ]_ n.+3]denom_rec //.
  have [[]] := (elt_pos r n.+2, denom_spos n.+1 r, denom_spos n r).
  by psatz Z 4.
have F2 : `{kr} - `{qar} = 1 - 't[r]_n.+1 + ('a[r ]_ n.+3 - k) * 't[r]_n.+2.
  rewrite -fracB //; last by lra. 
  have -> : kr - qar = - ('q[r , 'a[r ]_ n.+3 - k]_n.+1  * r).
    by rewrite /kr /qar /idenom !plus_IZR !mult_IZR minus_IZR; nra.
  (rewrite fracN ihalton_frac /= ?nE //=; try by lia); last first.
    have /ihalton_bound : (0 <= 'a[r ]_ n.+3 - k < 'a[r ]_ n.+3)%Z by lia.
    by lra.
  by rewrite ihaltonE minus_IZR; nra.
suff : `{qar} = 't[r ]_ n.+3 by rewrite nE halton_rec // => FF; nra.
rewrite /qar idenom_ar; last by lia.
case: (Z.eq_dec ('a[r ]_ n.+4) 0) => a4D.
  by rewrite frac_denom_eq0 // halton_eq_0.
by rewrite halton_frac //= nE.
Qed.

Lemma idenom_mul_qr_min n r i k : 
  (0 <= i < 'a[r]_ n.+3)%Z -> (1 < 'q[r ]_ n.+2)%Z -> (0 < k <= i + 1)%Z ->
  ~~ odd n ->  `{(k * 'q[r]_ n.+2)%Z * r} >= `{'q[r, i]_n.+1 * r}.
Proof.
move=> iaD kD qqD nO.
have nnO : odd n = false by case: odd nO.
rewrite mul_qrE //; last by lia.
rewrite nnO ihalton_frac /= ?nnO //= ihaltonE.
have  : (0 < k <= i + 1).
  split; first by apply: (IZR_lt 0); lia.
  by rewrite -(plus_IZR _ 1); apply: IZR_le; lia.
have : 't[r ]_ n.+2 >= 0 by have := halton_pos n.+2 r; lra.
have :  'a[r ]_ n.+3 >= 0 by apply/Rle_ge/(IZR_le 0); lia.
by have trD := halton_sum n r; nra.
Qed.

Lemma idenom_mul_qr_max n r i k : 
  (0 <= i < 'a[r]_ n.+3)%Z -> (1 < 'q[r ]_ n.+2)%Z -> (0 < k <= i + 1)%Z ->
  odd n ->  `{(k * 'q[r]_ n.+2)%Z * r} <= `{'q[r, i]_n.+1 * r}.
Proof.
move=> iaD kD qqD nO.
rewrite mul_qrE //; last by lia.
rewrite nO ihalton_frac /= ?nO //= ihaltonE.
have  : (0 < k <= i + 1).
  split; first by apply: (IZR_lt 0); lia.
  by rewrite -(plus_IZR _ 1); apply: IZR_le; lia.
have : 't[r ]_ n.+2 >= 0 by have := halton_pos n.+2 r; lra.
have :  'a[r ]_ n.+3 >= 0 by apply/Rle_ge/(IZR_le 0); lia.
by have trD := halton_sum n r; nra.
Qed.

Lemma idenom_min n r i q : 
  (0 <= i < 'a[r]_ n.+3)%Z -> (1 < 'q[r ]_ n.+2)%Z ->
   (0 < q < 'q[r, i + 1 ]_ n.+1)%Z -> ~~ odd n ->
   `{q * r} >= `{'q[r, i]_n.+1 * r}.
Proof.
move=> iaD qD qqD nO.
case: (Z.eq_dec (q  mod 'q[r]_ n.+2) 0) => modD.
  have /Znumtheory.Zmod_divide/(_ modD)[k Hk] : 'q[r ]_ n.+2 <> 0%Z by lia.
  rewrite Hk.
  apply: idenom_mul_qr_min => //.
  have := qqD; rewrite Hk /idenom.
  have : ('q[r ]_ n.+1 <= 'q[r ]_ n.+2)%Z by apply: denom_le.
  by nia.
rewrite (ihalton_frac _ _ _ iaD) /= nO.
rewrite -Rmod1_ihalton //.
have :  `|q * r|  >= `|'q[r, i]_n.+1 * r|.
  apply: Rmod1_idenom => // k Hk qE.
  by case: modD; rewrite qE Zdiv.Z_mod_mult.
rewrite {1}/Rmod1 /Rmin; case: Rle_dec; lra.
Qed.

Lemma idenom_max n r q i : (0 <= i < 'a[r]_ n.+3)%Z -> (1 < 'q[r ]_ n.+2)%Z ->
  (0 < q < 'q[r, i + 1 ]_ n.+1)%Z -> odd n -> `{q * r} <= `{'q[r, i]_n.+1 * r}.
Proof.
move=> iaD qD qqD nO.
case: (Z.eq_dec (q  mod 'q[r]_ n.+2) 0) => modD.
  have /Znumtheory.Zmod_divide/(_ modD)[k Hk] : 'q[r ]_ n.+2 <> 0%Z by lia.
  rewrite Hk.
  apply: idenom_mul_qr_max => //.
  have := qqD; rewrite Hk /idenom.
  have : ('q[r ]_ n.+1 <= 'q[r ]_ n.+2)%Z by apply: denom_le.
  by nia.
rewrite (ihalton_frac _ _ _ iaD) /= nO /=.
rewrite -Rmod1_ihalton //.
have :  `|q * r|  >= `|'q[r, i]_n.+1 * r|.
  apply: Rmod1_idenom => // k Hk qE.
  by case: modD; rewrite qE Zdiv.Z_mod_mult.
rewrite {1}/Rmod1 /Rmin; case: Rle_dec; lra.
Qed.
