Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun. 
From mathcomp Require Import fintype bigop seq.
Require Import Zpower.
Require Import moreR moreZ rfrac fib.
Open Scope R_scope.

(******************************************************************************)
(* This file contains some basic properties of Ostrovski numeration :         *)
(*                                                                            *)
(*  'z[r]_n    = the n^th complete quotient of r                              *)
(*                                                                            *)
(*  'bo[r,n]   = the bound of the summation of n in the Ostrovski numeration  *)
(*               of base r                                                    *)
(*  'o[r,n]_i  = the i^th element of the Ostrovski numeration of n in base r  *)
(*               of base r                                                    *)
(*  'mo[r,n] =   the index of the first non-zero element of the Ostrovski     *)
(*               numeration of n in base r                                    *)
(*                                                                            *)
(******************************************************************************)

(* Complete quotient *)
Fixpoint zeta r i := 
  if i is j.+1 then / (zeta r j - 'a[r]_i) else r.

Notation " 'z[ r ]_ k " := (zeta r k) 
  (at level 10, format " ''z[' r ]_ k ").

Lemma zeta_0 r : 'z[r]_0 = r.
Proof. by []. Qed.

Lemma zeta_rec r k :  'z[r]_k  =  'a[r]_k.+1 + /  'z[r]_k.+1 .
Proof. by rewrite /= Rinv_inv; lra. Qed.

Lemma pair_zetaProp r k : 
 'a[r]_k.+1 = `[zeta r k] /\ zeta (/ `{r}) k = / `{zeta r k}.
Proof.
elim: k r => [|k IH] r; first by rewrite elt_1.
have [IHr1 IHr2] := IH r.
have [IHir1 IHir2] := IH (/ `{r}).
split; last by rewrite /= IHir1 IHr2 IHr1.
have [re0|rneq0] := Req_dec `{r} 0.
  rewrite eltE_z //=.
  suff -> : 'z[r]_k = 'a[r]_k.+1 by rewrite Rminus_diag Rinv_0 ZfloorZ.
  elim: (k) => [|k1 IH1].
    rewrite zeta_0 elt_1.
    by rewrite /frac_part in re0; lra.
  rewrite eltE_z //= IH1.
  by rewrite  Rminus_diag Rinv_0.
rewrite /=.
rewrite eltE /=; first by rewrite IHir1 IHr2 IHr1.
by move=> H; case: (irrational_IZR 0); rewrite -H; apply: irrational_frac.
Qed.

Lemma zeta_frac_part r k : 'a[r]_k.+1 = `[ 'z[r]_k].
Proof. by have [] := pair_zetaProp r k. Qed.

Lemma zeta_inv r k : 'z[/ `{r}]_k  = / `{'z[r]_k}.
Proof. by have [] := pair_zetaProp r k. Qed.

Lemma zeta_pos r k : 0 <= r -> 0 <= zeta r k.
Proof.
elim: k r => //= k IH r r_pos.
rewrite zeta_frac_part -[_ - _]/(`{ 'z[r]_k }).
apply: Rinv_0_le_compat.
by have := frac_bound (zeta r k); lra.
Qed.

Fixpoint mko_list (r : R) (n : nat) (v : Z) : list Z :=
  if n is n1.+1 then
    (v / 'q[r]_n)%Z :: mko_list r n1 (v mod 'q[r]_n)%Z
  else nil.

Lemma mko_listS (r : R) (n : nat) (v : Z) :
  mko_list r n.+1 v = 
    (v / 'q[r]_n.+1)%Z :: mko_list r n (v mod 'q[r]_n.+1)%Z.
Proof. by []. Qed.

Lemma mko_list0 r n : mko_list r n 0 = nseq n 0%Z.
Proof.
by elim: n => //= n IH; rewrite Zdiv.Zdiv_0_l Zdiv.Zmod_0_l IH.
Qed.

Lemma mko_list_denom r n : mko_list r n.+1 ('q[r]_n.+1) = 1%Z :: nseq n 0%Z.
Proof.
have q_pos : (0 < 'q[r]_n.+1)%Z by apply: denom_spos.
by rewrite /= Zdiv.Z_div_same ?Zdiv.Z_mod_same ?mko_list0 //; lia.
Qed.

Lemma mko_list_le (r : R) (n : nat) (v : Z) i :
  irrational r -> 0 <= r ->
  (0 <= v < 'q[r]_n.+1 -> 0 <=  nth 0 (mko_list r n v) i <= 'a[r]_(n.+1 - i))%Z. 
Proof.
move=> rI r_gt_0 ; elim: n v i => /= [|n IH] v i vLq.
  rewrite nth_nil; case: i => /= [|i].
    by rewrite subn0 elt_1; have := Zfloor_pos r r_gt_0; lia.
  by rewrite  subSS sub0n elt_0; lia.
have rF := frac_neq_0_irrational r rI.
case: i => /=; last first.
  move=> i1; case: n IH vLq => [|n] IH vLq.
    rewrite /= nth_nil.
    case: i1 => [|i1]; first by rewrite elt_1; have := Zfloor_pos r r_gt_0; lia.
    by rewrite elt_0; lia.
  by apply/IH/Z.mod_pos_bound/denom_spos.
rewrite subn0; split.
  apply: Zdiv.Z_div_nonneg_nonneg; first by lia.
  by apply: denom_pos.
case: (n) vLq => [|n1] vLq.
  rewrite denom_1 Zdiv.Zdiv_1_r.
  rewrite eltE // elt_1.
  rewrite denomE // in vLq.
  by rewrite num_1 in vLq; lia.
have q_pos : 'q[r]_n1.+2  <> 0%Z by have := denom_spos n1.+1 r; lia. 
have <- : (('a[r]_n1.+3 * 'q[r]_n1.+2 + ('q[r]_n1.+1 - 1)) /  'q[r]_n1.+2 = 
            'a[r]_n1.+3)%Z.
  rewrite Z.div_add_l // Z.div_small; first by lia.
  by have := denom_spos n1 r; have := denom_leS n1.+1 r; lia.
apply: Z.div_le_mono; first by apply: denom_spos.
rewrite denom_rec in vLq; first by lia.
by apply: irrational_elt_neq_0.
Qed.

Lemma mko_list_eq0 (r : R) (n : nat) (v : Z) i :
  irrational r -> 0 <= r ->
  (0 <= v < 'q[r]_n.+1 -> nth 0 (mko_list r n v) i = 'a[r]_(n.+1 - i) -> 
  nth 0 (mko_list r n v) i.+1 = 0)%Z. 
Proof.
move=> rI r_gt_0 ; elim: n v i => /= [|n IH] v i vLq.
  by rewrite nth_nil; case: i => //= [|i].
have rF := frac_neq_0_irrational r rI.
case: i => /=; last first.
  move=> i1; case: n IH vLq => [|n] IH vLq vDE //.
  apply: IH => //.
  by apply/Z.mod_pos_bound/denom_spos.
rewrite subn0 => vDE.  
rewrite denom_rec // in vLq; last by apply: irrational_elt_neq_0.
case: n {IH}vDE vLq => //= n vDE vLq.
apply: Z.div_small; split.
  apply: Zdiv.Z_mod_nonneg_nonneg; first by lia.
  by apply: denom_pos.
suff : ('a[r]_n.+3 * 'q[r]_n.+2 + v mod  'q[r]_n.+2 <  
        'a[r]_n.+3 * 'q[r]_n.+2 + 'q[r]_n.+1)%Z by lia.
by rewrite -{1}vDE Zmult_comm -Zdiv.Z_div_mod_eq_full; lia.
Qed.

Lemma mko_list_le_q (r : R) (n : nat) (v : Z) i :
  irrational r -> 0 <= r ->
  (0 <= v < 'q[r]_n.+1 -> (i <= n)%nat -> 
   0 <=  nth 0 (mko_list r n v) i < 'q[r]_(n.+1 - i))%Z. 
Proof.
move=> rI r_gt_0 ; elim: n v i => /= [|n IH] v [|i] //= iLn vLq.
  rewrite subn0; split.
    apply: Zdiv.Z_div_nonneg_nonneg; first by lia.
    by apply: denom_pos.
  by apply: Z.le_lt_trans (divZ_le _ _ _) _; lia.
by apply: IH => //; apply/Z.mod_pos_bound/denom_spos.
Qed.

Lemma size_mko_list r n v : size (mko_list r n v) = n.
Proof. by elim: n v => //= n IH v; rewrite IH. Qed.

Lemma big_mko_list r n v : 
  let l := mko_list r n v in 
  (0 < n)%nat -> 
  v = \big[Zplus/0%Z]_(i < n) (nth 0%Z l (n - i.+1) * 'q[r]_i.+1)%Z.
Proof.
elim: n v => // [] [|n] IH v l _.
  by rewrite !big_ord_recr big_ord0 /= denom_1 Z.div_1_r; lia.
rewrite /l mko_listS big_ord_recr /= subnn /=.
rewrite [LHS](Z.div_mod v ('q[r]_n.+2)); last first.
  by have := denom_spos n.+1 r; lia.
rewrite Zplus_comm; congr (_ + _)%Z; last by lia.
rewrite [LHS]IH //.
apply: eq_bigr => /= u _; congr (_ * _)%Z.
suff -> : (n.+2 - u.+1 = (n.+1 - u.+1).+1)%nat by [].
by rewrite subSn // -ltnS.
Qed.

Definition bostro r (n : nat) : nat := 
  [arg min_(i < ord_max | (Z.of_nat n <? 'q[r]_(i: 'I_(n.+4)))%Z == true) i].-1.

Notation " 'bo[ r , n ]" := (bostro r n) 
  (at level 10, format " ''bo[' r ,  n ]").

Lemma bostro_0 r : bostro r 0 = 0%nat.
Proof. 
rewrite /bostro; case: arg_minnP => /=; last first.
  case => [] [|[|n]] //= _ _.
  move=> /(_ (Ordinal (isT : 1 < 4)%nat)) /=.
  by rewrite denom_1 ltnS ltn0 => /(_ isT).
apply/eqP/Z.ltb_lt.
apply: Z.lt_le_trans (_ : 'q[r]_1 <= _)%Z; first by rewrite denom_1; lia.
by apply: denom_le.
Qed.

Lemma bostro_1 r : 
 irrational r -> bostro r 1 = (if 'q[r]_2 == 1%Z then 2%nat else 1%nat).
Proof. 
move=> rI; rewrite /bostro; case: arg_minnP => /=.
  apply/eqP/Z.ltb_lt => /=.
  rewrite -(denom_1 r).
  apply: Z.le_lt_trans (irrational_denom_ltS _ _ _) => //.
  by apply: denom_le.
case => [] [|[|[|i]]] //= _ /eqP/Z.ltb_lt Hi; first by case: eqP; lia.
case: ('q[r]_2 =P 1%Z) => [Hq|Hnq] Hj.
  suff : (i.+2 < 3)%nat by case: (i).
  apply: (Hj (Ordinal (isT : (3 < 5)%nat))).
  apply/eqP/Z.ltb_lt => /=.
  by rewrite -Hq; apply: irrational_denom_ltS.
suff : (i.+2 < 2)%nat by case: (i).
apply: (Hj (Ordinal (isT : (2 < 5)%nat))).
apply/eqP/Z.ltb_lt => /=. 
by have := denom_leS 1 r; rewrite denom_1; lia.
Qed.

Lemma bostro_spos r n : irrational r -> (0 < bostro r n.+1)%nat.
Proof.
move=> rI; rewrite /bostro; case: arg_minnP => /= [|i Hi Hj].
  have := irrational_denom_lbound n.+3 _ rI.
  by case: Z.ltb_spec => //; lia.
case: i Hi Hj => //= [] [|[|[|]]] //; rewrite denom_1.
by case: Z.ltb_spec => //; lia.
Qed.

Lemma bostro_bound r n : 
  irrational r -> 
  ('q[r]_(bostro r n) <= Z.of_nat n < 'q[r]_(bostro r n).+1)%Z.
Proof.
move=> iR.  
rewrite /bostro; case: arg_minnP => /=; last first.
  move=> i /eqP /Zlt_is_lt_bool Hi Hf; split; last first.
    by case: (i : nat) Hi => //=; rewrite denom_0; lia.
  have i1B : (i.-1 < n.+4)%nat.
  apply: leq_ltn_trans (leq_pred _) (ltn_ord i).
  have /= := Hf (Ordinal i1B).
  case: Z.ltb_spec => //Hi1 Hi2.
  have : (i <= i.-1)%nat by apply: Hi2.
  case: (i : nat) => [| k] /=; first by rewrite denom_0; lia.
  by rewrite ltnn.
suff : (Z.of_nat n < 'q[r]_n.+3)%Z by case: Z.ltb_spec => //=; lia.
apply: Z.le_lt_trans (irrational_denom_lbound _ _ iR) _.
apply: Z.le_lt_trans (irrational_denom_ltS _ _ _) => //.
by apply: denom_le.
Qed.

Lemma bostro_denom r n :
  irrational r -> (1 < n)%nat -> bostro r (Z.to_nat ('q[r]_n)) = n.
Proof.
move=> rI; case: n => //= [] [//|n] _.
have := bostro_bound r (Z.to_nat ('q[r]_n.+2)) rI.
rewrite Z2Nat.id; last by apply: denom_pos.
set u := 'bo[_,_] => Hu.
case: (ltngtP u n.+2) => // Hl ; last first.
  suff : ('q[r]_n.+2 <  'q[r]_u)%Z by lia.
  by apply: irrational_denom_lt.
by have := denom_le r _ _ Hl; lia.
Qed.

Definition ostro r n i := 
  if (i <=  'bo[r, n].+1)%nat then 
    nth 0%Z (mko_list r (bostro r n) (Z.of_nat n)) (bostro r n - i.-1)
  else 0%Z.

Notation " 'o[ r , n ]_ i" := (ostro r n i) 
  (at level 10, format " ''o[' r ,  n ]_ i").

Lemma ostro_0l r n : 'o[r, 0]_n  = 0%Z.
Proof. by rewrite /ostro mko_list0 nth_nseq !if_same. Qed.

Lemma ostro_0 r n : 'o[r, n]_0  = 0%Z.
Proof. by rewrite /ostro /= subn0 nth_default // size_mko_list. Qed.

Lemma ostro_1 r n : 'o[r, n]_1  = 0%Z.
Proof. by rewrite /ostro /= subn0 nth_default // size_mko_list. Qed.

Lemma ostro_bostro r n i : ('bo[r, n].+1 < i)%nat ->  'o[r, n]_i = 0%Z.
Proof. by rewrite /ostro; case: leqP. Qed.

Lemma ostro_bostro_le r n i : 'o[r, n]_i != 0%Z -> (i <= 'bo[r, n].+1)%nat.
Proof. by case: leqP (ostro_bostro r n i) => // _ /(_ isT) ->. Qed.

Lemma ostro_bostro_neq r n : 
  irrational r -> 'o[r, n.+1]_('bo[r,n.+1].+1) != 0%Z.
Proof.
move=> rI.
rewrite /ostro ifT // subnn.
case: ('bo[_,_]) (bostro_spos r n rI) (bostro_bound r n.+1 rI) => //= k _ Hl.
have q_gt0 := denom_spos k r.
apply/eqP.
suff : (1 <= Z.pos (Pos.of_succ_nat n) /  'q[r]_k.+1)%Z.
  suff : (0 <= Z.pos (Pos.of_succ_nat n) /  'q[r]_k.+1)%Z by lia.
  by apply: Zdiv.Z_div_nonneg_nonneg; lia.
by apply: Z.div_le_lower_bound; lia.
Qed.

Lemma big_ostro r n : 
  irrational r -> 
  (Z.of_nat n = \big[Zplus/0%Z]_(i < 'bo[r, n].+1) ('o[r, n]_i.+1 * 'q[r]_i))%Z.
Proof.
move=> rI; case: n => [|n].
  by rewrite bostro_0 big_ord_recl big_ord0 denom_0; lia.
rewrite /ostro big_ord_recl /= denom_0 Zmult_0_r Zplus_0_l.
rewrite [LHS](big_mko_list r ('bo[r, n.+1]) (Z.of_nat n.+1)).
  by apply: eq_bigr => //= u _; rewrite ifT // ltnS.
by apply: bostro_spos.
Qed.

Lemma ostro_bound (r : R) (n : nat) i :
  irrational r -> 0 <= r -> (0 <=  'o[r, n]_i <= 'a[r]_i)%Z. 
Proof.
move=> rI rP; rewrite /ostro.
case: i => [|i] /=.
  by rewrite subn0 nth_default // size_mko_list.
rewrite ltnS; case: leqP => [iLb|bLi].
  have := mko_list_le r ( 'bo[r, n]) (Z.of_nat n)  ( 'bo[r, n] - i)  rI rP.
  rewrite subnBAC // ?subSnn ?addn1 //.
  apply.
  split; first by lia.
  by have := bostro_bound r n rI; lia.
by have := elt_ppos i.+1 r rP; lia.
Qed.

Lemma denom_2 r : 'a[r]_2 <> 0%Z -> 'q[r]_2 = 'a[r]_2.
Proof. by move=> ar_neq0; rewrite denom_rec // denom_1 denom_0; lia. Qed.

Lemma ostro2_lt r m : irrational r -> 0 <= r -> ('o[r,m]_2 < 'a[r]_2)%Z.
Proof.
move=> rI r_pos; rewrite /ostro.
case: leqP.
  by have := elt_pos r 0; have := irrational_elt_neq_0 r 0 rI; lia.
rewrite -denom_2; last by apply: irrational_elt_neq_0.
case: ('bo[_,_]) (bostro_bound r m) => // k /(_ rI) Hk _; rewrite subSS subn0.
set u := nth _ _ _; suff : (0 <= u < 'q[r]_2)%Z by lia.
have <- : (k.+2 - k = 2)%nat by rewrite -addn2 addnC addnK.
apply: mko_list_le_q => //; split ; first by apply: Zle_0_nat.
by lia.
Qed.

Lemma ostro_eq0 (r : R) (n : nat) i :
  irrational r -> 0 <= r -> 
  ('o[r, n]_i.+1 = 'a[r]_i.+1)%Z -> ('o[r, n]_i = 0)%Z. 
Proof.
move=> rI rP; rewrite /ostro.
case: i => [|i] /=.
  by rewrite subn0 nth_default // size_mko_list.
rewrite !ltnS; case: ltngtP => // [|Hi a_eq0]; last first.
  by case: (irrational_elt_neq_0 r i).
case E : ('bo[_,_]) => [//|i1] iL1 aH.
rewrite subSn //; apply: mko_list_eq0 => //; last first.
  by rewrite subnA ?subSn ?subnn // (leq_trans (_ : i1 <= i1.+1)%N) //.
split; first by lia.
by rewrite -E; have [] := bostro_bound _ n rI.
Qed.

Lemma gr_ostro_bound (n : nat) i : (0 <=  'o[gr, n]_i <= 1)%Z. 
Proof.
have : (0 <= 'o[gr, n]_i <= 'a[gr]_ i)%Z.
  apply: ostro_bound; first by apply: gr_irr.
  by have := grB; lra.
case: i => [|i] /=; first by rewrite elt_0; lia.
by rewrite gr_elt.
Qed.

Lemma gr_ostro_eq0 (n : nat) i :
  ('o[gr, n]_i.+1 = 1)%Z -> ('o[gr, n]_i = 0)%Z. 
Proof.
rewrite -(gr_elt i.+1) //; apply: ostro_eq0; first by apply: gr_irr.
by have := grB; lra.
Qed.

Lemma gr_big_ostro n : 
  (Z.of_nat n = 
  \big[Zplus/0%Z]_(i < 'bo[gr, n].+1) ('o[gr, n]_i.+1 * (Z.of_nat (fib i))))%Z.
Proof.
rewrite (big_ostro gr n); last by apply: gr_irr.
by apply: eq_bigr => /= i _; rewrite denom_gr_fib.
Qed.

Lemma Rmod1_ostro m r : 
   irrational r ->
  `| Z.of_nat m * r | = 
  `| \big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)| .
Proof.
move=> rI.
rewrite -[LHS](Rmod1_addz _
          (\big[Zplus/0%Z]_(i < 'bo[r, m].+1) (- ('o[r, m]_i.+1 * 'p[r]_i))%Z)).
rewrite [X in IZR X * r](big_ostro _ m rI) // !IZR_sum.
rewrite big_distrl /= -big_split /=.
congr (`|_|); apply: eq_bigr => i _.
by rewrite opp_IZR !mult_IZR /ahalton; lra.
Qed.

Definition fnz_ostro r m : option 'I_'bo[r, m].+1 :=
  [pick i : 'I_'bo[r, m].+1|
     ('o[r, m]_i.+1 != 0%Z) &&
    [forall j : 'I_'bo[r, m].+1, (j < i)%nat ==> ('o[r, m]_j.+1 == 0%Z)]].

Lemma fnz_ostro_none r m : irrational r -> fnz_ostro r m = None -> m = 0%nat.
Proof.
move=> rI; rewrite /fnz_ostro; case: pickP => // Hf _.
apply: Nat2Z.inj; rewrite (big_ostro r) // big1 //= => i _.
have [->|i_neq0] := Z.eq_dec ('o[r, m]_i.+1) 0; first by lia.
have := Hf [arg min_(j < i | 'o[r, m]_j.+1 != 0%Z) j].
case: arg_minnP => /=; first by apply/eqP.
move=> j -> j_min /= /forallP[k]; apply/implyP => kLj.
have := j_min k; rewrite leqNgt; case: eqP kLj; case: ltngtP => //.
by move=> _ _ _ /=; apply.
Qed.

Lemma fnz_ostro_some r m i : 
  fnz_ostro r m = Some i ->  
    [/\ (i <= 'bo[r, m])%nat, 
        'o[r, m]_i.+1 != 0%Z &
        forall j,  (j < i)%nat -> 'o[r, m]_j.+1 = 0%Z].
Proof.
rewrite /fnz_ostro; case: pickP => //= j /andP[Hj /forallP Hj1] [<-].
split => //; first by rewrite -ltnS.
move=> k Hk.
have oK : (k < 'bo[r, m].+1)%nat.
  by apply: leq_trans Hk _; apply: ltnW.
by have /= /implyP /(_ Hk)/eqP := Hj1 (Ordinal oK).
Qed.

Definition mostro r m : nat := if fnz_ostro r m is Some i then i else 0.
Local Notation " 'mo[ r , n ]" := (mostro r n) 
  (at level 10, format " ''mo[' r ,  n ]").

Lemma mostro_le_ostro r m : ('mo[r, m] <= 'bo[r, m])%N.
Proof.
by rewrite /mostro; case: fnz_ostro (fnz_ostro_some r m) => // k /(_ k) [].
Qed.

Lemma mostro_leq0_ostro r m i : (i < 'mo[r, m])%N -> 'o[r, m]_i.+1 = 0%Z.
Proof.
rewrite /mostro; case: fnz_ostro (fnz_ostro_some r m) => // k /(_ k) [] // _ _.
by apply.
Qed.

Lemma mostro0 r : 'mo[r, 0] = 0%N.
Proof.
rewrite /mostro /fnz_ostro; case: pick; rewrite ?ostro_0l ?bostro_0 //=.
by case; case.
Qed.

Lemma mostro_neq0 r m :
  irrational r -> (0 < m)%N -> 'o[r, m]_('mo[r, m].+1) != 0%Z.
Proof.
move=> Hr; rewrite /mostro.
by case: fnz_ostro (fnz_ostro_none r m Hr) (fnz_ostro_some r m) => 
    [k _ /(_ k) []|->].
Qed.

Lemma big_ordD (R : Type) (idx : R) (op : Monoid.com_law idx) 
               (f : nat -> R) (m n : nat) :
  \big[op/idx]_(i < m + n)  f i = 
  op (\big[op/idx]_(i < m)  f i) (\big[op/idx]_(i < n)  f (m + i)%N).
Proof.
elim: n => [|n IH]; first by rewrite addn0 big_ord0 !Monoid.simpm.
by rewrite !addnS !big_ord_recr /= IH -!Monoid.mulmA.
Qed.

Lemma half_big (R : Type) (idx : R) (op : Monoid.com_law idx) 
  (f : nat -> R) (n : nat) :
  \big[op/idx]_(i < n)  f i = 
  op (\big[op/idx]_(i < uphalf n)  f i.*2) (\big[op/idx]_(i < n./2)  f i.*2.+1).
Proof.
elim/ltn_ind: n => [] [|[|n]] IH.
- by rewrite  /= !big_ord0 // !Monoid.simpm.
- by rewrite /= !big_ord_recl !big_ord0 !Monoid.simpm.
rewrite /= !big_ord_recr /= IH //.
case: {IH}n => [|n].
  by rewrite !big_ord0 /= !Monoid.simpm /= !Monoid.simpm.
set x := \big[op/idx]_(i < _) _; set y := \big[op/idx]_(i < _) _.
rewrite uphalfK -!Monoid.mulmA; congr (op _ _).
case E : odd; first by rewrite odd_halfK //= [RHS]Monoid.mulmC !Monoid.simpm.
rewrite even_halfK ?add0n //; last by rewrite E.
rewrite [RHS]Monoid.mulmC -!Monoid.mulmA; congr (op _ _).
by rewrite [RHS]Monoid.mulmC.
Qed.

Lemma bound_left_big m r :
  irrational r -> 0 <= r -> 
  let i := 'mo[r, m] in
  ('o[r, m]_i.+1 - 1) * 't[r]_i + 't[r]_i.+1 <  
  Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)).
Proof.
move=> r_irr r_pos i.
have [m_pos|] := ltnP 0%N m; last first.
  rewrite {}/i; case: m => //.
  rewrite mostro0 /= ostro_0l halton_0 halton_1 bostro_0.
  rewrite big_ord_recl /= big_ord0.
  by rewrite ostro_0l Rmult_0_l Rplus_0_l Rabs_R0; have := frac_bound r; lra.
have iLbo := mostro_le_ostro r m.
have /eqP o_neq0 := mostro_neq0 _ _ r_irr m_pos.
have o_eq0 := mostro_leq0_ostro r m.
rewrite -/i in iLbo o_neq0 o_eq0.
rewrite -ltnS in iLbo.
have F1 j : (0 <= 'o[r, m]_j <= 'a[r]_j)%Z by apply: ostro_bound.
have F2 : (0 <= 'o[r, m]_i.+2 <= 'a[r]_i.+2 - 1)%Z.
  have : (0 <= 'o[r, m]_i.+2 <= 'a[r]_i.+2)%Z by apply: ostro_bound.
  by have := ostro_eq0 _ m i.+1 r_irr r_pos; lia.
rewrite -(subnK (ltnW iLbo)) addnC.
rewrite (@big_ordD _ _ _ (fun i => 'o[r, m]_i.+1 *  'ta[r]_i)) /=.
rewrite big1 ?Rplus_0_l; last by move=> j _; rewrite o_eq0 //; lra.
rewrite (@half_big _ _ _ (fun j => 'o[r, m]_(i + j).+1 *  'ta[r]_(i + j))) /=.
have F3 k l : (- 1) ^ (k + l.*2).+1 = (- 1) ^ k.+1.
  by rewrite -addSn pow_add -mul2n pow_1_even; lra.
have F4 k l n : k * (l * n) = l * (k * n) by lra.
under eq_bigr do rewrite ahaltonE F3 F4.
rewrite -big_distrr; set v1 := _ ^ _; rewrite /=.
set v1B := \big[_/_]_(_ < _) _.
have {}F3 k l : (- 1) ^ (k + l.*2.+1).+1 = (- 1) ^ k.+2.
  by rewrite -addSn -addSnnS pow_add -mul2n pow_1_even; lra.
under eq_bigr do rewrite ahaltonE F3 F4.
rewrite -big_distrr; set v2 := _ ^ _; rewrite /=.
set v2B := \big[_/_]_(_ < _) _.
have -> : v1 * v1B + v2 * v2B = v1 * (v1B - v2B) 
  by rewrite /v1 /v2 /v1B /v2B /=; lra.
rewrite Rabs_mult pow_1_abs Rmult_1_l.
have -> : ('o[r, m]_i.+1 - 1) *  't[r]_i  +  't[r]_i.+1 = 
         'o[r, m]_i.+1 * 't[r]_i  -  ('t[r]_i - 't[r]_i.+1) by lra.
apply: Rlt_le_trans (_ : Rabs v1B - Rabs v2B <= _); last by split_Rabs; lra.
have {}F3 a b c d : a <= b -> c < d -> a - d < b - c by lra.
apply: F3.
  rewrite Rabs_pos_eq; last first.
    rewrite /v1B; elim: uphalf => [|u IH]; first by rewrite big_ord0; lra.
    rewrite big_ord_recr /=.
    set x := \big[_/_]_(_ < _) _  in IH; rewrite -/x.
    suff : 0 <= 'o[r, m]_(i + u.*2).+1 *  't[r]_(i + u.*2) by lra.
    apply: Rmult_le_pos.
      by apply: IZR_le;  have := ostro_bound r m (i + u.*2).+1 r_irr r_pos; lia.
    by apply: halton_pos.
  have : (0 < uphalf (( 'bo[r, m]).+1 - i))%nat.
    rewrite -[1%nat]/(uphalf 1); apply: uphalf_leq.
    by rewrite ltn_subRL addn0.
  rewrite /v1B; case: uphalf => // k _.
  rewrite big_ord_recl /= !addn0.
  set v3B := \big[_/_]_(_ < _ | _) _.
  suff : 0 <= v3B by lra.
  rewrite {}/v3B; elim: k => [|u IH]; first by rewrite big_ord0; lra.
  rewrite big_ord_recr /=; set v := (_ + _)%nat.
  apply: Rplus_le_le_0_compat; first by apply: IH.
  apply: Rmult_le_pos.
    by apply: IZR_le;  have := ostro_bound r m v.+1 r_irr r_pos; lia.
  by apply: halton_pos.
rewrite Rabs_pos_eq; last first.
  rewrite /v2B; elim: (_./2) => [|u IH]; first by rewrite big_ord0; lra.
  rewrite big_ord_recr /=; set v := (_ + _)%nat.
  apply: Rplus_le_le_0_compat; first by apply: IH.
  apply: Rmult_le_pos.
    by apply: IZR_le;  have := ostro_bound r m v.+1 r_irr r_pos; lia.
  by apply: halton_pos.
have F5 : 't[r]_i.+1 < 't[r]_i.
  case: {iLbo o_neq0 o_eq0 F2 v1 v1B v2 v2B}i => [|i].
    by rewrite halton_0 halton_1; have := frac_bound r; lra.
  by apply/halton_ltS/irrational_elt_neq_0.
rewrite /v2B; case: (_./2) => [|k]; first by rewrite big_ord0; lra.
apply: Rle_lt_trans (_ : 
  \big[Rplus/0]_(j < k.+1) ( 'a[r]_(i + j.*2.+1).+1 *  't[r]_(i + j.*2.+1)) -
  't[r]_i.+1 < _); last first.
  suff : \big[Rplus/0]_(j < k.+1)
           ( 'a[r]_(i + j.*2.+1).+1 *  't[r]_(i + j.*2.+1))  < 't[r]_i  by lra.
  elim: k {iLbo o_neq0 o_eq0 F2 v1 v1B v2 v2B F5}i => [i |k IH i].
    rewrite big_ord_recr big_ord0 /= ?addn1 Rplus_0_l.
    have : 'a[r]_i.+2 *  't[r]_i.+1 = 't[r]_i - 't[r]_i.+2.
      by have := (halton_rec _ _ (irrational_elt_neq_0 r i r_irr)); lra.
    suff : 0 < 't[r]_i.+2 by lra.
    by apply: irrational_halton_pos.
  rewrite big_ord_recl /= /bump /=.
  have F5 k1 l : (k1 + (1 + l).*2.+1 = k1.+2 + l.*2.+1)%nat.
    by rewrite add1n !addSnnS doubleS.
  under eq_bigr do rewrite F5.
  rewrite addn1.
  have -> : 'a[r]_i.+2 *  't[r]_i.+1 = 't[r]_i - 't[r]_i.+2.
    by have := (halton_rec _ _ (irrational_elt_neq_0 r i r_irr)); lra.
  set x := \big[_/_]_(_ < _) _.
  suff : x < 't[r]_i.+2 by lra.
  by apply: IH.
rewrite !big_ord_recl /= addn1.
set x := \big[_/_]_(_ < _) _; set y := \big[_/_]_(_ < _) _.
suff : 'o[r, m]_i.+2 *  't[r]_i.+1  + x <=
       ('a[r]_i.+2  -1) *  't[r]_i.+1  + y by lra.
apply: Rplus_le_compat.
  apply: Rmult_le_compat_r; first by apply: halton_pos.
  by rewrite -minus_IZR; apply: IZR_le; lia.
rewrite {}/x {}/y.
elim: k => [|k IH]; first by rewrite !big_ord0; lra.
rewrite !big_ord_recr /=.
set v := (_ + _)%nat.
set x := \big[_/_]_(_ < _) _ in IH; set y := \big[_/_]_(_ < _) _ in IH.
rewrite -/x -/y.
set x1 := _ * _; set y1 := _ * _.
suff : x1 <= y1 by lra.
apply: Rmult_le_compat_r; first by apply: halton_pos.
apply: IZR_le.
have := F1 v.+1; lia.
Qed.

Lemma bound_left_big_alt_strict m r : 
  irrational r -> 0 <= r ->  (0 < m)%N -> 
  ('mo[r,m] != 'bo[r, m]) || ('o[r, m]_('mo[r,m].+1) != 1%Z) ->
  't[r]_('bo[r, m]) <  
  Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)).
Proof.
move=> rI r_pos m_pos m_cond.
pose i := 'mo[r, m].
have iLbo := mostro_le_ostro r m.
have /eqP o_neq0 := mostro_neq0 _ _ rI m_pos.
have o_eq0 := mostro_leq0_ostro r m.
rewrite -/i in iLbo o_neq0 o_eq0 m_cond.
rewrite leq_eqVlt in iLbo.
have /orP[/eqP iE|{}iLbo] := iLbo.
  rewrite -iE; rewrite -iE eqxx /= in m_cond.
  have {m_cond}/eqP  m_cond := m_cond.
  rewrite big_ord_recr /= big1.
    rewrite Rplus_0_l ahaltonE 2!Rabs_mult pow_1_abs Rmult_1_l !Rabs_pos_eq.
    - suff : (1 < 'o[r, m]_i.+1).
        by have := irrational_halton_pos _ i rI; nra.
      by apply: IZR_lt; have := ostro_bound _ m i.+1 rI r_pos; lia.
    - by apply: halton_pos.
    by apply: IZR_le; have := ostro_bound _ m i.+1 rI r_pos; lia.
  by case => j /= jLi _; rewrite o_eq0 //; lra.
rewrite -ltnS in iLbo.
apply: Rle_lt_trans (bound_left_big m _ rI r_pos) => //.
rewrite -/i.
suff: 't[r]_( 'bo[r, m])  <=  't[r]_i.+1.
  suff : 0 <= ( 'o[r, m]_i.+1 - 1) *  't[r]_i by lra.
  apply: Rmult_le_pos; last by apply: halton_pos.
  suff : 1 <= 'o[r, m]_i.+1 by lra.
  by apply: IZR_le; have := ostro_bound _ m i.+1 rI r_pos; lia.
rewrite ltnS leq_eqVlt in iLbo.
have /orP[/eqP<-|{}iLbo] := iLbo; first by lra.
by apply/Rlt_le/halton_lt; first by apply: irrational_elt_neq_0.
Qed.

Lemma bound_left_big_alt m r : 
  irrational r -> 0 <= r ->  (0 < m)%N -> 't[r]_('bo[r, m]) <=  
  Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)).
Proof.
move=> rI r_pos m_pos.
have [moE |/eqP/negPf moE] := 'mo[r,m] =P 'bo[r, m]; last first.
  apply/Rlt_le/bound_left_big_alt_strict => //.
  by rewrite moE.
have [oE |/eqP/negPf oE] := 'o[r, m]_('mo[r,m].+1) =P 1%Z; last first.
  apply/Rlt_le/bound_left_big_alt_strict => //.
  by rewrite oE orbT.
rewrite big_ord_recr /= big1 => [|i _].
  rewrite Rplus_0_l ahaltonE 2!Rabs_mult pow_1_abs Rmult_1_l -moE oE.
  rewrite Rabs_R1 Rabs_pos_eq //; try lra.
  by apply: halton_pos.
rewrite mostro_leq0_ostro; first by lra.
by rewrite moE.
Qed.

Lemma bound_right_big m r : 
  irrational r -> 0 <= r -> 
  let i := 'mo[r, m] in
  Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)) <
  'o[r, m]_i.+1 * 't[r]_i + 't[r]_i.+1.
Proof.
move=> r_irr r_pos i.
have [m_pos|] := ltnP 0%N m; last first.
  rewrite {}/i; case: m => //.
  rewrite mostro0 /= ostro_0l halton_0 halton_1 bostro_0.
  rewrite big_ord_recl /= big_ord0.
  rewrite ostro_0l Rmult_0_l Rplus_0_l Rabs_R0.
   have := frac_bound r; have := frac_neq_0_irrational r r_irr; lra.
have iLbo := mostro_le_ostro r m.
have /eqP o_neq0 := mostro_neq0 _ _ r_irr m_pos.
have o_eq0 := mostro_leq0_ostro r m.
rewrite -/i in iLbo o_neq0 o_eq0.
rewrite -ltnS in iLbo.
have tri_pos : 0 <= 't[r]_i by apply: halton_pos.
have oB j : (0 <= 'o[r, m]_j <= 'a[r]_j)%Z by apply: ostro_bound.
rewrite -(subnK (ltnW iLbo)) addnC.
rewrite (@big_ordD _ _ _ (fun i => 'o[r, m]_i.+1 *  'ta[r]_i)) /=.
rewrite big1 ?Rplus_0_l; last by move=> j _; rewrite o_eq0 //; lra.
rewrite (@half_big _ _ _ (fun j => 'o[r, m]_(i + j).+1 *  'ta[r]_(i + j))) /=.
have m1E k l : (- 1) ^ (k + l.*2).+1 = (- 1) ^ k.+1.
  by rewrite -addSn pow_add -mul2n pow_1_even; lra.
have mAC k l n : k * (l * n) = l * (k * n) by lra.
under eq_bigr do rewrite ahaltonE m1E mAC.
rewrite -big_distrr; set v1 := _ ^ _; rewrite /=.
set v1B := \big[_/_]_(_ < _) _.
have {}m1E k l : (- 1) ^ (k + l.*2.+1).+1 = (- 1) ^ k.+2.
  by rewrite -addSn -addSnnS pow_add -mul2n pow_1_even; lra.
under eq_bigr do rewrite ahaltonE m1E mAC.
rewrite -big_distrr; set v2 := _ ^ _; rewrite /=.
set v2B := \big[_/_]_(_ < _) _.
have -> : v1 * v1B + v2 * v2B = v1 * (v1B - v2B)
  by rewrite /v1 /v2 /v1B /v2B /=; lra.
rewrite Rabs_mult pow_1_abs Rmult_1_l.
have v1BB : 't[r]_i <= v1B.
  have : (0 < uphalf (( 'bo[r, m]).+1 - i))%nat.
    rewrite -[1%nat]/(uphalf 1); apply: uphalf_leq.
    by rewrite ltn_subRL addn0.
  rewrite /v1B; case: uphalf => // [] k _ /=.
  rewrite big_ord_recl !addn0.
  have : 't[r]_i  <=  'o[r, m]_i.+1 *  't[r]_i.
    suff : 1 <= 'o[r, m]_i.+1 by nra.
    by apply: IZR_le; have:= oB i.+1; lia.
  set v3B := \big[_/_]_(_ < _) _.
  suff : 0 <= v3B by lra.
  rewrite /v3B; elim: {v3B}k => [|k IH]; first by rewrite big_ord0; lra.
  rewrite big_ord_recr /=; set v := (_ + _)%nat.
  apply: Rplus_le_le_0_compat; first by apply: IH.
  apply: Rmult_le_pos; first by apply: IZR_le; have := oB v.+1; lia.
  by apply: halton_pos.
have v2BB : v2B <= 't[r]_i.
  rewrite /v2B; set k := _./2.
  apply: Rle_trans (_ : 
    \big[Rplus/0]_(j < k) ( 'a[r]_(i + j.*2.+1).+1 *  't[r]_(i + j.*2.+1)) 
          <= _); last first.
    move: k => k.
    elim: k {iLbo o_neq0 o_eq0 v1 v1B v2 v2B tri_pos v1BB}i => [i |k IH i].
      by rewrite big_ord0; apply: halton_pos.
    rewrite big_ord_recl /= /bump /=.
    have F5 k1 l : (k1 + (1 + l).*2.+1 = k1.+2 + l.*2.+1)%nat.
      by rewrite add1n !addSnnS doubleS.
    under eq_bigr do rewrite F5.
    rewrite addn1.
    have -> : 'a[r]_i.+2 *  't[r]_i.+1 = 't[r]_i - 't[r]_i.+2.
      by have := (halton_rec _ _ (irrational_elt_neq_0 r i r_irr)); lra.
    set x := \big[_/_]_(_ < _) _.
    suff : x <= 't[r]_i.+2 by lra.
    by apply: IH.
  elim: k => [|k IH]; first by rewrite !big_ord0; lra.
  rewrite !big_ord_recr /=; set v := (_ + _)%nat.
  apply: Rplus_le_compat; first by apply: IH.
  apply: Rmult_le_compat; first by apply: IZR_le; have := oB v.+1; lia.
  - by apply: halton_pos.
  - by apply: IZR_le; have := oB v.+1; lia.
  by lra.
apply: Rle_lt_trans (_ : v1B < _).
  rewrite Rabs_pos_eq; try lra.
  suff : 0 <= v2B by lra.
  rewrite /v2B; set k := _./2.
  elim: k => [|k IH]; first by rewrite big_ord0; lra.
  rewrite big_ord_recr /=; apply Rplus_le_le_0_compat; first by apply: IH.
  rewrite /v2B; set v := (_ + _)%nat.
  apply: Rmult_le_pos; first by apply: IZR_le; have := oB v.+1; lia.
  by apply: halton_pos.
have : (0 < uphalf (( 'bo[r, m]).+1 - i))%nat.
  rewrite -[1%nat]/(uphalf 1); apply: uphalf_leq.
  by rewrite ltn_subRL addn0.
rewrite /v1B; case: uphalf => // k _.
rewrite big_ord_recl /= !addn0; apply: Rplus_lt_compat_l.
rewrite /bump /=.
have F5 k1 l : (k1 + (1 + l).*2 = k1.+2 + l.*2)%nat.
  by rewrite add1n !addSnnS doubleS.
under eq_bigr do rewrite F5.
apply: Rle_lt_trans (_ : 
    \big[Rplus/0]_(j < k) ('a[r]_(i.+2 + j.*2).+1 *  't[r]_(i.+2 + j.*2)) < _).
  elim: k => [| k IH]; first by rewrite !big_ord0; lra.
  rewrite !big_ord_recr /=; apply: Rplus_le_compat; first by apply: IH.
  set v := (_ + _)%nat.
  apply: Rmult_le_compat_r; first by apply: halton_pos.
  by apply: IZR_le; have := oB v.+1; lia.
elim: k {iLbo o_neq0 o_eq0 tri_pos v1 v1B v2 v2B v1BB v2BB}i => [i| k IH i].
  by rewrite big_ord0; apply: irrational_halton_pos.
rewrite big_ord_recl /= /bump /= addn0.
under eq_bigr do rewrite F5.
have -> : 'a[r]_i.+3 *  't[r]_i.+2 = 't[r]_i.+1 - 't[r]_i.+3.
  by have := (halton_rec _ _ (irrational_elt_neq_0 r i.+1 r_irr)); lra.
set x := \big[_/_]_(_ < _) _.
suff : x < 't[r]_i.+3 by lra.
by apply: IH.
Qed.

Lemma Rmod1_ostro_Rabs_3p m r : 
  irrational r -> 0 <= r -> 'o[r, m]_2 = 0%Z -> 'o[r, m]_3 = 0%Z ->
  `| Z.of_nat m * r | = 
   Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)).
Proof.
move=> rI r_pos o2_eq0 o3_eq0; rewrite Rmod1_ostro //.
apply: Rmod1_small.
have [m_pos|] := ltnP 0%N m; last first.
  case: {o2_eq0 o3_eq0}m => //.
  rewrite bostro_0 big_ord_recl /= big_ord0 ostro_0l.
  by split_Rabs; lra.
pose i := 'mo[r, m].
have iLbo := mostro_le_ostro r m.
have /eqP o_neq0 := mostro_neq0 _ _ rI m_pos.
have o_eq0 := mostro_leq0_ostro r m.
rewrite -/i in iLbo o_neq0 o_eq0.
have iL2 : (2 < i)%nat.
  by case: (i) o_neq0 => [|[|[|j]]]; rewrite ?ostro_1.
apply: Rlt_le.
apply:  Rlt_le_trans (bound_right_big _ _ _ _) _ => //.
rewrite -/i.
apply:  Rle_trans (_ : 'a[r]_i.+1 *  't[r]_i + 't[r]_i.+1 <= _).
  have Hj := halton_pos i r; have Hj1 := halton_pos i.+1 r.
  apply: Rplus_le_compat_r => //.
  apply: Rmult_le_compat_r => //.
  by apply: IZR_le; have := ostro_bound _ m i.+1 rI r_pos; lia.
rewrite -[i : nat]prednK; last by case: (i : nat) iL2.
rewrite halton_rec; last by apply: irrational_elt_neq_0.
suff : 't[r]_i.-1 </ 2 by lra.
apply: Rle_lt_trans (halton_2 r).
rewrite leq_eqVlt in iL2;  have /orP[/eqP<-/=|iL3] := iL2; first by lra.
apply/Rlt_le/halton_lt; first by apply: irrational_elt_neq_0.
by case: (i : nat) iL3.
Qed.

Lemma Rmod1_ostro_Rabs_half2 m r : 
  irrational r -> 0 <= r -> `{r} < / 2 -> 
  'o[r, m]_2 = 0%Z -> 'o[r, m]_3 != 0%Z ->
  `| Z.of_nat m * r | = 
   Rabs (\big[Rplus/0%R]_(i < 'bo[r, m].+1) ('o[r, m]_i.+1 * 'ta[r]_i)).
Proof.
move=> rI r_pos r_half o2_eq0 o3_neq0; rewrite Rmod1_ostro //.
have m_pos : (0 < m)%N by case: (m) o3_neq0; rewrite ?ostro_0l.
apply: Rmod1_small.
pose i := 'mo[r, m].
have iLbo := mostro_le_ostro r m.
have /eqP o_neq0 := mostro_neq0 _ _ rI m_pos.
have o_eq0 := mostro_leq0_ostro r m.
rewrite -/i in iLbo o_neq0 o_eq0.
have iE2 : i = 2%nat :> nat.
  case: (leqP i 2) => [|i_gt2].
    by case: (i) o_neq0 => [|[|[|]]]; rewrite ?ostro_1.
  by case/eqP: o3_neq0; apply: o_eq0.
apply: Rlt_le.
apply:  Rlt_le_trans (bound_right_big _ _ _ _) _ => //.
rewrite -/i.
apply:  Rle_trans (_ : 'a[r]_i.+1 *  't[r]_i + 't[r]_i.+1 <= _).
  have Hi := halton_pos i r; have Hi1 := halton_pos i.+1 r.
  apply: Rplus_le_compat_r => //.
  apply: Rmult_le_compat_r => //.
  by apply: IZR_le; have := ostro_bound _ m i.+1 rI r_pos; lia.
rewrite iE2.
rewrite ['t[_]_3]halton_rec; last by apply: irrational_elt_neq_0.
suff : 't[r]_1 </ 2 by lra.
by rewrite halton_1.
Qed.

Lemma Rmod1_ostro_Rabs_half1 m r : 
  irrational r -> 0 <= r -> `{r} < / 2 -> 'o[r, m]_2 != 0%Z ->
  't[r]_2 < `| Z.of_nat m * r |.
Proof.
move=> rI r_pos r_half o2_neq0; rewrite Rmod1_ostro //.
have m_pos : (0 < m)%N by case: (m) o2_neq0; rewrite ?ostro_0l.
apply: Rmod1_0Lt1 (_ : _ < _ < 1 - 't[r]_1).
  split; first by apply: halton_pos.
  by apply/Rlt_le/halton_ltS/irrational_elt_neq_0.
have /eqP F1 := o2_neq0.
have bo_gt1 : (1 < ( 'bo[r, m]).+1)%N.
  case: (m) F1 o2_neq0 => [| m1 F1 o2_neq0]; first by rewrite ostro_0l.
  by rewrite ltnS; apply: bostro_spos.
have moE : 'mo[r, m] = 1%N.
  case: (leqP ('mo[r, m]) 1) => [|i_gt1].
    have := mostro_neq0 r m rI m_pos.
    by case: mostro o2_neq0 => [|[]]; rewrite ?ostro_1.
  by case/eqP: o2_neq0; apply: mostro_leq0_ostro.
split.
  apply: Rle_lt_trans (bound_left_big _ _ _ _) => //.
  suff : 0 <= ( 'o[r, m]_2 - 1) *  't[r]_1  by rewrite moE; lra.
  apply: Rmult_le_pos; last by apply: halton_pos.
  suff: 1 <= 'o[r, m]_2 by lra.
  apply: IZR_le.
  by have := ostro_bound _ m 2 rI r_pos; lia.
apply: Rlt_le_trans (bound_right_big _ _ _ _) _ => //.
rewrite moE.
apply: Rle_trans (_ : ('a[r]_2 - 1) *  't[r]_1  +  't[r]_2 <= _).
  apply: Rplus_le_compat_r.
  apply: Rmult_le_compat_r; first by apply: halton_pos.
  rewrite -minus_IZR; apply: IZR_le.
  suff: ('o[r, m]_2 <  'a[r]_2)%Z by lia.
  by apply: ostro2_lt.
suff : 'a[r]_2 *  't[r]_1  +  't[r]_2  <=  't[r]_0 by rewrite halton_0; lra.
rewrite ['t[r]_2]halton_rec; first by lra.
by apply: irrational_elt_neq_0.
Qed.

Lemma ostro2_mhalf m r : 
  irrational r -> 0 <= r -> / 2  < `{r} -> 'o[r, m]_2 = 0%Z.
Proof.
move=> rI r_pos r_half.
have : ('o[r,m]_2 < 'a[r]_2)%Z by apply: ostro2_lt.
have := ostro_bound _ m 2 rI r_pos; have := elt2_mhalf _ rI r_pos r_half.
by lia.
Qed.

Lemma Rmod1_ostro_mhalf1 r m : 
  irrational r -> 0 <= r -> / 2 < `{r} -> (1 < 'o[r, m]_3)%Z ->
  `|r| < `| Z.of_nat m * r |.
Proof.
move=> rI r_pos r_half o3_pos; rewrite Rmod1_ostro //.
have m_pos : (0 < m)%N by case: (m) o3_pos; rewrite ?ostro_0l.
have -> : `|r| = 1 - `{r} by rewrite /Rmod1 /Rmin; case: Rle_dec; lra.
apply: Rmod1_0Lt1 (_ : _ < _ < 1 - (1 - `{r})).
  by have := frac_bound r; lra.
have F1 : ('o[r, m]_3 <> 0)%Z by lia.
have F2 : (2 < ( 'bo[r, m]).+1)%N.
  rewrite ltnS; apply/leP.
  suff : (( 'bo[r, m]).+1 < 3)%coq_nat ->  'o[r, m]_3 = 0%Z by lia.
  by move/leP; apply: ostro_bostro.
have /eqP o_neq0 := mostro_neq0 _ _ rI m_pos.
have moE : 'mo[r, m] = 2%N.
  case: (leqP ('mo[r, m]) 2) => [|i_gt2].
    case: ('mo[r, m]) o_neq0 => [|[|[]]] //; first by rewrite ostro_1.
    by rewrite ostro2_mhalf.
  by case: F1; apply: mostro_leq0_ostro.
split.
  have -> : 1 - `{r}  = 't[r]_2.
    rewrite halton_rec; last by apply: irrational_elt_neq_0.
    by rewrite halton_0 halton_1 elt2_mhalf //; lra.
  apply: Rle_lt_trans (bound_left_big _ _ _ _) => //.
  rewrite moE.
  suff : (2 <= 'o[r, m]_3).
    by have := halton_pos 2 r; have := halton_pos 3 r; nra.
  by apply: IZR_le; lia.
have -> : 1 - (1 - `{r})  = 't[r]_1 by rewrite halton_1; lra.
apply: Rlt_le_trans (bound_right_big _ _ _ _) _ => //.
rewrite moE.
have -> : 't[r]_1 = 'a[r]_3 *  't[r]_2  +  't[r]_3.
  rewrite ['t[r]_3]halton_rec; first by lra.
  by apply: irrational_elt_neq_0.
apply: Rplus_le_compat_r.
apply: Rmult_le_compat_r; first by apply: halton_pos.
by apply: IZR_le; have := ostro_bound r m 3 rI r_pos; lia.
Qed.

Lemma elt_1_2_ineq r : 
  irrational r -> 0 <= r -> (0 < 'a[r]_3)%Z -> / 2 < `{r} ->
  r <= 'a[r]_1 + / ('a[r]_2 + / (2 * 'a[r]_3)).
Proof.
move=> rI r_pos mH aH.
have aH1 : 1 <= 'a[r]_3 by apply: IZR_le; lia.
rewrite -{1}(zeta_0 r) 2!zeta_rec elt2_mhalf //.
apply: Rplus_le_compat_l.
apply: Rinv_le_contravar.
  suff : 0 <= / (2 *  'a[r]_3) by lra.
  by apply: Rinv_0_le_compat; lra.
apply: Rplus_le_compat_l.
apply: Rinv_le_contravar.
  rewrite zeta_frac_part in aH1.
  by have := Zfloor_bound (zeta r 2); lra.
rewrite zeta_frac_part in aH1 *.
by have := Zfloor_bound (zeta r 2); lra.
Qed.

Lemma Rmod1_ostro_mhalf2 r m : 
  irrational r -> 0 <= r -> / 2 < `{r} -> ('o[r, m]_3 = 1)%Z ->
  't[r]_3 < `| Z.of_nat m * r |.
Proof.
move=> rI r_pos r_half o3_eq1; rewrite Rmod1_ostro //.
have m_pos : (0 < m)%N by case: (m) o3_eq1; rewrite ?ostro_0l.
apply: Rmod1_0Lt1 (_ : _ < _ < 1 - (1 - ('t[r]_3 + 't[r]_2))).
  split; first by apply: halton_pos.
  suff : 2 * 't[r]_3 +  't[r]_2 <= 1 by lra.
  rewrite ['t[r]_3]halton_rec; last by apply: irrational_elt_neq_0.
  rewrite halton_1 halton_rec; last by apply: irrational_elt_neq_0.
  rewrite halton_1 halton_0 elt2_mhalf // Rmult_1_l.
  have Hr :  r <= 'a[r]_1 + / ('a[r]_2 + / (2 * 'a[r]_3)).
    apply: elt_1_2_ineq => //.
    by have := ostro_bound _ m 3 rI r_pos; lia.
  rewrite elt2_mhalf // in Hr.  
  have Hf : 0 < 'a[r]_3.
    by apply: IZR_lt; have := ostro_bound r m 3 rI r_pos; lia.
  have HH : / (1 + / (2 *  'a[r]_3)) = 2 *  'a[r]_3 / (1 +  2 *  'a[r]_3).
    by field; lra.
  rewrite HH in Hr.
  have Hr1 : (r - 'a[r]_1) * (1 + 2 *  'a[r]_3) <= 2 *  'a[r]_3.
    have {2}-> : 2 *  'a[r]_3 = 
              (2 *  'a[r]_3 / (1 + 2 *  'a[r]_3)) * (1 + 2 *  'a[r]_3).
      by field; lra.
    apply: Rmult_le_compat_r; first by lra.
    by lra.
  by rewrite elt_1 -[_ - _]/`{r} in Hr1; lra.
have -> :  1 - (1 -  ('t[r]_3  +  't[r]_2))  = 't[r]_3 + 't[r]_2 by lra.
have F1 : ('o[r, m]_3 <> 0)%Z by lia.
have F2 : (2 < ( 'bo[r, m]).+1)%N.
  rewrite ltnS; apply/leP.
  suff : (( 'bo[r, m]).+1 < 3)%coq_nat ->  'o[r, m]_3 = 0%Z by lia.
  by move/leP; apply: ostro_bostro.
have /eqP o_neq0 := mostro_neq0 _ _ rI m_pos.
have moE : 'mo[r, m] = 2%N.
  case: (leqP ('mo[r, m]) 2) => [|i_gt2].
    case: ('mo[r, m]) o_neq0 => [|[|[]]] //; first by rewrite ostro_1.
    by rewrite ostro2_mhalf.
  by case: F1; apply: mostro_leq0_ostro.
split.
  apply: Rle_lt_trans (bound_left_big _ _ _ _) => //.
  by rewrite moE o3_eq1; lra.
apply: Rlt_le_trans (bound_right_big _ _ _ _) _ => //.
by rewrite moE o3_eq1; lra.
Qed.

Lemma ostro_best_approx r n : 
  irrational r -> 0 <= r -> (0 < n)%nat -> 
  't[r]_(bostro r n) <= `| Z.of_nat n * r|.
Proof.
move=> rI r_pos n_pos.
have [orn2_eq0|/eqP orn2_neq0] := Z.eq_dec ('o[r, n]_2) 0%Z.
  have [orn3_eq0|/eqP orn3_neq0] := Z.eq_dec ('o[r, n]_3) 0%Z.
    rewrite Rmod1_ostro_Rabs_3p //.
    by apply: (@bound_left_big_alt n r).
 have [rLh|hLr] := Rle_lt_dec `{r} (/ 2).
    have rLh' : `{r} < / 2.
      suff : `{r} <> / 2 by lra.
      move=> rE; have : ~ irrational (/ 2).
        by move=> /irrational_inv H1; case: (irrational_IZR 2).
      by rewrite -rE; have /irrational_frac := rI.
    rewrite Rmod1_ostro_Rabs_half2 //.
    by apply: (@bound_left_big_alt n r).
  have b_gt1 : (1 < 'bo[r, n])%nat by rewrite -ltnS; apply: ostro_bostro_le.
  have [o_eq1|o_neq1] := Z.eq_dec ('o[r, n]_3) 1%Z.
    move: b_gt1; rewrite leq_eqVlt => /orP[/eqP b_eq2|b_gt2]; last first.
      apply: Rle_trans (_ : 't[r]_3 <= _); first by apply: halton_le.
      by apply/Rlt_le/Rmod1_ostro_mhalf2.
    rewrite (big_ostro r n) // -b_eq2 !big_ord_recr /= big_ord0.
    rewrite ostro_1 orn2_eq0 o_eq1 !Zplus_0_l Zmult_1_l.
    rewrite denom_2 //; last by apply: irrational_elt_neq_0.
    rewrite elt2_mhalf // Rmult_1_l.
    rewrite -Rmod1_halton_1 //; last by rewrite elt2_mhalf.
    by rewrite denom_1 Rmult_1_l; lra.
  apply: Rle_trans (_ : `|r| <= _); last first.
    apply/Rlt_le/Rmod1_ostro_mhalf1 => //.
    have /eqP := orn3_neq0.
    by have := ostro_bound r n 3 rI r_pos; lia.
  apply: Rle_trans (_ : 't[r]_2 <= _); first by apply: halton_le.
  rewrite -Rmod1_halton_1 //.
    by rewrite denom_1 // Rmult_1_l; lra.
  by rewrite elt2_mhalf.
have [rLh|hLr] := Rle_lt_dec (/ 2) `{r}.
  suff rLh' : / 2 < `{r}.
    by case/eqP: orn2_neq0; apply: ostro2_mhalf.
  suff : `{r} <> / 2 by lra.
  move=> rE; have : ~ irrational (/ 2).
    by move=> /irrational_inv H1; case: (irrational_IZR 2).
  by rewrite -rE; have /irrational_frac := rI.
have : (0 < 'bo[r, n])%nat by rewrite -ltnS; apply: ostro_bostro_le.
rewrite leq_eqVlt => /orP[/eqP b_eq1|b_gt1]; last first.
  apply: Rle_trans (_ : 't[r]_2 <= _); first by apply: halton_le.
  by apply/Rlt_le/Rmod1_ostro_Rabs_half1.
(* Don't know a more direct proof of this. I actually an instance of 
   another proof of the theorem I want to proof. There should be a more
   direct proof when bo[r,n] = 1 and `{r} < /2                       *)
rewrite -b_eq1 -Rmod1_halton; last first.
  have := ostro2_lt r n rI r_pos; have := ostro_bound r n 2 rI r_pos.
  have /eqP := orn2_neq0; lia.
suff : `|Z.of_nat n * r| >= `| 'q[r]_1 * r| by lra.
apply: Rmod1_denom_lt.
split; first by apply/(inj_lt 0)/ltP.
have := bostro_bound r n rI; rewrite -b_eq1; lia.
Qed.
