Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun. 
From mathcomp Require Import fintype bigop seq.
Require Import Zpower.
Require Import moreR moreZ rfrac fib.

Open Scope R_scope.

Local Notation " 'a[ r ]_ n" := (elt r n) (at level 10, format " ''a[' r ]_ n").
Local Notation " 'p[ r ]_ n" := (num r n) (at level 10, format " ''p[' r ]_ n").
Local Notation " 'q[ r ]_ n" := (denom r n) 
  (at level 10, format " ''q[' r ]_ n").
Local Notation " 't[ r ]_ n " := (halton r n) 
  (at level 10, format  " ''t[' r ]_ n ").

Definition bostro r (n : nat) : nat := 
 [arg min_(i < ord_max | (Z.of_nat n <? 'q[r]_(i: 'I_(n.+4)))%Z == true) i].-1.
Local Notation " 'bo[ r , n ]" := (bostro r n) 
  (at level 10, format " ''bo[' r ,  n ]").


Fixpoint mko_list (r : R) (n : nat) (v : Z) : list Z :=
  if n is n1.+1 then
    (v / 'q[r]_n)%Z :: mko_list r n1 (v mod 'q[r]_n)%Z
  else nil.

Lemma mko_listS (r : R) (n : nat) (v : Z) :
  mko_list r n.+1 v = 
    (v / 'q[r]_n.+1)%Z :: mko_list r n (v mod 'q[r]_n.+1)%Z.
Proof. by []. Qed.

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
  by have := denom_spos n1 r; have := denom_le n1.+1 r; lia.
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

Lemma bostro_0 r : bostro r 0 = 0%nat.
Proof.
rewrite /bostro.
case: arg_minnP => /= [|i Hi].
  by case: Z.ltb_spec (denom_spos 2 r) => //=; lia.
have O4 : (1 < 4)%nat by [].
move=> /(_ (Ordinal O4)) /=; rewrite denom_1 => /(_ isT).
by case: (i) => // [] [|[]].
Qed.

Lemma bostro_spos r n : irrational r -> (0 < bostro r n.+1)%nat.
Proof.
move=> rI; rewrite /bostro; case: arg_minnP => /= [|i Hi Hj].
  have := irrational_denom_lbound n.+3 _ rI.
  by case: Z.ltb_spec => //; lia.
case: i Hi Hj => //= [] [|[|[|]]] //; rewrite denom_1.
by case: Z.ltb_spec => //; lia.
Qed.

Lemma bostroP r n : 
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
apply: Z.le_lt_trans (irrational_denom_lt _ _ iR).
by apply: denom_le.
Qed.

Definition ostro r n i := 
  if (i <=  (bostro r n).+1)%nat then 
    nth 0%Z (mko_list r (bostro r n) (Z.of_nat n)) (bostro r n - i.-1)
  else 0%Z.

Local Notation " 'o[ r , n ]_ i" := (ostro r n i) 
  (at level 10, format " ''o[' r ,  n ]_ i").

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
  by have := bostroP r n rI; lia.
by have := elt_ppos i.+1 r rP; lia.
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
by rewrite -E; have [] := bostroP _ n rI.
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

Definition ahalton r n := 'q[r]_ n * r - 'p[r]_ n.
Local Notation " 'ta[ r ]_ n " := (ahalton r n) 
  (at level 10, format  " ''ta[' r ]_ n ").

Lemma ahaltonE r n :  'ta[ r]_ n = (- 1) ^ n.+1 * 't[r]_n.
Proof.
by rewrite /ahalton /halton -Rmult_assoc -pow_add 
           plusE addnn -mul2n pow_1_even Rmult_1_l.
Qed.

Lemma ahalton_rec r n : 
  'a[r]_n.+2 <> 0%Z -> 'ta[r]_n.+2 = 'a[r]_n.+2 * 'ta[r]_n.+1 + 'ta[r]_n.
Proof. by move=> ar_neq0; rewrite !ahaltonE halton_rec //=; ring. Qed.

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
