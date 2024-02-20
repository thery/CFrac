Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun. 
From mathcomp Require Import fintype bigop seq.
Require Import Zpower.
Require Import moreR moreZ rfrac.

Open Scope R_scope.

Local Notation " 'a[ r ]_ n" := (elt r n) (at level 10, format " ''a[' r ]_ n").
Local Notation " 'p[ r ]_ n" := (num r n) (at level 10, format " ''p[' r ]_ n").
Local Notation " 'q[ r ]_ n" := (denom r n) 
  (at level 10, format " ''q[' r ]_ n").


Definition bostro r (n : nat) : nat := 
 [arg min_(i < ord_max | (Z.of_nat n <? 'q[r]_(i: 'I_(n.+4)))%Z == true) i].-1.

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
  nth 0%Z (mko_list r (bostro r n) (Z.of_nat n)) (bostro r n - i.-1).
 
Local Notation " 'o[ r , n ]_ i" := (ostro r n i) 
  (at level 10, format " ''o[' r ,  n ]_ i").

Lemma big_ostro r n : 
  irrational r -> 
  (Z.of_nat n = \big[Zplus/0%Z]_(i < (bostro r n).+1) ('o[r, n]_i.+1 * 'q[r]_i))%Z.
Proof.
move=> rI; case: n => [|n].
  by rewrite bostro_0 big_ord_recl big_ord0 denom_0; lia.
rewrite /ostro big_ord_recl /= denom_0 Zmult_0_r Zplus_0_l.
by apply/big_mko_list/bostro_spos.
Qed.
