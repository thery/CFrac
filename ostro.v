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
 [arg min_(i < ord_max | (Z.of_nat n <? 'q[r]_(i: 'I_(n.+4)))%Z == true) i].

Fixpoint mko_list (r : R) (n : nat) (v : Z) : list Z :=
  if n is n1.+1 then
    (v / 'q[r]_n)%Z :: mko_list r n1 (v mod 'q[r]_n)%Z
  else nil.

Lemma mko_listS (r : R) (n : nat) (v : Z) :
  mko_list r n.+1 v = 
    (v / 'q[r]_n.+1)%Z :: mko_list r n (v mod 'q[r]_n.+1)%Z.
Proof. by []. Qed.

Lemma size_mko_list r n v : size (mko_list r n v) = n.
Proof. by elim: n v => //= n IH v; rewrite IH. Qed.

Lemma big_mko_list r n v : 
  let l := mko_list r n v in 
  (0 < n)%nat -> 
  v = \big[Zplus/0%Z]_(i < n.+1) (nth 0%Z l (n - i) * 'q[r]_i)%Z.
Proof.
elim: n v => // [] [|n] IH v l _.
  by rewrite !big_ord_recr big_ord0 denom_1 /= Z.div_1_r; lia.
rewrite /l mko_listS big_ord_recr /= subnn /=.
rewrite [LHS](Z.div_mod v ('q[r]_n.+2)); last first.
  by have := denom_spos n.+1 r; lia.
rewrite Zplus_comm; congr (_ + _)%Z; last by lia.
rewrite [LHS]IH //.
apply: eq_bigr => /= u _; congr (_ * _)%Z.
suff -> : (n.+2 - u = (n.+1 - u).+1)%nat by [].
by rewrite subSn // -ltnS.
Qed.

Lemma bostroP r n : 
  irrational r -> 
  ('q[r]_((bostro r n).-1) <= Z.of_nat n < 'q[r]_(bostro r n))%Z.
Proof.
move=> iR.  
rewrite /bostro; case: arg_minnP => /=; last first.
  move=> i /eqP Hi Hf; split; last by apply/Zlt_is_lt_bool.
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
  nth 0%Z (mko_list r (bostro r n) (Z.of_nat n)) (bostro r n - i).

Local Notation " 'o[ r , n ]_ i" := (ostro r n i) 
  (at level 10, format " ''o[' r ,  n ]_ i").

Lemma big_ostro r n : 
  irrational r -> 
  (Z.of_nat n = \big[Zplus/0%Z]_(i < (bostro r n).+1) ('o[r, n]_i * 'q[r]_i))%Z.
Proof.
move=> rI; apply: big_mko_list.
case: bostro (bostroP r n rI) => //.
by rewrite denom_0; lia.
Qed.
