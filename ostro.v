Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun. 
From mathcomp Require Import fintype bigop seq.
Require Import Zpower moreR.
From rfac Require Import rfrac.

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
  
Definition ostro r n i := 
  nth 0%Z (mko_list r (bostro r n) (Z.of_nat n)) (bostro r n - i).

Local Notation " 'o[ r , n ]_ i" := (ostro r n i) 
  (at level 10, format " ''o[' r ,  n ]_ i").

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

