From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype.
From mathcomp Require Import bigop seq div.
Require Import Reals.
Require Import slater moreR.
Import ssrnat.

Open Scope nat_scope.

Section Continuant.

Definition is_Rzero r :=
  match (Req_EM_T r 0) with left _ => true | right _ => false end.

Lemma is_Rzero0 : is_Rzero 0.
Proof. by rewrite /is_Rzero; case: Req_EM_T. Qed.

Fixpoint elt n (r : R) := 
  match n with O => `[r] | S n => 
  if is_Rzero `{r} then 0%Z else elt n (1/ `{r}) end.

Lemma eltS n r :
  elt (S n) r = if is_Rzero `{r} then 0%Z else elt n (1/ `{r}).
Proof. by []. Qed.

Lemma elt_0_INR n : elt 0 (INR n) = (Z_of_nat n).
Proof. by rewrite /= INR_IZR_INZ ZfloorZ. Qed.

Lemma elt_S_INR m n : elt (S n) (INR m) = 0%Z.
Proof. by rewrite /= INR_IZR_INZ fracZ is_Rzero0. Qed.

Definition finite r := exists N, forall n, N < n -> elt r n = 0%Z.

Fixpoint nfrac (l : seq nat) :=
  if l is a :: l1 then 
     let (n, d) := nfrac l1 in (a * n + d, n) else (1, 0).

Local Notation "`| l | " := (nfrac l).

Lemma nfracS a l : `|a :: l| =  
                 let (n, d) := nfrac l in (a * n + d, n).
Proof. by []. Qed.

Compute `|[:: 3%N]|.
Compute `|[:: 3; 7; 15]|.

Lemma nfrac_num_eq0 l : `|l|.1 = 0 -> 0 \in l.
Proof.
elim: l => //= a l; case: nfrac => /= n d; case: a => // a; case: n => // IH _.
by rewrite inE IH ?orbT.
Qed.

(* Removing all zeros except the first one for (a :: l) *)
Fixpoint arm_zeroes a (l : seq nat) :=
  if l is b :: l1 then
    if b == 0 then
      if l1 is c :: l2 then arm_zeroes (a + c) l2 else [::]
    else a :: (arm_zeroes b l1)  
  else [::a].

Lemma arm_zeroes_nfrac a l : `|a :: l| = `|arm_zeroes a l|. 
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) a => [[] //= |n IH [//= |b l] sLn a].
rewrite [arm_zeroes _ _]/=.
case: (_ =P 0)=> [->|_]; last by rewrite /= -IH.
case: l sLn=> [|c l sLn]; first by rewrite /= muln0.
have sLn1 : size l <= n by rewrite -ltnS (leq_trans _ sLn) /=.
rewrite -IH //=; case: `|_|=> x y //.
by rewrite mul0n add0n mulnDl addnA.
Qed.

Lemma arm_zeroes_eq0 a l : 0 \in arm_zeroes a l -> a = 0.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) a => [[] _ a|n IH [_ a|b l sLn a]] //=.
- by rewrite inE => /eqP.
- by rewrite inE => /eqP.
case: (_ =P 0)=> [_ |bNZ]; last first.
  by rewrite inE => /orP [/eqP | /(IH _ sLn)].
case: l sLn => // c l sLn.
have sLn1 : size l <= n by rewrite -ltnS (leq_trans _ sLn) /=.
by move/(IH _ sLn1); case: a.
Qed.

Lemma arm_zeroes_zero_notin a l : 0 \notin behead (arm_zeroes a l).
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) a => [[] _ a|n IH [_ a|b l sLn a]] //=.
case: (_ =P 0)=> [_ |bNZ /=]; last first.
  by apply/negP=> /arm_zeroes_eq0.
case: l sLn => // c l sLn.
by apply IH; rewrite -ltnS (leq_trans _ sLn) /=.
Qed.

(* Removing all zeros except the first one for l *)
Definition rm_zeroes l := if l is a :: l1 then arm_zeroes a l1 else l.

Lemma rm_zeroes_nfrac l : `|l| = `|rm_zeroes l|. 
Proof. by case: l => // a l; exact: arm_zeroes_nfrac. Qed.

Lemma rm_zeroes_zero_notin l : 0 \notin behead (rm_zeroes l).
Proof. by case: l => //= a l; exact: arm_zeroes_zero_notin. Qed.

Fixpoint ncontinuant (l : seq nat) :=
  if l is a :: l1 then
     if l1 is b :: l2 then a * (ncontinuant l1) + ncontinuant l2
     else a
  else 1.

Local Notation K := ncontinuant.

Lemma ncontinuantS a b l : K [:: a , b & l] = a * (K (b :: l)) + K l.
Proof. by []. Qed.

Lemma ncontinuantD a b l : K ((a + b)%nat :: l) = K (a :: l) + K l * b.
Proof. 
case: l =>  [/=| c l]; first by rewrite mul1n.
by rewrite ncontinuantS mulnDl addnAC [b * _]mulnC.
Qed.

Lemma ncontinuant_lbound l : 
  0 \notin l -> 2 ^ ((size l).-1)./2  <= ncontinuant l .
Proof.
elim: (_).+1 {-2}l (ltnSn (size l)) => //= {l}n IH [|a [|b l]] //.
- by case: a.
rewrite inE negb_or ltnS => sLn /andP[aNZ zNl].
rewrite ncontinuantS.
have F1 : 2 ^ ((size [:: a, b & l]).-1)./2 <=
       1 * 2 ^ ((size (b :: l)).-1)./2 + 2 ^ ((size l).-1)./2.
  rewrite /= uphalf_half expnD mul1n.
  case: size => //= k; rewrite uphalf_half.
  case: odd; first by rewrite mul1n leq_addr.
  by rewrite expn1 mul2n -addnn.
apply: leq_trans F1 _.
apply: leq_add; last first.
  apply: IH; first by apply: leq_trans sLn => /=.
  by move: zNl; rewrite inE negb_or => /andP[].
apply: leq_mul; first by case: (a) aNZ.
by apply: IH.
Qed.

Lemma ncontinuant_neq0 l : 0 \notin l -> K l != 0.
Proof.
move/ncontinuant_lbound.
by case: K => //; rewrite leqNgt expn_gt0.
Qed.

Lemma ncontinuant_rcons a b l :
  K (rcons (rcons l b) a)  = a * K (rcons l b) + K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l))=> /= [[] //= _ | n IH].
  by rewrite mulnC.
case=> [/= _|a1 [/= _|b1 l]]; first by rewrite mulnC.
  by rewrite !mulnDr [a * _]mulnC !mulnA !muln1 addnAC.
rewrite  [(_ <= _)%N]/= ltnS => sLn.
rewrite !rcons_cons !ncontinuantS.
rewrite (IH (b1 :: l)) ?IH ?rcons_cons //; last by apply: ltnW.
by rewrite !mulnDr mulnCA -!addnA; congr (_ + _); rewrite addnCA.
Qed.

Lemma ncontinuant_rev l : K (rev l) = K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l))=> /= [[] //|n IH].
case=> [//= _|a1 [//= _|b1 l]].
rewrite  [(_ <= _)%N]/= ltnS => sLn.
by rewrite !rev_cons ncontinuant_rcons -rev_cons !IH //= ltnW.
Qed.

Lemma ncontinuant_even_neq0 l : ~~ odd (size l) -> K l != 0.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l))=> /= [[] //|n IH].
case=> [//= _|a1 [//= _|b1 l]].
rewrite  [(_ <= _)%N]/= ltnS => sLn.
rewrite ncontinuantS [odd _]/= negbK => /(IH _ (ltnW sLn)).
by case: (K l) => // m; rewrite addnS.
Qed.

Lemma nfrac_continuant (l : seq nat) : l != [::] -> `|l| = (K l, K (behead l)).
Proof.
by elim: l => //= a [_ _ /= |b l ->];  first by rewrite muln1 addn0.
Qed.

End Continuant.

From mathcomp Require Import ssralg ssrint rat ssrnum.

Import GRing.Theory Num.Theory order.Order.POrderTheory order.Order.TotalTheory.

Section MoreContinuant.

Local Notation K := ncontinuant.
Local Notation "`| l | " := (nfrac l).

Section Rat.

(* Definition of the floor function *)
Definition floor (x : rat) := `|numq x| %/  `|denq x|.

Lemma floor_nat n : floor n%:R = n.
Proof. by rewrite /floor pmulrn numq_int denq_int !absz_nat divn1. Qed.

Lemma floor_between_pos q : (0 <= q -> (floor q)%:R <= q < (floor q)%:R + 1)%R.
Proof.
move=> qPos.
rewrite /floor -{3 4}[q]divq_num_den.
rewrite !(ler_pdivlMr , ltr_pdivrMr) ?(ltr_int _ 0, denq_gt0) //.
rewrite -{2 3}[numq q]gez0_abs ?numq_ge0 //.
rewrite -{2 4}[denq q]gez0_abs ?numq_ge0 //.
rewrite -(natrD _ _ 1) !pmulrn -!intrM ler_int  ltr_int.
rewrite -!PoszM lez_nat ltz_nat addn1.
by rewrite leq_divM ltn_ceil  // absz_gt0 denq_neq0.
Qed.

Lemma floor_posE p (q : rat) : 
  (0 <= q -> p%:R <= q < p%:R + 1 -> p = floor q)%R.
Proof.
move=> qPos /andP[L1 L2].
have /andP[L3 L4] := floor_between_pos _ qPos.
have := le_lt_trans L3 L2; have := le_lt_trans L1 L4.
rewrite -!(natrD _ _ 1) !ltr_nat !addn1 !ltnS => H1 H2.
by apply: anti_leq; rewrite H1.
Qed.

Definition round x := 
  let p := floor x in
  if (x  <= p%:R + 1/2%:R)%R then p else p.+1.

Lemma roundE (x : rat) p : (0 <= x)%R -> (`|x - (round x)%:R| <= `|x - p%:R|)%R.
Proof.
move=> /floor_between_pos/andP[H1 H2].
rewrite /round; case: (lerP x)=> Hx.
  rewrite ger0_norm; last by rewrite subr_ge0.
  case: (leqP p (floor x))=> Hp.
    rewrite ger0_norm; first by rewrite lerB // ler_nat.
    by rewrite subr_ge0 (le_trans _ H1) // ler_nat.
  rewrite ler0_norm; last first.
    rewrite subr_le0 ltW // (lt_le_trans H2) //.
    by rewrite -(natrD _ _ 1) ler_nat addn1.
  rewrite opprB.
  apply: (le_trans (_ : _ <= (floor x).+1%:R - x)%R); last first.
    by apply: lerB => //; rewrite ler_nat.
  apply: (le_trans (_ : _ <=  1/2%:R)%R).
    by rewrite lerBlDr addrC.
  rewrite lerBrDr -[(floor _).+1]addn1 natrD [X in (_ <= X)%R]addrC.
  have-> : (1%:R = (1/2%:R + 1/2%:R) :> rat)%R.
    rewrite -[(1/2%:R)%R]mulr1 -mulrDr -(natrD _ 1 1) divfK //.
  by rewrite -!addrA; apply: lerD => //; rewrite addrC.
rewrite ler0_norm; last by rewrite subr_le0 ltW // -addn1 natrD.
rewrite opprB.
case: (leqP p (floor x))=> Hp.
  rewrite ger0_norm; last first.
    by rewrite subr_ge0 (le_trans _ H1) // ler_nat.
  apply: (le_trans (_ : _ <= x - (floor x)%:R)%R); last first.
    by apply: lerB => //; rewrite ler_nat.
  apply: (le_trans (_ : _ <=  1/2%:R)%R); last first.
    by rewrite lerBrDr addrC ltW.
  rewrite lerBlDr -[(floor _).+1]add1n natrD.
  have-> : (1%:R = (1/2%:R + 1/2%:R) :> rat)%R.
    rewrite -[(1/2%:R)%R]mulr1 -mulrDr -(natrD _ 1 1) divfK //.
  by rewrite -!addrA; apply: lerD => //; rewrite addrC ltW.
rewrite ler0_norm; last first.
  rewrite subr_le0 ltW // (lt_le_trans H2) //.
  by rewrite -(natrD _ _ 1) ler_nat addn1.
by rewrite opprB lerB // ler_nat.
Qed.

Lemma round_id x : round x%:R = x.
Proof.
have /roundE : (0 <= (x%:R : rat))%R by apply: ler0n.
by move => /(_ x); rewrite subrr normr_le0 subr_eq0 eqr_nat => /eqP<-.
Qed.

Definition frac l : rat := let (n,d) := `|l| in (n%:Q / d%:Q)%R.

Variable l : list nat.
Hypothesis l_zero : 0 \notin behead l.
Hypothesis l_one : last 0 (behead l) != 1.

Local Notation alpha := (frac l).

Lemma alpha_pos : (0 <= alpha)%R.
Proof. by rewrite /frac; case: `|_| => a b; rewrite divr_ge0 ?ler0n. Qed.

(* Element of the fraction *)
Definition eltn n := nth 1 l n.
Local Notation a_ := eltn.

Lemma eltn_pos (n : nat) : n != 0 -> a_ n != 0.
Proof.
case: n => //= n _; rewrite /a_.
case: l l_zero => //= _ l1.
case: (leqP (size l1) n) => [sLn|/(mem_nth 1)]; first by rewrite nth_default.
by case: nth => // zIl /negP[].
Qed.

(* Numerator *)
Definition numn n := K (take n l).
Local Notation p_ := numn.

Lemma numn0 : p_ 0 = 1.
Proof. by rewrite /p_ take0. Qed.

Lemma numn1 : p_ 1 = a_ 0.
Proof. by rewrite /p_ /a_; case: l => //= a l1; rewrite take0. Qed.

Lemma numnE n : n.+1 < size l -> p_(n.+2) = a_(n.+1) * p_(n.+1) + p_ n.
Proof.
rewrite /p_ /a_ => nDs.
by rewrite !(take_nth 1) // 1?ltnW // ncontinuant_rcons.
Qed.

Lemma numn_oversize n : size l <= n -> p_ n = p_ (size l).
Proof. by move=>sLn; rewrite /p_ !take_oversize. Qed.

Lemma numn_nil n : l = [::] -> p_ n = 1.
Proof. by rewrite /p_ => ->. Qed.

(* Denominator. Following kirchin we set q_0 = 0 *)
Definition denomn n := 
  if n is _.+1 then  K (behead (take n l)) else 0.
Local Notation q_ := denomn.

Lemma denomn_eq0 n : (q_ n == 0) = (n == 0).
Proof.
case: n => [|n]; rewrite /q_ //.
have/ncontinuant_neq0/negPf->// : 0 \notin behead (take n.+1 l).
case: l l_zero=> //= a l1.
by apply/contra/mem_take.
Qed.

Corollary denomn_gt0 n : n != 0 -> (0 < (q_ n)%:Q)%R .
Proof. by rewrite -denomn_eq0; case: q_ => // k _;  exact: ltr0Sn. Qed.

Lemma denomn0 : q_ 0 = 0.
Proof. by []. Qed.

Lemma denomn1 : q_ 1 = 1.
Proof. by rewrite /q_; case: l => //= a l1; rewrite take0. Qed.

Lemma denomnE n : 
  n.+1 < size l -> q_(n.+2) = a_(n.+1) * q_(n.+1) + q_ n.
Proof.
rewrite /a_ /q_.
case: n => // [| n].
  by case: l => // a [|b l1] //=; rewrite take0 muln1 addn0.
case: l => // a l1 nDs; rewrite /a_ /q_.
have nDs1: n.+1 < size l1 by [].
rewrite ![behead _]/= !(take_nth 1) // ?ncontinuant_rcons //.
by apply: leq_trans nDs1.
Qed.

Lemma denomn_monotone m n : m <= n <= size l -> q_ m <= q_ n.
Proof.
elim: n m => [[]|n IH m] //.
rewrite (leq_eqVlt m) => /andP[/orP[/eqP->|mLn] nLs] //.
suff /(leq_trans _)->//: q_ n <= q_ n.+1 => //.
  by apply: IH; rewrite [_ <= n]mLn ltnW.
case: {IH}n mLn nLs => // n mLn nLs.
rewrite denomnE //.
apply: leq_trans (leq_pmull _ _) (leq_addr _ _).
suff : a_ n.+1 != 0 by case: a_.
by apply: eltn_pos.
Qed.

Lemma denomn_lt m n : 
  ((n != 2) || (a_ 1 != 1%N)) -> m < n -> n <= size l -> q_ m < q_ n.
Proof.
case: n => // [[|n SC H Hs]] //.
  by case: m => //; rewrite denomn0 denomn1.
suff /(leq_trans _)->// : q_ n.+1 < q_ n.+2 => //.
  by apply: denomn_monotone; rewrite [m <= _]H ltnW.
have Ha : a_ n.+1 != 0 by rewrite eltn_pos.
rewrite denomnE //.
case: n SC H Hs Ha => [|n] SC H Hs Ha.
  rewrite denomn0 denomn1 addn0 muln1.
  by case: a_ SC Ha => [|[]].
rewrite -[X in X < _]mul1n -addn1.
apply: leq_add.
  by apply: leq_mul => //; case: a_ Ha.
have: q_ n.+1 != 0 by rewrite denomn_eq0.
by case: q_.
Qed.

Lemma denomn_oversize n : 0 < size l <= n -> q_ n = q_ (size l).
Proof. 
move=>/andP[sP sLn]; rewrite /q_ !take_oversize //.
by case: l sP sLn => //=; case: n.
Qed.

Lemma denomn_nil n : l = [::] -> q_ n = (n != 0).
Proof. by case: n => [|n] //; rewrite /q_ => -> /=. Qed.

(* Relation between numerator and denominator *)
Lemma numMdenomnS k : k < size l ->
  if odd k  then p_ k.+1 * q_ k = (q_ k.+1 * p_ k).+1
  else q_ k.+1 * p_ k = (p_ k.+1 * q_ k).+1.
Proof.
elim: k => [_ |k IH sLn].
  by rewrite denomn1 denomn0 numn0 muln0.
rewrite numnE // denomnE // !mulnDl -!addnS.
rewrite ![p_ _ * q_ _.+1]mulnC![q_ _ * p_ _.+1]mulnC.
have/IH: k < size l by apply: leq_trans sLn. 
by rewrite mulnAC [odd _.+1]/=; case: odd => ->.
Qed.

Lemma coprime_num_denon k : coprime (p_ k) (q_ k).
Proof.
case: k => [|k]; first by rewrite numn0 denomn0.
wlog: k /k < size l=> [kLs|]; last first.
  move/numMdenomnS.
  (case: (p_ (k.+1)); case: (q_ (k.+1)); case: odd) => //[n|n|m n Emn|m n Emn].
  - by rewrite mulnC; case: n; case: p_.
  - by rewrite mulnC; case: n; case: q_.
  - apply/coprimeP=> //; exists (q_ k, p_ k).
    by rewrite mulnC Emn mulnC subSnn.
  rewrite coprime_sym; apply/coprimeP=> //; exists (p_ k, q_ k).
  by rewrite mulnC Emn mulnC subSnn.
case: (size l =P 0)=>[|sL]; first by rewrite /p_ /q_; case: l.
case: (leqP (size l) k)=> sLk; last by apply: kLs.
rewrite numn_oversize ?(leq_trans sLk) //.
rewrite denomn_oversize; last first.
  by case: size sL sLk => //= s _ SL; rewrite ltnS ltnW.
by case: size (kLs (size l).-1) sL => //= n ->.
Qed.

Lemma numMdenomnSS k : k.+1 < size l ->
  if odd k  then p_ k.+2 * q_ k = q_ k.+2 * p_ k + a_ k.+1
  else q_ k.+2 * p_ k = p_ k.+2 * q_ k + a_ k.+1.
Proof.
move=> sLn.
rewrite numnE // denomnE // !mulnDl -!mulnA.
have/numMdenomnS: k < size l by apply: leq_trans sLn.
by case: odd => ->; 
   rewrite !mulnS -!addnA addnC -!addnA; congr (_ + _);
   rewrite mulnC addnC.
Qed.

(* The convergent *)
Definition convn n := frac (take n l).
Local Notation s_ := convn.

Lemma convn0 : s_ 0 = 0%R.
Proof. by rewrite /s_; case: (l). Qed.

Lemma convn1 : l != nil -> s_ 1 = (a_ 0)%:R%R.
Proof.
rewrite /s_ /a_; case: (l) =>  //= a l1 _.
by rewrite take0 /frac //= addn0 muln1 divr1.
Qed.

Lemma convn_pos n : (0 <= s_ n)%R.
Proof.
by rewrite /s_ /frac; case: nfrac => p q; rewrite divr_ge0 ?ler0z.
Qed.

Lemma convn_oversize n : size l <= n -> s_ n = alpha.
Proof.
by move=> sLn; congr frac; apply: take_oversize.
Qed.

(* We take advance of the fact that 1 / 0 = 0 *)
Lemma convnE n :  l != [::] -> s_ n = ((p_ n)%:Q / (q_ n)%:Q)%R.
Proof.
move=> lNe; case: n => [|n].
  by apply/eqP; rewrite /s_ take0 numn0.
by rewrite /s_ /frac nfrac_continuant //; case: l lNe.
Qed.

Local Notation neq_lt := order.Order.TotalTheory.neq_lt.

(* The usual form of numMdenomnS *) 
Lemma convnS k : 0 < k < size l ->
  (s_ k.+1 =  if odd k  then s_ k + 1 / ((q_ k.+1)%:Q * (q_ k)%:Q)
              else s_ k - 1 / ((q_ k.+1)%:Q * (q_ k)%:Q))%R.
Proof.
move=> /andP[zLk kLs].
have lNe : l != [::] by case: l kLs.
rewrite !convnE // 1?ltnW //.
set x := p_ _; set y := p_ _; set z := q_ _; set t := q_ _.
have qkNZ : ((t%:Q)%Q != (0%:Q))%R.
  by rewrite eq_sym neq_lt denomn_gt0 //; case: (k) zLk.
have qk1NZ : ((z%:Q)%Q != (0%:Q))%R.
  by rewrite eq_sym neq_lt denomn_gt0.
rewrite -[(x%:Q)%R](mulfK qkNZ) -[(y%:Q)%R](mulfK qk1NZ) -![(_ / _ / _)%R]mulrA.
rewrite -!invfM [(t%:~R * _)%R]mulrC -!mulrDl -!intrM -!PoszM.
case: odd (numMdenomnS _ kLs) => [->|]; last rewrite mulnC => ->.
  by rewrite -addn1 PoszD intrD mulnC.
by rewrite -addn1 PoszD intrD mulnC mulrDl addrK.
Qed.

(* The usual form of numMdenomnSS *) 
Lemma convnSS k : 0 < k -> k.+1 < size l ->
 (s_ k.+2 = 
   if odd k  then s_ k + (a_ k.+1)%:Q / ((q_ k.+2)%:Q * (q_ k)%:Q)
   else s_ k - (a_ k.+1)%:Q / ((q_ k.+2)%:Q * (q_ k)%:Q))%R.
Proof.
move=> zLk kLs.
have lNe : l != [::] by case: l kLs.
rewrite !convnE // 1?ltnW ?(leq_trans _ kLs) //.
set x := p_ _; set y := p_ _; set z := q_ _; set t := q_ _.
have qkNZ : ((t%:Q)%Q != (0%:Q))%R.
  by rewrite eq_sym neq_lt denomn_gt0 //; case: (k) zLk.
have qk1NZ : ((z%:Q)%Q != (0%:Q))%R.
  by rewrite eq_sym neq_lt denomn_gt0.
rewrite -[(x%:Q)%R](mulfK qkNZ) -[(y%:Q)%R](mulfK qk1NZ) -![(_ / _ / _)%R]mulrA.
rewrite -!invfM [(t%:~R * _)%R]mulrC -!mulrDl -!intrM -!PoszM.
case: odd (numMdenomnSS _ kLs) => [->|]; last rewrite mulnC => ->.
  by rewrite  PoszD intrD mulnC.
by rewrite PoszD intrD mulnC mulrDl addrK.
Qed.

Lemma convn_odd_incr m n : m < n ->  n <= size l ->
  odd m -> odd n -> (s_ m < s_ n)%R.
Proof.
have F1: forall k, k.+1 < size l -> odd k -> (s_ k < s_ k.+2)%R.
  move=> k k1Ls Ok.
  have Pk : 0 < k by case: (k) Ok.
  rewrite convnSS // Ok -{1}[s_ k]addr0 // ltrD2l divr_gt0 //.
    by case: a_ (eltn_pos k.+1 is_true_true) => // u _; apply: ltr0Sn.
  by rewrite mulr_gt0 ?denomn_gt0 //; last by case: (k) Pk.
move=> kLs.
have Eq := subnK (ltnW kLs).
move: kLs; rewrite -{}Eq; set k := (_ - _).
rewrite -{1}[m]add0n ltn_add2r.
elim: k.+1 {-2}k (ltnSn k) => {k} // N IH [|[|[|k]]] //.
- by rewrite addSn /= => _ _  _ ->.
- by rewrite [odd (_ + _)]/= negbK; move=> *; apply: F1.
move=> kLN _ kmLs Om; rewrite [odd _]/= !negbK => Okm.
have /lt_trans->//: (s_ m < s_ (k.+1 + m))%R.
  apply: IH => //; first by apply: leq_trans (kLN : k.+2 < N).
  by apply: leq_trans kmLs; rewrite leq_add2r ltnS ltnW.
by apply: F1 => //.
Qed.

Lemma convn_even_decr m n : 0 < m < n ->  n <= size l ->
  ~~ odd m -> ~~ odd n -> (s_ n < s_ m)%R.
Proof.
have F1: forall k, 0 < k -> k.+1 < size l -> ~~ odd k -> (s_ k.+2 < s_ k)%R.
 move=> k Pk k1Ls Ek.
 rewrite convnSS // (negPf Ek) ltrBlDr -{1}[s_ k]addr0 // ltrD2l.
 rewrite divr_gt0 //.
   by case: a_ (eltn_pos k.+1 is_true_true) => // u _; apply: ltr0Sn.
  by rewrite mulr_gt0 ?denomn_gt0 //; last by case: (k) Pk.
move=> /andP[zLk kLs].
have Eq := subnK (ltnW kLs).
move: kLs; rewrite -{}Eq; set k := (_ - _).
rewrite -{1}[m]add0n ltn_add2r.
elim: k.+1 {-2}k (ltnSn k) => {k} // N IH [|[|[|k]]] //.
- by rewrite addSn /= => _ _  _ ->.
- by rewrite [odd (_ + _)]/= negbK; move=> *; apply: F1.
move=> kLN _ kmLs Om; rewrite [odd _]/= !negbK => Okm.
have /(lt_trans _) ->//: (s_ (k.+1 + m) < s_ m)%R.
  apply: IH => //; first by apply: leq_trans (kLN : k.+2 < N).
    by apply: leq_trans kmLs; rewrite leq_add2r ltnS ltnW.
  by rewrite negbK.
by apply: F1 => //; rewrite negbK.
Qed.

Lemma convn_odd_even m n : m <= size l -> 0 < n <= size l ->
  odd m -> ~~ odd n -> (s_ m < s_ n)%R.
Proof.
case: m => // m; case: n => // n; rewrite !andTb => mLs nLs.
case: (ltngtP m n)=> [mLn|nLm|-> Om /negP[]] // Om On.
  have Opn: odd n by rewrite negbK in On.
  have snLsn1: (s_ n < s_ n.+1)%R.
    rewrite convnS ?Opn //; last by case: (n) Opn nLs.
    rewrite -{1}[s_ n]addr0 ltrD2l divr_gt0 //.
    by rewrite mulr_gt0 ?denomn_gt0 //; last by case: (n) mLn.
  case: (boolP (m.+1 == n))=> [/eqP-> //| Dmn].
  apply/(lt_trans _ snLsn1)/convn_odd_incr => //; last by rewrite ltnW.
  by rewrite ltn_neqAle Dmn.
have Opn: odd n by rewrite negbK in On.
have smLsm1: (s_ m.+1 < s_ m)%R.
  rewrite convnS ?(negPf Om : odd m = _) //; last by case: (m) nLm mLs.
  rewrite  ltrBlDr -{1}[s_ m]addr0 ltrD2l divr_gt0 //.
  by rewrite mulr_gt0 ?denomn_gt0 //; case: (m) nLm.
case: (boolP (n.+1 == m))=> [/eqP-> //| Dmn].
apply/(lt_trans smLsm1)/convn_even_decr => //; last by rewrite ltnW.
by rewrite andTb ltn_neqAle Dmn.
Qed.

Lemma convn_odd_alpha n : n < size l -> odd n -> (s_ n < alpha)%R.
Proof.
move=> nLs On; rewrite -(convn_oversize _ (leqnn _)).
case: (boolP (odd (size l))) => Os; first by apply: convn_odd_incr.
apply: convn_odd_even => //; first by apply: ltnW.
by case: size nLs => // m; rewrite leqnn.
Qed.

Lemma convn_even_alpha n : 
  0 < n < size l -> if odd n  then (s_ n < alpha)%R else (alpha < s_ n)%R.
Proof.
move=> /andP[nPos nLs]; rewrite -(convn_oversize _ (leqnn _)).
case: (boolP (odd (size l))) => Os; case: (boolP (odd n)) => On.
- by  apply: convn_odd_incr.
- by apply: convn_odd_even; rewrite // nPos ltnW.
- by apply: convn_odd_even; rewrite ?(ltnW nLs) // (leq_trans nPos) //= ltnW.
by apply: convn_even_decr => //; rewrite nPos.
Qed.

Lemma convn_even_alphaW n :  0 < n ->
  if odd n  then (s_ n <= alpha)%R else (alpha <= s_ n)%R.
Proof.
have [sLn _ | nLn nP ] := leqP (size l) n; first by rewrite convn_oversize // if_same.
by have:= convn_even_alpha n; rewrite nP; case: odd => sLa; rewrite ltW // sLa.
Qed.

Lemma convn_betweenl (r : rat) : 
  (s_ 1 <= r < alpha -> exists2 n, odd n & s_ n <= r < s_ n.+2)%R.
Proof.
case/andP=> s1Lr rLa.
have P0 : exists n,  (s_ n <= r)%R by exists 1.
have P1 n : (s_ n <= r)%R -> n <= size l.
  rewrite leNgt leqNgt; apply: contra => rLs.
  apply: lt_le_trans rLa _.
  by rewrite convn_oversize // ltnW.
exists (ex_maxn P0 P1); case: ex_maxnP => i sLr Pj; last first.
  by rewrite sLr; case: lerP => // /Pj; rewrite ltnNge leqnSn.
have sLa : (s_ i < alpha)%R by apply: le_lt_trans rLa.
case: (leqP (size l) i)=> [/convn_oversize Hi|iLs].
  by rewrite Hi ltxx in sLa.
have /convn_even_alpha : 0 < i < size l by have -> := Pj _ s1Lr.
by case: odd => //; rewrite ltNge ltW.
Qed.

Lemma convn_betweenr (r : rat) : 
  (alpha < r <= s_ 2 -> 
   exists2 n : nat, ((n != 0%N) && (~~ odd n)) & s_ n.+2 < r <= s_ n)%R.
Proof.
case/andP=> aLr rLs2.
have P0 : exists n,  (r <= s_ n)%R by exists 2.
have P1 n : (r <= s_ n)%R -> n <= size l.
  rewrite leNgt leqNgt; apply: contra => rLs.
  by rewrite convn_oversize // ltnW.
exists (ex_maxn P0 P1); case: ex_maxnP => i sLr Pj; last first.
  by rewrite sLr; case: lerP => // /Pj; rewrite ltnNge leqnSn.
have sLa : (alpha < s_ i)%R by apply: lt_le_trans aLr _.
case: (leqP (size l) i)=> [/convn_oversize Hi|iLs].
  by rewrite Hi ltxx in sLa.
have /convn_even_alpha : 0 < i < size l.
  by have /(ltn_trans (_ : (0 < 1))) -> := Pj _ rLs2.
case: odd; first  by rewrite ltNge ltW.
by case: (i) => //; rewrite convn0 ltNge alpha_pos.
Qed.

(* Upper Bound                                                                *)

Lemma convn_alpha_up n: 0 < n < size l -> 
   (`|alpha - s_ n| <= 1 / ((q_ n.+1)%:Q * (q_ n)%:Q))%R.
Proof.
move=> PnLs.
have /andP[nPos nLs] := PnLs.
have OPos : (0 < 1 / ((q_ n.+1)%:Q * (q_ n)%:Q))%R.
  by rewrite divr_gt0 // ?mulr_gt0 ?denomn_gt0 //; case: (n) nPos.
have /le_trans->//: (`|alpha - s_ n| <= `|s_ n.+1 - s_ n|)%R.
  case: (boolP (odd n))=> [On|En].
    rewrite !ger0_norm.
    - apply: lerB (lexx _).
      move: nLs; rewrite leq_eqVlt => /orP[/eqP->|nLs].
        by rewrite -(convn_oversize _ (leqnn _)) lexx.
      have/convn_even_alpha: 0 < n.+1 < size l by [].
      by rewrite [odd _]/= On /= => /ltW.
    - rewrite subr_ge0; apply/ltW/convn_odd_even=> //; first by apply: ltnW.
      by rewrite negbK.
    by rewrite subr_ge0; apply/ltW/convn_odd_alpha.
  rewrite distrC [X in (X <= _)%R]ger0_norm 1?distrC ?ger0_norm.
  - apply: lerB (lexx _) _.
      case: (boolP (n.+1 == size l))=> [/eqP->|Dmn].
        by rewrite -(convn_oversize _ (leqnn _)) lexx.
      apply/ltW/convn_odd_alpha => //.
      by rewrite ltn_neqAle Dmn.
  - rewrite subr_ge0; apply/ltW/convn_odd_even=> //.
    by rewrite nPos ltnW.
  by move/convn_even_alpha: PnLs; rewrite (negPf En) /= subr_ge0 => /ltW.
rewrite convnS ?nPos //; case: odd.
  rewrite [(s_ n + _)%R]addrC addrK ler_norml lexx andbT.
  by apply: le_trans (_ : (_ <= 0)%R) _; [rewrite oppr_le0|idtac]; apply: ltW.
rewrite [(s_ n + _)%R]addrC addrK ler_norml lexx.
by apply: le_trans (_ : (_ <= 0)%R) _; [rewrite oppr_le0|idtac]; apply: ltW.
Qed.

(* The remainder *)
Definition remn n := frac (drop n l).
Local Notation r_ := remn.

Lemma remn0 : r_ 0 = alpha.
Proof. by rewrite /s_ /r_ drop0. Qed.

Lemma remn_oversize n : size l <= n -> r_ n = 0%R.
Proof. by move=> sLn; rewrite /r_ drop_oversize. Qed.

Lemma remnS k : k < size l -> (r_ k = (a_ k)%:Q + 1 / r_ k.+1)%R.
Proof.
move=> kLs.
rewrite /r_ /frac.
rewrite (drop_nth 1) ?(leq_trans _ kLs) //=.
have : `|drop k.+1 l|.1 != 0.
  case: l l_zero kLs => //= a l1 /negP zI kLs.
  by apply/eqP => /nfrac_num_eq0/mem_drop.
case: `|_|; rewrite -[nth _ _ _]/(a_ _) => n d /= nNZ.
rewrite /= PoszD intrD [((_ + _) / _)%R]mulrDl; congr (_ + _)%R; last first.
  by rewrite invfM invrK mul1r mulrC.
have qnNZ : ((n%:Q)%Q != (0%:Q))%R.  by apply: contra nNZ => /eqP /intr_inj /eqP.
by rewrite PoszM intrM mulfK.
Qed.

Lemma remnPos k : 0 < k < size l -> (0 < r_ k)%R.
Proof.
move=> /andP[kPos kLs].
rewrite remnS // -[0%R]add0r ltr_leD //; last first.
  apply: divr_ge0 => //.
  rewrite /r_ /frac; case: nfrac => a b.
  by apply: divr_ge0 => //; apply: ler0n.
have/(eltn_pos k) : k != 0 by case: (k) kPos.
by case a_ => // u _; apply: ltr0Sn.
Qed.

Lemma remnSS k : k.+1 < size l ->
  alpha = (((p_ k.+1)%:Q * r_ k.+1 + (p_ k)%:Q) / 
            ((q_ k.+1)%:Q * r_ k.+1 + (q_ k)%:Q))%R.
Proof.
elim: k => [oLs|k IH k2Ls].
  rewrite numn0 numn1 denomn0 denomn1 addr0 mul1r.
  rewrite -remn0 remnS ?(ltn_trans _ oLs) //.
  rewrite -[((a_ 0)%:~R)%R]divr1 addf_div ?mul1r ?divr1 //.
  apply/eqP=> rEz.
  have: (0 < r_ 1)%R by apply: remnPos.
  by rewrite rEz.
have k1Ls : k.+1 < size l by apply: ltn_trans k2Ls.
case: (boolP (k.+1 == size l)) => [/eqP->|kLs].
  rewrite remn_oversize // !mulr0 !add0r.
  rewrite -(convn_oversize _ (leqnn _)) -convnE //.
  by case: l k2Ls.
rewrite IH ?(ltn_trans _ sP) // remnS //.
have rNZ : r_ k.+2 != 0%R.
  apply/eqP=> rEz.
  have: (0 < r_ k.+2)%R by apply: remnPos.
  by rewrite rEz.
rewrite -[((a_ _)%:~R)%R]divr1 addf_div ?mul1r ?divr1 //.
rewrite ![(_ * (_ / _))%R]mulrA.
rewrite -[((p_ k)%:~R)%R]divr1 addf_div ?mul1r ?divr1 //.
rewrite -[((q_ k)%:~R)%R]divr1 addf_div ?mul1r ?divr1 //.
rewrite -mulf_div ?divff ?invr_neq0 //.
rewrite !mulrDr !mulr1 !mulrA -!intrM -!PoszM ![_ * a_ _]mulnC.
rewrite addrAC -mulrDl -intrD -PoszD -numnE //.
by rewrite addrAC -mulrDl -intrD -PoszD -denomnE.
Qed.

Lemma denomn_quotient k : k.+1 < size l ->
  ((q_ k.+1)%:Q / (q_ k)%:Q = frac (rev (take k (behead l))))%R.
Proof.
elim: k => [|[|k] IH k2Ls].
- by rewrite take0 /rev /frac /= invr0 !mulr0.
rewrite /q_; case: l k2Ls => // a [|b [|c l1]] _ //=.
  by rewrite /rev /frac /= invr1 !mulr1 muln1 addn0.
have k1Ls : k.+2 < size l by apply: ltn_trans k2Ls.
have kLs : k.+1 < size (behead l) by case: (l) k1Ls.
rewrite denomnE // PoszD PoszM intrD intrM mulrDl.
move: (IH k1Ls); rewrite (take_nth 1 kLs) rev_rcons nth_behead /frac.
rewrite nfracS; case: `|_| => n d ndE.
have PosqM : (0 < (q_ k.+2)%:Q / (q_ k.+1)%:Q)%R.
  by apply: divr_gt0; apply/denomn_gt0.
rewrite PoszD PoszM intrD intrM !mulrDl !mulfK; last 2 first.
- by apply/eqP=> Zn; rewrite ndE Zn mul0r in PosqM.
- by apply/eqP=> Zn; rewrite Zn mul0r in PosqM.
rewrite -[((q_ k.+1)%:~R)%R]invrK -invfM mulrC ndE.
by rewrite invfM invrK mulrC.
Qed.

(* The mediant is dependent of the actual fraction representation             *)

Definition mediant (n1 n2 d1 d2 : int) : rat :=
  ((n1 + n2)%:Q / (d1 + d2)%:Q)%R.

Lemma mediantC n1 n2 d1 d2 : mediant n1 n2 d1 d2 = mediant n2 n1 d2 d1.
Proof. by congr (_ / _)%R; rewrite addrC. Qed.


Lemma mediant_lt (n1 n2 d1 d2 : nat) :
  let r1 : rat := (n1%:~R / d1%:~R)%R in
  let r2 : rat := (n2%:~R / d2%:~R)%R in
  d1 != 0 -> d2 != 0 -> (r1 < r2)%R -> (r1 < mediant n1 n2 d1 d2 < r2)%R.
Proof.
move=> r1 r2 Pd1 Pd2 r1Lr2.
have Pd1d2 : ((0 : rat) < ((d1 : int) + d2 : int)%:~R)%R.
  rewrite -!lt0n -!ltz_nat in Pd1 Pd2.
  by rewrite intrD addr_gt0 // (ltr_int (Num.NumDomain.clone _ rat) 0).
rewrite ltr_pdivlMr // ltr_pdivrMr // !intrD !mulrDr.
have -> : (n1%:~R = r1 * d1%:~R)%R.
  by rewrite mulfVK // gt_eqF // (ltr_int _ 0); case: (d1) Pd1.
have -> : (n2%:~R = r2 * d2%:~R)%R.
  by rewrite mulfVK // gt_eqF // (ltr_int _ 0); case: (d2) Pd2.
have Pr1: (0 <= r1)%R by rewrite divr_ge0 // (ler_int _ 0).
have Pr2: (0 <= r2)%R by rewrite divr_ge0 // (ler_int _ 0).
rewrite !(ltrD2l, ltrD2r) //.
rewrite -subr_gt0 -mulrBl mulr_gt0 /=; last 2 first.
- by rewrite subr_gt0.
- by rewrite (ltr_int _ 0); case: (d2) Pd2.
rewrite -subr_gt0 -mulrBl mulr_gt0 //=.
  by rewrite subr_gt0.
by rewrite (ltr_int _ 0); case: (d1) Pd1.
Qed.

Lemma mediant_eq (n1 n2 d1 d2 : nat) :
  let r1 : rat := (n1%:~R / d1%:~R)%R in
  let r2 : rat := (n2%:~R / d2%:~R)%R in
  d1 != 0 -> d2 != 0 -> r1 = r2 -> mediant n1 n2 d1 d2 = r1.
Proof.
move=> r1 r2 Pd1 Pd2 r1E; apply/eqP.
rewrite -[r1]divr1 /mediant eqr_div //.
  rewrite mulr1 !intrD mulrDr divfK ?(eqr_int _ _ 0) //.
  by rewrite r1E divfK ?(eqr_int _ _ 0).
by rewrite (eqr_int _ _ 0); case: (d1) Pd1.
Qed.

Lemma mediant_le (n1 n2 d1 d2 : nat) :
  let r1 : rat := (n1%:~R / d1%:~R)%R in
  let r2 : rat := (n2%:~R / d2%:~R)%R in
  d1 != 0 -> d2 != 0 -> (r1 <= r2)%R -> (r1 <= mediant n1 n2 d1 d2 <= r2)%R.
Proof.
move=> r1 r2 Pd1 Pd2 r1Lr2.
case: (r1 =P r2) => [r1E|r1D]; first by rewrite mediant_eq ?lexx.
suff /andP[rL rR] : (r1 < mediant n1 n2 d1 d2 < r2)%R by rewrite !ltW.
apply: mediant_lt => //.
by rewrite lt_def r1Lr2 andbC /= eq_sym; apply/eqP.
Qed.

(* An intermediate fraction *)
Definition iconvn n a := 
  (((a * p_(n.+1) + p_ n)%N%:Q / ((a * q_(n.+1) + q_ n)%N)%:Q)%R).

Local Notation "'i[' a ']_' n " := (iconvn n a) (at level 10).
  
Lemma iconvn0 n : l != [::] -> i[0]_n = s_ n.
Proof. by move=> lD; rewrite /iconvn !add0n convnE. Qed.

Lemma iconvna n : n.+1 < size l -> i[a_(n.+1)]_n = s_ n.+2.
Proof.
rewrite /iconvn.
by move=> nLs; rewrite /iconvn -numnE // -denomnE // convnE //; case: l nLs.
Qed.

Lemma iconvnaS n : n.+1 < size l -> i[(a_(n.+1)).+1]_n = i[1]_n.+1.
Proof.
move=> nLs; rewrite /iconvn -add1n !mulnDl -!addnA.
by rewrite -numnE // -denomnE //; congr (_ / _)%R; rewrite !add0n addnC.
Qed.

Lemma iconv_oversize n a : 0 < size l <= n ->  i[a]_ n = alpha.
Proof.
move=> PsLn; have /andP[_ sLn] := PsLn.
rewrite /iconvn !numn_oversize //;  last by apply: leq_trans sLn _.
rewrite !denomn_oversize //; last first.
  by have/andP[-> /leq_trans->] := PsLn.
rewrite -!mulSnr !PoszM !intrM -mulf_div.
rewrite mulfV ?mul1r; last first.
  by rewrite (eqr_int _ _ 0) eqz_nat.
rewrite -convnE; last by case: l PsLn.
by apply: convn_oversize.
Qed.

Lemma iconvn_limr (a b u1 v1 u2 v2 : nat) (d : rat := (a%:R / b%:R)%R) : 
  b != 0 -> v1 != 0 -> v2 != 0 ->
  (u1%:R / v1%:R <= d < u2%:R / v2%:R -> 
   exists n,  d < (n * u2 + u1)%:R / (n * v2 + v1)%:R)%R.
Proof.
move=> Pb Pv1 Pv2 /andP[L1 L2].
have P1 : b * u1 <= a * v1.
  rewrite lter_pdivrMr in L1; last first.
    by rewrite (ltr_nat _ 0); case: (v1) Pv1.
  rewrite mulrC mulrA ler_pdivlMr in L1; last first.
    by rewrite (ltr_nat _ 0); case: (b) Pb.
  by rewrite -!natrM ler_nat [u1 * _]mulnC [v1 * _]mulnC in L1.
have P2 : a * v2 < b * u2.
  rewrite ltr_pdivrMr in L2; last by rewrite (ltr_nat _ 0); case: (b) Pb.
  rewrite mulrC mulrA ltr_pdivlMr in L2; last first.
    by rewrite (ltr_nat _ 0); case: (v2) Pv2.
  by rewrite -!natrM ltr_nat in L2.
exists (a * v1 - b * u1).+1.
rewrite lter_pdivrMr; last by rewrite (ltr_nat _ 0); case: (b) Pb.
rewrite mulrC mulrA ltr_pdivlMr; last first.
  by rewrite addnC (ltr_nat _ 0); case: (v1) Pv1.
set w := _.+1.
rewrite -!natrM ltr_nat.
apply: leq_trans (_ : a * (w * v2) + b * u1 + w <= _).
  by rewrite mulnDr -addnA ltn_add2l addnS ltnS [b * _ + _]addnC subnK.
rewrite mulnDr addnAC leq_add2r.
by rewrite mulnCA [b * _]mulnCA -mulnSr leq_mul2l P2 orbC.
Qed.

Lemma iconvn_liml (a b u1 v1 u2 v2 : nat) (d : rat := (a%:R / b%:R)%R) : 
  b != 0 -> v1 != 0 -> v2 != 0 ->
  (u1%:R / v1%:R < d <= u2%:R / v2%:R -> 
   exists n,  (n * u1 + u2)%:R / (n * v1 + v2)%:R < d)%R.
Proof.
move=> Pb Pv1 Pv2 /andP[L1 L2].
have P1 : b * u1 < a * v1.
  rewrite ltr_pdivrMr in L1; last by rewrite (ltr_nat _ 0); case: (v1) Pv1.
  rewrite mulrC mulrA ltr_pdivlMr in L1; last first.
    by rewrite (ltr_nat _ 0); case: (b) Pb.
  by rewrite -!natrM ltr_nat [u1 * _]mulnC [v1 * _]mulnC in L1.
have P2 : a * v2 <= b * u2.
  rewrite ler_pdivrMr in L2; last first.
    by rewrite (ltr_nat _ 0); case: (b) Pb.
  rewrite mulrC mulrA ler_pdivlMr in L2; last first.
    by rewrite (ltr_nat _ 0); case: (v2) Pv2.
  by rewrite -!natrM ler_nat in L2.
exists (b * u2 - a * v2).+1.
rewrite lter_pdivrMr; last first.
  by rewrite (ltr_nat _ 0) addnC; case: (v1) Pv1 => //= n; rewrite addnC.
rewrite mulrC mulrA ltr_pdivlMr; last by rewrite (ltr_nat _ 0); case: (b) Pb.
set w := _.+1.
rewrite -!natrM ltr_nat.
apply: leq_trans (_ : b * (w * u1) + a * v2 + w <= _).
  by rewrite mulnC mulnDr -addnA ltn_add2l addnS ltnS [a * _ + _]addnC subnK.
rewrite [_ * a]mulnC mulnDr addnAC leq_add2r.
by rewrite mulnCA [a * _]mulnCA -mulnSr leq_mul2l P1 orbC.
Qed.

Lemma iconvnDelta n a 
    (d := ((a.+1 * q_(n.+1) + q_ n) * (a * q_(n.+1) + q_ n))) : 
  (a != 0) || (n != 0) -> n < size l -> 
  (i[a.+1]_n - i[a]_n = ((-1)^+ n.+1 / d%:Q))%R.
Proof.
move=> anNZ nLs.
have d1NZ : ((a.+1 * q_ n.+1 + q_ n)%N%:~R)%R != 0%R :> rat.
  by move: (denomn_eq0 n.+1); rewrite (eqr_int _ _ 0); case: q_.
have d2NZ : ((a * q_ n.+1 + q_ n)%N%:~R)%R != 0%R :> rat.
  move: (denomn_eq0 n.+1) (denomn_eq0 n) anNZ.
  by rewrite (eqr_int _ _ 0); case: (a)=> [_|n1]; case: q_ => //; case: (n).
rewrite /iconvn -mulNr addf_div //.
congr (_ / _)%R; last by rewrite PoszM intrM.
rewrite mulSn -addnA PoszD intrD mulrDl.
rewrite mulSn -addnA  [q_ n.+1 + _]addnC.
set x := (_ * _)%R; set y := (_ * _)%R.
rewrite !PoszD !intrD mulrDr -!intrD -!PoszD.
rewrite !mulNr addrA addrK /x !PoszD !intrD mulrDr mulrDl.
rewrite PoszM intrM mulrCA mulrA -intrM -PoszM [X in (X - _ = _)%R]addrC.
set x1 := (_ * _)%R; set x2 := (_ * _)%R; set x3 := (_ * _)%R.
rewrite opprD addrA addrK /x1 /x3 -signr_odd [odd _]/=.
rewrite [((p_ n)%:~R * _)%R]mulrC -!intrM -!PoszM.
have /numMdenomnS:= nLs.
case: odd => ->; first by rewrite -add1n PoszD intrD addrK.
by rewrite -[(_ * _).+1]addn1 PoszD intrD opprD addrA subrr sub0r.
Qed.

Lemma iconvnqDelta n a b c (d := (c * (a * q_(n.+1) + q_ n))) :
 (b%:Q / c%:Q != i[a]_n -> 1 / d%:Q <= `|(b%:Q / c%:Q) - i[a]_n|)%R.
Proof.
case: (boolP (c ==0))=> [/eqP|Pc].
  by rewrite /d => -> _; rewrite invr0 mulr0 normr_ge0.
case: (boolP ((a == 0) && (n == 0))) => [/andP[]|anNZ].
  by rewrite /d => /eqP-> /eqP-> _; rewrite muln0 invr0 mulr0 normr_ge0.
rewrite negb_and in anNZ; rewrite -subr_eq0.
have d1NZ : ((a * q_ n.+1 + q_ n)%N%:~R)%R != 0%R :> rat.
  move: (denomn_eq0 n.+1) (denomn_eq0 n) anNZ.
  by rewrite (eqr_int _ _ 0); case: (a)=> [_|n1]; case: q_ => //; case: (n).
have d2NZ : (d%:Q != 0 :> rat)%R.
  by rewrite PoszM intrM mulf_eq0 negb_or d1NZ (eqr_int _ _ 0) andbT.
rewrite /iconvn -mulNr addf_div ?(eqr_int _ _ 0) //; last first.
  by apply: contra d1NZ => /eqP->.
rewrite normrM normfV -!intrM -!PoszM.
rewrite  [X in (_ <= _ / X)%R]ger0_norm -/d ?(ler_int _ 0) //.
rewrite mulf_eq0 negb_or -rmorphN -intrM -intrD.
rewrite intq_eq0 -absz_eq0 -!intr_norm -abszE.
case: absz => // k /andP[_ NZd].
apply: ler_pM => //; first by rewrite invr_ge0 // (ler_int _ 0).
by rewrite (ler_int _ 1).
Qed.

Lemma iconvn_monotone n a b :
  (a != 0) || (n != 0) -> n < size l -> a < b ->
  (if odd n then i[a]_n < i[b]_n else i[b]_n < i[a]_n)%R.
Proof.
move=> Han nLs aLb.
rewrite -(subnKC aLb); elim: (_ - _)=> [|d IH].
  rewrite addn0 -subr_gt0 -[X in if _ then _ else X]subr_lt0.
  rewrite -[(_ < 0)%R]subr_gt0 sub0r.
  rewrite (iconvnDelta _ _ Han nLs) -signr_odd [odd _.+1]/=.
  set u := (_%:~R)%R; suff uPos : (0 < u)%R.
    by case: odd; rewrite -?mulNr; apply: divr_gt0.
  rewrite ltr0z ltz_nat muln_gt0.
  move: (denomn_eq0 n.+1) (denomn_eq0 n) Han.
  by case: q_ =>  // n1 _; case: (a) => //; case: q_ => //; case: (n).
suff: if odd n then (i[a.+1 +d ]_ n < i[a.+1 + d.+1 ]_ n)%R
         else (i[a.+1 + d.+1 ]_ n < i[a.+1 + d]_ n)%R.
  by case: odd IH => H1 H2; [exact: lt_trans H2| exact: lt_trans H1].
rewrite -subr_gt0 -[X in if _ then _ else X]subr_lt0.
rewrite -[(_ < 0)%R]subr_gt0 sub0r addnS.
have Ha1n : (a.+1 + d != 0) || (n != 0) by [].
rewrite (iconvnDelta _ _ Ha1n nLs) -signr_odd [odd _.+1]/=.
set u := (_%:~R)%R; suff uPos : (0 < u)%R.
  by case: odd; rewrite -?mulNr; apply: divr_gt0.
rewrite ltr0z ltz_nat muln_gt0.
by move: Ha1n (denomn_eq0 n.+1); case: q_ => //; case: (a).
Qed.

Lemma iconvn_between n : n.+2 < size l -> 
  (if odd n then i[a_ n.+1]_n < alpha < i[(a_ n.+1).+1]_n 
            else i[(a_ n.+1).+1]_n < alpha < i[a_ n.+1]_n)%R.
Proof.
move=> nLs.
have n1Ls : n.+1 < size l by apply: leq_trans nLs.
rewrite iconvna // iconvnaS //.
have := convn_even_alpha _ (nLs : 0 < n.+2 < _).
case: (leqP (a_ n.+2) 1) => [|oLa].
  rewrite leq_eqVlt => /orP[/eqP aE1|]; last first.
    by case: a_ (eltn_pos n.+2 is_true_true).
  rewrite -aE1 iconvna //.
  move: nLs aE1 l_one; rewrite /a_ leq_eqVlt => /orP[|nLs _ _].
    rewrite (last_nth 1) size_behead => /eqP<-.
    by case: l => //= k1 k2 Hk /eqP[].
  have := convn_even_alpha _ (nLs : 0 < n.+3 < _).
  by rewrite ![odd _.+1]/=; case: odd => /= -> ->.
have := iconvn_monotone _ _ _ (is_true_true : (1 != 0) || (n.+1 != 0)) n1Ls oLa.
rewrite iconvna // ![odd _.+1]/=.
move: nLs; rewrite leq_eqVlt => /orP[/eqP->|nLs].
  by rewrite convn_oversize //; case: odd => /= -> ->.
have := convn_even_alpha _ (nLs : 0 < n.+3 < _).
rewrite [odd _.+1]/=; case: odd => /=.
  by move=> aLs /(lt_trans aLs) -> ->.
by move=> sLa /(lt_trans) /(_ sLa) -> ->.
Qed.

(*
Lemma iconvn_cmp n : n.+2 < size l -> 
  (if odd n then i[a_ n.+1]_n < alpha else alpha < i[a_ n.+1]_n)%R.
Proof.
by move/iconvn_between; case: odd=> /andP[].
Qed.

Lemma iconvn_cmp1 n : n.+2 = size l ->  i[a_ n.+1]_n = alpha.
Proof.
move=> sE.
have /convn_oversize<- : size l <= n.+2 by rewrite sE.
by rewrite iconvna sE.
Qed.
*)

Lemma iconvn_cmp n : n < size l -> n.+2 != size l ->
  (if odd n then i[a_ n.+1]_n < alpha else alpha < i[a_ n.+1]_n)%R.
Proof.
rewrite leq_eqVlt=> /orP[/eqP|]; last first.
  rewrite leq_eqVlt=> /orP[HE /negP //|/iconvn_between].
  by case: odd=> /andP[].
case: (boolP (n == 0)) => [/eqP -> /=| NZn sE _].
  rewrite /iconvn /= numn1 numn0 /a_ /=; case: (l) => // a [] //= _.
  rewrite /frac /= addn0 !muln1 addn0.
  by rewrite !divr1 mul1n ltr_int ltz_nat addnC.
have /convn_oversize<- : size l <= n.+1 by rewrite sE.
have lNN : l != [::] by case: l sE.
have sn1E : s_ n.+1 = ((a_ n.+1 * p_ n.+1)%N%:~R / (a_ n.+1 * q_ n.+1)%N%:~R)%R.
  rewrite !PoszM !intrM -mulf_div divff ?mul1r ?convnE //.
  by rewrite intq_eq0 -lt0n; have /eltn_pos : n.+1 != 0 by []; case: a_.
case: (boolP (odd n))=> [On|En].
  suff: (s_ n < i[a_ n.+1 ]_ n < s_ n.+1)%R by case/andP.
  have: (s_ n < s_ n.+1)%R by apply/convn_odd_even;rewrite -?sE ?negbK /=.
  rewrite sn1E convnE // /iconvn [_ + p_ n]addnC [_ + q_ n]addnC => LL.
  apply: mediant_lt => //; first by rewrite denomn_eq0; case: (n) On.
  by rewrite muln_eq0 negb_or eltn_pos // denomn_eq0.
suff: (s_ n.+1 < i[a_ n.+1 ]_ n < s_ n)%R by case/andP.
have: (s_ n.+1 < s_ n)%R.
  by apply/convn_odd_even;rewrite -?sE ?negbK //=; case: (n) NZn => /=.
rewrite sn1E convnE // /iconvn => LL.
apply: mediant_lt => //; last by rewrite denomn_eq0.
by rewrite muln_eq0 negb_or eltn_pos // denomn_eq0.
Qed.

Lemma iconvn_cmpW n : n < size l -> 
  (if odd n then i[a_ n.+1]_n <= alpha else alpha <= i[a_ n.+1]_n)%R.
Proof.
have [/eqP En2 nLs|Dn2 nLs] := (boolP (n.+2 == size l)); last first.
  by have := iconvn_cmp _ nLs Dn2; case: odd => V; rewrite ltW. 
have /convn_oversize<- : size l <= n.+2 by rewrite En2.
by rewrite iconvna En2 ?if_same.
Qed.

(* Unfortunately these theorems are false. As we are working with
   rational numbers, the number of stage leading to alpha is finite. So this 
   means that at the end we are going to get closer only on one side.
   In the irrational case, there is not this disymmetry so the theorems are true


Lemma iconvn_betweenl r: 
  (s_ 1 <= r < alpha -> 
      exists2 n, odd n & exists2 a, (a < a_ n.+1)%N & i[a]_ n <= r < i[a.+1]_ n)%R.

Lemma iconvn_betweenr r: 
  (alpha < r <= s_ 2 -> 
      exists2 n, ~~even n & exists2 a, (a < a_ n.+1)%N & i[a.+1]_ n < r <= i[a]_ n <= r)%R.

*)

(* Lower bound                                                                *)
Lemma convn_alpha_low n: 0 < n < size l -> 
   (1 / ((q_ n.+1 + q_ n) * (q_ n))%:R < `|alpha - s_ n|)%R.
Proof.
case: n => n // Pn.
have aLn := convn_even_alpha _ Pn.
rewrite -iconvn0; last by case: (l) Pn.
rewrite -iconvn0 in aLn; last by case: (l) Pn.
have Hn0 : (0 != 0) || (n.+1 != 0) by [].
have H1n : (1 != 0) || (n.+1 != 0) by [].
suff : (`|i[1]_ n.+1 - i[0 ]_ n.+1| < `|alpha - i[0 ]_ n.+1|)%R.
  have := iconvnDelta _ _ Hn0 Pn; rewrite mul1n => -> //.
  rewrite normrMsign mul1r  normrV  ?normr_nat //.
  rewrite unitfE (eqr_int _ _ 0) addnC.
  by case: q_ Pn (denomn_eq0 n.+1).
have := iconvn_monotone _ 0 _ Hn0 Pn (leqnn _).
have : a_ n.+2 != 1 ->
        if odd n.+1 then (i[1 ]_ n.+1 < i[a_ n.+2 ]_ n.+1)%R 
                else (i[a_ n.+2 ]_ n.+1 < i[1 ]_ n.+1)%R.
  have:  a_ n.+2 != 0 by rewrite eltn_pos.
  case: a_ => // [] [|a _ _] //.
  by have := iconvn_monotone _ _ _ H1n Pn (is_true_true : 1 < a.+2).
case: (boolP (odd n.+1)) aLn (iconvn_cmp _ Pn)  => [On|nOn] aLn iLa aLb i1Li.
rewrite /(i[_]_ _) in aLb.
  rewrite distrC [X in (X < _)%R]ltr0_norm ?subr_lt0 // opprB.
  rewrite distrC ltr0_norm ?subr_lt0 // opprB.
  rewrite ltr_leB //.
  case: (boolP (n.+3 == (size l))) => [/eqP HE| /iLa niLa].
    have /aLb naLb : a_ n.+2 != 1.
      have := l_one; rewrite /a_ (last_nth 1).
      have ->: size (behead l) = n.+2 by case: l HE => //= _ l1 [].
      by case: l HE => //.
    rewrite -(convn_oversize _ (_ : _ <= n.+3)); last by rewrite HE.
    by rewrite -iconvna ?HE.
  case: (boolP (a_ n.+2 == 1)) => [/eqP<- //| /aLb naLb].
  by rewrite (lt_trans _ niLa).
rewrite ltr0_norm ?subr_lt0 // opprB.
rewrite ltr0_norm ?subr_lt0 // opprB.
rewrite ler_ltB //.
case: (boolP (n.+3 == (size l))) => [/eqP HE| /iLa niLa].
  have /aLb naLb : a_ n.+2 != 1.
    have := l_one; rewrite /a_ (last_nth 1).
    have ->: size (behead l) = n.+2 by case: l HE => //= _ l1 [].
    by case: l HE => //.
  rewrite -(convn_oversize _ (_ : _ <= n.+3)); last by rewrite HE.
  by rewrite -iconvna ?HE.
case: (boolP (a_ n.+2 == 1)) => [/eqP<- //| /aLb naLb].
by rewrite (lt_trans niLa).
Qed.

Definition halton n : rat := 
  ((-1) ^+ n.+1 * ((q_ n)%:R * alpha - (p_ n)%:R))%R.

Local Notation t_ := halton.

Lemma halton0 : t_ 0 = 1%:Q%R.
Proof.
by rewrite /halton mul0r sub0r -signr_odd mulN1r opprK numn0.
Qed.

Lemma halton1 : t_ 1 = (alpha - (a_ 0)%:R)%R.
Proof. by rewrite /halton denomn1 !mul1r numn1. Qed.

Lemma haltonE n : n.+1 < size l -> 
  (t_ n.+2 = t_ n - (a_ n.+1)%:R * t_ n.+1)%R.
Proof.
move=> nLs.
rewrite /halton denomnE // numnE //.
rewrite -![((-1) ^+ _.+1)%R]signr_odd ![odd _.+1]/= !negbK signrN.
rewrite !(mulrBr, mulrBl, mulrDl, mulrDr, natrD, opprD, natrM).
rewrite -!addrA addrC -!addrA; congr (_ + _)%R.
rewrite addrC -!addrA; congr (_ + _)%R; congr (_ - _)%R.
  rewrite !mulNr; congr (- _)%R.
  by rewrite mulrC -!mulrA; congr (_ * _)%R; rewrite !mulrA mulrC mulrA.
by rewrite !mulNr !mulrA; congr (- _)%R; congr (_ * _)%R; rewrite mulrC.
Qed.

Lemma halton_nil n : l = [::] -> t_ n = ((-1) ^+ n)%R.
Proof.
move=> lN.
rewrite /t_ numn_nil // denomn_nil //.
rewrite lN /frac /= invr0 mulr0 sub0r // -exprSr.
by rewrite -signr_odd /= negbK signr_odd.
Qed.

Lemma halton_pos n : n < size l -> (0 < t_ n)%R.
Proof.
case: n => [|n nLs]; first by rewrite halton0.
have /convn_even_alpha : 0 < n.+1 < size l by [].
rewrite /halton -signr_odd ![odd _.+1]/= negbK; case: odd.
  rewrite mulN1r opprB subr_gt0 convnE; last by case: (l) nLs.
  by rewrite ltr_pdivlMr ?denomn_gt0 //= mulrC.
rewrite mul1r subr_gt0 convnE; last by case: (l) nLs.
by rewrite ltr_pdivrMr ?denomn_gt0 //= mulrC.
Qed.

Lemma halton_oversize n : 0 < size l <= n -> (t_ n  = 0)%R.
Proof.
move=> PsLn; have /andP[_ sLn] := PsLn. 
rewrite /halton -(convn_oversize _ sLn) convnE; last by case: l PsLn.
rewrite [((q_ n)%:R * _)%R]mulrC divfK ?subrr ?mulr0 //.
have /denomn_gt0  : n != 0 by case: (n) PsLn; case: l.
by rewrite lt0r; case/andP.
Qed.

Lemma halton_posW n :  l != [::] -> (0 <= t_ n)%R.
Proof.
have [sLn lDn| nLs lDn] := leqP (size l) n.
  by rewrite halton_oversize // sLn; case: l lDn.
by apply/ltW/halton_pos.
Qed.

Lemma halton_lt  n : n < size l -> (t_ n.+1 < t_ n)%R.
Proof.
rewrite leq_eqVlt => /orP[/eqP nE|].
  by rewrite halton_oversize -?nE  ?leqnn // halton_pos // -nE.
rewrite leq_eqVlt => /orP[/eqP nE|nLs].
   have /(halton_posW n.+2) : l != [::] by case: l nE.
  rewrite haltonE ?nE // subr_ge0 => atLt.
  apply:  lt_le_trans atLt .
  rewrite -{1}[t_ _]mul1r -subr_gt0 -mulrBl pmulr_rgt0.
    by rewrite halton_pos // nE.
  rewrite subr_gt0 (ltr_nat _ 1).
  have: a_ n.+1 != 0 by rewrite eltn_pos.
  suff: a_ n.+1 != 1 by case: a_ => // [[|]].
  apply: contra l_one => /eqP<-.
  rewrite -nth_last nth_behead size_behead -nE.
  by apply/eqP/set_nth_default; rewrite nE.
have := halton_pos _ nLs.
rewrite haltonE ?nE ?(ltn_trans _ nLs) // subr_gt0 => atLt.
apply:  le_lt_trans atLt .
rewrite -{1}[t_ _]mul1r -subr_ge0 -mulrBl pmulr_lge0; last first.
  by rewrite halton_pos // (ltn_trans _ nLs).
rewrite subr_ge0 (ler_nat _ 1).
have: a_ n.+1 != 0 by rewrite eltn_pos.
by case: a_.
Qed.

Lemma halton_floor  n : n.+1 < size l ->  a_ n.+1 = floor (t_ n / t_ n.+1).
Proof.
move=> nLs; apply: floor_posE.
  apply: divr_ge0; apply: ltW; apply: halton_pos => //.
  by apply: leq_ltn_trans nLs.
rewrite !(ler_pdivlMr, ltr_pdivrMr) ?halton_pos //.
rewrite addrC mulrDl mul1r -subr_ge0 -subr_gt0 -addrA.
rewrite -[(_ * _ -  t_ n)%R]opprB -haltonE //.
rewrite halton_posW; last by case: l nLs.
by rewrite subr_gt0 halton_lt.
Qed.

Lemma halton_sum n : 
  n < size l -> (t_ n * (q_ n.+1)%:R + t_ n.+1 * (q_ n)%:R = 1)%R.
Proof.
move /numMdenomnS.
rewrite /halton !(mulrBl, mulrBr, mulrDl, mulrDr).
rewrite -![((-1) ^+ _.+1)%R]signr_odd ![odd _.+1]/= negbK signrN !mulNr opprK.
rewrite addrCA -mulrA [(_ * (q_ n)%:R)%R]mulrC  [(_ * alpha)%R]mulrC !mulrA.
rewrite !addrA addrN add0r -!mulrA -!natrM.
case: odd => [->|]; last first.
  by rewrite !mul1r mulnC => ->; rewrite -add1n natrD addrK.
by rewrite addrC !mulNr opprK !mul1r mulnC -add1n natrD addrK.
Qed.

(* Best approximation *)

Definition best_approx (a b : nat) :=
  b != 0 /\ 
  forall c d : nat, 0 < d <= b -> (a%:R/b%:R != c%:R / d%:R :> rat)%R -> 
    (`|b %:R * alpha - a%:R| < `|d%:R * alpha - c%:R |)%R.

Lemma dist_fact a b (c : rat) (Pb : b != 0): 
  (`|b %:R * c - a%:R| = b %:R * `|c - (a%:R / b%:R)|)%R.
Proof.
rewrite -{2}normr_nat -normrM mulrBr.
by rewrite [(_ * (_ / _))%R]mulrC divfK // (eqr_nat _ _ 0).
Qed.

Fact best_ax1 (a b c d : nat) : 
  (a%:Q / b%:Q != c%:Q / d%:Q -> 
  1 / (b%:Q * d%:Q) <= `|a%:Q / b%:Q - c%:Q / d%:Q |)%R.
Proof.
case: b => [|b]; first by rewrite mul0r invr0 mulr0 normr_ge0.
case: d => [|d]; first by rewrite invr0 !mulr0 normr_ge0.
have [L G|L G] := lerP (a%:~R / b.+1%:~R) (c%:~R / d.+1%:~R)%R.
  have : (a%:~R / (b.+1%:~R : rat) < c%:~R / d.+1%:~R)%R.
    by move: L; rewrite le_eqVlt => /orP[] //; move/negP: G.
  rewrite ltr_pdivrMr ?(ltr_nat _ 0) // mulrC mulrA.
  rewrite ltr_pdivlMr ?(ltr_nat _ 0) // (mulrC _ (c%:~R)%R).
  rewrite -(intrM _ _ b.+1) -(intrM _ a) ltr_int ltz_nat => K.
  rewrite !ler_pdivrMr ?mulr_gt0 ?(ltr_nat _ 0) // mulrBl.
  rewrite {1}[(b.+1%:~R * _)%R]mulrC !mulrA !divfK ?(eqr_int _ _ 0) //.
  rewrite lerBrDr -(intrM _ _ b.+1) -(intrM _ a).
  by rewrite -(intrD _ 1) ler_int // -PoszM -PoszD lez_nat add1n.
have := L.
rewrite ltr_pdivrMr ?(ltr_nat _ 0) // mulrC mulrA.
rewrite ltr_pdivlMr ?(ltr_nat _ 0) //.
rewrite -(intrM _ c) -(intrM _ d.+1) ltr_int ltz_nat => K.
rewrite !ler_pdivrMr ?mulr_gt0 ?(ltr_nat _ 0) // mulrBl.
rewrite {2}[(b.+1%:~R * _)%R]mulrC !mulrA !divfK ?(eqr_int _ _ 0) //.
rewrite lerBrDr -(intrM _ _ b.+1) -(intrM _ a).
by rewrite -(intrD _ 1) ler_int // -PoszM -PoszD lez_nat add1n [a * _]mulnC.
Qed.


Fact best_ax2 (a b n : nat) : b != 0 -> 0 < n < size l ->
   s_ n != (a%:Q / b%:Q)%R ->
  (`|a%:Q / b%:Q - s_ n|  <  `|s_ n.+1 - s_ n|)%R -> q_ n.+1 < b.
Proof.
move=> bP nLs snDab.
have P1 : (0 < (q_ n)%:Q)%R by rewrite denomn_gt0 //; case: (n) nLs.
have P2 : (0 < (q_ n.+1)%:Q)%R by rewrite denomn_gt0.
have P3 : (0 < b%:Q)%R by rewrite (ltr_int _ 0); case: (b) bP.
have-> :  (`|s_ n.+1 - s_ n| = 1/ ((q_ n.+1)%:R * (q_ n)%:R))%R.
  rewrite convnS //; case: odd.
    rewrite [(s_ n + _)%R]addrC addrK ger0_norm // divr_ge0 ?mulr_ge0 ?ltrW //.
  rewrite [(s_ n - _)%R]addrC addrK normrE ger0_norm // divr_ge0 //.
  by rewrite mulr_ge0 // ltrW.
move: snDab; rewrite eq_sym.
rewrite convnE => [K L|]; last by case: (l) nLs => //; case: (n).
have := le_lt_trans (best_ax1 _ _ _ _ K) L.
rewrite ltr_pdivrMr ?mulr_gt0 //.
rewrite [(1 / _ * _)%R]mulrC mulrA mulr1.
rewrite ltr_pdivlMr ?mul1r ?mulr_gt0 //.
by rewrite -subr_gt0 -mulrBl pmulr_lgt0 // subr_gt0 ltr_nat.
Qed.

Fact best_ax3 (a b n : nat) : b != 0 -> 0 < n < size l ->
  s_ n.+1 != (a%:Q / b%:Q)%R ->
  (`|s_ n.+1 - a%:Q / b%:Q| <= `|alpha - a%:Q / b%:Q|)%R -> 
  (`|(q_ n)%:R * alpha - (p_ n)%:R|  <=  `|b%:R * alpha - a%:R|)%R.
Proof.
move=> bP nLs snDab sBabLaBab.
have P1 : (0 < (q_ n)%:Q)%R by rewrite denomn_gt0 //; case: (n) nLs.
have P2 : (0 < (q_ n.+1)%:Q)%R by rewrite denomn_gt0.
have P3 : (0 < b%:Q)%R by rewrite (ltr_int _ 0); case: (b) bP.
have P4 : l != [::] by case: (l) nLs; case: (n).
apply: (le_trans (_ : _ <= 1 / (q_ n.+1)%:R)%R).
  have := convn_alpha_up _ nLs.
  rewrite invfM mulrA ler_pdivlMr // mulrC.
  by rewrite dist_fact ?convnE // denomn_eq0; case: (n) nLs.
have := snDab; rewrite convnE // => /best_ax1; rewrite -convnE // => G.
have := le_trans G sBabLaBab.
by rewrite invfM mulrA ler_pdivrMr // [(_ * b%:R)%R]mulrC dist_fact.
Qed.

Fact rat_uniq x y z t : 
 y != 0 -> t != 0 -> coprime x y -> coprime t z -> 
 (x%:R / y%:R = z%:R / t%:R :> rat)%R -> x = z /\ y = t.
Proof.
move=> NZy NZt Cxy Ctz /eqP Eqr.
have Eqn : x * t == y * z.
  by rewrite -(@eqr_nat (Num.NumDomain.clone _ rat)) [y * _]mulnC 
          !natrM -eqr_div // (eqr_nat _ _ 0).
have G x1 y1 z1 t1 : 
     x1 * t1 = y1 * z1 -> coprime x1 y1 -> coprime t1 z1 -> x1 = z1.
  move=> ME Cx1y1 Ct1z1.
  apply/eqP; rewrite eqn_dvd.
  rewrite -(Gauss_dvdr _ Cx1y1) -ME dvdn_mulr //.
  rewrite coprime_sym in Ct1z1.
  by rewrite -(Gauss_dvdr _ Ct1z1) mulnC ME dvdn_mull.
split; first by apply: G Cxy Ctz; apply/eqP.
rewrite coprime_sym in Cxy; rewrite coprime_sym in Ctz.
by apply: G Cxy Ctz; apply/eqP; rewrite mulnC (eqP Eqn) mulnC.
Qed.

Lemma best_approx_ex a b : l != [::] ->
  best_approx a b -> exists n : nat, n != 0 /\ (s_ n = a%:R / b%:R)%R.
Proof.
move=> lNZ [bP baE].
set v : rat := (a%:R / b%:R)%R.
have vPos : (0 <= v)%R by rewrite divr_ge0 ?ler0n.
have [/eqP|s1Dv] := boolP ((s_ 1) ==  v); first by exists 1.
have oLb : 0 < 1 <= b by case: (b) bP.
have /(baE _ _ oLb) : v != ((p_ 1)%:R / 1%:R)%R.
  by rewrite -{2}denomn1 -convnE // eq_sym.
have s1E : s_ 1 = (p_ 1)%:R%R by rewrite convnE // denomn1 divr1.
rewrite mul1r -s1E => baBaLaBp.
have [vLa |aLv |->] := ltrgtP v alpha; last first.
- exists (size l); split; first by case: l lNZ.
  by apply: convn_oversize.
- have [vLs2 | s2Lv] := lerP v (s_ 2).
    have [|n /andP[On En] /andP[sn2Ls]] := convn_betweenr v; first by rewrite aLv.
    rewrite le_eqVlt => /orP[/eqP->|vLsn]; first by exists n.
    have [/eqP|sDsn] := boolP ((s_ n) ==  v); first by exists n.
    have [/eqP|sDsn1] := boolP ((s_ n.+1) ==  v); first by exists n.+1.
    have [/eqP|sDsn2] := boolP ((s_ n.+2) ==  v); first by exists n.+2.
    have nP : 0 < n.
      by case: (n) vLsn => //; rewrite convn0 ltNge vPos.
    have [nLs | sLn] := leqP (size l) n.
      by move: vLsn; rewrite convn_oversize ?ltNge ?ltW.
    have qLb :  q_ n.+1 < b.
      apply:  best_ax2 sDsn _ => //; first by rewrite nP.
      have F1 := convn_even_alphaW _ (is_true_true : 0 < n.+1).
      rewrite /= En in F1.
      have F2 := convn_even_alphaW _ nP.
      rewrite (negPf En) in F2.
      rewrite !ler0_norm ?opprB; last by rewrite subr_le0; apply: ltW.
        by rewrite ler_ltB //; apply: le_lt_trans _ aLv.
      by rewrite subr_le0; apply: le_trans F2.
    have G : (`|b%:R * alpha - a%:R| < `|(q_ n.+1)%:R * alpha - (p_ n.+1)%:R|)%R.
      apply: baE => //; last by rewrite -convnE // eq_sym.
      have := denomn_gt0 _ (is_true_true : n.+1 != 0).
      by rewrite (ltr_nat _ 0) => ->; rewrite ltnW.
    rewrite ltNge in G; case/negP: G.
    have := sLn; rewrite leq_eqVlt=> /orP[/eqP nE|n1Ls].
      have /convn_oversize<- : size l <= n.+1 by rewrite nE.
      rewrite convnE // mulrC divfK ?addrN //.
        by rewrite normr0 normr_ge0.
      by rewrite (eqr_nat _ _ 0) denomn_eq0.
    apply: best_ax3 => //.
    rewrite !ler0_norm //; try by rewrite subr_le0 ltW.
    rewrite !opprB lerB //.
    have := convn_even_alphaW _ (is_true_true : 0 < n.+2).
    by rewrite /= En.
  have : 1 <= size l by case: (l) lNZ.
  rewrite leq_eqVlt => /orP[/eqP sE|oLs].
    move: baBaLaBp; rewrite -(convn_oversize _ (leqnn _)) -sE.
    by rewrite subrr normr0 ltNge normr_ge0.
  move: baBaLaBp; rewrite ltNge; case/negP.
  have /convn_alpha_up/le_trans->// : 0 < 1 < size l by rewrite oLs.
  rewrite denomn1 mulr1 dist_fact //.
  rewrite [X in (_ <= X)%R]mulrC -ler_pdivrMr; last first.
    by rewrite (ltr_nat _ 0); case: (b) bP.
  rewrite -mulrA -invfM.
  apply: le_trans (_ : `|s_ 2 - v| <= _)%R.
    rewrite convnE // best_ax1 // -convnE //.
    by rewrite ltNge in s2Lv; apply: contra s2Lv => /eqP->.
  rewrite !ler0_norm ?opprB ?subr_le0; try by rewrite ltW.
  rewrite lerB //.
  by have := convn_even_alphaW _ (is_true_true : 0 < 2).
have [s1Lv | vLs1] := lerP (s_ 1) v; last first.
  move: baBaLaBp; rewrite ltNge; case/negP.
  apply: le_trans (_ : `|alpha - v| <= _)%R.
     have /= F := convn_even_alphaW _ (is_true_true : 0 < 1).
     by rewrite !ger0_norm  ?lerB ?subr_ge0 // ?ltW //.
  rewrite dist_fact // -/v.
  rewrite -[X in (X <= _)%R]mul1r ler_pM //.
  by rewrite (ler_nat _ 1); have /andP[] := oLb.
have [|n En /andP[]] := convn_betweenl v; first by rewrite s1Lv.
have NZ0 : n != 0 by case: (n) En.
rewrite le_eqVlt => /orP[/eqP<- * |snLv vLsn2]; first by exists n.
have [/eqP|sDsn] := boolP ((s_ n) ==  v); first by exists n.
have [/eqP|sDsn1] := boolP ((s_ n.+1) ==  v); first by exists n.+1.
have [/eqP|sDsn2] := boolP ((s_ n.+2) ==  v); first by exists n.+2.
have nP : 0 < n by case: (n) En.
have [nLs | sLn] := leqP (size l) n.
  by move: snLv; rewrite convn_oversize ?ltNge ?ltW.
have qLb :  q_ n.+1 < b.
  apply:  best_ax2 sDsn _ => //; first by rewrite nP.
  have F1 := convn_even_alphaW _ (is_true_true : 0 < n.+1).
  rewrite /= En /= in F1.
  have F2 := convn_even_alphaW _ nP.
  rewrite En in F2.
  rewrite !ger0_norm; last by rewrite subr_ge0; apply: ltW.
    by rewrite ltr_leB //; apply: lt_le_trans vLa _.
  by rewrite subr_ge0; apply: le_trans F1.
have G : (`|b%:R * alpha - a%:R| < `|(q_ n.+1)%:R * alpha - (p_ n.+1)%:R|)%R.
  apply: baE => //; last by rewrite -convnE // eq_sym.
  have := denomn_gt0 _ (is_true_true : n.+1 != 0).
  by rewrite (ltr_nat _ 0) => ->; rewrite ltnW.
rewrite ltNge in G; case/negP: G.
have := sLn; rewrite leq_eqVlt=> /orP[/eqP nE|n1Ls].
  have /convn_oversize<- : size l <= n.+1 by rewrite nE.
  rewrite convnE // mulrC divfK ?addrN //.
    by rewrite normr0 normr_ge0.
  by rewrite (eqr_nat _ _ 0) denomn_eq0.
apply: best_ax3 => //.
rewrite !ger0_norm //; try by rewrite subr_ge0 ltW.
rewrite lerB //.
have := convn_even_alphaW _ (is_true_true : 0 < n.+2).
by rewrite /= En.
Qed.

Let val k : rat := (`|k%:R * alpha - (round (k%:R * alpha))%:R|)%R.
 
Fixpoint find_best k :=
 if k is k1.+1 then
   if k1 is _.+1 then
       let v := find_best k1 in
       if (val v <= val k)%R then v else k 
   else k else 0.

Definition find_bestE k :
  find_best k.+2 = 
       let v := find_best k.+1 in
       if (val v <= val k.+2)%R then v else k.+2.
Proof. by []. Qed.
   
Lemma find_best_le k : k != 0 -> 0 < find_best k <= k.
Proof.
elim: k => // [[|n]] // H _.
rewrite find_bestE.
lazy zeta; case: (val _ <= val _)%R => //.
  by case/andP: (H is_true_true) => -> /leq_trans->.
by rewrite leqnn.
Qed.

Lemma val_id n k (aE : alpha = n%:R%R) : val k = 0%R.
Proof. by rewrite /val aE -natrM round_id subrr normr0. Qed.

Lemma find_best_id n k (aE : alpha = n%:R%R) : k != 0 -> find_best k = 1.
Proof.
elim: k => [|[|k]] // IH _.
rewrite find_bestE IH //.
by lazy zeta; rewrite !(val_id _ _ aE).
Qed.

Lemma find_best_val_le k i : 0 < i <= k ->  (val (find_best k) <= val i)%R.
Proof.
elim: k => [|[|k] IH] //; first by case: i.
  by case: (i) => // [[|]].
rewrite find_bestE; lazy zeta.
have [] := lerP _ (val k.+2) => H //.
  rewrite (leq_eqVlt i)=> /andP[Pi /orP[/eqP->|H1]] //.
  by apply: IH; rewrite Pi -ltnS.
rewrite (leq_eqVlt i)=> /andP[Pi /orP[/eqP->|H1]] //.
apply: le_trans (ltW H) (IH _).
by rewrite Pi -ltnS.
Qed.

Lemma find_best_val_le2 k i j : k != 0 ->
  0 < i <= k -> (val (find_best k) <= `|i%:R * alpha - j%:R|)%R.
Proof.
move=> NZk iR.
apply: le_trans _ (roundE _ _ _); first by apply: find_best_val_le.
rewrite pmulr_rge0 ?alpha_pos // ltr0n.
by case: i iR.
Qed.

Lemma find_best_small k i :
  0 < i <= k ->  (val i <= val (find_best k))%R -> (find_best k <= i).
Proof.
elim: k => // [[|k] IH]; first by case: (i).
rewrite find_bestE; lazy zeta.
have [] := lerP _ (val k.+2) => H //.
  rewrite (leq_eqVlt i) => /andP[Pi /orP[/eqP->|Hi] Hu].
    apply: leq_trans (_ : (k.+1 <= _)) => //.
    by have /andP[] := find_best_le _ (is_true_true : k.+1 != 0).
  by apply: IH=> //; rewrite Pi -ltnS.
rewrite (leq_eqVlt i) => /andP[Pi /orP[/eqP->|Hi] Hu] //.
have: (val (find_best k.+1) <= val i)%R.
  by apply: find_best_val_le => //; rewrite Pi.
rewrite leNgt => /negP[].
by apply: le_lt_trans H.
Qed.


Lemma find_best_coprime k : 
  k != 0 -> coprime (round ((find_best k)%:R * alpha)) (find_best k).
Proof.
move=> NZk.
set a := round _; set b := find_best _.
have Pb : 0 < b by case/andP : (find_best_le _ NZk).
pose g := gcdn a b.
have : 0 < g by rewrite gcdn_gt0 Pb orbC.
rewrite leq_eqVlt => /orP[|Lg1]; first by rewrite eq_sym.
pose a1 := (a %/ g); pose b1 := (b %/ g).
have b1B : 0 < b1 <= b.
  rewrite divn_gt0; last by apply: leq_trans Lg1.
  rewrite (dvdn_leq _ (dvdn_gcdr _ _)) //=.
  by rewrite leq_divLR ?dvdn_gcdr // leq_pmulr // (leq_trans _ Lg1).
have : (val (find_best k) <= `|b1%:R * alpha - a1%:R|)%R.
  have /andP[Pb1 b1Lb] := b1B.
  apply/find_best_val_le2/andP=> //; split => //.
  apply: leq_trans b1Lb _.
  by have /andP[] := find_best_le _ NZk.
rewrite /val -/a -/b.
have->: (b%:R * alpha - a%:R = g%:R * (b1%:R * alpha - a1%:R))%R.
  by rewrite mulrBr mulrA -!natrM ![g * _]mulnC !divnK ?(dvdn_gcdr, dvdn_gcdl).
rewrite normrM -[X in (_ <= X)%R]mul1r -subr_ge0 -mulrBl.
move=> HH.
have : (0 <= `|b1%:R * alpha - a1%:R|)%R by apply: normr_ge0.
rewrite le_eqVlt => /orP[/eqP F| F]; last first.
  move: HH; rewrite pmulr_lge0 //.
  by rewrite normr_nat subr_ge0 (ler_nat _ _ 1) leqNgt Lg1.
suff : b <= b1 by rewrite leqNgt ltn_Pdiv.
apply: find_best_small.
  have /andP[-> /= _] := b1B.
  have /andP[_ /(leq_trans _)->//] := find_best_le _ NZk.
  by apply: leq_div.
apply: le_trans (_: `|b1%:R * alpha - a1%:R|%R <= _)%R.
  apply: roundE.
  by apply: mulr_ge0 (ler0n _ _) alpha_pos.
by rewrite -F normr_ge0.
Qed.

Lemma dist_eq0 (r : rat) x y (Py : 0 < y) :
     (`|y%:R * r - x%:R|%R == 0%R) = (r == (x%:R / y%:R)%R).
Proof.
have Dy : (y%:R != 0 :> rat)%R.
  by rewrite (eqr_nat _ _ 0); case: y Py.
rewrite dist_fact; last by case: (y) Py.
by rewrite mulf_eq0 (negPf Dy) normr_eq0 subr_eq0.
Qed.

Lemma rat_coprime_eq a b c d: 
  b != 0 -> d != 0 -> coprime a b -> coprime c d ->
         ((a%:R)/(b%:R) = (c%:R)/(d%:R) :> rat)%R -> a = c /\ b = d.
Proof.
move=> Pb Pd Cab Ccd /eqP.
have Cba : coprime b a by rewrite coprime_sym.
have Cdc : coprime d c by rewrite coprime_sym.
rewrite eqr_div ?(eqr_nat _ _ 0) //  -!natrM eqr_nat => /eqP F.
split; apply/eqP; rewrite eqn_dvd.
  rewrite -(Gauss_dvdl _ Cab) -F dvdn_mulr //.
  by rewrite -(Gauss_dvdl _ Ccd) F dvdn_mulr.
rewrite -(Gauss_dvdr _ Cba) F dvdn_mull //.
by rewrite -(Gauss_dvdr _ Cdc) -F dvdn_mull.
Qed.

Lemma find_best_best_approx (lE : l != [:: a_ 0; 2]) k : 
  k != 0 -> best_approx (round ((find_best k)%:R * alpha)) (find_best k) .
Proof.
set v := round _.
move=> kP; split => [|c d /andP[dP dLk] Dk].
  by have := find_best_le _ kP; case: find_best.
have [L1s|L2s] := (leqP 2 (size l)); last first.
  pose n := nth 0 l 0.
  have alphaE : alpha = n%:R%R.
    rewrite /n; case: l L2s => [|a [|b]] //=.
    by rewrite /frac /= invr1 !mulr1 addn0 muln1.
  move: Dk.
  rewrite /v (find_best_id _ _ alphaE) // mul1r alphaE round_id.
  rewrite divr1 subrr normr0 normr_gt0 subr_eq0.
  apply: contra => /eqP<-.
  rewrite [(d%:R * _)%R]mulrC mulfK // (eqr_nat _ _ 0).
  by case: (d) dP.
case: lerP => // Hv.
have dPLk : 0 < d <= k.
  rewrite dP (leq_trans dLk) //.
  by have /andP[] := find_best_le _ kP.
have fbE : find_best k = d.
  apply/eqP; rewrite eqn_leq dLk andbT.
  apply: find_best_small => //.
  apply: le_trans Hv.
  apply: roundE; apply: mulr_ge0 => //.
  by rewrite /alpha; case: nfrac => p q; apply: divr_ge0; apply: ler_nat _ 0 _.
have valfbE : (`|d%:R * alpha - c%:R|)%R = val (find_best k).
  apply: le_anti; rewrite Hv /=.
  by apply:  find_best_val_le2.
pose x := c + v.
pose y := 2 * d.
have Py : 0 < y by rewrite muln_gt0.
have alphaE : alpha = (x%:R / y%:R)%R.
  have /eqP := valfbE.
  rewrite /val -/v fbE eqr_norm2; case/orP=> /eqP H.
    have /eqP[] := Dk; congr (_ / _)%R; last by rewrite fbE.
    by rewrite -[v%:R%R](subrK (d%:R * alpha)%R) -opprB -H opprB subrK.
  apply/eqP; rewrite -[alpha]divr1 eqr_div //; last first.
    by rewrite (eqr_nat _ _ 0); case: y Py.
  rewrite mulr1 /x natrD /y natrM.
  rewrite -[c%:R%R](subrK (d%:R * alpha)%R) -opprB H opprK.
  rewrite addrAC subrK -[(d%:R * alpha)%R]mul1r -mulrDl -(natrD _ 1 1) mulrCA.
  by rewrite [(alpha * _)%R]mulrC.
have Cp : coprime x y.
  pose g := gcdn x y.
  have : 0 < g by rewrite gcdn_gt0 muln_gt0 dP orbT.
  rewrite leq_eqVlt => /orP[|Lg1]; first by rewrite eq_sym.
  pose x1 := ((c + v) %/ g).
  pose y1 := (2 * d %/ g).
  have y1B : 0 < y1 <= k.
    rewrite divn_gt0; last by apply: leq_trans Lg1.
    rewrite (dvdn_leq _ (dvdn_gcdr _ _)) /=; last by rewrite muln_gt0.
    have /andP[_ /(leq_trans _)->//] := dPLk.
    by rewrite leq_divLR ?dvdn_gcdr // mulnC leq_mul2l Lg1 orbT.
  have alphaE1 : alpha = (x1%:R / y1%:R)%R.
    rewrite !natq_div ?dvdn_gcdr ?dvdn_gcdl //.
    rewrite -mulf_div // ?divff ?mulr1 ?invr_neq0 //.
    by rewrite (eqr_nat _ _ 0); case: (g) Lg1.
  have y1V : val y1 = 0%R.
    apply/eqP; rewrite eq_le normr_ge0 andbT.
    have /roundE : (0 <= y1%:R * alpha)%R => [|/(_ x1)].
      by rewrite mulr_ge0 ?alpha_pos ?ler0n.
    rewrite {3}alphaE1 [(_ * (_ / _))%R]mulrC divfK.
      by rewrite subrr normr0.
    rewrite (eqr_nat _ _ 0).
    by case: (y1) y1B.
  have /negP[] := Dk.
  have HH : val (find_best k) == 0%R.
    have := find_best_val_le _ _ y1B.
    by rewrite y1V normr_le0 normr_eq0.
  have/eqP<-: alpha == (c%:R / d%:R)%R by rewrite -dist_eq0 ?valfbE.
  by rewrite eq_sym -dist_eq0 // fbE.
pose n := (size l).-2.
have Ln : n.+2 = size l by rewrite !prednK; try by case: l L1s.
have [xE yE] : x = p_ n.+2 /\ y = q_ n.+2.
  apply: rat_coprime_eq => //.
  - by case: (y) Py.
  - by rewrite denomn_eq0.
  - by apply: coprime_num_denon.
  rewrite -alphaE -convnE ?convn_oversize ?Ln //.
  by case: (l) Ln.
have La1 : 1 < a_ n.+1.
  have-> : n.+1 = (size l).-1 by rewrite -Ln.
  rewrite /a_ nth_last.
  case: l L1s l_one l_zero => //= a [|] //= b l1.
  case: last (mem_last b l1) => [|[]] //.
  by move=> H1 _ _ /negP.
have Lqd : q_ n.+1 < d.
  rewrite -(ltn_pmul2l (_ : 0 < 2)) //-/y yE denomnE ?Ln //.
  have := L1s; rewrite leq_eqVlt => /orP[/eqP sE|L2s]; last first.
    rewrite -addn1; apply: leq_add.
      by rewrite leq_mul2r denomn_eq0 La1.
    suff : q_ n != 0 by case: q_.
    by rewrite denomn_eq0 /n; case: (l) L2s => // a [|] // b [|].
  have := La1; rewrite leq_eqVlt => /orP[/eqP|L2a].
    move: lE sE; rewrite /a_ /n.
    case: (l) => //= a [|b []] //= /negP H _ bE.
    by case: H; rewrite bE.
  apply: leq_trans (leq_addr _ _).
  rewrite ltn_mul2r.
   suff : q_ n.+1 != 0 by case: q_.
  by rewrite denomn_eq0.
have F1 : (`|(q_ n.+1)%:R * alpha - (p_ n.+1)%:R| < 1 / 2%:R)%R.
  rewrite dist_fact ?denomn_eq0 // -convnE //; last by case: (l) L1s.
  apply: lt_le_trans (_ : d%:R * `|alpha - s_ n.+1| <= _)%R.
    rewrite -subr_gt0 -mulrBl pmulr_rgt0; last first.
      by rewrite subr_gt0 ltr_nat.
    rewrite normr_gt0 subr_eq0; apply/eqP=> H.
    have /convn_even_alpha : 0 < n.+1 < size l by rewrite -Ln /=.
    by rewrite H ltxx if_same.
  have ->: (1 / 2%:R = d%:R * (1 / (q_ n.+2)%:R) :> rat)%R.
    rewrite -yE /y mulrA mulr1 mulnC natrM invfM //.
    by rewrite mulrA divff // (eqr_nat _ _ 0); case: (d) dP.
  apply: ler_pM; rewrite ?ler0n //.
  have /convn_alpha_up/le_trans->// : 0 < n.+1 < size l by rewrite -Ln /=.
  rewrite ler_pdivrMr; last by rewrite mulr_gt0 // denomn_gt0.
  rewrite mulrA divfK ?mul1r.
    by rewrite (ler_nat _ 1) -(ltr_nat (Num.NumDomain.clone _ rat)) denomn_gt0.
  by rewrite (eqr_nat _ _ 0) denomn_eq0.
have F2 : (1 / 2%:R <= `|(find_best k)%:R * alpha - v%:R|)%R.
  rewrite fbE alphaE /y ler_pdivrMr; last by rewrite (ltr_nat _ 0).
  rewrite -(normr_nat _ 2) -normrM mulrBl mulrC mulrA mulrC -natrM.
  rewrite divfK; last by rewrite (eqr_nat _ _ 0) -/y; case: (y) Py.
  rewrite -natrM mulnC; have [xLv|vLx] := (leqP x (2 * v)) .
    rewrite -normrN opprB -natrB // normr_nat (ler_nat _ 1).
    have := xLv; rewrite leq_eqVlt => /orP[/eqP H|]; last by rewrite subn_gt0.
    by have := Cp; rewrite H coprimeMl coprimeMr coprime2n.
  by rewrite -natrB 1?ltnW // normr_nat (ler_nat _ 1) subn_gt0.
have F :  0 < q_ n.+1 <= k .
  apply/andP; split; first by case: q_ (denomn_eq0 n.+1).
  by apply: leq_trans (ltnW Lqd) _; have /andP[] := dPLk.
have := find_best_val_le2 _ _ (p_ n.+1) kP F .
by rewrite leNgt => /negP[]; apply: lt_le_trans F2.
Qed.

Lemma best_approx_num_denom (lE : l != [::]) (l1E : l != [:: a_ 0; 2]) n :
  n != 0 -> ((n != 1) || (a_ 1 != 1%N)) -> best_approx (p_ n) (q_ n).
Proof.
case: n => // n _ nD.
have [sLn|nLs] := leqP (size l) n.+1.
  split=> [|c d cLd Dcd]; first by rewrite denomn_eq0.
  have : (0 <= `|d%:R * alpha - c%:R|)%R by apply: normr_ge0.
  rewrite -(convn_oversize _ sLn) // convnE //.
  rewrite [((q_ _)%:R * _)%R]mulrC divfK; last first.
    by rewrite (eqr_nat _ _ 0) denomn_eq0.
  rewrite subrr normr0 le_eqVlt => /orP[] //.
  have /andP[dP _] := cLd.
  rewrite eq_sym dist_eq0 // => /eqP F; case/negP: Dcd.
  by rewrite -F -convnE // (convn_oversize _ sLn).
have NZq : q_ n.+1 != 0 by rewrite denomn_eq0.
have /(find_best_best_approx l1E) := NZq.
set a := round _; set b := find_best _=> Hab.
have Pb : 0 < b by have /andP[-> ] := find_best_le _ NZq.
have [k [Nzk Hk]] := best_approx_ex _ _ lE Hab.
have Cab : coprime a b by apply: find_best_coprime.
have [aE bE] : a = p_ k /\ b = q_ k.
  apply: rat_coprime_eq => //.
  - by case: (b) Pb.
  - by rewrite denomn_eq0.
  - by apply: coprime_num_denon.
  by rewrite -convnE.
  have /andP[_ qkLqn] : 0 < q_ k <= q_ n.+1 by rewrite -bE find_best_le.
have [|nLk] := leqP k n.+1; last first.
  have [kLs|sLk] := leqP k (size l); last first.
    move: qkLqn; rewrite leqNgt => /negP[].
    rewrite [q_ k]denomn_oversize //.
    apply: denomn_lt => //.
      case/orP: nD => [nD|->]; last by rewrite orbT.
      case: eqP=> // sE.
      by move: nLs nD; rewrite sE; case: (n).
    by rewrite (leq_trans _ nLs) // ltnW.
  move: qkLqn; rewrite leqNgt => /negP[].
  apply: denomn_lt => //.
  case/orP: nD => [nD|->]; last by rewrite orbT.
  case: eqP=> // sE.
  by move: nLk nD; rewrite sE; case: (n).
rewrite leq_eqVlt => /orP[/eqP<-|kLn1].
  by rewrite -aE -bE.
have : q_ n + q_ n.+1 <= q_ n.+2.
  rewrite denomnE // addnC -{1}[q_ n.+1]mul1n.
  apply: leq_add=> //.
  apply: leq_mul => //.
  have : a_ n.+1 !=0 by rewrite eltn_pos.
  by case: a_.
rewrite -(ler_nat (Num.NumDomain.clone _ rat)) natrD leNgt => /negP[].
rewrite -[X in (X < _)%R]mul1r.
rewrite -ltr_pdivlMr ?denomn_gt0 //.
rewrite -ltr_pdivrMl; last first.
  rewrite -natrD (ltr_nat _ 0) addnC.
  have : q_ n.+1 != 0 by rewrite denomn_eq0.
  by case: q_.
rewrite mulrC -[X in (_ < X)%R]mul1r.
apply: lt_le_trans (_ : (`|(q_ k)%:R * alpha - (p_ k)%:R|)%R <= _)%R.
  apply: le_lt_trans (_ : (1 / ((q_ k)%:R + (q_ k.+1)%:R) < _)%R).
    rewrite ler_pdivrMr; last first.
      by rewrite -natrD (ltr_nat _ 0) addnC; case: q_ NZq.
    rewrite mulrC mulrA mulr1 ler_pdivlMr; last first.
      by apply: addr_gt0; apply: denomn_gt0.
    rewrite mul1r.
    apply: lerD; rewrite ler_nat; apply: denomn_monotone => //.
      by rewrite [k <= _]kLn1 ltnW // ltnW.
    by rewrite kLn1 ltnW.
  rewrite dist_fact ?denomn_eq0 // -convnE //.
  rewrite [X in (_ < X)%R]mulrC -lter_pdivrMr; last by rewrite  denomn_gt0.
  rewrite -mulrA -invfM -?(natrD, natrM) addnC.
  apply: convn_alpha_low.
  rewrite (leq_trans _ nLs); first by case: (k) Nzk.
  by rewrite ltnS ltnW.
apply: le_trans (_ : (`|(q_ n.+1)%:R * alpha - (p_ n.+1)%:R|)%R <= _)%R.
  rewrite -aE -bE.
  apply: find_best_val_le2; first by rewrite denomn_eq0.
  have: q_ n.+1 != 0 by rewrite denomn_eq0.
  by case: q_ => /=.
rewrite dist_fact?denomn_eq0 // -convnE // mulrC -ler_pdivlMr; last first.
  by rewrite denomn_gt0.
by rewrite -mulrA -invfM convn_alpha_up.
Qed.

End Rat.

Local Notation " `[ a / b ]" := (Rat (valq :=(a, b)) _).

Compute nfrac [:: 0; 2].

Compute convn [:: 3; 7; 15] 0.
Compute remn [:: 3; 7; 15] 0.
Compute convn [:: 3; 7; 15] 1.
Compute remn [:: 3; 7; 15] 1.
Compute convn [:: 3; 7; 15] 2.
Compute remn [:: 3; 7; 15] 2.
Compute convn [:: 3; 7; 15] 3. 
Compute remn [:: 3; 7; 15] 3.
Compute halton [::  3; 7; 15] 1.

Compute nfrac [:: 0; 1 ; 2].
Compute numn [:: 0; 1 ; 2] 1.
Compute denomn [:: 0; 1 ; 2] 1.
Compute numn [:: 0; 1 ; 2] 2.
Compute denomn [:: 0; 1 ; 2] 2.

Compute nfrac [:: 0; 1 ; 2].
Compute numn [:: 0; 1 ; 2] 1.
Compute denomn [:: 0; 1 ; 2] 1.
Compute numn [:: 0; 1 ; 2] 2.
Compute denomn [:: 0; 1 ; 2] 2.

End MoreContinuant.