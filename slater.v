(******************************************************************************)
(*                                                                            *)
(* Formalisation du papier :                                                  *)
(*          Gaps and steps for the sequence n@ mod 1                          *)
(*                                                                            *)
(******************************************************************************)

Require Import Reals Psatz.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun fintype bigop.
Require Import moreR.

Open Scope R_scope.

Section Paper.

Variable a : R.
Hypothesis a_range : 0 < a < 1.

(* Some auxillary facts                                                       *)

Fact a0 : `{0 * a} = 0.
Proof. by rewrite Rmult_0_l (fracZ 0); lra. Qed.

Fact aD  m n : (m + n)%N * a = m * a + n * a.
Proof. by rewrite plus_INR; ring. Qed.

Fact aB m n : (n <= m)%N -> (m - n)%N * a = m * a - n * a.
Proof. by move=> s2Ls1; rewrite minus_INR; try ring. Qed.

Variable N : nat.
Hypothesis Npos : (0 < N)%nat.
Hypothesis Ndiff0 : forall n, (0 < n <= N)%N -> `{n * a} <> 0.

Lemma a1NZ : `{a} <> 0.
Proof. by rewrite -[a]Rmult_1_l; apply: (Ndiff0 1). Qed.

Lemma Ninj m n :
   (m <= N)%N -> (n <= N)%N -> `{m * a} = `{n * a} -> m = n.
Proof.
wlog : m n / (m < n)%N => [WH mLN nLN maEna|mLN nLN mLn maEna].
  by case: (ltngtP m n)=> // H; last apply: esym; apply WH=> //; rewrite ltnW.
case: (Ndiff0 (n - m)).
  by rewrite subn_gt0 mLN (leq_trans (leq_subr _ _)).
rewrite aB 1?ltnW // fracB; lra.
Qed.

(* Find the largest `{a * m} strictly smaller than x  for m <= n             *)
Fixpoint get_left n x : option nat :=
  if n is n1.+1 then
    if Rlt_dec `{n * a} x then
       if get_left n1 x is Some m then
          Some (if Rle_dec `{m * a} `{n * a} then n else m)
        else Some n
    else get_left n1 x
  else if Rlt_dec 0 x then Some 0%N else None.

Inductive get_left_prop (n : nat) (x : R) : option nat -> Type :=
  | get_left_None :  
       (forall m, (m <= n)%N -> x <= `{m * a}) -> get_left_prop n x None
  | get_left_Some :
       forall m, (m <= n)%N -> `{m * a} < x ->
       (forall m1, (m1 <= n)%N -> `{m1 * a} < x -> `{m1 * a} <= `{m * a}) ->
       get_left_prop n x (Some m).

Lemma get_left_spec n x : get_left_prop n x (get_left n x).
Proof.
elim: n => /= [|n [IH|m mLn maLx IH]].
- case: Rlt_dec=> H.
    by constructor=> [||[_|]] //; rewrite a0; lra.
  constructor=> m _.
  by have := frac_bound (m * a); lra.
- by  (case: Rlt_dec=> H; constructor)=> // [m1|m];
      rewrite leq_eqVlt=> /orP[/eqP->|];
      try (rewrite ?ltnS => /IH); lra.
case: Rlt_dec=> n1aLx; last first.
  constructor; try lra; first by rewrite (leq_trans mLn).
  move=> m1; rewrite leq_eqVlt=> /orP[/eqP->|]; try lra.
  by rewrite ltnS; exact: IH.
(case: Rle_dec=> mxLnx; constructor)=> //= [m1||m1].
- rewrite  leq_eqVlt=> /orP[/eqP->|]; try lra; rewrite ltnS.
  by move=> m1Ln m1aLx; have:= IH _ m1Ln m1aLx; lra.
- by apply: leq_trans mLn _.
rewrite  leq_eqVlt=> /orP[/eqP->|]; try lra; rewrite ltnS.
by move=> m1Ln m1aLx; have:= IH _ m1Ln m1aLx; lra.
Qed.

(* Find the largest '{m * a} for m <= n                                       *)
Definition get_max n := odflt 0%N (get_left n 1).

Lemma get_max0 : get_max 0 = 0%N.
Proof. by rewrite /get_max /get_left; case: Rlt_dec. Qed.

Lemma get_max1 : get_max 1 = 1%N.
Proof. 
rewrite /get_max /get_left; do 2 case: Rlt_dec=> //=; try lra.
  rewrite a0; case: Rle_dec=> //=.
  by rewrite Rmult_1_l; have := frac_bound a; lra.
rewrite Rmult_1_l; have := frac_bound a; lra.
Qed.

Lemma get_max_max m n : (m <= n)%N -> `{m * a} <= `{get_max n * a}.
Proof.
move=> mLn; rewrite /get_max; case: get_left_spec=> /=.
  by move/(_ _ mLn); have := frac_bound (m * a); lra.
 move=> m1 m1Lm m1aL1; apply=> //; have := frac_bound (m * a); lra.
Qed.

Lemma get_maxB n m1 m2 : (m2 < m1 <= n)%N -> (n <= N)%N ->
  `{m1 * a} <= `{m2 * a} -> 1 - `{get_max n * a} <= `{m2 * a} - `{m1 * a}.
Proof.
move=> /andP[m2Lm1 m1Ln] nLN m1aLm2a.
rewrite -fracB // -[X in _ <= `{X}]Ropp_minus_distr -aB;  last by apply: ltnW.
have m1Bm2Ln : (m1 - m2 <= n)%N by apply: (leq_trans (leq_subr _ _)).
rewrite fracN; first by move/get_max_max : m1Bm2Ln; lra.
by apply: Ndiff0; rewrite subn_gt0 m2Lm1 (leq_trans _ nLN). 
Qed.

Lemma Lget_max n : (get_max n <= n)%N.
Proof. by rewrite /get_max; case: get_left_spec. Qed.

Lemma get_max_NZ n : n != 0%N -> get_max n != 0%N.
Proof.
move=> nNZ; apply/eqP=> gZ.
have/get_max_max: (1 <= n)%N by rewrite lt0n.
rewrite Rmult_1_l gZ Rmult_0_l (fracZ 0).
have [] := (frac_bound a, a1NZ); lra.
Qed.

(* Find the smallest `{a * m} strictly larger than x  for m <= n              *)
Fixpoint get_right n x : option nat :=
  if n is n1.+1 then
    if Rlt_dec x `{n * a} then
       if get_right n1 x is Some m then
          Some (if Rle_dec `{n * a} `{m * a} then n else m)
        else Some n
    else get_right n1 x
  else if Rlt_dec x 0 then Some 0%N else None.

Inductive get_right_prop (n : nat) (x : R) : option nat -> Type :=
  | get_right_None :  
       (forall m, (m <= n)%N -> `{m * a} <= x) -> get_right_prop n x None
  | get_right_Some :
       forall m, (m <= n)%N -> x < `{m * a} ->
       (forall m1, (m1 <= n)%N -> x < `{m1 * a} -> `{m * a} <= `{m1 * a}) ->
       get_right_prop n x (Some m).

Lemma get_right_spec n x : get_right_prop n x (get_right n x).
Proof.
elim: n => /= [|n [IH|m mLn maLx IH]].
- case: Rlt_dec=> H.
    by constructor=> [||[_|]] //; rewrite a0; lra.
  by constructor=> [[|]] // _; rewrite a0; lra.
- by  (case: Rlt_dec=> H; constructor)=> // [m1|m];
      rewrite leq_eqVlt=> /orP[/eqP->|];
      try (rewrite ?ltnS => /IH); lra.
case: Rlt_dec=> n1aLx; last first.
  constructor; try lra; first by rewrite (leq_trans mLn).
  move=> m1; rewrite leq_eqVlt=> /orP[/eqP->|]; try lra.
  by rewrite ltnS; exact: IH.
(case: Rle_dec=> mxLnx; constructor)=> //= [m1||m1].
- rewrite  leq_eqVlt=> /orP[/eqP->|]; try lra; rewrite ltnS.
  by move=> m1Ln m1aLx; have:= IH _ m1Ln m1aLx; lra.
- by apply: leq_trans mLn _.
rewrite  leq_eqVlt=> /orP[/eqP->|]; try lra; rewrite ltnS.
by move=> m1Ln m1aLx; have:= IH _ m1Ln m1aLx; lra.
Qed.

(* Find the smallest '{m * a} for 0 < m <= n                                  *)
Definition get_min n := odflt 0%N (get_right n 0).

Lemma get_min0 : get_min 0 = 0%N.
Proof. by rewrite /get_min /get_right; case: Rlt_dec. Qed.

Lemma get_min1 : get_min 1 = 1%N.
Proof. 
rewrite /get_min /get_right; do 2 case: Rlt_dec=> //=; try lra.
rewrite Rmult_1_l; have [] := (frac_bound a, a1NZ); lra.
Qed.

Lemma get_min_min m n : 
  (m <= n <= N)%N -> m != 0%N -> `{get_min n * a} <= `{m * a}.
Proof.
move=> mLnLN mNZ; have /andP[mLn nLm] := mLnLN.
 rewrite /get_min; case: get_right_spec=> /=.
  move/(_ _ mLn); have := frac_bound (m * a); rewrite a0; lra.
move=> m1 m1Lm m1aL1; apply=> //.
have := frac_bound (m * a); try lra.
suff: `{m * a} <> 0 by lra.
by apply: Ndiff0; rewrite lt0n mNZ (leq_trans mLn _).
Qed.

Lemma Lget_min n : (get_min n <= n)%N.
Proof. by rewrite /get_min; case: get_right_spec. Qed.

Lemma get_min_NZ n : n != 0%N -> get_min n != 0%N.
Proof.
rewrite /get_min; case: get_right_spec=> /= [naD aNZ|m _ maPos _ _].
  have /naD : (1 <= n)%N by case: (n) aNZ.
  by rewrite Rmult_1_l; have := frac_bound a; have := a1NZ; lra.
by apply/eqP=> mZ; rewrite mZ a0 in maPos; lra.
Qed.

Lemma get_minB n m1 m2 : (m1 < m2 <= n)%N -> (n <= N)%N ->
  `{m1 * a} <= `{m2 * a} -> `{get_min n * a} <= `{m2 * a} - `{m1 * a}.
Proof.
move=> /andP[m1Lm2 m2Ln] nLN m1aLm2a.
rewrite -fracB // -aB 1?ltnW //.
apply: get_min_min; last by rewrite -lt0n subn_gt0.
by rewrite (leq_trans (leq_subr _ _)).
Qed.

(* Find the next on the right                                                 *)
Definition get_next (n m : nat) := odflt 0%N (get_right n `{m * a}).

Lemma get_next0 : get_next 0 0 = 0%N.
Proof. by rewrite /get_next /get_right a0; case: Rlt_dec. Qed.

Lemma get_next1_0 : get_next 1 0 = 1%N.
Proof. 
rewrite /get_next /get_right a0 Rmult_1_l; do 2 case: Rlt_dec=> //=; try lra.
have [] := (frac_bound a, a1NZ); lra.
Qed.

Lemma get_next1_1 : get_next 1 1 = 0%N.
Proof. 
rewrite /get_next /get_right Rmult_1_l; do 2 case: Rlt_dec=> //=; lra.
Qed.

Inductive get_next_prop (n : nat) : nat -> nat -> Type :=
  | get_next_is_max :  get_next_prop n (get_max n) 0
  | get_next_val :
       forall (m m1 : nat), (m1 <= n)%N -> `{m * a} < `{m1 * a} ->
       (forall m2, 
          (m2 <= n)%N -> `{m * a} < `{m2 * a} -> `{m1 * a} <= `{m2 * a}) ->
        get_next_prop n m m1.

Lemma get_next_spec n m : (m <= n <= N)%N -> get_next_prop n m (get_next n m).
Proof.
move=> /andP[mLn nLN]; rewrite /get_next; case: get_right_spec=> /=; last first.
  by move=> m1 m1Ln maLm1 H; apply: get_next_val=> //.
move=> Lma.
suff->: m = get_max n by constructor.
apply: Ninj; first by apply: leq_trans nLN.
  by apply: leq_trans (Lget_max _) _.
have := get_max_max _ _ mLn; suff: `{get_max n * a} <= `{m * a}; try lra.
apply/Lma/Lget_max.
Qed.

Lemma get_next_0 n m :
  (m <= n <= N)%N -> get_next n m = 0%N -> m = get_max n.
Proof.
move=> mLnLN; case: get_next_spec=> //.
move=> m1 m2 m2Ln m1aLm2a _ m2Z.
by rewrite m2Z a0 in m1aLm2a; have := frac_bound (m1 * a); lra.
Qed.

Lemma get_next_max n : get_next n (get_max n) = 0%N.
Proof.
rewrite /get_next; case: get_right_spec=> //= m mLn HH _.
by have := get_max_max _ _ mLn; lra.
Qed.

Lemma Lget_next n m : (get_next n m <= n)%N.
Proof. by rewrite /get_next; case: get_right_spec. Qed.

Lemma get_nextL n m :
  (m <= n <= N)%N -> m != get_max n -> `{m * a} < `{get_next n m * a}.
Proof.  by move=> mLnLN; case: get_next_spec=> // /negP[]. Qed.

Lemma LminDmax n :  n != 0%N -> (n <= N)%N -> (n < get_min n + get_max n)%N.
Proof.
move=> nNZ nLM; case: leqP=> // mmLn.
have gNZ := get_min_NZ _ nNZ.
have /Ndiff0 gaNZ : (0 < get_min n <= N)%N.
  by rewrite lt0n  gNZ // (leq_trans (Lget_min _)).
have :=  frac_bound (get_min n * a).
have := get_max_max _ _ mmLn.
rewrite -{2}(addnK (get_min n) (get_max n)) (addnC (get_max n)) aB ?fracB; try lra.
  apply: get_min_min; first by rewrite mmLn.
  by rewrite -lt0n addn_gt0 lt0n gNZ.
by apply: leq_addr.
Qed.

Lemma get_minD n m :
   (0 < n <= N)%N -> (m + get_min n <= n)%N -> 
    `{(m + get_min n)%N * a} = `{m * a} + `{get_min n * a}.
Proof.
move=> /andP[nP nLN] mgLn.
have nNZ : n != 0%N by rewrite  -lt0n.
have mgNZ : (m + get_min n != 0)%N.
  by rewrite -lt0n addn_gt0 !lt0n get_min_NZ ?orbT.
have mL : (m + get_min n <= n <= N)%N by rewrite mgLn.
have := get_min_min _ _ mL mgNZ.
have := frac_bound (m * a); try lra.
rewrite aD => Lmg.
by case: Rle_dec (fracD_cond (m * a) (get_min n * a))=> /=; lra.
Qed.

Lemma get_nextDmin n m :
  (0 < n <= N)%N -> (m + get_min n <= n)%N -> get_next n m = (m + get_min n)%N.
Proof.
move=> nPLN mgLn; have /andP[nP nLN] := nPLN.
have nNZ : n != 0%N by rewrite  -lt0n.
apply: Ninj; first by apply: leq_trans (Lget_next _ _) nLN.
  by apply: leq_trans _ nLN.
case: get_next_spec (mgLn) => [|Ln|m1 m2 m2Ln m1aLm2a m2_max m1gLn].
- by rewrite (leq_trans (leq_addr _ _) mgLn).
- by have := LminDmax _ nNZ nLN; rewrite leqNgt addnC ltnS Ln.
apply: Rle_antisym.
  apply: m2_max=> //.
  have /Ndiff0 : (0 < get_min n <= N)%N.
    by rewrite lt0n get_min_NZ // (leq_trans (Lget_min _)).
  have := frac_bound (get_min n * a).
  rewrite get_minD //; lra.
case: (leqP m1 m2)=> [m1Lm2|m2Lm1].
  have m1Bm2NZ : (m2 - m1 != 0)%N.
    rewrite -lt0n subn_gt0 ltn_neqAle andbC m1Lm2.
    by apply/eqP=> m1Em2; rewrite m1Em2 in m1aLm2a; lra.
  have/get_min_min/(_ m1Bm2NZ) : (m2 - m1 <= n <= N)%N.
    by rewrite (leq_trans (leq_subr _ _)).
  by rewrite get_minD // aB // fracB; lra.
have [/eqP->|s1NZ] := boolP (m1 == 0%N).
  rewrite add0n.
  apply: get_min_min; rewrite ?m2Ln //.
  apply/eqP=> m2Z; rewrite m2Z a0 in m1aLm2a.
  by have := frac_bound (m1 * a); lra.
have [|m2aLm1a] := Rle_or_lt `{(m1 + get_min n)%N * a} `{m2 * a}.
  by lra.
suff : `{get_min n * a} <= `{(m1 + get_min n)%N * a} - `{m2 * a}.
  by rewrite get_minD //; lra.
apply: get_minB=> //; try lra.
by rewrite (leq_trans m2Lm1 (leq_addr _ _)) // ltnW.
Qed.

Lemma get_maxD n m :
   (n <= N)%N -> (get_max n < m <= n)%N ->
    `{m * a} = `{(m - get_max n)%N * a} + `{get_max n * a} - 1.
Proof.
set b := get_max n; set m1 := (m - b)%N.
move=> nLN gLmLn; have /andP[gLm mLn] := gLmLn.
have : `{b * a - m * a} = `{b * a} - `{m * a}.
  by rewrite fracB //; apply: get_max_max.
have Bb := frac_bound (b * a).
have->: b * a - m * a = - (m1 * a).
  rewrite minus_INR 1?ltnW //; lra.
rewrite fracN ?addnK; try lra.
apply: Ndiff0.
by rewrite subn_gt0 gLm (leq_trans (leq_subr _ _) (leq_trans _ nLN)).
Qed.

Lemma get_nextDmax n m :
  (n <= N)%N -> (get_max n <= m <= n)%N -> get_next n m = (m - get_max n)%N.
Proof.
move=> nLN /andP[].
rewrite leq_eqVlt=> /orP[/eqP<- mLn|gLn mLn]; first by rewrite subnn get_next_max.
have mLN : (m <= N)%N by apply: leq_trans nLN.
have mBLN : (m - get_max n <= N)%N by apply: leq_trans (leq_subr _ _) mLN.
apply: Ninj=> //; first by apply: leq_trans (Lget_next _ _) nLN.
case: get_next_spec gLn (mLn) (mLN) mBLN; first by rewrite mLn.
  by rewrite subnn.
move=> {m mLn mLN} m m1 m1Lm mgaLm1a m2_min gLn mLn mLN mBLN.
set b := get_max n in gLn, mLn, mBLN; rewrite -/b.
have Ea : `{m * a} = `{(m - b)%N * a} + `{b * a} - 1.
  by apply: get_maxD; rewrite ?gLn.
apply: Rle_antisym.
  apply: m2_min; first by apply: leq_trans (leq_subr _ _) _.
  have := frac_bound (b * a); lra.
suff: 1 - `{b * a} <=  `{m1 * a} -  `{m * a} by lra.
case: (leqP m m1)=> [mgLm1|m1Lmg]; last first.
  by apply: get_maxB=> //; try lra; rewrite m1Lmg.
move: mgLm1; rewrite leq_eqVlt => /orP[/eqP mgEm1|mgLm1].
  by rewrite mgEm1 in mgaLm1a; lra.
have [|maLm1a] := Rle_or_lt `{(m - b)%N * a} `{m1 * a}; try lra.
suff : 1 - `{b * a} <= `{(m - b)%N * a} - `{m1 * a} by lra.
apply: get_maxB => //; try lra.
by rewrite (leq_trans _ mgLm1) // ltnS leq_subr.
Qed.

Lemma diff_min_max n : (1 < n <= N)%N -> get_min n != get_max n.
Proof.
set b := get_min n; set B := get_max n.
move=> nG1LN;  have /andP[nG1 nLN] := nG1LN.
apply/eqP=> bEB.
have nNZ : (0 < n)%N by exact: (ltnW nG1).
suff: (1 = 2)%N by [].
apply: Ninj; try (apply: leq_trans nLN=> //).
by apply: Rle_antisym; (apply: (Rle_trans _ `{B * a}); 
  [apply: get_max_max | rewrite -bEB; apply: get_min_min];
  rewrite ?nNZ).
Qed.

Lemma LBget_nextDmax_min n m m1 (b := get_min n) (B := get_max n) : 
    (n <= N)%N -> (n - b < m < B)%N -> (m1 <= n)%N -> 
    `{m * a} < `{m1 * a} -> `{b * a} + 1 - `{B * a} <= `{m1 * a} - `{m * a}.
Proof.
move=> nLN /andP[nBgLm mLg] m1Ln m1aLma.
case: (ltngtP m m1)=> [mLm1|m1Lm|mEm1]; last first.
- by rewrite mEm1 in m1aLma; lra. 
- have Bm1mLB : (B + m1 - m <= B)%N.
    by rewrite leq_subLR addnC leq_add2r ltnW.
  have Bm1mLn : (B + m1 - m <= n)%N.
    by apply: (leq_trans _ (Lget_max _)).
  have m1mE : (m - m1 = (B - (B + m1 - m)))%N.
    rewrite subnBA ?subnDl //.
    by rewrite (leq_trans (ltnW mLg) (leq_addr _ _)).
  rewrite -fracB; try lra.
  rewrite -[X in _ <= `{X}]Ropp_minus_distr -aB ?fracN //; last by apply: ltnW.
    rewrite m1mE aB ?fracB //.
    suff: `{b * a} <=`{(B + m1 - m)%N * a} by lra.
      apply: get_min_min; first by rewrite Bm1mLn.
      rewrite -lt0n addnC.
      by rewrite -addnBA ?addn_gt0 1?orbC ?subn_gt0 ?mLg // ltnW.
    by apply: get_max_max.
  apply: Ndiff0; rewrite subn_gt0 m1Lm.
  rewrite (leq_trans (leq_subr _ _)) // (leq_trans (ltnW mLg)) //.
  by rewrite (leq_trans (Lget_max _)).
have nNZ : n != 0%N.
  by rewrite -lt0n (leq_trans _ m1Ln) // (leq_ltn_trans _ mLm1).
have bNZ : b != 0%N by apply: get_min_NZ.
have m1mLb: (m1 - m < b)%N.
  rewrite -[b](addnK m) ltn_sub2r //.
    by rewrite -{1}[m]add0n ltn_add2r lt0n.
  rewrite (leq_ltn_trans m1Ln) //.
  by rewrite -[n](@subnK b) 1?addnC ?ltn_add2l // Lget_min.
rewrite -fracB; try lra; rewrite -aB 1?ltnW //.
have m1mE : (m1 - m = (b - (b + m - m1)))%N.
  by rewrite subnBA ?subnDl // addnC -leq_subLR ltnW.
have bmm1Lb : (b + m - m1 <= b)%N.
  rewrite -subnBA; last by rewrite ltnW.
  by rewrite -{2}[b]subn0 leq_sub2l.
have bmm1Ln : (b + m - m1 <= n)%N.
  by apply: leq_trans _ (Lget_min _).
rewrite m1mE aB // -[X in _ <= `{X}]Ropp_minus_distr fracN.
  rewrite [X in _ <= 1 - X]fracB.
    suff:  `{(b + m - m1)%N * a} <= `{B * a} by lra.
    by apply: get_max_max.
  apply: get_min_min; first by rewrite (leq_trans bmm1Ln) ?nLN.
  rewrite -subnBA; last by rewrite ltnW.
  by rewrite -lt0n subn_gt0.
apply : fracNZ_N; rewrite Ropp_minus_distr -aB // -m1mE.
apply: Ndiff0; rewrite subn_gt0 mLm1 (leq_trans (ltnW m1mLb)) //.
by apply: (leq_trans (Lget_min _)).
Qed.

Fact diff_min_max_nb n m (b := get_min n) (B := get_max n) :
    (n <= N)%N -> (n - b < m < B)%N -> (b != B).
Proof.
move=> nLN /andP[nbLm mLB].
case: (leqP 2 n)=> [nG2|nL1]; first by apply: diff_min_max; rewrite nG2.
move: nL1 nbLm mLB; rewrite /B /b.
case: (n) => [|[|]]; rewrite ?(get_max0, get_max1) //.
by rewrite get_min1; case: (m).
Qed.

Lemma get_min_maxD n m (b := get_min n) (B := get_max n) : 
    (n <= N)%N -> (n - b < m < B)%N -> 
    `{(m + b - B)%N * a} = `{m * a} + 1 + `{b * a} - `{B * a}.
Proof.
move=> nLN /andP[nBgLm mLg].
have [bLn BLn] := (Lget_min n, Lget_max n).
have BLN : (B <= N)%N by apply: leq_trans BLn _.
have bLN : (b <= N)%N by apply: leq_trans bLn _.
have mLN : (m <= N)%N.
  by apply: (leq_trans (leq_trans (ltnW mLg) _) nLN).
have mLn : (m <= n)%N by apply: leq_trans (ltnW mLg) _.
have /eqP bNEB : b != B.
  by apply: (diff_min_max_nb _ m); rewrite ?nBgLm.
have mNZ : m != 0%N.
  by rewrite -lt0n (leq_ltn_trans _ nBgLm).
have [baLma maLBa] : `{b * a} <= `{m * a} <= `{B * a}.
  by split; [apply: get_min_min | apply: get_max_max]; rewrite ?mLn.
have BmaE : `{(B - m)%N * a} = `{B * a} - `{m * a}.
  by rewrite aB 1?ltnW // fracB; lra.
have baLBama : `{b * a} <= `{(B - m)%N * a}.
  apply: get_min_min; last by rewrite -lt0n subn_gt0.
  by rewrite (leq_trans (leq_subr _ _)).
case: (ltngtP b B)=> // [bLB|BLb].
  have BbLm : (B - b <= m)%N.
    by apply/(leq_trans _ (ltnW nBgLm))/leq_sub2r.
  have BbLN : (B - b <= N)%N  by apply: leq_trans mLN.
  have BbaE : `{(B - b)%N * a} = `{B * a} - `{b * a}.
    by rewrite aB 1?ltnW // fracB; lra.
  have -> : (m + b - B)%N * a = m * a  + - ((B - b)%N * a).
    by rewrite -subnBA 1?ltnW // aB; try lra.
  move: (fracD_cond (m * a) (- ((B - b)%N * a))).
  rewrite fracN; last first.
    by apply: Ndiff0; rewrite subn_gt0 bLB.
  case: Rle_dec=> /= Lma; try lra.
  suff mEBb : m = (B - b)%N by move: nBgLm; rewrite mEBb ltnNge leq_sub2r.
  by apply: Ninj=> //; lra.
have BmLN : (B - m <= N)%N by apply: leq_trans (leq_subr _ _) _.
have BbLN : (B - b <= N)%N by apply: leq_trans (leq_subr _ _) _.
have bBaE : `{(b - B)%N * a} = 1 + `{b * a} - `{B * a}.
  rewrite aB 1?ltnW // -Ropp_minus_distr fracN; first by rewrite fracB; lra.
  apply : fracNZ_N; rewrite Ropp_minus_distr -aB 1? ltnW //.
  apply: Ndiff0; rewrite subn_gt0 BLb.
  by apply: leq_trans (leq_subr _ _) _.
have -> : (m + b - B)%N * a = m * a  + ((b - B)%N * a).
  by rewrite -addnBA 1?ltnW // aD; lra.
move: (fracD_cond (m * a) ((b - B)%N * a)).
case: Rle_dec=> /= Lma; try lra.
suff bEBm : b = (B - m)%N.
  by move: BLb; rewrite bEBm ltnNge leq_subr.
have BbaE : `{(B - m)%N * a} = `{B * a} - `{m * a}.
  rewrite aB 1?ltnW // fracB; lra.
apply: Ninj=> //; lra.
Qed.

Lemma get_nextDmin_max n m (b := get_min n) (B := get_max n) :
    (n <= N)%N -> (n - b < m < B)%N -> (get_next n m = m + b - B)%N.
Proof.
move=> nLN /andP[nBgLm mLg].
have bNEB : b != B by apply: (diff_min_max_nb _ m); rewrite ?nBgLm.
case: get_next_spec (nBgLm) (mLg).
- by rewrite (leq_trans (ltnW mLg)) // Lget_max.
- by rewrite ltnn.
have nNZ : n != 0%N.
  apply: contra bNEB; rewrite /b /B=> /eqP->.
  by rewrite get_min0 get_max0.
move=> {m nBgLm mLg} m m1 m1Ln maLm1a m2_min nBgLm mLg.
have mbBLn: (m + b - B <= n)%N.
  apply: leq_trans (Lget_min _).
  rewrite -[get_min n](addnK B) -/b.
  by apply: leq_sub2r; rewrite addnC leq_add2l ltnW.
apply: Ninj; first by rewrite (leq_trans m1Ln).
  by apply: leq_trans nLN.
apply: Rle_antisym.
  apply: m2_min=> //.
  rewrite get_min_maxD ?nBgLm -/b -/B //.
  by have [] := (frac_bound (b * a), frac_bound (B * a)); lra.
rewrite get_min_maxD ?nBgLm -/b -/B //.
suff: `{b * a} + 1 - `{B * a} <= `{m1 * a} - `{m * a} by lra.
case: (ltngtP m m1)=> [mLm1|m1Lm|mEm1]; last first.
- by rewrite mEm1 in maLm1a; lra. 
- have Bm1mLB : (B + m1 - m <= B)%N.
    by rewrite leq_subLR addnC leq_add2r ltnW.
  have Bm1mLn : (B + m1 - m <= n)%N.
    by apply: (leq_trans _ (Lget_max _)).
  have m1mE : (m - m1 = (B - (B + m1 - m)))%N.
    rewrite subnBA ?subnDl //.
    by rewrite (leq_trans (ltnW mLg) (leq_addr _ _)).
  rewrite -fracB; try lra.
  rewrite -[X in _ <= `{X}]Ropp_minus_distr -aB ?fracN //; last by apply: ltnW.
    rewrite m1mE aB ?fracB //.
    suff: `{b * a} <=`{(B + m1 - m)%N * a} by lra.
      apply: get_min_min; first by rewrite Bm1mLn.
      rewrite -lt0n addnC.
      by rewrite -addnBA ?addn_gt0 1?orbC ?subn_gt0 ?mLg // ltnW.
    by apply: get_max_max.
  apply: Ndiff0; rewrite subn_gt0 m1Lm.
  rewrite (leq_trans (leq_subr _ _)) // (leq_trans (ltnW mLg)) //.
  by rewrite (leq_trans (Lget_max _)).
have bNZ : b != 0%N by apply: get_min_NZ.
have m1mLb: (m1 - m < b)%N.
  rewrite -[b](addnK m) ltn_sub2r //.
    by rewrite -{1}[m]add0n ltn_add2r lt0n.
  rewrite (leq_ltn_trans m1Ln) //.
  by rewrite -[n](@subnK b) 1?addnC ?ltn_add2l // Lget_min.
rewrite -fracB; try lra; rewrite -aB 1?ltnW //.
have m1mE : (m1 - m = (b - (b + m - m1)))%N.
  by rewrite subnBA ?subnDl // addnC -leq_subLR ltnW.
have bmm1Lb : (b + m - m1 <= b)%N.
  rewrite -subnBA; last by rewrite ltnW.
  by rewrite -{2}[b]subn0 leq_sub2l.
have bmm1Ln : (b + m - m1 <= n)%N.
  by apply: leq_trans _ (Lget_min _).
rewrite m1mE aB // -[X in _ <= `{X}]Ropp_minus_distr fracN.
  rewrite [X in _ <= 1 - X]fracB.
    suff:  `{(b + m - m1)%N * a} <= `{B * a} by lra.
    by apply: get_max_max.
  apply: get_min_min; first by rewrite (leq_trans bmm1Ln) ?nLN.
  rewrite -subnBA; last by rewrite ltnW.
  by rewrite -lt0n subn_gt0.
apply : fracNZ_N; rewrite Ropp_minus_distr -aB // -m1mE.
apply: Ndiff0; rewrite subn_gt0 mLm1 (leq_trans (ltnW m1mLb)) //.
by apply: (leq_trans (Lget_min _)).
Qed.

Lemma get_maxS n : (n.+1 <= N)%N ->
   get_max n.+1 = 
     if Rle_dec `{get_max n * a} `{n.+1 * a} then n.+1 else get_max n.
Proof.
move=> nLN.
have naB := frac_bound (n.+1 * a).
rewrite /get_max /=; case: get_left=> [g|] /=.
  case: Rlt_dec=> //=; lra.
case: Rlt_dec=> //=; try lra.
case: Rle_dec=> //=; try lra.
rewrite a0; move=> HH.
by suff /Ndiff0 : (0 < n.+1 <= N)%N by lra.
Qed.

Lemma get_minS n : (1 < n.+1 <= N)%N ->
   get_min n.+1 = 
     if Rle_dec `{n.+1 * a} `{get_min n * a} then n.+1 else get_min n.
Proof.
move=> /andP[oLn nLN].
have : get_min n != 0%N by apply: get_min_NZ; case: (n) oLn.
have naB := frac_bound (n.+1 * a).
rewrite /get_min /=; case: get_right => [g|] /=.
  case: Rlt_dec=> //=; try lra.
  by suff /Ndiff0 : (0 < n.+1 <= N)%N by lra.
case: Rle_dec; case: Rlt_dec=> //=; lra.
Qed.

(* Find the predecessor on the left                                           *)
Definition get_prev (n m : nat) := odflt (get_max n) (get_left n `{m * a}).

Inductive get_prev_prop (n : nat) : nat -> nat -> Type :=
  | get_prev_is_max :  get_prev_prop n 0 (get_max n)
  | get_prev_val :
       forall (m m1 : nat), (m1 <= n)%N -> `{m1 * a} < `{m * a} ->
       (forall m2, 
          (m2 <= n)%N -> `{m2 * a} < `{m * a} -> `{m2 * a} <= `{m1 * a}) ->
        get_prev_prop n m m1.

Lemma get_prev_spec n m : (m <= n <= N)%N -> get_prev_prop n m (get_prev n m).
Proof.
move=> /andP[mLn nLN]; rewrite /get_prev; case: get_left_spec=> /=; last first.
  by move=> m1 m1Ln maLm1 H; apply: get_prev_val=> //.
move=> Lma.
suff->: m = 0%N by constructor.
apply: Ninj=> //; first by apply: leq_trans nLN.
have : `{0%N * a} <= `{m * a} by rewrite a0; have := frac_bound (m * a); lra.
suff: `{m * a} <= `{0%N * a}; try lra.
by apply/Lma.
Qed.

Lemma get_prev0 n : get_prev n 0 = get_max n.
Proof.
rewrite /get_prev; case: get_left_spec => //= m.
rewrite a0; have := frac_bound (m * a); lra.
Qed.

Lemma get_nextK n m : (m <= n <= N)%N -> get_prev n (get_next n m) = m.
Proof.
move=> /andP[mLn nLN].
(case: get_next_spec (mLn); rewrite ?mLn //=).
   by rewrite get_prev0.
move=> {m mLn}m m1 m1Ln; case: get_prev_spec (m1Ln).
- by rewrite m1Ln.
- by rewrite a0; have := frac_bound (m * a); lra.
move=> {m1 m1Ln}m1 m2 m2Ln m2aLm1a m2P m1Ln maLm1a m1P mLn.
apply: Ninj=> //; try by rewrite (leq_trans _ nLN).
have maLm2a := m2P _ mLn maLm1a.
suff : ~ `{m * a} < `{m2 * a} by lra.
move=> masLm2a.
suff : `{m1 * a} <= `{m2 * a} by lra.
apply: m1P=> //; lra.
Qed.

Lemma get_prevK n m :
   (m <= n <= N)%N -> get_next n (get_prev n m) = m.
Proof.
move=> /andP[mLn nLN].
case: get_prev_spec (mLn)=> //; first by rewrite mLn.
  by rewrite get_next_max.
move=> {m mLn}m m1 m1Ln.
case: get_next_spec (m1Ln); first by rewrite m1Ln.
  by move=> _ gaLma _ mLn; have := get_max_max _ _ mLn; lra.
move=> {m1 m1Ln}m1 m2 m2Ln m1aLm2a m2P m1Ln m1aLma m1P mLn.
apply: Ninj=> //; try by rewrite (leq_trans _ nLN).
have m2aLma := m2P _ mLn m1aLma.
suff : ~ `{m2 * a} < `{m * a} by lra.
move=> m2asLma.
suff : `{m2 * a} <= `{m1 * a} by lra.
apply: m1P=> //; lra.
Qed.

Lemma Lget_prev n m : (get_prev n m <= n)%N.
Proof.  rewrite /get_prev; case: get_left_spec=> //= *; apply: Lget_max. Qed.

Lemma sum_get_next n : (n <= N)%N ->
   \big[Rplus/0]_(i < n.+1) (`{(get_next n i)  * a} - `{i * a}) = 0.
Proof.
move=> nLN.
have on (i : 'I_n.+1) : (get_next n i < n.+1)%N by rewrite ltnS Lget_next.
pose f (i : 'I_n.+1) := Ordinal (on i).
have op (i : 'I_n.+1) : (get_prev n i < n.+1)%N by rewrite ltnS Lget_prev.
pose g (i : 'I_n.+1) := Ordinal (op i).
have mO : {morph Ropp : x y / x + y >-> x + y}  by move=> x y /=; lra.
rewrite big_split //= [X in _ + X  = _](reindex f) //=; last first.
  exists g=> /= m _; apply/val_eqP/eqP.
    by apply: get_nextK; rewrite -ltnS // ltn_ord.
  by apply: get_prevK; rewrite -ltnS // ltn_ord.
rewrite -(big_morph _ mO Ropp_0) /=; lra.
Qed.

Lemma sum_min_max n (b := get_min n) (B := get_max n) : 
  (0 < n <= N)%N -> B * `{b * a} +  b * (1 - `{B * a}) = 1.
Proof.
move=> ZLnLN.
have /andP[nP nLN] := ZLnLN; rewrite lt0n in nP.
have : \big[Rplus/0]_(i < n.+1) (`{(get_next n i)  * a} - `{i * a}) = 0.
  have on (i : 'I_n.+1) : (get_next n i < n.+1)%N by rewrite ltnS Lget_next.
  pose f (i : 'I_n.+1) := Ordinal (on i).
  have op (i : 'I_n.+1) : (get_prev n i < n.+1)%N by rewrite ltnS Lget_prev.
  pose g (i : 'I_n.+1) := Ordinal (op i).
  have mO : {morph Ropp : x y / x + y >-> x + y}  by move=> x y /=; lra.
  rewrite big_split //= [X in _ + X  = _](reindex f) //=; last first.
    exists g=> /= m _; apply/val_eqP/eqP.
      by apply: get_nextK; rewrite -ltnS // ltn_ord.
    by apply: get_prevK; rewrite -ltnS // ltn_ord.
  by rewrite -(big_morph _ mO Ropp_0) /=; lra.
pose f i := `{get_next n i  * a} - `{i * a}.
rewrite -[X in X = _](big_mkord xpredT f).
have nbF : (0 <= (n - b).+1)%N by [].
rewrite (big_cat_nat _ _ _ nbF) /=; last by rewrite ltnS leq_subr.
rewrite (eq_big_seq (fun _ => `{b * a})) => [/=|x]; last first.
  rewrite mem_index_iota /f /= ltnS => mLN.
  have xgLn : (x + b <= n)%N.
    by rewrite -[n](subnK (Lget_min n)) leq_add2r.
  have := (get_minD _ _ ZLnLN xgLn).
  by rewrite get_nextDmin -/b //; lra.
rewrite big_const_R subn0. 
have ngLg : (n - b < B)%N.
  rewrite -[B](addnK b) ltn_sub2r //.
    by rewrite -[X in (X < _)%N]add0n ltn_add2r lt0n get_max_NZ.
  by rewrite addnC; apply:  LminDmax.
rewrite (big_cat_nat _ _ _ ngLg) /=; last first.
  by rewrite (leq_trans (Lget_max n)).
rewrite (eq_big_seq (fun _ => `{b * a} + 1 - `{B * a})) => [/=|x]; last first.
  rewrite mem_index_iota /f => ngLxLg.
  by rewrite get_nextDmin_max // get_min_maxD -/b -/B //; lra.
rewrite /= big_const_R big_ltn; last by rewrite ltnS Lget_max.
rewrite (eq_big_seq (fun _ => 1 - `{B * a})) => [/=|x]; last first.
  rewrite mem_index_iota /f /= ltnS => mLN.
  rewrite get_nextDmax //; last by rewrite ltnW; have /andP[] := mLN.
  by rewrite (get_maxD _ _ _ mLN) -/B //; lra.
rewrite big_const_R {}/f get_next_max a0 subSS.
by rewrite !(minus_INR, S_INR) ?Lget_max ?Lget_min; try lra.
Qed.

Corollary csum_min_max  n 
      (b := get_min n) (B := get_max n) (c := `[b * a]) (C := 1 + `[B * a]) :
     (0 < n <= N)%N -> b * C - B * c = 1.
Proof. 
move=> ZLnLN.
by have := sum_min_max _ ZLnLN; rewrite /c /C  /b /B /frac_part; lra.
Qed.

Lemma La_min_max  n 
      (b := get_min n) (B := get_max n) (c := `[b * a]) (C := 1 + `[B * a]) :
     (0 < n <= N)%N -> c / b < a < C / B.
Proof. 
move=> ZLnLN; have /andP[nP nLN] := ZLnLN; rewrite lt0n in nP.
split.
  have bP : 0 < b by apply/lt_0_INR/leP; rewrite lt0n get_min_NZ.
  apply: (Rmult_lt_reg_l b)=> //.
  rewrite -Rmult_assoc [b * _]Rmult_comm Rmult_assoc Rinv_r; try lra.
  have /Ndiff0 : (0 < b <= N)%N.
    by rewrite lt0n get_min_NZ // (leq_trans (Lget_min _)).
  have := frac_bound (b * a); rewrite /c /`{_}; lra.
have BP : 0 < B by apply/lt_0_INR/leP; rewrite lt0n get_max_NZ.
apply: (Rmult_lt_reg_l B)=> //.
rewrite -Rmult_assoc [B * C]Rmult_comm Rmult_assoc Rinv_r; try lra.
have /Ndiff0 : (0 < B <= N)%N.
  by rewrite lt0n get_max_NZ // (leq_trans (Lget_max _)).
by have := frac_bound (B * a); rewrite /C /`{_}; lra.
Qed.

End Paper.

