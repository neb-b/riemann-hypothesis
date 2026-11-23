module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit
public import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
public import Formalism.DivisorInequality.BaseLevelBoundsWithCovolume
public import Formalism.DivisorInequality.DivisorInequalityProofs.EvenDegreeWeightBounds
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.BranchSandwichDivisors.StatementR
public import Formalism.BranchSandwichDivisors.StatementL
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Bundle0001
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.PerEmbeddingCoupledBound
public import Formalism.LocalToGlobal.KernelLattices.ThDistC

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
open Formalism.LatticeIndexTer (ph)

section Numbers

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl)

namespace RecNums

theorem x_pos : 0 < R.x := lt_trans zero_lt_one R.p1
theorem L_nonneg : 0 ≤ R.L := by
  rw [R.p3]
  exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one R.p1)) _
theorem b_ge : 1 ≤ R.b := by
  rw [R.p4]
  exact Real.one_le_exp R.L_nonneg
theorem a_ge : 1 ≤ R.a := by
  have h1 := R.p1
  have h2 := R.b_ge
  rw [R.p5]
  nlinarith
theorem La_nonneg : 0 ≤ R.La := by
  have h1 := R.a_ge
  have h2 := R.p6
  rw [R.p9]
  exact Real.log_nonneg (by nlinarith)
theorem Nn_ge : 1 ≤ R.Nn := by
  linarith [R.p1, R.p2, R.p6, R.p11, R.p14, R.p15, R.p16, R.p17, R.p18, R.p19, R.p20, R.p24, R.p25, R.p26, R.p27, R.p28,
    R.p29, R.p30, R.p31, R.p32, R.p33, R.p34, R.p35, R.p36, R.p37, R.p38, R.c1, R.c3, R.c4, R.c5]

theorem La_eq : R.La = Real.log R.x + R.L + Real.log R.rd := by
  have hx : 0 < R.x := R.x_pos
  have hb : 0 < R.b := by rw [R.p4]; exact Real.exp_pos _
  have hrd : 0 < R.rd := by linarith [R.p6]
  rw [R.p9, R.p5, Real.log_mul (mul_pos hx hb).ne' hrd.ne', Real.log_mul hx.ne' hb.ne', R.p4, Real.log_exp]

theorem unit_nonneg : 0 ≤ R.x ^ R.eps * (R.B0 + R.Nc) := by
  have hx : 0 ≤ R.x := le_of_lt R.x_pos
  have hf : 0 ≤ R.f := le_trans (Nat.cast_nonneg _) R.p13
  have hb : 0 ≤ R.b := by linarith [R.b_ge]
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hxe := Real.rpow_nonneg hx R.eps
  apply mul_nonneg hxe
  rw [R.p10]
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hf hm) hb) hxe) R.p11

theorem hu_eq : R.hu = R.hA + ∑ j, R.hB j - ∑ j, R.hX j := by
  show R.hA + ∑ j, (R.hB j - R.hX j) = _
  rw [Finset.sum_sub_distrib]
  ring

def NcF : ℝ := R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2

theorem NcF_nonneg : 0 ≤ R.NcF := by
  show 0 ≤ R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt R.x_pos) _) R.p11) (sq_nonneg _)

theorem NcF_spec : (Real.log R.x) ^ 2 * R.NcF = R.x ^ R.eps * R.Nc := by
  show (Real.log R.x) ^ 2 * (R.x ^ R.eps * R.Nc / (Real.log R.x) ^ 2) = R.x ^ R.eps * R.Nc
  have hl : Real.log R.x ≠ 0 := (Real.log_pos R.p1).ne'
  field_simp

end RecNums

theorem HtNums.le_hu {R : RecNums J Pl} {Emb : Type} [Fintype Emb] [Nonempty Emb] (H : HtNums R Emb) (mlam : ℝ)
    (hm : ∑ j, R.hX j ≤ mlam) :
    H.hPn + ∑ j, (∑ s, H.sz j s) / (Fintype.card Emb : ℝ) - mlam ≤ R.hu :=
  Formalism.DivisorInequality.height_bound_at_set J Pl Emb R.TT R.r R.hu H.hPn mlam R.logT (fun j => (∑ s, H.sz j s) / (Fintype.card Emb : ℝ))
    R.aT R.logH R.Ch R.nV R.Lp R.ν R.x R.eps R.L R.b R.a R.rd R.La R.m R.f R.k R.Nn R.S R.η R.b' R.logOm
    H.g0 H.sz H.MainNotions H.logOmτ H.logth0 H.logh H.logh' H.vv H.logg H.C2 H.Cth H.C4 H.c5 H.c6 H.CT H.C8 H.Ce
    H.ev H.bT H.nτ H.lam1 H.D0 H.D1 H.logc H.logxi H.Cev
    rfl hm (fun _ _ => le_refl _) (fun _ => rfl) H.i1 H.i2 H.i3 H.i4 H.i5 H.i6 H.i7 H.i8 H.i9
    H.i10.1 H.i10.2.1 H.i10.2.2.1 H.i10.2.2.2.1 H.i10.2.2.2.2.1 H.i10.2.2.2.2.2.1 H.i10.2.2.2.2.2.2
    H.t1 H.t2 H.t3 H.t4 H.t5 H.t6 H.t7 H.t8 H.t9 H.t10.1 H.t10.2.1 H.t10.2.2 R.p34 H.t11.1 H.t11.2
    R.p1.le R.p2 R.p3 R.p4 R.p5 R.p6 R.p9 R.p13 R.p14 R.p15 R.p16 R.p17 R.p18 R.p20 H.k1 H.k2 H.k3

theorem RecNums.divIneq (muC mu0 Fo Lpass Eb : ℝ) (hC : muC ≤ mu0 + Lpass)
    (hM : mu0 ≤ (∑ j, ∑ ρ, R.pq j * R.w j ρ * R.logOm) + 2 * Fo + Eb)
    (hpass : Lpass ≤ 1 + R.C0 * (R.m * R.lam0)) (hEb : Eb ≤ R.errB) :
    muC + R.hu - 2 * Fo ≤ R.rhs := by
  have hf : 0 ≤ R.f := by linarith [R.p15]
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hN : 0 ≤ R.Nn := by linarith [R.Nn_ge]
  have hL := R.L_nonneg
  have hLa := R.La_nonneg
  have hη := R.p20
  have hS := R.p18
  have hb' := R.p34
  have hC0 : 0 ≤ R.C0 := by linarith [R.c1]
  have H := Formalism.DivisionValues.divIneqRecord J Pl R.TT muC mu0 Fo R.hu R.hA (∑ j, R.hX j) R.logT
    R.hB R.aT (fun j ρ => ∑ i, ph (R.ν j ρ i)) (fun j ρ => ∑ i, R.ν j ρ i) R.logH R.x R.eps R.L R.b R.a R.rd R.La R.B0 R.NcF
    R.m R.f R.k R.Nn R.S R.tt R.η R.w'' R.b' R.lam0 R.C0 R.ce Lpass Eb
    (R.m * (R.Ch * R.f * R.nV ^ 2 * R.Lp))
    (R.Ch * ((R.TT.card : ℝ) * R.b' * R.Nn + R.f * (R.m * R.η + R.S) * R.Nn + R.f * R.Nn ^ 2) * R.La)
    R.logOm (fun _ => R.Ch * R.f * R.Nn ^ 2 * (R.La + R.m ^ 3 * R.L)) R.pq R.w R.eE R.δ
    hC hM R.hu_eq (fun _ => le_refl _)
    (by
      simp only [RecNums.hX, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12]
      exact le_refl _)
    (le_refl _) R.weight_height_sum_le R.weight_sum_eq R.p1.le R.p2 R.p3 R.p4 R.p5 R.p6 R.p7 R.p8 R.p9 R.p10 R.NcF_nonneg
    R.p12 R.p13 R.p14 R.p15 R.p16 R.Nn_ge R.p18 R.p19 R.p20 R.p21 R.p22 R.p23 R.p24 R.p25 R.p26 R.p27 R.p28 R.p29
    R.p30 R.p31 R.p32 R.p33 R.c1 R.c2 hpass
    (by rw [R.NcF_spec]; have := hEb; unfold RecNums.errB at this; linarith)
    (fun _ => by
      have hX : 0 ≤ R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L := by positivity
      calc R.Ch * R.f * R.Nn ^ 2 * (R.La + R.m ^ 3 * R.L)
          = R.Ch * (R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L) := by ring
        _ ≤ R.C0 * (R.f * R.Nn ^ 2 * R.La + R.f * R.m ^ 3 * R.Nn ^ 2 * R.L) := mul_le_mul_of_nonneg_right R.c4 hX)
    (by
      have h1 : R.nV ^ 2 ≤ R.Nn ^ 2 := pow_le_pow_left₀ R.p36 R.p37 2
      have h2 : 0 ≤ R.Ch * R.Lp := mul_nonneg R.c3 R.p38
      have h3 : R.nV ^ 2 * (R.Ch * R.Lp) ≤ R.Nn ^ 2 * (R.C0 * R.La) :=
        mul_le_mul h1 R.c5 h2 (by positivity)
      have h4 : 0 ≤ R.m * R.f := mul_nonneg hm hf
      calc R.m * (R.Ch * R.f * R.nV ^ 2 * R.Lp) = R.m * R.f * (R.nV ^ 2 * (R.Ch * R.Lp)) := by ring
        _ ≤ R.m * R.f * (R.Nn ^ 2 * (R.C0 * R.La)) := mul_le_mul_of_nonneg_left h3 h4
        _ = R.C0 * R.m * R.f * R.Nn ^ 2 * R.La := by ring)
    (by
      have hY : 0 ≤ (R.TT.card : ℝ) * R.b' * R.Nn + R.f * (R.m * R.η + R.S) * R.Nn + R.f * R.Nn ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R.c4 hY) hLa)
    R.sE R.sδ
  rw [R.NcF_spec] at H
  unfold RecNums.rhs
  have e : R.x ^ R.eps * R.B0 + R.x ^ R.eps * R.Nc = R.x ^ R.eps * (R.B0 + R.Nc) := by ring
  rw [e] at H
  exact H

theorem le_exp_half {t h : ℝ} (H : t ^ 2 ≤ Real.exp h) : t ≤ Real.exp (h / 2) := by
  have he : Real.exp (h / 2) ^ 2 = Real.exp h := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  by_contra hc
  push_neg at hc
  have hp := Real.exp_pos (h / 2)
  nlinarith

theorem log_exp_half_sq (h : ℝ) : Real.log (Real.exp (h / 2) ^ 2) = h := by
  rw [sq, ← Real.exp_add, Real.log_exp]
  ring

end Numbers

section KerChainDefs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def famIpAt (F : Formalism.L2.Col.GFam K) (h : F.Ok) (v : InfinitePlace K) (φ ψ : F.Forms) : ℂ :=
  ∑ b, (F.mem b).ipAt (h b) v (φ b : (F.mem b).D → F.V) (ψ b : (F.mem b).D → F.V)

structure KerChain (K : Type) [Field K] [NumberField K] [StarRing K] where

  n : ℕ

  F : ℕ → Formalism.L2.Col.GFam K

  hF : ∀ j, (F j).Ok

  kk : Formalism.L2.Col.KerFam F

  S : Formalism.L2.Col.GSD K

  hS : S.Ok

  S₁ : Formalism.L2.Col.GSD K

  hS₁ : S₁.Ok

  Y : Formalism.L2.Col.Cpl S

  cp : ∀ b : (F n).β, Formalism.L2.Col.CplKer ((F n).mem b) S S₁ Y

namespace KerChain

variable (Q : KerChain K)

def col : (Q.F 0).Forms →ₗ[K] Q.S₁.EqFun := Formalism.L2.Col.colCpl Q.kk Q.hF Q.n Q.cp Q.hS

def step (j : ℕ) : (Q.F j).Forms →ₗ[K] (Q.F (j + 1)).Forms := Q.kk.step Q.hF j

def cpl : (Q.F Q.n).Forms →ₗ[K] Q.S₁.EqFun :=
  (∑ b : (Q.F Q.n).β, (((Q.cp b).comp Q.hS Q.S.outSec).opOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec) ∘ₗ (LinearMap.proj b))

end KerChain

end KerChainDefs

section OfCol

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu))
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def KerChain.ofCol {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)}
    {hY : YbHyp (R := R) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) : KerChain X.K where
  n := m2
  F := chF W sel mu L u
  hF := hF
  kk := A.kk
  S := midGSD W sel mu L u m2 b
  hS := hF (m2 + 1) b
  S₁ := evGSD W Ch sel mu P u
  hS₁ := hE
  Y := ybCpl W sel mu cst L u m2 b hY
  cp := A.cp

end OfCol

section Comparison₂

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

structure ChainTie {Df : DefSide Bs} {Dc : DefCols Df} {u : Dc.Mem} (ch : ColChain Dc u) (Q : KerChain K) where

  hmm : ch.mm = Q.n + 1

  coF : ∀ i (h : i ≤ Q.n), (Fin (ch.c ⟨i, by omega⟩) → K) →ₗ[K] (Q.F i).Forms

  coL : (Fin (ch.c ⟨Q.n + 1, by omega⟩) → K) →ₗ[K] Q.S₁.EqFun

  metF : ∀ i (h : i ≤ Q.n) (v : InfinitePlace K) (x : Fin (ch.c ⟨i, by omega⟩) → K),
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨i, by omega⟩))) (ch.X ⟨i, by omega⟩) v x ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F i) (Q.hF i) v (coF i h x) (coF i h x)

  metL : ∀ (v : InfinitePlace K) (x : Fin (ch.c ⟨Q.n + 1, by omega⟩) → K),
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨Q.n + 1, by omega⟩))) (ch.X ⟨Q.n + 1, by omega⟩) v x ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (coL x) (coL x)

  kerF : ∀ j (h : j < Q.n) (x : Fin (ch.c ⟨j, by omega⟩) → K),
    coF (j + 1) h ((ch.Kj ⟨j, by omega⟩).mulVec x) = Q.step j (coF j h.le x)

  kerC : ∀ x : Fin (ch.c ⟨Q.n, by omega⟩) → K, coL ((ch.Kj ⟨Q.n, by omega⟩).mulVec x) = Q.cpl (coF Q.n le_rfl x)

variable {Df : DefSide Bs} {Dc : DefCols Df} {u : Dc.Mem} {ch : ColChain Dc u} {Q : KerChain K}

theorem ChainTie.chain (T : ChainTie ch Q) (x : Fin (ch.c 0) → K) :
    T.coL ((chainMat ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩).mulVec x) = Q.col (T.coF 0 (Nat.zero_le _) x) := by
  have e : (chainMat ch.Kj ⟨Q.n + 1, by have := T.hmm; omega⟩).mulVec x =
      (ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec ((chainMat ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec x) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  have aux : ∀ i (h : i ≤ Q.n), T.coF i h
      ((chainMat ch.Kj ⟨i, by have := T.hmm; omega⟩).mulVec x) =
      Q.kk.colTo Q.hF i (T.coF 0 (Nat.zero_le _) x) := by
    intro i
    induction i with
    | zero =>
      intro h
      simp [chainMat, Formalism.L2.Col.KerFam.colTo]
    | succ i ih =>
      intro h
      have hi : i < Q.n := by omega
      have ee : (chainMat ch.Kj ⟨i + 1, by have := T.hmm; omega⟩).mulVec x =
          (ch.Kj ⟨i, by have := T.hmm; omega⟩).mulVec
            ((chainMat ch.Kj ⟨i, by have := T.hmm; omega⟩).mulVec x) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      rw [ee, T.kerF i hi, ih hi.le]
      rfl
  rw [e, T.kerC, aux Q.n le_rfl]
  rfl

theorem ChainTie.step_norm (T : ChainTie ch Q) (j : ℕ) (h : j < Q.n) (v : InfinitePlace K) (x : Fin (ch.c ⟨j, by have := T.hmm; omega⟩) → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨j + 1, by have := T.hmm; omega⟩))) (ch.X ⟨j + 1, by have := T.hmm; omega⟩) v
        ((ch.Kj ⟨j, by have := T.hmm; omega⟩).mulVec x) ^ 2 : ℝ) : ℂ) =
      famIpAt (Q.F (j + 1)) (Q.hF (j + 1)) v (Q.step j (T.coF j h.le x)) (Q.step j (T.coF j h.le x)) := by
  rw [T.metF (j + 1) h v, T.kerF j h x]

theorem ChainTie.cpl_norm (T : ChainTie ch Q) (v : InfinitePlace K) (x : Fin (ch.c ⟨Q.n, by have := T.hmm; omega⟩) → K) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (ch.c ⟨Q.n + 1, by have := T.hmm; omega⟩))) (ch.X ⟨Q.n + 1, by have := T.hmm; omega⟩) v
        ((ch.Kj ⟨Q.n, by have := T.hmm; omega⟩).mulVec x) ^ 2 : ℝ) : ℂ) =
      Q.S₁.ipAt Q.hS₁ v (Q.cpl (T.coF Q.n le_rfl x)) (Q.cpl (T.coF Q.n le_rfl x)) := by
  rw [T.metL v, T.kerC x]

def ChainTie.First (T : ChainTie ch Q) (f : (Fin (ch.c 0) → K) →ₗ[K] (Q.F 0).Forms) : Prop :=
  ∀ x, T.coF 0 (Nat.zero_le _) x = f x


end Comparison₂

section ColFace

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} (W : Wts X Pr.Word Rk) (Ch : Chars X Pr Rk.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr Rk (QE sel (mu : Chr X.F X.E X.K)))

abbrev ramDim (u : Pr.Word) : ℕ := (colGSD W Ch u 0).subD (colOk W Ch hX u 0) (MramV W Ch u)

abbrev ramBas (u : Pr.Word) : Basis (Fin (ramDim W Ch hX u)) X.K (MramV W Ch u) :=
  (colGSD W Ch u 0).subB (colOk W Ch hX u 0) (MramV W Ch u)

def colOfCoord (u : Pr.Word) : (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] MfV W Ch u :=
  (MramV W Ch u).subtype ∘ₗ (ramBas W Ch hX u).equivFun.symm.toLinearMap

def colsIn {m2 : ℕ} {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) (u : Pr.Word) :
    (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] (chF W sel mu L u 0).Forms :=
  startC hL u ∘ₗ colOfCoord W Ch hX u

variable {W Ch sel mu cst L}

def colPerL {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    (u : Pr.Word) {n : ℕ} (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) :
    (evGSD W Ch sel mu P u).EqFun →ₗ[X.K] Module.Dual X.K (Fin n → X.K) :=
  (PtilFF W Ch sel mu P hP u).compl₁₂ (evGSD W Ch sel mu P u).EqFun.subtype
    ((mtildeKGSD W Ch sel mu).EqFun.subtype ∘ₗ (V0X W Ch sel mu Xg P).subtype ∘ₗ ev)

def colPer {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) {n : ℕ}
    (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) :
    (Fin (ramDim W Ch hX u) → X.K) →ₗ[X.K] Module.Dual X.K (Fin n → X.K) :=
  ((BtOf W Ch sel mu P hP Xg u (colC A hF hL)).compl₂ ev) ∘ₗ (ramBas W Ch hX u).equivFun.symm.toLinearMap

theorem colPer_eq {P : LevFam X.E X.K Rk.r Pr.vGs} (hP : (mtildeGSD W Ch sel mu P).Ok) (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {u : Pr.Word} {m2 : ℕ} {b : L.β (m2 + 1)} {hY : YbHyp (R := Rk) sel mu cst L u m2 b} (A : ChKer W Ch sel mu cst L P u m2 b hY)
    (hF : ∀ j, (chF W sel mu L u j).Ok) (hE : (evGSD W Ch sel mu P u).Ok) {G : ChGlob X Rk.m} (hL : L.Ok Ch sel mu cst G m2) {n : ℕ}
    (ev : (Fin n → X.K) →ₗ[X.K] V0X W Ch sel mu Xg P) (φ : Fin (ramDim W Ch hX u) → X.K) (F : Fin n → X.K) :
    colPer hX hP Xg A hF hL ev φ F =
      colPerL hP Xg u ev ((KerChain.ofCol W Ch sel mu cst L A hF hE).col (colsIn W Ch hX sel mu cst L hL u φ)) F := rfl

end ColFace

section ColFaceAll

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}

def colFace (hX : X.Ok) {Bs : DefBase X.K} (Df : DefSide Bs) {P : LevFam X.E X.K Rk.r Pr.vGs} (Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K))
    {m2 : ℕ} {G : ChGlob X Rk.m} (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) G m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (A : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x)) (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P) : DefCols Df where
  Mem := Mem
  a x := ramDim W Ch hX (wd x)
  Xc x := (MramH W Ch hX (wd x)).X
  Pt x t := colPer hX (hP t) Xg (A t x) (hF t x) (hL t) (ev t)

section Face

variable {hX : X.Ok} {Bs : DefBase X.K} {Df : DefSide Bs} {P : LevFam X.E X.K Rk.r Pr.vGs}
  {Xg : Finset (G0 X.E Pr.vGs Rk.r → X.K)} {m2 : ℕ} {G : ChGlob X Rk.m} {mu : Bs.Tup → Tup X.F X.E X.K Sg}
  {cst : ∀ t, LocCst X (rowSG Pr sel (mu t))} {L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))}
  {hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) G m2} {hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok}
  {Mem : Type} {wd : Mem → Pr.Word} {b : ∀ t, Mem → (L t).β (m2 + 1)}
  {hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)}
  {A : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x)}
  {hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok} {ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P}

variable (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) P (wd x)).Ok) {x : Mem}
  {ch : ColChain (colFace hX Df Xg mu cst L hL hP Mem wd b hY A hF ev) x}

abbrev memQ : KerChain X.K :=
  KerChain.ofCol W Ch sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (A Bs.μ0 x) (hF Bs.μ0 x) (hE x)

def FirstCols (T : ChainTie ch (memQ (A := A) (hF := hF) hE (x := x))) : Prop :=
  T.First ((colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (L Bs.μ0) (hL Bs.μ0) (wd x)).comp
    (LinearMap.funLeft X.K X.K (Fin.cast ch.c0.symm)))

end Face

end ColFaceAll

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}

def DivClauses {Pl : Type} [Fintype Pl] [DecidableEq Pl] (P : IndefCore Df0 Df1 Dc Sp N) (R : RecNums Bs.J Pl)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ) : Prop :=
  (∀ φ ∈ shiftLat Nu sg, P.cols.col.B u φ ∈ Formalism.HN.dualLat P.cols.RR) ∧
  (∃ cu : InfinitePlace K → ℝ, (∀ v, 0 < cu v ∧
      Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin P.cols.D)).dualBasis
        (Formalism.HN.dualFrame P.cols.XE) v (P.cols.col.B u) ^ 2 ≤ cu v) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (cu v) = R.hu - meanLog P.cols.κ) ∧
  P.cols.muCC - meanLog P.cols.κ + R.hu - 2 * FoOf P ≤ R.rhs ∧
  Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (shiftLat Nu sg) =
    Formalism.HN.muDef (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) Nu +
      2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (shiftZ sg w : ℝ)

theorem nK_of_cb {m : ℕ} {c : Fin (m + 1) → ℕ} {Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ}
    {Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K} (D : CBData Xc Kj) (B : Fin m → InfinitePlace K → ℝ)
    (hB : ∀ j v, Real.log (D.sq j v) ≤ B j v) (j : Fin m) (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v
      (Matrix.mulVecLin (Kj j)) ^ 2 ≤ Real.exp (B j v) := by
  have H := Formalism.DimensionVariation.chain_coupled_bound K m c Xc Kj D.AA D.Cl D.W D.γ D.Φ D.ε D.T D.hcl D.tmax D.hyp
    (fun j v => Real.sqrt (D.sq j v)) (fun _ _ => rfl)
  have h1 := H.1 j v
  have h2 : Real.sqrt (D.sq j v) ^ 2 = D.sq j v := H.2.1 j v
  have h0 := OperatorNormFrames.opNormAt_nonneg (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ)))
    (Xc j.succ) v (Matrix.mulVecLin (Kj j))
  have h3 : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v
      (Matrix.mulVecLin (Kj j)) ^ 2 ≤ D.sq j v := by
    rw [← h2]; exact pow_le_pow_left₀ h0 h1 2
  rcases le_or_gt (D.sq j v) 0 with hs | hs
  · exact h3.trans (hs.trans (Real.exp_pos _).le)
  · calc _ ≤ D.sq j v := h3
      _ = Real.exp (Real.log (D.sq j v)) := (Real.exp_log hs).symm
      _ ≤ Real.exp (B j v) := Real.exp_le_exp.2 (hB j v)

theorem exists_cu {ι : Type} [Fintype ι] [Nonempty ι] (x a : ι → ℝ) (t : ℝ) (hx : ∀ v, 0 ≤ x v)
    (ha : ∀ v, x v = 0 ∨ Real.log (x v ^ 2) ≤ a v) (hm : (1 / (Fintype.card ι : ℝ)) * ∑ v, a v ≤ t) :
    ∃ cu : ι → ℝ, (∀ v, 0 < cu v ∧ x v ^ 2 ≤ cu v) ∧ (1 / (Fintype.card ι : ℝ)) * ∑ v, Real.log (cu v) = t := by
  refine ⟨fun v => Real.exp (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w)), fun v => ⟨Real.exp_pos _, ?_⟩, ?_⟩
  · by_cases h0 : x v = 0
    · rw [h0]
      nlinarith [Real.exp_pos (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w))]
    · have hl := (ha v).resolve_left h0
      have hpos : 0 < x v ^ 2 := pow_pos (lt_of_le_of_ne (hx v) (Ne.symm h0)) 2
      calc x v ^ 2 = Real.exp (Real.log (x v ^ 2)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (a v + (t - (1 / (Fintype.card ι : ℝ)) * ∑ w, a w)) := Real.exp_le_exp.mpr (by linarith)
  · have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Real.log_exp]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

theorem complex_height_cast_at (hH : HeightBoundConstant) {K : Type} [Field K] [NumberField K] [StarRing K] {a n dQ D m : ℕ}
    (c : Fin (m + 1) → ℕ) (c0 : c 0 = a) (hd : dQ = D)
    (Xa : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (hXc : ∀ i v, IsUnit (Xc i v).det)
    (hXz : ∀ v i j, Xc 0 v i j = Xa v (Fin.cast c0 i) (Fin.cast c0 j))
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding)
    (P : Matrix (Fin dQ) (Fin n) K) (hP : Function.Surjective P.mulVec)
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (hXQ : IsQuotMetric P H XQ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXE : ∀ v, IsUnit (XE v).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (Ix J : Type) [Fintype Ix] [Nonempty Ix] [Fintype J] (Qp : Ix → Submodule K (Fin dQ → K)) (hQp : (⨆ p, Qp p) = ⊤)
    (κ : InfinitePlace K → ℝ) (lam : J → Ix → InfinitePlace K → ℝ) (hκ : ∀ v, 0 < κ v) (hlam : ∀ j p v, 0 < lam j p v)
    (hsc : ∀ v p, IsScalarOn XQ XE v ι (Qp p) (κ v * ∏ j, lam j p v))
    (Pt : (Fin (c (Fin.last m)) → K) →ₗ[K] Module.Dual K (Fin n → K))
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (hB : ∀ φ F, B φ (ι.mulVec (P.mulVec F)) = Pt ((chainMat Kj (Fin.last m)).mulVec fun i => φ (Fin.cast c0 i)) F)
    (hne : B ≠ 0) (pU : InfinitePlace K → ℝ) (kU : Fin m → InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m))
      (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v Pt ≤ pU v)
    (hkU : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v) (v : InfinitePlace K) :
    Real.log (Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) Xa (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) v B ^ 2) ≤
      Real.log (pU v ^ 2) + ∑ j, Real.log (kU j v ^ 2) - Real.log (κ v) - minOver (fun p => ∑ j, Real.log (lam j p v)) := by
  subst c0 hd
  obtain rfl : Xc 0 = Xa := by
    funext v; ext i j; simpa using hXz v i j
  exact (hH K n dQ m c Xc hXc Kj H X0 hX0 P hP XQ hXQ XE hXE ι (isUnit_det_of_bij _ hι) Ix J Qp hQp κ lam lam hκ hlam
    (fun _ _ _ => le_rfl) hsc Pt B (by simpa using hB) hne pU kU hpU hkU).1 v

theorem nonempty_Ix {Df : DefSide Bs} (wf : Df.WF) (hpos : Df.Pos) : Nonempty Bs.Ix := by
  by_contra h
  rw [not_nonempty_iff] at h
  have ht := wf.Qp_top
  rw [iSup_of_empty] at ht
  have : Nonempty (Fin (Df.dQ Bs.μ0)) := ⟨⟨0, hpos⟩⟩
  exact bot_ne_top ht

theorem errB_of_units {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Z : IndefScale Bs) (C CH : ℝ) (R : RecNums Bs.J Pl)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (c3 cG c2 cE : ℝ) (hC : 0 ≤ C)
    (hE1 : Z.E1u ≤ R.x ^ R.eps * (R.B0 + R.Nc)) (hl3 : C * Z.l3u ≤ c3 * (R.x ^ R.eps * (R.B0 + R.Nc)))
    (hLG : LG ≤ cG * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc)))) (hE2 : ∀ j, E2 j ≤ c2 * (R.x ^ R.eps * (R.B0 + R.Nc)))
    (hE3 : E3 ≤ cE * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc)))) (hce : c3 + cG + C + c2 + cE ≤ R.ce) :
    R.m * (C * Z.l3u) + LG + (∑ j, ((Z.num C CH).E1 j + E2 j)) + E3 ≤ R.errB := by
  have hU := R.unit_nonneg
  have hm : 0 ≤ R.m := by linarith [R.p14]
  have hmU : 0 ≤ R.m * (R.x ^ R.eps * (R.B0 + R.Nc)) := mul_nonneg hm hU
  show R.m * (C * Z.l3u) + LG + (∑ j, (C * Z.E1u + E2 j)) + E3 ≤ R.ce * R.m * (R.x ^ R.eps * (R.B0 + R.Nc))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12]
  have hE2s : ∑ j, E2 j ≤ ∑ _j : Bs.J, c2 * (R.x ^ R.eps * (R.B0 + R.Nc)) := Finset.sum_le_sum fun j _ => hE2 j
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, R.p12] at hE2s
  have a1 : R.m * (C * Z.l3u) ≤ R.m * (c3 * (R.x ^ R.eps * (R.B0 + R.Nc))) := mul_le_mul_of_nonneg_left hl3 hm
  have a2 : R.m * (C * Z.E1u) ≤ R.m * (C * (R.x ^ R.eps * (R.B0 + R.Nc))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE1 hC) hm
  have a3 : (c3 + cG + C + c2 + cE) * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))) ≤
      R.ce * (R.m * (R.x ^ R.eps * (R.B0 + R.Nc))) :=
    mul_le_mul_of_nonneg_right hce hmU
  linarith

end Generic

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def faceOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : DefSub A.fam.amb → DefFace A.fam.base :=
  fun Zs => ⟨A.side P0 ψ0 Zs, A.side P1 ψ1 Zs, Dc Zs, Sp Zs, Zsc Zs⟩

end Concrete

section ConcreteCol

open Formalism.BasicNotions Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {Rk : Ranks} {W : Wts X Pr.Word Rk} {Ch : Chars X Pr Rk.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

abbrev kerRec {Bs : DefBase X.K} {P : LevFam X.E X.K Rk.r Pr.vGs} {m2 : ℕ} (mu : Bs.Tup → Tup X.F X.E X.K Sg)
    (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (L : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))) {Mem : Type}
    (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1)) (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Am : Formalism.L2.Ker.Amb X) (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P) :
    ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x) :=
  fun t x => Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x)


end ConcreteCol

end Formalism.L2.DIV

namespace Formalism.L2.DIV.Inst

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Examples₂ Formalism.L2.DIV
open Formalism.LatticeIndexTer (ph)





def kk : Fin 2 → K3 := ![2, 2⁻¹]

end Formalism.L2.DIV.Inst
