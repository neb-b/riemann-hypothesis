module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure OrbitChart (P : Ideal (MRing ι)) (e : ℕ) where

  D : Set (Fin e → ℂ)
  isOpen_D : IsOpen D

  φ : (Fin e → ℂ) → (Σ k, ι k) → ℂ
  holo : ∀ p, AnalyticOnNhd ℂ (fun w => φ w p) D
  mem : ∀ w ∈ D, φ w ∈ mcPts P

  O : Set ((Σ k, ι k) → ℂ)
  O_open : ∃ O' : Set ((Σ k, ι k) → ℂ), IsOpen O' ∧ O = O' ∩ mcPts P
  O_orbit : ∀ z ∈ O, ∀ z' ∈ mcPts P, SameOrbit z' z → z' ∈ O

  ρ : ((Σ k, ι k) → ℂ) → Fin e → ℂ
  ρ_cont : ContinuousOn ρ O
  ρ_orbit : ∀ z ∈ O, ∀ z' ∈ O, SameOrbit z' z → ρ z' = ρ z
  φ_mem_O : ∀ w ∈ D, φ w ∈ O
  ρ_φ : ∀ w ∈ D, ρ (φ w) = w
  ρ_mem : ∀ z ∈ O, ρ z ∈ D
  φ_ρ : ∀ z ∈ O, SameOrbit (φ (ρ z)) z
  immersion : ∀ w ∈ D, ∀ p : (k : K) → ι k, (∀ k, φ w ⟨k, p k⟩ ≠ 0) →
    (fderiv ℂ (fun w' => affCoord p (φ w')) w).ker = ⊥

end Orbit

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def stepOf (N j : ℕ) (c : Fin N) : Fin N :=
  ⟨if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j, by
    have := c.2
    split_ifs <;> omega⟩

def lowMat (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then c ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if e : ∃ p, M.blk p = some q.1 then
    ∑ I, valAt M.x (F.u q I) zb * minorIJ (h e.choose.1) I (stepCols N j e.choose.2)
  else zb ⟨⟨q.1, fun p hp => e ⟨p, hp⟩⟩, q.2⟩

def sqZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (k₀ : K) (τ : Ψ) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagZ M F zb h ⟨k, m⟩
  | ⟨none, m⟩ => flagZ M F zb (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩

def pluck (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (k : K)
    (z : (Σ k, ι k) → ℂ) (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * z ⟨k, m⟩

def twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * pluck M F zb k z I

def lowRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ' : Ψ) (a' b' : Fin N) : ℂ :=
  (M.blk (τ', stepOf N j b')).elim 0 fun k =>
    twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b'))

def baseOf (M : FlagModel y Ψ N j) (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (fstPt k₀ z)

abbrev wP (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) :
    Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀))) :=
  mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)

section Param

variable {n e : ℕ} {Λ : Type}

def wB (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def wL (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr (Sum.inl q)))

def wT (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : ℂ := w (ε (Sum.inr (Sum.inr ())))

def wD (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | wB ε w ∈ V}

end Param

variable {n e : ℕ}

def wH (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (w : Fin e → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := h τ' * lowMat (wL ε w) τ'

def wPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (k₀ : K) (τ : Ψ) (ca cb : Fin N)
    (w : Fin e → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ :=
  sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)

def IsBaseChart (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk)
    (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ (Rb.A.chart kb).target ∧ (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
    (∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl w)) V) ∧
    ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, bl w ⟨k, F.c k⟩ = 1) ∧ M.GoodAt F (mCoordIdeal (bl w)) ∧
      SameOrbit (Rb.lift ((Rb.A.chart kb).symm w) ((Rb.A.chart kb).symm w)) (bl w)

def IsWCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N)
    (d : ℕ) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (b : ℕ) = a + 1 ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) ∧ M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧
    (cb : ℕ) = ca + 1 ∧ IsArithVar (mCoordIdeal y) (d + 2) ∧ M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0

def wO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ) :=
  {z | z ∈ mcPts (wP M τ a k₀ ca cb) ∧ r (baseOf M k₀ z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (baseOf M k₀ z)) ∈ V ∧
    (∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0) ∧
    twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0}

def wRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (baseOf M k₀ z)) l
  | Sum.inr (Sum.inl q) => lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2
  | Sum.inr (Sum.inr _) =>
    lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def flagAt {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (ca cb : Fin N) (t : ℂ) (w : Fin d → ℂ)
    (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  if τ' = τ then H τ w * (1 + Matrix.single cb ca t) else H τ' w

def IsFibreData {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N) (ca cb : Fin N)
    {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) : Prop :=
  (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) ∧
    ContinuousOn bp Un ∧ (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) ∧
    (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) ∧
    (∀ w ∈ Un, ∀ r s : Fin 2, Gn w r s =
      minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
          (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
        minorIJ ((H τ w)ᴴ * BM.G l τ (bp w) * H τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) ∧
    (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∀ x₀, FA.Re.π x₀ = ΦYn z → ∃ z₀ : (Σ k, ι k) → ℂ,
      SameOrbit (FA.Re.R.lift x₀ x₀) z₀ ∧ SameOrbit (basePart M.blk z₀) (BM.Rb.lift (bp (Fin.tail z)) (bp (Fin.tail z))) ∧
      ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) z₀ (flagAt H τ ca cb (z 0) (Fin.tail z) τ')) ∧
    ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un →
      q 0 (ΦWn z) = ΦYn (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦWn z) = ΦYn (Fin.tail z)

theorem isFibreChart_iff {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n} (FA : FlagAn BM d) (τ : Ψ) (a : Fin N)
    (ca cb : Fin N) {X : Type} (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ))
    (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) :
    IsFibreChart FA τ a ca cb q Un Gn ΦYn ΦWn ↔ ∃ l H bp, IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp :=
  Iff.rfl

def upsVal {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℂ :=
  valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b)

def upsLogAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X) : ℝ :=
  if M.blk p = none then Real.log ‖upsVal BM l p b‖ else 0

def potAt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X)
    (hf : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  blockPot j p.2 (BM.G l p.1 b) hf - upsLogAt BM l p b

def alphaOf {M : FlagModel y Ψ N j} {n d : ℕ} (BM : BaseMetric M n) (l : Fin BM.q)
    (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X) (p : Ψ × Fin N) (w : Fin d → ℂ) : ℝ :=
  potAt BM l p (bp w) (H p.1 w)

def facOf (N j : ℕ) (a : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
    else minorIJ h (omIdx N j) (omIdx N j)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def IsImg {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (z : (Σ k, ι' k) → ℂ) (w : (Σ k, ι k) → ℂ) : Prop :=
  ∀ z₁, SameOrbit z₁ z → ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z₁ h → ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) ∧
      M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ

theorem IsImg.orbit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {Cv : FlagCover M' M}
    {z z₁ : (Σ k, ι' k) → ℂ} {w w₁ : (Σ k, ι k) → ℂ} (h : IsImg Cv z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : IsImg Cv z₁ w₁ := by
  intro z₂ h2 F' F hF' hF hg' hg hh hfl
  obtain ⟨z₀, a, b, c⟩ := h z₂ (Cj.sameOrbit_trans h2 hz) F' F hF' hF hg' hg hh hfl
  exact ⟨z₀, Cj.sameOrbit_trans a (Cj.sameOrbit_symm hw), b, c⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def xiDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) : K → ℤ := fun k => ∑ p, xiCoef τ a p * M.dy p k

def aDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : Option K → ℤ := fun o =>
  match o with
  | none => 1
  | some k => if k = k₀ then 1 else -xiDeg M τ a k

def potA (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : HermLine fun o : Option K => ι (o.getD k₀) :=
  fsHerm (fun o : Option K => ι (o.getD k₀)) (aDeg M τ a k₀)

def IsPtData (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ (fstPt k₀ (RW.lift x x)) ∧
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) ∧ IsBlockDiag j h ∧ h.det ≠ 0 ∧ t ≠ 0 ∧
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) ∧ ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))

def IsLocSec (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x : RW.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (V : Set RW.X)
    (u : RW.X → ℂ) : Prop :=
  (∃ F H, IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H) ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧
    RW.A.HoloOn V u ∧ (∀ y' ∈ V, u y' ≠ 0) ∧
    (∀ y' ∈ V, ψ y' i₀ = 0 ↔ SameOrbit (fstPt k₀ (RW.lift y' y')) (sndPt k₀ (RW.lift y' y'))) ∧
    ∀ y' ∈ V, ψ y' i₀ ≠ 0 → ∀ z₀ z₁ F h t, IsPtData M τ a k₀ ca cb RW y' z₀ z₁ F h t →
      Real.log ‖u y' * ψ y' i₀‖ - Real.log ((potA M τ a k₀).h (RW.lift x y')) = normRhs M τ a F z₀ z₁ h t

def diagSet (k₀ : K) {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀)))} {e : ℕ} (R : AnLogRes P J e) : Set R.X :=
  {x | SameOrbit (fstPt k₀ (R.lift x x)) (sndPt k₀ (R.lift x x))}

def diagSec {e : ℕ} {X : Type} [TopologicalSpace X] (ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)) (i₀ : X → Fin e)
    (u : X → X → ℂ) : X → X → ℂ := fun x y' => u x y' * ψ x y' (i₀ x)

def secPot {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] {P J : Ideal (MRing ρ)} {e : ℕ}
    (R : AnLogRes P J e) (A : HermLine ρ) (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (c : ℝ) :
    LocPot R.X where
  U := V
  isOpen_U := hV
  mem_U := hm
  φ x y' := Real.log (A.h (R.lift x y')) + c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

noncomputable def scaleT (c : K → ℂ) : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleT_inv_scaleT (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (f : MvPolynomial K ℂ) :
    scaleT (fun k => (c k)⁻¹) (scaleT c f) = f := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact DFunLike.congr_fun h f


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mConeMap_torus (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    mConeMap (fun q : Σ k, ι k => c q.1 * z q) f = scaleT c (mConeMap z f) := by
  have h : mConeMap (fun q : Σ k, ι k => c q.1 * z q) =
      ((scaleT c).restrictScalars ℤ).comp (mConeMap z) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [mConeMap, scaleT, AlgHom.comp_apply, aeval_X, AlgHom.restrictScalars_apply, map_mul,
      algHom_C, algebraMap_eq, mul_assoc]
    rw [mul_left_comm]
  rw [h]
  rfl


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mCoordIdeal_torus (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z := by
  ext f
  rw [mCoordIdeal, mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_torus]
  constructor
  · intro h
    have := congrArg (scaleT fun k => (c k)⁻¹) h
    rwa [scaleT_inv_scaleT c hc, map_zero] at this
  · intro h
    rw [h, map_zero]

theorem isValueAt_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s z v) :
    IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v := by
  obtain ⟨d, g, h, hg, hh, hy, he, h0, rfl⟩ := hv
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, he, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero hu h0
  · rw [eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem isValueAt_of_torus {x : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ} (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) (hv : IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v) :
    IsValueAt x s z v := by
  have h := isValueAt_torus (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hv
  have e : (fun q : Σ k, ι k => (c q.1)⁻¹ * (c q.1 * z q)) = z := by
    funext q
    exact inv_mul_cancel_left₀ (hc q.1) _
  rwa [e] at h

theorem valAt_torus {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : z ∈ mcPts (mCoordIdeal x))
    (hcz : (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x)) (s : Ω) :
    valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z := by
  by_cases h : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := h
    rw [valAt_eq hz hv, valAt_eq hcz (isValueAt_torus c hc hv)]
  · have h' : ¬ ∃ v, IsValueAt x s (fun q : Σ k, ι k => c q.1 * z q) v :=
      fun ⟨v, hv⟩ => h ⟨v, isValueAt_of_torus c hc hv⟩
    rw [valAt, valAt, dite_eq_right h, dite_eq_right h']

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    mCoordIdeal (fun q : Σ k, ι k => c q.1 * z q) = mCoordIdeal z ∧
      (z ∈ mcPts (mCoordIdeal x) → (fun q : Σ k, ι k => c q.1 * z q) ∈ mcPts (mCoordIdeal x) ∧
        ∀ s : Ω, valAt x s (fun q : Σ k, ι k => c q.1 * z q) = valAt x s z) := by
  intro K _ ι _ Ω _ x z c hc
  refine ⟨mCoordIdeal_torus c hc z, fun hz => ?_⟩
  have hcz := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal x) c hc hz
  exact ⟨hcz, valAt_torus c hc hz hcz⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentMulSelM
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot

variable {N : ℕ}

theorem mul_selM_apply {m : Type} (A : Matrix m (Fin N) ℂ) (S : Finset (Fin N)) (a : m) (b : Fin S.card) :
    (A * selM S) a b = A a (S.orderEmbOfFin rfl b) := by
  rw [Matrix.mul_apply]
  simp [selM, Matrix.of_apply]

theorem selM_conjTranspose_mul_mul (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    (selM S)ᴴ * A * selM S = A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl) := by
  ext a b
  rw [mul_selM_apply, Matrix.mul_apply]
  simp [selM, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite]

theorem det_selM (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((selM S)ᴴ * A * selM S).det = minorIJ A S S := by
  rw [selM_conjTranspose_mul_mul, minorIJ, dite_eq_left rfl]

theorem selM_transpose (S : Finset (Fin N)) (b : Fin S.card) :
    (selM S)ᵀ b = Pi.basisFun ℂ (Fin N) (S.orderEmbOfFin rfl b) := by
  ext a
  simp [selM, Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]

theorem linearIndependent_selM (S : Finset (Fin N)) : LinearIndependent ℂ (selM S)ᵀ := by
  have h := (Pi.basisFun ℂ (Fin N)).linearIndependent.comp _ (S.orderEmbOfFin rfl).injective
  have e : (selM S)ᵀ = (Pi.basisFun ℂ (Fin N)) ∘ (S.orderEmbOfFin rfl) := funext fun b => selM_transpose S b
  rw [e]
  exact h

theorem linearIndependent_mul_selM {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    LinearIndependent ℂ (h * selM S)ᵀ := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hi : Function.Injective h.mulVecLin := Matrix.mulVec_injective_of_isUnit hu
  have := (linearIndependent_selM S).map' h.mulVecLin (LinearMap.ker_eq_bot.2 hi)
  have e : (h * selM S)ᵀ = h.mulVecLin ∘ (selM S)ᵀ := by
    funext b
    ext a
    rfl
  rw [e]
  exact this

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (S : Finset (Fin N)) :
    0 < minorIJ G S S := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (S.orderEmbOfFin rfl).injective).det_pos

theorem log_re_mul {a b : ℂ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b).re = Real.log a.re + Real.log b.re := by
  have ha' := Complex.lt_def.1 ha
  have hb' := Complex.lt_def.1 hb
  have hi : a.im = 0 := ha'.2.symm
  rw [Complex.mul_re, hi, zero_mul, sub_zero]
  exact Real.log_mul ha'.1.ne' hb'.1.ne'

theorem gram_mul_selM (G h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((h * selM S)ᴴ * G * (h * selM S)).det = minorIJ (hᴴ * G * h) S S := by
  rw [← det_selM, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blockPot_eq_gram (N j : ℕ) (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    (∀ S : Finset (Fin N), LinearIndependent ℂ (selM S)ᵀ) ∧
    (h.det ≠ 0 → ∀ S : Finset (Fin N), LinearIndependent ℂ (h * selM S)ᵀ) ∧
    (G.PosDef → blockPot j i G h = (1 / 2) * ((if j ≤ (i : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * G * selM (wIdx N j)).det.re else 0) + (if (i : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * G * selM (omIdx N j)).det.re else 0) + (if IsProperStep N j i then Real.log ((h * selM (stepCols N j i))ᴴ * G * (h * selM (stepCols N j i))).det.re else 0))) := by
  refine ⟨linearIndependent_selM, fun hd S => linearIndependent_mul_selM hd S, fun hG => ?_⟩
  simp only [det_selM, gram_mul_selM, blockPot, detFac]
  have hW := minor_pos hG (wIdx N j)
  have hO := minor_pos hG (omIdx N j)
  split_ifs <;>
    simp only [one_mul, mul_one, Complex.one_re, Real.log_one, log_re_mul hW hO] <;> ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot
end
end

