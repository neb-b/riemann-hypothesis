module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecond
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem gramPlane_posDef : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp _ hF w hw
  unfold IsFibreData at hF
  obtain ⟨-, -, -, h4, h5, -, -⟩ := hF
  obtain ⟨hbp, hH⟩ := h4 w hw
  obtain ⟨hGbd, hGpd⟩ := BM.G_pos l τ (bp w) hbp
  obtain ⟨G₂, hG₂, hG₂eq, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.norm_three_steps N j a b ca cb (BM.G l τ (bp w)) (H τ w)
    M.j_le hb hab hca hcb hGbd hGpd (hH τ).1 (hH τ).2
  have hEq : Gn w = G₂ := Matrix.ext fun r s => by rw [h5 w hw r s, hG₂eq r s]
  rw [hEq]
  exact hG₂

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

section Cell

variable {Ψ : Type} {N j : ℕ}

def Sep (keep : Ψ × Fin N → Prop) (q : LowIdx Ψ N j) : Prop :=
  ∃ i, keep (q.1.1, i) ∧ IsProperStep N j i ∧ q.1.2.2 ∈ stepCols N j i ∧ q.1.2.1 ∉ stepCols N j i

abbrev PIdx (j : ℕ) (keep : Ψ × Fin N → Prop) : Type := {q : LowIdx Ψ N j // Sep keep q}

def cExt (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) : LowIdx Ψ N j → ℂ :=
  fun q => if h : Sep keep q then c ⟨q, h⟩ else 0

def pMat (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  lowMat (cExt keep c) τ

def pSteps (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i

def pStep (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Fin N :=
  if h : (pSteps j keep τ b).Nonempty then (pSteps j keep τ b).min' h else b

def pSgn (S : Finset (Fin N)) (a b : Fin N) : ℂ :=
  minorIJ (1 + Matrix.single a b (1 : ℂ)) (insert a (S.erase b)) S

end Cell

section Param

variable {n e : ℕ} {Λ : Type}

def pB (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def pL (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr q))

def pD (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | pB ε w ∈ V}

end Param

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {n e : ℕ}

def upV (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => if h : ∃ q', v q' = q then z h.choose else 0

def pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (upV v z)

def pRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ : Ψ) (a b : Fin N) : ℂ :=
  (M.blk (τ, pStep j keep τ b)).elim 0 fun k =>
    twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (insert a ((stepCols N j (pStep j keep τ b)).erase b)) /
      (pSgn (stepCols N j (pStep j keep τ b)) a b *
        twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (stepCols N j (pStep j keep τ b)))

def pH (keep : Ψ × Fin N → Prop) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ)
    (w : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ := h τ * pMat keep (pL ε w) τ

def pPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (w : Fin e → ℂ) : (Σ k, ιk k) → ℂ :=
  fun q => flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) (v q)

def IsPCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsBlockMap κ v ∧ (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) ∧
    M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0

def pO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Set ((Σ k, ιk k) → ℂ) :=
  {z | z ∈ mcPts (mCoordIdeal (y ∘ v)) ∧ r (pBase M v z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (pBase M v z)) ∈ V ∧
    ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0}

def pRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n)
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (z : (Σ k, ιk k) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (pBase M v z)) l
  | Sum.inr q => pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2

theorem upV_apply {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : Function.Injective v) (z : (Σ k, ιk k) → ℂ) (q : Σ k, ιk k) :
    upV v z (v q) = z q := by
  have h : ∃ q', v q' = v q := ⟨q, rfl⟩
  simp only [upV, dif_pos h]
  rw [hv h.choose_spec]

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem sameOrbit_symm' {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  rw [inv_mul_cancel_left₀ (hc p.1)]

theorem isValueAt_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ} (h : SameOrbit z z')
    (hv : IsValueAt x s z' v) : IsValueAt x s z v := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := hv
  have hprod : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog f d hf c]
    exact mul_ne_zero hprod hz0
  · rw [eval_smul_homog g d hg c, eval_smul_homog f d hf c, mul_div_mul_left _ _ hprod]

theorem valAt_eq_of_sameOrbit (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z z' : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal x))
    (h : SameOrbit z z') : valAt x s z = valAt x s z' := by
  have hz' : z' ∈ mcPts (mCoordIdeal x) :=
    mem_mcPts_of_sameOrbit (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x)
      (sameOrbit_symm' h) hz
  by_cases hv : ∃ v, IsValueAt x s z v
  · obtain ⟨v, hv⟩ := hv
    rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_sameOrbit (sameOrbit_symm' h) hv)]
  · have hv' : ¬ ∃ v, IsValueAt x s z' v := fun ⟨v, hw⟩ => hv ⟨v, isValueAt_of_sameOrbit h hw⟩
    rw [valAt, valAt, dite_eq_right hv, dite_eq_right hv']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueNeZeroOfRegularUnit
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe

private theorem mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {F : Type} [Field F]
    (w : (Σ k, ι k) → F) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap w h = MvPolynomial.C (MvPolynomial.aeval w h) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
  have key : ∀ m ∈ h.support, (∏ p : (Σ k, ι k), (MvPolynomial.C (w p) * MvPolynomial.X p.1 : MvPolynomial K F) ^ m p)
      = MvPolynomial.C (∏ p, w p ^ m p) * ∏ k, (MvPolynomial.X k : MvPolynomial K F) ^ d k := by
    intro m hm
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    · rw [map_prod]
      simp only [map_pow]
    · rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hh m hm k]
  simp only [mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [key m hm, map_mul, ← mul_assoc]
  congr 2

private theorem aeval_eq_eval_map_intCast {K : Type} {ι : K → Type} (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    MvPolynomial.aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem exists_isValueAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {t : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    (ht : RegAt x (mCoordIdeal z) t) : ∃ v, IsValueAt x t z v := by
  obtain ⟨d, g, h, hg, hh, hQ, he⟩ := ht
  have hz0 : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hQ
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog z hh, aeval_eq_eval_map_intCast, h0, map_zero, zero_mul]
  have hx0 : MvPolynomial.aeval x h ≠ 0 := by
    intro h0
    apply hz0
    exact hz.2 h (by rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_C_aeval_mul_prod_X_pow_of_multiHomog x hh, h0, map_zero, zero_mul])
  refine ⟨MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) /
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) h), ?_⟩
  unfold IsValueAt
  exact ⟨d, g, h, hg, hh, hx0, he, hz0, rfl⟩

theorem valAt_ne_zero_of_regAt_inv : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal x) → s ≠ 0 →
    RegAt x (mCoordIdeal z) s → RegAt x (mCoordIdeal z) s⁻¹ → valAt x s z ≠ 0 := by
  intro K _ ι _ Ω _ x s z hz hs h1 h2
  obtain ⟨v, hv⟩ := exists_isValueAt_of_regAt hz h1
  obtain ⟨w, hw⟩ := exists_isValueAt_of_regAt hz h2
  have hvw := isValueAt_mul hv hw
  rw [mul_inv_cancel₀ hs] at hvw
  have hone : IsValueAt x 1 z 1 := by
    unfold IsValueAt
    exact ⟨0, MvPolynomial.C 1, MvPolynomial.C 1, isMultiHomog_C_zero 1, isMultiHomog_C_zero 1,
      by simp, by simp, by simp, by simp⟩
  have h11 := isValueAt_unique hz hvw hone
  rw [valAt_eq hz hv]
  intro hv0
  rw [hv0, zero_mul] at h11
  exact zero_ne_one h11

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ValNe
end
end

