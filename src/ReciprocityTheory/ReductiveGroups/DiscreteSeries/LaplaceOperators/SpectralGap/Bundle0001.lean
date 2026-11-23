module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapNum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.JSIntFin

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.BesselIntegralSquareIntegrable
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def SigZeroStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (h : ℝ), NonvanishingHypotheses k r z c u v b h →
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ₀ : Mat k r → (H →L[ℂ] H)),
    Formalism.MainNotions.S.IsDSHpk k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ₀ ∧
    Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ₀ ∧
    ∀ w₀ : H, Formalism.MainNotions.S.IsLowUnitH k r (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ₀ w₀ →
      (∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
        ∃ d : ℝ, S0.IsFdegB μG σ₀ d) ∧
      (∃ a C : ℝ, 4 * max (S0.bG k r) (S0.bS k r) < a - 1 ∧
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪w₀, σ₀ g w₀⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN g ^ (-a)) ∧
      ∃ (T : S7.KType (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b)))
        (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r) (v₁ : T.V) (c₁ : ℂ),
        v₁ ≠ 0 ∧ c₁ ≠ 0 ∧ S7.IsMu (Formalism.MainNotions.CayleySignature.lam48 k r v b) μ ∧
        Formalism.MainNotions.S.IsCayley k r (Formalism.MainNotions.CayleySignature.eps48 k r) P ∧
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ⟪w₀, σ₀ g w₀⟫_ℂ = c₁ * psiCoef T μ P v₁ v₁ g

def HCTypeWURepStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] (π : Mat k r → (Vp →L[ℂ] Vp)),
    Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π →
    Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UWset k r z) π

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA
section
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

variable {n : ℕ} {ε : Fin n → Bool}

lemma kset_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε) :
    a * b ∈ Formalism.REAL.Kset ε := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at ha hb ⊢
  refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
  rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]

lemma uj_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) :
    a * b ∈ Formalism.MainNotions.S.UJset ε := by
  simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_setOf_eq] at ha hb ⊢
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

lemma kset_uj {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ Formalism.MainNotions.S.UJset ε := by
  simp only [Formalism.REAL.Kset, Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  have h1 : gᴴ * g = 1 := by
    have h2 := Matrix.mem_unitaryGroup_iff'.mp hu
    simpa [Matrix.star_eq_conjTranspose] using h2
  rw [mul_assoc, ← hc, ← mul_assoc, h1, one_mul]

lemma conj_back {a b g : Matrix (Fin n) (Fin n) ℂ} (hba : b * a = 1) : b * (a * g * b) * a = g := by
  calc b * (a * g * b) * a = (b * a) * g * (b * a) := by simp only [mul_assoc]
    _ = g := by rw [hba, one_mul, mul_one]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Conj

variable (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {a b : Matrix (Fin n) (Fin n) ℂ}
  (hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ₁)
  (hab : a * b = 1) (hba : b * a = 1) (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε)

include hrep hab ha hb in
lemma ab_cancel (x : H) : σ₁ a (σ₁ b x) = x := by
  have h := hrep.1.2 a (kset_uj ha) b (kset_uj hb)
  rw [hab, hrep.1.1] at h
  rw [← ContinuousLinearMap.comp_apply, ← h, ContinuousLinearMap.one_apply]


include hrep ha hb in
lemma conj_apply {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) (x : H) :
    σ₁ (b * g * a) x = σ₁ b (σ₁ g (σ₁ a x)) := by
  have hb' := kset_uj hb
  have ha' := kset_uj ha
  rw [hrep.1.2 _ (uj_mul hb' hg) _ ha', hrep.1.2 _ hb' _ hg]
  simp only [ContinuousLinearMap.comp_apply]

include hrep hab ha hb in
lemma inner_b (w y : H) : ⟪w, σ₁ b y⟫_ℂ = ⟪σ₁ a w, y⟫_ℂ := by
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ₁ a : H →ₗ[ℂ] H), norm_map' := hrep.2.1 a (kset_uj ha) }
  have key : ⟪σ₁ a w, σ₁ a (σ₁ b y)⟫_ℂ = ⟪w, σ₁ b y⟫_ℂ := f.inner_map_map w (σ₁ b y)
  rw [ab_cancel σ₁ hrep hab ha hb y] at key
  exact key.symm

end Conj

end ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {a b : Matrix (Fin n) (Fin n) ℂ}
  (hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ₁)
  (hab : a * b = 1) (hba : b * a = 1) (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε)

include hrep hab hba ha hb in
lemma urep_conj : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (fun g => σ₁ (b * g * a)) := by
  have ha' := kset_uj ha
  have hb' := kset_uj hb
  have hmem : ∀ g ∈ Formalism.MainNotions.S.UJset ε, b * g * a ∈ Formalism.MainNotions.S.UJset ε :=
    fun g hg => uj_mul (uj_mul hb' hg) ha'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show σ₁ (b * 1 * a) = 1
    rw [mul_one, hba, hrep.1.1]
  · intro g hg h hh
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [conj_apply σ₁ hrep ha hb (uj_mul hg hh), conj_apply σ₁ hrep ha hb hg,
      conj_apply σ₁ hrep ha hb hh, ab_cancel σ₁ hrep hab ha hb, hrep.1.2 _ hg _ hh,
      ContinuousLinearMap.comp_apply]
  · intro g hg v
    exact hrep.2.1 _ (hmem g hg) v
  · intro v
    have hc : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => b * g * a) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hrep.2.2 v).comp hc.continuousOn hmem

include hab hba ha hb in
lemma irred_conj (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ₁) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (fun g => σ₁ (b * g * a)) := by
  intro S hS hinv
  apply hirr S hS
  intro g hg v hv
  have hm : a * g * b ∈ Formalism.MainNotions.S.UJset ε := uj_mul (uj_mul (kset_uj ha) hg) (kset_uj hb)
  have h1 : σ₁ (b * (a * g * b) * a) v ∈ S := hinv (a * g * b) hm v hv
  rwa [conj_back hba] at h1

include hrep hab ha hb in
lemma coef_conj (v w : H) :
    Formalism.MainNotions.S.coefOn (ε := ε) (fun g => σ₁ (b * g * a)) v w = Formalism.MainNotions.S.coefOn (ε := ε) σ₁ (σ₁ a v) (σ₁ a w) := by
  funext g
  have hg : Formalism.MainNotions.S.umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
  simp only [Formalism.MainNotions.S.coefOn]
  rw [conj_apply σ₁ hrep ha hb hg, inner_b σ₁ hrep hab ha hb]

include hrep hab ha hb in
lemma sqint_conj (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ₁) : Formalism.MainNotions.S.IsSqIntOn ε (fun g => σ₁ (b * g * a)) := by
  intro v w
  rw [coef_conj σ₁ hrep hab ha hb v w]
  exact hsq (σ₁ a v) (σ₁ a w)

include ha hb in
lemma isKStable_biTranslate_of_isKStable {S : Submodule ℂ H} (h : Formalism.MainNotions.S.IsKStableOn ε σ₁ S) :
    Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) S := by
  intro g hg v hv
  exact h _ (kset_mul (kset_mul hb hg) ha) v hv

include hba ha hb in
lemma isKStable_of_isKStable_biTranslate {S : Submodule ℂ H} (h : Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) S) :
    Formalism.MainNotions.S.IsKStableOn ε σ₁ S := by
  intro g hg v hv
  have h1 : σ₁ (b * (a * g * b) * a) v ∈ S := h (a * g * b) (kset_mul (kset_mul ha hg) hb) v hv
  rwa [conj_back hba] at h1

include hrep hab ha hb in
lemma wt12 {μ : Fin n → ℝ} {v : H} (h : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ v) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (fun g => σ₁ (b * g * a)) μ (σ₁ b v) := by
  intro θ hθ
  have e := conj_apply σ₁ hrep ha hb (kset_uj hθ) (σ₁ b v)
  rw [ab_cancel σ₁ hrep hab ha hb, h θ hθ, map_smul] at e
  exact e

include hrep hab ha hb in
lemma wt21 {μ : Fin n → ℝ} {v : H} (h : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (fun g => σ₁ (b * g * a)) μ v) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ (σ₁ a v) := by
  intro θ hθ
  have e := congrArg (fun y => σ₁ a y) ((conj_apply σ₁ hrep ha hb (kset_uj hθ) v).symm.trans (h θ hθ))
  rw [ab_cancel σ₁ hrep hab ha hb, map_smul] at e
  exact e

include hrep ha in
lemma ne_a {v : H} (hv : v ≠ 0) : σ₁ a v ≠ 0 := by
  intro h0
  apply hv
  have h1 := hrep.2.1 a (kset_uj ha) v
  rw [h0, norm_zero] at h1
  exact norm_eq_zero.mp h1.symm

include hrep hab hba ha hb in
lemma ktype_iff (μ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε (fun g => σ₁ (b * g * a)) μ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S := by
  have hst : ∀ T : Submodule ℂ H, Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) T ↔
      Formalism.MainNotions.S.IsKStableOn ε σ₁ T :=
    fun T => ⟨isKStable_of_isKStable_biTranslate σ₁ hba ha hb, isKStable_biTranslate_of_isKStable σ₁ ha hb⟩
  constructor
  · rintro ⟨hfd, hs, hmin, ⟨v, hvS, hv0, hwt⟩, hdom⟩
    have hs' := (hst S).1 hs
    refine ⟨hfd, hs', fun S' hS' hst' => hmin S' hS' ((hst S').2 hst'),
      ⟨σ₁ a v, hs' a ha v hvS, ne_a σ₁ hrep ha hv0, wt21 σ₁ hrep hab ha hb hwt⟩, ?_⟩
    intro μ' u huS hu0 hwu
    exact hdom μ' (σ₁ b u) (hs' b hb u huS) (ne_a σ₁ hrep hb hu0) (wt12 σ₁ hrep hab ha hb hwu)
  · rintro ⟨hfd, hs, hmin, ⟨v, hvS, hv0, hwt⟩, hdom⟩
    refine ⟨hfd, (hst S).2 hs, fun S' hS' hst' => hmin S' hS' ((hst S').1 hst'),
      ⟨σ₁ b v, hs b hb v hvS, ne_a σ₁ hrep hb hv0, wt12 σ₁ hrep hab ha hb hwt⟩, ?_⟩
    intro μ' u huS hu0 hwu
    exact hdom μ' (σ₁ a u) (hs a ha u huS) (ne_a σ₁ hrep ha hu0) (wt21 σ₁ hrep hab ha hb hwu)


end ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

def ClosedSubgroupsStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UH (Hpk k r)) ∧
      Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Nset k r) ∧
      (inWb k r z → 0 < Tz k r z →
        Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (UWset k r z) ∧
          Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) (Sset k r z))

def HaarUniq2Statement : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ ν : Measure (Mt k r)),
    Formalism.FourierDecayAlt.B2.IsClosedSubgroup (k := k) (r := r) U →
    Formalism.MainNotions.S.IsHaarOn U μ → Formalism.MainNotions.S.IsHaarOn U ν → ∃ c : ℝ≥0, 0 < c ∧ ν = c • μ

def HaarMapStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), Formalism.MainNotions.S.IsCayley k r ε P →
    Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r))
      ((Formalism.REAL.muG ε).map (fun g : Formalism.REAL.UJ ε => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)))

def SchurBStatement : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H))
    (μG : Measure (Mt k r)),
    Formalism.MainNotions.S.IsDSHpk k r ε lam σ → Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG →
    Formalism.MainNotions.S.IsURepOn (UH (Hpk k r)) σ ∧ ∃ d : ℝ, S0.IsFdegB μG σ d

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem parabolicSign_false_iff (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + k + 1)) :
    Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ k ≤ i.val ∧ (i.val - k) % 2 = 0 := by
  unfold Formalism.MainNotions.CayleySignature.eps48
  split_ifs with h1
  · simp; omega
  · simp; omega

theorem noncompactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) : qOf (Formalism.MainNotions.CayleySignature.eps48 k r) = r + 1 := by
  unfold qOf
  have hs : (Finset.univ.filter fun a : Fin (2 * r + k + 1) => Formalism.MainNotions.CayleySignature.eps48 k r a = false) =
      Finset.univ.image (fun j : Fin (r + 1) => (⟨k + 2 * j.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, parabolicSign_false_iff k r hk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(i.val - k) / 2, by omega⟩, ?_⟩
      ext; simp only; omega
    · rintro ⟨j, rfl⟩
      simp only
      omega
  rw [hs, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    ext; omega

theorem compactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    pOf (Formalism.MainNotions.CayleySignature.eps48 k r) = 2 * r + k + 1 - (r + 1) := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * r + k + 1))))
    (fun a => Formalism.MainNotions.CayleySignature.eps48 k r a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  have hq := noncompactCount_parabolicSign k r hk
  unfold qOf at hq
  unfold pOf
  omega

theorem gapBound_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) = hNum (2 * r + k + 1) (r + 1) := by
  unfold hNeed hNum
  rw [compactCount_parabolicSign k r hk, noncompactCount_parabolicSign k r hk]
  simp only [Nat.cast_min]

theorem parabolicWeight_sub_succ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k)
    (y : Fin (2 * r + k + 1)) (hy : k ≤ y.val) :
    Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ - Formalism.MainNotions.CayleySignature.lam48 k r v b y =
      b ⟨y.val - k + 1, by omega⟩ - b ⟨y.val - k, by omega⟩ := by
  unfold Formalism.MainNotions.CayleySignature.lam48
  rw [dite_eq_right (by simp only; omega), dite_eq_right (by omega)]
  have e1 : b ⟨y.val - 1 - (k - 1), by omega⟩ = b ⟨y.val - k, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  have e2 : b ⟨y.val - (k - 1), by omega⟩ = b ⟨y.val - k + 1, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  simp only at e1 e2 ⊢
  rw [e1, e2]; ring

theorem gapAtLeast_parabolicWeight (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k) (h : ℝ)
    (hanti : StrictAnti (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b) :
    GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h := by
  have key : ∀ x y : Fin (2 * r + k + 1), x < y →
      Formalism.MainNotions.CayleySignature.eps48 k r x ≠ Formalism.MainNotions.CayleySignature.eps48 k r y →
      h ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x - Formalism.MainNotions.CayleySignature.lam48 k r v b y := by
    intro x y hxy hne
    have hy : k ≤ y.val := by
      by_contra hcon
      apply hne
      have hx : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r x = false) := by
        rw [parabolicSign_false_iff k r hk]; have := Fin.lt_def.mp hxy; omega
      have hy' : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r y = false) := by
        rw [parabolicSign_false_iff k r hk]; omega
      simp only [Bool.not_eq_false] at hx hy'
      rw [hx, hy']
    have hst := parabolicWeight_sub_succ k r v b hk y hy
    have hle : Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x :=
      hanti.antitone (show x ≤ (⟨y.val - 1, by omega⟩ : Fin (2 * r + k + 1)) from by
        rw [Fin.le_def]; have := Fin.lt_def.mp hxy; simp only; omega)
    have hl := hlow ⟨y.val - k, by omega⟩ (by simp only; omega)
    simp only at hl
    linarith
  intro a a' hne
  rcases lt_trichotomy a a' with h1 | h1 | h1
  · exact le_trans (key a a' h1 hne) (le_abs_self _)
  · exact absurd (h1 ▸ rfl) hne
  · rw [abs_sub_comm]; exact le_trans (key a' a h1 (Ne.symm hne)) (le_abs_self _)

theorem gapBig_gapLap : GapBigLapStatement := by
  intro k r z c u v b hS
  obtain ⟨hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, t, ht, htn, ht1801, hgap⟩ := hS
  let g : Fin (2 * r + 1) → ℝ := fun j => b ⟨j.val + 1, by omega⟩ - b ⟨j.val, by omega⟩
  let h : ℝ := Finset.univ.inf' Finset.univ_nonempty g
  have hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b := by
    intro j hj
    exact Finset.inf'_le g (Finset.mem_univ (⟨j.val, by omega⟩ : Fin (2 * r + 1)))
  have hX : 2 * ((Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < h := by
    rw [Finset.lt_inf'_iff]
    intro j _
    exact hgap ⟨j.val, by omega⟩ (by simp only; omega)
  have hN : hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) < h := by
    rw [gapBound_parabolicSign k r hk]
    refine gapNum (2 * r + k + 1) (r + 1) t h (by omega) (by omega) (by omega)
      (by unfold Formalism.MainNotions.CayleySignature.rk48 at htn; omega) ?_
    have e : (2 * r + k + 1 + 2 * (r + 1) * t : ℕ) = Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t := by
      unfold Formalism.MainNotions.CayleySignature.rk48; ring
    rw [e]; exact hX
  exact ⟨h, hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, hlow,
    hlam.1, gapAtLeast_parabolicWeight k r v b hk h hlam.1 hlow, hN⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NVHTop
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop

theorem intS : S0.IntSStatement :=
  S0.IntS.intS_of_sIntFin (Mult1.S0.sIntFin Mult1.multiplicity_one_hypotheses_hold)

end ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop
end

