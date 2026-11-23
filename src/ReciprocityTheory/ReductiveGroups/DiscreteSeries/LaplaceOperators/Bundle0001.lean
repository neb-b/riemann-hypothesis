module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

section Bessel

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def chiInv (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (h m : Mat k r) (ξ : Vp) : Vp :=
  star (ψ m) • π h⁻¹ ξ

def sInt (μW μN : Measure (Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (f : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) : Vp :=
  ∫ p : Mt k r × Mt k r, f (Matrix.of p.1 * Matrix.of p.2 * x) •
    chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)

def IsBData (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ (∀ a, c a ≠ 0) ∧ Formalism.MainNotions.S.IsHCTypeW k r z u π ∧
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW ∧ Formalism.MainNotions.S.IsHaarOn (Nset k r) μN

end Bessel

section Coef

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

def psiCoef (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r) (v₁ v₂ : T.V)
    (g : Mat k r) : ℂ :=
  ⟪v₂, S7.PsiM T μ (P * g * P⁻¹) v₁⟫_ℂ

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def aaFun (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (μW μN : Measure (Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r) : Vp :=
  sInt μW μN ψ π (fun g => psiCoef T μ P v₁ v₂ (x₀⁻¹ * g)) ξ x

end Coef

section B

variable {k r : ℕ}

def BesselNZ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∃ (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) (_ : NormedAddCommGroup Vp)
    (_ : InnerProductSpace ℂ Vp) (_ : CompleteSpace Vp) (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)),
    S7.IsMu lam μ ∧ Formalism.MainNotions.S.IsCayley k r ε P ∧ IsBData z c u π μW μN ∧
    ∃ (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) ∧ x ∈ UH (Hpk k r) ∧
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0

def BesselAll (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∀ (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)),
    S7.IsMu lam μ → Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ v : T.V, v ≠ 0 → ∃ (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) ∧ x ∈ UH (Hpk k r) ∧
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v v ξ x₀ x ≠ 0

end B

section Gap

variable {n : ℕ}

def hNeed (ε : Fin n → Bool) : ℝ :=
  max (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)))
    (max (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2)
      (8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) *
        (4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))

def GapLap (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  StrictAnti lam ∧ GapAtLeast ε lam h ∧ hNeed ε < h

end Gap

section L2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end L2

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.TransportIntA
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA

def extL {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v i := if h : p i then v ⟨i, h⟩ else 0
  map_add' v w := by
    funext i
    by_cases h : p i <;> simp [h]
  map_smul' c v := by
    funext i
    by_cases h : p i <;> simp [h]

theorem extL_injective {n : ℕ} (p : Fin n → Prop) [DecidablePred p] : Function.Injective (extL p) := by
  intro v w h
  funext j
  have hj := congrFun h j.1
  simpa [extL, j.2] using hj

theorem form_conj {n : ℕ} (Q J : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) = star x ⬝ᵥ ((Qᴴ * J * Q) *ᵥ x) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem jm_ext_pos {n : ℕ} (ε : Fin n → Bool) (v : {i // ε i = true} → ℂ) :
    Formalism.REAL.Jm ε *ᵥ extL (fun i => ε i = true) v = extL (fun i => ε i = true) v := by
  funext i
  rw [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  by_cases h : ε i = true <;> simp [extL, h]

theorem jm_ext_neg {n : ℕ} (ε : Fin n → Bool) (v : {i // ε i = false} → ℂ) :
    Formalism.REAL.Jm ε *ᵥ extL (fun i => ε i = false) v = -extL (fun i => ε i = false) v := by
  funext i
  rw [Formalism.REAL.Jm, Matrix.mulVec_diagonal]
  by_cases h : ε i = false <;> simp [extL, h]

private theorem pq_lemma {n : ℕ} (η : Fin n → Bool) : pOf η + qOf η = n := by
  classical
  unfold pOf qOf
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun a _ h1 h2 => by simp_all)]
  have hu : (Finset.univ.filter fun a => η a = true) ∪ (Finset.univ.filter fun a => η a = false) =
      Finset.univ := by
    ext a
    cases h : η a <;> simp [h]
  rw [hu, Finset.card_univ, Fintype.card_fin]

theorem pOf_le_of_conj {n : ℕ} (ε ε' : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε') : pOf ε' ≤ pOf ε := by
  classical
  by_contra hlt
  push_neg at hlt
  let f1 : ({i // ε' i = true} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Q.mulVecLin ∘ₗ extL (fun i => ε' i = true)
  let f2 := extL (fun i : Fin n => ε i = false)
  have hpos : ∀ u, extL (fun i => ε' i = true) u ≠ 0 →
      0 < star (Q *ᵥ extL (fun i => ε' i = true) u) ⬝ᵥ
        (Formalism.REAL.Jm ε *ᵥ (Q *ᵥ extL (fun i => ε' i = true) u)) := by
    intro u hu
    rw [form_conj, hQ, jm_ext_pos]
    exact Matrix.dotProduct_star_self_pos_iff.2 hu
  have hf1 : Function.Injective f1 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hne
    have hz : extL (fun i => ε' i = true) u ≠ 0 := fun h =>
      hne (extL_injective _ (by rw [h, map_zero]))
    have h := hpos u hz
    have hu' : Q *ᵥ extL (fun i => ε' i = true) u = 0 := hu
    rw [hu'] at h
    simp at h
  have hf2 : Function.Injective f2 := extL_injective _
  have hr1 : Module.finrank ℂ (LinearMap.range f1) = pOf ε' := by
    rw [LinearMap.finrank_range_of_inj hf1, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hr2 : Module.finrank ℂ (LinearMap.range f2) = qOf ε := by
    rw [LinearMap.finrank_range_of_inj hf2, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
    rfl
  have hpq := pq_lemma ε
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f1) (LinearMap.range f2)
  rw [hr1, hr2] at hsum
  have hle : Module.finrank ℂ ↥(LinearMap.range f1 ⊔ LinearMap.range f2) ≤ n := by
    have h := Submodule.finrank_le (LinearMap.range f1 ⊔ LinearMap.range f2)
    rwa [Module.finrank_fin_fun] at h
  have hne : LinearMap.range f1 ⊓ LinearMap.range f2 ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsum
    simp at hsum
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hy1
  obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hy2
  have hu' : Q *ᵥ extL (fun i => ε' i = true) u = y := hu
  have hw' : extL (fun i => ε i = false) w = y := hw
  have hz : extL (fun i => ε' i = true) u ≠ 0 := fun h => by
    rw [h, Matrix.mulVec_zero] at hu'
    exact hy0 hu'.symm
  have h1 := hpos u hz
  rw [hu', ← hw', jm_ext_neg, hw', dotProduct_neg] at h1
  have h2 : 0 < star y ⬝ᵥ y := Matrix.dotProduct_star_self_pos_iff.2 hy0
  have h3 := add_pos h2 h1
  rw [add_neg_cancel] at h3
  exact lt_irrefl _ h3

theorem pOf_le_of_two {n : ℕ} (ε ε' : Fin n → Bool) (H P P₀ : Matrix (Fin n) (Fin n) ℂ)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = H) (hP₀ : P₀ᴴ * Formalism.REAL.Jm ε' * P₀ = H) (h0 : IsUnit P₀.det) :
    pOf ε' ≤ pOf ε := by
  apply pOf_le_of_conj ε ε' (P * P₀⁻¹)
  have h1 : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ h0
  calc (P * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P₀⁻¹) = (P₀⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P₀⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε' * P₀) * P₀⁻¹ := by rw [hP, hP₀]
    _ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε' * (P₀ * P₀⁻¹) := by
        rw [Matrix.conjTranspose_mul]
        simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε' := by rw [h1, Matrix.conjTranspose_one, one_mul, mul_one]

theorem cayley_signature' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayley k r ε P) : pOf ε = k + r ∧ qOf ε = r + 1 := by
  obtain ⟨-, -, -, ε0, hε0, P0, hP0det, hP0⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have h1 : pOf ε0 ≤ pOf ε := pOf_le_of_two ε ε0 _ P P0 hP.2 hP0 hP0det
  have h2 : pOf ε ≤ pOf ε0 :=
    pOf_le_of_two ε0 ε _ P0 P hP0 hP.2 ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
  have h0 : pOf ε0 = k + r := hε0
  have hpq := pq_lemma ε
  constructor <;> omega

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA
end
end

