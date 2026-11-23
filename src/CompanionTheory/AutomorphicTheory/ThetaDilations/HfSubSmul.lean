module

public import CompanionTheory.AutomorphicTheory.ThetaDilations.ParAlg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianDiagonalizeOverReducedTensor
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

section Ring

variable {S : Type} [CommRing S] {s : S →+* S} {M : ℕ} {J : Matrix (Fin M) (Fin M) S}

theorem hf_conj (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (x y : Fin M → S) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_sub_smul (x y z : Fin M → S) (c : S) :
    hform s J z (x - c • y) = hform s J z x - c * hform s J z y ∧
      hform s J (x - c • y) z = hform s J x z - s c * hform s J y z := by
  constructor <;>
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib] <;>
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_U {g : Matrix (Fin M) (Fin M) S} (hg : cT s g * J * g = J) (x y : Fin M → S) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s J x y := by
  have e : (s : S → S) ∘ (g *ᵥ x) = (s ∘ x) ᵥ* cT s g := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg]

theorem quasi (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (u : Fin M → S) (c : S)
    (hc : c + s c = c * s c * hform s J u u) :
    ∃ g ∈ UJ s J, ∀ z, g.val *ᵥ z = z - (c * hform s J u z) • u := by
  let T : S → Matrix (Fin M) (Fin M) S := fun c => 1 - c • Matrix.vecMulVec u ((s ∘ u) ᵥ* J)
  have hT : ∀ c z, T c *ᵥ z = z - (c * hform s J u z) • u := fun c z => by
    simp only [T, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hform_eq, mul_smul]
    simp
  have hm : ∀ a b, a + b = a * b * hform s J u u → T a * T b = 1 := fun a b h => by
    refine Matrix.mulVec_injective (funext fun z => ?_)
    rw [← Matrix.mulVec_mulVec, hT, hT, (hf_sub_smul _ _ _ _).1, Matrix.one_mulVec, sub_sub, ← add_smul,
      show b * hform s J u z + a * (hform s J u z - b * hform s J u z * hform s J u u) = 0 by
        linear_combination (hform s J u z) * h, zero_smul, sub_zero]
  refine ⟨⟨T c, T (s c), hm _ _ hc, hm _ _ (by rw [add_comm, hc]; ring)⟩, ?_, hT c⟩
  have hb : ∀ (A : Matrix (Fin M) (Fin M) S) i j, hform s A (Pi.single i 1) (Pi.single j 1) = A i j := fun A i j => by
    simp [hform, Pi.single_apply, apply_ite s]
  have hp : ∀ x y, hform s (cT s (T c) * J * T c) x y = hform s J (T c *ᵥ x) (T c *ᵥ y) := fun x y => by
    have e : (s : S → S) ∘ (T c *ᵥ x) = (s ∘ x) ᵥ* cT s (T c) := by
      funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
    rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show cT s (T c) * J * T c = J
  ext i j
  rw [← hb (cT s (T c) * J * T c), ← hb J, hp, hT, hT, (hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, map_mul,
    hf_conj hs hJ]
  linear_combination (-(hform s J (Pi.single i 1) u * hform s J u (Pi.single j 1))) * hc

end Ring

theorem refl_fix : ∀ (S : Type) [CommRing S] (s : S →+* S), (∀ z, s (s z) = z) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) S), cT s J = J → ∀ (x y : Fin M → S) (lam : S), lam * s lam = 1 → hform s J y y = hform s J x x → IsUnit (hform s J x x) → IsUnit (hform s J x x - s lam * hform s J y x) → ∃ g ∈ UJ s J, (g : Matrix (Fin M) (Fin M) S) *ᵥ x = y ∧ ∀ z, hform s J x z = 0 → hform s J y z = 0 → (g : Matrix (Fin M) (Fin M) S) *ᵥ z = z := by
  intro S _ s hs M J hJ x y lam hl hy hb hc
  obtain ⟨γ, hγ⟩ := hc.exists_left_inv
  obtain ⟨β, hβ⟩ := hb.exists_left_inv
  have hγs := congrArg s hγ
  have hβs := congrArg s hβ
  simp only [map_mul, map_sub, hs, hf_conj hs hJ, map_one] at hγs hβs
  obtain ⟨g₁, h1, e1⟩ := quasi hs hJ (x - lam • y) γ (by
    rw [(hf_sub_smul _ _ _ _).1, (hf_sub_smul _ _ _ _).2, (hf_sub_smul _ _ _ _).2, hy]
    linear_combination (-s γ) * hγ - γ * hγs - γ * s γ * hform s J x x * hl)
  obtain ⟨g₂, h2, e2⟩ := quasi hs hJ y ((1 - s lam) * β) (by
    rw [map_mul, map_sub, map_one, hs, hy]
    have hββ : s β = β := by linear_combination β * hβs - s β * hβ
    rw [hββ]
    linear_combination (-((1 - s lam) * (1 - lam) * β)) * hβ - β * hl)
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ h2 h1, ?_, fun z hx hy' => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hγ, one_smul, sub_sub_cancel,
      Matrix.mulVec_smul, e2, hy, mul_assoc, hβ, mul_one, sub_smul, one_smul, sub_sub_cancel, smul_smul, hl, one_smul]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, e1, (hf_sub_smul _ _ _ _).2, hx, hy']
    simp [e2, hy']

section Tuples

variable {S : Type} [CommRing S] {s : S →+* S} {M n : ℕ} {J : Matrix (Fin M) (Fin M) S}

theorem witt_diag (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) (D : Fin n → S) (hD : ∀ i, IsUnit (D i))
    (hl : ∀ i t, ∃ lam, lam * s lam = 1 ∧ IsUnit (D i - s lam * t)) (X Y : Fin n → Fin M → S)
    (hX : ∀ a b, hform s J (X a) (X b) = Matrix.diagonal D a b)
    (hY : ∀ a b, hform s J (Y a) (Y b) = Matrix.diagonal D a b) : ∃ g ∈ UJ s J, ∀ a, g.val *ᵥ X a = Y a := by
  classical
  suffices h : ∀ T : Finset (Fin n), ∃ g ∈ UJ s J, ∀ a ∈ T, g.val *ᵥ X a = Y a from
    (h Finset.univ).imp fun g hg => ⟨hg.1, fun a => hg.2 a (Finset.mem_univ a)⟩
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | insert k T hk ih =>
    obtain ⟨g, hg, e⟩ := ih
    have hx : hform s J (g.val *ᵥ X k) (g.val *ᵥ X k) = D k := by rw [hf_U hg, hX, Matrix.diagonal_apply_eq]
    obtain ⟨lam, l1, l2⟩ := hl k (hform s J (Y k) (g.val *ᵥ X k))
    obtain ⟨g', hg', e1, e2⟩ := refl_fix S s hs M J hJ (g.val *ᵥ X k) (Y k) lam l1
      (by rw [hx, hY, Matrix.diagonal_apply_eq]) (hx ▸ hD k) (hx ▸ l2)
    refine ⟨g' * g, Subgroup.mul_mem _ hg' hg, fun a ha => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact e1
    · have hne : k ≠ a := fun h => hk (h ▸ ha)
      rw [e2 _ (by rw [hf_U hg, hX, Matrix.diagonal_apply_ne _ hne]) (by rw [e a ha, hY, Matrix.diagonal_apply_ne _ hne]),
        e a ha]

end Tuples

theorem cT_JR' {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

end CompanionTheory.PlacePermOperatorBicommutantSpan
