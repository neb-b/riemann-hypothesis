module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionGlobal
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryTransitiveOnIsotropicVectors
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.WittIso

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_sum (x y : Fin M → E) :
    hE σ J x y = ∑ i, ∑ j, σ (x i) * J i j * y j := rfl

theorem hE_add_right (x y z : Fin M → E) : hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp only [hE_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_right (c : E) (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hE_add_left (x y z : Fin M → E) : hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp only [hE_eq_sum, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hE_smul_left (c : E) (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE_eq_sum, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) :
    σ (hE σ J x y) = hE σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE_eq_sum, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_hE_ne_zero (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0) :
    ∃ w, hE σ J x w ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hu : (fun i => σ (x i)) ᵥ* J = 0 := by
    funext j
    have h := hcon (Pi.single j 1)
    simp only [hE_eq_sum, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hu
  apply hx
  funext i
  have := congrFun h0 i
  simpa using this

theorem exists_hyperbolic_partner [CharZero E] (hσ : ∀ a, σ (σ a) = a)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0)
    (hxx : hE σ J x x = 0) :
    ∃ x', hE σ J x x' = 1 ∧ hE σ J x' x = 1 ∧ hE σ J x' x' = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_hE_ne_zero (σ := σ) hdet hx
  obtain ⟨w, hxw⟩ : ∃ w, hE σ J x w = 1 :=
    ⟨(hE σ J x w₀)⁻¹ • w₀, by rw [hE_smul_right, inv_mul_cancel₀ hw₀]⟩
  have hwx : hE σ J w x = 1 := by
    rw [← hE_conj hσ hJ x w, hxw, map_one]
  obtain ⟨t, ht⟩ : ∃ t, t = hE σ J w w := ⟨_, rfl⟩
  have hσt : σ t = t := by
    rw [ht]; exact hE_conj hσ hJ w w
  obtain ⟨c, hc⟩ : ∃ c : E, c = -t / 2 := ⟨_, rfl⟩
  have hσc : σ c = c := by
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [hc, map_div₀, map_neg, hσt, h2]
  have h1 : hE σ J x (w + c • x) = 1 := by
    rw [hE_add_right, hE_smul_right, hxx, hxw]; ring
  have h2 : hE σ J (w + c • x) x = 1 := by
    rw [hE_add_left, hE_smul_left, hxx, hwx]; ring
  refine ⟨w + c • x, h1, h2, ?_⟩
  rw [hE_add_left, hE_smul_left, h1, hE_add_right, hE_smul_right, hwx, ← ht, hσc, hc]
  ring

end Alg

theorem transitive_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 →
    ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x y hx hy hxx hyy
  have hσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  obtain ⟨x', h1, h2, h3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hx hxx
  obtain ⟨y', k1, k2, k3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hy hyy
  have hgram : gramE σ J ![x, x'] = gramE σ J ![y, y'] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramE, hxx, hyy, h1, h2, h3, k1, k2, k3]
  have hdet : (gramE σ J ![x, x']).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [gramE, hxx, h1, h2, h3]
  obtain ⟨g, hg, hgX⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittE.witt_tuple F E σ hCM M J hJ 2 ![x, x'] ![y, y'] hgram hdet
  exact ⟨g, hg, by simpa using hgX 0⟩

end GlobalTheory.CompanionTheory.SW.WittIso
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KUnits

theorem continuousOn_ringInverse {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (h : IsOpenEmbedding (Units.val : Rˣ → R)) :
    ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  refine (h.continuousAt_iff).1 ?_
  have : (Ring.inverse ∘ (Units.val : Rˣ → R)) = fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
    funext v
    simp
  rw [this]
  exact (Units.continuous_val.comp continuous_inv).continuousAt

theorem units_val_isOpenEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R →
    IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR
  obtain ⟨hTR, hLC, hSC, hT2, hArt, hRd, hUo, -⟩ := hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hArt
  haveI := hRd
  obtain ⟨-, -, -, hinv, -, hfix, hunit⟩ := _root_.GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol F E σ hσ R
  obtain ⟨hTK, -, -, -, hsc, htr, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have hfin : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfin
  let N : R ⊗[F] E → R := fun y =>
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y)
  have hNc : Continuous N :=
    continuous_const.mul (htr.comp (continuous_id.mul hsc))
  have hhalf : algebraMap F R (1 / 2) * (2 : R) = 1 := by
    have : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul]
      norm_num
    rwa [map_ofNat] at this
  have hnorm : ∀ y : R ⊗[F] E, y * sigR R σ y = N y ⊗ₜ[F] (1 : E) := by
    intro y
    obtain ⟨r, hr⟩ := hfix (y * sigR R σ y) (by rw [map_mul, hinv, mul_comm])
    have htrace : Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = 2 * r := by
      have h1 : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [h1, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) r]
      simp [two_mul, two_nsmul]
    have hNr : N y = r := by
      show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y) = r
      rw [hr, htrace, ← mul_assoc, hhalf, one_mul]
    rw [hNr, hr]
  have hiff : ∀ y : R ⊗[F] E, IsUnit y ↔ IsUnit (N y) := by
    intro y
    constructor
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := hy.mul (hy.map (sigR R σ))
      rw [hnorm y] at h1
      exact (hunit _).1 h1
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := by
        rw [hnorm y]
        exact (hunit _).2 hy
      exact isUnit_of_mul_isUnit_left h1
  have hone : Continuous fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) := by
    have h1 : (fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [h1]
    exact Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id continuous_const
  let f : R ⊗[F] E → R ⊗[F] E := fun y => sigR R σ y * (Ring.inverse (N y) ⊗ₜ[F] (1 : E))
  have hfc : ContinuousOn f {y | IsUnit y} := by
    have h1 : ContinuousOn (fun y => Ring.inverse (N y)) {y : R ⊗[F] E | IsUnit y} :=
      (continuousOn_ringInverse hUo).comp hNc.continuousOn (fun y hy => (hiff y).1 hy)
    exact hsc.continuousOn.mul (hone.comp_continuousOn h1)
  have hfu : ∀ u : (R ⊗[F] E)ˣ, f u.1 = ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    intro u
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have hu : IsUnit (N u.1) := (hiff _).1 u.isUnit
    show u.1 * (sigR R σ u.1 * (Ring.inverse (N u.1) ⊗ₜ[F] (1 : E))) = 1
    rw [← mul_assoc, hnorm, Algebra.TensorProduct.tmul_mul_tmul, Ring.mul_inverse_cancel _ hu,
      mul_one]
    rfl
  refine ⟨Units.isEmbedding_val_mk' hfc hfu, ?_⟩
  have hrange : Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) =
      N ⁻¹' Set.range (Units.val : Rˣ → R) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact (hiff _).1 u.isUnit
    · intro hy
      exact (hiff y).2 hy
  rw [hrange]
  exact hUo.isOpen_range.preimage hNc

end GlobalTheory.CompanionTheory.SW.KUnits
end

