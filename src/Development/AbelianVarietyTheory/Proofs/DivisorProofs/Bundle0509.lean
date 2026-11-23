module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCongruenceSubgroups
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.UCls.KGrp
open scoped ENNReal TensorProduct

theorem GlobalTheory.UCls.exists_special_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  intro E _ _ _ r M m G Λ L g g0 S Γ Λi hM hΛ hg0 hL hLhat hg hT hΓ
  have hU : ∀ {γ : GL (Fin r) E}, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) → ∀ x y,
      herm G (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
    intro γ hγ x y
    rw [← hγ, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
  have hRA : ∀ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
      IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E)) :=
    fun γ hγ => _root_.GlobalTheory.RatUnit.isUA_ratM E r G _ (Matrix.isUnits_det_units γ).ne_zero hγ
  have hR1 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.mul_inv, ratM_one]
  have hR2 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.inv_mul, ratM_one]
  have hdet : ∀ γ : Matrix (Fin r) (Fin r) E, (ratM (maximalRealSubfield E) γ).det =
      (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := fun γ =>
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
      RA (maximalRealSubfield E) E).toRingHom γ).symm
  have hex : ∀ i, ∃ (γ : GL (Fin r) E) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), i ∈ S →
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧
      IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧
      IsSA G (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * k⁻¹ * g0⁻¹) := by
    intro i
    by_cases hi : i ∈ S
    swap
    · exact ⟨1, 1, fun h => absurd h hi⟩
    obtain ⟨u, hu, k, hk, hdg⟩ := hT i hi
    obtain ⟨γ, hγ, hγdet⟩ : ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (0 < r → (γ : Matrix (Fin r) (Fin r) E).det = u) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exact ⟨1, fun x y => by simp, fun h => absurd h (by omega)⟩
      · obtain ⟨γ, h1, h2⟩ := _root_.GlobalTheory.UnitDet.main E r G u hr hΛ.1 hΛ.2.1 hu
        exact ⟨γ, h1, fun _ => h2⟩
    refine ⟨γ, k, fun _ => ⟨hγ, hk, ?_, ?_⟩⟩
    · exact isUA_mul _ G (isUA_mul _ G (isUA_mul _ G (hRA _ (hU hγ)) (hg i)) (isUA_inv _ G hk.1))
        (isUA_inv _ G hg0)
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hγ1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det * u = 1 := by
          rw [← hγdet hr, ← det_mul, Units.inv_mul, det_one]
        have e1 : ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hγ1, Algebra.TensorProduct.one_def]
        have e2 := Ring.mul_inverse_cancel _ hg0.1
        have e3 := Ring.mul_inverse_cancel _ hk.1.1
        rw [det_mul, det_mul, det_mul, det_nonsing_inv, det_nonsing_inv, hdet, hdg]
        calc _ = (((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u)) *
            (g0.det * Ring.inverse g0.det) * (k.det * Ring.inverse k.det) := by ring
          _ = 1 := by rw [e1, e2, e3, one_mul, one_mul]
  choose γ k hγk using hex

  refine ⟨γ, fun i => ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
    (k i)⁻¹ * g0⁻¹, ?_, ?_⟩
  · intro i hi
    obtain ⟨hγU, hk, hsSA⟩ := hγk i hi
    refine ⟨hγU, hsSA, fun δ hδdet hδU => ?_⟩
    have hmap : δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ γ i * δ * (γ i)⁻¹ ∈ Γ i := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    obtain ⟨hΛi, hΓi⟩ := hΓ i hi
    have hgU : IsUnit (g i) := (Matrix.isUnit_iff_isUnit_det _).2 (hg i).1
    obtain ⟨Λ', hΛ'1, -, -, hΛ'hat⟩ := exists_lattice_latOf (maximalRealSubfield E) E r Λ hgU.unit
      hΛ.2.2.1 hΛ.2.2.2.1
    rw [IsUnit.unit_spec] at hΛ'1 hΛ'hat
    have hhat : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i).mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set _) := by
      rw [hΛi, ← hΛ'1, hΛ'hat]
    have hrat : ∀ v, fv (maximalRealSubfield E) v ∈ hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) ↔
        v ∈ Λi i := fun v => by
      rw [← SetLike.mem_coe, hhat, ← SetLike.mem_coe (x := v), hΛi]; rfl
    have hβU : ∀ x y, herm G (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
      intro x y
      simp only [Units.val_mul, ← mulVec_mulVec, hγU, hδU, hU hγU]
    have e0 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ek : k i * (k i)⁻¹ = 1 := mul_nonsing_inv _ hk.1.1
    have ek' : (k i)⁻¹ * k i = 1 := nonsing_inv_mul _ hk.1.1
    have eg : g i * (g i)⁻¹ = 1 := mul_nonsing_inv _ (hg i).1
    have eg' : (g i)⁻¹ * g i = 1 := nonsing_inv_mul _ (hg i).1
    have c0 : ∀ P, P * g0 * g0⁻¹ = P := fun P => by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
    have c0' : ∀ P, P * g0⁻¹ * g0 = P := fun P => by rw [Matrix.mul_assoc, e0', Matrix.mul_one]
    have ck : ∀ P, P * k i * (k i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, ek, Matrix.mul_one]
    have ck' : ∀ P, P * (k i)⁻¹ * k i = P := fun P => by rw [Matrix.mul_assoc, ek', Matrix.mul_one]
    have cg : ∀ P, P * g i * (g i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, eg, Matrix.mul_one]
    have cg' : ∀ P, P * (g i)⁻¹ * g i = P := fun P => by rw [Matrix.mul_assoc, eg', Matrix.mul_one]
    have cR : ∀ P, P * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P := fun P => by
      rw [Matrix.mul_assoc, hR1, Matrix.mul_one]
    have hXY : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i * (k i)⁻¹ * g0⁻¹).mulVec '' (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) := by
      rw [hhat, ← isKM_image _ G _ M (GlobalTheory.UCls.KGrp.isKM_inv _ G _ M hk), Set.image_image, hLhat, Set.image_image]
      simp only [mulVec_mulVec, c0']
    have hsinv : (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ = g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) := by
      refine Matrix.inv_eq_left_inv ?_
      simp only [← Matrix.mul_assoc, cR, cg', ck, e0]
    have hconj := hatKM_conj (X := (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set _))
      (Y := (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E))) M
      (A := g i * (k i)⁻¹ * g0⁻¹) (A' := g0 * k i * (g i)⁻¹)
      (P := ratM (maximalRealSubfield E) ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (by simp only [← Matrix.mul_assoc, c0', ck', eg]) (by simp only [← Matrix.mul_assoc, cg', ck, e0]) hXY
    have hPeq : g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E)
        ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (g i * (k i)⁻¹ * g0⁻¹) =
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹) := by
      rw [hsinv, Units.val_mul, Units.val_mul, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
    rw [hPeq] at hconj
    have hsUA := hsSA.1
    have hKUA : IsUA (IsCMField.complexConj E) G ((ratM (maximalRealSubfield E)
        (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * (k i)⁻¹ * g0⁻¹)⁻¹ *
        ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)) :=
      isUA_mul _ G (isUA_mul _ G (isUA_inv _ G hsUA) (hRA δ hδU)) hsUA
    have hL5 := GlobalTheory.T.lattice_congruence_iff_completion (maximalRealSubfield E) E r (Λi i) M (γ i * δ * (γ i)⁻¹) hM hrat
    rw [hmap, hΓi]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨hKUA, hconj.1 (hL5.1 ⟨h1, h2⟩)⟩
    · intro hK
      obtain ⟨h1, h2⟩ := hL5.2 (hconj.2 hK.2)
      exact ⟨⟨hβU, h1⟩, h2⟩

  · intro i hi j hj hSE
    obtain ⟨δ, hδ, κ, hκ, -, hsj⟩ := hSE
    simp only at hsj
    obtain ⟨hγiU, hki, -⟩ := hγk i hi
    obtain ⟨hγjU, hkj, -⟩ := hγk j hj
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ekj : k j * (k j)⁻¹ = 1 := mul_nonsing_inv _ hkj.1.1
    have egj : g j * (g j)⁻¹ = 1 := mul_nonsing_inv _ (hg j).1
    refine ⟨(γ j : Matrix (Fin r) (Fin r) E) * δ * (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E), ?_,
      (k i)⁻¹ * (g0⁻¹ * κ * g0) * k j, ?_, ?_⟩
    · rw [ratM_mul, ratM_mul]
      exact isUA_mul _ G (isUA_mul _ G (hRA _ hγjU) hδ.1) (hRA _ (hU hγiU))
    · exact GlobalTheory.UCls.KGrp.isKM_mul _ G _ M (GlobalTheory.UCls.KGrp.isKM_mul _ G _ M (GlobalTheory.UCls.KGrp.isKM_inv _ G _ M hki) (isKM_conj _ G _ _ M hg0 hLhat hκ)) hkj
    · have hdj : g j = ratM (maximalRealSubfield E) (γ j : Matrix (Fin r) (Fin r) E) *
          (ratM (maximalRealSubfield E) (((γ j)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g j *
            (k j)⁻¹ * g0⁻¹) * g0 * k j := by
        simp only [← Matrix.mul_assoc, hR1 (γ j), Matrix.one_mul]
        rw [Matrix.mul_assoc (g j * (k j)⁻¹), e0', Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul _ hkj.1.1,
          Matrix.mul_one]
      rw [hdj, hsj, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKill
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem rAug_comp_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) :
    rAug (Int.castRingHom S) (resAug F) ≫ δ.toZ = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  apply Sheaf.hom_ext
  ext U b
  obtain ⟨-, -, -, -, h5, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic S F
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
  let a : Sec ((restr (Int.castRingHom S)).obj F) U.unop := Sec.map e.hom b
  have hb : b = Sec.map (sglι ((restr (Int.castRingHom S)).obj F)) a := by
    change b = Sec.map (e.hom ≫ e.inv) b
    rw [Iso.hom_inv_id]; rfl
  have h1 := rAug_f_zero (Int.castRingHom S) (resAug F) U.unop a
  change Sec.map (δ.toZ.f 0) (Sec.map ((rAug (Int.castRingHom S) (resAug F)).f 0) b) = 0
  rw [hb]
  have key : δ.app U.unop 0 (Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a))) = 0 := by
    have h6 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a)) = Sec.map (resι S F) a := by
      rw [← h5]; rfl
    rw [h6]; exact hδ _ _
  exact (congrArg (δ.app U.unop 0) h1).trans key

theorem cpush_zero_hom {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [cpost_mk]
  have : zcomp z (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := by
    ext1; simp [zcomp]
  rw [this, CohomologyClass.mk_zero]

theorem cpush_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) (E : Spc) (n : ℤ)
    (y : CohomologyClass ((chains ℤ).obj E) ((rcx (Int.castRingHom S)).obj (res S F)) n) :
    cpush ((chains ℤ).obj E) δ.toZ n y = 0 := by
  obtain ⟨-, -, -, hqF, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic S F
  obtain ⟨-, hinjG, hgeG, hqG, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R G
  let G' := (restr (Int.castRingHom R)).obj G
  obtain ⟨hKI', -, hGE', -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic ℤ G'
  haveI := hqF; haveI := hqG; haveI := hgeG; haveI := hKI'; haveI := hGE'
  haveI : QuasiIso (rAug (Int.castRingHom S) (resAug F)) := rAug_quasiIso _ _
  haveI : QuasiIso (rAug (Int.castRingHom R) (resAug G)) := rAug_quasiIso _ _
  obtain ⟨v, hv⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (res ℤ G')
    (rAug (Int.castRingHom R) (resAug G))).1 (resAug G')
  have hacyc : ∀ (t : ℤ) (P : PSh) (m : ℤ), 0 < m →
      Subsingleton (H ℤ (disc.obj P) (((rcx (Int.castRingHom R)).obj (res R G)).X t) m) :=
    fun t P m hm => GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R (Int.castRingHom R) ((res R G).X t) P m hm
  have hbij := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (rAug (Int.castRingHom R) (resAug G)) v hv
    hacyc E n
  have hzero := rAug_comp_toZ_eq_zero_of_kill S F R G δ hδ
  obtain ⟨hom⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ ((restr (Int.castRingHom S)).obj F) ((rcx (Int.castRingHom S)).obj (res S F)) (res ℤ G')
    (rAug (Int.castRingHom S) (resAug F))).2 (δ.toZ ≫ v) 0 (by rw [← Category.assoc, hzero]; simp)
  have h1 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.2.2 _ _ ⟨hom⟩ ((chains ℤ).obj E) n).2
  have h2 : cpush ((chains ℤ).obj E) v n (cpush ((chains ℤ).obj E) δ.toZ n y) = cpush ((chains ℤ).obj E) v n 0 := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.1, h1, cpush_zero_hom, map_zero]
  exact hbij.1 h2

theorem semiMap_op_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R)
    (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) →
    ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  intro S R _ _ F G δ hδ E n x
  let ιA := idSemi (Int.castRingHom S) (res S F)
  let ιB := idSemi (Int.castRingHom R) (res R G)
  let ρ' : SemiMap (res S F) ((rcx (Int.castRingHom R)).obj (res R G)) :=
    { app := fun U s => δ.app U s
      nat := fun g s a => δ.nat g s a
      comm := fun U s t a => δ.comm U s t a }
  have hA := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S ℤ ιA ρ' δ.toZ (fun _ _ _ => rfl)).1 E n x
  have hB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ ιB ιB (𝟙 _) (fun _ _ _ => rfl)).2
    (fun _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩) E n
  have hcomp : ρ'.op.app E n x = ιB.op.app E n (δ.op.app E n x) := by
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).1 E n β
    rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).2 E n β γ hγ,
      (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S ℤ ρ').2 E n α γ ?_]
    intro p s h U y
    rw [hγ p s h U y, hβ p s h U y]
    rfl
  apply hB.1
  rw [map_zero, ← hcomp, hA, cpush_toZ_eq_zero_of_kill S F R G δ hδ E n]

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometry
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem shLift_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' →
    (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) =
      (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  intro F F' _ _ _ _ s hs n f f' hf hf'
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  letI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  have hex := GlobalTheory.T.every_element_is_norm F F' s hs n
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hlf := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f hf).1
  have hlf' := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f' hf').1
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin n) F → ℂ, ∀ γ, c γ = (Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} : ℂ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Fin n) F → ℂ, ∀ γ, v γ = f γ * star (f' γ) := ⟨_, fun _ => rfl⟩
  have hcne : ∀ γ, c γ ≠ 0 := by
    intro γ
    rw [hc, Nat.cast_ne_zero]
    haveI : Nonempty {γ' : GL (Fin n) F // IsConj γ γ'} := ⟨⟨γ, IsConj.refl γ⟩⟩
    exact Nat.card_pos.ne'

  have hclass : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∀ γ' : GL (Fin n) F, IsNorm s δ γ' ↔ IsConj γ γ' := by
    intro δ γ h γ'
    unfold IsNorm at *
    constructor
    · intro h'
      exact hnd γ γ' (IsConj.trans h (IsConj.symm h'))
    · intro h'
      exact IsConj.trans (IsConj.symm (MonoidHom.map_isConj (incl F F' n) h')) h
  have hcard : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → c γ = ((Finset.univ.filter fun γ' => IsNorm s δ γ').card : ℂ) := by
    intro δ γ h
    rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    ext γ'
    simp [hclass δ γ h γ']
  have key : ∀ δ : GL (Fin n) F',
      (∑ γ, if IsNorm s δ γ then v γ / c γ else 0) = shLift s f δ * star (shLift s f' δ) := by
    intro δ
    obtain ⟨γ0, h0⟩ := hex δ
    have e : ∀ γ, (if IsNorm s δ γ then v γ / c γ else 0) =
        if IsNorm s δ γ then (shLift s f δ * star (shLift s f' δ)) / c γ0 else 0 := by
      intro γ
      split_ifs with h
      · rw [hv, hcard δ γ h, ← hcard δ γ0 h0, hlf δ γ h, hlf' δ γ h]
      · rfl
    rw [Finset.sum_congr rfl (fun γ _ => e γ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, ← hcard δ γ0 h0]
    field_simp [hcne γ0]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have lhs : (∑ δ, shLift s f δ * star (shLift s f' δ)) =
      ∑ γ, ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ) := by
    rw [← Finset.sum_congr rfl (fun δ _ => key δ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [lhs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h := hfib γ
  rw [Nat.card_eq_fintype_card (α := {δ : GL (Fin n) F' // IsNorm s δ γ}), Fintype.card_subtype] at h
  have h' : (Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) =
      c γ * (Nat.card (GL (Fin n) F') : ℂ) := by
    rw [hc]
    exact_mod_cast (by rw [mul_comm]; exact h)
  rw [show (Nat.card (GL (Fin n) F) : ℂ) * (((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)) =
      ((Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ)) * v γ / c γ by ring,
    h', hv]
  field_simp [hcne γ]

end GlobalTheory.Shin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  intro Y _ I y hreg n r T hR hI
  refine ⟨hreg, ?_⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  have hSo : IsOpen (⋂ i, (O i : Set Y)) := isOpen_iInter_of_finite fun i => (O i).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz) i
  let f : Fin n → Γ(Y, V) := fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)
  have hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i := fun i => by
    simp only [f]; rw [TopCat.Presheaf.germ_res_apply]; exact ht i
  let a : Γ(Y, V) := ∏ i ∈ T, f i
  have hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i := by
    simp only [a, map_prod, hgf]
  let V' : Y.affineOpens := ⟨V, hV⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'
  have hmap := WMult.stalkId_eq_map_germ I y V' hyV
  rw [hI] at hmap

  obtain ⟨h₂, hu₂, hm₂⟩ := IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a)
    (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')
        rw [← hmap, hga]; exact Ideal.mem_span_singleton_self _)

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)
  have hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a} := by
    intro g
    apply IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV
    have hg : g.1 ∈ I.ideal V' := hs ▸ Submodule.subset_span g.2
    have : Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V') :=
      Ideal.mem_map_of_mem _ hg
    rw [← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span] at this
    exact this
  choose d hdu hdm using hgen
  let h₁ : Γ(Y, V) := ∏ g : s, d g
  have hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁) := by
    simp only [h₁, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g
  have hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a}) := by
    rw [← hs, Submodule.span_le]
    classical
    intro g hg
    show h₁ * g ∈ Ideal.span {a}
    have e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [e, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)
  let h : Γ(Y, V) := h₁ * h₂
  have hyD : y ∈ Y.basicOpen h := (Y.mem_basicOpen h y hyV).2 (by
    simp only [h, map_mul]; exact hu₁.mul hu₂)
  let D : Y.affineOpens := Y.affineBasicOpen (U := V') h
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op
  have hρ : IsUnit (ρ h) := Y.toRingedSpace.isUnit_res_basicOpen h
  have hρ₁ : IsUnit (ρ h₁) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_left hρ
  have hρ₂ : IsUnit (ρ h₂) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_right hρ
  refine ⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩
  · have e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r := by
      funext i
      show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i
      rw [TopCat.Presheaf.germ_res_apply]
      exact hgf i
    rw [e]; exact hR
  · rw [← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op]
    show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}
    have ha : ∏ i ∈ T, ρ (f i) = ρ a := by simp only [a, map_prod]
    rw [ha]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h₁ * x ∈ Ideal.span {a} := hcol hx
      have h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a} := by
        rw [← Set.image_singleton, ← Ideal.map_span]; exact Ideal.mem_map_of_mem _ h1
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁] at h2
      exact h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V') := Ideal.mem_map_of_mem _ hm₂
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂] at h2
      exact h2
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCoefficientReductionUnitClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCoefficientReduction_unitClass : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc, Inv Q E → red Q q E 0 0 (one Q E) = one q E := by
  first
  | exact @GlobalTheory.EtC.red_one
  | exact GlobalTheory.EtC.red_one
  | (intros; apply GlobalTheory.EtC.red_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRestrictedCharacterInIsotypicPartStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_restricted_character_in_isotypic_part : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ → IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 → Kills (fun δ => χ (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (exact GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (intros; apply GlobalTheory.Shin.kills_twist_of_pair_ne_zero  <;> assumption)
end

