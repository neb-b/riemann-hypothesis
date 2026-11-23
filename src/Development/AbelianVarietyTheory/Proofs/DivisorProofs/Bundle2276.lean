module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomOfLinearMapKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HomAlgAny

open MeasureTheory

theorem surjective_of_forall_sub_mem {g : ℕ} (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : DiscreteTopology Λ) (h : ∀ x, ∃ z, x - T z ∈ Λ) : Function.Surjective T := by
  by_contra hT
  have hV : (LinearMap.range T).restrictScalars ℝ ≠ ⊤ := by
    intro h'
    apply hT
    intro x
    have hx : x ∈ (LinearMap.range T).restrictScalars ℝ := h' ▸ Submodule.mem_top
    exact LinearMap.mem_range.1 ((Submodule.restrictScalars_mem ℝ _ x).1 hx)
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcov : (Set.univ : Set (Fin g → ℂ)) ⊆ ⋃ l : Λ,
      (fun y => y + -(l : Fin g → ℂ)) ⁻¹' (((LinearMap.range T).restrictScalars ℝ : Submodule ℝ (Fin g → ℂ)) : Set (Fin g → ℂ)) := by
    intro x _
    obtain ⟨z, hz⟩ := h x
    refine Set.mem_iUnion.2 ⟨⟨x - T z, hz⟩, ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.restrictScalars_mem]
    exact ⟨z, by abel⟩
  have h0 : volume (Set.univ : Set (Fin g → ℂ)) = 0 :=
    measure_mono_null hcov (measure_iUnion_null fun l => by
      rw [measure_preimage_add_right]
      exact Measure.addHaar_submodule volume _ hV)
  exact (isOpen_univ.measure_ne_zero volume Set.univ_nonempty) h0

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a b : Fin g → ℂ)
    (h : u.ex a = u.ex b) : a - b ∈ u.Λ := by
  rw [← u.ker]
  have e := u.ex_add (a - b) b
  rw [sub_add_cancel, h] at e
  have e2 := congrArg (· * (u.ex b)⁻¹) e
  simpa using e2.symm

theorem exists_of_polAV (P P' : Out.PolAV (Sp ℂ)) (n n' : ℕ) (v : HolUnif P.A P.L n) (v' : HolUnif P'.A P'.L n')
    (F : (Fin n → ℂ) →ₗ[ℂ] (Fin n' → ℂ)) (hn : P.g = n) (hn' : P'.g = n') (hF : ∀ z ∈ v.Λ, F z ∈ v'.Λ) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, v'.ex (F z) = v.ex z ≫ f := by
  subst hn hn'
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := existsUnique_isMonHom_of_map_lattice hL hL2 AbLaw.CubeAssembly.cube_gen
    thetaUnifAV_all P P' P.L P'.L v v' F hF
  exact ⟨f, hf, hfe⟩


open GlobalTheory.HolUnifEnd GlobalTheory.HolUnifHom in
theorem exists_isMonHom_of_map_lattice (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (g g' : ℕ)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hgA : SmoothOfRelativeDimension g A.hom)
    (hgA' : SmoothOfRelativeDimension g' A'.hom) (L : LB A.left) (L' : LB A'.left) (u : HolUnif A L g)
    (u' : HolUnif A' L' g') (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hM : ∀ x ∈ u.Λ, M x ∈ u'.Λ) :
    ∃ α : A ⟶ A', IsMonHom α ∧ ∀ w, u'.ex (M w) = u.ex w ≫ α := by
  obtain ⟨Q, v, i, r, J, R, m, hQ, hi, hr, hm, hJ, hR, hJΛ, hRΛ, hRJ⟩ := exists_linear_factor A g hA hgA L u
  obtain ⟨Q', v', i', r', J', R', m', hQ', hi', hr', hm', hJ', hR', hJΛ', hRΛ', hRJ'⟩ :=
    exists_linear_factor A' g' hA' hgA' L' u'
  obtain ⟨β, hβ, hβe⟩ := exists_of_polAV Q Q' (8 * g) (8 * g') v v' (J' ∘ₗ M ∘ₗ R) hQ hQ'
    (fun l hl => hJΛ' _ (hM _ (hRΛ _ hl)))
  haveI := hi; haveI := hr'; haveI := hβ
  have hφ : ∀ z, u.ex z ≫ i ≫ β ≫ r' = u'.ex ((m' * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR', hRJ', hRJ, map_nsmul, smul_smul]
  have := hA'.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A' hA (m' * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    (i ≫ β ≫ r') fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u'.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m' * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m' * m ≠ 0 by positivity)
  have hw : (m' * m) • (((m' * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u'.ex (M w) = u'.ex ((m' * m) • M (((m' * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ i ≫ β ≫ r' := (hφ _).symm
    _ = u.ex (((m' * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m' * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

theorem existsUnique_isMonHom_of_map_ker : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (g g' : ℕ), IsAbelianScheme A → IsAbelianScheme A' → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g' A'.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (e' : (Fin g' → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A')) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), IsExp (𝟙 (Sp ℂ)) e → IsExp (𝟙 (Sp ℂ)) e' → (∀ z, e z = 1 → e' (M z) = 1) → ∃! f : A ⟶ A', IsMonHom f ∧ ∀ z, e' (M z) = e z ≫ f := by
  intro A A' _ _ _ _ g g' hA hA' hg hg' e e' M he he' hM
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨L', ⟨u'⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif A' g' hA' hg'
  obtain ⟨t1, t2⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨t1', t2'⟩ := GlobalTheory.TorusTransfer.tangent_bijective u' hg'
  obtain ⟨T, hT, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA L g g u t1 t2 e he.1 he.2.2.1
  obtain ⟨T', hT', -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g' u' t1' t2' e' he'.1 he'.2.2.1
  have hTs : Function.Surjective T := surjective_of_forall_sub_mem T u.Λ u.discrete fun x => by
    obtain ⟨z, hz⟩ := he.2.1 (u.ex x)
    exact ⟨z, sub_mem_of_ex_eq u _ _ (by rw [hT]; exact hz.symm)⟩
  have hTi : Function.Injective T := LinearMap.injective_iff_surjective.2 hTs
  let Te : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
  have hTe : ∀ z, Te.symm (T z) = z := fun z => Te.symm_apply_apply z
  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := T' ∘ₗ M ∘ₗ Te.symm.toLinearMap
  have hFT : ∀ z, F (T z) = T' (M z) := fun z => by simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, hTe]
  have hF : ∀ x ∈ u.Λ, F x ∈ u'.Λ := fun x hx => by
    obtain ⟨z, rfl⟩ := hTs x
    rw [hFT, ← u'.ker, hT']
    refine hM z ?_
    rw [← hT, u.ker]
    exact hx
  obtain ⟨α, hα, hαe⟩ := exists_isMonHom_of_map_lattice A A' g g' hA hA' hg hg' L L' u u' F hF
  have hex : ∀ z, e' (M z) = e z ≫ α := fun z => by
    rw [← hT', ← hFT, hαe, hT]
  refine ⟨α, ⟨hα, hex⟩, fun f hf => ?_⟩
  haveI := hA.smooth
  haveI := hA'.proper
  haveI : IsReduced A.left := GlobalTheory.isReduced_of_smooth_complex _ A.hom hA.smooth
  refine GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
  obtain ⟨z, rfl⟩ := he.2.1 x
  rw [← hf.2, hex]

end GlobalTheory.HomAlgAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunction
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatSec

theorem nat_of_comp (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
      (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
    (x : Pt Y D) (x' : Pt Y D') (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (h : spMap φ ≫ x.left = x'.left) :
    t D' x' = φ (t D x) := by
  have h1 : x.left ≫ Y.hom = spMap (algebraMap R D) := Over.w x
  have h2 : x'.left ≫ Y.hom = spMap (algebraMap R D') := Over.w x'
  have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ ≫ spMap _ = spMap _
    rw [← h1, ← h2, ← h, Category.assoc]
  let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
  have h4 := ht D D' ψ x hx
  have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
  rw [h5] at h4
  exact h4

theorem fromSpecStalk_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem ext_of_evU (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (a a' : Γ(Y.left, U))
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U a = evU z.left U a') : a = a' := by
  refine TopCat.Presheaf.section_ext Y.left.sheaf U a a' fun y hy ↦ ?_
  let S : CommRingCat.{0} := Y.left.presheaf.stalk y
  letI al : Algebra R S := (Spec.preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).hom.toAlgebra
  let z : Pt Y S := Over.homMk (Y.left.fromSpecStalk y)
    (Spec.map_preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).symm
  have hz : ⊤ ≤ z.left ⁻¹ᵁ U := fromSpecStalk_top y U hy
  have e := h S z hz
  unfold evU at e
  rw [dite_eq_left hz, dite_eq_left hz] at e
  unfold evalAt at e
  change (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a) =
    (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a') at e
  rw [fromSpecStalk_appLE y U hy] at e
  simp only [CommRingCat.comp_apply] at e
  change (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ = (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ at e
  simp only [Iso.inv_hom_id_apply] at e
  exact e

theorem exists_unique_section : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) → ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → evU z.left U a = t E z := by
  intro R _ Y U t ht
  let Z : Scheme.{0} := U.toScheme
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), @Pt R _ Y D _ (al D x) := fun D x ↦
    Over.homMk (x ≫ U.ι) (by rw [Category.assoc]; exact (Spec.map_preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).symm)
  have hin : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), ⊤ ≤ (x ≫ U.ι) ⁻¹ᵁ U := by
    intro D x p _
    exact (x p).2
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Z) → D := fun D x ↦ @t D _ (al D x) (pt D x)
  obtain ⟨s, hs⟩ := NatConst.exists_section Z (fun _ : Unit ↦ (⊤ : Z.Opens)) (by simp) κ
    fun D D' φ x _ ↦ @NatSec.nat_of_comp R _ Y U t ht D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom
      (pt D x) (pt D' _) (hin D x) (by change Spec.map φ ≫ x ≫ U.ι = (Spec.map φ ≫ x) ≫ U.ι; rw [Category.assoc])
  have hex : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U (U.topIso.hom s) = t E z := by
    intro E _ inst z hz
    have hr : Set.range z.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact hz (Set.mem_univ q)
    let w : Spec (CommRingCat.of E) ⟶ Z := IsOpenImmersion.lift U.ι z.left hr
    have hw : w ≫ U.ι = z.left := IsOpenImmersion.lift_fac U.ι z.left hr
    have h1 : κ (CommRingCat.of E) w = t E z := by
      refine (@NatSec.nat_of_comp R _ Y U t ht E _ inst E _ (al (CommRingCat.of E) w) (RingHom.id E) z
        (pt (CommRingCat.of E) w) hz ?_)
      change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ z.left = w ≫ U.ι
      rw [hw, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← h1, hs (CommRingCat.of E) w ⟨(), le_top⟩]
    unfold evU
    rw [dite_eq_left hz]
    unfold evalAt
    simp only [RingHom.comp_apply]
    congr 1
    have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
      rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    have key : ∀ (g : Spec (CommRingCat.of E) ⟶ Y.left) (_ : w ≫ U.ι = g) (h : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ h = U.topIso.inv ≫ w.appLE ⊤ ⊤ le_top := by
      rintro _ rfl h
      rw [← hι]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [key _ hw hz, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨U.topIso.hom s, hex, fun a ha ↦ ?_⟩
  exact NatSec.ext_of_evU R Y U a _ fun E _ _ z hz ↦ (ha E z hz).trans (hex E z hz).symm

end GlobalTheory.PtExt.NatSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingAdd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorAdd

open GlobalTheory.CechPic

variable {S S' : Scheme.{0}}

theorem comp_psum {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G))
    (x' : Fin n → (T' ⟶ G)) (h : ∀ i, u ≫ x i = x' i) (I : Finset (Fin n)) :
    u.left ≫ (psum G x I).left = (psum G x' I).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom u) x I).trans (congrArg (fun q => psum G q I) (funext h)))

theorem pull_lam {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (h : (abelian₂ G L).IsLB)
    (x y : T ⟶ G) :
    pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L) h) =
      pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
        pull (1 : T ⟶ G).left (cls L hL) := by
  have e := cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum G (x2 G) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) h
  refine (congrArg (pull (lift x y : T ⟶ G2 G).left) e).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left (cls L hL)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x y : T ⟶ G2 G) (x2 G) ![x, y] (fun i => by fin_cases i <;> simp [x2])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem cube {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (x x' y : T ⟶ G) :
    pull (x * x' * y).left (cls L.L L.isLB) - pull (x * x').left (cls L.L L.isLB) - pull (x * y).left (cls L.L L.isLB)
      - pull (x' * y).left (cls L.L L.isLB) + pull x.left (cls L.L L.isLB) + pull x'.left (cls L.L L.isLB)
      + pull y.left (cls L.L L.isLB) - pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have h : (Theta G L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have z : cls (Theta G L.L) h = 0 := (cls_eq_zero_iff h).2 ⟨c.t, c.isGen⟩
  have e := cls_linComb L.isLB (K := ULift.{0} (Finset (Fin 3))) (fun I => (psum G (x3 G) I.down).left)
    (fun I => (-1) ^ (3 - I.down.card)) h
  have e' := (congrArg (pull (lift x (lift x' y) : T ⟶ G3 G).left) (e.symm.trans z)).trans (map_zero _)
  refine Eq.trans (Eq.symm ?_) e'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, x', y] I).left (cls L.L L.isLB)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x (lift x' y) : T ⟶ G3 G) (x3 G) ![x, x', y]
      (fun i => by fin_cases i <;> simp [x3])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [neg_smul, one_smul]
  abel

theorem lam_add {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (h : (abelian₂ G L.L).IsLB)
    (x x' y : T ⟶ G) :
    pull (lift (x * x') y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) - pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h)
      - pull (lift x' y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) = 0 := by
  rw [pull_lam L.isLB, pull_lam L.isLB, pull_lam L.isLB, ← cube c x x' y]
  abel

theorem lift_square {G : Over S} {H : Over S'} [GrpObj G] [GrpObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x y : T ⟶ H) :
    (lift x y : T ⟶ G2 H).left ≫ κ = (lift (pushHom hp T x) (pushHom hp T y) : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
  have A : ∀ (p q : Over.mk (T.hom ≫ f) ⟶ G), p.left = x.left ≫ φ → q.left = y.left ≫ φ →
      (lift x y : T ⟶ G2 H).left ≫ κ = (lift p q : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
    intro p q hp' hq'
    apply pullback.hom_ext
    · show (_ ≫ κ) ≫ (fst G G).left = (lift p q ≫ fst G G).left
      rw [lift_fst, hp', Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ κ) ≫ (snd G G).left = (lift p q ≫ snd G G).left
      rw [lift_snd, hq', Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact A _ _ rfl rfl

theorem exists_gen {G G' : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj H]
    {L : RigLB G'} (c : CubicalStr G' L) (a b : G ⟶ G') [IsMonHom a] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x x' y : T ⟶ H) (ψ : Fin 3 → (T.left ⟶ (G2 H).left))
    (h₀ : ψ 0 = (lift (x * x') y : T ⟶ G2 H).left) (h₁ : ψ 1 = (lift x y : T ⟶ G2 H).left)
    (h₂ : ψ 2 = (lift x' y : T ⟶ G2 H).left) :
    ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' L.L).pull (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left).pull κ)
      (K := Fin 3) ψ ![1, -1, -1]), u.IsGen := by
  have hΛ : (abelian₂ G' L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have hP := pull_isLB (pull_isLB hΛ (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left) κ
  have key : ∀ p q : T ⟶ H, pull (lift p q : T ⟶ G2 H).left (cls _ hP) =
      pull (lift (pushHom hp T p ≫ a) (pushHom hp T q ≫ b) : Over.mk (T.hom ≫ f) ⟶ G2 G').left (cls _ hΛ) := by
    intro p q
    rw [cls_pull (pull_isLB hΛ _), cls_pull hΛ, ← pull_comp, ← pull_comp, lift_square hp hκ]
    refine congrArg (fun m => pull m (cls _ hΛ)) ?_
    refine congrArg (fun m : Over.mk (T.hom ≫ f) ⟶ G2 G' => m.left)
      (show lift (pushHom hp T p) (pushHom hp T q) ≫ lift (fst G G ≫ a) (snd G G ≫ b) = _ from ?_)
    simp
  refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
  rw [cls_linComb hP, Fin.sum_univ_three, h₀, h₁, h₂, key, key, key, map_mul, MonObj.mul_comp]
  have e := lam_add c hΛ (pushHom hp T x ≫ a) (pushHom hp T x' ≫ a) (pushHom hp T y ≫ b)
  refine Eq.trans ?_ e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    one_smul, neg_smul, sub_eq_add_neg]

end GlobalTheory.Mum.FactorAdd

theorem GlobalTheory.Mum.factorPairing_add : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F A' G' _ _ _ U' oA oG _ G _ _ _ inc pr hinc _ _ _ κ₀ hκ
  exact GlobalTheory.Mum.FactorAdd.exists_gen U'.cubG inc (inc ≫ oG.act F.f) (isGrpPullback_pullback G (jK R)) hκ
    (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) _ rfl rfl
    (by rw [lift_comp_fst_snd]; rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
section
noncomputable section

namespace GlobalTheory.InvAlg

theorem factorPow_evalₐ {A : Type} [CommRing A] (I : Ideal A) {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I A x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule A A) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {I : Ideal A} {J : Ideal B}
    (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono h n)

def adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I A →+* B ⧸ J ^ n :=
  (Ideal.quotientMap (J ^ n) f (pow_le_comap f h n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)

theorem factorPow_comp_adicCompletionMapToQuotientPow {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) {k n : ℕ} (hle : k ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (adicCompletionMapToQuotientPow f I J h n) = adicCompletionMapToQuotientPow f I J h k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionMapToQuotientPow, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) : AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J (adicCompletionMapToQuotientPow f I J h) (factorPow_comp_adicCompletionMapToQuotientPow f I J h)

theorem evalₐ_cmap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (cmap f I J h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap f h n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (factorPow_comp_adicCompletionMapToQuotientPow f I J h) n x

theorem cmap_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (h : I.map f ≤ J) (a : A) : cmap f I J h (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_cmap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem map_algebraMap_le {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    (g : B →ₐ[A] B') (J : Ideal A) : (J.map (algebraMap A B)).map (g : B →+* B') ≤ J.map (algebraMap A B') := by
  rw [Ideal.map_map, g.comp_algebraMap]

def galAlg {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) :
    R' →ₐ[R] R' :=
  { σ.1.toRingHom with commutes' := σ.2 }

def galTensor {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O] [Algebra R O]
    (σ : GlobalTheory.Mum.Gal (algebraMap R R')) : TensorProduct R O R' →ₐ[O] TensorProduct R O R' :=
  Algebra.TensorProduct.map (AlgHom.id O O) (galAlg σ)

@[simp] theorem galTensor_tmul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (O : Type) [CommRing O]
    [Algebra R O] (σ : GlobalTheory.Mum.Gal (algebraMap R R')) (x : O) (y : R') :
    galTensor O σ (x ⊗ₜ[R] y) = x ⊗ₜ[R] σ.1 y := rfl

end GlobalTheory.InvAlg
end
end

