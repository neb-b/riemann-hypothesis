module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

namespace ClosedInj

theorem epi_spMap_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (io : Ω →+* Ω') : Epi (spMap io) := by
  have : Flat (spMap io) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := io.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (spMap io) := ⟨fun t ↦ ⟨IsLocalRing.closedPoint Ω', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_residue_factor {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] (y : Sp Ω ⟶ Sp R)
    (hy : ∀ t, y t = closedPoint R) : ∃ κ : ResidueField R →+* Ω, y = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage y).hom with hφ
  have hyφ : y = spMap φ := (Spec.map_preimage y).symm
  have hker : ∀ a : R, a ∈ maximalIdeal R → φ a = 0 := by
    intro a ha
    have h1 := hy (IsLocalRing.closedPoint Ω)
    rw [hyφ] at h1
    have h2 : (PrimeSpectrum.comap φ (IsLocalRing.closedPoint Ω)).asIdeal = maximalIdeal R := by
      exact congrArg PrimeSpectrum.asIdeal h1
    rw [← h2] at ha
    have : φ a ∈ maximalIdeal Ω := ha
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at this
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have := hker a ((IsLocalRing.mem_maximalIdeal a).2 h)
    rw [this] at ha
    exact not_isUnit_zero ha⟩
  exact ⟨ResidueField.lift φ, by rw [ResidueField.lift_comp_residue]; exact hyφ⟩

end ClosedInj


open ClosedInj in
theorem Emb.eq_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  intro R _ _ _ M G' _ E Ω _ p p' hcl hs hf
  set s : Sp Ω ⟶ M.S := p ≫ E.H.ι ≫ G'.hom with hsdef
  obtain ⟨κ, hκ⟩ := exists_residue_factor (s ≫ M.π) (fun t => by simpa [s] using hcl t)
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω s κ hκ
  let q : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p ≫ E.H.ι) (𝟙 _) (by simp [s])
  let q' : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p' ≫ E.H.ι) (𝟙 _) (by simp [s, hs])
  have hq : q ≫ l = spMap io ≫ p := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hq' : q' ≫ l = spMap io ≫ p' := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hfst : q ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
      q' ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) := by
    have := E.imm
    rw [← cancel_mono E.j]
    simp only [Category.assoc]
    rw [← hlf, ← Category.assoc q, hq, ← Category.assoc q', hq', Category.assoc, Category.assoc, hf]
  have hw : e.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ s) :=
    Over.w e.hom
  have hqe : q ≫ e.hom.left = q' ≫ e.hom.left := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simp only [Category.assoc]
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hqq : q = q' := by
    have := congrArg (· ≫ e.inv.left) hqe
    simpa [← Over.comp_left] using this
  have h2 : spMap io ≫ p = spMap io ≫ p' := by rw [← hq, ← hq', hqq]
  have := epi_spMap_field io
  exact (cancel_epi (spMap io)).1 h2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivRegularFunctionsAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPerImm

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ z ∈ pre u.ex U, ∀ w : Fin g → ℂ, (∀ b : Γ(A.left, U), fderiv ℂ (val u.ex U b) z w = 0) → w = 0 := by
  intro A _ g L u _ U hU z hz w hw
  refine GlobalTheory.HolUnifSec.eq_zero_of_fderiv_eq_zero u z w fun O f hO => ?_
  have hzU : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U := hz
  have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ O ⊓ U :=
    (GlobalTheory.top_le_preimage_iff_mem _ _).1 ((GlobalTheory.top_le_preimage_inf _ O U).2 ⟨hO, hzU⟩)
  obtain ⟨r, hrle, hrmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨_, hmem⟩ hmem.2
  have hDO : A.left.basicOpen r ≤ O := hrle.trans inf_le_left
  have hDU : A.left.basicOpen r ≤ U := A.left.basicOpen_le r
  letI := (A.left.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  haveI := hU.isLocalization_basicOpen r
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj r (resG A.left hDO f)
  let P : Set (Fin g → ℂ) := {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ A.left.basicOpen r}
  have hP : IsOpen P := (u.hol _ 0).1
  have hzP : z ∈ P := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hrmem
  set F := fun y => valAt' (u.ex y).left O f
  set R := fun y => valAt' (u.ex y).left U r
  set B := fun y => valAt' (u.ex y).left U b
  have key : ∀ y ∈ P, F y * R y ^ n = B y := by
    intro y hy
    have h1 := congrArg (valAt' (u.ex y).left (A.left.basicOpen r)) hb
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_pow _ hy] at h1
    have e1 : valAt' (u.ex y).left (A.left.basicOpen r) (resG A.left hDO f) = F y := GlobalTheory.valAt'_res _ hDO f hy
    have e2 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ r) = R y := GlobalTheory.valAt'_res _ hDU r hy
    have e3 : valAt' (u.ex y).left (A.left.basicOpen r) (algebraMap Γ(A.left, U) _ b) = B y := GlobalTheory.valAt'_res _ hDU b hy
    rw [e1, e2, e3] at h1
    exact h1
  have hpreO : IsOpen {y | ⊤ ≤ (u.ex y).left ⁻¹ᵁ O} := (u.hol O f).1
  have hF : HasFDerivAt F (fderiv ℂ F z) z :=
    (((u.hol O f).2 z hO).differentiableAt (hpreO.mem_nhds hO)).hasFDerivAt
  have hR : HasFDerivAt R (fderiv ℂ R z) z :=
    (((u.hol U r).2 z hzU).differentiableAt ((u.hol U r).1.mem_nhds hzU)).hasFDerivAt
  have hB : HasFDerivAt B (fderiv ℂ B z) z :=
    (((u.hol U b).2 z hzU).differentiableAt ((u.hol U b).1.mem_nhds hzU)).hasFDerivAt
  have hFR := hF.mul (hR.pow n)
  have hev : (fun y => F y * R y ^ n) =ᶠ[nhds z] B :=
    Filter.eventually_of_mem (hP.mem_nhds hzP) key
  have hB' := hFR.congr_of_eventuallyEq hev.symm
  have e := congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T w) (hB'.unique hB)
  have hRw : fderiv ℂ R z w = 0 := hw r
  have hBw : fderiv ℂ B z w = 0 := hw b
  have hRz : R z ≠ 0 := (GlobalTheory.top_le_preimage_basicOpen_iff _ U r).1 hzP
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hRw, hBw, smul_zero, smul_eq_mul,
    mul_zero, zero_add] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hRz)

end GlobalTheory.CechPerImm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalisationOfEtaleAffineFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.AffFib

theorem etale_basicOpen_iff (S R : CommRingCat.{0}) (θ : S ⟶ R) (f : R) :
    Etale ((show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := by
  have e : (show (Spec R).Opens from PrimeSpectrum.basicOpen f).ι ≫ Spec.map θ =
      (basicOpenIsoSpecAway f).hom ≫ Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [Spec.map_comp, ← Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [e]
  have key : Etale (Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ↔
      ((algebraMap R (Localization.Away f)).comp θ.hom).Etale := HasRingHomProperty.Spec_iff (P := @Etale)
  rw [← key]
  constructor
  · intro H
    have e2 : Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f))) =
        (basicOpenIsoSpecAway f).inv ≫ ((basicOpenIsoSpecAway f).hom ≫
          Spec.map (θ ≫ CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
      (Iso.inv_hom_id_assoc _ _).symm
    rw [e2]; infer_instance
  · intro H; infer_instance

end GlobalTheory.Mum.AffFib

theorem GlobalTheory.Mum.etale_localisation_of_etale_affine_fibre : ∀ (A C B : CommRingCat.{0}) (φ : A ⟶ C) (ψ : C ⟶ B) (Ω : Type) [Field Ω] (ω : A ⟶ CommRingCat.of Ω) (W : (pullback (Spec.map (φ ≫ ψ)) (Spec.map ω)).Opens) (w : ↥(pullback (Spec.map (φ ≫ ψ)) (Spec.map ω))), w ∈ W → Etale (W.ι ≫ pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _) (by simp [Spec.map_comp]) (by simp)) → letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra; letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl); ∃ (Q' : Ideal (TensorProduct A Ω B)) (_ : Q'.IsPrime) (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = (pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w).asIdeal ∧ f ∉ Q' ∧ ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale := by
  intro A C B φ ψ Ω _ ω W w hw hE
  letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra; letI := (φ ≫ ψ).hom.toAlgebra; letI := ω.hom.toAlgebra
  letI : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set F := pullback.map (Spec.map (φ ≫ ψ)) (Spec.map ω) (Spec.map φ) (Spec.map ω) (Spec.map ψ) (𝟙 _) (𝟙 _)
    (by simp [Spec.map_comp]) (by simp) with hFdef
  haveI := hE
  let θ := Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)
  let θc : CommRingCat.of (TensorProduct A Ω C) ⟶ CommRingCat.of (TensorProduct A Ω B) :=
    CommRingCat.ofHom θ.toRingHom
  have pB : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω B)))
      (Spec.map (φ ≫ ψ)) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω B)).flip
  have pC : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] TensorProduct A Ω C).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Ω →+* TensorProduct A Ω C)))
      (Spec.map φ) (Spec.map ω) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ω C)).flip
  let eB := pB.isoPullback
  let eC := pC.isoPullback
  have hF : eB.hom ≫ F = Spec.map θc ≫ eC.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, hFdef, pullback.lift_fst,
        ← Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
    · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd, hFdef, pullback.lift_snd,
        ← Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp, Category.comp_id]
      congr 1
      ext c
      simp [θc, θ]
  have hθ : Spec.map θc = eB.hom ≫ F ≫ eC.inv := by
    rw [← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let U : (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens := eB.hom ⁻¹ᵁ W
  let y := eB.inv w
  have hy : y ∈ U := by
    show eB.hom (eB.inv w) ∈ W
    simpa using hw
  obtain ⟨_, ⟨f, rfl⟩, hyf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy U.2
  have hD : (show (Spec (CommRingCat.of (TensorProduct A Ω B))).Opens from PrimeSpectrum.basicOpen f) ≤ U := hfU
  refine ⟨y.asIdeal, y.isPrime, f, ?_, (PrimeSpectrum.mem_basicOpen f y).1 hyf, ?_⟩
  · have : pullback.fst (Spec.map (φ ≫ ψ)) (Spec.map ω) w =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B).toRingHom) y := by
      rw [← pB.isoPullback_hom_fst]
      show _ = (eB.hom ≫ pullback.fst _ _) (eB.inv w)
      simp
    rw [this]
    rfl
  · refine (GlobalTheory.Mum.AffFib.etale_basicOpen_iff _ _ θc f).1 ?_
    rw [hθ, ← Scheme.homOfLE_ι _ hD]
    have e1 : (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ U.ι ≫ eB.hom ≫ F ≫ eC.inv =
        (Spec (CommRingCat.of (TensorProduct A Ω B))).homOfLE hD ≫ (eB.hom ∣_ W) ≫ (W.ι ≫ F) ≫ eC.inv := by
      rw [← Category.assoc (U.ι), ← morphismRestrict_ι]
      simp only [Category.assoc]
    rw [Category.assoc, e1]
    infer_instance
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNhdsAffineSpaceMapOfFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleAtDescent

open TensorProduct

theorem notMem_support_of_flat {B D M N : Type} [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module D N] [IsScalarTower B D N]
    (φ : M →ₗ[B] N) (hφ : Function.Injective (φ.liftBaseChange D)) (Q : PrimeSpectrum D)
    (hQ : Q ∉ Module.support D N) : PrimeSpectrum.comap (algebraMap B D) Q ∉ Module.support B M := by
  rw [Module.notMem_support_iff'] at hQ ⊢
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨f, hf, hfx⟩ := hQ (φ x)
  have h0 : f ⊗ₜ[B] x = 0 := hφ (by simpa using hfx)
  have hex := Module.Flat.lTensor_exact D (LinearMap.exact_subtype_ker_map (LinearMap.toSpanSingleton B M x))
  obtain ⟨z, hz⟩ := (hex (f ⊗ₜ[B] 1)).1 (by simpa using h0)
  have key : ∀ z : D ⊗[B] LinearMap.ker (LinearMap.toSpanSingleton B M x),
      TensorProduct.rid B D (LinearMap.lTensor D (LinearMap.ker (LinearMap.toSpanSingleton B M x)).subtype z) ∈
        Q.asIdeal := by
    intro z
    induction z with
    | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact Q.asIdeal.add_mem ha hb
    | tmul d r =>
      have hr : algebraMap B D r.1 ∈ Q.asIdeal := by
        by_contra h
        exact hx r.1 h (LinearMap.mem_ker.1 r.2)
      simpa [Algebra.smul_def] using Q.asIdeal.mul_mem_right d hr
  have := key z
  rw [hz] at this
  exact hf (by simpa using this)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem mem_etaleLocus_of_flat {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] (Q : PrimeSpectrum (C ⊗[A] B)) (hQ : Q ∈ Algebra.etaleLocus C (C ⊗[A] B)) :
    PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) Q ∈ Algebra.etaleLocus A B := by
  rw [Algebra.etaleLocus_eq_compl_support] at hQ ⊢
  haveI : Module.Flat B (C ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A B C (C ⊗[A] B)).toLinearEquiv.symm
  refine ⟨notMem_support_of_flat (KaehlerDifferential.map A C B (C ⊗[A] B)) ?_ Q hQ.1,
    notMem_support_of_flat (Algebra.H1Cotangent.map A C B (C ⊗[A] B)) ?_ Q hQ.2⟩
  · have hc : (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B) : _ → _) =
        (KaehlerDifferential.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) Ω[B⁄A]).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, Function.comp_apply,
          Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B)).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)
  · have hc : (Algebra.tensorH1CotangentOfFlat A B C : _ → _) =
        (Algebra.H1Cotangent.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) (Algebra.H1Cotangent A B)).symm := by
      funext z
      induction z with
      | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [Algebra.tensorH1CotangentOfFlat_tmul, Function.comp_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (Algebra.tensorH1CotangentOfFlat A B C).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exists_etale_spec {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] [Algebra.FinitePresentation A B] (W : (Spec (.of (C ⊗[A] B))).Opens)
    (p : Spec (.of (C ⊗[A] B))) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))) :
    ∃ V : (Spec (.of B)).Opens, Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) p ∈ V ∧
      Etale (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap (C ⊗[A] B) (Localization.Away f)))
  have hj : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    refine subset_trans ?_ hf
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le
  have h1 : Etale (IsOpenImmersion.lift W.ι j hj ≫ W.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) := inferInstance
  rw [IsOpenImmersion.lift_fac_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
    HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap] at h1
  have h2 := mem_etaleLocus_of_flat p (Algebra.basicOpen_subset_etaleLocus_iff_etale.2 h1 hpf)
  rw [Algebra.mem_etaleLocus_iff] at h2
  obtain ⟨g, hg, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A)
    (PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) p).asIdeal
  let i := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  refine ⟨i.opensRange, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge hg
  · have h3 : Etale (i ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
      exact hE
    rw [← i.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

theorem exists_etale_of_isAffine {U T S : Scheme.{0}} [IsAffine S] (τ : U ⟶ S) (h : T ⟶ S)
    [LocallyOfFinitePresentation τ] [Flat h] (W : (pullback τ h).Opens) (p : ↥(pullback τ h)) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ pullback.snd τ h)) : ∃ V : U.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  obtain ⟨B, i, _, q, hq⟩ := U.exists_Spec_apply_eq (pullback.fst τ h p)
  obtain ⟨C, k, _, t, ht⟩ := T.exists_Spec_apply_eq (pullback.snd τ h p)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ τ ≫ S.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ h ≫ S.isoSpec.hom)
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  letI : Algebra B (C ⊗[Γ(S, ⊤)] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.FinitePresentation Γ(S, ⊤) B := by
    have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 this
  haveI : Module.Flat Γ(S, ⊤) C := by
    have : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) (Spec.map φ) (Spec.map ψ) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) C B)).flip
  let m := pullback.map (Spec.map φ) (Spec.map ψ) τ h i k S.isoSpec.inv (by simp [hφ]) (by simp [hψ])
  have hm : IsOpenImmersion m := inferInstance
  have hpm : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨q, hq⟩, ⟨t, ht⟩⟩
  let j := hpb.isoPullback.hom ≫ m
  have j1 : j ≫ pullback.fst τ h = Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))) ≫ i := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
  have j2 : j ≫ pullback.snd τ h = Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B))) ≫ k := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨p', rfl⟩ : ∃ p', j p' = p := by
    obtain ⟨p₀, rfl⟩ := hpm
    obtain ⟨p₁, rfl⟩ := hpb.isoPullback.hom.surjective p₀
    exact ⟨p₁, by simp [j]⟩
  have h1 : Etale ((j ∣_ W) ≫ W.ι ≫ pullback.snd τ h) := inferInstance
  rw [morphismRestrict_ι_assoc, j2, ← Category.assoc] at h1
  have h2 := Etale.of_comp ((j ⁻¹ᵁ W).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) k
  obtain ⟨V, hV, hE⟩ := exists_etale_spec (j ⁻¹ᵁ W) p' hp h2
  refine ⟨i ''ᵁ V, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, j1, Scheme.Hom.comp_apply]
    exact ⟨_, hV, rfl⟩
  · have hE' : Etale (V.ι ≫ Spec.map φ) := hE
    have e : (i ''ᵁ V).ι ≫ τ = (i.isoImage V).inv ≫ (V.ι ≫ Spec.map φ) ≫ S.isoSpec.inv := by
      simp [hφ]
    rw [e]
    infer_instance

theorem etale_nhds_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  intro R _ _ _ hR U g τ hU hτ T h hh W p hp hW
  haveI := hR.1
  haveI : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hU
  haveI : LocallyOfFiniteType τ := locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  haveI : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  exact exists_etale_of_isAffine τ h W p hp hW

end GlobalTheory.EtaleAtDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyRelAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.Mum.PosMult

theorem eventually_relAmple : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (a : P.A ⟶ P.A), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]) := by
  intro R _ P a
  have := P.isAb.proper
  have hL := P.isLB
  have hA : IsAmpleLB P.L := isAmpleLB_of_relAmple_of_isAffine P.A hL P.ample
  have hNb : (LB.LinComb P.L (K := Fin 1) ![a.left] ![-1]).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hA.eventually_isAmpleLB_tens_lbPow_succ hNb)
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have key := hn₀ (N - 1) (by omega)
  have hN1 : N - 1 + 1 = N := by omega
  rw [hN1] at key
  have hM := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P.A.left, a.left] ![(N : ℤ), -1]
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM]
  refine key.of_lbIso hM ((cls_eq_iff hM (isLB_tens hNb (isLB_lbPow hL N))).1 ?_)
  rw [cls_tens hNb (isLB_lbPow hL N), cls_lbPow hL, cls_linComb hL, cls_linComb hL]
  simp [Fin.sum_univ_two, pull_id]
  abel

theorem exists_pos_mult : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧ ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 → (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) → (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) → (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) → ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y) := by
  intro R _ _ _ hR D a a' h h' _
  obtain ⟨N₀, hN₀⟩ := eventually_relAmple R D.toPre.P a
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound D.toPre.X h h'
  refine ⟨max N₀ (C + 1), le_trans (by omega) (le_max_right _ _), hN₀ _ (le_max_left _ _), ?_⟩
  exact _root_.GlobalTheory.exists_pow_eq_mul_of_quadratic_bound R hR D.toPre.X h h' C hC _ (le_max_right _ _)

end GlobalTheory.Mum.PosMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  first | (exact @GlobalTheory.CycAwayCover.exists_cycAway_cover) | (exact GlobalTheory.CycAwayCover.exists_cycAway_cover) | (intros; apply GlobalTheory.CycAwayCover.exists_cycAway_cover  <;> assumption)
end

