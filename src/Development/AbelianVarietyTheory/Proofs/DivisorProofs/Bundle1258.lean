module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsLift

theorem surjective_algebraMap_of_finite_unramified : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T]
    [Algebra.FormallyUnramified R T], Function.Surjective (algebraMap R T) := by
  intro R _ _ _ T _ _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := T)
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  have hk : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  let N : Submodule R T := LinearMap.range (Algebra.linearMap R T)
  have hNN : (⊤ : Submodule R T) ≤ N ⊔ IsLocalRing.maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨c, hc⟩ := hk (IsLocalRing.residue T x)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    have hr : IsLocalRing.residue T (algebraMap R T r) = IsLocalRing.residue T x := by
      rw [← hc, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R)]
    have hx : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hr, sub_self]
    rw [← hm] at hx
    have hx' : x - algebraMap R T r ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R T) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    have : x = algebraMap R T r + (x - algebraMap R T r) := by ring
    rw [this]
    exact Submodule.add_mem_sup ⟨r, rfl⟩ hx'
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hNN
  intro y
  obtain ⟨r, hr⟩ := hle (Submodule.mem_top (x := y))
  exact ⟨r, hr⟩

theorem nonempty_algHom_residueField : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T],
    Nonempty (T →ₐ[R] IsLocalRing.ResidueField R) := by
  intro R _ _ _ T _ _ _ _
  haveI := GlobalTheory.isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T) :=
    inferInstance
  let l : IsLocalRing.ResidueField T →ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R :=
    IsAlgClosed.lift
  exact ⟨(l.restrictScalars R).comp (IsScalarTower.toAlgHom R T (IsLocalRing.ResidueField T))⟩

theorem exists_section_of_point : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (B : Type) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (K : Type) [Field K] (φ : R →+* K) (χ : B →+* K), χ.comp (algebraMap R B) = φ →
    ∃ ψ : B →+* R, ψ.comp (algebraMap R B) = RingHom.id R ∧ φ.comp ψ = χ := by
  intro R _ _ _ B _ _ _ _ K _ φ χ hχ
  classical
  obtain ⟨J, hJ, T, _, _, e, hT, hT'⟩ := GlobalTheory.finite_algebra_strictly_henselian_pi R B
  haveI := Fintype.ofFinite J
  let ε : J → B := fun i => e.symm (Pi.single i 1)
  have hεsum : ∑ i, ε i = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ε, ← map_sum, Finset.univ_sum_single]
    exact map_one e.symm
  have hεid : ∀ i, IsIdempotentElem (ε i) := fun i => by
    show e.symm _ * e.symm _ = e.symm _
    rw [← map_mul, ← Pi.single_mul, _root_.one_mul]

  have hfac : ∀ (L : Type) [CommRing L] (ω : B →+* L) (i : J), ω (ε i) = 1 →
      ∀ (x : B) (r : R), e x i = algebraMap R (T i) r → ω x = ω (algebraMap R B r) := by
    intro L _ ω i hωi x r hr
    have hx : x * ε i = algebraMap R B r * ε i := by
      apply e.injective
      funext j
      simp only [ε, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, Pi.mul_apply,
        Pi.algebraMap_apply]
      by_cases h : j = i
      · subst h; simp [hr]
      · simp [Pi.single_eq_of_ne h]
    have := congrArg ω hx
    rwa [map_mul, map_mul, hωi, _root_.mul_one, _root_.mul_one] at this
  obtain ⟨i, hi⟩ : ∃ i, χ (ε i) ≠ 0 := by
    by_contra h
    push_neg at h
    have := congrArg χ hεsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, h] at this
  have hi1 : χ (ε i) = 1 := (IsIdempotentElem.iff_eq_zero_or_one.1 ((hεid i).map χ)).resolve_left hi
  haveI : IsLocalRing (T i) := inferInstance
  haveI : Module.Finite R (T i) := (hT' i).2
  let π : B →ₐ[R] T i := (Pi.evalAlgHom R T i).comp e.toAlgHom
  have hπ : Function.Surjective π := fun y => ⟨e.symm (Pi.single i y), by simp [π]⟩
  haveI : Algebra.FormallyUnramified R (T i) := Algebra.FormallyUnramified.of_surjective π hπ
  have hsurj : Function.Surjective (algebraMap R (T i)) := surjective_algebraMap_of_finite_unramified R (T i)
  obtain ⟨β⟩ := nonempty_algHom_residueField R (T i)
  obtain ⟨ψ₀, hψ₀⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R B R).2 (β.comp π)
  have hψi : ψ₀ (ε i) = 1 := by
    have h1 : IsLocalRing.residue R (ψ₀ (ε i)) = 1 := by
      have := congrArg (fun g : B →ₐ[R] IsLocalRing.ResidueField R => g (ε i)) hψ₀
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at this
      rw [← IsLocalRing.ResidueField.algebraMap_eq, this]
      simp [π, ε]
    have hloc : ∀ a : R, IsIdempotentElem a → a = 0 ∨ a = 1 := fun a ha => by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
      · right; exact h.mul_left_cancel (by rw [ha.eq, _root_.mul_one])
      · left
        have h0 : (1 - a) * a = 0 := by rw [sub_mul, _root_.one_mul, ha.eq, sub_self]
        exact h.mul_right_eq_zero.1 h0
    rcases hloc _ ((hεid i).map ψ₀) with h | h
    · rw [h, map_zero] at h1; exact absurd h1.symm one_ne_zero
    · exact h
  refine ⟨ψ₀.toRingHom, ?_, ?_⟩
  · ext r; simp
  · ext x
    obtain ⟨r, hr⟩ := hsurj (e x i)
    have h1 : χ x = φ r := by
      rw [hfac K χ i hi1 x r hr.symm]
      show (χ.comp (algebraMap R B)) r = φ r
      rw [hχ]
    have h2 : ψ₀ x = r := by
      have := hfac R ψ₀.toRingHom i hψi x r hr.symm
      simpa using this
    show φ (ψ₀ x) = χ x
    rw [h1, h2]

theorem exists_iso_sp_of_finite_etale : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsFinite f → Etale f →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Algebra.Etale R B ∧ Module.Finite R B ∧
      ∃ e : X ≅ Sp B, e.hom ≫ spMap (algebraMap R B) = f := by
  intro R _ X f hf hfe
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let ρ : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom
  letI : Algebra R Γ(X, ⊤) := ρ.toAlgebra
  have key : X.isoSpec.hom ≫ spMap (algebraMap R Γ(X, ⊤)) = f := by
    have h := Scheme.isoSpec_hom_naturality f
    rw [Scheme.isoSpec_Spec_hom] at h
    show X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ) = f
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop from rfl,
      Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have hsp : spMap (algebraMap R Γ(X, ⊤)) = X.isoSpec.inv ≫ f := by
    rw [← key, Iso.inv_hom_id_assoc]
  have het : Etale (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  have hfi : IsFinite (spMap (algebraMap R Γ(X, ⊤))) := by rw [hsp]; infer_instance
  refine ⟨Γ(X, ⊤), inferInstance, inferInstance, ?_, ?_, X.isoSpec, key⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 het
  · exact (IsFinite.SpecMap_iff _).1 hfi

theorem preconnectedSpace_sp (R : Type) [CommRing R] [IsLocalRing R] : PreconnectedSpace (Sp R) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  have key : ∀ z : Sp R, z ⤳ (IsLocalRing.closedPoint R : PrimeSpectrum R) := fun z =>
    IsLocalRing.specializes_closedPoint (R := R) z
  by_cases h : (IsLocalRing.closedPoint R : PrimeSpectrum R) ∈ s
  · right; ext z; simp only [Set.mem_univ, iff_true]; exact (key z).mem_open hs.isOpen h
  · left; ext z; simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hz => h ((key z).mem_closed hs.isClosed hz)

theorem torsion_points_restrict_bijective : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (n : ℕ), 0 < n → IsUnit (n : Γ(S, ⊤)) →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (t : Sp R ⟶ S)
    (K : Type) [Field K] (φ : R →+* K),
    (∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g =
        (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ h → g = h) ∧
    ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 → ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧
      (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ t) ⟶ Over.mk t) ≫ g = x := by
  intro S A _ _ hA n _ hn R _ _ _ t K _ φ
  haveI := hA
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A hn
  haveI := hfin
  haveI := het
  haveI := preconnectedSpace_sp R
  let ψK : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let E := GlobalTheory.TorsionUnram.torsionEquiv A n
  refine ⟨fun g h hg hh hgh => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := (E _).surjective ⟨g, hg⟩
    obtain ⟨b, hb⟩ := (E _).surjective ⟨h, hh⟩
    have ga : a ≫ torsion.ι A n = g := congrArg Subtype.val ha
    have gb : b ≫ torsion.ι A n = h := congrArg Subtype.val hb
    have hab : ψK ≫ a = ψK ≫ b := by
      apply (E _).injective
      apply Subtype.ext
      show (ψK ≫ a) ≫ torsion.ι A n = (ψK ≫ b) ≫ torsion.ι A n
      rw [Category.assoc, Category.assoc, ga, gb]
      exact hgh
    have hab' : spMap φ ≫ a.left = spMap φ ≫ b.left := congrArg (fun u => u.left) hab
    haveI : PreconnectedSpace (Over.mk t).left := preconnectedSpace_sp R
    have : a = b := GlobalTheory.over_eq_of_preconnected_of_unramified (spMap φ) hab'
    rw [← ga, ← gb, this]
  · obtain ⟨y, hy⟩ := (E _).surjective ⟨x, hx⟩
    have yx : y ≫ torsion.ι A n = x := congrArg Subtype.val hy
    obtain ⟨B, _, _, _, _, e, he⟩ :=
      exists_iso_sp_of_finite_etale R _ (pullback.snd (torsion A n).hom t) inferInstance inferInstance
    let q : Sp K ⟶ Sp B := pullback.lift y.left (spMap φ) (Over.w y) ≫ e.hom
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective q
    have hq : q ≫ spMap (algebraMap R B) = spMap φ := by
      simp only [q, Category.assoc, he, pullback.lift_snd]
    have hχ : χ'.hom.comp (algebraMap R B) = φ := by
      have h0 : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ χ') =
          Spec.map (CommRingCat.ofHom φ) := by
        rw [Spec.map_comp, hχ']
        exact hq
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
    obtain ⟨ψ, hψ1, hψ2⟩ := exists_section_of_point R B K φ χ'.hom hχ
    let s : Sp R ⟶ (torsion A n).left := spMap ψ ≫ e.inv ≫ pullback.fst _ _
    have h1 : e.inv ≫ pullback.snd (torsion A n).hom t = spMap (algebraMap R B) := by
      rw [← he, Iso.inv_hom_id_assoc]
    have hs : s ≫ (torsion A n).hom = t := by
      simp only [s, Category.assoc, pullback.condition]
      rw [reassoc_of% h1, ← Category.assoc, ← GlobalTheory.TorsionUnram.spMap_comp', hψ1]
      show Spec.map (CommRingCat.ofHom (RingHom.id R)) ≫ t = t
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    let gs : Over.mk t ⟶ torsion A n := Over.homMk s hs
    refine ⟨gs ≫ torsion.ι A n, ((E _) gs).2, ?_⟩
    have h2 : spMap φ ≫ spMap ψ = q := by
      rw [← GlobalTheory.TorsionUnram.spMap_comp', hψ2, ← hχ']
      rfl
    have hy' : ψK ≫ gs = y := by
      apply Over.OverMorphism.ext
      show spMap φ ≫ s = y.left
      simp only [s, ← Category.assoc]
      rw [h2]
      simp only [q, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
    rw [← Category.assoc, hy', yx]

end GlobalTheory.TorsLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLe
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MajMul

theorem maj_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x := by
  intro D θ hθ V n Q hQ K hK
  obtain ⟨K', hK', hbox⟩ := _root_.GlobalTheory.BoxMove.inBox_image_mul D V n Q hQ K hK
  obtain ⟨C₀, hC₀, hreal⟩ := _root_.GlobalTheory.Unf.RealMove.realSize_le_of_isCompact D θ hθ V n Q hQ
  refine ⟨K', hK', fun N => ⟨C₀ ^ N, by positivity, fun y hy x => ?_⟩⟩
  set z : Mx D V.rank n := HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x with hz
  unfold GlobalTheory.Unf.maj
  by_cases hin : GlobalTheory.Unf.InBox K z
  · rw [if_pos hin, if_pos (hbox y hy x hin)]
    have h0 := GlobalTheory.Unf.realSize_nonneg θ z
    have h1 := GlobalTheory.Unf.realSize_nonneg θ x
    have h2 := hreal y hy x
    have h3 : 1 + GlobalTheory.Unf.realSize θ x ≤ C₀ * (1 + GlobalTheory.Unf.realSize θ z) := by nlinarith
    have hp : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
    have hq : (0:ℝ) < (1 + GlobalTheory.Unf.realSize θ z) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hq hp, one_mul]
    calc (1 + GlobalTheory.Unf.realSize θ x) ^ N ≤ (C₀ * (1 + GlobalTheory.Unf.realSize θ z)) ^ N := by gcongr
      _ = C₀ ^ N * (1 + GlobalTheory.Unf.realSize θ z) ^ N := by rw [mul_pow]
  · rw [if_neg hin]
    have := GlobalTheory.Unf.maj_nonneg θ K' N x
    unfold GlobalTheory.Unf.maj at this
    have hC : (0:ℝ) ≤ C₀ ^ N := by positivity
    exact mul_nonneg hC this

end GlobalTheory.MajMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dite_eq_right hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem inBlock_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.PGEquiv F → (R.toCx3 F).zs.InBlock := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hC hE hG
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block R F hL hOk hC hE (schurAll_of_cuspRapidDecay hP R.toRealDat) hG
  have hM := hC.base.models
  refine ⟨fun t x hx => ?_, fun j t x hx => ?_⟩
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HX t
    have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx' : R.jX t x ∈ LinearMap.range (LinearMap.adjoint (R.Th t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.Th t) (R.jX t x)).1 hx
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jX t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h1 t hx')
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L j t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HV j t
    have h := kForm_semi (R.jV j t) (R.HV j t).e (R.B.L j t).pres.extL (fun x => hM.jV j t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx1 := range_adjoint_smul_le (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hx
    have hx' : R.jV j t x ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t x)).1 hx1
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jV j t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h2 j t hx')

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicMorseExistsSectionAmpleSubGeneratedStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_morse_exists_section_ample_sub_generated : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  first | exact @GlobalTheory.exists_sec_of_ample_sub_generated | exact GlobalTheory.exists_sec_of_ample_sub_generated | (intros; apply GlobalTheory.exists_sec_of_ample_sub_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPosStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) → ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  first | exact @GlobalTheory.AmplePos.topSelf_pos | exact GlobalTheory.AmplePos.topSelf_pos | (intros; apply GlobalTheory.AmplePos.topSelf_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorizationStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_frame_character_factorization : GlobalTheory.FunPr.Hypotheses₂ →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → At (evI F) ((h.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @GlobalTheory.RealLift.CharTrace.deriv_char | exact GlobalTheory.RealLift.CharTrace.deriv_char | (intros; apply GlobalTheory.RealLift.CharTrace.deriv_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzIntegralMulStarNeZeroStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartz_integral_mul_star_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f : SInf F κ), f ≠ 0 →
    (∫ x : κ → mixedEmbedding.mixedSpace F, f x * star (f x)) ≠ 0 := by
  first | exact @GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | exact GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero | (intros; apply GlobalTheory.L2InnerProductNonvanishing.integral_mul_star_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompMemKinfEquivariantAutomorphicMapsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W) (T : W →ₗ[ℂ] Sm E a), T ∈ maps L W hW → ∀ z ∈ Zalg E a, z ∘ₗ T ∈ maps L W hW := by
  first | exact @GlobalTheory.AutGrowth.comp_mem_maps | exact GlobalTheory.AutGrowth.comp_mem_maps | (intros; apply GlobalTheory.AutGrowth.comp_mem_maps <;> assumption)
end

