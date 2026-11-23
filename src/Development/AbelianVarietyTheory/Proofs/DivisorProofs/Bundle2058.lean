module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
section
open IsLocalRing TensorProduct

noncomputable section

namespace GlobalTheory

def intDerivationOfLeibniz {A M : Type} [CommRing A] [AddCommGroup M] {instZA : Algebra ℤ A}
    {_ : Module A M} {instZM : Module ℤ M} (f : A →+ M) (h : ∀ a b, f (a * b) = a • f b + b • f a) :
    Derivation ℤ A M :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      obtain rfl : instZM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
      obtain rfl : instZA = Ring.toIntAlgebra A := Subsingleton.elim _ _
      exact map_zsmul f c x
    map_one_eq_zero' := by
      have h1 := h 1 1
      rw [one_mul, one_smul] at h1
      simpa using h1
    leibniz' := h }

theorem derivation_extend_completion_localization_atPrime (S : Type) [CommRing S] (P : Ideal S)
    [P.IsPrime] (d : Derivation ℤ S S) :
    ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
      (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)),
      ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ S (Localization.AtPrime P) P
    (intDerivationOfLeibniz
      ((algebraMap S (Localization.AtPrime P)).toAddMonoidHom.comp d.toLinearMap.toAddMonoidHom)
      (fun a b => by simp [d.leibniz, Algebra.smul_def]))
  have hadd : ∀ y z, BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D' (y + z) =
      BK.complDerFun _ D' y + BK.complDerFun _ D' z := fun y z => by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) y)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) z)
    rw [BK.evalₐ_complDerFun _ D' (r := r + t) (by rw [map_add (f := _), map_add (f := _), hr, ht]), map_add (f := _),
      map_add, map_add, BK.evalₐ_complDerFun _ D' hr.symm, BK.evalₐ_complDerFun _ D' ht.symm]
  refine ⟨intDerivationOfLeibniz
    { toFun := BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D'
      map_zero' := by
        have h0 := hadd 0 0
        rw [add_zero] at h0
        simpa using h0
      map_add' := hadd }
    (fun a b => by simpa [smul_eq_mul] using BK.complDerFun_mul _ D' a b),
    fun x => ?_⟩
  have h2 := BK.complDerFun_algebraMap (maximalIdeal (Localization.AtPrime P)) D'
    (algebraMap S (Localization.AtPrime P) x)
  rw [hD'] at h2
  exact h2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormal
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := _root_.GlobalTheory.NormSheafDescent.isField_stalk_genPt Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := _root_.GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.Desc

theorem exists_desc_specStalk : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R)
    (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' →
    QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ →
    ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁)
      (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) →
    u₁ ≫ pZ = φ₁ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) →
    ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧
      ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
        t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  intro R _ _ f hf x S₁ B Z B₀ B₁ ξ' hξf hξs hξq pB pZ hpB hpZ φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ hu₁ H
  have hs : Flat ((Sp R).fromSpecStalk x) := GenericExt.flat_fromSpecStalk _ x
  let π : B₁ ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
    pullback.lift φ₁ (q₁ ≫ ξ') (by rw [h₁.w, Category.assoc])
  have hπ₁ : π ≫ pullback.fst _ _ = φ₁ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = q₁ ≫ ξ' := pullback.lift_snd _ _ _
  have hsq : IsPullback π q₁ (pullback.snd pB ((Sp R).fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ₂ (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x))
    rw [hπ₁]; exact h₁
  have : Flat π := MorphismProperty.of_isPullback hsq.flip hξf
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip hξs
  have : QuasiCompact π := MorphismProperty.of_isPullback hsq.flip hξq
  have : Flat φ₁ := by rw [← hπ₁]; infer_instance
  have key : pullback.fst π π ≫ u₁ = pullback.snd π π ≫ u₁ := by
    let g : pullback π π ⟶ Sp R := pullback.fst π π ≫ φ₁ ≫ pB
    have hg : Flat g := inferInstance
    have hφ : pullback.fst π π ≫ φ₁ = pullback.snd π π ≫ φ₁ := by
      rw [← hπ₁, pullback.condition_assoc]
    have hAf : IsSchemeTheoreticallyDominant (awayMap f) :=
      schDom_spec_map _ (IsLocalization.injective (Localization.Away f)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf))
    have hdom : IsSchemeTheoreticallyDominant (pullback.fst g (awayMap f)) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback g (awayMap f)).flip
    refine ext_of_schDom pZ ?_ (pullback.fst g (awayMap f)) ?_
    · simp only [Category.assoc, hu₁]; exact (reassoc_of% hφ) pB
    · let t₀ : pullback g (awayMap f) ⟶ B₀ :=
        h₀.lift (pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁) (pullback.snd g (awayMap f))
          (by simpa [g] using pullback.condition (f := g) (g := awayMap f))
      have ht₀ : t₀ ≫ φ₀ = pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁ := h₀.lift_fst _ _ _
      have e₁ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.fst π π) (by rw [ht₀, Category.assoc])
      have e₂ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.snd π π) (by rw [ht₀, Category.assoc, hφ])
      simp only [Category.assoc] at e₁ e₂
      rw [← e₁, ← e₂]
  have hE : EffectiveEpi π := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let u := EffectiveEpi.desc π u₁ (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hu : π ≫ u = u₁ := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨u, ?_, ?_⟩
  · rw [← cancel_epi π, reassoc_of% hu, hu₁, reassoc_of% hπ₁]
  · intro T t₀ t ht
    have : Epi (pullback.fst t π) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.fst t π), pullback.condition_assoc, hu]
    have := H _ (pullback.fst t π ≫ t₀) (pullback.snd t π) (by
      rw [Category.assoc, ht, pullback.condition_assoc, hπ₁])
    simpa only [Category.assoc] using this

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.DualBasis

open GlobalTheory.LieVB GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.Pdiv (LieG ptMap dualScale specO)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_of_isTangent {w : epsR R ⟶ G} (hw : IsTangent w) :
    ptMap (TrivSqZeroExt.fstHom R R R) ≫ (w : specO R (DualNumber R) ⟶ G) = toUnit (specO R R) ≫ η[G] := by
  have h : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h]
  exact hw.trans (Category.id_comp _).symm

theorem isTangent_val (x : LieG G) : IsTangent (G := G) x.1 := sec_epsZero_comp x

theorem exists_prod [QuasiSeparated G.hom] (l : List (LieG G)) :
    ∃ p : LieG G, p.1 = (l.map (·.1)).prod ∧ tangent p = (l.map tangent).sum := by
  induction l with
  | nil =>
    refine ⟨⟨1, ?_⟩, rfl, ?_⟩
    · exact comp_one _
    · refine dual_ext fun W _ s => ?_
      have e : cotMap (1 : specO R (DualNumber R) ⟶ G) (epsZero_comp ⟨1, comp_one _⟩) = 0 := cotMap_eq_zero rfl _
      rw [List.map_nil, List.sum_nil]
      exact (congr((epsIso R).hom.app W (($e).app W s))).trans (map_zero _)
  | cons x l ih =>
    obtain ⟨p, hp, hp'⟩ := ih
    refine ⟨⟨x.1 * p.1, OmegaGlobal.fst_mul x p⟩, by simp [hp], ?_⟩
    rw [tangent_mul, hp', List.map_cons, List.sum_cons]

theorem isLieComb_iff [QuasiSeparated G.hom] {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G) :
    IsLieComb (G := G) a (fun i => (v i).1) w.1 ↔ tangent w = ∑ i, cst R (a i) • tangent (v i) := by
  let u : Fin n → LieG G := fun i => ⟨ptMap (dualScale (a i)) ≫ (v i).1, OmegaGlobal.fst_scale (a i) (v i)⟩
  have hu (i : Fin n) : (u i).1.left = spMap (epsScaleR (a i)) ≫ (v i).1.left := by
    have ha : (dualScale (a i)).toRingHom = epsScaleR (a i) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v i).1.left) ha
  obtain ⟨p, hp, hp'⟩ := exists_prod (List.ofFn u)
  rw [List.map_ofFn] at hp hp'
  rw [List.sum_ofFn] at hp'
  have hs : tangent p = ∑ i, cst R (a i) • tangent (v i) :=
    hp'.trans (Finset.sum_congr rfl fun i _ => tangent_scale (a i) (v i) _)
  constructor
  · rintro ⟨u', hu', e⟩
    obtain rfl : u' = fun i => (u i).1 := funext fun i => Over.OverMorphism.ext ((hu' i).trans (hu i).symm)
    obtain rfl : w = p := Subtype.ext (e.trans hp.symm)
    exact hs
  · intro e
    obtain rfl : w = p := tangent_injective R G (e.trans hs.symm)
    exact ⟨fun i => (u i).1, hu, hp⟩

theorem exists_dual_of_isFrame [QuasiSeparated G.hom] {n : ℕ} {e : Fin n → Γ(omega G, ⊤)} (he : IsFrame e) :
    ∃ v : Fin n → LieG G, (∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0) ∧
      IsLieBasis (G := G) fun j => (v j).1 := by
  choose v hv using fun j => TangentSurj.tangent_surjective R G (he.coord j)
  refine ⟨v, fun j k => ?_, fun j => isTangent_val (v j), fun w hw => ?_⟩
  · have h := he.dualApp_coord_frame j k le_rfl
    rw [Twist.resM_self] at h
    rw [hv]
    exact h.trans (if_congr eq_comm rfl rfl)
  · have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
    let b := he.dual.basis le_rfl
    have hb (j : Fin n) : b j = tangent (v j) := by
      rw [hv]
      exact (IsFrame.basis_apply _ _ _).trans (Twist.resM_self _ _)
    have key (a : Fin n → R) := isLieComb_iff a v ⟨w, fst_of_isTangent hw⟩
    simp only [← hb] at key
    choose a ha using fun j => hc.2 (b.repr (tangent ⟨w, fst_of_isTangent hw⟩) j)
    refine ⟨a, (key a).2 ?_, fun a' h' => funext fun j => hc.1 ?_⟩
    · simp only [ha]
      exact (b.sum_repr _).symm
    · rw [ha, (key a').1 h', b.repr_sum_self]

theorem exists_isDual : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  intro S G _ g c R _ ξ hG _ hc
  have h := isGrpPullback_pullback G ξ
  have : QuasiSeparated (bG G ξ).hom := MorphismProperty.of_isPullback h.1 inferInstance
  have h₁ := ((c.isFrame.pullback ξ).res hc).map_iso (omegaBase h)
  have hf : IsFrame (pfr c ξ hc) := by
    convert h₁ using 2 with k
    exact congrArg _ (QCoh.res_pullbackSections ξ _ le_rfl hc (c.e k)).symm
  obtain ⟨v, hv, hb⟩ := exists_dual_of_isFrame hf
  exact ⟨fun j => (v j).1, ⟨hc, fun j => ⟨v j, rfl, hv j⟩⟩, hb⟩

end GlobalTheory.KeyVals.DualBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

section
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompHS.exists_eigFrame_vecAt₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  intro E _ _ _ H Dw l Xo c TF Z W hW φ hφ k hz x' hx
  subst hx
  haveI := TF.X.proper
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : LocallyOfFiniteType TF.Y.s := inferInstance
  haveI : LocallyOfFiniteType (str₀ TF.X Z) := by unfold str₀ flagStr; infer_instance
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  obtain ⟨K, _, ρ, hρ, hK⟩ := _root_.GlobalTheory.affineOpen_injects_to_dense (Y₀ TF.X Z) (U₀ TF.X Z) (dense_U₀ TF.X Z) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have hz' : ⊤ ≤ (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_comp _ hz
  have hr : Set.range ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) ⊆ Set.range TF.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift TF.Y.j ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) hr
  have hyK : yK ≫ TF.Y.j = (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, ← hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ TF.Y.X) (hx : (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π = x''),
      (∀ σ, initSpan K (TF.X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (TF.X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) =
        eigLie c ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) σ := by
    rintro x'' rfl h
    exact h
  exact GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (hW.fromSpec ≫ inc₀ TF.X Z) k hz hz'
    (key _ hyK.symm fun σ => TF.X.top K yK hy _ hyK.symm k hz' σ)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  first | exact @GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | exact GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | (intros; apply GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem flat_stalkClosedPointTo {S : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R]
    (ξ : Spec R ⟶ S) [Flat ξ] : (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp]
  exact (Flat.stalkMap ξ _).comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso R).hom))

theorem exists_faithfullyFlat_factor_localScheme :
    ∀ (S : Scheme.{0}) (R₁ : Type) [CommRing R₁] [IsLocalRing R₁] (ξ : Sp R₁ ⟶ S) (x : S),
      ξ (closedPoint R₁) = x → Flat ξ → ∃ ξ' : Sp R₁ ⟶ Spec (S.presheaf.stalk x),
        ξ' ≫ S.fromSpecStalk x = ξ ∧ Flat ξ' ∧ Surjective ξ' ∧ QuasiCompact ξ' := by
  intro S R₁ _ _ ξ x hx hf
  subst hx
  have hflat := flat_stalkClosedPointTo (R := CommRingCat.of R₁) ξ
  refine ⟨Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ),
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R₁) ξ,
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat, ⟨?_⟩, inferInstance⟩
  set φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ).hom with hφ
  have hl : IsLocalHom φ := by rw [hφ]; infer_instance
  letI := φ.toAlgebra
  have : Module.Flat (S.presheaf.stalk (ξ (closedPoint R₁))) R₁ := hflat
  have : IsLocalHom (algebraMap (S.presheaf.stalk (ξ (closedPoint R₁))) R₁) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  first | exact @GlobalTheory.LogPole.exists_eigBasis_near | exact GlobalTheory.LogPole.exists_eigBasis_near | (intros; apply GlobalTheory.LogPole.exists_eigBasis_near <;> assumption)
end

