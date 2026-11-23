module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_normal_finite_model_of_finite_over_open : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Field F] [Algebra O F] [IsFractionRing O F] (X U : Scheme.{0}) (s : X ⟶ Sp O) (c : U ⟶ Sp F) (f : U ⟶ X) (W : (pullback s (spMap (algebraMap O F))).Opens) (fW : U ⟶ W.toScheme), IsProjOver s → Geo.Tor.IsNormalScheme U → IsFinite fW → fW ≫ W.ι ≫ pullback.fst _ _ = f → fW ≫ W.ι ≫ pullback.snd _ _ = c → ∃ (Y : Scheme.{0}) (π : Y ⟶ X) (jQ : U ⟶ pullback (π ≫ s) (spMap (algebraMap O F))), IsFinite π ∧ Geo.Tor.IsNormalScheme Y ∧ IsProjOver (π ≫ s) ∧ Flat (π ≫ s) ∧ jQ ≫ pullback.snd _ _ = c ∧ jQ ≫ pullback.fst _ _ ≫ π = f ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ ∀ y : ↥(pullback (π ≫ s) (spMap (algebraMap O F))), y ∈ Set.range jQ ↔ π (pullback.fst (π ≫ s) (spMap (algebraMap O F)) y) ∈ Set.range (W.ι ≫ pullback.fst s (spMap (algebraMap O F))) := by
  intro O F _ _ _ _ _ _ X U s c f W fW hs hU hfW hf hc
  have hprop : IsProper s := (isProjOver_iff_isProper_and_exists_isAmpleLB s).mp hs |>.1
  have hN : GlobalTheory.IsNormalScheme U := .of_pred hU
  have hb : IsPullback (pullback.fst s (spMap (algebraMap O F))) (pullback.snd _ _) s
      (spMap (algebraMap O F)) := .of_hasPullback _ _
  have : IsLocallyNoetherian (pullback s (spMap (algebraMap O F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap O F)))
  have : QuasiCompact f := by rw [← hf]; infer_instance
  have : QuasiSeparated f := by rw [← hf]; infer_instance
  have : LocallyOfFiniteType c := by rw [← hc]; infer_instance
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian c
  have w : f ≫ s = c ≫ spMap (algebraMap O F) := by
    rw [← hf, ← hc]; simp only [Category.assoc, pullback.condition]
  have hfin : IsFinite f.fromNormalization :=
    isFinite_fromNormalization_of_over_fractionRing (o := .of O) f s F c w
  have h := isPullback_toNormalization_of_isLocalization (M := nonZeroDivisors O) hb fW W.ι f hf.symm
  have hb' : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F)))
      (pullback.snd _ _) (f.fromNormalization ≫ s) (spMap (algebraMap O F)) := .of_hasPullback _ _
  have hpre := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb
  have hpre' := isPreimmersion_of_isPullback_localization (nonZeroDivisors O) hb'
  let q : pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) ⟶
      pullback s (spMap (algebraMap O F)) :=
    pullback.lift (pullback.fst _ _ ≫ f.fromNormalization) (pullback.snd _ _)
      (by simpa using pullback.condition)
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.fromNormalization := pullback.lift_fst ..
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd ..
  have hq : IsPullback (pullback.fst (f.fromNormalization ≫ s) (spMap (algebraMap O F))) q
      f.fromNormalization (pullback.fst s (spMap (algebraMap O F))) :=
    IsPullback.of_bot (by rw [hq₂]; exact hb') hq₁.symm hb
  let j : U ⟶ pullback (f.fromNormalization ≫ s) (spMap (algebraMap O F)) :=
    pullback.lift f.toNormalization c (by simpa using w)
  have hj₁ : j ≫ pullback.fst _ _ = f.toNormalization := pullback.lift_fst ..
  have hj₂ : j ≫ pullback.snd _ _ = c := pullback.lift_snd ..
  have hjq : j ≫ q = fW ≫ W.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, reassoc_of% hj₁, Category.assoc, hf]
      simp
    · rw [Category.assoc, hq₂, hj₂, Category.assoc, hc]
  have hj : IsPullback j fW q W.ι := IsPullback.of_right (by rw [hj₁]; exact h) hjq hq
  refine ⟨f.normalization, f.fromNormalization, j, hfin, IsNormalScheme.pred _,
    isProjOver_comp_of_isFinite _ hs, flat_fromNormalization_comp f F s c w, hj₂,
    by rw [reassoc_of% hj₁]; simp,
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hj.flip inferInstance, ?_, fun y ↦ ?_⟩
  · rw [hpre'.isEmbedding.isInducing.dense_iff]
    intro y
    have hd : DenseRange f.toNormalization := f.toNormalization.denseRange
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hj₁]
    exact hd _
  · rw [← Scheme.Hom.comp_apply, ← hq₁, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fW u, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply fW, ← hjq]; simp⟩
    · rintro ⟨v, hv⟩
      rw [Scheme.Hom.comp_apply] at hv
      obtain ⟨u, hu, -⟩ := Scheme.exists_preimage_of_isPullback hj y v
        (hpre.isEmbedding.injective hv).symm
      exact ⟨u, hu⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjectAtMinimalPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem TObj.HasTh.unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem exists_object_at_minimalPrime :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ w w' d, Out.Laws → Out.Laws2 → 3 ≤ N' → Odd N' → Countable o → GoodClass em C Mat κ w w' d → ∀ 𝔭 ∈ (thIdeal em C).minimalPrimes, ∃ t v, C t ∧ t.HasTh (𝟙 _) v ∧ RingHom.ker (MvPolynomial.eval₂Hom em v) = 𝔭 := by
  intro o _ g N' J b em C Mat κ w w' d hL hL2 h3 _ _ hG 𝔭 h𝔭
  classical
  obtain ⟨r, B, θ, hB, hC⟩ := hG.fam
  have : NeZero (N' ^ 2) := ⟨pow_ne_zero _ (by omega)⟩
  have hvg := fun i : {i : Fin r // (B i).Nonempty} =>
    GlobalTheory.exists_veryGeneral_point_of_holomorphic_family o em (Ix g (N' ^ 2)) d (B i) (θ i)
      (hB i).1 (hB i).2.1 i.2 (hB i).2.2.1
  choose z hz c hc hgen using hvg
  let p : {i : Fin r // (B i).Nonempty} → Ideal (MvPolynomial (Ix g (N' ^ 2)) o) := fun i =>
    RingHom.ker (MvPolynomial.eval₂Hom em (c i • θ i (z i)))
  have hobj : ∀ i, ∃ t, C t ∧ t.HasTh (𝟙 _) (c i • θ i (z i)) := by
    intro i
    obtain ⟨t, ht, hth⟩ := ((hB i).2.2.2 (z i) (hz i)).1
    exact ⟨t, ht, hth.unit_mul (c i) (hc i).isUnit⟩
  have hle : ∀ i, thIdeal em C ≤ p i := by
    intro i
    obtain ⟨t, ht⟩ := hobj i
    exact iInf_le_of_le t (iInf_le_of_le _ (iInf_le_of_le ht le_rfl))
  have hge : Finset.univ.inf p ≤ thIdeal em C := by
    refine le_iInf fun t => le_iInf fun v => le_iInf fun htv => ?_
    obtain ⟨i, z', hz', hth⟩ := hC t htv.1
    have hspan : Ideal.span (Set.range (θ i z')) = ⊤ := by
      obtain ⟨a, ha⟩ := _root_.GlobalTheory.coset_of_hasTh hL hL2 o g N' J b _ _ t N' ℂ (𝟙 _) (θ i z') ⊥ (by omega)
        dvd_rfl hth Ideal.isPrime_bot 0
      rw [Ideal.mem_bot] at ha
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit ha)
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b _ _ t ℂ (𝟙 _) (θ i z') v hth htv.2 hspan
    have hv : v = (u : ℂ) • θ i z' := funext fun a => hu a
    intro F hF
    have hF' : F ∈ p ⟨i, z', hz'⟩ := Finset.inf_le (f := p) (Finset.mem_univ _) hF
    rw [RingHom.mem_ker, hv]
    exact hgen ⟨i, z', hz'⟩ F hF' z' hz' u u.ne_zero
  have hp : 𝔭.IsPrime := h𝔭.1.1
  obtain ⟨i, -, hi⟩ := hp.inf_le'.mp (hge.trans h𝔭.1.2)
  obtain ⟨t, ht, hth⟩ := hobj i
  refine ⟨t, _, ht, hth, le_antisymm hi ?_⟩
  exact h𝔭.2 ⟨RingHom.ker_isPrime _, hle i⟩ hi

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_thetaFrame_family : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) :=
  fun hT hL => ThetaFamily.exists_thetaFrame_of_preconnected hL
    (fun k _ X s hs => by
      obtain ⟨hr, hn, hnoe⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k X s hs
      exact ⟨hr, IsNormalScheme.of_pred hn, hnoe⟩)
    obj_isAbelianScheme_dim_rigidified_sym
    (existsUnique_thetaChar_of_unif hT hL obj_pull obj_isAbelianScheme_dim_rigidified_sym)
    (SecFamily.exists_secOn_nonvanishing hL)
    differentiableOn_quotient_of_differentiableOn_slice

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem image_inf_le {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (U V : Z'.Opens) :
    f ''ᵁ U ⊓ f ''ᵁ V ≤ f ''ᵁ (U ⊓ V) := by

  rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
  obtain rfl : b = a := f.isOpenEmbedding.injective hba
  exact ⟨b, ⟨ha, hb⟩, rfl⟩

def pushLB {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') : LB Z :=
  ⟨A.ι, fun i => f ''ᵁ A.U i, fun i j => res (image_inf_le f (A.U i) (A.U j))
    (Units.map (f.appIso (A.U i ⊓ A.U j)).inv.hom.toMonoidHom (A.g i j))⟩

def sumLB {Z : Scheme.{0}} (A B : LB Z) : LB Z :=
  ⟨A.ι ⊕ B.ι, Sum.elim A.U B.U, fun p q => match p, q with
    | .inl i, .inl j => A.g i j
    | .inr i, .inr j => B.g i j
    | .inl _, .inr _ => 1
    | .inr _, .inl _ => 1⟩

def AmpleFam {Z : Scheme.{0}} (A : LB Z) : Prop :=
  ∀ z : Z, ∃ (d : ℕ) (s : H0 A d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

def HasFrames {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n : ℕ) (r s : ℤ) : Prop :=
  ∃ (th : ∀ i : A.ι, LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk (A.U i).ι)))
    (b : ∀ i : A.ι, Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (A.U i).ι))),
  (∀ i j : A.ι, ∃ (c : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((A.U i ⊓ A.U j).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => th i) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (fun _ : Fin 1 => th j) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => b i k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (b j) (fun k' => M.val k k') t) ∧
    (A.U i ⊓ A.U j).topIso.inv.hom (A.g i j).val = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) ∧
  ∀ (i : A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ (A.U i).toScheme,
    Set.range (jK W ≫ χ ≫ (A.U i).ι) ⊆ abLocus G →
    BasisAlong G L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (fun _ : Fin 1 => th i) ∧
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (b i)

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem hasFrames_of_ampFrames (F : AmpFrames G L N) : HasFrames G L N F.A F.n F.r F.s := by
  refine ⟨F.th, F.b, ?_, ?_⟩
  · intro i j
    exact F.trans i j
  · intro i W _ _ _ hW χ hχ
    exact F.trait i W hW χ hχ

theorem exists_ampFrames {A : LB Z} {n : ℕ} {r s : ℤ} (hA : A.IsLB) (ha : AmpleFam A) (h : HasFrames G L N A n r s) :
    ∃ F : AmpFrames G L N, F.A = A ∧ F.n = n ∧ F.r = r ∧ F.s = s := by

  obtain ⟨th, b, htr, htrait⟩ := h
  exact ⟨⟨A, hA, ha, n, th, b, r, s, htr, htrait⟩, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ModelSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomDescendsToFgIntermediateField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem hom_descends_to_fg_intermediateField : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (A B : Over (Sp K)) (f : (Over.pullback (spMap (algebraMap K C))).obj A ⟶ (Over.pullback (spMap (algebraMap K C))).obj B), LocallyOfFiniteType A.hom → QuasiCompact A.hom → IsSeparated A.hom → LocallyOfFiniteType B.hom → ∃ (L : IntermediateField K C) (f₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ B.left), L.FG ∧ f₀ ≫ B.hom = pullback.fst _ _ ≫ A.hom ∧ ∀ i : pullback A.hom (spMap (algebraMap K C)) ⟶ pullback A.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ → i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) → i ≫ f₀ = f.left ≫ pullback.fst _ _ := by
  intro K C _ _ _ A B f _ _ _ _
  have hw : f.left ≫ pullback.snd B.hom (spMap (algebraMap K C)) =
      pullback.snd A.hom (spMap (algebraMap K C)) := by
    simpa using Over.w f
  have hφ : (f.left ≫ pullback.fst _ _) ≫ B.hom = pullback.fst _ _ ≫ A.hom := by
    rw [Category.assoc, pullback.condition, reassoc_of% hw, pullback.condition]
  obtain ⟨R, ψ, hR, hψ, hRψ⟩ := Spread.exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) hφ
  obtain ⟨t, rfl⟩ := hR
  let L : IntermediateField K C := IntermediateField.adjoin K (t : Set C)
  have hle : Algebra.adjoin K (t : Set C) ≤ L.toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin K _
  refine ⟨L, Spread.bcMap A.hom (Subalgebra.inclusion hle) ≫ ψ, ⟨t, rfl⟩, ?_, ?_⟩
  · rw [Category.assoc, hψ, Spread.bcMap_fst_assoc]
  · intro i h₁ h₂
    rw [Spread.eq_bcMap A.hom L.val h₁ h₂, ← Category.assoc,
      Spread.bcMap_comp_of_eq A.hom _ _ (Algebra.adjoin K (t : Set C)).val fun _ ↦ rfl, hRψ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isAbelianScheme_of_common_generic_fibre
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B G : Over (Sp V)) [GrpObj B] [GrpObj G] (hB : IsAbelianScheme B) (hG : IsSemiAbelian G)
    (hext : ∀ f : (Over.pullback (spMap (algebraMap V K))).obj B ⟶ (Over.pullback (spMap (algebraMap V K))).obj G,
      IsMonHom f → ∃ F : B ⟶ G, (Over.pullback (spMap (algebraMap V K))).map F = f)
    (A : Over (Sp K)) [GrpObj A] {φ₁ : A.left ⟶ B.left} {φ₂ : A.left ⟶ G.left}
    (h₁ : IsGrpPullback A B (spMap (algebraMap V K)) φ₁) (h₂ : IsGrpPullback A G (spMap (algebraMap V K)) φ₂) :
    IsAbelianScheme G := by
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback B (spMap (algebraMap V K))) h₁
  obtain ⟨e', he', -⟩ := grpPullback_iso h₂ (isGrpPullback_pullback G (spMap (algebraMap V K)))
  obtain ⟨F, hF⟩ := hext (e.hom ≫ e'.hom) inferInstance
  refine isAbelianScheme_of_generically_surjective V K B G hB hG F ?_
  rintro x ⟨k, hk⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk.symm
  have hsq : ((Over.pullback (spMap (algebraMap V K))).map F).left ≫ pullback.fst G.hom (spMap (algebraMap V K)) =
      pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left := by
    simp
  rw [hF] at hsq
  have hid : (e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Iso.trans_hom, Iso.inv_hom_id, Over.id_left]
  refine ⟨pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z), ?_⟩
  calc F.left (pullback.fst B.hom (spMap (algebraMap V K)) ((e ≪≫ e').inv.left z))
      = ((e ≪≫ e').inv.left ≫ pullback.fst B.hom (spMap (algebraMap V K)) ≫ F.left) z := rfl
    _ = ((e ≪≫ e').inv.left ≫ (e.hom ≫ e'.hom).left ≫ pullback.fst G.hom (spMap (algebraMap V K))) z := by rw [hsq]
    _ = pullback.fst G.hom (spMap (algebraMap V K)) z := by rw [← Category.assoc, hid, Category.id_comp]
    _ = x := hz

theorem goodRedExt_of_isDiscreteValuationRing :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K], Y.GoodRedExt V K := by
  intro hext E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ b y hy hex
  obtain ⟨𝒜, _, 𝓛, A, _, φ₁, φ₂, h𝒜, -, -, hp1, hp2, -⟩ := hex
  obtain ⟨y', t, m, hy's, hy'j, hab⟩ := GlobalTheory.model_point_extends E H D l Xo c O β Y V K b y hy
  refine ⟨y', hy's, hy'j, hab ?_⟩
  have hm := m.cart
  have hc := IsGrpPullback.comp hp2 Y.m.cart
  have hw : (φ₂ ≫ Y.m.cm.F) ≫ Y.t.G.hom = (A.hom ≫ spMap (algebraMap V K)) ≫ y' := by
    rw [hc.1.w, Category.assoc, hy'j]; rfl
  have h2 : IsGrpPullback A t.G (spMap (algebraMap V K)) (hm.1.lift _ _ hw) :=
    IsGrpPullback.cancel hm (hc.congr (by rw [hy'j]; rfl) (hm.1.lift_fst _ _ hw).symm) (hm.1.lift_snd _ _ hw)
  exact isAbelianScheme_of_common_generic_fibre 𝒜 t.G h𝒜 t.semi
    (fun f hf => (hext V K 𝒜 t.G (isSemiAbelian_of_isAbelianScheme 𝒜 h𝒜) t.semi f hf).exists.imp fun _ h => h.2)
    A hp1 h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem isAffineOpen_preimage_nonzeroLocus {k : Type} [CommRing k] {X Y : Scheme.{0}} (g : Y ⟶ Sp k) [IsProper g]
    (π : Y ⟶ X) {M : LB X} (hM : M.IsLB) (hA : Out.RelAmple (Over.mk g) (M.pull π)) {d : ℕ} (hd : 1 ≤ d)
    (u : LB.Sec (pw M d)) : IsAffineOpen (π ⁻¹ᵁ Out.nonzeroLocus u) := by
  let s : (lbPow M d).Sec := powSecMk d u.f fun i j =>
    (u.compat i j).trans (congrArg (· * _) (by
      change (M.g i j ^ (d : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val]))
  have hs : Out.nonzeroLocus s = Out.nonzeroLocus u := nonzeroLocus_powSecMk _ _ _
  have h := isAmpleLB_of_relAmple_of_isAffine (Over.mk g) (LB.isLB_pull hM π) hA
  have := IsAmpleLB.isAffineOpen_nonzeroLocus g h hd (secPowPull s π)
  rwa [nonzeroLocus_secPowPull, hs] at this

theorem isFinite_of_fibres {R : Type} [CommRing R] {X : Scheme.{0}} {m : ℕ} (φ : X ⟶ PSpace R m)
    (f : X ⟶ Sp R) [IsProper f] (hf : φ ≫ PSpace.str R m = f)
    (H : ∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧
      ∀ i, IsAffineOpen (pullback.fst f (spMap β) ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart R m i))) : IsFinite φ := by
  have := isProper_str R m
  have : IsProper (φ ≫ PSpace.str R m) := by rw [hf]; infer_instance
  have : IsProper φ := .of_comp φ (PSpace.str R m)
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun p => ?_
  obtain ⟨k, _, β, hβ, hk⟩ := H (PSpace.str R m p).asIdeal (PSpace.str R m p).isPrime
  have B := ProjSpace.isPullback_baseChange m β
  let φ' : pullback f (spMap β) ⟶ PSpace k m :=
    B.lift (pullback.fst f (spMap β) ≫ φ) (pullback.snd f (spMap β))
      (by rw [Category.assoc, hf, pullback.condition])
  have e₁ : φ' ≫ ProjSpace.baseChange m β = pullback.fst f (spMap β) ≫ φ := B.lift_fst _ _ _
  have e₂ : φ' ≫ PSpace.str k m = pullback.snd f (spMap β) := B.lift_snd _ _ _
  have P : IsPullback (pullback.fst f (spMap β)) φ' φ (ProjSpace.baseChange m β) :=
    IsPullback.of_bot (by rw [e₂, hf]; exact IsPullback.of_hasPullback f (spMap β)) e₁.symm B
  have : IsProper φ' := MorphismProperty.of_isPullback (P := @IsProper) P inferInstance
  have : IsAffineHom φ' := isAffineHom_of_forall_exists_isAffineOpen _ fun y => by
    obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k m y
    refine ⟨_, hi, ProjSpace.isAffineOpen_chart k m i, ?_⟩
    rw [← ProjSpace.baseChange_preimage_chart m β i, ← Scheme.Hom.comp_preimage, e₁, Scheme.Hom.comp_preimage]
    exact hk i
  have : IsFinite φ' := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨p', hp', -⟩ := Scheme.exists_preimage_of_isPullback B p (⊥ : PrimeSpectrum k)
    (PrimeSpectrum.ext hβ.symm)
  refine ((φ'.finite_preimage_singleton p').image (pullback.fst f (spMap β))).subset fun x hx => ?_
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P x p' (hx.trans hp'.symm)
  exact ⟨z, h₂, h₁⟩

theorem isAffineOpen_nonzeroLocus_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  intro R _ X f M d m u hd _ hM hu H i
  have : IsFinite (ProjSpace.toProj f u hu) :=
    isFinite_of_fibres (ProjSpace.toProj f u hu) f (ProjSpace.toProj_str f u hu) fun q hq => by
      obtain ⟨k, _, β, hβ, hA⟩ := H q hq
      refine ⟨k, _, β, hβ, fun j => ?_⟩
      rw [ProjSpace.toProj_preimage_chart]
      exact isAffineOpen_preimage_nonzeroLocus _ _ hM hA hd (u j)
  rw [← ProjSpace.toProj_preimage_chart f u hu]
  exact (ProjSpace.isAffineOpen_chart R m i).preimage _

end GlobalTheory.FibreAmple
end

