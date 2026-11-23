module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0071
public import Development.EtaleCohomology.EtaleSheaves.Bundle0047
public import Development.EtaleCohomology.EtaleSheaves.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.Bundle0081
public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.SpreadOf
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.Etale
public import Development.EtaleCohomology.EtaleSheaves.Bundle0074

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.CurveKrullDim
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

def LeafCurveNotPoint : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsCurve c → ¬ Subsingleton C

theorem dim_le_one (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) {Ω : Type} [Field Ω] {C : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : SmoothOfRelativeDimension 1 c) : topologicalKrullDim C ≤ 1 := by
  let e : (⊥ : Subalgebra Ω Ω) ≃+* Ω := (Algebra.botEquiv Ω Ω).toRingEquiv
  let φ : Sp Ω ⟶ Sp (⊥ : Subalgebra Ω Ω) := Spec.map e.toCommRingCatIso.hom
  have : IsIso φ := inferInstance
  have : SmoothOfRelativeDimension 1 (c ≫ φ) := inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (c ≫ φ))
  have h := hD Ω Ω (⊥ : Subalgebra Ω Ω) Subalgebra.fg_bot (c ≫ φ) this
  rwa [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field, zero_add] at h

theorem LeafCurveSmall_of_cut (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) (hP : LeafCurveNotPoint) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := by
  intro Ω _ _ C c hc
  obtain ⟨hI, hPr, hS⟩ := id hc
  have : LocallyOfFiniteType c := inferInstance
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : CompactSpace C := by
    have : QuasiCompact c := inferInstance
    exact (quasiCompact_iff_compactSpace c).mp this
  have : IsNoetherian C := by constructor
  have : NoetherianSpace C := inferInstance
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  have hd := dim_le_one hD c hS
  refine ⟨fun hfin => hP Ω c hc ?_, fun Z hZ hinf => ?_⟩
  · have hcp : closedPoints C = univ := by
      have : IsClosed (closedPoints C) := by
        have : closedPoints C = ⋃ x ∈ (hfin.subset (subset_univ (closedPoints C))).toFinset, {x} := by
          ext; simp
        rw [this]; exact isClosed_biUnion_finset fun x hx => by simpa using hx
      rw [← this.closure_eq]; exact closure_closedPoints
    have hη : IsClosed ({genericPoint C} : Set C) := by
      rw [← mem_closedPoints_iff, hcp]; trivial
    have : ({genericPoint C} : Set C) = univ := by
      rw [← hη.closure_eq]; exact (genericPoint_spec C).def
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({genericPoint C} : Set C) := this ▸ mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := this ▸ mem_univ b
    exact ha.trans hb.symm
  · by_contra hne
    exact hinf (finite_of_closed hd Z hZ hne)

theorem curveNotPoint : LeafCurveNotPoint := by
  intro Ω _ _ C c hc hsub
  obtain ⟨hI, hPr, hS⟩ := id hc
  obtain ⟨x⟩ : Nonempty C := inferInstance
  have : IsAffine C := inferInstance
  let _ : Field Γ(C, ⊤) := (isField_of_isIntegral_of_subsingleton C).toField
  have hft : (c.appTop).hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω))
  let φ : Ω →+* Γ(C, ⊤) := (c.appTop).hom.comp ι.inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso ι.inv).2)
  let _ : Algebra Ω Γ(C, ⊤) := φ.toAlgebra
  have : Algebra.FiniteType Ω Γ(C, ⊤) := hφ
  have : Module.Finite Ω Γ(C, ⊤) := finite_of_finite_type_of_isJacobsonRing Ω Γ(C, ⊤)
  have hb : Function.Bijective φ := IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hb2 : Function.Bijective (c.appTop).hom := by
    have : (c.appTop).hom = φ.comp ι.hom.hom := by
      ext a; simp [φ]
    rw [this]; exact hb.comp (ConcreteCategory.bijective_of_isIso ι.hom)
  have : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hb2
  have : IsIso c := by
    have h := Scheme.isoSpec_hom_naturality c
    have : c = C.isoSpec.hom ≫ Spec.map c.appTop ≫ (Sp Ω).isoSpec.inv := by
      rw [reassoc_of% h]; simp
    rw [this]; infer_instance
  have h0 : SmoothOfRelativeDimension 0 c := inferInstance
  exact absurd (ReciprocityTheory.ChartRestriction.G.H1.dim_unique c hS h0 x) (by norm_num)

theorem LeafCurveSmall_of (hD : LateralTheory.E.LeafDescendVCut.LeafDimBound) :
    LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall :=
  LeafCurveSmall_of_cut hD curveNotPoint

end LateralTheory.E.CurveKrullDim
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DgMapIsPullback
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafMapFPPf2

theorem dgMap_isPullback {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R : Subalgebra k Ω} {D1 : Scheme.{0}}
    (q1 : D1 ⟶ Sp R) {S T : Subalgebra k Ω} (hS : R ≤ S) (hT : R ≤ T) (h : S ≤ T) :
    IsPullback (dgMap q1 hS hT h) (pullback.snd q1 (incl hT)) (pullback.snd q1 (incl hS)) (incl h) := by
  have t : IsPullback (dgMap q1 hS hT h ≫ pullback.fst _ _) (pullback.snd q1 (incl hT)) q1 (incl h ≫ incl hS) := by
    rw [dgMap_fst, incl_comp]; exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_right t (dgMap_snd q1 hS hT h) (IsPullback.of_hasPullback _ _)

theorem stages : LeafStagesFP := by
  intro k _ Ω _ _ R D1 q1 hq1
  obtain ⟨_, h2, h3⟩ := hq1
  refine ⟨fun S => ⟨?_, ?_⟩, fun S T h => ?_⟩
  · have : QuasiCompact (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h2
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd q1 (incl S.unop.2.2)) this _
  · have : QuasiSeparated (pullback.snd q1 (incl S.unop.2.2)) :=
      by
      first
        | exact MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback q1 (incl S.unop.2.2)) h3
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd q1 (incl S.unop.2.2)) _ this
  · first
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h) inferInstance
      | exact MorphismProperty.of_isPullback (P := @IsAffineHom) (dgMap_isPullback q1 S.2.2 T.2.2 h).flip inferInstance

theorem morphismDescent_of_isLimit (hL : LeafLimFP) : LeafMapFP := LateralTheory.E.LeafMapFPPf.morphismDescent_of_isLimit hL stages

end LateralTheory.E.LeafMapFPPf2

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtStagePf
section
noncomputable section
open CategoryTheory Limits TensorProduct

namespace LateralTheory.E.EtStagePf

theorem exists_model {A T : CommRingCat.{0}} (f : A ⟶ T) (hf : f.hom.Etale) :
    ∃ (A₀ B₀ : CommRingCat.{0}) (a : A₀ ⟶ A) (f₀ : A₀ ⟶ B₀) (b : B₀ ⟶ T),
      (Int.castRingHom A₀).FinitePresentation ∧ f₀.hom.Etale ∧ IsPushout a f₀ f b := by
  let _ := f.hom.toAlgebra
  have h : Algebra.Etale A T := hf
  obtain ⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ A T
  have hft : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have hfp : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp hft
  refine ⟨CommRingCat.of A₀, CommRingCat.of B₀, CommRingCat.ofHom (algebraMap A₀ A),
    CommRingCat.ofHom (algebraMap A₀ B₀),
    CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_, ?_⟩
  · have := RingHom.finitePresentation_algebraMap.mpr hfp
    rwa [RingHom.ext_int (algebraMap ℤ A₀) (Int.castRingHom A₀)] at this
  · exact RingHom.etale_algebraMap.mpr het
  · refine (CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext x
      exact e.symm.commutes x
    · ext x
      rfl

theorem EtStage_of : LateralTheory.E.SpreadPf.Cut.EtStage := by
  intro J _ _ D c hc _ _ T _ f _ _ _ hf
  obtain ⟨A₀, B₀, a, f₀, b, hfp, het, hP⟩ := exists_model f hf
  let α : (Functor.const J).obj (CommRingCat.of ℤ) ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom _)
      naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext_int _ _) }
  obtain ⟨k, a', -, ha⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of ℤ) D α
    (CommRingCat.ofHom (Int.castRingHom A₀)) c hc hfp a
    (fun _ => CommRingCat.hom_ext (RingHom.ext_int _ _))
  subst ha
  have hQ := IsPushout.of_hasPushout a' f₀
  have hw : a' ≫ c.ι.app k ≫ f = f₀ ≫ b := by rw [← hP.w, Category.assoc]
  refine ⟨k, pushout a' f₀, pushout.inl a' f₀, pushout.desc (c.ι.app k ≫ f) b hw, ?_, ?_⟩
  · refine IsPushout.of_left ?_ (pushout.inl_desc _ _ _).symm hQ
    rw [pushout.inr_desc]
    exact hP
  · have := (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := @RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
    exact this.of_isPushout hQ het

end LateralTheory.E.EtStagePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLimFPPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafLimFPPf

theorem isLimit_pullback_finitelyGenerated : LeafLimFP := by
  intro k _ Ω _ _ R hR C1 D1 c1 q1 v1 hs _
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let o : GlobalTheory.FGAbove R := ⟨R, hR, le_rfl⟩
  let a : ∀ S : GlobalTheory.FGAbove R, s.pt ⟶ pullback q1 (incl S.2.2) := fun S => s.π.app (op S)
  have ha : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), a T ≫ dgMap q1 S.2.2 T.2.2 h = a S :=
    fun S T h => s.w (homOfLE (show S ≤ T from h)).op
  have hsnd : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1),
      (a T ≫ pullback.snd _ _) ≫ incl h = a S ≫ pullback.snd _ _ := fun S T h => by
    rw [← ha S T h, Category.assoc, Category.assoc, dgMap_snd]
  obtain ⟨ψ, hψ⟩ := GlobalTheory.FGAbove.exists_ringHom hR
    (fun S => ((Scheme.ΓSpecIso (.of S.1)).inv ≫ (a S ≫ pullback.snd _ _).appTop).hom) (by
      intro S T h x
      rw [← hsnd S T h]
      exact (GlobalTheory.appTop_comp_spMap (Subalgebra.inclusion h).toRingHom _ x).symm)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp Ω, (Scheme.ΓSpecIso (.of Ω)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ S : GlobalTheory.FGAbove R, b ≫ toR S.1 = a S ≫ pullback.snd _ _ := fun S =>
    GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      refine (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b x).trans ?_
      rw [hb]
      exact hψ S x))
  have hf : ∀ S : GlobalTheory.FGAbove R, a S ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun S => by
    rw [← ha o S S.2.2, Category.assoc, dgMap_fst]
  have hw : (a o ≫ pullback.fst _ _) ≫ q1 = b ≫ toR R := by
    conv_rhs => rw [← toR_incl o.2.2]
    rw [← Category.assoc, hb' o, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨hs.lift (a o ≫ pullback.fst _ _) b hw, fun S => ?_, fun m hm => ?_⟩
  · show _ ≫ pullback.lift v1 (c1 ≫ toR S.unop.1) _ = a S.unop
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hs.lift_fst, hf S.unop]
    · rw [Category.assoc, pullback.lift_snd, hs.lift_snd_assoc, hb']
  · change s.pt ⟶ C1 at m
    have hm' : ∀ S : GlobalTheory.FGAbove R, m ≫ pullback.lift v1 (c1 ≫ toR S.1)
        (by rw [Category.assoc, toR_incl, hs.w]) = a S := fun S => hm (op S)
    apply hs.hom_ext
    · rw [hs.lift_fst, ← hm' o, Category.assoc, pullback.lift_fst]
    · rw [hs.lift_snd]
      refine GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨S, hx⟩ := GlobalTheory.FGAbove.exists_mem hR x
      have e : (m ≫ c1) ≫ toR S.1 = b ≫ toR S.1 := by
        rw [hb', ← hm' S, Category.assoc, Category.assoc, pullback.lift_snd]
      exact (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) _ ⟨x, hx⟩).symm.trans
        (e ▸ GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b ⟨x, hx⟩)

end LateralTheory.E.LeafLimFPPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadRelDimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf

namespace LateralTheory.E.LeafSpreadRelDimPf

def LeafRelDimAtImage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ y : C, ∃ V : D.Opens, v y ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q)

def LeafGenericOpenSpread : Prop := ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (D : Scheme.{0}) (q : D ⟶ Sp A),
    IsAffine D → LocallyOfFinitePresentation q → ∀ U : D.Opens,
    (∀ x : D, (show PrimeSpectrum A from q x).asIdeal = ⊥ → x ∈ U) →
    ∃ f : A, f ≠ 0 ∧ ∀ x : D, f ∉ (show PrimeSpectrum A from q x).asIdeal → x ∈ U

theorem generic_pt {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (ω : Sp Ω) :
    (show PrimeSpectrum R from toR R ω).asIdeal = ⊥ := by
  have h0 : (show PrimeSpectrum Ω from ω).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap (algebraMap R Ω) (show PrimeSpectrum Ω from ω).asIdeal = ⊥
  rw [h0]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R Ω)

theorem LeafSpreadRelDim_of_sub (hA : LeafRelDimAtImage) (hB : LeafGenericOpenSpread) : LeafSpreadRelDim := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv
  let U : D.Opens := sSup {V : D.Opens | SmoothOfRelativeDimension 1 (V.ι ≫ q)}
  have hU : ∀ x : D, (show PrimeSpectrum R from q x).asIdeal = ⊥ → x ∈ U := by
    intro x hx
    let ω : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    have he : q x = toR R ω := PrimeSpectrum.ext (hx.trans (generic_pt R ω).symm)
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x ω he
    obtain ⟨V, hV, hVs⟩ := hA k Ω R hR c q v hD hlfp hsm hs hv (hv.isoPullback.inv z)
    have : v (hv.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz1]
    rw [this] at hV
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hVs, hV⟩
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨f, hf0, hf⟩ := hB R D q hD hlfp U hU
  have hf0' : (f : Ω) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let T : Subalgebra k Ω := Algebra.adjoin k ((({((f : Ω))⁻¹} : Finset Ω)) : Set Ω)
  refine ⟨R ⊔ T, le_sup_left, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  intro R' hR' hRR E q' r hE
  have hinv : ((f : Ω))⁻¹ ∈ R' :=
    hR' (le_sup_right (a := R) (Algebra.subset_adjoin (by simp)))
  have hunit : IsUnit (Subalgebra.inclusion hRR f) := by
    have h1 : Subalgebra.inclusion hRR f * (⟨_, hinv⟩ : R') = 1 := Subtype.ext (mul_inv_cancel₀ hf0')
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun V : {V : D.Opens // SmoothOfRelativeDimension 1 (V.ι ≫ q)} => r ⁻¹ᵁ V.1) ?_ ?_
  · refine top_le_iff.mp fun e _ => ?_
    have hq : q (r e) = incl hRR (q' e) := by
      rw [← Scheme.Hom.comp_apply, hE.w, Scheme.Hom.comp_apply]
    have hx : f ∉ (show PrimeSpectrum R from q (r e)).asIdeal := by
      rw [hq]
      change Subalgebra.inclusion hRR f ∉ (show PrimeSpectrum R' from q' e).asIdeal
      exact fun h => (show PrimeSpectrum R' from q' e).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h hunit)
    obtain ⟨V, hVs, hV⟩ := TopologicalSpace.Opens.mem_sSup.mp (hf (r e) hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hV⟩
  · intro V
    have h2 := (isPullback_morphismRestrict r V.1).paste_vert hE
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback h2 V.2

end LateralTheory.E.LeafSpreadRelDimPf

namespace LateralTheory.E.LeafSpreadRelDimPf.Spread
open Topology TopologicalSpace

theorem exists_ne_zero_of_constructible {A : Type} [CommRing A] [IsDomain A] (T : Set (PrimeSpectrum A))
    (hT : IsConstructible T) (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ T) :
    ∃ f : A, f ≠ 0 ∧ ∀ p ∈ T, f ∈ p.asIdeal := by
  revert h
  induction T, hT using IsConstructible.induction_of_isTopologicalBasis
    (fun f : A => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))
    PrimeSpectrum.isTopologicalBasis_basic_opens (fun f => PrimeSpectrum.isCompact_basicOpen f) with
  | sdiff g s hs =>
    intro h
    by_cases hg : g = 0
    · refine ⟨1, one_ne_zero, fun p hp => ?_⟩
      have := hp.1
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hg] at this
      exact absurd p.asIdeal.zero_mem this
    · have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hg
      have : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ ⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum A)) := by
        by_contra hn; exact h ⟨hη, hn⟩
      obtain ⟨j, hj, hηj⟩ := Set.mem_iUnion₂.mp this
      have hj0 : j ≠ 0 := by simpa [PrimeSpectrum.mem_basicOpen] using hηj
      refine ⟨j, hj0, fun p hp => ?_⟩
      have h2 := hp.2
      by_contra hn
      exact h2 (Set.mem_iUnion₂.mpr ⟨j, hj, by simpa [PrimeSpectrum.mem_basicOpen] using hn⟩)
  | union s hs t ht ihs iht =>
    intro h
    obtain ⟨f1, h1, hf1⟩ := ihs (fun hh => h (Or.inl hh))
    obtain ⟨f2, h2, hf2⟩ := iht (fun hh => h (Or.inr hh))
    refine ⟨f1 * f2, mul_ne_zero h1 h2, fun p hp => ?_⟩
    rcases hp with hp | hp
    · exact Ideal.mul_mem_right _ _ (hf1 p hp)
    · exact Ideal.mul_mem_left _ _ (hf2 p hp)

theorem LeafGenericOpenSpread_pf : LeafGenericOpenSpread := by
  intro A _ _ _ D q hD hlfp U hU
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := {}
  have hZ : IsConstructible ((U : Set D)ᶜ) :=
    ((NoetherianSpace.isCompact (U : Set D)).isConstructible U.isOpen).compl
  have : QuasiCompact q := inferInstance
  have hI := q.isConstructible_image hZ
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_of_constructible (A := A) (q '' ((U : Set D)ᶜ)) hI (by
    rintro ⟨x, hx, hqx⟩
    exact hx (hU x (by rw [hqx])))
  refine ⟨f, hf0, fun x hx => ?_⟩
  by_contra hxU
  exact hx (hf (q x) ⟨x, hxU, rfl⟩)

end LateralTheory.E.LeafSpreadRelDimPf.Spread

namespace LateralTheory.E.LeafSpreadRelDimPf

theorem LeafRelDimAtImage_pf : LeafRelDimAtImage := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv y
  obtain ⟨n, W, hW, hWs⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim q (v y)
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_base hv hWs hs y hW
  subst this
  exact ⟨W, hW, hWs⟩

theorem LeafSpreadRelDim_of : LeafSpreadRelDim :=
  LeafSpreadRelDim_of_sub LeafRelDimAtImage_pf Spread.LeafGenericOpenSpread_pf

end LateralTheory.E.LeafSpreadRelDimPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.QuasiFiniteAtOfIsOpenFiber
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.QuasiFiniteAtDescent

theorem quasiFiniteAt_of_isOpen_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (a : X) (hza : f.fiberι y z = a) (hz : IsOpen ({z} : Set (f.fiber y))) :
    f.QuasiFiniteAt a := by
  have hy : y = f a := by
    rw [← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst hy
  have : z = f.asFiber a := by
    apply (f.fiberι (f a)).isEmbedding.injective
    rw [hza, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]
  exact hz

theorem qf_of_fiberMap {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B)
    [LocallyOfFiniteType g] [LocallyOfFiniteType γ] (x : CA)
    (φ : γ.fiber (γ x) ⟶ g.fiber (vB (γ x))) (hφ : UniversallyOpen φ)
    (e : φ ≫ g.fiberι (vB (γ x)) = γ.fiberι (γ x) ≫ vA) (hx : γ.QuasiFiniteAt x) :
    g.QuasiFiniteAt (vA x) := by
  have hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
  have hopen := φ.isOpenMap _ hx'
  have h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x)))) := by
    convert hopen using 1
    exact (Set.image_singleton).symm
  refine quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]

theorem LeafQFAtDescend_of : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := by
  intro CA CB A B γ g vA vB sq hg x hx
  have : LocallyOfFiniteType γ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)
  have hφ := MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance
  refine qf_of_fiberMap γ g vA vB x _ hφ ?_ hx
  exact pullback.lift_fst _ _ _

end LateralTheory.E.QuasiFiniteAtDescent
end
end

