module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle0068
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.EtaleCohomology.EtaleSheaves.Bundle0069

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLiftNonconstOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.NonconstantLift

theorem dim_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) = topologicalKrullDim (U : Set X) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  symm
  exact IsHomeomorph.topologicalKrullDim_eq _ (hU.isoSpec.hom.homeomorph).isHomeomorph

theorem appTop_eq {k Ω : Type} [Field k] [Field Ω] (f : CommRingCat.of k ⟶ CommRingCat.of Ω)
    (g : Sp Ω ⟶ Sp k) (hg : g = Spec.map f) (e) : g.appLE ⊤ ⊤ e = (Spec.map f).appTop := by
  subst hg
  first
  | exact Scheme.Hom.appLE_eq_app _
  | (simp only [Scheme.Hom.appLE]; exact (CategoryTheory.Category.comp_id _).trans rfl)
  | (simp only [Scheme.Hom.appLE]; erw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl)
  | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; convert Category.comp_id _ using 2; exact (Subsingleton.elim _ _ : (homOfLE e).op = 𝟙 _) ▸ rfl)

theorem stalk_inj {X : Scheme.{0}} [IsIntegral X] {x : X} (hx : x = genericPoint X) {T : CommRingCat}
    [Nontrivial T] (f : X.presheaf.stalk x ⟶ T) : Function.Injective f.hom := by
  subst hx
  exact (f.hom : X.functionField →+* T).injective

theorem key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω] (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ R : Subalgebra k Ω, R.FG ∧ ringKrullDim R = ringKrullDim Γ(X, U) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hle : (⊤ : (Sp Ω).Opens) ≤ φ ⁻¹ᵁ U := fun z _ => by
    show φ z ∈ U
    rw [hη z]; exact hηU
  have hU' : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let α : k →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU').hom
  let ψ : Γ(X, U) →+* Ω := (φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
  have hcomp : ψ.comp α = algebraMap k Ω := by
    have h1 : p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle =
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appTop_eq _ _ hφ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap k Ω) := by
      rw [reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    ext a
    simpa [α, ψ] using congrArg (fun g => (CommRingCat.Hom.hom g) a) h2
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have hs' : (φ.appLE U ⊤ hle).hom s = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom hs
      simpa [ψ] using this
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    have h3 := Scheme.Hom.germ_stalkMap_apply φ U z (hle trivial) s
    have h4 : (X.presheaf.germ U (φ z) (hle trivial)).hom s = 0 := by
      apply stalk_inj (hη z) (φ.stalkMap z)
      rw [h3, map_zero]
      have := congrArg ((Sp Ω).presheaf.germ ⊤ z (show z ∈ (⊤ : (Sp Ω).Opens) from Set.mem_univ z)).hom hs'
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero] at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      exact this
    exact germ_injective_of_isIntegral X (φ z) (hle trivial) (by rw [map_zero]; exact h4)
  let _ : Algebra k Γ(X, U) := α.toAlgebra
  let ψa : Γ(X, U) →ₐ[k] Ω := { ψ with commutes' := fun a => DFunLike.congr_fun hcomp a }
  have hft : α.FiniteType := by
    have := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU hU'
    exact RingHom.FiniteType.comp this (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  have : Algebra.FiniteType k Γ(X, U) := hft
  refine ⟨ψa.range, ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  · exact (ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective ψa hinj).toRingEquiv).symm

theorem dim_contra {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω]
    (hdim : ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X) (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) : False := by
  have hU : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨W, hW, hx⟩
  choose V hV hxV using hU
  have hlt : ∀ x, topologicalKrullDim (V x : Set X) < topologicalKrullDim X := fun x => by
    obtain ⟨R, hR, hRd⟩ := key p φ hφ hη (hV x) ⟨x, hxV x⟩
    rw [← dim_affine (hV x), ← hRd]
    exact hdim R hR
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hne : t.Nonempty := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨i, hi⟩
  have hle : topologicalKrullDim X ≤ t.sup' hne (fun i => topologicalKrullDim (V i : Set X)) := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨V i, (V i).isOpen, hx, Finset.le_sup' (fun i => topologicalKrullDim (V i : Set X)) hi⟩
  exact lt_irrefl _ (hle.trans_lt ((Finset.sup'_lt_iff hne).2 fun i _ => hlt i))

theorem LeafLiftNonconst_of : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen y
  by_contra! hcon
  obtain ⟨_, _, _⟩ := id hc0
  have hsnd : ∀ a, e a = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm a) := fun a => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hconst : ∀ a, e a = genericPoint X := by
    obtain ⟨b, hb⟩ := hgen
    intro a
    rw [← hb, hsnd a, hsnd b, hcon a, hcon b]
  have : JacobsonSpace C0 := LocallyOfFiniteType.jacobsonSpace c0
  obtain ⟨a0, -, ha0⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨y, trivial⟩
    isClosed_univ.isLocallyClosed
  have hcl : IsClosed ({a0} : Set C0) := by simpa [closedPoints] using ha0
  exact dim_contra p hdim (pointOfClosedPoint c0 a0 hcl ≫ e)
    (by rw [Category.assoc, he, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp])
    (fun z => by rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hconst])

end LateralTheory.E.NonconstantLift
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjAffPf

theorem desc_spec (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] (A : Type) [CommRing A]
    [Algebra Ω A] [Algebra.FinitePresentation Ω A] :
    Desc k (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) := by
  let P := Algebra.Presentation.ofFinitePresentation Ω A
  let R : Subalgebra k Ω := Algebra.adjoin k P.coeffs
  have : P.HasCoeffs R := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let B := P.ModelOfHasCoeffs R
  let e : Ω ⊗[R] B ≃ₐ[Ω] A := P.tensorModelOfHasCoeffsEquiv R
  have hR : R.FG := ⟨P.finite_coeffs.toFinset, by simp [R]⟩
  let gB : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.toRingEquiv.toCommRingCatIso.hom
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Ω)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap Ω A)) gB := by
    refine (CommRingCat.isPushout_tensorProduct R Ω B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change e (x ⊗ₜ 1) = algebraMap Ω A x
      simpa [Algebra.TensorProduct.algebraMap_apply] using e.commutes x
    · simp [gB]
  refine ⟨R, hR, Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap R B)), _, ?_,
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem desc_of_iso (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (i : X ≅ Y) (g : Y ⟶ Sp Ω) (h : Desc k g) : Desc k (i.hom ≫ g) := by
  obtain ⟨R, hR, D, q, v, hq, hpb⟩ := h
  exact ⟨R, hR, D, q, i.hom ≫ v, hq,
    hpb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

theorem LeafObjAff_of : LeafObjAff := by
  intro k _ Ω _ _ X f hX hf
  obtain ⟨h1, h2, h3⟩ := hf
  let g : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of Ω) := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  letI : Algebra Ω Γ(X, ⊤) := φ.hom.toAlgebra
  have hg : LocallyOfFinitePresentation g := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤))) = g := Spec.map_preimage g
  have hfp : Algebra.FinitePresentation Ω Γ(X, ⊤) := by
    rw [← Spec.map_preimage g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hg
    exact hg
  have := desc_spec k (Ω := Ω) Γ(X, ⊤)
  rw [hφ] at this
  have hf' : f = X.isoSpec.hom ≫ g := by simp [g]
  rw [hf']
  exact desc_of_iso k X.isoSpec g this

end LateralTheory.E.LeafObjAffPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafObjGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjGluePf

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

def DescAt (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D), FP q ∧ IsPullback v f q (toR R)

theorem toR_eq {R R' : Subalgebra k Ω} (h : R ≤ R') : toR R' ≫ incl h = toR R := by
  simp only [toR, incl]
  rw [← Spec.map_comp]
  rfl

theorem fp_snd {X Y Z : Scheme.{0}} (q : X ⟶ Z) (g : Y ⟶ Z) (hq : FP q) : FP (pullback.snd q g) := by
  obtain ⟨h1, h2, h3⟩ := hq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem descAt_mono {R R' : Subalgebra k Ω} (h : R ≤ R') {X : Scheme.{0}} {f : X ⟶ Sp Ω}
    (hd : DescAt R f) : DescAt R' f := by
  obtain ⟨D, q, v, hq, hp⟩ := hd
  refine ⟨pullback q (incl h), pullback.snd q (incl h),
    pullback.lift v (f ≫ toR R') (by rw [hp.w, Category.assoc, toR_eq]), fp_snd _ _ hq, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback q (incl h))
  rw [pullback.lift_fst, toR_eq]
  exact hp

def GlueData (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) (U V : X.Opens) : Prop :=
  ∃ (DU DV DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qV : DV ⟶ Sp R) (qW : DW ⟶ Sp R)
    (vU : U.toScheme ⟶ DU) (vV : V.toScheme ⟶ DV) (vW : (U ⊓ V).toScheme ⟶ DW) (φU : DW ⟶ DU) (φV : DW ⟶ DV),
    FP qU ∧ FP qV ∧ FP qW ∧ IsOpenImmersion φU ∧ IsOpenImmersion φV ∧ φU ≫ qU = qW ∧ φV ≫ qV = qW ∧
    IsPullback vU (U.ι ≫ f) qU (toR R) ∧ IsPullback vV (V.ι ≫ f) qV (toR R) ∧
    IsPullback vW ((U ⊓ V).ι ≫ f) qW (toR R) ∧
    vW ≫ φU = X.homOfLE inf_le_left ≫ vU ∧ vW ≫ φV = X.homOfLE inf_le_right ≫ vV

def LeafInclDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens) (R : Subalgebra k Ω), R.FG →
    DescAt R (U.ι ≫ f) → DescAt R (V.ι ≫ f) → DescAt R ((U ⊓ V).ι ≫ f) →
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ GlueData R' f U V

def LeafGlueTwo : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω) (U V : X.Opens) (R : Subalgebra k Ω), U ⊔ V = ⊤ → GlueData R f U V → DescAt R f

theorem LeafObjGlue_of (hI : LeafInclDescend) (hG : LeafGlueTwo) : LeafObjGlue := by
  intro k _ Ω _ _ X f hf U V hUV ⟨R1, h1, d1⟩ ⟨R2, h2, d2⟩ ⟨R3, h3, d3⟩
  obtain ⟨R', -, hR', g⟩ := hI k Ω f hf U V (R1 ⊔ R2 ⊔ R3) ((h1.sup h2).sup h3)
    (descAt_mono (le_sup_left.trans le_sup_left) d1) (descAt_mono (le_sup_right.trans le_sup_left) d2)
    (descAt_mono le_sup_right d3)
  exact ⟨R', hR', hG k Ω f U V R' hUV g⟩

end LateralTheory.E.LeafObjGluePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPairRelPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafTripleFPPf

namespace LateralTheory.E.LeafPairRelPf

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' R'' : Subalgebra k Ω} (h : R ≤ R')
    (h' : R' ≤ R'') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

def LeafFactorStage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C E Y : Scheme.{0}} (c : C ⟶ Sp Ω) (p : E ⟶ Sp R) (w : C ⟶ E), FP p → ∀ (hs : IsPullback w c p (toR R))
    (f : Y ⟶ Sp R), LocallyOfFinitePresentation f → ∀ (a : C ⟶ Y), a ≫ f = c ≫ toR R →
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (g : pullback p (incl h) ⟶ Y),
      g ≫ f = pullback.snd p (incl h) ≫ incl h ∧
      pullback.lift w (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ g = a

theorem LeafPairRel_of (hO : LeafObjFP) (hF : LeafFactorStage) : LeafPairRel := by
  intro k _ Ω _ _ R hRfg C0 C1 c0 γ1 h1fp D0 q v0 hq hs
  obtain ⟨R1, hR1, E, p1, w, hp1, hsE⟩ := hO k Ω (γ1 ≫ c0) h1fp
  have h0 : R ≤ R ⊔ R1 := le_sup_left
  have h1 : R1 ≤ R ⊔ R1 := le_sup_right
  have hfg : (R ⊔ R1).FG := hRfg.sup hR1
  have hsE' := pb_lift h1 hsE
  have hlfp : LocallyOfFinitePresentation (pullback.snd q (incl h0)) := (fp_snd q (incl h0) hq).1
  obtain ⟨S, h, hS, g, hg1, hg2⟩ := hF k Ω (R ⊔ R1) hfg (γ1 ≫ c0) (pullback.snd p1 (incl h1)) _
    (fp_snd _ _ hp1) hsE' (pullback.snd q (incl h0)) hlfp
    (γ1 ≫ pullback.lift v0 (c0 ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hs.w))
    (by simp only [Category.assoc, pullback.lift_snd])
  refine ⟨S, h0.trans h, hS, pullback (pullback.snd p1 (incl h1)) (incl h),
    pullback.lift (g ≫ pullback.fst q (incl h0)) (pullback.snd _ _) ?_,
    pullback.lift (pullback.lift w ((γ1 ≫ c0) ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hsE.w))
      ((γ1 ≫ c0) ≫ toR S) (by simp only [Category.assoc, toR_incl, pullback.lift_snd]), ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc, incl_incl]
  · rw [pullback.lift_snd]; exact fp_snd _ _ (fp_snd _ _ hp1)
  · convert pb_lift h hsE' using 2
    simp only [pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hg2,
        Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LeafPairRelPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianNeighbourhood

def IsPtNb {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) : Prop :=
  s default = x ∧ (∀ j, IsIso (e j)) ∧ (∀ j, l j ≫ e j ≫ (a j).left = s) ∧
  (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
  (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧
  (∀ (j k : J) (f : j ⟶ k), l k ≫ Spec.map (CommRingCat.ofHom (D.map f).hom) = l j) ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (l' : Spec (CommRingCat.of Ω) ⟶ U'.left), l' ≫ b.left = s →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left ∧ l j ≫ e j ≫ g = l') ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (j : J) (g g' : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left →
      g' ≫ b.left = (a j).left → l j ≫ e j ≫ g = l j ≫ e j ≫ g' →
      ∃ (k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g =
        Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g')

def LeafSHNbSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left),
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t

def LeafSHLoc : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt

def LeafSHHens : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt →
  SH c.pt

theorem LeafSHNb_of (hS : LeafSHNbSys) (hL : LeafSHLoc) (hH : LeafSHHens) : LeafSHNb := by
  intro _ q _ k _ hq B U s0 x
  obtain ⟨Ω, _, _, s, J, _, _, D, c, hc, V, a, l, e, t, hP⟩ := hS U x
  obtain ⟨hs, he, hl, hcomp, ht, -, hcof, -⟩ := id hP
  refine ⟨J, inferInstance, inferInstance, D, c, hc, V, a, fun j => (l j ≫ e j) default, e, t, he, ?_, ?_, hcomp, ht,
    hH U x Ω s D c hc V a l e t hP (hL U x Ω s D c hc V a l e t hP), ?_⟩
  · intro j
    rw [← hs, ← hl j]
    rfl
  · intro j
    have := hq.map (Spec.preimage (e j ≫ (a j).left ≫ s0)).hom
    simpa using this
  · intro U' b y' hy'
    obtain ⟨l', hl', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed b.left s y' (hy'.trans hs.symm)
    obtain ⟨j, g, hg, -⟩ := hcof U' b l' hl'
    exact ⟨j, g, hg⟩

end LateralTheory.E.StrictHenselianNeighbourhood
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHPtOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpecGenClosed
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
end
end

