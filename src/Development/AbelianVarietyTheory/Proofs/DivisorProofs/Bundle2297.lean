module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfCohomologous
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LBObs.obU_eq_of_cohomologous : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c' → c = c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c c' hF ht hc hc'
  exact _root_.GlobalTheory.LBObs.isObU_unique R R₀ I hI π hπ hk R₁ α C F L u' c c'
    (_root_.GlobalTheory.LBObs.isObU_of_cob R R₀ I hI π hπ hk R₁ α C F L u u' t c hF ht hc) hc'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionPairPullback
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

theorem obAt_pairPull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (D : Type) [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ), ObAt S α L (K ⋙ pairSnd f₀) ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) → ObAt S' α (L.pull f₀) (K ⋙ pairFst f₀) ((extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c)) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D _ K hob
  obtain ⟨u, hfr, hu⟩ := hob
  let n : CoefMap (RingHom.id R₀) ((K ⋙ pairSnd f₀) ⋙ OAff s₀) ((K ⋙ pairFst f₀) ⋙ OAff t₀) :=
    { G := 𝟭 D
      α := fun T ↦ (pairPull h).α (K.obj T)
      naturality := fun a b ↦ (pairPull h).naturality (K.map a) b
      smul := fun T r b ↦ (pairPull h).smul (K.obj T) r b }
  have hH : ∀ T : D, opOf (K ⋙ pairFst f₀) T ≤ f₀ ⁻¹ᵁ opOf (K ⋙ pairSnd f₀) ((𝟭 D).obj T) :=
    fun T ↦ (K.obj T).unop.2
  refine ⟨_, isFrame_pull X₀ D _ (opOf_le (K ⋙ pairSnd f₀)) L u Z₀ f₀ D _ (opOf_le (K ⋙ pairFst f₀)) (𝟭 D) hH hfr, ?_⟩
  have key : (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairPull h)).pull2 c) =
      (extMap R₁ n).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).pull2 c) := by
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    have hy : ∀ (T : D) (y : R₁ ⊗[R₀] (OAff s₀).obj ((pairSnd f₀).obj (K.obj T))),
        (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).α T ((extMap R₁ (pairPull h)).α (K.obj T) y) =
          (extMap R₁ n).α T ((extMap R₁ (CoefMap.restrict (OAff s₀) (K ⋙ pairSnd f₀))).α T y) := by
      intro T y
      induction y using TensorProduct.induction_on with
      | zero => repeat erw [map_zero]
      | tmul x y => rfl
      | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy]
    rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
    congr 1
    apply Subtype.ext
    funext T T' T'' a b
    simp only [CoefMap.pullCocycleTwo_apply]
    exact hy T'' _
  rw [key]
  refine isObU_pull R R₀ I hI π hπ hk R₁ α D _ ((ofSys S).restrict (K ⋙ pairSnd f₀)) D _
    ((ofSys S').restrict (K ⋙ pairFst f₀)) n (fun T ↦ l (K.obj T)) u _ _
    (fun T b ↦ hl (K.obj T) b) (fun T T' a b ↦ hn (K.map a) b) ?_ hu
  intro T T' a
  change (Z₀.presheaf.map _).hom ((f₀.app _).hom _) = (f₀.appLE _ _ _).hom _
  rfl

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasis
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
  {C D : Type} [Category.{0} C] [Category.{0} D]

theorem opOf_le_of_natTrans (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) (T : D) :
    opOf K T ≤ opOf G (H.obj T) := leOfHom (θ.app T).unop

def natCoef (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) :
    CoefMap (RingHom.id R₀) (G ⋙ OAff s₀) (K ⋙ OAff s₀) where
  G := H
  α T := (mp (OAff s₀) (θ.app T)).toRingHom
  naturality {T T'} φ b := by
    change mp (OAff s₀) (θ.app T') (mp (OAff s₀) ((H ⋙ G).map φ) b) = mp (OAff s₀) (K.map φ) (mp (OAff s₀) (θ.app T) b)
    rw [← mp_comp, ← mp_comp, θ.naturality φ]
  smul T r b := by
    change mp (OAff s₀) (θ.app T) (r • b) = r • mp (OAff s₀) (θ.app T) b
    exact map_smul _ r b

theorem obAt_refine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)
    (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀)))
    (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C)
    (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) →
      ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L c C D _ _ G K H θ h
  obtain ⟨u, hf, ho⟩ := h
  refine ⟨fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)), ?_, ?_⟩
  · exact _root_.GlobalTheory.LBObs.isFrame_restrict X₀ C (opOf G) (opOf_le G) L u D (opOf K) (opOf_le K) H (opOf_le_of_natTrans G K H θ) hf
  · have key := _root_.GlobalTheory.LBObs.isObU_pull R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) D (K ⋙ OAff s₀)
      ((ofSys S).restrict K) (natCoef (s₀ := s₀) G K H θ) (fun T ↦ mp S.F (θ.app T)) u
      (fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)))
      ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)
      (fun T b ↦ S.nat (θ.app T) b)
      (fun T T' a b ↦ by
        change mp S.F (K.map a) (mp S.F (θ.app T) b) = mp S.F (θ.app T') (mp S.F ((H ⋙ G).map a) b)
        exact (mp_comp S.F _ _ b).symm.trans
          ((congrArg (fun f ↦ mp S.F f b) (θ.naturality a).symm).trans (mp_comp S.F _ _ b)))
      (fun T T' a ↦ rfl) ho
    have hc : (extMap R₁ (natCoef (s₀ := s₀) G K H θ)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) =
        (extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c := by
      rw [← CoefMap.pullCohomologyTwo_comp]
      refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ (fun T b ↦ ?_) c
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [← hc]
    exact key

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetricOfSymmetricGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGenericExt

theorem symm_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  intro R _ _ _ _ _ G _ hG L hL h
  have e := GlobalTheory.SymBaseChange.inv_left_fst _ _ G (jK R)
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R))
    (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom (jK R)) e
  refine GlobalTheory.GenericDec.lbIso_of_generic G hG (pull_isLB hL _) hL ?_
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h2)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h1 h)

end GlobalTheory.SymGenericExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUnifor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UTraitHyp

theorem hypS_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  intro V _ _ I E _ _ _ H t P
  letI := P.A.isAb.comm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ t.G P.A.A (jK V) _ t.PP.L P.A.L t.PP.isLB P.A.isLB h1 h2
    ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
      by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

end GlobalTheory.UTraitHyp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactIntertwinesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  first | exact @GlobalTheory.DblScal.scalW_main | exact GlobalTheory.DblScal.scalW_main | (intros; apply GlobalTheory.DblScal.scalW_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SquareSpread

theorem germ_res_hom {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (X.presheaf.germ U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

theorem res_res_hom {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_res_eq {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) (s t : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    ∃ W : X.Opens, ∃ hW : W ≤ U, x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t := by
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have h1 : iU = homOfLE iU.le := rfl
  have h2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rw [h1] at e
  rw [h2] at e
  exact e

end GlobalTheory.Mum.SquareSpread


open GlobalTheory.Mum.SquareSpread in
theorem GlobalTheory.Mum.unit_mul_sq_spread : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro X L2 h x j₀ hx u a ha hh

  obtain ⟨W₁, hW₁, hx₁, a', ha'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a hx
  obtain ⟨W₂, hW₂, hx₂, u', hu'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf (u : X.presheaf.stalk x) hx₁
  obtain ⟨W₃, hW₃, hx₃, v', hv'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) hx₂
  have l31 : W₃ ≤ W₁ := hW₃.trans hW₂
  have l30 : W₃ ≤ L2.U j₀ := l31.trans hW₁
  set A : Γ(X, W₃) := (X.presheaf.map (homOfLE l31).op).hom a' with hA
  set U' : Γ(X, W₃) := (X.presheaf.map (homOfLE hW₃).op).hom u' with hU'
  set H : Γ(X, W₃) := (X.presheaf.map (homOfLE l30).op).hom (h.f j₀) with hH
  have gA : (X.presheaf.germ W₃ x hx₃).hom A = a := by rw [hA, germ_res_hom]; exact ha'
  have gU : (X.presheaf.germ W₃ x hx₃).hom U' = u := by rw [hU', germ_res_hom]; exact hu'
  have gV : (X.presheaf.germ W₃ x hx₃).hom v' = ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := hv'
  have gH : (X.presheaf.germ W₃ x hx₃).hom H = u * a ^ 2 := by rw [hH, germ_res_hom]; exact hh
  obtain ⟨W₄, hW₄, hx₄, e₄⟩ := exists_res_eq hx₃ (U' * v') 1 (by
    rw [map_mul, map_one, gU, gV, Units.mul_inv])
  obtain ⟨W₅, hW₅, hx₅, e₅⟩ := exists_res_eq hx₃ H (U' * A ^ 2) (by
    rw [map_mul, map_pow, gU, gA, gH])

  have lV3 : W₄ ⊓ W₅ ≤ W₃ := inf_le_left.trans hW₄
  have hxV : x ∈ W₄ ⊓ W₅ := ⟨hx₄, hx₅⟩
  have e₄' : (X.presheaf.map (homOfLE lV3).op).hom U' * (X.presheaf.map (homOfLE lV3).op).hom v' = 1 := by
    rw [← map_mul, ← map_one (X.presheaf.map (homOfLE lV3).op).hom, ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄),
      ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄) 1, e₄]
  have e₅' : (X.presheaf.map (homOfLE lV3).op).hom H = (X.presheaf.map (homOfLE lV3).op).hom U' *
      ((X.presheaf.map (homOfLE lV3).op).hom A) ^ 2 := by
    rw [← map_pow, ← map_mul, ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅),
      ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅) (U' * A ^ 2), e₅]
  let uV : Γ(X, W₄ ⊓ W₅)ˣ := ⟨_, _, e₄', by rw [mul_comm]; exact e₄'⟩
  refine ⟨W₄ ⊓ W₅, hxV, (X.presheaf.map (homOfLE lV3).op).hom A, ?_, ?_⟩
  · intro h0
    apply ha
    rw [← gA, ← germ_res_hom lV3 hxV, h0, map_zero]
  · intro j
    have k : W₄ ⊓ W₅ ⊓ L2.U j ≤ L2.U j ⊓ L2.U j₀ := le_inf inf_le_right (inf_le_left.trans (lV3.trans l30))
    refine ⟨res k (L2.g j j₀) * Units.map (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom uV, ?_⟩
    have c := congrArg (X.presheaf.map (homOfLE k).op).hom (h.compat j j₀)
    rw [map_mul, res_res_hom, res_res_hom] at c
    have e6 := congrArg (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom e₅'
    rw [map_mul, map_pow, hH, res_res_hom, res_res_hom, res_res_hom] at e6
    rw [Units.val_mul, Units.coe_map, res, Units.coe_map]
    simp only [MonoidHom.coe_coe, hA, res_res_hom] at e6 ⊢
    rw [c, e6, _root_.mul_assoc]
    congr 2
    exact (res_res_hom lV3 _ U').symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorPrimeComapCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


open KaehlerDifferential TensorProduct in
theorem mapBaseChange_residueField_bijective_of_etale_fibre :
    ∀ (A C B Ω : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Field Ω] [Algebra A Ω] (Q : Ideal B) [Q.IsPrime] (Q' : Ideal (TensorProduct A Ω B)) [Q'.IsPrime] (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = Q → f ∉ Q' → ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale → Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) := by
  intro A C B Ω _ _ _ _ _ _ _ _ _ Q _ Q' _ f hQ hf het
  classical
  letI : Algebra C (TensorProduct A Ω C) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (TensorProduct A Ω B) := Algebra.TensorProduct.rightAlgebra
  set ψ := ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp
    (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom) with hψ
  letI : Algebra (TensorProduct A Ω C) (Localization.Away f) := ψ.toAlgebra
  haveI : Algebra.Etale (TensorProduct A Ω C) (Localization.Away f) := het
  haveI : IsScalarTower Ω (TensorProduct A Ω C) (Localization.Away f) :=
    IsScalarTower.of_algebraMap_eq fun w => by
      change _ = ψ _
      simp [hψ, Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply Ω (TensorProduct A Ω B) (Localization.Away f)]

  have hunit : IsUnit (algebraMap (TensorProduct A Ω B) Q'.ResidueField f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hf
  letI : Algebra (Localization.Away f) Q'.ResidueField :=
    (Localization.awayLift (algebraMap (TensorProduct A Ω B) Q'.ResidueField) f hunit).toAlgebra
  have hlift : ∀ s, algebraMap (Localization.Away f) Q'.ResidueField
      (algebraMap (TensorProduct A Ω B) (Localization.Away f) s) =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField s := fun s =>
    IsLocalization.Away.lift_eq f hunit s
  have hBK : ∀ b : B, algebraMap B Q'.ResidueField b =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField (algebraMap B (TensorProduct A Ω B) b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q') Q'.ResidueField,
      IsScalarTower.algebraMap_apply B (TensorProduct A Ω B) (Localization.AtPrime Q'),
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra C Q'.ResidueField := ((algebraMap B Q'.ResidueField).comp (algebraMap C B)).toAlgebra
  haveI : IsScalarTower C B Q'.ResidueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨eB, heB⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω B (TensorProduct A Ω B)
    (Localization.Away f) Q'.ResidueField (fun x => by rw [hlift, hBK])
  obtain ⟨eC, heC⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω C (TensorProduct A Ω C)
    (Localization.Away f) Q'.ResidueField (fun x => by
      change algebraMap B Q'.ResidueField (algebraMap C B x) =
        algebraMap (Localization.Away f) Q'.ResidueField (ψ ((1 : Ω) ⊗ₜ[A] x))
      rw [hBK, hψ, RingHom.comp_apply, hlift]
      congr 1)
  set K := Q'.ResidueField
  let E := eC.trans eB.symm
  have hE : ∀ c : C, E ((1 : K) ⊗ₜ[C] KaehlerDifferential.D A C c) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (algebraMap C B c) := by
    intro c
    simp only [E, LinearEquiv.trans_apply, heC, LinearEquiv.symm_apply_eq, heB]
    rfl
  have hE' : ∀ ω : Ω[C⁄A], E ((1 : K) ⊗ₜ[C] ω) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro ω
    have hω : ω ∈ Submodule.span C (Set.range (KaehlerDifferential.D A C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; rw [hE, KaehlerDifferential.map_D]
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul c x _ hx =>
      have h1 : (1 : K) ⊗ₜ[C] (c • x) = algebraMap C K c • ((1 : K) ⊗ₜ[C] x) := by
        rw [TensorProduct.tmul_smul]; exact (algebraMap_smul K c _).symm
      rw [h1, map_smul, hx, LinearMap.map_smul_of_tower, ← algebraMap_smul B c,
        TensorProduct.tmul_smul, ← algebraMap_smul K (algebraMap C B c)]
      rfl
  have hE'' : ∀ (k : K) (ω : Ω[C⁄A]), E (k ⊗ₜ[C] ω) = k ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro k ω
    have h1 : k ⊗ₜ[C] ω = k • ((1 : K) ⊗ₜ[C] ω) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h1, map_smul, hE', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  letI : Algebra Q.ResidueField K :=
    (Ideal.ResidueField.map Q Q' (algebraMap B (TensorProduct A Ω B)) (by rw [← hQ]; rfl)).toAlgebra
  haveI : IsScalarTower B Q.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, hBK]
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_bijective_iff_bijective Q.ResidueField K]
  let cM := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K
    (TensorProduct C B Ω[C⁄A])
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K Ω[B⁄A]
  let cC := TensorProduct.AlgebraTensorModule.cancelBaseChange C B K K Ω[C⁄A]
  have key : ∀ z, ((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K z =
      cN.symm (E (cC (cM z))) := by
    intro z
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add (f := _), h₁, h₂]
      | tmul l m =>
        induction m using TensorProduct.induction_on with
        | zero => simp
        | add m₁ m₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add (f := _), h₁, h₂]
        | tmul b ω =>
          simp only [cM, cN, cC, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            KaehlerDifferential.mapBaseChange_tmul, hE'', TensorProduct.smul_tmul]
  have hfun : ⇑(((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K) =
      ⇑cN.symm ∘ ⇑E ∘ ⇑cC ∘ ⇑cM := funext key
  rw [hfun]
  exact cN.symm.bijective.comp (E.bijective.comp (cC.bijective.comp cM.bijective))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_of_closedPoints_closedFibre_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R),
    LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) →
    ∀ x : T, q x = closedPoint R → x ∈ U := by
  intro R _ _ T q hq U hU x hx
  by_contra hxU
  set c : Sp R := closedPoint R
  have hc : IsClosed ({c} : Set (Sp R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
  have hft : LocallyOfFiniteType (q.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : JacobsonSpace (q.fiber c) := LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)
  let e := q.fiberι c
  have hemb : Topology.IsClosedEmbedding e := by
    refine ⟨IsPreimmersion.isEmbedding e, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hc.preimage q.continuous
  let Z : Set T := closure {x} ∩ (U : Set T)ᶜ
  have hZ : IsClosed Z := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨x', hx'⟩ : x ∈ Set.range e := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  have hne : (e ⁻¹' Z).Nonempty := ⟨x', by
    show e x' ∈ Z
    rw [hx']; exact ⟨subset_closure rfl, hxU⟩⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed
  have hyc' : IsClosed ({e y} : Set T) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hyc
  have hqy : q (e y) = c := by
    have : e y ∈ Set.range e := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact hyZ.2 (hU _ hyc' hqy)

end GlobalTheory.Mum
end

