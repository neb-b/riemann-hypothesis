module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_affineOpen_restrict_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  intro E _ _ _ H X t U W hW f _ n v hv hb
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  open scoped CategoryTheory.Obj in
    let φ := (X.presheaf.map (homOfLE hW).op).hom
    let x := GlobalTheory.LogKS.chart U
    have := t.semi.comm
    have := t.semi.smooth
    have h₁ := isGrpPullback_pullback t.G x
    have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
    have h₃ := h₂.comp h₁
    have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
    have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
      Functor.isCommMonObj_obj
    obtain ⟨a₁, b₁⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t x _ _ h₁
    obtain ⟨-, b₃⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ h₃
    choose u hu using fun i => a₁ (v i) (hv i)
    have hbase : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hb⟩
    have hs : Smooth ((Over.pullback x).obj t.G).hom :=
      inferInstanceAs (Smooth (pullback.snd t.G.hom x))
    obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ _ _ _ h₂ hs n u hbase
    have e : Chart.dualMapR φ = dualMap φ := by
      ext a <;> rfl
    have key := (b₃ n u').1 hb'
    have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
        spMap (dualMap φ) ≫ v i := fun i => by
      rw [← Category.assoc, hu', e, Category.assoc, hu]
    rw [← funext e']
    have hchart : spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
      IsAffineOpen.map_fromSpec U.2 W.2 (homOfLE hW).op
    rw [← hchart]
    exact key.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
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

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSPkg

open GlobalTheory.DeRham GlobalTheory.Cris

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem ksPackage : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  intro PP E _ _ _ H Dw l Xo c TF U δ K _ _ P hU y' hU' hs hev
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ y' = frX P := by
    apply GlobalTheory.FlagMod.xF_ext (Y := TF.Y)
    · rw [Category.assoc, hs, spMap_comp_spMap]
      congr 1
    · exact GlobalTheory.FlagMod.frX_snd P
    · have h1 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ (y' ≫ TF.Y.j)) ⁻¹ᵁ U.1 :=
        GlobalTheory.FlagMod.le_preimage_comp _ hU'
      rw [Category.assoc, ← GlobalTheory.FlagMod.spMap_ev _ U.2 h1, ← GlobalTheory.FlagMod.spMap_ev _ U.2 hU,
        GlobalTheory.FlagMod.ev_spMap _ _ _ hU' h1]
      refine congrArg (fun f => spMap f ≫ (U.2 : IsAffineOpen U.1).fromSpec) ?_
      ext r
      rw [RingHom.comp_apply, hev r]
      simp [GlobalTheory.FlagTan.red]
  have hx : GlobalTheory.FlagTan.IsTanX P (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp_spMap]
      rfl
    · rw [← Category.assoc, hred, GlobalTheory.FlagMod.frX_fst]
  have P5 := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G (y' ≫ pullback.fst _ _)
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G P.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hUn := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := _root_.GlobalTheory.PolExists.polForm_exists P5 Xo hπ
  have hadj := _root_.GlobalTheory.PolAdjoint.polForm_adjoint P5 Xo hπ a ha hpol
  have hK := _root_.GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P5 hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback P hπ a ha
  have hL := (P5.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := _root_.GlobalTheory.LieBasis.lifts_basis_mod_fil P5 P hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))),
      ∃ w, GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ => by
    obtain ⟨_, w, -, hw⟩ := _root_.GlobalTheory.KSExist.ksRow_exists_lieComb hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => _root_.GlobalTheory.KSExist.isKSValue_act hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, GlobalTheory.KSExist.conj_embK]) a₀
    exact ⟨w, hw⟩
  exact ⟨A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub, hb, _, hπ, hπ', rfl, hpol, hu,
    fun σ k => hbl ⟨σ, k⟩, hrow, hA, gA, hA', gA', LB.isLB_pull Xo.univ.t.PP.isLB _⟩

end GlobalTheory.KSPkg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem isLocalRing_tsz (S M : Type) [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M]
    [IsCentralScalar S M] : IsLocalRing (TrivSqZeroExt S M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

theorem isLocalHom_map {S M N : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    IsLocalHom ((TrivSqZeroExt.map L : TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N) : TrivSqZeroExt S M →+* TrivSqZeroExt S N) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

variable {X : Scheme.{0}}

def valAt {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (p : X) (h : x (IsLocalRing.closedPoint A) = p) :
    X.presheaf.stalk p →+* A :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom

theorem valAt_comp {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] (x : Sp A ⟶ X) (p : X) (hx : x (IsLocalRing.closedPoint A) = p)
    (hy : (spMap g ≫ x) (IsLocalRing.closedPoint B) = p) (f : X.presheaf.stalk p) :
    valAt (spMap g ≫ x) p hy f = g (valAt x p hx f) := by
  subst hx
  let ψ : X.presheaf.stalk (x (IsLocalRing.closedPoint A)) ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x ≫ CommRingCat.ofHom g
  have hψl : IsLocalHom ψ.hom := by
    show IsLocalHom (g.comp (Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom)
    infer_instance
  have e1 : Spec.map ψ ≫ X.fromSpecStalk _ = spMap g ≫ x := by
    simp only [ψ, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e2 := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of B)) e1
  have e3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)) (Spec.map ψ ≫ X.fromSpecStalk _) = ⟨_, ψ, hψl⟩ :=
    (SpecToEquivOfLocalRing X (CommRingCat.of B)).apply_symm_apply ⟨_, ψ, hψl⟩
  rw [e3] at e2
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.1 e2.symm
  dsimp only [SpecToEquivOfLocalRing, Equiv.coe_fn_mk] at h2
  have h2' : Scheme.stalkClosedPointTo (R := CommRingCat.of B) (spMap g ≫ x) =
      (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).inv ≫ ψ := h2
  simp only [valAt, h2', Iso.hom_inv_id_assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, ψ]
  rfl

theorem valAt_congr {A : Type} [CommRing A] [IsLocalRing A] {x x' : Sp A ⟶ X} (e : x = x') (p : X)
    (h : x (IsLocalRing.closedPoint A) = p) (h' : x' (IsLocalRing.closedPoint A) = p) :
    valAt x p h = valAt x' p h' := by
  subst e; rfl

end GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

namespace GlobalTheory.CoordsOrigin

open GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem tanDer_add : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)),
    tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  intro R _ _ G _ _ u v f
  haveI : IsLocalRing (TrivSqZeroExt R (R × R)) := isLocalRing_tsz R (R × R)
  let P : overAt (𝟙 (Sp R)) (TrivSqZeroExt R (R × R)) ⟶ G :=
    (homAt (𝟙 (Sp R)) (tm (LinearMap.inl R R R)) ≫ tv u) * (homAt (𝟙 (Sp R)) (tm (LinearMap.inr R R R)) ≫ tv v)
  have hz : (0 : R →ₗ[R] R) = (0 : R) • (LinearMap.id : R →ₗ[R] R) := by simp
  have hid : ∀ w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G,
      homAt (𝟙 (Sp R)) (tm (LinearMap.id : R →ₗ[R] R)) ≫ w = w := by
    intro w
    simp only [tm]
    rw [TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
  have hfst : homAt (𝟙 (Sp R)) (tm (LinearMap.fst R R R)) ≫ P = tv u := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz]
    change _ * smT (𝟙 (Sp R)) 0 (tv v) = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.mul_one, hid]
  have hsnd : homAt (𝟙 (Sp R)) (tm (LinearMap.snd R R R)) ≫ P = tv v := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz]
    change smT (𝟙 (Sp R)) 0 (tv u) * _ = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.one_mul, hid]
  have hsum : homAt (𝟙 (Sp R)) (tm (LinearMap.coprod (LinearMap.id : R →ₗ[R] R) LinearMap.id)) ≫ P = tv (u + v) := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.coprod_inl, LinearMap.coprod_inr,
      hid, hid, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add]
  have hP : P.left (IsLocalRing.closedPoint (TrivSqZeroExt R (R × R))) = origin G := by
    have e : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left = (tv u).left := congrArg (fun q => q.left) hfst
    haveI := isLocalHom_map (LinearMap.fst R R R)
    have e0 : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) (IsLocalRing.closedPoint (DualNumber R)) =
        IsLocalRing.closedPoint (TrivSqZeroExt R (R × R)) :=
      Spec_closedPoint (f := CommRingCat.ofHom _)
    rw [← e0, ← tv_closedPoint G u, ← e]
    rfl
  have key : ∀ (L : R × R →ₗ[R] R) (w : TanM (𝟙 (Sp R)) G), homAt (𝟙 (Sp R)) (tm L) ≫ P = tv w →
      tanDer G w f = L (valAt P.left (origin G) hP f).snd := by
    intro L w hw
    haveI := isLocalHom_map L
    have e : (tv w).left = spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left := (congrArg (fun q => q.left) hw).symm
    have hy : (spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left) (IsLocalRing.closedPoint (DualNumber R)) = origin G :=
      e ▸ tv_closedPoint G w
    rw [tanDer_eq]
    change (valAt (tv w).left (origin G) (tv_closedPoint G w) f).snd = _
    rw [valAt_congr e (origin G) _ hy, valAt_comp _ P.left (origin G) hP hy]
    simp [tm]
  rw [key _ _ hsum, key _ _ hfst, key _ _ hsnd]
  simp

end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin


set_option backward.isDefEq.respectTransparency false in
theorem stalkClosedPointTo_localMap_comp {X : Scheme.{0}} {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B]
    (x : Spec A ⟶ X) (g : A ⟶ B) [IsLocalHom g.hom] (y : Spec B ⟶ X) (hy : y = Spec.map g ≫ x) (x₀ : X)
    (h₁ : x (IsLocalRing.closedPoint A) = x₀) (h₂ : y (IsLocalRing.closedPoint B) = x₀) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo y =
      ((X.presheaf.stalkCongr (Inseparable.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo x) ≫ g := by
  subst h₁
  have hy' : y = Spec.map (Scheme.stalkClosedPointTo x ≫ g) ≫ X.fromSpecStalk _ := by
    rw [hy, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  clear hy
  subst hy'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo x ≫ g).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo x ≫ g) U _

theorem tanDer_smul : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  intro R _ _ G _ _ r v f
  have hl : IsLocalHom (CommRingCat.ofHom (epsMul r)).hom := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hy : (tv (r • v)).left = Spec.map (CommRingCat.ofHom (epsMul r)) ≫ (tv v).left := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left]
  have key := stalkClosedPointTo_localMap_comp (A := CommRingCat.of (DualNumber R)) (B := CommRingCat.of (DualNumber R))
    (tv v).left (CommRingCat.ofHom (epsMul r)) (tv (r • v)).left hy (origin G) (tv_closedPoint G v)
    (tv_closedPoint G (r • v))
  rw [tanDer_eq, tanDer_eq]
  refine (congrArg (fun φ => (φ.hom f).snd) key).trans ?_
  have hs : ∀ a : DualNumber R, (epsMul r a).snd = r * a.snd := fun a => by simp [epsMul]
  exact hs _

end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauPeriodValNegCubicalRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauNeg

theorem val_tau_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (D.tau (-a) (-b)) (𝟙 _) z J * cubV D.cub z J (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c (-a)) (toUnit (TK R) ≫ D.c b) * (cubV D.cub z J (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c (-b)) (toUnit (TK R) ≫ D.c (-a)))⁻¹ := by
  intro R _ _ D hB a b z J hJ
  have xadd : ∀ u v : D.X, toUnit (TK R) ≫ D.c (u + v) = (toUnit (TK R) ≫ D.c u) * (toUnit (TK R) ≫ D.c v) := by
    intro u v; rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have x0 : toUnit (TK R) ≫ D.c 0 = 1 := by
    have h := xadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have face (x y : TK R ⟶ D.P.A) : cubV D.cub z J 1 x y = 1 := by
    have h := val_corr hJ (D.cub.face 0) (lift x y).left
    rw [val_one] at h
    refine Eq.trans ?_ h
    refine Eq.trans ?_ (val_cub D.cub (lift x y) hJ (pzero D.P.A _) (x2 D.P.A 0) (x2 D.P.A 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have B : ∀ u u' w v : D.X, u + u' = w → val (D.tau w v) (𝟙 _) z J *
      cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) =
      val (D.tau u v) (𝟙 _) z J * val (D.tau u' v) (𝟙 _) z J := by
    rintro u u' w v rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
    have hc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 u u' v)) (𝟙 _) z J =
        cubV D.cub z J (toUnit (TK R) ≫ D.c u) (toUnit (TK R) ≫ D.c u') (toUnit (TK R) ≫ D.c v) := by
      refine (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans ?_
      rw [Category.id_comp, Category.id_comp, Category.id_comp]
    rw [← hc]
    exact h
  have sym : ∀ u v : D.X, val (D.tau u v) (𝟙 _) z J = val (D.tau v u) (𝟙 _) z J := by
    intro u v
    simp only [DegPre.tau, val_mul hJ, val_inv]
    rw [add_comm u v, mul_right_comm (val (D.psi (v + u)) (𝟙 _) z J)]
  have T0 : ∀ v : D.X, val (D.tau 0 v) (𝟙 _) z J = 1 := by
    intro v
    have h := B 0 v v v (zero_add v)
    rw [x0, face, _root_.mul_one] at h
    exact (mul_eq_right.1 h.symm)
  have e1 := B a (-a) 0 b (add_neg_cancel a)
  have e2 := B b (-b) 0 (-a) (add_neg_cancel b)
  rw [T0, _root_.one_mul] at e1 e2
  rw [e1, e2, sym b (-a), sym (-b) (-a)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

theorem GlobalTheory.tensor_fraction_injective_of_injective
    (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K]
    (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L) (hβ : Function.Injective β)
    (hβt : ∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r)
    (n : ℕ) (u : Fin n → K) (r : Fin n → R₁) (h : ∑ j, c (r j) * θ (u j) = 0) :
    ∑ j, u j ⊗ₜ[R] r j = 0 := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) (Finset.univ : Finset (Fin n)) u
  choose x hx using fun j => hs j (Finset.mem_univ j)

  have hx' : ∀ j, algebraMap B K (x j) = algebraMap B K (s : B) * u j := by
    intro j; rw [hx j, Algebra.smul_def]
  have h0 : ∑ j, x j ⊗ₜ[R] r j = 0 := by
    apply hβ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    simp only [hβt, hx', map_mul]
    calc ∑ j, θ (algebraMap B K (s : B)) * θ (u j) * c (r j)
        = θ (algebraMap B K (s : B)) * ∑ j, c (r j) * θ (u j) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have h1 := congrArg ((IsScalarTower.toAlgHom R B K).toLinearMap.rTensor R₁) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom', map_zero] at h1
  have h2 : (algebraMap B K (s : B)) • ∑ j, u j ⊗ₜ[R] r j = 0 := by
    rw [Finset.smul_sum]
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, hx'] using h1
  have hne : algebraMap B K (s : B) ≠ 0 :=
    (IsLocalization.map_units K s).ne_zero
  have := congrArg (fun z => (algebraMap B K (s : B))⁻¹ • z) h2
  simp only [smul_zero] at this
  rwa [inv_smul_smul₀ hne] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ x / χ' x
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

end GlobalTheory.ThKRatInv
end
end

