module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)
open GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB GlobalTheory.LieVB.TangentSurj
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.TanFibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ π = 𝟙 X)
  {x : Sp k ⟶ X} {v v' : (specO k (DualNumber k)).left ⟶ Y}

def form (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e) :
    (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k) :=
  baseMap (sec_hom (epsZero k)) w we ≫ (epsIso k).hom

theorem form_d (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ e ⁻¹ᵁ W) (f : Γ(Y, W)) {U : (Sp k).Opens} (hU : U ≤ x ⁻¹ᵁ V)
    (q : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W) (a b : Γ(Sp k, U))
    (H : v.appLE W _ q f = (specO k (DualNumber k)).hom.appLE U _ le_rfl a +
      (specO k (DualNumber k)).hom.appLE U _ le_rfl b * resG _ le_top (epsFn k)) :
    (form w we).app U (pullbackSections x _ hU (d he h f)) = b := by
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  refine (congrArg ((epsIso k).hom.app U) (baseMap_d he (sec_hom (epsZero k)) w we h hU hV q f)).trans ?_
  rw [H, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : U ≤ ⊤)))).trans (_root_.mul_one b)

theorem preimage_le (we : sec (epsZero k) ≫ v = x ≫ e) {U : (Sp k).Opens} {W : Y.Opens}
    (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ e) ⁻¹ᵁ W := h h₁
  rw [← we] at h₂
  exact h₂

theorem appLE_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {U : (Sp k).Opens} (hU : IsAffineOpen U) {W : Y.Opens} (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(Y, W)) :
    v.appLE W _ (preimage_le we h) f =
      (specO k (DualNumber k)).hom.appLE U _ le_rfl ((x ≫ e).appLE W U h f) +
        (specO k (DualNumber k)).hom.appLE U _ le_rfl
          ((form w we).app U (pullbackSections x _ h (d he le_rfl f))) * resG _ le_top (epsFn k) := by
  obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k U hU).2 (v.appLE W _ (preimage_le we h) f)
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have hb := form_d he w we le_rfl f h (preimage_le we h) a b E.symm
  have ha : (x ≫ e).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero k)).appLE _ U hV) E
    simp only [map_add (f := _), map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      resG_self, appLE_appLE we _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact E.symm


include he in
theorem eq_of_form_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    (w' : v' ≫ π = (specO k (DualNumber k)).hom ≫ x) (we' : sec (epsZero k) ≫ v' = x ≫ e)
    (H : form w we = form w' we') : v = v' := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, hW', -⟩ := QCoh.exists_affine_mem_le (U := ⊤)
    (e (x ((specO k (DualNumber k)).hom t))) trivial
  obtain ⟨U, hU, hU', h⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ e ⁻¹ᵁ W)
    ((specO k (DualNumber k)).hom t) hW'
  have hT : IsAffineOpen ((specO k (DualNumber k)).hom ⁻¹ᵁ U) := hU.preimage _
  have E : v.appLE W _ (preimage_le we h) = v'.appLE W _ (preimage_le we' h) := by
    ext f
    exact (appLE_eq he w we hU h f).trans (H ▸ (appLE_eq he w' we' hU h f).symm)
  refine ⟨(specO k (DualNumber k)).hom ⁻¹ᵁ U, hU', ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we h),
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we' h), E]


include he in
theorem exists_form_eq [QuasiSeparated π]
    (L : (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k)) :
    ∃ (v : (specO k (DualNumber k)).left ⟶ Y) (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x)
      (we : sec (epsZero k) ≫ v = x ≫ e), form w we = L := by
  let e' : Sp k ⟶ pullback π x := pullback.lift (x ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd π x = 𝟙 _ := pullback.lift_snd _ _ _
  have we' : e' ≫ pullback.fst π x = x ≫ e := pullback.lift_fst _ _ _
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have : QuasiCompact e' :=
    have : QuasiCompact (e' ≫ pullback.snd π x) := he' ▸ inferInstance
    .of_comp _ (pullback.snd π x)
  have := isIso_baseMap he he' (IsPullback.of_hasPullback π x) we'
  let β := baseMap he' (IsPullback.of_hasPullback π x).w we'
  let D := homEquivDer _ he' (inv β ≫ L)
  let u := deform (specO k (DualNumber k)).hom (epsFn k) (epsFn_sq k) D
  have w : (u ≫ pullback.fst π x) ≫ π = (specO k (DualNumber k)).hom ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, deform_comp _ _ _ D he']
  have we : sec (epsZero k) ≫ u ≫ pullback.fst π x = x ≫ e := by
    rw [← Category.assoc, comp_deform _ _ (epsFn_sq k) D (sec_hom (epsZero k)) (epsZero_epsFn k), we']
  refine ⟨_, w, we, pullback_hom_ext he fun W f => ?_⟩
  have k₁ : x ⁻¹ᵁ e ⁻¹ᵁ W ≤ e' ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := le_of_sq we' le_rfl le_rfl
  have k₂ := (specO k (DualNumber k)).hom.preimage_mono k₁
  let g := (pullback.fst π x).appLE W _ le_rfl f
  refine (form_d he w we le_rfl f le_rfl (preimage_le we le_rfl) (e'.appLE _ _ k₁ g) (val D k₁ g) ?_).trans ?_
  · have k₃ : (specO k (DualNumber k)).hom ⁻¹ᵁ x ⁻¹ᵁ e ⁻¹ᵁ W ≤ u ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := k₂
    have e₁ : u.appLE _ _ k₃ g = resG _ k₂ (psi _ _ (epsFn_sq k) D _ g) :=
      deform_appLE _ _ (epsFn_sq k) D _ k₂ g
    rw [← appLE_appLE (f := u) (g := pullback.fst π x) rfl le_rfl k₃, e₁, psi_apply, map_add (f := _), map_mul, LB.resG_resG, DualPull.resG_appLE, DualPull.resG_appLE,
      ← DualPull.resG_appLE e' k₁ le_rfl, DualPull.appLE_resG,
      show val D k₁ g = resG _ k₁ (val D le_rfl g) from (D.res_app le_rfl k₁ g).symm, DualPull.appLE_resG]
  · have b := baseMap_d he he' (IsPullback.of_hasPullback π x).w we' le_rfl le_rfl k₁ le_rfl f
    have c : val D k₁ g = (inv β ≫ L).app _ (d he' k₁ g) := homEquivDer_app he' (inv β ≫ L) k₁ g
    rw [c, ← b]
    generalize pullbackSections x (conormal e) _ (d he _ f) = s
    have i : β ≫ inv β ≫ L = L := IsIso.hom_inv_id_assoc β L
    conv_rhs => rw [← i]
    rw [Scheme.Modules.Hom.comp_app β, AddCommGrpCat.comp_apply]

theorem exists_hom_of_isFrame {F : X.Modules} {n : ℕ} {s : Fin n → Γ(F, ⊤)} (hs : IsFrame s) (c : Fin n → Γ(X, ⊤)) :
    ∃ L : F ⟶ structureModule X, ∀ l, L.app ⊤ (s l) = c l := by
  refine ⟨homGlobalEquiv _ _ (∑ i, c i • hs.coord i), fun l => ?_⟩
  change dualApp (∑ i, c i • hs.coord i) le_rfl (s l) = c l
  have hsum (T : Finset (Fin n)) : dualApp (∑ i ∈ T, c i • hs.coord i) le_rfl (s l) = if l ∈ T then c l else 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have := dualApp_smul (0 : Γ(X, ⊤)) (hs.coord l) le_rfl
      rw [zero_smul, map_zero, zero_smul] at this
      rw [Finset.sum_empty, this]
      simp
    | insert i T hi ih =>
      have := hs.dualApp_coord_frame i l le_rfl
      rw [Twist.resM_self] at this
      rw [Finset.sum_insert hi, dualApp_add, LinearMap.add_apply, ih, dualApp_smul, LinearMap.smul_apply, this,
        resG_self]
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  simpa using hsum Finset.univ

theorem existsUnique_tanEv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  intro E _ _ _ H X t k _ x V h n m hm c
  have := t.semi
  have hf : IsFrame fun l => pullbackSections x (omega t.G) h (m l) := by
    have := (hm.pullback x).res h
    exact (funext fun l => QCoh.res_pullbackSections x (omega t.G) le_rfl h (m l)) ▸ this
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame hf fun l => cst k (c l)
  obtain ⟨v, w, we, hv⟩ := exists_form_eq (sec_hom η[t.G]) L
  have hv' : IsTanAtG t x v := ⟨w, we.trans (by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl)⟩
  have hval (l) : tanEv t hv' h (m l) = c l :=
    (congrArg (fun (a : Γ(Sp k, ⊤)) => (Scheme.ΓSpecIso (.of k)).hom a)
      ((congr(($hv).app ⊤ _)).trans (hL l))).trans (Iso.inv_hom_id_apply _ _)
  refine ⟨v, ⟨hv', hval⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  refine eq_of_form_eq (sec_hom η[t.G]) hu.1 (epsZero_comp_of_isTanAtG t hu) w we (hom_ext_of_isFrame hf fun l => ?_)
  exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ((hu' l).trans (hval l).symm)

end GlobalTheory.TanFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibre
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.GenFibreComp

theorem exists_fn_hom {F L : Type} [Field F] [Field L] {V : Scheme.{0}} [IsIntegral V] (p : V ⟶ Sp F)
    (g : Sp L ⟶ V) (hg : g (IsLocalRing.closedPoint L) = genericPoint V) (ψ : F →+* L) (hψ : g ≫ p = spMap ψ) :
    ∃ φ : V.functionField →+* L, φ.comp (GlobalTheory.Cartier.constFn p) = ψ := by
  have hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V := hg ▸ specializes_rfl
  refine ⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩
  have h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g
      = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
    exact congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans
      (Category.id_comp _))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = CommRingCat.ofHom ψ := by
    rw [← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h1] at h2
  ext a
  have h3 := congrArg (fun t => t.hom a) h2
  refine Eq.trans ?_ h3
  have h4 : p.appLE ⊤ ⊤ le_top = p.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [← h4]
  rfl

theorem isProjOver_comp_equiv {F K : Type} [Field F] [Field K] (e : F ≃+* K) {X : Scheme.{0}} (p : X ⟶ Sp K)
    (h : IsProjOver p) : IsProjOver (p ≫ spMap e.toRingHom) := by
  have hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have : IsIso (spMap e.symm.toRingHom) := ⟨_, hi, hi'⟩
  have h1 := (GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h
  have h2 := (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _
    inferInstance h1
  convert h2 using 1
  rw [IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]

theorem exists_vars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed (Xo := Xo) (c := c) → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1 := fun i => CompSplitPfD.cspD_gen i.2
  have hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1 := fun i => by
    by_contra hn
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _
      ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h))
      mem_connectedComponent (hgen i).mem
  let V : Comp Xo c → (gen Z).Opens := fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧
      ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom := fun i => by
    have : IrreducibleSpace (V i).toScheme := Subtype.irreducibleSpace (hcc _).1.1
    have : IsIntegral (V i).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hcl : IsClosedImmersion (V i).ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
    have hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) :=
      (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
    have hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
      simpa using h
    have hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]
      exact mem_connectedComponent
    let g : Sp (kap i) ⟶ (V i).toScheme := IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr
    have hg : g ≫ (V i).ι = genSp i ≫ Z.jQ := IsOpenImmersion.lift_fac _ _ _
    have hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i) := by
      exact (Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))
    have hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme := by
      have h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i) :=
        hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous
      obtain ⟨a, ha⟩ := h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
      have h2 : a = genPt i := CompSplitPfD.cspD_max i.2 (hgen i) a
        (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))
      apply (V i).ι.isOpenEmbedding.injective
      rw [hgp, ← ha, h2]
    obtain ⟨φ, hφ⟩ := exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg
      ((algebraMap c.F (kap i)).comp e.toRingHom) (by
        rw [reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]
        exact (congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)
    have : GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
      rintro a ⟨P, hP, hPa⟩
      let χ : (V i).toScheme.functionField →+* Om i := (algebraMap (kap i) (Om i)).comp φ
      have hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) =
          (algebraMap c.F (Om i)).comp e.toRingHom := by
        rw [RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]
      obtain ⟨b, hb⟩ := hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩
      refine ⟨e.symm b, χ.injective ?_⟩
      rw [← hb]
      exact (RingHom.congr_fun hχ _).trans (by simp)
    exact GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  choose B ε hd hs using key
  have hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i)) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  refine ⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [hrange]
    rw [← hpre] at hp
    exact hp
  · refine ⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩
    · beta_reduce
      rw [hrange]
      have h := (hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem
      rw [← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]
      exact mem_connectedComponent
    · beta_reduce at hi
      rw [hrange] at hi
      apply Subtype.ext
      rw [← hpre, connectedComponent_eq hi]

end GlobalTheory.GenFibreComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeA
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms


set_option maxHeartbeats 4000000 in
theorem extendedData_liftFormsLattice_baseLevel_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and (StepW.and (_root_.GlobalTheory.Mem.R3.Rw.goodForms_lift_bc h1 h2 h3 h4 h5 h6 h7) (_root_.GlobalTheory.Mem.R3.LiftForms.lift_Mj_base h1 h2 h3 h4 h5 h6 h7)) (_root_.GlobalTheory.Mem.R3.LiftRead.read_ext h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, ⟨H1, H2⟩, H3⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hM := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hJ := H3 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  obtain ⟨G, hGb, hGid⟩ := GlobalTheory.Mem.R3.LiftForms.exists_mat φ hn _ _ hW
  refine ⟨G, hGb, ?_, ?_⟩
  · exact GlobalTheory.Mem.R3.LiftForms.lat_coords φ hn _ _
      ((Module.finBasis _ _).linearIndependent.map' _ (Submodule.ker_subtype _)) G hGid _
      (fun x hx => GlobalTheory.Mem.R3.LiftForms.mem_span_basis _ ((z.R.FW j).Mj_sub_Wgood _ _ _ hx)) _ hM
  · intro y
    exact HEq.trans (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z'.R z'.F j' _)
      (HEq.trans (hJ _ _ (hGid y)) (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z.R z.F j y).symm)

end GlobalTheory.Mem.R3.LiftForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem pairwise_letters (Dw : Datum H) :
    (letters Dw).Pairwise fun x y : GlobalTheory.ShFam.Pad.Letter Dw => x.1 = y.1 → (x.2 : ℕ) < y.2 := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange _).imp ?_
    exact fun h _ => h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx y hy h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem get_bijective (Dw : Datum H) : Function.Bijective (letters Dw).get :=
  ⟨List.nodup_iff_injective_get.1 (LetterConjugation.nodup_letters Dw), fun x => List.get_of_mem (LetterConjugation.mem_letters Dw x)⟩

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

theorem comb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (u i)).left) a w ↔ w = (tv (∑ i, a i • u i)).left := by
  have h0 := (GlobalTheory.LieMet.isComb_iff u a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, hq'⟩ := h0
  obtain rfl : p = q := funext fun i => Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  exact hq'

end

theorem concat_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  intro E _ _ _ H Dw l c X t k _ f x u hu
  classical
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → TanM x t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  let e := Equiv.ofBijective _ (get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (tv (∑ i, cf i • U ⟨τ, i⟩)).left := fun τ cf w =>
    comb_iff (fun i => U ⟨τ, i⟩) cf w
  refine ⟨fun cf cf' w h h' => ?_, fun j cf w h0 h => ?_⟩
  · have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, -, -⟩ :=
      exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    let ρ := actR (x0 := x) (S := k) t.act
    have hE : ∀ τ (v : TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
        (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ (tv v).left := fun τ v =>
      forall_congr' fun a => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => GlobalTheory.LieMet.tan_ext h⟩
    have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) := fun τ a s => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hE τ (U ⟨τ, i⟩)).2 (hu.1 τ i).2 s, smul_comm]
    have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
    rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
    funext i
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
    have h2 := congrArg (proj ρ (embK c) α τ) h1
    rw [proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _), proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
    have h3 := hu.2 τ _ (GlobalTheory.LieMet.isTan_tv _) ((hE τ _).1 (hS τ fun i => cf (e.symm ⟨τ, i⟩)))
    exact congrFun (h3.unique ((hτ τ _ _).2 rfl) ((hτ τ _ _).2 (congrArg (fun z => (tv z).left) h2))) i
  · let B : GlobalTheory.ShFam.Pad.Letter Dw → k := fun y => if h : y.1 = ((letters Dw).get j).1 then cf (h ▸ y.2) else 0
    refine ⟨fun m => B ((letters Dw).get m), fun m hm => ?_, by simp [B], ?_⟩
    · have hp := List.pairwise_iff_get.1 (pairwise_letters Dw) j m hm
      show B ((letters Dw).get m) = 0
      revert hp
      generalize (letters Dw).get m = y
      obtain ⟨τ, i⟩ := y
      intro hp
      by_cases hy : τ = ((letters Dw).get j).1
      · subst hy
        exact (dif_pos rfl).trans (h0 _ (hp rfl))
      · exact dif_neg hy
    · rw [hc, (hτ _ _ _).1 h]
      congr 2
      have : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
      simp only [this]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ((letters Dw).get j).1]
      · exact Finset.sum_congr rfl fun i _ => by simp [B]
      · intro σ _ hσ
        exact Finset.sum_eq_zero fun i _ => by rw [show B ⟨σ, i⟩ = 0 from dif_neg hσ, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.Proof.frame_combination_coeff_unique
end

