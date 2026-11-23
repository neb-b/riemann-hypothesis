module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_chartPull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_derivation_transport {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ r, D' (e r) = e (D r) := by
  let f : B →ₗ[ℤ] B :=
    { toFun := fun b => e (D (e.symm b)), map_add' := fun a b => by simp, map_smul' := fun k b => by simp }
  refine ⟨{ toLinearMap := f, map_one_eq_zero' := by simp [f], leibniz' := fun a b => ?_ }, fun r => by simp [f]⟩
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _),
    RingEquiv.apply_symm_apply]

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem isKS_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) → ∀ (V : X.Opens) (W : X.affineOpens) (W' : X'.affineOpens) (hW' : W'.1 = j ⁻¹ᵁ W.1), Function.Bijective (j.appLE W.1 W'.1 hW'.le).hom → W.1 ≤ V → W.1 ≤ j.opensRange → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', W'.1)) ⟶ t'.G.left)), (∀ i, IsTanAtG t (chart W) (v i)) → (∀ i, IsTanAtG t' (chart W') (v' i)) → (∀ i, v' i ≫ m.φ = spMap (dualMap (j.appLE W.1 W'.1 hW'.le).hom) ≫ v i) → ∀ (D : Γ(X, W.1) → Γ(X, W.1)) (D' : Γ(X', W'.1) → Γ(X', W'.1)), (∀ r, D' ((j.appLE W.1 W'.1 hW'.le).hom r) = (j.appLE W.1 W'.1 hW'.le).hom (D r)) → ∀ Θ' : Matrix (Fin n) (Fin n) Γ(X', W'.1), IsKS t' ⊤ W' v' D' Θ' → ∃ Θ, IsKS t V W v D Θ := by
  intro E _ _ _ H X X' t t' j _ m hcp V W W' hW' hbij hWV hWr n v v' hv hv't hvv D D' hD Θ' hKS
  obtain ⟨cp⟩ := hcp
  obtain ⟨J, Wc, jj, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  obtain ⟨hφo, hφr⟩ := _root_.GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  set ψ := j.appLE W.1 W'.1 hW'.le with hψ
  let e := RingEquiv.ofBijective ψ.hom hbij
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hx : chart W' ≫ j = spMap ψ.hom ≫ chart W :=
    (IsAffineOpen.SpecMap_appLE_fromSpec j W.2 W'.2 hW'.le).symm
  have hWc : ∀ i, Wc i ≤ t'.G.hom ⁻¹ᵁ W'.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t'.G.hom.preimage_mono inf_le_left))
  choose d₂ hd₂F hd₂ using fun i => _root_.GlobalTheory.LogKS.isField_image _ _ m.φ (Wc i) (d i) (hfld i)
  have hpi : ∀ i, m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) = Wc i := fun i => m.φ.preimage_image_eq (Wc i)
  have cong : ∀ {A B : Scheme.{0}} {f g : A ⟶ B} (_ : f = g) (U : B.Opens) (U' : A.Opens) (p₁ : U' ≤ f ⁻¹ᵁ U)
      (p₂ : U' ≤ g ⁻¹ᵁ U), f.appLE U U' p₁ = g.appLE U U' p₂ := by
    intros; subst_vars; rfl
  have happ : ∀ (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ W.1) (h' : m.φ ⁻¹ᵁ O ≤ t'.G.hom ⁻¹ᵁ W'.1)
      (r : Γ(X, W.1)), (m.φ.app O).hom ((t.G.hom.appLE W.1 O h).hom r) =
        (t'.G.hom.appLE W'.1 (m.φ ⁻¹ᵁ O) h').hom (ψ.hom r) := by
    intro O h h' r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, hψ,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, cong sq]
  have vpull : ∀ {A : Type} [CommRing A] (z : Sp A ⟶ t'.G.left) (U₁ : t.G.left.Opens) (U₂ : t'.G.left.Opens)
      (le : U₂ ≤ m.φ ⁻¹ᵁ U₁), ⊤ ≤ z ⁻¹ᵁ U₂ → ∀ y, valR z U₂ ((m.φ.appLE U₁ U₂ le).hom y) = valR (z ≫ m.φ) U₁ y := by
    intro A _ z U₁ U₂ le hz y
    have e : (m.φ.appLE U₁ U₂ le).hom y = resG _ le ((m.φ.app U₁).hom y) := rfl
    rw [e, GlobalTheory.CechKS.valR_resG z le hz, GlobalTheory.CechKS.valR_comp_app]
  refine ⟨e.symm.toRingHom.mapMatrix Θ', J, fun i => m.φ ''ᵁ Wc i, fun i => cp.idx (jj i), d₂, ?_, ?_, hd₂F, ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hsup, inf_top_eq, inf_eq_left.2 hWV, hW']
    have e1 : t'.G.hom ⁻¹ᵁ (j ⁻¹ᵁ W.1) = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ W.1) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq]
    rw [e1, Scheme.Hom.image_preimage_eq_opensRange_inf, hφr, ← Scheme.Hom.preimage_inf, inf_eq_right.2 hWr]
  · intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact cp.le _ (hj i hx)
  · intro i h r
    apply (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ Wc i))).1
    have hle : m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) ≤ Wc i := (hpi i).le
    rw [hd₂ i _ le_rfl, happ _ h (hle.trans (hWc i)), happ _ h (hle.trans (hWc i)),
      ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle, ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle,
      (hfld i).2.2 (Wc i) _ hle le_rfl, hcomp i (hWc i), hD]
  · intro i i' O hO f S _ φS g₀ w hg₀ hO' hw
    have hOr : ∀ y ∈ O, ∃ x, m.φ.base x = y := fun y hy => by
      obtain ⟨x, -, hx⟩ := (hO hy).1
      exact ⟨x, hx⟩
    have hg₀r : Set.range g₀.base ⊆ Set.range m.φ.base := by
      rintro _ ⟨p, rfl⟩
      exact hOr _ (hO' (Set.mem_univ p))
    set g₀' := IsOpenImmersion.lift m.φ g₀ hg₀r with hg₀'def
    have hg₀'φ : g₀' ≫ m.φ = g₀ := IsOpenImmersion.lift_fac _ _ _
    let φS' : Γ(X', W'.1) →+* S := φS.comp e.symm.toRingHom
    have hφS : φS'.comp ψ.hom = φS := by
      ext r
      show φS (e.symm (ψ.hom r)) = φS r
      congr 1
      exact e.symm_apply_apply r
    have spc : spMap φS' ≫ spMap ψ.hom = spMap (φS'.comp ψ.hom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hg₀' : g₀' ≫ t'.G.hom = spMap φS' ≫ chart W' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg₀'φ, hg₀, Category.assoc, hx,
        ← Category.assoc, spc, hφS]
    have hw' : ∀ a, ∃ w', w' ≫ m.φ = w a ∧ IsTranslate t' φS' g₀' (v' a) w' := fun a =>
      _root_.GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.hom (chart W) (chart W') hx (v a) (v' a) (hv a) (hv't a) (hvv a) S φS'
        g₀' hg₀' (w a) (by rw [hφS, hg₀'φ]; exact hw a)
    choose w' hw'φ hw'T using hw'
    have hOi : m.φ ⁻¹ᵁ O ≤ Wc i ⊓ Wc i' :=
      le_inf ((m.φ.preimage_mono (hO.trans inf_le_left)).trans (hpi i).le)
        ((m.φ.preimage_mono (hO.trans inf_le_right)).trans (hpi i').le)
    have hO'' : ⊤ ≤ g₀' ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := by
      rw [← Scheme.Hom.comp_preimage, hg₀'φ]
      exact hO'
    have key := htest i i' (m.φ ⁻¹ᵁ O) hOi ((m.φ.app O).hom f) S φS' g₀' w' hg₀' hO'' hw'T
    rw [← hg₀'φ, GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂ i O (hO.trans inf_le_left),
      hd₂ i' O (hO.trans inf_le_right), key]
    have hU' : ⊤ ≤ g₀' ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) :=
      hO''.trans (g₀'.preimage_mono (hOi.trans (inf_le_inf (hj i) (hj i'))))
    have hgp := _root_.GlobalTheory.chartPull_g_appLE _ _ t'.PP.L t.PP.L m.φ cp (jj i) (jj i')
    set le₀ : t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i') ≤ m.φ ⁻¹ᵁ (t.PP.L.U (cp.idx (jj i)) ⊓ t.PP.L.U (cp.idx (jj i'))) :=
      le_inf (inf_le_left.trans (cp.le (jj i))) (inf_le_right.trans (cp.le (jj i')))
    have hgi : ((t'.PP.L.g (jj i) (jj i'))⁻¹ : Γ(t'.G.left, _)ˣ).val =
        (m.φ.appLE _ _ le₀).hom ((t.PP.L.g (cp.idx (jj i)) (cp.idx (jj i')))⁻¹ : Γ(t.G.left, _)ˣ).val := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hgp, ← map_mul, Units.mul_inv, map_one]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hred := _root_.GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ _ φS' (chart W') g₀' (v' b) (w' b) hg₀' (hv't b) (hw'T b)
    have hwU : ⊤ ≤ w' b ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) := GlobalTheory.CechKS.le_preimage_of_red hred hU'
    rw [hgp, hgi, vpull _ _ _ le₀ hwU, vpull _ _ _ le₀ hU', hw'φ, hg₀'φ, ← hw'φ a, ← GlobalTheory.CechKS.valR_comp_app]
    rfl

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_isKS_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Y.X.affineOpens), W.1 ≤ interior Y → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, W.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart W) (v i)) → (∀ w, IsTanAtG Y.t (chart W) w → ∃! cf : Fin n → Γ(Y.X, W.1), IsCombAtG Y.t (chart W) v cf w) → ∀ D : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1), ∃ Θ, IsKS Y.t (interior Y) W v D Θ := by
  intro E _ _ _ H Dw l Xo c Y W hW n v hv hb D
  obtain ⟨t', m, hcp⟩ := exists_sab_chartPull Y.j Y.t
  obtain ⟨m', -⟩ := GlobalTheory.ArcChartExt.exists_sab_cancel_id Y.m m
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.KSObj.proper_ample_kTriv Y.oF m'
  have hWr : W.1 ≤ Y.j.opensRange := hW
  let W' : (Xo.XF c).affineOpens := ⟨Y.j ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion _ hWr⟩
  have hW' : W'.1 = Y.j ⁻¹ᵁ W.1 := rfl
  let ψ := Y.j.appLE W.1 W'.1 hW'.le
  have hx : chart W' ≫ Y.j = spMap ψ.hom ≫ chart W := (IsAffineOpen.SpecMap_appLE_fromSpec Y.j W.2 W'.2 hW'.le).symm
  have hbij : Function.Bijective ψ.hom := by
    have e : Y.j ''ᵁ (Y.j ⁻¹ᵁ W.1) = W.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hWr]
    have key : ψ = Y.X.presheaf.map (eqToHom e).op ≫ (Y.j.appIso (Y.j ⁻¹ᵁ W.1)).hom := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rw [key]
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨v', hv'φ, hv't, hv'b⟩ := _root_.GlobalTheory.SabTan.tanBasis_sabMap E H _ _ Y.t t' Y.j m _ _ ψ.hom (chart W) (chart W') hx n v hv hb
  obtain ⟨D', hD'⟩ := exists_derivation_transport (RingEquiv.ofBijective ψ.hom hbij) D
  obtain ⟨Θ', hΘ'⟩ := _root_.GlobalTheory.KSExists.exists_isKS E H _ t' hP hA hK W' n v' hv't hv'b D'
  exact isKS_transport E H _ _ Y.t t' Y.j m hcp (interior Y) W W' hW' hbij hW hWr n v v' hv hv't hv'φ D D'
    (fun r => hD' r) Θ' hΘ'

end GlobalTheory.KSInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem GlobalTheory.homotopyInvariance_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  classical
  intro q _ A _ _ hq
  have hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R := by
    intro d
    induction d with
    | zero =>
      intro R _ _ _ hd
      apply _root_.GlobalTheory.EtC.hInv_of_subsingleton
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
    | succ d ih =>
      intro R _ _ hR hd
      have hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D := by
        intro D _ _ _ hD hDd
        refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)
        intro x hx
        have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
          rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
          exact (algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))
        have h0 : x = 0 := by
          apply hinj
          have := congrArg Subtype.val (RingHom.mem_ker.mp hx)
          simpa using this
        rw [h0]; exact zero_mem _
      refine GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_
      revert hd
      induction ringKrullDim R with
      | bot => intro _; exact bot_le
      | coe n =>
        intro h
        have h' : n < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))
  let S : Finset A → Subalgebra ℤ A := fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))
  have hmono : Monotone S := fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))
  have hcov : ∀ a, ∃ s, a ∈ S s := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  have hunit : ∀ s, IsUnit (q : S s) := by
    intro s
    have hm : (↑(hq.unit⁻¹) : A) ∈ S s := Algebra.subset_adjoin (Set.mem_insert _ _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    simp
  have hinv : ∀ s, HInv q (S s) := by
    intro s
    have : Algebra.FiniteType ℤ (S s) := by
      have hfg' : (S s).FG := by
        have : (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A) := by simp
        rw [show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]
        exact Subalgebra.fg_adjoin_finset _
      exact Subalgebra.fg_iff_finiteType _ |>.mp hfg'
    have hlt := GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d := by
      revert hlt
      induction ringKrullDim (S s) with
      | bot => intro _; exact ⟨0, bot_le⟩
      | coe n =>
        intro h
        induction n with
        | top => exact absurd h (lt_irrefl _)
        | coe m => exact ⟨m, le_rfl⟩
    exact hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  intro i
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenDesc

theorem isSemiAbelian_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) (hG : IsSemiAbelian G) :
    IsSemiAbelian G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := he
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)

theorem mono_jK (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

end GlobalTheory.Mum.EvenDesc


set_option maxHeartbeats 2000000 in
open GlobalTheory.Mum.EvenDesc in
theorem GlobalTheory.Mum.evenOn_of_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (P : GlobalTheory.UU.CP G₁), FinExt ρ → IsGrpPullback G₁ G (spMap ρ) β → κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → LBIso (P.L.L.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G₁) X) → EvenOn P := by
  intro R _ _ _ hR G _ _ hG A gen hgen W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW R' _ _ _ ρ G₁ _ _ β κ₁ P
    hfin hG₁ hκ₁ hP X _ _ _ hTQ

  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := GlobalTheory.Mum.TraitExt.exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    _root_.GlobalTheory.TraitExt.exists_finite_trait_extension R W R' hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hGW' : IsSemiAbelian GW := isSemiAbelian_of_isGrpPullback hGW hG
  have hG₁' : IsSemiAbelian G₁ := isSemiAbelian_of_isGrpPullback hG₁ hG

  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hPu⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hGW' UW
  have hw1 : LBIso U''.LG.L
      (UW.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj GW)).hom.left ≫ pullback.fst GW.hom (specOf iw))) :=
    ⟨hPu.lg.choose, hPu.lg.choose_spec.1⟩

  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) GW (spMap iw) (pullback.fst GW.hom (specOf iw)) :=
    isGrpPullback_pullback GW (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [GlobalTheory.Mum.TraitExt.spMap_comp, GlobalTheory.Mum.TraitExt.spMap_comp, hcomm]
  have hpb2 := hpb1.comp hGW
  have hsq : (pullback.fst GW.hom (specOf iw) ≫ βW) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hGW.1.w, ← Category.assoc, pullback.condition]
    rfl
  obtain ⟨β'', hβ1, hβ2⟩ : ∃ β'' : ((Over.pullback (specOf iw)).obj GW).left ⟶ G₁.left,
      β'' ≫ β = pullback.fst GW.hom (specOf iw) ≫ βW ∧
        β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ :=
    ⟨hG₁.1.lift _ _ hsq, hG₁.1.lift_fst _ _ _, hG₁.1.lift_snd _ _ _⟩
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) G₁ (spMap φ₁) β'' :=
    hG₁.cancel (hpb2.congr hsp hβ1.symm) hβ2

  have hGW₁ : IsSemiAbelian ((Over.pullback (specOf iw)).obj GW) := IsSemiAbelian.pullback _ GW hGW'
  obtain ⟨P'', hP''L, hP''E⟩ := GlobalTheory.Mum.unif_evenOn W₁ hAW₁ D'' A'' _ hGW₁ U''

  have hprop : IsProper (pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)) := by
    have hi : IsIso U''.gen.hom.left := ((Over.forget _).mapIso U''.gen).isIso_hom
    have := A''.isAb.proper
    have hw : pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) = U''.gen.hom.left ≫ A''.A.hom :=
      (Over.w U''.gen.hom).symm
    rw [hw]; infer_instance

  have c1 : pullback.fst GW.hom (specOf iw) ≫ GW.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap iw :=
    pullback.condition
  have c2 : pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ ((Over.pullback (specOf iw)).obj GW).hom =
      pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ jK W₁ := pullback.condition
  have e1 : jK W₁ ≫ spMap iw = GlobalTheory.ArcPull.genMap hiwi ≫ jK W := by
    have := GlobalTheory.ArcPull.fracMap_sq hiwi
    rwa [Category.id_comp] at this
  have e2 : jK W₁ ≫ spMap φ₁ = GlobalTheory.ArcPull.genMap hφ₁i ≫ jK R' := by
    have := GlobalTheory.ArcPull.fracMap_sq hφ₁i
    rwa [Category.id_comp] at this
  obtain ⟨kW, hkW⟩ : ∃ kW : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback GW.hom (jK W),
      kW ≫ pullback.fst GW.hom (jK W) =
        pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw) := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hiwi) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, Category.assoc, e1]
  obtain ⟨kG, hkG⟩ : ∃ kG : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback G₁.hom (jK R'),
      kG ≫ pullback.fst G₁.hom (jK R') = pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β'' := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hφ₁i) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, hβ2, ← Category.assoc, c2, Category.assoc, Category.assoc, e2]
  have hkk : kW ≫ κ = kG ≫ κ₁ := by
    haveI := mono_jK R
    apply (cancel_mono (pullback.fst G.hom (jK R))).1
    rw [Category.assoc, Category.assoc, hκ, hκ₁, ← Category.assoc, ← Category.assoc, hkW, hkG, Category.assoc,
      Category.assoc, hβ1]
  have ga : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw))) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso hw1 _ (by simp)
  have gb : LBIso (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫
      pullback.fst GW.hom (specOf iw))) ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kW hkW.symm rfl hUW
  have gc : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kG hkG.symm hkk hP
  have gd : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    GlobalTheory.GenSpread.lbIso_pull_pull P.L.isLB _ rfl
  have hLg : ((A.L.pull gen.hom.left).pull (kW ≫ κ)).IsLB := pull_isLB (pull_isLB A.isLB _) _
  have hgen' : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB UW.LG.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) ga
      (LBIso.trans (pull_isLB UW.LG.isLB _) hLg (pull_isLB (pull_isLB P.L.isLB _) _) gb
        (LBIso.trans hLg (pull_isLB P.L.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) gc.symm gd))

  haveI : IsNoetherianRing W₁ := hAW₁.1
  haveI : IsIntegrallyClosed W₁ := hAW₁.2.2.1
  haveI : Smooth ((Over.pullback (specOf iw)).obj GW).hom := hGW₁.smooth
  haveI : GeometricallyIntegral ((Over.pullback (specOf iw)).obj GW).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hGW₁.smooth hGW₁.geomConnected
  have hLB : LBIso U''.LG.L (P.L.L.pull β'') :=
    GlobalTheory.Mum.lbIso_of_generic_local W₁ _ (eSec ((Over.pullback (specOf iw)).obj GW))
      (Over.w η[(Over.pullback (specOf iw)).obj GW]) _ _ U''.LG.isLB (pull_isLB P.L.isLB _) hgen'
  have hLB' : LBIso P''.L.L (P.L.L.pull β'') := by rw [hP''L]; exact hLB

  exact _root_.GlobalTheory.Mum.evenOn_of_local R' W₁ φ₁ hφ₁l G₁ hG₁' _ β'' hpb3 hprop P P'' hLB' hP''E X hTQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DefIrred

theorem integrable_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X}
    (hω : GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω) (hs : ∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0)
    {ν : Measure (GA D M)} {𝓕 : Set (GA D M)} (hν : IsHaarFD M ν 𝓕) :
    ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  intro Φ hΦ
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn false M) X Φ := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  exact (_root_.GlobalTheory.DefSourceInt.theta_integral_source_definite D ψ false M X χ χ' ω ν 𝓕 Φ hω (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs τ)) hν.1 hν.2
    hth).1

end GlobalTheory.DefIrred

end
end

