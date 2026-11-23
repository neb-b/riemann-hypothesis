module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalAtOfUnif
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyScalarIsUnitOnIntegralModels
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.KeyUnitModels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

open GlobalTheory.FlagMod (ev_res ev_spMap le_preimage_mono)

theorem norm_bounds {κ : KeyRule} (hκ : IsKeyRule κ) (x : KeyIn ℂ) {τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hab : GlobalTheory.KeyPow.charHalf _ a b) (hc : c₀ ≠ 0)
    (hN : GlobalTheory.KeyPow.NormalAt x τ Mx a b c₀) {C : ℝ} (hC : 0 < C) (h₁ : C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2)
    (h₂ : ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C) : ‖(κ ℂ x : ℂ)‖ ≤ C ^ 4 ∧ ‖(κ ℂ x : ℂ)⁻¹‖ ≤ C ^ 4 := by
  have hr : 0 < ‖Mx.det‖ / ‖c₀‖ ^ 2 := (inv_pos.2 hC).trans_le h₁
  have hM : Mx.det ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨P, hg, rig, hrig, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := GlobalTheory.KeyConst.exists_rescale P hg rig hrig th hth v hv τ Mx _ _ c₀ hc hM hN
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff _ _ _ _).1 hN₀
  have e := hκ.1 ℂ P hg rig hrig _ hth₀ v₀ hv₀ th hth v hv c₀ Mx e₁ hMv
  rw [hκ.2.2.2.1 ⟨P, hg, rig, hrig, th₀, hth₀, v₀, hv₀⟩ u τ a b k₁ k₂ hab.1 hab.2 k₃ k₄ k₅ k₆, Units.val_one,
    _root_.mul_one] at e
  have q : 0 < ‖c₀‖ := norm_pos_iff.2 hc
  have e' : ‖(κ ℂ ⟨P, hg, rig, hrig, th, hth, v, hv⟩ : ℂ)‖ = (‖Mx.det‖ / ‖c₀‖ ^ 2) ^ 4 := by
    have := congrArg (‖·‖) e
    simp only [norm_mul, norm_pow] at this
    rw [div_pow, ← pow_mul, eq_div_iff (by positivity), ← this, _root_.mul_comm]
  constructor
  · rw [e']
    gcongr
  · rw [norm_inv, e', ← inv_pow]
    gcongr
    exact inv_le_of_inv_le₀ hC h₁

theorem countable_sections {X : Scheme.{0}} {O : Type} [CommRing O] [Countable O] (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have hf : (s.appLE ⊤ _ le_top).hom.FiniteType :=
    (HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨_, hU⟩ le_top)
  letI := (s.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp O, ⊤) Γ(X, U) := hf
  have hc : Countable Γ(Sp O, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.symm.injective.countable
  obtain ⟨n, f, hfs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  have : Countable (MvPolynomial (Fin n) Γ(Sp O, ⊤)) :=
    (MvPolynomial.basisMonomials (Fin n) Γ(Sp O, ⊤)).repr.injective.countable
  exact hfs.countable

theorem exists_chart_unit {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (M : GChart Y) : ∃ u : Γ(Y.X, M.U), IsUnit u ∧ ∀ (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ Y.X)
      (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn K), Set.range z ⊆ Set.range Y.j → KeyAt M z hz x → (κ K x : K) = ev z M.U hz u := by
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, hopen⟩ := _root_.GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l c W
  have := Y.jQ_open
  have hj : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  obtain ⟨-, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen W c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  obtain ⟨W₀, f₀, hW, hf⟩ := _root_.GlobalTheory.KeyOpenModel.exists_unit_open E H D l Xo c _ _ Y inferInstance hj hpq κ hκ M
  have hcF : Countable c.F := by
    have := c.fin
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F
    rw [← Cardinal.mk_le_aleph0_iff]
    simpa [Cardinal.mkRat] using this
  have : Countable W := Subtype.val_injective.countable
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := M.dom
  have hpos : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) := by
    have h₁ := IsTotallyComplex.finrank E
    have h₂ : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact Nat.mul_pos (by omega) hpq
  have hWU : W₀ ≤ M.U := fun x hx => ((hW x).1 hx).1
  have hWj : ∀ {K : Type} [Field K] {z : Sp K ⟶ Y.X}, ⊤ ≤ z ⁻¹ᵁ W₀ → Set.range z ⊆ Set.range Y.j := fun hz => by
    rintro _ ⟨q, rfl⟩; exact ((hW _).1 (hz (Set.mem_univ q))).2
  have hne : ∃ x, x ∈ W₀ := by
    obtain ⟨q⟩ : Nonempty (Sp Γ(Y.X, M.U)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    obtain ⟨x, hx, hx'⟩ := hdense.exists_mem_open M.U.isOpen ⟨_, tau_le M.hU le_rfl (Set.mem_univ q)⟩
    exact ⟨x, (hW x).2 ⟨hx', hx⟩⟩
  obtain ⟨hinj, hext⟩ := GlobalTheory.GenExt.extend_of_integral_at_dvr _ _ W₀ hWU M.hU M.dom
    (IsLocallyNoetherian.component_noetherian ⟨_, M.hU⟩) (GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen M.hU)
    (countable_sections Y.s M.hU) hne
  have key : ∀ u : Γ(Y.X, W₀), (u = f₀.val ∨ u = (f₀⁻¹).val) → ∃ f, resG _ hWU f = u := by
    intro u hu
    refine hext u fun R K _ _ _ _ _ _ z hR hz h => ?_
    let y := IsOpenImmersion.lift Y.j (spMap (algebraMap R K) ≫ z) (hWj h)
    have : CharZero K := charZero_of_injective_ringHom (Spec.preimage (y ≫ pullback.snd _ _)).hom.injective
    refine GlobalTheory.T.integral_of_arcs_and_goodReduction_points E H D l Xo c W Y h3 h4 hs hj M.U W₀ u (fun x hx hx' => (hW x).2 ⟨hx, hx'⟩)
      (fun a χ hA hover hgen hχ => ?_) (fun R K _ _ _ _ _ _ _ z y hz hy hab h => ?_) R K z y hR hz
      (IsOpenImmersion.lift_fac _ _ _) h
    · obtain ⟨y, hy, T, C', hC', hT⟩ := GlobalTheory.ArcNormal.arc_normal_form _ _ _ _ _ _ _ Y hpq hP a χ hA hover hgen M hχ
      refine GlobalTheory.ArcReg.not_pole_of_bounded _ M.U W₀ u χ y M.hU hWU hχ hy ⟨T, C' ^ 4, fun w hw hyw => ?_⟩
      obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M (y w) (le_preimage_mono hWU hyw) (hWj hyw) hpos
      obtain ⟨τ, Mx, a', b', c₀, k₁, k₂, k₃, k₄, k₅⟩ := hT w hw _ x hk
      obtain ⟨b₁, b₂⟩ := norm_bounds hκ x k₁ k₂ k₃ hC' k₄ k₅
      have e := hf ℂ (y w) hyw _ x hk
      rcases hu with rfl | rfl
      · rwa [e]
      · rwa [map_units_inv, e]
    · obtain ⟨x, -, hk⟩ := GlobalTheory.KeyAtEx.exists_keyAt_model M _ (le_preimage_comp _ hz) (hWj h) hpos
      obtain ⟨v, hv⟩ := _root_.GlobalTheory.KeyUnitGood.isUnit_key_of_good E H D l Xo c _ _ Y κ hκ M R K z hz y hy hab x hk
      have e := hf K _ h _ x hk
      rcases hu with rfl | rfl
      · exact ⟨v, by rw [e, hv]⟩
      · exact ⟨(v⁻¹ : Rˣ), by rw [map_units_inv, map_units_inv, e, hv]⟩
  obtain ⟨f, hf₁⟩ := key _ (Or.inl rfl)
  obtain ⟨f', hf₂⟩ := key _ (Or.inr rfl)
  refine ⟨f, IsUnit.of_mul_eq_one f' (hinj ?_), fun K _ _ z hz x hr hk => ?_⟩
  · exact ((RingHom.map_mul _ f f').trans ((congrArg₂ (· * ·) hf₁ hf₂).trans f₀.mul_inv)).trans (RingHom.map_one _).symm
  · have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := fun q hq => (hW _).2 ⟨hz hq, hr ⟨q, rfl⟩⟩
    rw [← hf K z hz₀ _ x hk, ← hf₁, ev_res z hWU hz₀ hz]

theorem lieComb_one {K : Type} [Field K] (x : KeyIn K) (i : Fin x.P.g) :
    IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i) x.v (x.v i) := by
  have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i = Pi.single i 1 := by
    ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this]
  have := x.P.isAb.comm
  exact (GlobalTheory.LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i

theorem unitAt_local {W : ValuationSubring c.F} (Y : Model Xo c W.subtype) (hpq : 1 ≤ D.p + D.q)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule} (hκ : IsKeyRule κ)
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] :
    UnitAt κ Y V K := by
  intro y yt hyt t m n w hw θ x hx
  obtain ⟨⟨⟨_, hDed⟩, -, -⟩, -⟩ := _root_.GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l c W
  obtain ⟨M, hM⟩ := GlobalTheory.FlagMod.exists_gChart hP (yt (IsLocalRing.closedPoint V))
  have hz : ⊤ ≤ yt ⁻¹ᵁ M.U := ((IsLocalRing.closed_point_mem_iff (U := yt ⁻¹ᵁ M.U)).1 hM).ge
  obtain ⟨u, hu, hval⟩ := exists_chart_unit Y hpq hP h3 h4 hs hκ M
  have := t.semi.smooth
  obtain ⟨θ₀, h₀⟩ : ∃ θ₀ : t.PP.L.Sec, NonzeroClosed (X := t.G) θ₀ := by
    obtain ⟨-, θ₀, -, -, hne⟩ := GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact ⟨θ₀, g, h₁, TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  have hC : ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
      Generates (X := t.G) θ → ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := fun θ x hx hθ => by
    obtain ⟨x', a, d, hk, e⟩ := GlobalTheory.T.exists_generatingFrame_unit_change_to_chart E H D l Xo c _ _ Y M V K yt hz t m n w hw θ x hx hθ
    have e₁ := e κ hκ
    rw [hval K _ _ x' (by
      rw [hyt]; rintro _ ⟨q, rfl⟩; exact ⟨y q, (Scheme.Hom.comp_apply _ _ _).symm⟩) hk,
      ev_spMap (algebraMap V K) yt M.U hz, RingHom.comp_apply] at e₁
    refine ⟨(d ^ 4)⁻¹ * (a ^ 8 * (hu.map (ev yt M.U hz)).unit), ?_⟩
    have hd : algebraMap V K d ≠ 0 := (d.isUnit.map _).ne_zero
    rw [Units.val_mul, map_mul, map_units_inv, Units.val_mul, map_mul, IsUnit.unit_spec, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, e₁, inv_mul_cancel_left₀ (pow_ne_zero _ hd)]
  have hB : ∀ (θ : t.PP.L.Sec), Generates (X := t.G) θ → ∀ N : ℕ, Generates (X := pow t.G N) (boxSec t.G θ N) :=
    fun θ' hθ N => by
      obtain ⟨a, ha, -⟩ := hθ θ₀
      obtain ⟨hfl, g, hg, hnz⟩ := GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre V t.G t.PP.L θ' (NonzeroClosed.of_isMul ha h₀).2 N
      obtain ⟨X', p', φ, L', b, k₁, k₂, k₃, k₄⟩ := _root_.GlobalTheory.BoxLine.sections_line V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx N
      exact generates_of_generic_line (pow t.G N).hom k₁ (LB.isLB_linComb t.PP.isLB _ _) k₂ k₃ b k₄ _ hg hnz
  refine ⟨fun hθ => ⟨hC θ x hx hθ, fun N _ => hB θ hθ N⟩, ?_⟩
  intro N hN σ a hσ hmul
  have hg₀ := generates_of_isFibreOf t.PP.isLB hx h₀
  obtain ⟨b, hθb, -⟩ := hg₀ θ
  obtain ⟨th₀, hth₀, hth, hx₀⟩ := GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple V K _ t.G t.PP.L t.PP.rig θ n w x t.PP.isLB hx θ₀ b hθb
  obtain ⟨u₀, hu₀⟩ := hC θ₀ _ hx₀ hg₀
  have hbox₀ := hB θ₀ hg₀ N
  have hom := hκ.1 K x.P x.g_pos x.rig x.rig_gen th₀ hth₀ x.v x.basis x.th x.th_ne x.v x.basis (algebraMap V K b) 1
    hth (lieComb_one x)
  rw [Matrix.det_one, one_pow, _root_.one_mul] at hom
  obtain ⟨c', hc', -⟩ := hσ (boxSec t.G θ₀ N)
  have hcu : IsUnit c' := Generates.isUnit hσ hbox₀ hc'
  have ha : a = b ^ N * c' := (hσ (boxSec t.G θ N)).unique hmul (IsMul.trans (isMul_boxSec hθb N) hc')
  obtain ⟨k, rfl⟩ := hN
  refine ⟨hcu.unit * u₀ ^ k, ?_⟩
  rw [ha, Nat.mul_div_cancel_left k (by norm_num : 0 < 8)]
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu₀, ← hom, pow_mul]
  ring

theorem unitAt_valuation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (hpq : 1 ≤ D.p + D.q)
    (hβ : IsBaseRing β) (hP : PushInvertible Y.t.G Y.t.PP.L) (h3 : Y.N3) (h4 : Y.N4) (hs : Y.SplitFibres) {κ : KeyRule}
    (hκ : IsKeyRule κ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] : UnitAt κ Y V K := by
  intro y yt hyt t m
  have hinj := IsFractionRing.injective V K
  have sp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B),
      spMap f ≫ spMap g = spMap (f.comp g) := fun _ _ => (Spec.map_comp _ _).symm
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* K, spMap io = y ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : O →+* V, spMap b₀ = yt ≫ Y.s := ⟨_, Spec.map_preimage _⟩
  have hc : (algebraMap V K).comp b₀ = io.comp β := by
    have e : spMap ((algebraMap V K).comp b₀) = spMap (io.comp β) := by
      rw [← sp, ← sp, hb₀, hio, ← Category.assoc, hyt, Model.j, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let W : ValuationSubring c.F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  let b : O →+* W := β.codRestrict W.toSubring fun a => ⟨b₀ a, RingHom.congr_fun hc a⟩
  have hb : W.subtype.comp b = β := rfl
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  let b' : W →+* V := e.symm.toRingHom.comp ((io.comp W.subtype).codRestrict (algebraMap V K).range fun a => a.2)
  have hb' : b'.comp b = b₀ := RingHom.ext fun a => by
    apply e.injective
    exact (e.apply_symm_apply _).trans (Subtype.ext (RingHom.congr_fun hc a).symm)
  obtain ⟨_, _⟩ := _root_.GlobalTheory.ValLocal.preimmersion_flat E H l c O β hβ W b hb
  let yt' : Sp V ⟶ (locModel Y b hb).X := pullback.lift yt (spMap b') (by rw [sp, hb', hb₀])
  have hy' : yt' ≫ pullback.fst Y.s (spMap b) = yt := pullback.lift_fst _ _ _
  obtain ⟨m', -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := yt') (locMap Y b) (hy'.symm ▸ m)
  exact unitAt_local (locModel Y b hb) hpq (locModel_pushInvertible Y b hb (_root_.GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l c W).1 hP) (localisedModel_uniformisation_baseChange Y b hb h3)
    (_root_.GlobalTheory.LocArc.arc_localise E H D l Xo c O β Y _ _ b hb h4) (_root_.GlobalTheory.KeyUnitModels.SplitLoc.locModel_splitFibres E H D l Xo c O β Y _ _ b hb hs) hκ V K y yt' (by
      rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, Category.assoc, hy', locModel_j, hyt]) t m'

theorem keyUnitOnModels : KeyUnitOnModels := by
  intro κ hκ E _ _ _ H D l Xo c O _ β Y p h₁ h₂ _ h₄ h₅ h₆ h₇
  refine ⟨fun V K _ _ _ _ _ _ _ _ => unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V K, fun V C _ _ _ _ _ _ _ hV => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.GoodRedUnitBall.valuationRing_of_unitBall hV
  exact unitAt_valuation Y h₁ h₂ h₄.2.2.1 h₅ h₆ h₇ hκ V C

end GlobalTheory.KeyUnitModels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.CrossTheta₂

theorem sval_comp {X Y Y' Z : Scheme.{0}} {L : LB X} (p : Y' ⟶ X) {k : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => k))) (r : Z ⟶ Y) (c : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} {I : (Y ⟶ X) → L.ι} (hI : Good L (r z) I) (hc : I (c ≫ p) = J (r ≫ c ≫ p)) :
    sval s (r ≫ c) z J = (r.stalkMap z).hom (sval s c (r z) I) := by
  rw [sval_of s (r ≫ c) z J (fun _ => I (c ≫ p)) (fun _ => by rw [Category.assoc, hc])]
  exact GlobalTheory.CrossTheta.gs_comp_stalk r c z _ (hI.mem (fun _ : Fin 1 => p) c) _

theorem cross_val {X₁ X₂ Y₁ Y₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (p₁ : Y₁ ⟶ X₁) (p₂ : Y₂ ⟶ X₂) (b : Y₁ ⟶ Y₂) {k k' : ℤ}
    (s₁ s₂ : LB.Sec (LB.LinComb L₂ (fun _ : Fin 1 => p₂) (fun _ => k)))
    (s₁' s₂' : LB.Sec (LB.LinComb L₁ (fun _ : Fin 1 => p₁) (fun _ => k')))
    (H : ∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval s₁ b y J₂ * sval s₂' (𝟙 _) y J₁ = sval s₂ b y J₂ * sval s₁' (𝟙 _) y J₁)
    {Z : Scheme.{0}} (r : Z ⟶ Y₁) (z : Z) {J₁ J₂} (hJ₁ : Good L₁ z J₁) (hJ₂ : Good L₂ z J₂) :
    sval s₁ (r ≫ b) z J₂ * sval s₂' r z J₁ = sval s₂ (r ≫ b) z J₂ * sval s₁' r z J₁ := by
  obtain ⟨I₁, hI₁, e₁⟩ := exists_good L₁ hL₁ (r z) (K := Unit) (fun _ => 𝟙 _ ≫ p₁)
    (fun _ => J₁ (r ≫ 𝟙 _ ≫ p₁)) (fun _ _ _ => rfl) (fun _ => hJ₁ (r ≫ 𝟙 _ ≫ p₁))
  obtain ⟨I₂, hI₂, e₂⟩ := exists_good L₂ hL₂ (r z) (K := Unit) (fun _ => b ≫ p₂)
    (fun _ => J₂ (r ≫ b ≫ p₂)) (fun _ _ _ => rfl) (fun _ => hJ₂ (r ≫ b ≫ p₂))
  have h := congrArg (r.stalkMap z).hom (H (r z) I₁ I₂ hI₁ hI₂)
  rw [map_mul, map_mul, ← sval_comp p₂ s₁ r b z hI₂ (e₂ ()), ← sval_comp p₂ s₂ r b z hI₂ (e₂ ()),
    ← sval_comp p₁ s₁' r (𝟙 _) z hI₁ (e₁ ()), ← sval_comp p₁ s₂' r (𝟙 _) z hI₁ (e₁ ()), Category.comp_id] at h
  exact h

theorem translT_whisker {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {T : Over S} (c : A₁ ⟶ A₂)
    [IsMonHom c] (x : T ⟶ A₁) :
    translT A₁ x ≫ T ◁ c = T ◁ c ≫ translT A₂ (x ≫ c) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, whiskerLeft_snd, lift_snd, lift_snd_assoc, ThetaPowOrder.translPt_eq,
      MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc]

theorem cross_act {S : Scheme.{0}} {A₁ A₂ : Over S} [GrpObj A₁] [GrpObj A₂] {L₁ : LB A₁.left} {L₂ : LB A₂.left}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {T : Over S} (c : A₁ ⟶ A₂) [IsMonHom c] {k k' : ℤ}
    (θ : ThetaGrp A₂ L₂ k T) (θ' : ThetaGrp A₁ L₁ k' T) (hp : θ.pt = θ'.pt ≫ c)
    {t₁ t₂ T₁ T₂ : LB.Sec (LPow A₂ L₂ k T)} {t₁' t₂' T₁' T₂' : LB.Sec (LPow A₁ L₁ k' T)}
    (h₁ : IsActOf A₂ L₂ k θ t₁ T₁) (h₂ : IsActOf A₂ L₂ k θ t₂ T₂) (h₁' : IsActOf A₁ L₁ k' θ' t₁' T₁')
    (h₂' : IsActOf A₁ L₁ k' θ' t₂' T₂') :
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) t₁ (T ◁ c).left y J₂ * sval (L := L₁) t₂' (𝟙 _) y J₁ =
        sval (L := L₂) t₂ (T ◁ c).left y J₂ * sval (L := L₁) t₁' (𝟙 _) y J₁) ↔
    (∀ y J₁ J₂, Good L₁ y J₁ → Good L₂ y J₂ →
      sval (L := L₂) T₁ (T ◁ c).left y J₂ * sval (L := L₁) T₂' (𝟙 _) y J₁ =
        sval (L := L₂) T₂ (T ◁ c).left y J₂ * sval (L := L₁) T₁' (𝟙 _) y J₁) := by
  have cc : (T ◁ c).left ≫ (translT A₂ θ.pt).left = (translT A₁ θ'.pt).left ≫ (T ◁ c).left := by
    rw [← Over.comp_left, ← Over.comp_left, hp, translT_whisker]
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A₁).left) (z : Z) {J₁ J₂}, Good L₁ z J₁ → Good L₂ z J₂ →
      (sval (L := L₂) T₁ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₂' r z J₁ =
        sval (L := L₂) T₂ (r ≫ (T ◁ c).left) z J₂ * sval (L := L₁) T₁' r z J₁ ↔
      sval (L := L₂) t₁ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₂' (r ≫ (translT A₁ θ'.pt).left) z J₁ =
        sval (L := L₂) t₂ ((r ≫ (translT A₁ θ'.pt).left) ≫ (T ◁ c).left) z J₂ *
          sval (L := L₁) t₁' (r ≫ (translT A₁ θ'.pt).left) z J₁) := by
    intro Z r z J₁ J₂ hJ₁ hJ₂
    rw [ThetaPowOrder.act_sval h₁ _ z hJ₂, ThetaPowOrder.act_sval h₂ _ z hJ₂, ThetaPowOrder.act_sval h₁' _ z hJ₁,
      ThetaPowOrder.act_sval h₂' _ z hJ₁, Category.assoc, cc, ← Category.assoc, _root_.mul_mul_mul_comm,
      _root_.mul_mul_mul_comm _ (sval (L := L₂) t₂ _ z J₂), ← Units.val_mul, Units.mul_right_inj]
  constructor
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (𝟙 _) y hJ₁ hJ₂).2 (cross_val hL₁ hL₂ _ _ _ t₁ t₂ t₁' t₂' H _ y hJ₁ hJ₂)
    rwa [Category.id_comp] at h
  · intro H y J₁ J₂ hJ₁ hJ₂
    have h := (key (translT A₁ θ'.pt⁻¹).left y hJ₁ hJ₂).1 (cross_val hL₁ hL₂ _ _ _ T₁ T₂ T₁' T₂' H _ y hJ₁ hJ₂)
    rwa [← Over.comp_left, ThetaPowOrder.translT_comp, mul_inv_cancel, ThetaPowOrder.translT_one, Over.id_left,
      Category.id_comp] at h

end GlobalTheory.CrossTheta₂

namespace GlobalTheory

theorem crossH_iff_of_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j j' : ℕ) (θ : ThetaGrp A₂.A A₂.L (j : ℤ) (TFK (R := R) F)) (θ' : ThetaGrp A₁.A A₁.L (j' : ℤ) (TFK (R := R) F)), θ.pt = θ'.pt ≫ c → ∀ (t₁ t₂ T₁ T₂ : SecA A₂ F j) (t₁' t₂' T₁' T₂' : SecA A₁ F j'), IsActOf A₂.A A₂.L j θ t₁ T₁ → IsActOf A₂.A A₂.L j θ t₂ T₂ → IsActOf A₁.A A₁.L j' θ' t₁' T₁' → IsActOf A₁.A A₁.L j' θ' t₂' T₂' → (CrossH c t₁ t₂ t₁' t₂' ↔ CrossH c T₁ T₂ T₁' T₂') := by
  intro R _ _ A₁ A₂ F _ _ c hc j j' θ θ' hp t₁ t₂ T₁ T₂ t₁' t₂' T₁' T₂' h₁ h₂ h₁' h₂'
  haveI := hc
  exact CrossTheta₂.cross_act A₁.isLB A₂.isLB c θ θ' hp h₁ h₂ h₁' h₂'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  have h : (Finset.univ.val.map fun b => c (σ b)) = Finset.univ.val.map c := by
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
    rfl
  funext j
  unfold symTup
  rw [h]

theorem map_symTup {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  have h : (Finset.univ.val.map fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  unfold symTup
  rw [h, map_pow]
  congr 1
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

theorem exists_symTup_ne_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : ∃ a, c a ≠ 0) :
    ∃ j, symTup c j ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  by_contra hne
  push Not at hne
  have hc : Multiset.card (Finset.univ.val.map c) = N := by simp
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := by
    intro k hk hkN
    have := hne ⟨k - 1, by omega⟩
    unfold symTup at this
    have h2 := eq_zero_of_pow_eq_zero this
    simpa [Nat.sub_add_cancel hk] using h2
  have hp : ((Finset.univ.val.map c).map fun t => Polynomial.X - Polynomial.C t).prod = Polynomial.X ^ N := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero]
    · simp [Multiset.esymm]
    · intro k hk
      rw [he (k + 1) (Nat.succ_pos _) (Finset.mem_range.1 hk)]
      simp
  have hev := congrArg (Polynomial.eval (c a)) hp
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero] at hev
  · simp only [Polynomial.eval_pow, Polynomial.eval_X] at hev
    exact pow_ne_zero N ha hev.symm
  · simp only [Multiset.mem_map]
    exact ⟨_, ⟨c a, ⟨a, Finset.mem_univ_val a, rfl⟩, rfl⟩, by simp⟩

theorem symTup_basic :
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N),
      symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)),
      symTup (fun b => c (σ b)) = symTup c) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N),
      i (symTup c j) = symTup (fun b => i (c b)) j) ∧
    ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 :=
  ⟨fun _ _ _ c a j => symTup_mul c a j, fun _ _ _ c σ => symTup_perm c σ,
    fun _ _ _ _ i _ c j => map_symTup i c j, fun _ _ _ c h => exists_symTup_ne_zero c h⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaValuePointLiesOverModuliPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem valPt_lies_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ F.X), RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = y ≫ i → ∃ yK : X₁.S.R →+* FractionRing V₁, (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ spMap yK ≫ X₁.u = y := by
  intro g n F Z i W X₁ z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle).toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    fun a => rfl, ?_⟩
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      φ.comp ψ :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  haveI := X₁.imm
  haveI : IsProper X₁.z := X₁.isProper_compactificationMap
  haveI : Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from X₁.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {C : Type} [CommRing C] [IsLocalRing C] (q : Sp C ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint C) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro C _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of C) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap X₁.S.R.val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ X₁.u ≫ i = X₁.M.Z.fromSpecStalk w ≫ X₁.π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, X₁.comp]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono i, Category.assoc, hK]
  change spMap (φ.comp ψ) ≫ X₁.u ≫ i = y ≫ i
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.Poinc.Sep
end
end

