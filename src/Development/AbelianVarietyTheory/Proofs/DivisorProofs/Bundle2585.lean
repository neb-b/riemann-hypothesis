module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetLineTrivialOfToroidal
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem good_or (c : Coeff l) (e : c.F →+* ℂ) :
    Formalism.L2.PjFree.GoodEmb c e ∨ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp e) := by
  set z := (e.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hz
  have h1 : z ^ 2 = H.rt0 ^ 2 := by rw [hz, ← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact .inl h
  · refine .inr (show starRingEnd ℂ z = H.rt0 from ?_)
    have h4 := H.sqrt_neg_disc_sq
    have h5 := congrArg Complex.im h4
    have h6 := congrArg Complex.re h4
    have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two] at h5 h6
    have h8 : H.rt0.re = 0 := by
      by_contra h0
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h0
      rw [this] at h6
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [h]
    exact Complex.ext (by simp [h8]) (by simp)

section Unique

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {τ : E →+* ℂ} {p q : ℕ}

theorem existsUnique_multiple {V : X.Opens} (hne : (V : Set X).Nonempty)
    (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {σ σ' : Rule t π p q} (hz : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (a : c.F) (h : ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V (Geo.Tor.constFn s V a) * σ R x v w) :
    ∃! a : c.F, IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := by
  have h1 : IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := fun R _ j x v w hf => by
    rw [h R j x v w hf, GlobalTheory.Points.valR_constFn_of_over s j x hf.1 V (fun z _ => hf.2.1 ⟨z, rfl⟩)]
  refine ⟨a, h1, fun b hb => ?_⟩
  obtain ⟨z, hzV⟩ := hne
  obtain ⟨W, hW, j, v, w, hzW, hf⟩ := hc z hzV
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  exact j.injective ((hz _ j _ v w hf).mul_right_cancel ((hb _ j _ v w hf).symm.trans (h1 _ j _ v w hf)))

end Unique

variable {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_of_geomConn {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) :
    (U : Set (Xo.XF c)).Nonempty := by
  have := _root_.GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected E H D l Xo c U hG
  exact ⟨_, (genericPoint U.toScheme).2⟩

theorem flat_unique {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (e : c.F →+* ℂ) (hT : HasTransport Xo c U e) {σ σ' : RuleU Xo c}
    (hs : SecU Xo c U τ σ) (hz : NzU Xo c U τ σ) (hf : IsFlatAt Xo c U τ σ e) (hs' : SecU Xo c U τ σ')
    (hf' : IsFlatAt Xo c U τ σ' e) :
    ∃! a : c.F, IsMultiple Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ' a σ := by
  have hc := _root_.GlobalTheory.DetLine.frameCover_univ E H D l Xo c U τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ U σ σ' hc hs hz hs'
  have fr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → Set.range y ⊆ U → ∃ v w, FrU Xo c U τ e y v w :=
    fun y hy hU => by
      obtain ⟨W, hW, j, v, w, hzW, h⟩ := hc _ (hU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)
      have hle : ⊤ ≤ y ⁻¹ᵁ W := (GlobalTheory.Points.le_preimage_iff y W).2 hzW
      have hy' := (GlobalTheory.Points.specMap_valMap_fromSpec hW y hle).symm
      obtain ⟨v', w', h', -⟩ := exists_pull (GlobalTheory.Points.valMap y W hle).hom h hy'
      obtain rfl : e = (GlobalTheory.Points.valMap y W hle).hom.comp j :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans h'.1))
      exact ⟨v', w', h'⟩
  obtain ⟨a, rfl⟩ := _root_.GlobalTheory.OneValue.exists_eq_constFn_of_one_value E H D l Xo c U e f hG fun y y' hy hy' hU hU' => by
    obtain ⟨v, w, h⟩ := fr y hy hU
    obtain ⟨v', w', h'⟩ := fr y' hy' hU'
    obtain ⟨o, m, g, u, Hm, κ, V, W, hA, hV, hW, iV, iW⟩ := _root_.GlobalTheory.DetLine.exists_unif_of_frame E H D l Xo c U τ e y v w h
    obtain ⟨o', m', g', u', Hm', κ', V', W', hA', hV', hW', -⟩ := _root_.GlobalTheory.DetLine.exists_unif_of_frame E H D l Xo c U τ e y' v' w' h'
    obtain ⟨φ, hφ⟩ := hT y y' hy hy' hU hU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm' κ κ' hA hA'
    obtain ⟨x, Δ, hΔ, hx⟩ := (_root_.GlobalTheory.DetLine.exists_wedgeCoord g _ _ Hm V W hA.1 hA.2.1).2 iV iW
    obtain ⟨Δ', hx'⟩ := (_root_.GlobalTheory.DetLine.exists_wedgeCoord g' _ _ Hm' V' W' hA'.1 hA'.2.1).1 fun k => φ (x k)
    have e1 := hf y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    have e2 := hf' y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    rw [hr ℂ e y v w h, hr ℂ e y' v' w' h', _root_.mul_assoc, _root_.mul_assoc, e1] at e2
    exact mul_right_cancel₀ (mul_ne_zero (hz ℂ e y' v' w' h').ne_zero hΔ) e2
  exact existsUnique_multiple (nonempty_of_geomConn hG) hc hz a hr

theorem cpt_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {U : (Xo.XF c).Opens}
    (hN : Geo.Tor.IsNormalScheme (gen Y)) (hU : IsClosed (U : Set (Xo.XF c)))
    (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {σ σ' : RuleY Y}
    (hs : SecY Y (compactOf Y U) τ σ) (hz : NzY Y (compactOf Y U) τ σ) (hs' : SecY Y (compactOf Y U) τ σ') :
    ∃! a : c.F, IsMultiple Y.t (genι Y) (genStr Y) (compactOf Y U) (HermitianCompactForm.chi c τ) σ' a σ := by
  obtain ⟨V, hV, -⟩ := _root_.GlobalTheory.DetLine.exists_open_compactOf_isIntegral E H D l Xo c O β Y U hN hU hG
  have hne : (V : Set (gen Y)).Nonempty := hV ▸ ((nonempty_of_geomConn hG).image _).closure
  have hk := _root_.GlobalTheory.CptConst.exists_eq_constFn_compactOf E H D l Xo c O β Y U V hN hU hG hV
  rw [← hV] at hs hz hs' ⊢
  have hc := _root_.GlobalTheory.DetLine.frameCover_gen E H D l Xo c O β Y V τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ V σ σ' hc hs hz hs'
  obtain ⟨a, rfl⟩ := hk f
  exact existsUnique_multiple hne hc hz a hr

def HasFlatSection (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) : Prop :=
  (∀ e : c.F →+* ℂ, HasTransport Xo c U e) ∧ ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ NzU Xo c U τ σ ∧
    (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ e) ∧
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Geo.Tor.IsNormalScheme (gen Y) →
      ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ

theorem exists_of_rank_zero (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (h : D.p + D.q = 0) : HasFlatSection Xo c U τ := by
  have : IsEmpty (Fin D.p) := ⟨fun i => by have := i.2; omega⟩
  have : IsEmpty (Fin D.q) := ⟨fun i => by have := i.2; omega⟩
  refine ⟨fun e => GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero E H D l Xo c U e h, fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun e => ?_, fun O _ β Y _ => ⟨fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩⟩
  intro y y' v w v' w' _ _ o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' _ _ _ _ _ _ _ ⟨a, _, ha⟩ ⟨a', _, ha'⟩
  rw [ha, ha', Matrix.det_isEmpty, Matrix.det_isEmpty]

theorem exists_of_snc {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z))
    {U : (Xo.XF c).Opens} (hU : IsClosed (U : Set (Xo.XF c))) (hG : GeometricallyConnected (U.ι ≫ toF Xo c))
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (hr : 1 ≤ D.p + D.q) : HasFlatSection Xo c U τ := by
  obtain ⟨B, io, h1, h2, h3⟩ := _root_.GlobalTheory.CompactVar.exists_var E H D l Xo c O β Z U hsm hU hG
  have fam : ∀ e : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c e → ∃ (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en)
      (x : ∀ i, Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx D τ) (Idx D τ) E),
      ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i) := fun e he => by
    let en : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
    obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
      (fun j => Formalism.L2.PjFree.relab c e (en j).1) hr he ((GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ en)
    choose x hm hx using fun i : Fin Fu.n => _root_.GlobalTheory.ShFam.Hor.PerBasis.exists_isPerBasis _ H D (Fu.Di i) τ (Fu.sig i)
    exact ⟨_, en, Fu, x, hm, hx⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀, Formalism.L2.PjFree.GoodEmb c e₀ := (good_or c c.F.val.toRingHom).elim (⟨_, ·⟩) (⟨_, ·⟩)
  obtain ⟨g₀, en₀, Fu₀, x₀, hm₀, hx₀⟩ := fam e₀ he₀
  obtain ⟨σZ, hsZ, hzZ⟩ := GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal E H D l Xo c O β Z τ e₀ _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he₀ hr hx₀)
  obtain ⟨σ, hs, hres, hz⟩ := _root_.GlobalTheory.DetLine.Restrict.exists_restriction E H D l Xo c O β Z U τ σZ hsZ
  have hflat : ∀ e, Formalism.L2.PjFree.GoodEmb c e → IsFlatAt Xo c U τ σ e := fun e he => by
    obtain ⟨g, en, Fu, x, hm, hx⟩ := fam e he
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate E H D l Xo c O β Z τ e _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he hr hx) σZ hsZ
    refine _root_.GlobalTheory.DetLine.FlatMul.isFlatAt_of_eq_perVal E H D l Xo c O β Z U τ e g en Fu x hm σZ σ κ B io hU h1 h2 h3 hτ hx hres
      fun a v w i Q hP hf hM => ?_
    rw [← horOf_eq_perVal hx a i Q hP]
    refine hκ a v w ?_ hf hM
    obtain ⟨P, W, y, -, -, hy, -⟩ := hP
    exact fun h => h ⟨y (IsLocalRing.closedPoint ℂ), by rw [← hy]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨fun e => ?_, σ, hs, hz hzZ, fun e => ?_, fun O' _ β' Y hN =>
    _root_.GlobalTheory.DetLine.ExtendNormal.exists_extension E H D l Xo c O' β' Y O β Z U τ σZ σ hN hU hG hτ hsZ hzZ hs hres⟩
  · rcases good_or c e with he | he
    · exact _root_.GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb E H D l Xo c O β Z U e B io hU h1 h2 h3 hr he
    · exact GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding E H D l Xo c U e (_root_.GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb E H D l Xo c O β Z U _ B io hU h1 h2 h3 hr he)
  · rcases good_or c e with he | he
    · exact hflat e he
    · exact GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj E H D l Xo c U τ σ e hs (hflat _ he)

theorem detLineTrivial_of_toroidal (hT : GlobalTheory.Published.ToroidalCompactification) : DetLineTrivial := by
  intro E _ _ _ H D l Xo c U hU hG τ hτ
  have hex : HasFlatSection Xo c U τ := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
    · exact exists_of_rank_zero U τ h
    · obtain ⟨Z, hsm, hsnc, -⟩ := hT E H D h l Xo c
      exact exists_of_snc Z
        ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm)
        (GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary hsnc) hU hG hτ h
  obtain ⟨htr, σ, hs, hz, hf, hY⟩ := hex
  refine ⟨htr, σ, hs, hz, hf, fun σ' hs' hf' => ?_, fun O _ β Y hN => ?_⟩
  · exact flat_unique hG hτ c.F.val.toRingHom (htr _) hs hz (hf _) hs' (hf' _)
  · obtain ⟨σb, h1, h2, h3⟩ := hY O β Y hN
    exact ⟨σb, h1, h2, h3, fun σ' h' => cpt_unique Y hN hU hG hτ h1 h2 h'⟩

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrders
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.ord_zpow_int {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  obtain ⟨m, rfl | rfl⟩ := r.eq_nat_or_neg
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]; ring

theorem DivOver.ord_finsetProd_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ)
    (e : ι → ℤ) : E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, E.ord_mul, ih, E.ord_zpow_int]

theorem DivOver.ord_eq_zero_of_unitAt_through {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {y : X} (hE : E.Through y) (v : X.functionFieldˣ)
    (h : UnitAt y (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, e⟩ := h
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, e⟩
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := by
    refine hE _ ⟨(ha.unit⁻¹ : (X.presheaf.stalk y)ˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val, ← e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have a1 := (E.ord_nonneg_iff v).2 h1
  have a2 := (E.ord_nonneg_iff v⁻¹).2 h2
  rw [E.ord_inv] at a2
  omega

end GlobalTheory.Discrepancy

namespace GlobalTheory.Discrepancy

theorem IsSncChart.discrep_eq_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  intro Y _ _ q n _ B y U hy z J w u hc η K Θ m g hη hK hm hΘ hg E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  set ω := formOf U (gen_mem hy) (dOn q z) with hω
  have hgen := isFreeGen_formOf (gen_mem hy) hc.frame
  have h0 : ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [← hω, h]))
  obtain ⟨c, hcη⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hcη]; simp [h])
  set k0 : Y.functionFieldˣ := Units.mk0 c hc0 with hk0
  have hηk : η = (k0 : Y.functionField) • ω := by rw [hk0, Units.val_mk0]; exact hcη.symm
  have hKy : K.IsEqn y k0 := hK U (dOn q z) hc.frame y hy k0 hηk
  have hΘy := GlobalTheory.T.snc_chart_divisor_equation ℂ Y q n B y U hy z J w u hc Θ hΘ
  set M : Y.functionFieldˣ := ∏ j ∈ J, u j ^ Θ.mult (w j) with hM
  have hsum : (Θ + m • K).IsEqn y (M * k0 ^ m) := hΘy.add (hKy.nsmul m)
  set v : Y.functionFieldˣ := g * (M * k0 ^ m)⁻¹ with hv
  have hvu : UnitAt y (v : Y.functionField) := by
    have := hsum.iff_unitAt.1 hg
    rwa [hv, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  have hv0 : E.ord v = 0 := E.ord_eq_zero_of_unitAt_through hE v hvu
  have hvo : E.ord v = E.ord g - (E.ord M + m * E.ord k0) := by
    rw [hv, E.ord_mul, E.ord_inv, E.ord_mul, E.ord_pow]; ring
  have hMo : E.ord M = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) := by
    rw [hM, E.ord_finsetProd_zpow]
  have hordg : E.ord g = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) + m * E.ord k0 := by
    rw [← hMo]; omega
  have hform : E.formOrd η = E.ord k0 + E.formOrd ω := by
    rw [hηk]; exact E.formOrd_smul hn h0 k0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, hform, hordg]
  push_cast
  have hs : ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * (E.ord (u j) : ℚ) =
      (∑ j ∈ J, (Θ.mult (w j) : ℚ) * E.ord (u j)) / m := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => div_mul_eq_mul_div _ _ _
  rw [hs]
  unfold DivOver.formOrd
  field_simp
  ring

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DzWedgeDzbarSumPowCardEqFactorialDetProd
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2.TopPow

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem eq_zero_of_eq_neg_self {x : R} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel x
  have h3 := congrArg (fun y : R => (1 / 2 : ℂ) • y) h2
  simp only [smul_smul, smul_zero] at h3
  norm_num at h3
  exact h3

theorem prod_eq_zero_of_pair {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → R) {i j : ι} (hij : i ≠ j)
    (h : f i * f j = 0) : ∏ k, f k = 0 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h, zero_mul]

theorem pow_card_sum_of_sq {B : Type} [Fintype B] [DecidableEq B] (w : B → R) (hw : ∀ a, w a * w a = 0) :
    (∑ a, w a) ^ Fintype.card B = (Fintype.card B).factorial • ∏ a, w a := by
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have key : ∀ g : Fin (Fintype.card B) → B,
      ∏ i, w (g i) = if Function.Injective g then ∏ a, w a else 0 := by
    intro g
    split_ifs with hg
    · exact Fintype.prod_bijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp⟩) _ _
        (fun _ => rfl)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
        by_contra h
        push_neg at h
        exact hg h
      exact prod_eq_zero_of_pair (fun k => w (g k)) hne (by simp only [hij]; exact hw _)
  simp only [key, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  congr 1
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]

theorem prod_perm {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (σ : Equiv.Perm B) :
    ∏ a, s a (σ a) = Equiv.Perm.sign σ • ∏ a, s a a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f x y hxy ih =>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy, mul_neg_one, Units.neg_smul, ← ih]
    have split : ∀ F : B → R, ∏ a, F a = F x * F y * ∏ a ∈ (Finset.univ.erase x).erase y, F a := fun F => by
      rw [mul_assoc, Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩),
        Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
    rw [split (fun a => s a ((f * Equiv.swap x y) a)), split (fun a => s a (f a))]
    have hrest : ∏ a ∈ (Finset.univ.erase x).erase y, s a ((f * Equiv.swap x y) a) =
        ∏ a ∈ (Finset.univ.erase x).erase y, s a (f a) := Finset.prod_congr rfl fun a ha => by
      have hay : a ≠ y := (Finset.mem_erase.1 ha).1
      have hax : a ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).1
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hay]
    rw [hrest]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hs, neg_mul]

theorem ι_three_swap {W : Type} [AddCommGroup W] [Module ℂ W] (v w x : W) :
    ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) =
      -(ExteriorAlgebra.ι ℂ x * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
  have h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q =
      -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p) :=
    fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)
  calc ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x)
      = (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ x := (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ x)) := by
      rw [h v w, neg_mul, mul_assoc]
    _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by
      rw [h v x, mul_neg, neg_neg, mul_assoc]
    _ = _ := by rw [h w x, neg_mul, mul_assoc]

theorem prod_smul_eq {ι : Type} [Fintype ι] (c : ι → ℂ) (x : ι → R) :
    ∏ a, c a • x a = (∏ a, c a) • ∏ a, x a := by
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

theorem sum_pow_card {B : Type} [Fintype B] [DecidableEq B] (s : B → B → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (K : Matrix B B ℂ) :
    (∑ a, ∑ b, K a b • s a b) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, s a a := by
  have hzero : ∀ a b c, s a b * s c b = 0 := fun a b c => eq_zero_of_eq_neg_self (hs a b c b)
  have hzero' : ∀ a b d, s a b * s a d = 0 := fun a b d =>
    eq_zero_of_eq_neg_self ((hs a b a d).trans (by rw [mul_comm]))
  have hw : ∀ a, (∑ b, K a b • s a b) * (∑ b, K a b • s a b) = 0 := fun a => by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
    rw [smul_mul_smul_comm, hzero', smul_zero]
  rw [pow_card_sum_of_sq _ hw, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp only [prod_smul_eq]
  have hnon : ∀ g : B → B, ¬ Function.Injective g → (∏ a, K a (g a)) • ∏ a, s a (g a) = 0 := by
    intro g hg
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
      by_contra h
      push_neg at h
      exact hg h
    rw [prod_eq_zero_of_pair (fun k => s k (g k)) hne (by simp only [hij]; exact hzero _ _ _), smul_zero]
  have hsum : ∑ g : B → B, (∏ a, K a (g a)) • ∏ a, s a (g a) =
      ∑ σ : Equiv.Perm B, (∏ a, K a (σ a)) • ∏ a, s a (σ a) := by
    have hm := Finset.sum_map (Finset.univ : Finset (Equiv.Perm B))
      ⟨fun σ : Equiv.Perm B => (σ : B → B), DFunLike.coe_injective⟩
      (fun g : B → B => (∏ a, K a (g a)) • ∏ a, s a (g a))
    simp only [Function.Embedding.coeFn_mk] at hm
    rw [← hm]
    refine (Finset.sum_subset (Finset.subset_univ _) fun g _ hg => hnon g fun hi => hg ?_).symm
    exact Finset.mem_map.2 ⟨Equiv.ofBijective g hi.bijective_of_finite, Finset.mem_univ _, rfl⟩
  rw [hsum]
  simp only [prod_perm s hs, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  rw [← Finset.sum_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Matrix.det_transpose, Matrix.det_apply]
  congr 2
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm]

end GlobalTheory.FlagCell2.TopPow

namespace GlobalTheory.FlagCell2

theorem pow_card_sum_sym : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e →
    ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B =
      ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  intro n B _ _ e _ K
  refine TopPow.sum_pow_card (fun a b => sym (e a, e b)) (fun a b c d => ?_) K
  apply Subtype.ext
  change dz (e a) * dzb (e b) * (dz (e c) * dzb (e d)) = -(dz (e a) * dzb (e d) * (dz (e c) * dzb (e b)))
  simp only [dz, dzb, mul_assoc]
  rw [← mul_neg]
  congr 1
  exact TopPow.ι_three_swap _ _ _

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevels
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

theorem eq_zero_of_ev_cube : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  intro p k _ d G c
  have hnil : ∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i) := by
    intro n i
    cases i with
    | inl i => exact (c.nil n i).map (Algebra.TensorProduct.includeLeft (R := k) (S := k))
    | inr j => exact (c.nil₂ n j).map (Algebra.TensorProduct.includeRight (R := k))
  refine ⟨hnil, fun f hf => ?_⟩
  ext α
  obtain ⟨n, hn⟩ := c.presents.2 (α.degree + 1)
  have hs := c.presents.1 n
  have h2 := _root_.GlobalTheory.evA_tensor_presents k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n) (c.nil n)
    (c.nil₂ n) hs hs
  have h3 := _root_.GlobalTheory.evA_tensor_presents k (Fin d) (Fin d ⊕ Fin d) (G.A n) (G.A n ⊗[k] G.A n) (c.x n) (c.nil n)
    (c.x₂ n) (c.nil₂ n) (hnil n) hs h2.1
  have := (h3.2 (α.degree + 1) hn (h2.2 (α.degree + 1) hn hn) f (hf n (hnil n)) α (Nat.lt_succ_self _))
  simpa using this

end GlobalTheory.Katz.Chart
end

