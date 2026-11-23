module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameThetaConstPos
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_latMod (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LatMod Dw k) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
  change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
  rw [natCast_zsmul, ← map_nsmul]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_levGrp (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI := finite_latMod Dw hk
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem map_etaExpr {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) :
    φ (etaExpr k cf x w) = etaExpr k cf x (fun q => φ (w q)) := by
  haveI := finite_levGrp Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [etaExpr, finprod_eq_prod_of_fintype, map_prod, map_sum, map_mul, map_intCast]

theorem etaExpr_comp {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (g₀ : LevGrp Dw k) :
    etaExpr k cf x (fun q => w (g₀ q)) = etaExpr k cf x w := by
  unfold etaExpr
  exact finprod_eq_of_bijective (fun g : LevGrp Dw k => g₀ * g) (Group.mulLeft_bijective g₀) fun g => rfl

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_level_baseChange (hL : Laws) {R : ℕ} (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    ∃ ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G), IsFullLev Xo (R ^ 4) z.x ev' ∧
      ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (ψ (w q)) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  refine ⟨fun q => h ≫ ev q,
    ((_root_.GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S T ψ.toRingHom y.x z.x h rfl ev hev).1, fun q => ?_⟩
  exact (_root_.GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.1 S T ψ y z hm (ev q) (h ≫ ev q) rfl _ (hw q)

theorem existsUnique_nullVal (hL : Laws) {R : ℕ} (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (q : LatMod Dw (R ^ 4)) : ∃! w, IsNullVal Xo c (R ^ 2) y (ev q) w := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine (_root_.GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).1 S y (ev q) ?_
  have h1 := ((_root_.GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S S (RingHom.id S) y.x y.x (𝟙 _)
    (by simp [spMap]) ev hev).2 q
  rw [← pow_mul]
  exact h1

theorem etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T}
    {ev ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G)} {w w' : LatMod Dw (R ^ 4) → T}
    (hev : IsFullLev Xo (R ^ 4) z.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) z (ev q) (w q))
    (hev' : IsFullLev Xo (R ^ 4) z.x ev') (hw' : ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (w' q)) :
    etaExpr (R ^ 4) cf x w = etaExpr (R ^ 4) cf x w' := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine Module.eq_of_localization_maximal (R := T) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap T (Localization.AtPrime P)) _ _ fun P _ => ?_
  let ψ : T →ₐ[c.F] Localization.AtPrime P := IsScalarTower.toAlgHom c.F T _
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T _ ψ z
  obtain ⟨e, he, hv⟩ := exists_level_baseChange hL hR ψ hu hev hw
  obtain ⟨e', he', hv'⟩ := exists_level_baseChange hL hR ψ hu hev' hw'
  obtain ⟨g, hg⟩ := ((_root_.GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.2.1 _ u.x e he).2 e' he'
  have hww : (fun q => ψ (w' q)) = fun q => ψ (w (g q)) := funext fun q =>
    (existsUnique_nullVal hL hR he (g q)).unique (hg q ▸ hv' q) (hv (g q))
  change algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w) =
    algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w')
  rw [map_etaExpr _ hk, map_etaExpr _ hk]
  exact (etaExpr_comp cf x (fun q => ψ (w q)) g).symm.trans (congrArg _ hww.symm)

theorem map_etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S₁ S₂ T : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂] [Algebra c.F S₂]
    [CommRing T] [Algebra c.F T] (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z : FrPt Xo c T} (h₁ : FrMap ψ₁ y₁ z) (h₂ : FrMap ψ₂ y₂ z)
    {ev₁ : LatMod Dw (R ^ 4) → (ptO Xo y₁.x ⟶ Xo.univ.t.G)} {w₁ : LatMod Dw (R ^ 4) → S₁}
    {ev₂ : LatMod Dw (R ^ 4) → (ptO Xo y₂.x ⟶ Xo.univ.t.G)} {w₂ : LatMod Dw (R ^ 4) → S₂}
    (hev₁ : IsFullLev Xo (R ^ 4) y₁.x ev₁) (hw₁ : ∀ q, IsNullVal Xo c (R ^ 2) y₁ (ev₁ q) (w₁ q))
    (hev₂ : IsFullLev Xo (R ^ 4) y₂.x ev₂) (hw₂ : ∀ q, IsNullVal Xo c (R ^ 2) y₂ (ev₂ q) (w₂ q)) :
    ψ₁ (etaExpr (R ^ 4) cf x w₁) = ψ₂ (etaExpr (R ^ 4) cf x w₂) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨e₁, he₁, hv₁⟩ := exists_level_baseChange hL hR ψ₁ h₁ hev₁ hw₁
  obtain ⟨e₂, he₂, hv₂⟩ := exists_level_baseChange hL hR ψ₂ h₂ hev₂ hw₂
  exact (map_etaExpr ψ₁.toRingHom hk cf x w₁).trans
    ((etaExpr_eq_of_levels hL hR cf x he₁ hv₁ he₂ hv₂).trans (map_etaExpr ψ₂.toRingHom hk cf x w₂).symm)

theorem map_eq_of_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S} {v : T}
    (h₀ : EtaValAt Xo c R cf x y₀ v₀) (h : EtaValAt Xo c R cf x y v) : φ v₀ = v := by
  obtain ⟨S', _, _, α, y₀', ev₀, w₀, hα, hmα, hev₀, hw₀, e₀⟩ := h₀
  obtain ⟨T', _, _, β, y', ev, w, hβ, hmβ, hev, hw, e⟩ := h
  obtain ⟨U, _, _, ψ₁, ψ₂, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F S T' S' (β.comp φ) α hα
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T' U ψ₁ y'
  have hz₀ : FrMap (ψ₂.comp α) y₀ z :=
    hc ▸ FramedBaseChange.trans _ ψ₁ (FramedBaseChange.trans φ β hm hmβ) hz
  have key := map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel α ψ₂ hmα hz₀) hev hw hev₀ hw₀
  have hβi : Function.Injective β := hβ.injective
  refine hβi (hinj ?_)
  rw [e, key, ← e₀]
  exact DFunLike.congr_fun hc v₀

theorem exists_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ v, EtaValAt Xo c R cf x y v := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨B, _, φ₀, ev₀, hφ, hev₀⟩ := (_root_.GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).1 S y.x
  letI : Algebra c.F B := (φ₀.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₀ with commutes' := fun _ => rfl }
  obtain ⟨y', hm⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S B φ y
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) y'.x ev := by
    rw [hm.1]
    exact ⟨ev₀, hev₀⟩
  choose w hw using fun q => (existsUnique_nullVal hL hR hev q).exists
  obtain ⟨v, hv, -⟩ := GlobalTheory.existsUnique_preimage_of_faithfullyFlat c.F S B φ hφ (etaExpr (R ^ 4) cf x w)
    fun T _ _ ψ₁ ψ₂ hc => by
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c B T ψ₁ y'
      have hz₀ : FrMap (ψ₂.comp φ) y z := hc ▸ FramedBaseChange.trans φ ψ₁ hm hz
      exact map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel φ ψ₂ hm hz₀) hev hw hev hw
  exact ⟨v, B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, hv⟩

theorem etaValAt_existsUnique_natural : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, EtaValAt Xo c R cf x y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, EtaValAt Xo c R cf x y0 v0 → EtaValAt Xo c R cf x y v → φ v0 = v := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  refine ⟨fun S _ _ y => ?_, fun S T _ _ _ _ φ y₀ y hm v₀ v h₀ h => map_eq_of_etaValAt hL hR φ hm h₀ h⟩
  obtain ⟨v, hv⟩ := exists_etaValAt hL hR cf x y
  exact ⟨v, hv, fun v' hv' => map_eq_of_etaValAt hL hR (AlgHom.id c.F S) (FramedBaseChange.refl y) hv' hv⟩

end GlobalTheory.EtaForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_biextension_chart_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  first | exact @GlobalTheory.AnVal.exists_analytic_chart | exact GlobalTheory.AnVal.exists_analytic_chart | (intros; apply GlobalTheory.AnVal.exists_analytic_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameOfUnitUniformisationFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), letI : Algebra c.F ℂ := σ.toAlgebra; ∃ Φ : AnPt (Xo := Xo) (c := c) (U.un k x) W.g (fun j => relab c σ (W.e j).1) W.e, Φ.OfFam W.F (W.ik k) W.Pm ∧ Φ.Hm = Wu.Hm ∧ Φ.χ = Wu.χl ∧ Φ.fr = Wu.fr ∧ Φ.toAnFr.Rd 1 (U.un k x).s Wu.θ ∧ (∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ) ∧ (∀ (α : 𝓞 E) a, W.Pm (W.F.t (W.ik k) (α • a)) = tyAct (fun j => relab c σ (W.e j).1) α (W.Pm (W.F.t (W.ik k) a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo (U.un k x).x a = Φ.e ((l.M : ℂ)⁻¹ • W.Pm (W.F.t (W.ik k) a)) := by
  first | exact @GlobalTheory.AnVal.exists_anPt_of_unitAt | exact GlobalTheory.AnVal.exists_anPt_of_unitAt | (intros; apply GlobalTheory.AnVal.exists_anPt_of_unitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogSumSqFibreZeroAndNonposAtMax
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviFibre

theorem contDiffAt_two_of_eventually {n : ℕ} {f : V n → ℂ} {z0 : V n}
    (h : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ f z) : ContDiffAt ℂ 2 f z0 := by
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 h
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffAt_complex hUo
    (fun z hz => (hU z hz).differentiableWithinAt) hz 2

theorem sum_wd_mul {n : ℕ} {f : V n → ℂ} {z0 : V n} (h : DifferentiableAt ℂ f z0)
    (ξ : Fin n → ℂ) : ∑ j, wd n j f z0 * ξ j = fderiv ℂ f z0 (WithLp.toLp 2 ξ) := by
  have hξ : (WithLp.toLp 2 ξ : V n) = ∑ j, ξ j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (WithLp.toLp 2 ξ)]
    simp [bas]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hξ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wd_of_differentiableAt h, map_smul, smul_eq_mul, mul_comm]

theorem fderiv_eq_of_quot {n : ℕ} {f g : V n → ℂ} {z0 v : V n} (hf : DifferentiableAt ℂ f z0)
    (hg : DifferentiableAt ℂ g z0) (h0 : g z0 ≠ 0)
    (h : fderiv ℂ (fun z => f z / g z) z0 v = 0) :
    fderiv ℂ f z0 v = (fderiv ℂ g z0 v / g z0) * f z0 := by
  have hq : DifferentiableAt ℂ (fun z => f z / g z) z0 := by
    simp only [div_eq_mul_inv]
    exact hf.mul (hg.inv h0)
  have hev : f =ᶠ[𝓝 z0] fun z => (f z / g z) * g z := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with z hz
    field_simp
  rw [hev.fderiv_eq, fderiv_fun_mul hq hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h]
  field_simp
  ring

theorem levi_log_sum_eq_zero {n m : ℕ} (z0 : V n) (ξ : Fin n → ℂ) (s : Fin m → V n → ℂ)
    (k0 : Fin m) (hs : ∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) (h0 : s k0 z0 ≠ 0)
    (hq : ∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) :
    leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ = 0 := by
  have hne : (fun i => s i z0) ≠ 0 := fun h => h0 (congrFun h k0)
  have key := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n m s z0 ξ
    (fun k => contDiffAt_two_of_eventually (hs k)) hne
  have hJ : ReciprocityTheory.L2DbarEstimates.H.wJac n m s z0 *ᵥ ξ =
      (fderiv ℂ (s k0) z0 (WithLp.toLp 2 ξ) / s k0 z0) • (fun i => s i z0) := by
    funext i
    have := sum_wd_mul (hs i).self_of_nhds ξ
    rw [fderiv_eq_of_quot (hs i).self_of_nhds (hs k0).self_of_nhds h0 (hq i)] at this
    simpa [ReciprocityTheory.L2DbarEstimates.H.wJac, Matrix.mulVec, dotProduct] using this
  have hP : ReciprocityTheory.L2DbarEstimates.projPerp (fun i => s i z0) *ᵥ (fun i => s i z0) = 0 :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self _ hne
  rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at key
  simp only [ReciprocityTheory.L2DbarEstimates.sqNorm, Complex.normSq_eq_norm_sq] at key
  rw [key]
  simp

theorem main : ∀ (n : ℕ) (z0 : V n) (ξ : Fin n → ℂ), (∀ (m : ℕ) (s : Fin m → V n → ℂ) (k0 : Fin m), (∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) → s k0 z0 ≠ 0 → (∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) → (leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ).re = 0) ∧ ∀ g : V n → ℝ, ContDiffAt ℝ 2 g z0 → IsLocalMax g z0 → (leviV n (fun z => ((g z : ℝ) : ℂ)) z0 ξ).re ≤ 0 := by
  intro n z0 ξ
  refine ⟨fun m s k0 hs h0 hq => ?_, fun g hg hmax => ?_⟩
  · rw [levi_log_sum_eq_zero z0 ξ s k0 hs h0 hq, Complex.zero_re]
  · exact ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hg hmax ξ

end GlobalTheory.LeviFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MarginsOfGaps
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_gaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), 0 < X.p0 → X.p0 < r → Nonempty X.Ψ → Xa.de = de2W X → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → ((b : ℕ) < X.p0 ∨ X.p0 ≤ (a : ℕ)) → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → ∀ bb m mL : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → (∀ τ (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → m ≤ (((Xa.Fp - kapW X - nd X • Xa.L) τ b : ℤ) : ℝ) - (((Xa.Fp - kapW X - nd X • Xa.L) τ a : ℤ) : ℝ) ∧ mL ≤ ((Xa.L τ b : ℤ) : ℝ) - ((Xa.L τ a : ℤ) : ℝ)) → bb + 2 * Xa.T < m → bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m + nd X * mL → 2 * (r : ℝ) < m → Margins X Xa := by
  intro E _ _ _ r X Xa h0 hr _ hde hL hgap bb m mL hbb hpair hm1 hm2 _
  obtain ⟨g1, g2, g3, g4⟩ := GlobalTheory.ThetaRecordCompare.arch_gaps Xa h0 hr
  have hT : (0 : ℝ) ≤ Xa.T := Nat.cast_nonneg _
  have hde2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X Xa.de := by
    rw [hde]
    intro τ i j
    refine ⟨fun h => ?_, fun a b => ?_⟩
    · simp only [de2W]
      split_ifs <;> omega
    · simp only [de2W]
      split_ifs <;> omega
  have hA : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a b => hgap τ i j a (Or.inl b)) (fun τ i j a b => hgap τ i j b (Or.inr a))
      (fun τ i j a b => (hpair τ i j a b).1) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      mL * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.L) z ξ :=
    (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ mL
      (fun τ i j a b => by
        rcases a.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).1 i j h b).le)
      (fun τ i j a b => by
        rcases b.eq_or_lt with h | h
        · rw [h]
        · exact ((hL τ).2.1 i j a h).le)
      (fun τ i j a b => (hpair τ i j a b).2)
  refine ⟨⟨bb, m - 2 * Xa.T, hbb, by linarith, fun t ht x0 ho z hz ξ => ?_⟩,
    ⟨bb, m + nd X * mL, hbb, hm2, fun x0 ho z hz ξ => ?_⟩, fun x0 ho z hz ξ => ?_,
    (GlobalTheory.ThetaRecordCompare.arch_extra Xa).2.2.2.1,
    fun k P => GlobalTheory.ThetaRecordCompare.cusp_of_gaps Xa.n_ge h0 hr
      (GlobalTheory.ThetaRecordCompare.gaps_add g3 (GlobalTheory.ThetaRecordCompare.gapsGe_mono g1 zero_le_one) k)
      (GlobalTheory.ThetaRecordCompare.pair_add g4 g2 k)⟩
  · have a := hA x0 ho z hz ξ
    have hrh := GlobalTheory.ThetaRecordCompare.leviRh_nonneg X ho hz ξ
    rcases ht with rfl | ht
    · have := mul_nonneg hT hrh
      nlinarith
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      have b := Xa.base_psi_levi_lower_bound x0 (IW.orth_mem_dom X x0 ho) z hz ξ
      have c : leviM X (phla X Xa.de) x0 z ξ = 2 * leviRh X x0 z ξ :=
        GlobalTheory.ThetaRecordCompare.levi_twoDelta hde2 ho hz ξ
      have ht : 0 ≤ 1 + Xa.c1 / Xa.a1 := by have := Xa.frame_theta_const_pos; have := Xa.frame_theta_weight_pos; positivity
      have d := mul_le_mul_of_nonneg_left b ht
      have e := mul_le_mul_of_nonneg_right Xa.rr_le hrh
      rw [c] at d
      unfold leviO at *
      nlinarith
  · have a := hA x0 ho z hz ξ
    have b := mul_le_mul_of_nonneg_left (hB x0 ho z hz ξ) (Nat.cast_nonneg (α := ℝ) (nd X))
    nlinarith
  · by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeight
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares.DivOne

open GlobalTheory.Up GlobalTheory.Up.DivUpPf

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWtG (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X G (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

theorem smoothWtG_contDiffOn (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWtG Xa G x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz G).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

theorem smoothWtG_levi (Xa : ArchInM X) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWtG Xa G x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWtG
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

theorem inAt_iffG (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r) (bb t : ℝ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (fun x => open Classical in if x ∈ X.dom then
      ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-t) else 0) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-t) *
        Real.exp (-smoothWtG Xa G x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdom : cpt X x0 z ∈ X.dom := hz
  have hw := sum_normSq_w_pos Xa hdom
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [if_pos hdom, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hsp,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hsp, ← Real.exp_add, ← Real.exp_add,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold smoothWtG
  ring

end

theorem divOne_up : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) → ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X + 1 : ℕ) : ℝ) - 1 / 2)) else 0) bb F → ∃ H : Fin (nd X) → V (nd X) → ℂ, (∀ k, DifferentiableOn ℂ (H k) (OmF X x0) ∧ InAt X x0 (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-(((nd X : ℕ) : ℝ) - 1 / 2)) else 0) bb (H k)) ∧ ∀ z ∈ OmF X x0, F z = ∑ k, Fl.s k (cpt X x0 z) * H k z := by
  intro E _ _ _ r X Xa Fl G x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hgn := HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds)
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0) hgn
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hcast : ((nd X + 1 : ℕ) : ℝ) - 1 / 2 = ((nd X : ℝ) - 1 / 2) + 1 := by
    push_cast; ring
  rw [inAt_iffG Xa Fl G x0 bb _ k0 hnull, hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.step Xa.n_ge hU (s := fun k z => Fl.s k (cpt X x0 z)) k0
    (s_diffOn Fl x0) hgn ⟨S, hS⟩ (smoothWtG_contDiffOn Xa G x0 bb)
    (fun z hz ξ => smoothWtG_levi Xa G x0 bb hz ξ (hm z hz ξ)) (t := (nd X : ℝ) - 1 / 2)
    (by linarith) hF hI
  exact ⟨H, fun k => ⟨(hH k).1, (inAt_iffG Xa Fl G x0 bb _ k0 hnull _).2 (hH k).2⟩, hFH⟩

end GlobalTheory.Shares.DivOne
end

