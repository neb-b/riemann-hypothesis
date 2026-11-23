module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frMap_along {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) : ∃ z : FrPt Xo c T, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r} {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}

theorem abs_fn_frBor_good (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') (i : Ix Dw) :
    |fn σ y' i| = cabs (t i : CAt σ) * |fn σ y i| := by
  obtain ⟨k, x, s, hx, hs⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hσ (hU σ hσ)).2 y
  have hc := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x) y y').2.2.1 s t hs hb
  rw [hp.1 σ hσ k x hx _ _ hc i, hp.1 σ hσ k x hx _ _ hs i, ← mul_assoc]
  congr 1
  exact norm_mul (show ℂ from (t i : CAt σ)) (show ℂ from (s i : CAt σ))

theorem abs_fn_frBor (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {σ : c.F →+* ℂ} {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') (i : Ix Dw) :
    |fn σ y' i| = cabs (t i : CAt σ) * |fn σ y i| := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact abs_fn_frBor_good hU hp hσ hb i
  · have hg : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    obtain ⟨z, hz⟩ := exists_frMap_along (conjAlg σ) y
    obtain ⟨z', hz'⟩ := exists_frMap_along (conjAlg σ) y'
    have hb' := frBorBC _ _ (conjAlg σ) t y y' z z' hb hz hz'
    have e := abs_fn_frBor_good hU hp hg hb' i
    rw [hp.2 σ y z hz i, hp.2 σ y' z' hz' i] at e
    rw [e]
    congr 1
    exact Complex.norm_conj (show ℂ from (t i : CAt σ))

def algOver {Z : Comp Xo c} (sg : c.F →+* ℂ) (P : Om Z →+* ℂ) (hP : sgOf P = sg) : Om Z →ₐ[c.F] CAt sg :=
  { P with commutes' := fun a => RingHom.congr_fun hP a }

theorem abs_fn_generic (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ))
    (hp : FnPin U xR fn) {Z : Comp Xo c} {z g : FrPt Xo c (Om Z)} {t : Ix Dw → (Om Z)ˣ} (hb : FrBor t z g)
    (sg : c.F →+* ℂ) (P : Om Z →+* ℂ) (hP : sgOf P = sg) {w : FrPt Xo c (CAt sg)}
    (hw : FrMap (algOver sg P hP) z w) {y : FrPt Xo c (CAt (sgOf P))} (hy : FrMap (PAlg P) g y) (i : Ix Dw) :
    |fn _ y i| = ‖P (t i : Om Z)‖ * |fn sg w i| := by
  subst hP
  have hb' := frBorBC _ _ (PAlg P) t z g w y hb hw hy
  exact abs_fn_frBor hU hp hb' i

end

theorem nrmAlong_of_fnPin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ [Fintype (Comp Xo c)], ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → NrmAlong fn yP ∧ ∀ (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)), STLoc h Dd N uL wR jc → FnTrdeg Xo c Dd → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → NrmContOff h fn yP Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hp _ h yP hyP
  have hne : FnNe Xo c fn := (GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm E H Dw l Xo c r U hU xR fn hx hp).1
  have main : NrmAlong fn yP := by
    intro Z sg G f _ _ X _ W Q hQ hQc
    have ha : Atlas h := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h
    obtain ⟨C, ψ, z, t, hz, hb⟩ := ha (Om Z) (genFr h Z)
    letI : Algebra c.F C.R := C.R.algebra
    haveI := C.sm
    have hsg : ∀ x : W, sgOf (Q x) = sg := fun x => hQ x x.2
    choose w hw using fun x : W => exists_frMap_along (algOver sg (Q x) (hsg x)) z
    have hQ' : ∀ a, Continuous (fun x : W => Q x a) := fun a => continuousOn_iff_continuous_restrict.1 (hQc a)
    have hcont := GlobalTheory.FrameNorm.fn_continuousOn_smooth E H Dw l Xo c r U hU xR fn hx hp sg C.R C.y W Set.univ
      (fun x => (algOver sg (Q x) (hsg x)).comp ψ) w (fun (a : C.R) => (hQ' (ψ a)).continuousOn)
      (fun x _ => frMap_trans _ _ _ ψ _ C.y z (w x) hz (hw x))
    have hfn : ∀ i, Continuous (fun x : W => |fn _ (yP Z (Q x)) i|) := by
      intro i
      have e : (fun x : W => |fn _ (yP Z (Q x)) i|) = fun x : W => ‖Q x (t i : Om Z)‖ * |fn sg (w x) i| :=
        funext fun x => abs_fn_generic hU hp hb sg (Q x) (hsg x) (hw x) (hyP Z (Q x)) i
      rw [e]
      exact (hQ' _).norm.mul (continuousOn_univ.1 (hcont i))
    rw [continuousOn_iff_continuous_restrict]
    show Continuous (fun x : W => ‖Q x (f.coeff G)‖ * ∏ i, |fn _ (yP Z (Q x)) i| ^ (-exZ Dw G i))
    refine (hQ' _).norm.mul (continuous_finsetProd _ fun i _ => ?_)
    exact (hfn i).zpow₀ _ fun x => Or.inl (abs_ne_zero.2 (hne _ _ _))
  exact ⟨main, fun Dd N uL wR jc hst htr hw =>
    nrmContOff_of h fn yP Dd N uL wR jc hst main hne htr (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 hw⟩

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.SupGeneric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem evR_of_frMap (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c g z = φ (evR Xo c g y) := by
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [evR_eq_map_of_test_point hL hg q χ y₀ y hy₀,
    evR_eq_map_of_test_point hL hg q (φ.comp χ) y₀ z (PullbackSections.frMap_trans χ φ hy₀ hyz)]
  rfl

theorem isFractionRing_chart {h : GenFrEx Xo c} (C : FChart h) : IsFractionRing C.R (Om C.Z) := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := C.frac x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
    change x = a / b
    rw [eq_div_iff hb0, e]⟩

section Pin

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r}
  (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ} (hx : 0 < xR) (hfn : FnPin U xR fn)
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}

include hU hx hfn

end Pin

end GlobalTheory.SupGeneric
end
end

