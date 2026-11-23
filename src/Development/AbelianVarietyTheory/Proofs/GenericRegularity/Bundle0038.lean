module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftModelHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveSectionStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LocStructStRecord

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftFrShFin
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frameShift_frShFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ h : GenFrEx Xo c, ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, (∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), T0.IsNormDiscrete v → ((∃ la, T0.IsOver (K := c.F) v la) ∨ T0.IsTrivOn c.F v) → ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))), (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧ (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) ∧ ∀ [Fintype (Comp Xo c)] (d : T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA h
  obtain ⟨hM, ⟨Y⟩⟩ := _root_.GlobalTheory.Reg.modelAt_and_nonempty_global_model E H Dw l Xo c hpq hgood hA
  have hEv : EvLaws Xo c := (_root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  have hInt : IntDiagUnit Xo c := (_root_.GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).2.1
  have hTw : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt :=
    GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.T.exists_frame_shift_of_valued_points hTw E H Dw l Xo c hEv hInt hM Y h
  exact ⟨δ, h1, fun d hD => GlobalTheory.Reg.frShFin_of_divFin_of_finset E H Dw l Xo c d δ hD h2⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteDimensionalOfModel
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PrimeData

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem ev_ne_zero_of_nonZeroComp (X : PJ D B P j) {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)]
    [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

theorem ne_zero_of_nval_eq {T T' : CDVR} {e : ℕ} {x : T.Fr} {x' : T'.Fr} (hx : x ≠ 0)
    (h : nval T.V e x = nval T'.V e x') : x' ≠ 0 := by
  rintro rfl
  rw [nval_zero, nval_of_ne hx] at h
  exact EReal.coe_ne_top _ h

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem finiteDimensional_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) :
    FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
  exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv

theorem isReduced_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) : IsReduced (OsK (xplus X E hM) la G.w) := by
  have : IsReduced (↥C.A' ⧸ C.JA) := C.red
  exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective

end General

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


include hT in
theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem fromW_ne_zero {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) (ζ : PtsG G la) :
    ∃ (y : (extAll h j hj).Pt' la) (hw : FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ y),
      ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
        hw.ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 := by
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, hnz⟩ := hR ζ
  obtain ⟨hw⟩ := @fromW_of D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)
    ka wL wF G la ζ (‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ) y hU Tc ι hl hunr ev hu hv hdeg
  exact ⟨y, hw, fun w F hF => ne_zero_of_nval_eq (hnz w F hF) ((hv w F).symm.trans (hw.hv w F))⟩

end Inst

end GlobalTheory.PrimeData
end
end

