module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareSizeBoundsAlongFamily
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.ShareNumbers

theorem real_bounds (PP TO Dp k f m r nW : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hk : 1 ≤ k) (hD : 1 ≤ Dp) (hr : 1 ≤ r)
    (hPP : (2 * f * m) ^ 4 * nW ≤ PP) (hn40 : 40 ≤ nW) (hnk : k ≤ nW) (hnr : f * r ^ 2 ≤ nW)
    (hTO : PP ^ 4 * Dp ^ 3 * k * f / m ≤ TO) :
    54 * f * r ^ 4 ≤ TO ∧ 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ TO := by
  have hm0 : 0 < m := by linarith
  have hc : 16 ≤ (2 * f * m) ^ 4 := by
    have : 2 ≤ 2 * f * m := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
  have hfm : f * m ≤ (2 * f * m) ^ 4 := by
    have h1 : 1 ≤ 2 * f * m := by nlinarith
    calc f * m ≤ 2 * f * m := by nlinarith
      _ = (2 * f * m) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)
  have hn0 : 0 ≤ nW := by linarith
  have hP640 : 640 ≤ PP := by nlinarith
  have hPm : m * nW ≤ PP := by nlinarith
  have hPfk : f * k ≤ PP := by nlinarith
  have hPfr : f * r ^ 2 ≤ PP := by nlinarith
  have hP0 : 0 ≤ PP := by linarith

  have h4 : PP ^ 3 ≤ PP ^ 4 / m := by
    rw [le_div_iff₀ hm0]
    have : m ≤ PP := by nlinarith
    calc PP ^ 3 * m ≤ PP ^ 3 * PP := by gcongr
      _ = PP ^ 4 := by ring
  have hDkf : 1 ≤ Dp ^ 3 * k * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hk) hf
  have hT : PP ^ 3 * (Dp ^ 3 * k * f) ≤ TO := by
    calc PP ^ 3 * (Dp ^ 3 * k * f) ≤ PP ^ 4 / m * (Dp ^ 3 * k * f) := by gcongr
      _ = PP ^ 4 * Dp ^ 3 * k * f / m := by ring
      _ ≤ TO := hTO
  have hP3 : 0 ≤ PP ^ 3 := by positivity
  constructor
  · have e1 : 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP ^ 3 := by
      have a : 54 * (f * r ^ 2) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * r ^ 2 := by positivity
      calc 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 54 * f * r ^ 4 ≤ 54 * (f * r ^ 2) * (f * r ^ 2) := by
      have : 0 ≤ r ^ 4 := by positivity
      have hff : f ≤ f * f := by nlinarith
      calc 54 * f * r ^ 4 = 54 * r ^ 4 * f := by ring
        _ ≤ 54 * r ^ 4 * (f * f) := by gcongr
        _ = _ := by ring
    calc 54 * f * r ^ 4 ≤ PP ^ 3 := e2.trans e1
      _ = PP ^ 3 * 1 := (mul_one _).symm
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT
  · have e1 : 28 * (f * k) * (f * k) ≤ PP ^ 3 := by
      have a : 28 * (f * k) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * k := by positivity
      calc 28 * (f * k) * (f * k) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by
      have hfk : 0 ≤ (f * k) ^ 3 := by positivity
      have hD2 : Dp * (Dp + 6) ≤ 7 * Dp ^ 3 := by
        have h1 : Dp ≤ Dp ^ 2 := by nlinarith
        have h2 : Dp ^ 2 ≤ Dp ^ 3 := by nlinarith
        nlinarith
      calc 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 4 * (f * k) ^ 3 * (7 * Dp ^ 3) := by gcongr
        _ = 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by ring
    calc _ ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := e2
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT


open Formalism.BasicNotions in
theorem params_bounds {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (p0 : ℕ) (hp : p0 ≤ D.R.r) :
    2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T.TO ∧
      (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / (T.TO : ℝ) ≤
        1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)) := by
  have hf2 : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hDp : T.Dp = D.R.f * (D.R.r * (D.R.r - 1) / 2) := by rw [T.Dp_eq, Nat.choose_two_right]
  have hD1 : 1 ≤ T.Dp := by
    rw [T.Dp_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hnk : D.R.k ≤ T.nWn := by
    have h := T.nW_lo.2.1
    have h' : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnr : D.R.f * D.R.r ^ 2 ≤ T.nWn := by
    have h := T.nW_lo.1
    have h' : D.R.f * D.R.r * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    calc D.R.f * D.R.r ^ 2 = D.R.f * D.R.r * D.R.r := by ring
      _ ≤ _ := h'.trans h
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast hm1
  have hTO : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
    have hn : 0 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f := by
      have : 0 ≤ T.PP ^ 4 := by positivity
      positivity
    have hd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    have hdm : (D.R.m : ℝ) * L.de2 ≤ D.R.m := mul_le_of_le_one_right hm0.le L.thickDensity_le_one
    calc T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m
        ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / ((D.R.m : ℝ) * L.de2) := div_le_div_of_nonneg_left hn hd hdm
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hn hx1) hd.le
  obtain ⟨A, B⟩ := real_bounds T.PP T.TO T.Dp D.R.k D.R.f D.R.m D.R.r T.nWn (by exact_mod_cast hm1)
    (by exact_mod_cast (show 1 ≤ D.R.f by omega)) (by exact_mod_cast hk1) (by exact_mod_cast hD1)
    (by exact_mod_cast (show 1 ≤ D.R.r by omega)) T.PP_nW (by exact_mod_cast T.nW_40) (by exact_mod_cast hnk)
    (by exact_mod_cast hnr) hTO
  constructor
  · have hA : 54 * (D.R.f * D.R.r ^ 4) ≤ T.TO := by
      have : ((54 * (D.R.f * D.R.r ^ 4) : ℕ) : ℝ) ≤ T.TO := by push_cast; linarith
      exact_mod_cast this
    have h1 : p0 * (D.R.r - p0) ≤ D.R.r * D.R.r := Nat.mul_le_mul hp (Nat.sub_le _ _)
    have h2 : 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * (D.R.f * D.R.r ^ 4) := by
      calc 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r)) := by gcongr
        _ = 50 * (D.R.f * D.R.r ^ 4) := by ring
    have h3 : D.R.r ≤ D.R.r ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : 1 ≤ D.R.r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h5 : D.R.r ^ 4 ≤ D.R.f * D.R.r ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [← hDp]
    have hT0 : (0 : ℝ) < T.TO := by
      have : 1 ≤ T.TO := le_trans (by omega) T.TO_40
      exact_mod_cast this
    have hq : (0 : ℝ) < 4 * ((D.R.f : ℝ) * D.R.k) ^ 3 := by
      have : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
      have : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
      positivity
    rw [div_le_div_iff₀ hT0 hq]
    linarith

end GlobalTheory.ShareNumbers


open GlobalTheory.ShareNumbers in
theorem GlobalTheory.ShareNumbers.numbers_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι p0 hp => params_bounds (Fm.parT x hx ι) p0 hp⟩⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortRuleChangeMat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := _root_.GlobalTheory.harmonicValue_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := _root_.GlobalTheory.changeRoot_of_chartIndep hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne



attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
section
open Matrix

noncomputable section
namespace GlobalTheory.SvNAnyChar

def scaleSnd {k : Type} [Field k] {κ : Type} (c : k) :
    (κ → k) × (κ → k) →+ (κ → k) × (κ → k) where
  toFun w := (w.1, c • w.2)
  map_zero' := by simp
  map_add' a b := by simp

@[simp] theorem scaleSnd_fst {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).1 = w.1 := rfl

@[simp] theorem scaleSnd_snd {k : Type} [Field k] {κ : Type} (c : k) (w : (κ → k) × (κ → k)) :
    (scaleSnd c w).2 = c • w.2 := rfl

theorem schr_mulShift_scaleSnd {k : Type} [Field k] [Invertible (2 : k)] {κ : Type} [Fintype κ]
    (ψ : AddChar k ℂ) {c : k} (hc : c ≠ 0) (w : (κ → k) × (κ → k)) (φ : (κ → k) → ℂ) :
    GlobalTheory.WeilM.schr (ψ.mulShift c) (scaleSnd c⁻¹ w) φ = GlobalTheory.WeilM.schr ψ w φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, scaleSnd_fst, scaleSnd_snd, AddChar.mulShift_apply, dotProduct_smul,
    smul_eq_mul]
  congr 2
  rw [mul_add, mul_left_comm c (⅟2), mul_inv_cancel_left₀ hc, mul_inv_cancel_left₀ hc]

theorem stoneVonNeumann_any_char :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc, hcond⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  have hψ1 : Continuous (ψ0.mulShift c) := by
    have : (ψ0.mulShift c : k → ℂ) = fun x => ψ0 (c * x) := by
      funext x
      exact AddChar.mulShift_apply
    rw [this]
    exact hψ.comp (continuous_const.mul continuous_id)
  let S : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k :=
    { toFun := fun z => c • z
      map_zero' := smul_zero c
      map_add' := smul_add c }
  have hS : ∀ z, S z = c • z := fun _ => rfl
  have hsum : ∀ (a : k) (Y z : Matrix (Fin n) (Fin d) k),
      ∑ i, ∑ j, Y i j * (a • z) i j = a * ∑ i, ∑ j, Y i j * z i j := by
    intro a Y z
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨ι, hbij, h1, h2⟩ := _root_.GlobalTheory.StoneVN.intertwiner_matrix (κ := κ) (n := n) (d := d) (ψ0.mulShift c) hψ1
    (fun x => by simpa only [AddChar.mulShift_apply] using hcond x)
    ((scaleSnd c⁻¹).comp wT) ((scaleSnd c⁻¹).comp (wM.comp S))
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hT, mul_zero])
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hM, mul_zero])
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply, scaleSnd_fst, scaleSnd_snd, dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, hTM, hS, hsum, inv_mul_cancel_left₀ hc])
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (scaleSnd c w)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      simp only [AddMonoidHom.comp_apply]
      rw [hS, smul_inv_smul₀ hc, ← map_add (f := _), h]
      exact Prod.ext rfl (inv_smul_smul₀ hc _))
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · have := h1 Y φ hφ
    rwa [AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc] at this
  · have := h2 (c⁻¹ • z) φ hφ
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, schr_mulShift_scaleSnd ψ0 hc, hS,
      smul_inv_smul₀ hc] at this
    rw [this]
    funext Y'
    rw [AddChar.mulShift_apply, hsum, mul_inv_cancel_left₀ hc]

end GlobalTheory.SvNAnyChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  first | exact @GlobalTheory.TwistedKernelChar.twisted_kernel_char | exact GlobalTheory.TwistedKernelChar.twisted_kernel_char | (intros; apply GlobalTheory.TwistedKernelChar.twisted_kernel_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharFiniteIdeleEqHeckeCharValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotPointDict

theorem chr_at_finIdl : ∀ {D : D7} (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    ∀ x y, IsFinIdl x y → ((c x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) :=
  fun c χ h x y hxy => GlobalTheory.FinIdlRead.chr_finIdl c χ h x y hxy

end GlobalTheory.BotPointDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElementStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_for_weyl_element : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  first | exact @GlobalTheory.WeylFour.weyl_hasOp | exact GlobalTheory.WeylFour.weyl_hasOp | (intros; apply GlobalTheory.WeylFour.weyl_hasOp <;> assumption)
end

