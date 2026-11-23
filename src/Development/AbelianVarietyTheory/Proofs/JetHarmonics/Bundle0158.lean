module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueConnectionIntegralChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTieSat
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actLev_full_level_group_framedPoints : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  first | exact @GlobalTheory.FullLevelAction.actLev_levFull | exact GlobalTheory.FullLevelAction.actLev_levFull | (intros; apply GlobalTheory.FullLevelAction.actLev_levFull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointData
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem numOf_sizes_le (D : D7) (L : SizeData₂ D) (hk : (1 : ℝ) ≤ D.R.k) (hm : (1 : ℝ) ≤ D.R.m) :
    (numOf D L).Sc + (numOf D L).eta ≤ L.Sc + L.etaSz := by
  have hS := L.Sc_pos
  have hE := L.Sc_eq
  have he := L.etaSz_pos
  have hDel : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have h1 : (numOf D L).Sc ≤ L.Sc := by
    show (D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)) ≤ L.Sc
    rw [hE]
    have := Nat.floor_le hDel
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (numOf D L).eta ≤ L.etaSz := by
    show (D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ) ≤ L.etaSz
    have hm0 : (0 : ℝ) < D.R.m := by linarith
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    have h0 : 0 ≤ LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; positivity
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le h0) hm0.le
  linarith

theorem card_RPl (R : Ranks) : Fintype.card (RPl R) = R.f := by
  simp [RPl, Ranks.f, Ranks.n, R.card_A]


set_option maxHeartbeats 1000000 in
theorem leafGood_run : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.GoodDepth.leafGood 100 (by norm_num)
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm R hPk hC hPg hSz hCn hx5 hx hkb tF
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe Scale.b Scale.L
    rw [R.x_eq, R.eps_eq]
  have hL : O.L = L.sc.L := by
    unfold OnObj.L
    rw [hb, Scale.b, Real.log_exp]
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hk1 : (1 : ℝ) ≤ D.R.k := R.k_eq ▸ hPg.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := R.m_eq ▸ hPg.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := R.f_eq ▸ hPg.2.2.2.1
  have hlog : Real.log D.R.k ≤ L.sc.L := by
    have := hSz.2.2.2.2.2.2.1
    rwa [R.k_eq, hL] at this
  refine hC0 D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι Nm (numOf D L)
    (fun z => DV.tauEmb D (plOf D z)) hC R.E_eq R.σ_eq R.T_eq ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
    (piSplit_depDataOf ..) (levelQ_depDataOf _ _ _ _ _ _ _ _ _ hT) R.star_eq
    (fun j => (_root_.GlobalTheory.IntChartExists.intChart_exists _ _ _ _ _ _).2.1 R.star_eq) hPk (_root_.GlobalTheory.GoodDepth.placeTie_of_pins D L T hT.pins) (fun j => ?_) ?_ hPg tF
    ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
  · have hj := R.inR j
    have hd := hT.pins.2.2.2 _ hj
    refine ⟨hj.1, hj.2, hd.1, hd.2.1, fun τ i i' h => (dom_wtA (lR Tp hK (ι j))).1 τ h, ?_⟩
    rw [hb, hL]
    exact _root_.GlobalTheory.GoodDepth.goodPage_run D L Pm Tp hK T hT.pins hCn hx5 hx hkb hlog _ hj
  · refine ⟨R.k_eq, R.m_eq, R.f_eq, ?_, R.depthNumbers_threshold_eq, R.th_eq, R.ad_eq, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · unfold OnObj.Se
      rw [R.Sc_eq, R.eta_eq]
      exact numOf_sizes_le D L hk1 hm1
    · rw [R.wt_eq]
      have h := (_root_.GlobalTheory.FirstRows.first_rows_and_sizes D L Pm Tp hK (ι j) (R.inR j) hx hkb).2
      calc (∑ z, (numOf D L).w (ι j) z) ≤ ∑ _z : RPl D.R, 2 * L.sc.b := Finset.sum_le_sum fun z _ => (h z).2
        _ = 2 * (D.R.f : ℝ) * L.sc.b := by
          rw [Finset.sum_const, Finset.card_univ, card_RPl, nsmul_eq_mul]; ring
    · rw [R.wt_eq, hb]; nlinarith
    · have h := (_root_.GlobalTheory.WeightExponents.weight_exponents D T.Q hT.pins (ι j) (R.inR j) (lR Tp hK (ι j))).1
      have h2 := R.DF_ge j
      rw [← h] at h2
      exact h2

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem addVal_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (u : F) (m : ℕ) (hm : 0 < m)
    (hu : u ^ m = 1) : v u = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hu
    exact zero_ne_one hu
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, hu, AddValuation.map_one]
  have ht : v u ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  lift v u to ℚ using ht with q hq
  have h3 : m • q = 0 := by exact_mod_cast h1
  rw [nsmul_eq_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h (by exact_mod_cast hm.ne')
  · rw [h]; rfl

theorem addVal_prod_eq_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (s : Finset K) (u : K → F)
    (hu : ∀ i, v (u i) = 0) : v (∏ i ∈ s, u i) = 0 := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, AddValuation.map_mul, hu, ih, add_zero]

theorem boxSer_smul {k : Type} [CommRing k] {n d : ℕ} (u : Fin n → k) (f : Fin n → PS k 1 d) :
    boxSer (fun i => u i • f i) = (∏ i, u i) • boxSer f := by
  simp only [boxSer, map_smul]
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]


set_option maxHeartbeats 1600000 in
theorem harmonicValue_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N = l.M → α * star α = (N : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y C hFT P hTors hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG
    U' PU _ oD' hxe hoD α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  letI := H.starRing
  letI := io.toAlgebra
  subst hN
  obtain rfl : q = l.M := by rw [← e, Nat.one_mul]
  have hodd : Odd l.M := l.odd
  have h1 : 1 ≤ l.M := le_trans (by norm_num) l.three_le

  obtain ⟨τ, hτG, hτEL, hτT⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.15 C.17 C.18
  have hUJ : IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT := _root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C
  have hAG := GlobalTheory.GermBasic.main T.V _ _ _ P.U _ C.xT hUJ τ hτG F l.M

  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1

  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hcol⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ rfl
    yF hyF α l.M hodd hα

  obtain ⟨u₀, p₁, w₁, ζ₁, r₀, r, σ₁, f, hu₀, hhf, hcols⟩ := GlobalTheory.ColumnSplit.main E H Dw l Xo c T io y C hFT P hTors hAlg
    ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD τ hτG hτEL α l.M h1 hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀
    t l.M e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm
  have hall := fun i => hcol (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcols i).1 (hcols i).2.1
    (hcols i).2.2.1 ((Category.assoc _ _ _).trans (hx i)) (hcols i).2.2.2.1 (hcols i).2.2.2.2.1 (hcols i).2.2.2.2.2.1
  choose U B HH S0 hU hB hTP hTie hσ using hall

  have hex : ∀ i, ∃ g, GermA P.U.toUnifPre C.xT τ F l.M (S0 i) g := fun i => hAG.2.2 (hτT hFT) (S0 i)
  choose f' hf' using hex
  have hff : ∀ i, f i = U i • f' i := by
    intro i
    have hlin := hAG.2.1 1 (fun _ => U i) (fun _ => S0 i) (fun _ => f' i) (σ₁ i) (fun _ => hf' i)
      (by intro jj; rw [Fin.sum_univ_one]; exact hσ i jj)
    have := hAG.1 (σ₁ i) _ _ (hcols i).2.2.2.2.2.2 hlin
    rw [Fin.sum_univ_one] at this
    exact this
  have hh2 : h = (u₀ * ∏ i, U i) • boxSer f' := by
    rw [hhf, show f = fun i => U i • f' i from funext hff, boxSer_smul, smul_smul]
  have hv0 : v (u₀ * ∏ i, U i) = 0 := by
    rw [AddValuation.map_mul, hu₀, zero_add]
    refine addVal_prod_eq_zero v Finset.univ U (fun i => ?_)
    obtain ⟨m, hm, hum⟩ := hU i
    exact addVal_eq_zero_of_pow_eq_one v (U i) m hm hum

  have hT := GlobalTheory.harmonic_value_of_tied_sections E H Dw l Xo c nab hnab T io y C P τ hτG hτEL F φ rfl yF hyF l.M n S0
    HH f' hTie hf'
  obtain ⟨xx, Fs, hFs, hA⟩ := GlobalTheory.AlphaForm.alphaForm_at_point E H Dw l Xo c nab hnab F yF α hα hMb n B HH hB hTP
  refine ⟨xx, u₀ * ∏ i, U i, hv0, ?_⟩
  intro a Pp hP fth hth
  have h9918 := GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ rfl yF hyF a n xx Pp hP Fs hFs fth hth
  have key : ∀ (g : PS F n (chD C.ch)) (s : F),
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M (s • g) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) =
      s * nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M g (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) := by
    intro g s
    have := (GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M n (LtN Dw n)
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))).2.1
      (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => s) (fun _ => g)
    simp only [Fin.sum_univ_one] at this
    exact this
  have hT' := hT a Pp hP
  rw [hA a Pp hP] at hT'
  rw [hh2, key, map_mul, h9918]
  exact congrArg (fun z => (u₀ * ∏ i, U i) * z) hT'.symm

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHold
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem pointStatements_on_copies :
    RPointT ∧ GenPointT ∧ JetsOnCopiesCompatibleFrames ∧ GermOfFamT ∧ ThetaFrameF ∧ PowPELF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have ht := GlobalTheory.twistBaseChange_and_valuation_statements.1
  exact ⟨GlobalTheory.SmallTranslate.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.GeneratorsAtPoint.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.PowJets.jets_on_copies h1 h2 h4 ht,
    GlobalTheory.PowGerm.germOfFam_holds h1 h2 h4 ht,
    GlobalTheory.PowThetaFrame.main h1 h2 h4 ht,
    GlobalTheory.PowGerm.powPEL_of_laws h1 h2 h3 h4 h5 ht⟩

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem laws_and_nuFinAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)], LawsM T → (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → LawsPi T (depOf T EX Tp hK) ∧ LawsDep T ∧ NuFinAt T (depOf T EX Tp hK) := by
  intro D L Pm Tp hK T EX _ h hs
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn : 2 * D.R.f * D.R.r ≤ Tp.nWn := by
    refine le_trans ?_ Tp.nW_lo.1
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hP : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun h EX _ _ _ _ _ fun j _ => hn
  have hD : LawsDep T :=
    ⟨hs, fun j _ => (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hs,
      fun j _ => GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hs⟩
  exact ⟨hP, hD, nuFinAt_of T h.pins _ hP.wts hD.chartEx
    fun j _ => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo j) T.Q.c⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRule_integralPoint_value_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io'), letI := io.toAlgebra; letI := io'.toAlgebra; ∀ φ : T.Fr →ₐ[c.F] T'.Fr, FrMap φ y.1 y'.1 → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, φ (evI y f) = evI y' f := by
  first | exact @GlobalTheory.ThetaRuleValue.evI_baseChange | exact GlobalTheory.ThetaRuleValue.evI_baseChange | (intros; apply GlobalTheory.ThetaRuleValue.evI_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveCharts
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthBd

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem nuW_eq_zero (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    (hl : Formalism.L2.Pj.DF Dw a < resCharOf la) : nuW Xo c la k a n = 0 := by
  refine max_eq_left ?_
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  letI := io.toAlgebra
  exact (iInf_le _ C).trans ((crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).2 hl)

theorem nuLocC_le_nuW (hI : ChartIndep Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (z : IntFr Xo c T io) (hz : z.IsAlg) (C : IntegralChartA3 Xo c T io z) :
    nuLocC C e k a n ≤ nuW Xo c la k a n := by
  have h1 : nuLocC C e k a n ≤ nuLoc z e k a n := le_iInf fun C' => (hI T io z C C' e k a n).le
  refine h1.trans (le_trans ?_ (le_max_right _ _))
  unfold nuSup
  exact le_iSup_of_le T (le_iSup_of_le io (le_iSup_of_le e (le_iSup_of_le ho (le_iSup_of_le z
    (le_iSup_of_le hz le_rfl)))))
end Gen

theorem ereal_unit {x : EReal} {r d q : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hq : 0 < q) (h0 : 0 ≤ x)
    (h1 : x ≤ max 0 ((r * d / q : ℝ) : EReal)) :
    x = ((r * (x.toReal / r) : ℝ) : EReal) ∧ 0 ≤ x.toReal / r ∧ x.toReal / r ≤ d / q := by
  have hb : (0 : ℝ) ≤ r * d / q := by positivity
  rw [max_eq_right (by exact_mod_cast hb)] at h1
  have ht : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
  have hb' : x ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  lift x to ℝ using ⟨ht, hb'⟩
  have h0' : 0 ≤ x := by exact_mod_cast h0
  have h1' : x ≤ r * d / q := by exact_mod_cast h1
  rw [EReal.toReal_coe]
  refine ⟨by rw [mul_div_cancel₀ _ hr.ne'], by positivity, ?_⟩
  rw [div_le_iff₀ hr]
  calc x ≤ r * d / q := h1'
    _ = d / q * r := by ring

theorem nuWt_bounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  intro D T h j hj w hn la
  letI := T.Q.H.starRing
  have hst : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun _ => rfl
  obtain ⟨hDF, hdom, -, -, hcard, -⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hE : IntChartEx (T.Q.Xo j) T.Q.c :=
    (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hst
  have hI : ChartIndep (T.Q.Xo j) T.Q.c := GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hst
  have hS : ChartSaturated (T.Q.Xo j) T.Q.c := SaturatedCharts.saturation_charts_holds _ _
  have hn' := hcard.trans hn
  have hr : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.GoodDepth.ramOverZ_ne_zero' la)
  have hq : (0 : ℝ) < (resCharOf la : ℝ) - 1 := by
    have : (1 : ℝ) < resCharOf la := by exact_mod_cast (Crude.resCharOf_prime la).one_lt
    linarith
  have hle := nuW_le_crude hE hS la T.Q.l.M (wtA w) w.n hdom hn'
  rw [hDF] at hle
  obtain ⟨a1, a2, a3⟩ := ereal_unit hr (Nat.cast_nonneg (WeightAlgebra.DF w)) hq (le_max_left _ _) hle
  refine ⟨a1, a2, a3, fun hl => ?_, fun T' io e ho z hz C => ?_⟩
  · unfold nuWt
    rw [nuW_eq_zero hE hS la T.Q.l.M (wtA w) w.n hdom hn' (hDF ▸ hl)]
    simp
  · exact (nuLocC_le_nuW hI la T.Q.l.M (wtA w) w.n T' io e ho z hz C).trans a1.le

end GlobalTheory.DepthBd
end

