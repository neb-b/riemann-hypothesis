module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowData


set_option maxHeartbeats 1000000 in
theorem exists_powData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ
  obtain ⟨hL, hL2, -, hL4, -⟩ := firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  refine ⟨?_, fun n => ?_⟩
  · choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨t', P', pG, pD, pA, ⟨PU⟩, -⟩ := PelUnifPowerDvr.main hL hT T.V E H C.I.G P n
  obtain ⟨M, oD, hx, hact⟩ := powOAct_of_globalFns hL.globalFns E H T.V C.I.G P n P'.D pD
  refine ⟨P'.D, P'.A, t'.G, inferInstance, inferInstance, pD, pA, pG, P'.U, PU, M, oD, hx, hact, ?_⟩
  intro F _ _ _ _ _ _ v hv Q hQ α N hN hα
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ P'.D (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D P'.D pD Q hQ) F v hv
  letI := M
  have hw : TraceFormTwistIso P'.D.toPre oD H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre P'.D.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V P'.D F (𝓞 E) oD H.w0 hw α N 1 hN le_rfl hα
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaLift

theorem exists_theta_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L ((0 : ℕ) : ℤ) T, θ.pt = x := by
  refine ⟨⟨x, ⟨fun _ => 1⟩, ?_⟩, rfl⟩
  refine isGen_of_gm (M := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A x).left])
    (ε := ![((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)]) _ fun w j j' h h' => ?_
  refine (map_one _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_one _)).symm)
  simp [trF, Fin.prod_univ_two]

theorem exists_theta_of_field : ∀ (K : Type) [Field K] (A : PolAV (Sp K)) (Y : Over (Sp K)) (F : Type) [Field F] (e : Y.left ≅ Sp F) (k : ℕ) (x : Y ⟶ A.A), x ^ k = 1 → ∃ θ : ThetaGrp A.A A.L (k : ℤ) Y, θ.pt = x := by
  intro K _ A Y F _ e k x hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact exists_theta_zero A.L x
  · have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    have : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
    have : Subsingleton Y.left := e.hom.homeomorph.toEquiv.subsingleton
    have : Nonempty Y.left := e.hom.homeomorph.toEquiv.nonempty
    exact GlobalTheory.BoxTheta.exists_theta GlobalTheory.firstFiveLaws.1.kerPow A hk x hx

end GlobalTheory.ThetaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

namespace TransPullEx

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem exists_isNormPull (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen)
    {T : Over S} (s : LB.Sec (LPow A L.L b T)) : ∃ s', IsNormPull A L φ a b s s' := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨s', hs', -⟩ := existsUnique_isTwistPull S A L.L hL T (endOver A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α hα s
  refine ⟨s', α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ, hs'⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end TransPullEx

theorem exists_isTransPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  intro E _ _ _ H Dw l Xo c F _ _ xF α N hN hα s b hb
  letI := H.starRing
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have := Xo.univ.t.act.hom α
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 α N hα (Xo.univ.t.adj α)
    Xo.univ.t.prim 1
  rw [Nat.one_mul] at h
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act α).left] ![(N : ℤ), -1] rfl
  obtain ⟨h₁, hh₁⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act α) (N : ℤ) 1 β hβ s
  obtain ⟨⟨U, hU⟩, -⟩ := symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) N hN
    (UnivPol.isUnit_natCast Xo _ hN.pos) (N : ℤ) rfl (ptO Xo xF) b hb
  obtain ⟨hh, hhh, -⟩ := existsUnique_isTwistPull Xo.X Xo.univ.t.G Xo.univ.t.PP.L hL (ptO Xo xF)
    (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _) (N : ℤ) (N : ℤ) U.φ U.isGen h₁
  exact ⟨hh, h₁, hh₁, hb, U, hU, hhh⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnity
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem exists_rootOfUnity_smul_of_pow_eq_one {F N : Type} [Field F] [AddCommGroup N] [Module F N]
    (Φ : Module.End F N) (ζ ξ : F) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (h : (ζ • Φ) ^ M = 1) (h' : (ξ • Φ) ^ M' = 1) :
    ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ξ • Φ = u • (ζ • Φ) := by
  rcases subsingleton_or_nontrivial (Module.End F N) with hs | hn
  · exact ⟨1, ⟨1, Nat.one_pos, one_pow _⟩, Subsingleton.elim _ _⟩
  have hζ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_pow (by omega)] at h
    exact zero_ne_one h
  have e : ξ • Φ = (ξ / ζ) • (ζ • Φ) := by rw [smul_smul, div_mul_cancel₀ _ hζ]
  refine ⟨ξ / ζ, ⟨M * M', by positivity, ?_⟩, e⟩
  have a : (ξ • Φ) ^ (M * M') = 1 := by rw [mul_comm M M', pow_mul, h', one_pow]
  rw [e, smul_pow, pow_mul (ζ • Φ), h, one_pow] at a
  have b : ((ξ / ζ) ^ (M * M') - 1) • (1 : Module.End F N) = 0 := by rw [sub_smul, a, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 b).resolve_right one_ne_zero)

theorem finOrd_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ ζ' : F), w.IsGen → w'.IsGen → FinOrd D F k p w ζ → FinOrd D F k p w' ζ' → ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ∀ s t₀ t t₀' t' : Fam D.toPre F k, PhiRel D.toPre F k p w s t₀ → Fam.IsSmul D.toPre F ζ t₀ t → PhiRel D.toPre F k p w' s t₀' → Fam.IsSmul D.toPre F ζ' t₀' t' → Fam.IsSmul D.toPre F u t t' := by
  intro V _ _ _ _ ϖ _ D F _ _ k hk p w w' ζ ζ' hw hw' h h'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D F k hk p w' hw'
  obtain ⟨c, hc⟩ := ThetaFinOrd.exists_scalar hG p w' w hw' hw Φ' Φ
    (fun s => (hΦ' _ _).2 rfl) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 h
  obtain ⟨M', hM', hW⟩ := (ThetaFinOrd.finOrd_iff p w' ζ' Φ' hΦ').1 h'
  rw [hc, smul_smul] at hW
  obtain ⟨u, hu, e⟩ := exists_rootOfUnity_smul_of_pow_eq_one (F := F) (N := Fam D.toPre F k) Φ ζ (ζ' * c)
    hM hM' hU hW
  refine ⟨u, hu, fun s t₀ t t₀' t' a b a' b' => ?_⟩
  rw [hΦ] at a
  rw [hΦ'] at a'
  rw [DVR.isSmul_iff] at b b' ⊢
  have f := LinearMap.congr_fun e s
  simp only [LinearMap.smul_apply] at f
  rw [b', a', b, a, hc, LinearMap.smul_apply, smul_smul, f]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.FiniteOrderConst

open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

theorem isHolTo_of_eqOn {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (e : ∀ b ∈ B, y' b = y b) : IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => and_congr_right fun hb => by rw [e b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [e b hb.1]⟩

theorem valAt'_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : Γ(X, ⊤)) : valAt' y ⊤ f = fnAt y f := by
  rw [valAt', dite_eq_left (show (⊤ : (Sp ℂ).Opens) ≤ y ⁻¹ᵁ ⊤ from le_rfl), valAt, fnAt]
  have : y.appLE ⊤ ⊤ le_rfl = y.appTop := Scheme.Hom.appLE_eq_app y
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (q.hom f)) this

theorem fnAt_eq_of_pow {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {a : V → (Sp ℂ ⟶ X)} (hB : IsPreconnected B) (h : IsHolTo B a) (f : Γ(X, ⊤)) {N : ℕ} (hN : 0 < N)
    (hp : ∀ b ∈ B, fnAt (a b) f ^ N = 1) {b b' : V} (hb : b ∈ B) (hb' : b' ∈ B) : fnAt (a b) f = fnAt (a b') f := by
  have hc : ContinuousOn (fun b => fnAt (a b) f) B := by
    have := (h ⊤ f).2.continuousOn
    simp only [valAt'_top] at this
    exact this.mono fun b hb => ⟨hb, le_rfl⟩
  have hfin : {z : ℂ | z ^ N = 1}.Finite :=
    (Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simpa [Polynomial.mem_nthRoots hN] using hz
  exact hB.constant_of_mapsTo hfin.isDiscrete hc hp hb hb'

theorem const_on_period_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  classical
  rintro E _ _ _ H Dw l Xo c σ f hf hfree ⟨N, hN, hp⟩ g ty F hty i P P' y y' hP hP' hy hy'
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.FrameFreeRule.exists_fn E H Dw l Xo c f hf hfree
  obtain ⟨m, B, Q, -, hB, hconv, h0, hQ0, hQ, hall⟩ := GlobalTheory.PeriodChart.period_chart E H (F.Di i) g ty
    (by rw [(F.sig i).1, (F.sig i).2]; exact hty) P hP
  obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := hall P' hP'
  have hbP : F.u i (Q b) = F.u i P' :=
    (F.fibre i (Q b) P' (hQ.1 b hb) hP').2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, hh⟩
  have hex : ∀ t, ∃ z : FrPt Xo c ℂ, t ∈ B → z.x = F.u i (Q t) := fun t => by
    by_cases ht : t ∈ B
    · have hx := F.over_σ i _ (hQ.1 t ht)
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist (F.u i (Q t))
      exact ⟨⟨F.u i (Q t), hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, fun _ => rfl⟩
    · exact ⟨y, fun h => absurd h ht⟩
  choose z hz using hex
  have hhol : IsHolTo B fun t => basePt (z t) :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (isHolTo_of_eqOn (F.hol i m B Q hB hQ).1 fun t ht => (pullback.lift_fst _ _ _).trans (hz t ht))
      (isHolTo_of_eqOn (GlobalTheory.HolFibre.isHolTo_const hB (spMap σ)) fun t _ => pullback.lift_snd _ _ _)
  have key := fnAt_eq_of_pow hconv.isPreconnected hhol f₀ hN
    (fun t _ => by rw [← hf₀ ℂ (z t)]; exact hp (z t)) h0 hb
  rw [← hf₀ ℂ, ← hf₀ ℂ] at key
  exact (hfree ℂ (z 0) y (hy.trans (by rw [hz 0 h0, hQ0]))).trans
    (key.trans (hfree ℂ y' (z b) ((hz b hb).trans (hbP.trans hy'.symm))))

end GlobalTheory.FiniteOrderConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyTateIsometryIntegralFramedPointChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.IntegralTate

theorem nonempty_tateIso_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : Type} [Field k]
    (x : Sp k ⟶ S')
    (I : TateIso D k (Over.mk (x ≫ f) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => WeilIs t.G t.PP.L n g g' (unitOn c))) :
    Nonempty (TateIso D k (Over.mk x ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
      (fun n g g' c => WeilIs t'.G t'.PP.L n g g' (unitOn c))) := by
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I⟩
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc

theorem nonempty_tateIso_of_intChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], Nonempty (TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P F _ _ _ _ _ _
  letI := io.toAlgebra
  obtain ⟨β, hβ⟩ := GlobalTheory.LevelFibre.exists_spMap ((jFK (R := T.V) F ≫ y.1.x) ≫ Xo.s)
  obtain ⟨-, I₀, -⟩ := Xo.univ.geom F (jFK (R := T.V) F ≫ y.1.x) β hβ
  obtain ⟨I₁⟩ := nonempty_tateIso_pull C.I.m1 (jFK (R := T.V) F) I₀
  obtain ⟨I₂, -⟩ := GlobalTheory.LevelFibre.exists_tate_push_comm C.I.m2 (jFK (R := T.V) F) _ rfl
    (ObjPull.pushEquiv C.I.m2.cart (Over.mk (jFK (R := T.V) F))) (fun _ => rfl) I₁
  obtain ⟨I₃, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.tateTransport_holds GlobalTheory.firstFiveLaws.1.weil E H T.V _ C.I.G P F Dw I₂
  exact ⟨I₃⟩

end GlobalTheory.IntegralTate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters
section
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)))
  · intro τ
    constructor
    · intro hτ
      have hex : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
        obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
        by_cases hgP : g ∈ D.R.Psi
        · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
          exact ⟨t, hg.symm.trans ht⟩
        · exfalso
          have h2 : g * D.R.cc ∈ D.R.Psi := by
            by_contra h
            exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
          obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
          have h3 : DV.tauEmb D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hh.2.2.2 t
          rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
          have h4 : τ (D.host.conj (T.Q.H.rt : D.host.E)) = star (τ (T.Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
          have hτ' : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
          have hc : (starRingEnd ℂ) T.Q.H.rt0 ≠ T.Q.H.rt0 := by
            intro he
            obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 he
            have hs := T.Q.H.sqrt_neg_disc_sq
            rw [hx] at hs
            have hs' : x ^ 2 = -(T.Q.H.d : ℝ) := by exact_mod_cast hs
            have hd : (0 : ℝ) < T.Q.H.d := by exact_mod_cast T.Q.H.d_prime.pos
            nlinarith [sq_nonneg x]
          apply hc
          calc star T.Q.H.rt0 = star (τ (T.Q.H.rt : D.host.E)) := by rw [hτ']
            _ = τ (D.host.conj (T.Q.H.rt : D.host.E)) := h4.symm
            _ = T.Q.H.rt0 := h3
      obtain ⟨t, ht⟩ := hex
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth
end

