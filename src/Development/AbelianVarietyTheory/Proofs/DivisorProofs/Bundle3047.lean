module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePeriodQuasiLogarithmPDivGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodFrobeniusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodIntegral
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) (F : BFrame ε) {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B} (hL : IsLift F.θ μ')
  (hμ : ∀ i, map F.θ (μ' i) = c.μ i)
include hv hε hL hμ

theorem hasPeriod_add_smul (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y y' : F.B} (b : F.B)
    (hg : DIn (⊤ : Ideal F.B) g) (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t g y') :
    c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') := by
  first
  | exact (_root_.GlobalTheory.QLog.hasPeriod_linear p C v O hv ε hε F G d c μ' hL hμ f g t y y' b hg h1 h2).1
  | exact (_root_.GlobalTheory.QLog.hasPeriod_linear p C v O hv ε hε F G d c μ' hL hμ f g t y y' b h1 h2).1

theorem hasPeriod_map_zero (t : G.Tate) (s : MvPowerSeries (Fin d) F.B) (hs : constantCoeff s = 0) :
    c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0 := by
  have hz := hasPeriod_zero c F.frame t
  have hd : DIn (⊤ : Ideal F.B) (0 : MvPowerSeries (Fin d) F.Q) := din_of_in (in_zero ⊤)
  first
  | exact (_root_.GlobalTheory.QLog.hasPeriod_linear p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hd hz hz).2 s hs
  | exact (_root_.GlobalTheory.QLog.hasPeriod_linear p C v O hv ε hε F G d c μ' hL hμ 0 0 t 0 0 0 hz hz).2 s hs

theorem hasPeriod_comb (t : G.Tate) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q)
    (hd : ∀ i, DIn (⊤ : Ideal F.B) (e i)) (y : ι → F.B) (hy : ∀ i, c.HasPeriod F.θ t (e i) (y i))
    (b : ι → F.B) : c.HasPeriod F.θ t (comb b e) (∑ i, b i * y i) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using hasPeriod_zero c F.frame t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a * y a)]
    exact hasPeriod_add_smul hv hε F c hL hμ t (b a) (hd a) ih (hy a)

theorem hasPeriod_integral (t : G.Tate) {D : MvPowerSeries (Fin d) F.Q}
    (hD : In (⊤ : Ideal F.B) D) (h0 : constantCoeff D = 0) : c.HasPeriod F.θ t D 0 := by
  obtain ⟨s, rfl⟩ := (in_top_iff D).1 hD
  have hs : constantCoeff s = 0 := by
    apply F.frame.inj
    rw [← constantCoeff_map, h0, map_zero]
  exact hasPeriod_map_zero hv hε F c hL hμ t s hs

theorem hasPeriod_unique (t : G.Tate) {f : MvPowerSeries (Fin d) F.Q} {y y' : F.B}
    (h1 : c.HasPeriod F.θ t f y) (h2 : c.HasPeriod F.θ t f y') : y = y' :=
  h1.unique F.frame h2

theorem hasPeriod_of_in (t : G.Tate) {f g : MvPowerSeries (Fin d) F.Q} {y : F.B}
    (hf : c.HasPeriod F.θ t f y) (hfg : In (⊤ : Ideal F.B) (f - g))
    (h0 : constantCoeff (f - g) = 0) : c.HasPeriod F.θ t g y := by
  have h := hasPeriod_add_smul hv hε F c hL hμ t (-1) (din_of_in hfg) hf
    (hasPeriod_integral hv hε F c hL hμ t hfg h0)
  rwa [map_neg, map_one, neg_one_smul, mul_zero, add_zero, neg_sub, add_sub_cancel] at h

end Frame

theorem window_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, PDivLat.IsConn G → PDivLat.IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hGd F
  obtain ⟨d, ⟨c⟩⟩ := _root_.GlobalTheory.ChartEx.chart_exists p C v O hv G hG
  have hdk := _root_.GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie p C v O hv G d c
  have hCf := _root_.GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  obtain ⟨k, e0, lb, hB0, hA0, hcob0, hLie0⟩ := _root_.GlobalTheory.QLogBasis.adapted_basis p C v O hv G d c C hCf
  obtain ⟨μ', hL, hμ⟩ := _root_.GlobalTheory.LiftLaw.exists_isLift F.B O F.θ F.frame.surj d c.μ c.isLaw
  obtain ⟨Θ, hΘ⟩ := frame_fraction_map p F.B O F.Q F.θ F.frame C hCf
  obtain ⟨e, he0, hB, hA⟩ := _root_.GlobalTheory.QLog.LiftBasis.exists_lift_isAdapted p C v O hv ε hε F G d c μ' hL hμ Θ hΘ k e0 hB0 hA0
  obtain ⟨U, hU⟩ := _root_.GlobalTheory.QLog.exists_frob_matrix p C v O hv ε hε F G d c μ' hL hμ k e hB hA
  have hUu := _root_.GlobalTheory.FrobUnit.frob_matrix_isUnit p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU
  have hN1 := _root_.GlobalTheory.QLog.isNil_frobenius_chart p C v O hv ε hε F G d c μ' hL hμ k e hB hA U fun i => (hU i).1
  have hN2 := _root_.GlobalTheory.DualFrobNil.isNil_dual_frobenius p C v O hv ε hε F G d c μ' hL hμ k e hB hA hGd U hUu hU
  haveI := integers_isIntegrallyClosedIn hv
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate :=
    Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  obtain ⟨χ, hχ, -⟩ :=
    GlobalTheory.DieudonneSandwich.exists_dual_basis hε (G.pairing_flip_bijective C) tb.equivFun
  have hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0 := by
    intro m m'
    have h1 := epsPairing_smul hε G (tb m) (χ m')
    rw [hχ m' (tb m)] at h1
    have h2 : epsPairing hε G (tb m) (χ m') = tb.equivFun (tb m) m' := (epsEquiv hε).injective h1
    rw [h2, Module.Basis.equivFun_self]
    all_goals
      by_cases h : m = m'
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
  have hQLe : ∀ l, QL μ' ⊤ (e l) := hB.1
  have hDe : ∀ l, DIn (⊤ : Ideal F.B) (e l) := fun l =>
    GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hL ⊤ (e l) (hQLe l)
  choose Y hY using fun l m =>
    (_root_.GlobalTheory.PeriodExists.main p C v O hv ε hε F G d c μ' hL hμ (e l) (tb m) (hQLe l)).exists
  choose fχ wχ hfχ using fun m => _root_.GlobalTheory.CharLog.exists_log_char_period p C v O hv ε hε F G d c μ' hL hμ (χ m)
  choose g hg using fun m => (hB.2 (fχ m) (hfχ m).1).exists
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let w : Module.Basis (Fin d) O G.omega :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination O c.form) hbij).symm
  have hw : ∀ i, w i = c.form i := by
    intro i
    simp [w, Module.Basis.ofEquivFun]
  have hcomb0 : ∀ m, constantCoeff (fχ m - comb (g m) e) = 0 := fun m => by
    rw [map_sub, (hfχ m).1.1, (ql_comb hL.const e hQLe (g m)).1, sub_zero]

  have hred : ∀ m, (∀ j, F.θ (g m (Sum.inr j)) = 0) ∧
      ∀ i, lin (map Θ (fχ m)) i = algebraMap O C (F.θ (g m (Sum.inl i))) := fun m => by
    refine _root_.GlobalTheory.QLog.RedO.main p C v O hv G d c k e0 lb hB0 hA0 hLie0 (map Θ (fχ m))
      (ql_map F.θ Θ hΘ hμ hL.const (hfχ m).1)
      (formalGroupLawCoboundaryOne_map_eq_zero F.θ Θ hΘ hμ hL.const (hfχ m).2.1) (fun l => F.θ (g m l)) ?_
    have := in_map_top F.θ Θ hΘ (hg m)
    rwa [map_sub, map_comb F.θ Θ hΘ, show (fun l => map Θ (e l)) = e0 from funext he0] at this

  have hperO : ∀ l m, c.HasPeriod (RingHom.id O) (tb m) (e0 l) (F.θ (Y l m)) := fun l m => by
    have h := _root_.GlobalTheory.QLog.hasPeriod_reduce p C v O hv ε hε F G d c μ' hL hμ C hCf Θ hΘ (e l) (tb m) (Y l m)
      (hQLe l) (hY l m)
    rwa [he0] at h
  refine ⟨d, k, U, Matrix.of Y, Matrix.of g, tb, χ, w, lb, ?_, hUu, ?_, ?_, ?_, ?_, ?_, hN1, hN2,
    hpair, ?_, ?_⟩
  · have := Module.finrank_eq_card_basis lb
    rw [Fintype.card_fin] at this
    omega
  ·
    ext i m
    have key : F.σ (Y i m) = ∑ l, (U * blk d k (p : F.B) 1) l i * Y l m := by
      have hc := hasPeriod_comb hv hε F c hL hμ (tb m) e hDe (fun l => Y l m) (fun l => hY l m)
        (fun l => (U * blk d k (p : F.B) 1) l i)
      have hf := _root_.GlobalTheory.QLog.hasPeriod_frob p C v O hv ε hε F G d c μ' hL hμ (e i) (tb m) (Y i m) (hQLe i)
        (hY i m)
      refine hasPeriod_unique hv hε F c hL hμ (tb m)
        (hasPeriod_of_in hv hε F c hL hμ (tb m) hf (hU i).1 ?_) hc
      rw [map_sub, constantCoeff_frob p F.s (hQLe i).1, (ql_comb hL.const e hQLe _).1, sub_zero]
    rw [Matrix.map_apply, Matrix.of_apply, key, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [blk, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.of_apply]
    ring
  ·
    ext l m
    have key : (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) =
        fun l => (p : F.B) * g m l := by
      have hP : QL μ' ⊤ (algebraMap F.B F.Q (p : F.B) • fχ m) := by
        simpa using ql_add_smul hL.const (ql_zero (Q := F.Q) hL.const ⊤) (hfχ m).1 (p : F.B)
      refine (hB.2 _ hP).unique ?_ ?_
      · have e1 : algebraMap F.B F.Q (p : F.B) • fχ m -
            comb (fun l => ∑ i, (U * blk d k (p : F.B) 1) l i * F.σ (g m i)) e =
            -(frob p F.s (fχ m) - (p : F.Q) • fχ m) + frob p F.s (fχ m - comb (g m) e) +
              ∑ i, algebraMap F.B F.Q (F.σ (g m i)) •
                (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
          rw [comb_sum (fun l i => (U * blk d k (p : F.B) 1) l i) (fun i => F.σ (g m i)) e, frob_sub, frob_comb p F.s F.σ F.s_alg, map_natCast]
          simp only [comb, smul_sub, Finset.sum_sub_distrib]
          abel
        rw [e1]
        refine in_add (in_add (in_neg (hfχ m).2.2.1) (in_frob p F.s F.σ F.s_alg (hg m)))
          (in_sum _ _ fun i _ => in_smul (hU i).1 _)
      · have e2 : algebraMap F.B F.Q (p : F.B) • fχ m - comb (fun l => (p : F.B) * g m l) e =
            algebraMap F.B F.Q (p : F.B) • (fχ m - comb (g m) e) := by
          simp only [comb, map_mul, mul_smul, smul_sub, Finset.smul_sum]
        rw [e2]
        exact in_smul (hg m) _
    have := congrFun key l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul, ← this,
      Matrix.mul_apply, Matrix.map_apply]
  ·
    ext m m'
    have key : ∑ l, g m l * Y l m' =
        F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G (tb m') (χ m))) := by
      refine hasPeriod_unique hv hε F c hL hμ (tb m')
        (hasPeriod_comb hv hε F c hL hμ (tb m') e hDe (fun l => Y l m') (fun l => hY l m') (g m)) ?_
      exact hasPeriod_of_in hv hε F c hL hμ (tb m') ((hfχ m).2.2.2.2.2 (tb m')) (hg m) (hcomb0 m)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [key, hpair]
    by_cases h : m' = m
    · subst h; simp
    · simp [h, Ne.symm h]
  ·
    intro i m
    have hlie := _root_.GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero p C v O hv G d c (e0 (Sum.inl i)) (hB0.1 (Sum.inl i)).1 (hcob0 i)
    have h2 := GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inl i)) 0 (hB0.1 _) hlie (tb m)
    simpa using (hperO _ m).unique hCf h2
  · intro m j
    exact (hred m).1 j
  · intro j m
    exact (hperO _ m).unique hCf
      (GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate p C v O hv G d c C hCf (e0 (Sum.inr j)) (lb j) (hB0.1 _) (hLie0 j) (tb m))
  · intro m
    rw [(hfχ m).2.2.2.2.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := (hred m).2 i
    rw [lin_map F.θ Θ hΘ, (hfχ m).2.2.2.1 i, hΘ] at h1
    rw [hw, Matrix.of_apply, hCf.inj h1]

end GlobalTheory.QLog.WindowMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSquaredThetaTermsTorusCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

theorem gs_top {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem unit_map_map {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.CoefInt

namespace GlobalTheory.Poinc.Sep.CoefInt

theorem integral_sq_terms : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult →
    ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁),
    (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) →
    ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X)
      (hs : ∀ k, IsUnit (s (.inr k))),
    GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) →
    (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) →
    ∃ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
      (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)))
      (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε))
      (s₀ : V₁) (G : X → C → V₁),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') ∧
      (∀ c, b c ^ N₁ = 1) ∧
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) ∧
      IsUnit s₀ ∧
      (∀ mu c, u mu c ^ 2 * s₀ = ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) * G mu c) ∧
      ∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro N₁ hN₁ V₁ _ _ _ hV hunit D hPE hTB X C _ e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ N₁ := by omega
  obtain ⟨th, g, b, w, hgb, ho, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ := thetaTerms_integral D hN1 e _ hT
  obtain ⟨θ, hθ, -, hlamE, -, -⟩ := ThetaOne.main hV D
  obtain ⟨lam, hlam, -⟩ := hlamE (FractionRing V₁) th
  have hψ0 := _root_.GlobalTheory.Poinc.Sep.PsiZero.psi_zero_mul_rigK V₁ D hTB

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D) ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)
    obtain ⟨ε', hε'⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε' z J hJ, gm_top_eq, unit_map_map]
  choose t htg htv using ht

  have hχ : ∀ mu c, ∃ χt : LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε), χt.IsGen ∧
      (∀ z J, Good D.P.L z J → val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J =
        val ((g c).s (e mu)) (𝟙 _) z J) ∧
      (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ D.c (e mu))
        (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c ^ i) (toUnit (TF (R := V₁) (FractionRing V₁)) ≫ b c) =
        val χt (toUnit (TF (R := V₁) (FractionRing V₁))).left z J ^ N₁) := by
    intro mu c
    obtain ⟨t', ht'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_gen_local (D := D)
      ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε
    obtain ⟨ε', h1, h2⟩ := char_unit hN1 (g c) (b c) (hgb c) (ho c) (e mu) t' ht'
    obtain ⟨χt, hg, hv⟩ := rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε')
    refine ⟨χt, hg, fun z J hJ => Units.ext ?_, fun z J hJ => Units.ext ?_⟩
    · rw [hv _ _ z J hJ, Units.val_mul, h1 z J hJ, gm_top_eq, unit_map_map]
    · rw [h2 z J hJ, hv _ _ z J hJ, mul_pow, Units.val_mul]
      simp only [Units.val_pow_eq_pow_val]
      rw [gm_top_eq, unit_map_map]
  choose χt hχg hχv hχc using hχ

  have hG : ∀ mu c, ∃ G : V₁, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
          (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
            (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := fun mu c =>
    GlobalTheory.T.thetaSquare_product_isFunction_on_spec V₁ D θ (b c) (e mu) (t c) (htg c) (χt mu c) (hχg mu c) (τ₀ (e mu) (-e mu)) (hτ _ _).1
  choose G hGv using hG
  have hk := fun mu => GlobalTheory.T.psi_sq_genericPoint_eq_monomial_mul_symmetric V₁ D hPE hψ0 τ₀ _ _ _ hτ (e mu)
  choose k hkv hkψ using hk
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have key : ∀ mu c, algebraMap V₁ (FractionRing V₁) (u mu c * mo mu) ^ 2 =
      lam ^ 2 * (k mu : FractionRing V₁) * algebraMap V₁ (FractionRing V₁) (G mu c) := by
    intro mu c
    have E1 := GlobalTheory.T.thetaFamily_coefficient_integral_torusPoint V₁ D θ lam th hlam hψ0 (e mu) (g c) (b c) (hgb c) (w c) _ (hcoef mu c) z J hJ
    have E2 := hkψ mu z J hJ
    have E3 := hGv mu c _ (toUnit (TF (R := V₁) (FractionRing V₁))).left z J hJ
    rw [gs_top, htv c z J hJ, hχv mu c z J hJ] at E3
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at E2 E3
    apply cst_inj z
    rw [cst_eq] at E2 E3
    rw [cst_eq, cst_eq] at E1
    rw [cst_eq, cst_eq, map_pow (cstH z), E1, map_mul (cstH z), map_mul (cstH z), map_pow (cstH z), E3,
      mul_pow, mul_pow, mul_pow, mul_pow, E2]
    ring

  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hsplit : ∀ mu, (k mu : FractionRing V₁) =
      (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inl j)) ^ ε (.inl j) (e mu) (e mu)) *
      ∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu) := by
    intro mu
    rw [hkv mu, ← Fintype.prod_sum_type (fun j => algebraMap V₁ (FractionRing V₁) (s j) ^ ε j (e mu) (e mu))]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hk0 : (k 0 : FractionRing V₁) = 1 := by
    rw [hkv]; simp
  have hl0 : lam ^ 2 * algebraMap V₁ (FractionRing V₁) (G 0 c₀) = 1 := by
    have := key 0 c₀
    rw [hc₀, map_one, one_pow, hk0, _root_.mul_one] at this
    exact this.symm
  obtain ⟨c₁, hc₁⟩ := _root_.GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq N₁ hN₁ V₁ hV hunit D θ hθ C b hcov
  have hb1 : b c₁ * D.c (e 0) = b c₁ := by rw [map_zero, ThetaOne.c_zero, _root_.mul_one]
  have hG1 : IsUnit (G 0 c₁) := hc₁ (G 0 c₁) (fun Z r z J => val (t c₁) r z J ^ 2 * val (χt 0 c₁) r z J ^ 2 *
      val D.sym (r ≫ (D.c (e 0)).left) z J * (val (τ₀ (e 0) (-e 0)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹)
    (fun Z r z J hJ => by rw [hGv 0 c₁ Z r z J hJ, hb1])
  have hs₀u : IsUnit (G 0 c₀) := by
    have k1 := key 0 c₁
    rw [hk0, _root_.mul_one] at k1
    refine IsUnit.of_mul_eq_one ((u 0 c₁ * mo 0) ^ 2 * ↑hG1.unit⁻¹) (hinj ?_)
    rw [map_mul, map_mul, map_one, map_pow, k1]
    have hGne : algebraMap V₁ (FractionRing V₁) (G 0 c₁) * algebraMap V₁ (FractionRing V₁) ↑hG1.unit⁻¹ = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    linear_combination (algebraMap V₁ (FractionRing V₁) (G 0 c₀) * lam ^ 2) * hGne + hl0
  have hP : ∀ mu, algebraMap V₁ (FractionRing V₁) ((∏ k, (hs k).unit ^ ε (.inr k) (e mu) (e mu) : V₁ˣ) : V₁) =
      ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
    intro mu
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    change (((Units.map (algebraMap V₁ (FractionRing V₁)).toMonoidHom ((hs k).unit ^ ε (.inr k) (e mu) (e mu)) :
      (FractionRing V₁)ˣ)) : FractionRing V₁) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec]
    rfl
  refine ⟨θ, b, t, χt, G 0 c₀, G, hθ, hbN, fun c => ⟨htg c, fun κ hκ Z r z' J' hJ' => ?_⟩,
    fun mu c => ⟨hχg mu c, fun T z' J' hJ' =>
      GlobalTheory.T.cubicalProduct_identity_of_genericPoint V₁ D N₁ (b c) (D.c (e mu)) (hbN c) (χt mu c) (hχg mu c) (hχc mu c) T z' J' hJ'⟩,
    hs₀u, fun mu c => ?_, hGv⟩
  · refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D N₁ (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · apply hinj
    have km := key mu c
    rw [hsplit, map_mul, mul_pow, ← hmo2 mu] at km
    have hmo0 : algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero_iff _ hinj).2 (hmo mu).1)
    have h3 : algebraMap V₁ (FractionRing V₁) (u mu c) ^ 2 =
        lam ^ 2 * (∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
          algebraMap V₁ (FractionRing V₁) (G mu c) :=
      mul_left_cancel₀ hmo0 (by linear_combination km)
    rw [map_mul, map_mul, map_pow, hP, h3]
    linear_combination ((∏ j, algebraMap V₁ (FractionRing V₁) (s (.inr j)) ^ ε (.inr j) (e mu) (e mu)) *
      algebraMap V₁ (FractionRing V₁) (G mu c)) * hl0

end GlobalTheory.Poinc.Sep.CoefInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOOfPowEqOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

theorem mem_O_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  haveI := RatModel.isIntegrallyClosed_O hn z
  have hint : IsIntegral (M.O z) u :=
    ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (c : CTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → (∀ μ κ, ‖t c yy₁ μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t c yy₁ μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t c yy₁ μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D p _ z₁ z₂ hz
  obtain ⟨U, hU, hB⟩ := GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D p z₁ z₂ hz
  classical
  refine ⟨fun a κ => U κ * part D z₁ z₂ a κ,
    fun c yy₁ => if h : IsLab X₁ ε₁ c yy₁ then (hB c yy₁ h).choose else fun _ _ => 0, ?_, ?_⟩
  · intro a κ z' hz'
    obtain ⟨k, hk, hUk⟩ := hU κ
    have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun z => by
      haveI := D.X.normal
      exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩
    refine mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hUk) ?_
    rw [part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (_root_.GlobalTheory.Poinc.GSumInt.main g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ j z' hz')
  · intro c yy₁ hl
    simp only [dif_pos hl]
    exact (hB c yy₁ hl).choose_spec

end GlobalTheory.Poinc.GSum
end
end

