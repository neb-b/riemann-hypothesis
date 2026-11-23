module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoinConvBdd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.HasDSComp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.ExistsIrreducibleSubrepresentationBis
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.Bundle0001
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.TestFnConstTermVanishX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrUnitaryTraceNeZeroCopyFinDSX
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallCentreInterpolationDetWeightSmallSignatu
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

section
open ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.OrbitInterpSmall

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_bound {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {s : ℝ} (hs : 2 * ((r : ℝ) - 1) ≤ s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  have hr : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  exact _root_.GlobalTheory.OrbitSum.orbitSum_le E r X x0 h0 hPD s (by linarith) (_root_.GlobalTheory.IntBall.intBall E r X hp0 hp1 hq s hs)

theorem kappa_exists {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (h0 : IsOrth X x0) (hPD : PropDisc X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) {bb : ℝ}
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) :
    ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧
      (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧
      (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom,
        ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧
      ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x := by
  obtain ⟨hm, hpos, hinv, hch⟩ := GlobalTheory.FramePotential.frame_potential_basic r X x0 h0
  obtain ⟨C, hC, hS⟩ := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  refine GlobalTheory.kaFrame_of_delta X x0 bb hb0 _ (fun x => Finset.prod_nonneg fun τ _ => by positivity)
    hm hpos hinv hch (GlobalTheory.MinorRatioNear.minorRatio_near r X x0 h0) ⟨C, hC, fun x hx => ?_⟩
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hS x hx)
  have hy : lact γ.1 x ∈ X.dom := MajInv.lact_mem_dom X (X.Γ_stab γ.1 γ.2) (IW.orth_mem_dom X x hx)
  congr 1
  rw [← GlobalTheory.Up.exp_neg_rhX h0 hy, ← Real.exp_mul]
  congr 1; ring


open GlobalTheory.Up.OrbitInterpolation in
theorem orbitInterp_small {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r)
    (la : Wt X.Ψ r) (ρ0 bb m : ℝ) (hPD : PropDisc X) (h0 : IsOrth X x0) (hd : 1 ≤ dimX X)
    (hp0 : 0 < X.p0) (hp1 : X.p0 < r) (hq : X.p0 * (r - X.p0) ≤ 3) (hρ0 : 0 < ρ0)
    (hG : FreeBall X G x0 ρ0) (hla : BlockConst X la)
    (hbb : 4 * ((r : ℝ) - 1) ≤ bb) (hb0 : 0 < bb) (hm : bb + dimX X / ρ0 < m)
    (hcurv : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ)
    (hSS : ∀ P, X.IsBddSec la P → P ∈ X.SS la) :
    ∃ u0 ∈ X.SS la, u0 x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → u0 (lact γ x0) = 0 := by
  classical
  have hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E) :=
    ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
  have hbb0 : 0 ≤ bb := hb0.le
  obtain ⟨κ, hκm, hκ1, hκB, hκF, ⟨Cs, hCs, hsum⟩, hloc⟩ := kappa_exists X x0 h0 hPD hp0 hp1 hq hbb hb0
  have hsumE := sum_bound X x0 h0 hPD hp0 hp1 hq (s := bb / 2) (by linarith)
  obtain ⟨-, hW, hWl⟩ := KronMetric.kronMetric hN r X la (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨⟨hz, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  let S : Submodule ℂ (Frame X.Ψ r → ℂ) :=
    { carrier := X.SS la
      add_mem' := fun {P Q} hP hQ => hadd P hP Q hQ
      zero_mem' := hz
      smul_mem' := fun a P hP => hsmul a P hP }
  obtain ⟨T, hT⟩ := X.Γ_index
  have hx0 := IW.orth_mem_dom X x0 h0
  obtain ⟨u, hu, hu1, hu0⟩ := exists_of_approx S x0
    (fun s : {s : T // s.1⁻¹ ∈ G ∧ s.1⁻¹ ∉ X.Γ} => lact s.1.1⁻¹ x0) fun η hη => by
    have hη' : 0 < η / (Cs.toReal + 1) := by positivity
    obtain ⟨F, P, hF, hIn, hP, hPF, hP1, hP0⟩ := exists_approx hN extFStatement_holds measInv_holds
      GlobalTheory.PoleExistence.poleEx_holds (GlobalTheory.PoleDbar.poleSolve measInv_holds)
      GlobalTheory.Up.polePoint_holds h0 hd hρ0 hG hla hbb0 hm hcurv hκm hκ1 hκB hκF hloc hη'
    obtain ⟨hs, hbd⟩ := GlobalTheory.PoinSumBound.poin_conv_bdd E r X x0 h0 hPD la _ bb hW hWl hb0 hsumE F P hF hIn hP hPF
    have hn : ∀ (γ : X.Γ) (y : Frame X.Ψ r), ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 y)‖ = ‖P (lact γ.1 y)‖ :=
      fun γ y => by rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have he : η / (Cs.toReal + 1) + η / (Cs.toReal + 1) * Cs.toReal = η := by field_simp; ring
    refine ⟨poin X la P, hSS _ hbd, ?_, fun s => ?_⟩
    · have hs0 := hs x0 hx0
      unfold poin
      rw [hs0.of_norm.tsum_eq_add_tsum_ite 1]
      simp only [OneMemClass.coe_one, chi_one, FundSetPf.lact_one, inv_one, one_mul]
      have hle : ∀ γ : X.Γ, ‖if γ = 1 then 0 else (X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ ≤
          ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x0)‖ := fun γ => by
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
      have hs1 := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs0
      have h2 := (norm_tsum_le_tsum_norm hs1).trans (tsum_le_of_le hs1 (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          split_ifs with h
          · rw [norm_zero]; positivity
          · rw [hn]
            exact hP0 γ.1 (hG.1 γ.2) fun h' => h (Subtype.ext h')) hCs (hsum x0 hx0))
      rw [add_sub_right_comm, ← he]
      exact (norm_add_le _ _).trans (add_le_add hP1 h2)
    · have hy := MajInv.lact_mem_dom X (hG.isUStab s.2.1) hx0
      have h2 := (norm_tsum_le_tsum_norm (hs _ hy)).trans (tsum_le_of_le (hs _ hy)
        (fun _ => norm_nonneg _) hη'.le
        (fun γ => by
          rw [hn, ← FundSetPf.lact_mul]
          refine hP0 _ (G.mul_mem (hG.1 γ.2) s.2.1) fun h => s.2.2 ?_
          rw [eq_inv_of_mul_eq_one_right h]
          exact X.Γ.inv_mem γ.2) hCs (hsum _ hy))
      exact h2.trans (by linarith)
  refine ⟨u, hu, by rw [hu1]; exact one_ne_zero, fun γ hγ hγ' => ?_⟩
  obtain ⟨s, hsT, hs⟩ := hT γ⁻¹ (hG.isUStab (G.inv_mem hγ))
  have e : s⁻¹ = (s⁻¹ * γ⁻¹) * γ := by group
  have e' : γ = (s⁻¹ * γ⁻¹)⁻¹ * s⁻¹ := by group
  have h1 : s⁻¹ ∈ G := by rw [e]; exact G.mul_mem (hG.1 hs) hγ
  have h2 : s⁻¹ ∉ X.Γ := fun h => hγ' (by rw [e']; exact X.Γ.mul_mem (X.Γ.inv_mem hs) h)
  have h3 : u (lact s⁻¹ x0) = 0 := hu0 ⟨⟨s, hsT⟩, h1, h2⟩
  have hu' : u ∈ X.SS la := hu
  rw [e', FundSetPf.lact_mul, hu'.1.1.2.2 _ (X.Γ.inv_mem hs) _
    (MajInv.lact_mem_dom X (hG.isUStab h1) hx0), h3, mul_zero]

end GlobalTheory.Up.OrbitInterpSmall
end

namespace GlobalTheory.Up.OrbitInterpSmall

theorem gapsPairing_deMul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (h0 : 0 < X.p0) (h1 : X.p0 < r) {s : ℕ} (hs : Even s) :
    GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (deMul X.Ψ r X.p0 s - kapW X) ((s : ℝ) - 2 * r + 2) := by
  obtain ⟨k, rfl⟩ := hs
  have hk : (k + k) / 2 = k := by omega
  intro τ
  refine ⟨fun i j hj hp => ?_, fun i0 i1 h0' h1' => ?_⟩
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
    simp only [Pi.sub_apply, deMul, kapW, hj']
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]; omega
    · rw [if_neg (mt e.1 hi), if_neg hi]; omega
  · simp only [Pi.sub_apply, deMul, kapW, h0', h1', hk]
    rw [if_pos h0, if_neg (by omega)]
    have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hr]
    push_cast
    linarith

theorem orbit_interp_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → X.p0 * (r - X.p0) ≤ 3 →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro E _ _ _ r X _ G x0 hx0 hFB h0 h1 hq s hs hsb
  have hd : 1 ≤ GlobalTheory.Up.dimX X := (GlobalTheory.Up.one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hD : GlobalTheory.Up.dimX X = X.Ψ.card * (X.p0 * (r - X.p0)) := rfl
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · rw [hD, h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (h0.trans h1)
  have hρ : (0 : ℝ) < 1 / (49 * (r : ℝ) ^ 2) := by positivity
  have hdR : (1 : ℝ) ≤ GlobalTheory.Up.dimX X := by exact_mod_cast hd
  have hsR : 2 * (r : ℝ) + 50 * (r : ℝ) ^ 2 * (GlobalTheory.Up.dimX X : ℝ) + 1 ≤ s := by
    rw [hD]; exact_mod_cast hsb
  have hq1 : (GlobalTheory.Up.dimX X : ℝ) / (1 / (49 * (r : ℝ) ^ 2)) = 49 * (r : ℝ) ^ 2 * GlobalTheory.Up.dimX X := by
    field_simp
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 (deMul X.Ψ r X.p0 s) ((s : ℝ) - 2 * r + 2)).2
    (gapsPairing_deMul' X h0 h1 hs) x0 hx0
  refine orbitInterp_small X G x0 _ _ (4 * ((r : ℝ) - 1) + 1 / 2) ((s : ℝ) - 2 * r + 2)
    (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) hx0 hd h0 h1 hq hρ hFB
    (fun _ _ _ h => if_congr h rfl rfl) (by linarith) (by linarith)
    (by rw [hq1]; nlinarith [mul_le_mul_of_nonneg_left hdR (sq_nonneg (r : ℝ)), sq_nonneg ((r : ℝ) - 2)])
    hcurv ?_
  refine cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (fun i j hj hp => ?_) (fun i0 i1 h0' h1' => ?_)
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    simp only [deMul]
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]
    · rw [if_neg (mt e.1 hi), if_neg hi]
  · simp only [deMul]
    rw [if_pos (by omega), if_neg (by omega)]
    omega

end GlobalTheory.Up.OrbitInterpSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDSComp
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PsCo.SpecX

open GlobalTheory GlobalTheory.SpecTraceProof MainStatements.Flath2

theorem hasDSComp (h1 : IrredSt) (h2 : CompSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
  have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
  have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨Q, hQ, hrep⟩ := _root_.GlobalTheory.TrSplit.repOp_tensor_split D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
  haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
  have hcont := continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem (placeOf D τ))
  have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) := hcont.integrable_of_hasCompactSupport (hmem _).1
  have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
    isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
  have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
  obtain ⟨W, hW⟩ := h1 _ H _ hπw (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ))) Q
    (fun S hS => hπw.comp_repOp hπw hcont (hmem _).1 S fun g v => DFunLike.congr_fun (hS g) v) hQ
    (GlobalTheory.DiscreteSum.isCompactOperator_of_isHilbertSchmidt htc.isHilbertSchmidt)
    (fun h0 => hc0 (by rw [← hc.2, hrep, h0]; exact trace_zero))
  obtain ⟨δ, hδ'⟩ := h2 D V H π hπ (placeOf D τ) W hW
  obtain ⟨c', hc', himp⟩ := GlobalTheory.PsCo.Plug.archTrace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    haveI := δ.isIrr.complete
    have hc'w : HasTrace (repOp δ.π (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := _root_.GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δ.π _ δ.isIrr hπw hδ' Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact GlobalTheory.isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

theorem copyFinDS (h1 : IrredSt) (h2 : CompSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification →  True → True → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestDataX V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → (∀ f ∈ CcGA V, IsCompactOperator (repOp π μ f)) → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ hcp c hc hc0
  have hcomp : HasDSComp M π := hasDSComp h1 h2 hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := _root_.GlobalTheory.TrCopy.isCopyFinDS_finPartDSSm D V S M H π hπ hcomp hU
  have hadm := h4 D V S M μ H π hπ.unitary hcp hU
  have hirr := GlobalTheory.FinPartIrrAdm.irreducible hπ hcomp hU hadm
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := _root_.GlobalTheory.FinTrace.hasTrace_finFn D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

theorem specTrace (h1 : IrredSt) (h2 : CompSt) (h3 : CptSt) (h4 : AdmSt) : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → True → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → True → SpecTraceX := by
  intro hDSC tc hChar hCO hPCT hPCS
  intro D V lam S M T U μa μf μ _ _ fa ff hTD ν hν n Ws _ _ σs hIrr hcover c hc
  have hcusp := GlobalTheory.PsCo.Plug.cuspOpT hCO hPCT D V lam S M T U μa μf μ fa ff hTD
  have hpone := copyFinDS h1 h2 h4 hDSC hChar hPCS D V lam S M T U μa μf μ fa ff hTD ν hν
  refine ⟨hcusp.traceClass, ?_⟩
  refine _root_.GlobalTheory.hasSum_eq_sum_of_matching_family (UDual (GA D V)) n (fun x => (mCusp V μ x.rep.π).toNat)
    (fun x => repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) (fun i => (mCuspDS μ (σs i) M).toNat) c
    (fun x i => IsCopyFinDS (σs i) M x.rep.π ⊤) _ hcusp.hasSum_trace ?_ ?_ ?_ ?_ ?_
  ·
    intro x hm ht
    have hm' : mCusp V μ x.rep.π ≠ 0 := fun h => hm (by rw [h]; simp)
    have htr : HasTrace (repOp x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff))
        (repTrace x.rep.π μ (tensor D.sp.cm.sig V.gram fa ff)) := ⟨hcusp.traceClass_rep x hm', rfl⟩
    obtain ⟨W, _, _, σ, hσi, hσa, hcopy, hσt⟩ := hpone x.rep.H x.rep.π x.rep.isIrr
      (h3 tc D V μ x.rep.H x.rep.π x.rep.isIrr hm') _ htr ht
    have hmσ : mCuspDS μ σ M ≠ 0 := by
      rwa [← _root_.GlobalTheory.AutMult.mCusp_eq_mCuspDS D V S M μ x.rep.H x.rep.π x.rep.isIrr W σ hσi hσa hcopy]
    obtain ⟨i, ⟨f⟩⟩ := hcover W σ hσi hσa hmσ (not_isIntegralOp_zero hσt ht)
    exact ⟨i, isCopyFinDS_of_equiv f hcopy⟩
  ·
    intro i hi
    have hi' : mCuspDS μ (σs i) M ≠ 0 := fun h => hi (by rw [h]; simp)
    obtain ⟨H, _, _, π, hπ, hcopy⟩ := _root_.GlobalTheory.AutMult.exists_isIrrUnitary_isCopyFinDS D V S M μ (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi'
    let R : IrrU (GA D V) := ⟨H, π, hπ⟩
    refine ⟨R.cl, isCopyFinDS_of_uEquiv ?_ hcopy⟩
    exact (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).symm
  ·
    intro x i hR
    refine ⟨?_, ?_⟩
    · rw [_root_.GlobalTheory.AutMult.mCusp_eq_mCuspDS D V S M μ x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hR]
    · exact (GlobalTheory.PsCo.Plug.copyTraceT D V lam S M T U μa μf μ fa ff hTD ν hν x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i)
        (hIrr.1 i) (hIrr.2.1 i) hR (c i) (hc i)).2
  ·
    intro x i j hi hj
    by_contra hne
    have e := (_root_.GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hi
      x.rep.H x.rep.π x.rep.isIrr (Ws j) (σs j) (hIrr.1 j) (hIrr.2.1 j) hj).1 (UEquiv.refl _)
    exact (hIrr.2.2 i j hne).false e.some
  ·
    intro x y i hx hy
    have e := (_root_.GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS D V S M x.rep.H x.rep.π x.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hx
      y.rep.H y.rep.π y.rep.isIrr (Ws i) (σs i) (hIrr.1 i) (hIrr.2.1 i) hy).2 ⟨Representation.Equiv.refl _⟩
    rw [← UDual.cl_rep x, ← UDual.cl_rep y]
    exact IrrU.cl_eq_iff.2 e

theorem main : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspTraceClass → GlobalTheory.TrMult.SpecTraceX :=
  fun ds tc => specTrace irredSt compSt cptSt admissible_representation_factorisation ds tc trivial (_root_.GlobalTheory.CuspidalOpAssembly.cuspidalOperators tc) GlobalTheory.PsCo.Plug.parabolicT trivial

end GlobalTheory.PsCo.SpecX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisSliceT
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open GlobalTheory.FlipMatch

namespace GlobalTheory.SwapHeis

theorem heis_sliceT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 → G.W.J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ) = 0 →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) = 0 →
    ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) +
                     GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι Φ (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ,
            Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hdV hdW v t ι hι d' hd' dd hdd u₁ u₂ hu₁ hu₂ hp₁ hp₂ Φ hΦ Z
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  have hc : Continuous ψv := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hstar : ∀ y, starRingEnd ℂ (ψv y) = ψv (-y) := fun y => GlobalTheory.DblVacLine.star_psiAt B.ψ hT.base.std.1 v y
  have hatT : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → At (evFin F v) uᵀ :=
    fun u hu r hr => by rw [← Matrix.transpose_smul, hu r hr, Matrix.transpose_zero]
  have Heisenberg₂ : ∀ u : Matrix (Fin (a + a')) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u →
      pairM (coX t 1 1 uᵀ) (coY σ G.V' G.W t 1 1 uᵀ) = 0 →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr ψv (GlobalTheory.LatVac.locCo G.M'.co v uᵀ) φ) Y =
          ψv (-pairM Y (coX t 1 1 uᵀ)) * ι φ (Y + coY σ G.V' G.W t 1 1 uᵀ) := by
    intro u hu hp φ hφ Y
    exact (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew hdV hdW G.M' B.ψ
      hT.base.std t 1 1 uᵀ (hatT u hu) hp φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v uᵀ (hatT u hu) φ)).2 ι hι Y
  have hloc : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).1 (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).2 (-(GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).2)) := by
    have e1 := hd' u₁ᵀ
    have e2 := hd' u₂ᵀ
    rw [Matrix.transpose_transpose] at e1 e2
    have h := hdd u₁ u₂
    ext k <;> cases k <;> simp [GlobalTheory.LatVac.locCo, h, e1, e2]
  have hconjSB : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (fun x => starRingEnd ℂ (φ x)) ∈ SB _ :=
    fun φ hφ => ⟨hφ.1.comp _, hφ.2.comp_left (map_zero _)⟩
  have hconj : ∀ (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
      (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (fun x => starRingEnd ℂ (schr ψv (w.1, -w.2) φ x)) = schr ψv w (fun x => starRingEnd ℂ (φ x)) := by
    intro w φ
    funext x
    simp only [GlobalTheory.WeilM.schr, map_mul, hstar]
    congr 2
    rw [dotProduct_neg, dotProduct_neg]
    ring
  have hbox : ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) (boxFun φ₁ φ₂)) Z =
        ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι (boxFun φ₁ φ₂) (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ) := by
    intro φ₁ h₁ φ₂ h₂
    rw [hloc, GlobalTheory.BoxSpan.schr_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.mk.eta]
    rw [GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, hconj (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ),
      Heisenberg₂ u₁ hu₁ hp₁ φ₁ h₁, Heisenberg₂ u₂ hu₂ hp₂ _ (hconjSB φ₂ h₂), map_mul, hstar, neg_neg, AddChar.map_add_eq_mul]
    ring
  let Lw : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ]
      ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    { toFun := schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂))
      map_add' := fun f g => by funext x; simp [schr, mul_add]
      map_smul' := fun c f => by funext x; simp [schr]; ring }
  let Z' : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ)
  let c : ℂ := ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ))
  let Λ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj Z).comp ((GlobalTheory.SwapSlice.sliceT ι).comp Lw) - c • (LinearMap.proj Z').comp (GlobalTheory.SwapSlice.sliceT ι)
  have hΛ : ∀ Ψ, Λ Ψ = GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Ψ) Z -
      c * GlobalTheory.SwapSlice.sliceT ι Ψ Z' := fun Ψ => rfl
  have h0 := GlobalTheory.BoxSpan.boxSpan_ker F v (Fin a' × Fin (a + a')) (Fin a' × Fin (a + a')) ψv hc
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) Λ
    (fun φ₁ h₁ φ₂ h₂ => by rw [hΛ, hbox φ₁ h₁ φ₂ h₂, sub_self]) Φ hΦ
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end GlobalTheory.SwapHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTer
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := _root_.GlobalTheory.SUAssemble.assemble _root_.GlobalTheory.PlaneSU.plane_closure _root_.GlobalTheory.PlaceIso.exists_isotropic_places F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (_root_.GlobalTheory.SUTrunc.mem_closure_supp F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (_root_.GlobalTheory.SUWeakApprox.weak_approx_SU F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinatesStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  first | exact @GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar | exact GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar | (intros; apply GlobalTheory.ResidueEisenstein.LeviConj.crd_conj_scalar <;> assumption)
end

