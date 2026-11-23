module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CmbPiA
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.TestsEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ValNil
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaFixTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0004
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableGA
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem pow_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (U : H →L[ℂ] H) (k : ℕ) :
    ‖U ^ k‖ ≤ (‖U‖ + 1) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

private theorem final_bd (κ g t : ℂ) (hκ : κ ≠ 0) (C a b u ρ : ℝ) (N k : ℕ) (hρ : 0 < ρ) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ ρ ^ k) (hb : b ≤ (u + 1) ^ k)
    (h : ‖κ * 1 * g - t / 2‖ ≤ C * (1 + k) ^ N * a + C * b * (ρ / (u + 1)) ^ k) :
    ‖g - t / (2 * κ)‖ ≤ ‖κ‖⁻¹ * (2 * |C|) * (1 + k) ^ N * ρ ^ k := by
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have e : κ * 1 * g - t / 2 = κ * (g - t / (2 * κ)) := by field_simp
  rw [e, norm_mul] at h
  have h1 : (1 : ℝ) ≤ (1 + k) ^ N := one_le_pow₀ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have h2 : C * (1 + k) ^ N * a ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) ha ha0 (by positivity)
  have h3 : C * b * (ρ / (u + 1)) ^ k ≤ |C| * (1 + k) ^ N * ρ ^ k := by
    calc C * b * (ρ / (u + 1)) ^ k ≤ |C| * (u + 1) ^ k * (ρ / (u + 1)) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C) hb hb0 (abs_nonneg C)) (by positivity)
      _ = |C| * 1 * ρ ^ k := by
          rw [mul_assoc, ← mul_pow, mul_one]
          congr 2
          field_simp
      _ ≤ _ := by gcongr
  rw [mul_assoc, mul_assoc, le_inv_mul_iff₀ hκ']
  linarith

end UpperTheory.Zero.ConvolutionTheory.EB

open UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Mult.stableGA :
    PiFin → PiAdm → GrowthPiJ → CmbPiA → CuspReadI → UpperTheory.V.Z.Mult.StableBlockGA := by
  intro hFin hAdm hG hPi hR E _ _ _ hE n hn l₁ l₂
  have hSp := specP _ (cuspReadP_inf hR)
  haveI : Nontrivial (InfinitePlace E) := _root_.GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace E hE
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  haveI : BorelSpace (GA E 0) := ⟨rfl⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E n
  obtain ⟨μ₂, hμ₂⟩ := haarEx E 0
  obtain ⟨D, -, hD⟩ := hG E n hn μ₁ μ₂
  obtain ⟨A⟩ := arEx E n 0 l₁ l₂ D
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E n
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E 0
  obtain ⟨κ, hκ, hell⟩ := cmbEll E hE n 0 l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c₁, hc₁, hl⟩ := hPi E hE n hn l₁ l₂ D A u₁ u₂ hu₁
  refine ⟨c₁ / ‖2 * κ‖, div_pos hc₁ (norm_pos_iff.2 (mul_ne_zero two_ne_zero hκ)),
    fun π hreg hdual hinf S hS Z hZ B τ hB hτ => ?_⟩
  have hθ : ThetaFix π := DiscreteGroups.T1.G.thetaFixOf E n hn π hdual
  obtain ⟨c₀, hc₀, htr⟩ := hl π hreg hdual hinf S hS Z hZ B τ hB hτ
  refine ⟨c₀ / (2 * κ), by rw [norm_div, hc₀], fun φ hφ hrg => ?_⟩
  obtain ⟨L, hL⟩ := lvEx E n 0 Z φ hφ
  obtain ⟨c, hc, htest⟩ := cmbTest E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  obtain ⟨k1, k2, -⟩ := kgFacts E n S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  obtain ⟨k3, -, -⟩ := kgFacts E 0 S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have hT := fun W hW => testsEx hAdm E n hn l₁ l₂ D A π hθ (Kg S L.L₁) W k1 k2 hW
  obtain ⟨kp, ko, -⟩ := hT ⊥ inferInstance
  haveI : CompleteSpace ((piSp D π A.blk.I)ᗮ : Submodule ℂ A.blk.Hb) := (Submodule.isClosed_orthogonal _).completeSpace_coe
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E n 0 l₁ l₂ D A S Z L hS hZ {π} Set.subsingleton_singleton
    (fun π' h => by rw [Set.mem_singleton_iff.1 h]; exact hθ.1) (piSp D π A.blk.I)ᗮ ko (fun W hW => (hT W hW).2.2)
  refine ⟨J, hJ, D₁, B₁, fun j => ⟨(a1 j).1 π rfl, fun w hw => ((a1 j).2 w hw).1⟩, fun j => (a2 j).1,
    fun T hTS hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn'⟩ := a3 T e₁ e₂ ρ ⟨hTS, hT'⟩ hd hρ fun j => by
    rw [valNil E n Z T S (D₂ j) (B₁ j) (B₂ j) e₁ e₂ hS hZ hTS hd fun w hw => ((a1 j).2 w hw).2]
    exact hv j
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := powRep E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  have hfin := hFin E n hn D π hθ A.μa A.μb A.ha A.hb _ _ Unit _ _ _ _ _ _ ((Kg S L.L₁).prod (Kg S L.L₂)) o₁.ka o₁.kb o₁.ψ
    (k1.prod k3) (fun x y u hu h => (idmAct E n 0 l₁ l₂ D A S Z L hS hZ).2.1 T φ _ _ hL x y u.1 hu.1 u.2 hu.2 h)
  obtain ⟨C, N, hb⟩ := hD π hθ A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) (ρ / (‖U‖ + 1)) b₁.1 b₂.1 hfin b₁.2.1 b₂.2.1
    (by positivity) (by positivity) (by positivity)
  obtain ⟨CU, u1, -, u3⟩ := hU
  obtain ⟨v1, v2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 CU _ _ u1
  rw [u3] at v2
  have p1 := powNorm A.blk.Hb (piSp D π A.blk.I) U _ (kp _ _ v1 v2) le_rfl
  have p2 := powNorm A.blk.Hb (piSp D π A.blk.I)ᗮ U ρ (ko _ _ v1 v2) hn'.le
  obtain ⟨-, hs⟩ := seenFam E n 0 S Z L hZ φ T e₁ e₂ hL ⟨hTS, hT'⟩
  refine ⟨‖κ‖⁻¹ * (2 * |C|), N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hrg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hrg ⟨hTS, hT'⟩ hrk c1
  have hw := htr L φ T _ _ Cm _ hL (hs k).1 hd c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ _ q1 q2 (p1 k).1 (p2 k).1
    (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht) hw
  rw [he, c2, (hs k).2.2.2] at hb'
  have hf := final_bd κ _ _ hκ C _ _ ‖U‖ ρ N k hρ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (p2 k).2 (pow_norm_le U k) hb'
  refine le_of_eq_of_le (congrArg norm ?_) hf
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableSA
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.stableSA :
    Enlarge → Places → StableBlockGA → StableBlockSA := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn l₁ l₂
  obtain ⟨c₀, hc₀, hl⟩ := hG E hunr n hn l₁ l₂
  refine ⟨c₀, hc₀, fun π hreg hd hinf S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl π hreg hd hinf S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end

