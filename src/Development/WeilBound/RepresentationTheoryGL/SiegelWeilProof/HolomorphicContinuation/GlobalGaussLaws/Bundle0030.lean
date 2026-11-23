module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0029
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneBH

variable {D : D7} {n : ℕ}

theorem mt_mul' (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem shiftPt (V : HSp D) (x k : GA D V) (y : Mx D V.rank n) :
    HMul.hMul (mt V (x * k⁻¹)⁻¹) y = HMul.hMul (mt V k) (HMul.hMul (mt V x⁻¹) y) := by
  rw [mul_inv_rev, inv_inv, mt_mul', Matrix.mul_assoc]

theorem leftInv_absTheta (V : HSp D) (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show ‖φ (HMul.hMul (mt V (γ * h)⁻¹) (rat ξ))‖ₑ = ‖φ (HMul.hMul (mt V h⁻¹) (rat (u.1 * ξ)))‖ₑ
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

section Quot

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure]

theorem absTheta_eq (φ : Mx D V.rank n → ℂ) (y : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V φ y =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (rat ξ : Mx D V.rank n))‖ₑ := rfl

theorem absThetaInt_eq (φ : Mx D V.rank n → ℂ) :
    GlobalTheory.SiegelFormula.absThetaInt V ν φ = ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V ν := rfl

theorem int_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ∫ q, descend (GQ V) f q ∂autMeasure V ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, integral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact integral_congr_ae (.of_forall fun x => hf.descend_mk x)

theorem lint_q (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) :
    ∫⁻ q, descend (GQ V) f q ∂autMeasure V ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, lintegral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact lintegral_congr fun x => hf.descend_mk x

theorem intg_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν)) :
    Integrable f (ν.restrict (stdDom (GQ V))) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [← memLp_one_iff_integrable] at hi ⊢
  have := (memLp_quotMeasure_iff (isFundamentalDomain_stdDom (GQ V) ν)).1 hi
  rwa [hf.lift_descend] at this

theorem desc_r {X' : Type} (f : GA D V → X') (hf : LeftInv (GQ V) f) (k : GA D V) (q : GlobalTheory.AutomorphicL2Unitary.Quot (GQ V)) :
    descend (GQ V) (fun x => f (x * k)) q = descend (GQ V) f (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k q) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  induction q using Quotient.inductionOn with
  | h x => exact ((hf.mul_right k).descend_mk x).trans (hf.descend_mk (x * k)).symm

theorem mp_r (k : GA D V) :
    MeasurePreserving (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k) (autMeasure V ν) (autMeasure V ν) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : ν.IsMulRightInvariant := GlobalTheory.RegSch.Ibp.isMulRightInvariant ν
  exact measurePreserving_rmul k

theorem int_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫ x in stdDom (GQ V), f (x * k) ∂ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  rw [← int_q V ν _ (hf.mul_right k), ← int_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).integral_comp' (descend (GQ V) f)

theorem lint_r (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫⁻ x in stdDom (GQ V), f (x * k) ∂ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  rw [← lint_q V ν _ (hf.mul_right k), ← lint_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (descend (GQ V) f)

theorem intg_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν))
    (k : GA D V) : Integrable (fun x => f (x * k)) (ν.restrict (stdDom (GQ V))) := by
  refine intg_q V ν _ (hf.mul_right k) ?_
  have e : descend (GQ V) (fun x => f (x * k)) = descend (GQ V) f ∘ GlobalTheory.ThetaInv.rmulEquiv (GQ V) k :=
    funext fun q => desc_r V f hf k q
  rw [e]
  exact ((mp_r V ν k).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi

end Quot

section Kernel

variable (V : HSp D)

def tK (φ : Mx D V.rank n → ℂ) (x : GA D V) : ℂ :=
  ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, φ (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n))

def FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) : ℂ :=
  φ (HMul.hMul (Formalism.L2.Theta.mt V (hh t)) (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)))

theorem leftInv_tK (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (tK V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show φ (HMul.hMul (Formalism.L2.Theta.mt V (γ * h)⁻¹) (rat ξ)) = φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (rat (u.1 * ξ)))
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

theorem tsum_FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, FF V φ hh x t ξ = tK V φ (x * (hh t)⁻¹) :=
  tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

theorem tsum_nFF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, ‖FF V φ hh x t ξ‖ₑ = GlobalTheory.SiegelFormula.absTheta V φ (x * (hh t)⁻¹) := by
  rw [absTheta_eq]
  exact tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

end Kernel

end PositivityTheory.Rg.Sw.Glob.DerOneBH

namespace PositivityTheory.Rg.Sw.Glob

open DerOneBH

set_option maxHeartbeats 1000000 in
theorem derivOne_of (hW : GlobalTheory.Published.WeilThetaConvergence) (hC : DerOneH.CurveSt) : DerivOne := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX Θ Θ' hΘ'
  obtain ⟨h0, -, hΦ⟩ := hC D n V θ τ s ε fr X hx.hθ hx.hs hx.hfr hX
  haveI : ν.IsHaarMeasure := hx.hν
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (autMeasure V ν) := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure ν
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  letI : MeasurableSpace (Matrix (Fin V.rank) (Fin n) D.host.E) := ⊤
  haveI : MeasurableSingletonClass (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun _ => trivial⟩
  haveI : IsFiniteMeasure (ν.restrict (stdDom (GQ V))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ (isFundamentalDomain_stdDom (GQ V) ν)]
        exact measure_lt_top _ _⟩
  have hT : ∀ Φ : schwartzA θ V.rank n, theta ω Φ 1 = tK V Φ.1 := fun Φ => by
    funext x
    simp only [theta, map_one, Module.End.one_apply, tK]
  have hfinA : ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤ :=
    fun Φ => hW D n V hx.hn (Or.inr hx.hr.2.2) θ hx.hθ ν hx.hν Φ
  have hfinA' : ∀ (Φ : schwartzA θ V.rank n) (k : GA D V),
      ∫⁻ x in stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V Φ.1 (x * k) ∂ν = GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 :=
    fun Φ k => by
      rw [lint_r V ν _ (leftInv_absTheta V Φ.1) k, ← lint_q V ν _ (leftInv_absTheta V Φ.1), absThetaInt_eq]
  have hintT : ∀ Φ : schwartzA θ V.rank n, Integrable (descend (GQ V) (tK V Φ.1)) (autMeasure V ν) := fun Φ => by
    rw [← hT]; exact _root_.GlobalTheory.StdThetaInt.integrable_theta hW D n V hx.hn hx.hr.2.2 θ hx.hθ ω ν hx.hν Φ 1
  have hhinv0 : (DerOneH.hhT θ V τ fr X 0)⁻¹ = 1 := by rw [h0, inv_one]
  have hmeasA : ∀ (Φ : schwartzA θ V.rank n) (t : ℝ), Measurable fun x : GA D V =>
      ∑' ξ, ‖FF V Φ.1 (DerOneH.hhT θ V τ fr X) x t ξ‖ₑ :=
    fun Φ t => Measurable.tsum fun ξ =>
      (((hΦ Φ).1 (rat ξ : Mx D V.rank n)).comp (Continuous.prodMk continuous_id continuous_const)).enorm.measurable
  have key := DerOneAbsH.integral_deriv_zero (ν.restrict (stdDom (GQ V)))
    (FF V Θ.1 (DerOneH.hhT θ V τ fr X)) (FF V Θ'.1 (DerOneH.hhT θ V τ fr X))
    (fun x ξ t _ => by
      have := (hΦ Θ).2 (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)) t
      rw [← hΘ'] at this
      exact this)
    (fun x ξ => by
      have h := ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).comp
        (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (x, t))
      exact h)
    (fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).aestronglyMeasurable)
    (by
      have hm : Measurable fun p : GA D V × ℝ => ∑' ξ, ‖FF V Θ'.1 (DerOneH.hhT θ V τ fr X) p.1 p.2 ξ‖ₑ :=
        Measurable.tsum fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).enorm.measurable
      rw [lintegral_prod_symm _ hm.aemeasurable]
      simp only [tsum_nFF, hfinA']
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      simp only [sub_zero, ENNReal.ofReal_one, mul_one]
      exact (hfinA Θ').ne)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 0).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 1).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact intg_q V ν _ (leftInv_tK V Θ.1) (hintT Θ))
    (by
      simp only [tsum_FF]
      exact intg_r V ν _ (leftInv_tK V Θ.1) (hintT Θ) _)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ.1) _)
    (fun t _ => by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ'.1) _)
  simp only [tsum_FF, hhinv0, mul_one] at key
  rw [thetaInt, hT, average_eq, int_q V ν _ (leftInv_tK V Θ'.1), key, smul_zero]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussO
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

private theorem isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one {n : ℕ} (A B D : Matrix (Fin n) (Fin n) ℂ) (h1 : Aᴴ * D = 1)
    (h3 : Bᴴ * D = Dᴴ * B) : IsUnit A.det ∧ D = (Aᴴ)⁻¹ ∧ (B * Aᴴ)ᴴ = B * Aᴴ := by
  have hDA : D * Aᴴ = 1 := mul_eq_one_comm.mp h1
  have hAD : A * Dᴴ = 1 := by simpa using congrArg conjTranspose hDA
  refine ⟨?_, (inv_eq_right_inv h1).symm, ?_⟩
  · have h := congrArg det h1
    rw [det_mul, det_one, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, star_zero, zero_mul] at h
    exact zero_ne_one h
  · rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc A * Bᴴ = A * (Bᴴ * D) * Aᴴ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hDA, Matrix.mul_one]
      _ = A * (Dᴴ * B) * Aᴴ := by rw [h3]
      _ = B * Aᴴ := by rw [← Matrix.mul_assoc A Dᴴ B, hAD, Matrix.one_mul]

theorem siegelP_data (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) :
    IsUnit (mR q).toBlocks₁₁.det ∧ (mR q).toBlocks₂₂ = ((mR q).toBlocks₁₁ᴴ)⁻¹ ∧
      ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)ᴴ = (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  have hG : InG (mR q) := q.2
  rw [InG, ← fromBlocks_toBlocks (mR q), hq, JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hG
  simp at hG
  exact isUnit_det_and_eq_inv_of_conjTranspose_mul_eq_one _ _ _ hG.1 (neg_add_eq_zero.mp hG.2.2).symm

theorem siegelP_actZ (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ) :
    actZ q Z = (mR q).toBlocks₁₁ * Z * (mR q).toBlocks₁₁ᴴ + (mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hu' : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by
    rw [det_conjTranspose]
    exact hu.star
  rw [actZ, hq, Matrix.zero_mul, zero_add, hD, Matrix.nonsing_inv_nonsing_inv _ hu', Matrix.add_mul]

theorem siegelP_jF (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (e : ℤ) (p p' : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    jF e p p' q Z = (mR q).toBlocks₁₁.det ^ e * (star (mR q).toBlocks₁₁.det) ^ (((p + p' : ℕ) : ℤ) - e) := by
  obtain ⟨hu, hD, -⟩ := siegelP_data q hq
  have hdet : det (mR q) = (mR q).toBlocks₁₁.det * (mR q).toBlocks₂₂.det := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR q), hq]
    exact det_fromBlocks_zero₂₁ _ _ _
  have hs : star (mR q).toBlocks₁₁.det ≠ 0 := hu.star.ne_zero
  rw [jF, hq, Matrix.zero_mul, Matrix.zero_mul, zero_add, hdet, hD, det_nonsing_inv,
    det_conjTranspose, Ring.inverse_eq_inv']
  generalize (mR q).toBlocks₁₁.det = a at hs ⊢
  generalize star a = s at hs ⊢
  rw [mul_zpow, _root_.inv_zpow', _root_.inv_zpow', _root_.inv_zpow', neg_neg, neg_neg, mul_assoc,
    mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]
  congr 2
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableAbsThetaToReal
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ}

def thS (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ℂ := ∑' ξ, f (invPt V h ξ)

theorem leftInv_thS (V : HSp D) (f : Mx D V.rank n → ℂ) : LeftInv (GQ V) (thS V f) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (invPt V h ξ))
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem enorm_thS_le (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ‖thS V f h‖ₑ ≤ absTheta V f h :=
  enorm_tsum_le_tsum_enorm

theorem absTheta_mono (V : HSp D) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) (h : GA D V) :
    absTheta V f h ≤ absTheta V M h :=
  ENNReal.tsum_le_tsum fun _ => enorm_le_iff_norm_le.2 (hfM _)

theorem absThetaInt_mono (V : HSp D) (ν : Measure (GA D V)) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) :
    absThetaInt V ν f ≤ absThetaInt V ν M :=
  lintegral_mono fun q => absTheta_mono V hfM _

theorem absThetaInt_smul_lt (V : HSp D) (ν : Measure (GA D V)) (c : ℂ) {M : Mx D V.rank n → ℂ}
    (hM : absThetaInt V ν M < ⊤) : absThetaInt V ν (c • M) < ⊤ := by
  unfold absThetaInt
  have : ∀ q, descend (GQ V) (absTheta V (c • M)) q = ‖c‖ₑ * descend (GQ V) (absTheta V M) q := fun q =>
    GlobalTheory.AbsThetaSemi.absTheta_smul V c M q.out
  simp_rw [this]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top hM

theorem aestronglyMeasurable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : AEStronglyMeasurable (descend (GQ V) (thS V f)) (autMeasure V ν) := by
  rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_thS V f).lift_descend]
  have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V f) q < ⊤ :=
    ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hf) hfin.ne
  have hae' : ∀ᵐ h ∂ν, absTheta V f h < ⊤ := by
    have := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)) hae
    filter_upwards [this] with h hh
    rwa [(leftInv_absTheta V f).descend_mk] at hh
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => f (invPt V h ξ) :=
    hae'.mono fun h hh => Summable.of_enorm hh.ne
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν)
    (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
    (f := fun F h => ∑ ξ ∈ F, f (invPt V h ξ))
    (fun F => (continuous_finsetSum F fun ξ _ =>
      hf.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
    (hsum.mono fun h hh => hh.hasSum)

theorem ae_absTheta_lt (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V M) q < ⊤ :=
  ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM) hfin.ne

theorem integrable_absTheta_toReal (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) :
    Integrable (fun q => (descend (GQ V) (absTheta V M) q).toReal) (autMeasure V ν) :=
  integrable_toReal_of_lintegral_ne_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM).aemeasurable hfin.ne

theorem sch_facts (hP : GlobalTheory.Published.WeilThetaConvergence) (V : HSp D) (hn : 1 ≤ n) (hr : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {M : Mx D V.rank n → ℂ}
    (hM : M ∈ schwartzA θ V.rank n) : Continuous M ∧ absThetaInt V ν M < ⊤ :=
  ⟨(_root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ _ _ M (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ M hM)).1,
    hP D n V hn (Or.inr hr) θ hθ ν hν ⟨M, hM⟩⟩

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SummableOfAbsTheta
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem summable_of_absTheta {D : D7} {V : HSp D} {n : ℕ} (φ : Mx D V.rank n → ℂ) (h : GA D V)
    (hh : GlobalTheory.SiegelFormula.absTheta V φ h < ⊤) :
    Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => φ (GlobalTheory.SiegelFormula.invPt V h ξ) :=
  Summable.of_enorm hh.ne

theorem thLin_of (hP : GlobalTheory.Published.WeilThetaConvergence) : ThLin := by
  intro D n V ψ χ θ μ ω H l s ν Φ Φ' hS hS' hR g
  obtain ⟨h1, h2, hr⟩ := hR
  have hn : 1 ≤ n := by omega
  have hI := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ g
  have hI' := GlobalTheory.StdThetaInt.integrable_theta hP D n V hn hr θ hS.hθ ω ν hS.hν Φ' g
  have hae : ∀ φ : schwartzA θ V.rank n,
      ∀ᵐ q ∂autMeasure V ν, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ := by
    intro φ
    have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hS.hθ ν hS.hν φ
    have hcont : Continuous φ.1 := (_root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hS.hθ _ _ φ.1
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hS.hθ _ _ φ.1 φ.2)).1
    exact ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
  have heq : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (Φ + Φ') g) q) =ᵐ[autMeasure V ν]
      fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q + GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ' g) q := by
    filter_upwards [hae (ω g Φ), hae (ω g Φ')] with q hq hq'
    simp only [GlobalTheory.AutomorphicL2Unitary.descend] at hq hq' ⊢
    have s1 := summable_of_absTheta (ω g Φ).1 _ hq
    have s2 := summable_of_absTheta (ω g Φ').1 _ hq'
    show (∑' ξ, (ω g (Φ + Φ')).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) =
      (∑' ξ, (ω g Φ).1 (GlobalTheory.SiegelFormula.invPt V _ ξ)) + ∑' ξ, (ω g Φ').1 (GlobalTheory.SiegelFormula.invPt V _ ξ)
    rw [← s1.tsum_add s2]
    congr 1
    funext ξ
    simp [map_add (f := _)]
  unfold thetaInt
  rw [MeasureTheory.average_eq, MeasureTheory.average_eq, MeasureTheory.average_eq, integral_congr_ae heq,
    integral_add hI hI', smul_add]

end PositivityTheory.Rg.Sw.Glob
end
end

