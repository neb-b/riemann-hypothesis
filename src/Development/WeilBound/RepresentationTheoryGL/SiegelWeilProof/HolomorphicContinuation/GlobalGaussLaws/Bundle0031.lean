module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferentiableOnAvg
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ} {V : HSp D}

structure Fam (V : HSp D) (ν : Measure (GA D V)) (U : Set ℂ) (f : ℂ → Mx D V.rank n → ℂ) : Prop where
  diff : ∀ x, DifferentiableOn ℂ (fun z => f z x) U
  maj : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ M : Mx D V.rank n → ℂ, Continuous M ∧ absThetaInt V ν M < ⊤ ∧
    ∀ z ∈ Metric.ball z₀ ε, ∀ x, ‖f z x‖ ≤ ‖M x‖
  meas : ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (f z))) (autMeasure V ν)

def dF (f : ℂ → Mx D V.rank n → ℂ) : ℂ → Mx D V.rank n → ℂ := fun z x => deriv (fun w => f w x) z

def iF (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : ℂ → Mx D V.rank n → ℂ := fun z x => iteratedDeriv r (fun w => f w x) z

theorem iF_zero (f : ℂ → Mx D V.rank n → ℂ) : iF f 0 = f := by
  funext z x; simp [iF]

theorem iF_succ (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : iF f (r + 1) = dF (iF f r) := by
  funext z x; simp only [iF, dF, iteratedDeriv_succ]

theorem cauchy_le {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall z r ⊆ U) (hC : ∀ w ∈ Metric.sphere z r, ‖g w‖ ≤ C) : ‖deriv g z‖ ≤ C / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hC
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball z hr.ne']
  exact hg.mono hsub

theorem fam_hasDeriv (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) ∧
    HasDerivAt (fun z => ∫ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν)
      (∫ q, descend (GQ V) (thS V (dF f z₀)) q ∂autMeasure V ν) z₀ := by
  obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsubU : ∀ z ∈ Metric.ball z₀ r, Metric.closedBall z r ⊆ U := by
    intro z hz w hw
    apply hball
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hmemM : ∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.sphere z r, w ∈ Metric.ball z₀ ε := by
    intro z hz w hw
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_sphere] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hcb : ∀ z ∈ Metric.ball z₀ r, ∀ x, ‖dF f z x‖ ≤ ‖M x‖ / r := fun z hz x =>
    cauchy_le (hf.diff x) hr0 (hsubU z hz) fun w hw => hMb w (hmemM z hz w hw) x
  have hballU : Metric.ball z₀ r ⊆ U := fun z hz => hsubU z hz (Metric.mem_closedBall_self hr0.le)
  have hz₀r : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  have hz₀ε : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε

  have hfinq := ae_absTheta_lt V ν hMc hMfin
  have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
    intro q hq
    refine Summable.of_eNorm ?_
    simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
  have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ = (descend (GQ V) (absTheta V M) q).toReal := by
    intro q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
    rw [ENNReal.tsum_toReal_eq fun ξ => eNorm_ne_top]
    simp

  have hdiff : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      HasDerivAt (fun z => descend (GQ V) (thS V (f z)) q) (descend (GQ V) (thS V (dF f z)) q) z := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
    refine hasDerivAt_tsum_of_isPreconnected (u := fun ξ => ‖M (invPt V q.out ξ)‖ / r) (hs.div_const r)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected (fun ξ y hy => ?_) (fun ξ y hy => hcb y hy _) hz₀r ?_ hz
    · exact ((hf.diff _).differentiableAt (hU.mem_nhds (hballU hy))).hasDerivAt
    · exact Summable.of_norm_bounded hs fun ξ => hMb z₀ hz₀ε _

  have hmeas' : AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) := by
    let s : ℕ → ℂ := fun k => z₀ + ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hs_ne : ∀ k, s k ≠ z₀ := by
      intro k h
      have : ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by simpa [s] using h
      have h2 : r / 2 / ((k : ℝ) + 1) ≠ 0 := by positivity
      exact h2 (by exact_mod_cast this)
    have hs_mem : ∀ k, s k ∈ Metric.ball z₀ r := by
      intro k
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [s, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc r / 2 / ((k : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ < r := by linarith
    have hs_lim : Tendsto s atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs_ne⟩
      have : Tendsto (fun k : ℕ => r / 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
        rw [mul_zero] at h0
        refine h0.congr fun k => ?_
        ring
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [s] using (tendsto_const_nhds (x := z₀)).add h2
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun k q => (s k - z₀)⁻¹ • (descend (GQ V) (thS V (f (s k))) q - descend (GQ V) (thS V (f z₀)) q))
      (fun k => ((hf.meas _ (hballU (hs_mem k))).sub (hf.meas _ hz₀)).const_smul (s k - z₀)⁻¹) ?_
    filter_upwards [hdiff] with q hq
    have hd := hq z₀ hz₀r
    exact (hasDerivAt_iff_tendsto_slope.1 hd).comp hs_lim
  refine ⟨hmeas', ?_⟩
  have hint0 : Integrable (descend (GQ V) (thS V (f z₀))) (autMeasure V ν) := by
    refine ⟨hf.meas _ hz₀, lt_of_le_of_lt (lintegral_mono fun q => ?_) (lt_of_le_of_lt (le_refl _) hMfin)⟩
    exact (enorm_thS_le V _ q.out).trans (absTheta_mono V (hMb z₀ hz₀ε) q.out)
  have hbound : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      ‖descend (GQ V) (thS V (dF f z)) q‖ ≤ (descend (GQ V) (absTheta V M) q).toReal / r := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    have hs' : Summable fun ξ => ‖dF f z (invPt V q.out ξ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb z hz _) (hs.div_const r)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS] at *
    calc ‖∑' ξ, dF f z (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖dF f z (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ / r := hs'.tsum_le_tsum (fun ξ => hcb z hz _) (hs.div_const r)
      _ = (∑' ξ, ‖M (invPt V q.out ξ)‖) / r := tsum_div_const
      _ = _ := by rw [htsM q hq]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ hr0) (Eventually.mono (hU.mem_nhds hz₀) fun z hz => hf.meas z hz)
    hint0 hmeas' hbound ((integrable_absTheta_toReal V ν hMc hMfin).div_const r) hdiff).2

theorem fam_dF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) : Fam V ν U (dF f) := by
  refine { diff := fun x => (hf.diff x).deriv hU, maj := ?_, meas := ?_ }
  · intro z₀ hz₀
    obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
    refine ⟨ε / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball, ((2 / ε : ℝ) : ℂ) • M,
      hMc.const_smul _, absThetaInt_smul_lt V ν _ hMfin, ?_⟩
    intro z hz x
    have hsub : Metric.closedBall z (ε / 2) ⊆ U := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : ∀ w ∈ Metric.sphere z (ε / 2), w ∈ Metric.ball z₀ ε := by
      intro w hw
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_sphere] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have h := cauchy_le (hf.diff x) (by positivity : (0 : ℝ) < ε / 2) hsub fun w hw => hMb w (hmem w hw) x
    calc ‖dF f z x‖ ≤ ‖M x‖ / (ε / 2) := h
      _ = ‖(((2 / ε : ℝ) : ℂ) • M) x‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
  · exact fun z hz => (fam_hasDeriv V ν hU hf hz).1

theorem fam_iF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) : Fam V ν U (iF f r) := by
  induction r with
  | zero => rwa [iF_zero]
  | succ r ih => rw [iF_succ]; exact fam_dF V ν hU ih

theorem iteratedDeriv_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) :
    ∀ z ∈ U, iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) z =
      ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν := by
  have hder : ∀ r, ∀ z ∈ U, HasDerivAt (fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν)
      (⨍ q, descend (GQ V) (thS V (iF f (r + 1) z)) q ∂autMeasure V ν) z := by
    intro r z hz
    simp only [average_eq]
    rw [iF_succ]
    exact (fam_hasDeriv V ν hU (fam_iF V ν hU hf r) hz).2.const_smul _
  induction r with
  | zero => intro z _; simp [iF_zero]
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) =ᶠ[𝓝 z]
        fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν :=
      Eventually.mono (hU.mem_nhds hz) fun w hw => ih w hw
    rw [heq.deriv_eq]
    exact (hder r z hz).deriv

theorem differentiableOn_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) :
    DifferentiableOn ℂ (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) U := by
  intro z hz
  simp only [average_eq]
  exact ((fam_hasDeriv V ν hU hf hz).2.const_smul _).differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussP
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

theorem pLaw (hN : LawN) (hMul : LocMul) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) {e : ℤ}
    (hLev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hG : IsSch (gZf ε (tLoc l τ) (cLoc l τ) Z)) :
    L q (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) q Z *
      gZf ε (tLoc l τ) (cLoc l τ) (actZ q Z) u := by
  obtain ⟨hA, hDd, hb⟩ := siegelP_data q hq
  have hAh : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  set q1 := mkGR (nU ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)) (by rw [det_nU]; exact one_ne_zero) (inG_nU hb)
  set q2 := mkGR (mM (mR q).toBlocks₁₁) (det_mM hA) (inG_mM hA)
  have hq12 : q = q1 * q2 := by
    apply GR_ext
    rw [mR_mul, mR_mkGR, mR_mkGR]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q), hq, hDd]
    unfold nU mM
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAh]
  have h2 := hLev q2 (mR q).toBlocks₁₁ hA (mR_mkGR _ _ _) _ hG
  have hs2 : IsSch (levF e (mR q).toBlocks₁₁ (gZf ε (tLoc l τ) (cLoc l τ) Z)) := by rw [← h2]; exact hL.1 q2 _ hG
  have h1 := hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 _ hb (mR_mkGR _ _ _) _ hs2
  have hm := hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 q2 _ hG
  rw [hq12, hm, h2, h1, ← hq12]
  funext u
  simp only [levF, gZf_mul]
  rw [siegelP_actZ q hq Z, siegelP_jF q hq, cnt_add, ← chN_mul_gZf ε (abs_tLoc l τ) _ _ hb u]
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem g_ext {n : ℕ} {g h : G D n} (e : mat g = mat h) : g = h := by
  unfold mat at e
  exact Subtype.ext (Units.ext e)

theorem exists_slice {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (x0 : Mx D m n)
    (z : Matrix (Fin m) (Fin n) ℂ) : ∃ x : Mx D m n, compAt θ τ x = z ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x0) ∧ x.map (finPart D) = x0.map (finPart D) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.AdForm.RatMove.realPt_spec hθ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0)
  refine ⟨x0 + GlobalTheory.AdForm.realPt θ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0), ?_, ?_, ?_⟩
  · rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp
  · intro τ' h
    rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp [h]
  · rw [Matrix.map_add _ (map_add (finPart D)), h1, add_zero]

theorem tens_at {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) (x : Mx D m n) (u : Matrix (Fin m) (Fin n) ℂ)
    (hx : compAt θ τ x = fr * u) : tens θ τ fr f Ψ x = f u * Ψ x := by
  simp only [tens, hx, Matrix.nonsing_inv_mul_cancel_left _ _ hfr]

theorem awayCls_zero {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    AwayCls θ τ fr (0 : Mx D m n → ℂ) := by
  refine ⟨fun _ _ _ _ => rfl, fun f _ => ?_⟩
  have : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
    funext x
    simp [tens]
  rw [this]
  exact zero_mem _

theorem exists_nU (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : ∃ y : GR n, mR y = nU b := by
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨nU b, nU (-b), by simp [nU, Matrix.fromBlocks_multiply], by simp [nU, Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ GR n := by
    show InG (nU b)
    simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
    simp
  exact ⟨⟨u, hu⟩, rfl⟩

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem finite_part_block_matrix {n : ℕ} (a b c d : Mx D n n) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem neg_block_matrix {R : Type} [CommRing R] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_neg]
  rfl

theorem jsq {R : Type} [CommRing R] {n : ℕ} :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  rw [GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, ← GlobalTheory.StdUnn.Frame.block_matrix_one, neg_block_matrix]
  simp

theorem mat_inv_w {n : ℕ} (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat w⁻¹ = -blk4 0 1 (-1) 0 := by
  have h1 : mat w⁻¹ * mat w = 1 := by
    show mat (w⁻¹ * w) = 1
    rw [inv_mul_cancel]
    rfl
  have h2 : mat w * (-mat w) = 1 := by rw [mul_neg, hw, jsq, neg_neg]
  calc mat w⁻¹ = mat w⁻¹ * (mat w * (-mat w)) := by rw [h2, mul_one]
    _ = -mat w := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [hw]

end PositivityTheory.Rg.Sw.Glob.OG
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiEqOfFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR thetaC eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

variable {D : D7}


set_option synthInstance.maxHeartbeats 400000 in
theorem incl_trA (z : AE D) : algebraMap (AF D.host.F) (AE D) (trA z) = z + cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [trA]
  | tmul a e =>
    simp only [trA]
    rw [GlobalTheory.SplitAdeleTrace.trace_baseChange_tmul (AF D.host.F) a e]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h : (Algebra.trace D.host.F D.host.E e : D.host.E) = e + star e := GlobalTheory.TraceAddStar.trace_eq_add_star e
    calc (a * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)) ⊗ₜ[D.host.F] (1 : D.host.E)
        = a ⊗ₜ[D.host.F] ((Algebra.trace D.host.F D.host.E e : D.host.F) : D.host.E) := by
          rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]; rfl
      _ = a ⊗ₜ[D.host.F] e + cA D (a ⊗ₜ[D.host.F] e) := by
          rw [h, TensorProduct.tmul_add]; rfl
  | add x y hx hy =>
    simp only [trA, map_add (f := _)] at hx hy ⊢
    rw [hx, hy]; abel


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_eq_of_fin {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (a : AF D.host.F) (ha : finPart D (algebraMap (AF D.host.F) (AE D) a) = 0) :
    ψ a = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (l τ : ℂ) * psiT D τ (algebraMap (AF D.host.F) (AE D) a)) := by
  have hsnd : sndA D.host.F a = 0 := by
    apply Algebra.TensorProduct.includeLeft_injective (S := Af D.host.F) (algebraMap D.host.F D.host.E).injective
    rw [map_zero]
    exact ha
  have ha' : a = pairA D.host.F (fstA D.host.F a) 0 := Prod.ext rfl hsnd
  have h1 : ψ a = psiInf D.host.F ψ (fstA D.host.F a) := by
    conv_lhs => rw [ha']
    rfl
  rw [h1, hl, eq_thetaC D hθ]
  rfl


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_trA_tau {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {l : D.what₂.Tau → ℝ}
    (hl : HasRealPar ψ θ l) (τ : D.what₂.Tau) (z : AE D) (hz : ∀ τ', τ' ≠ τ → psiT D τ' z = 0)
    (hzf : finPart D z = 0) :
    ψ (trA z) = Complex.exp (Complex.I * ((4 * Real.pi * l τ : ℝ) : ℂ) * ((psiT D τ z).re : ℂ)) := by
  have hfin : finPart D (algebraMap (AF D.host.F) (AE D) (trA z)) = 0 := by
    rw [incl_trA, RingHom.map_add (f := _), hzf, cA, Formalism.IndefR.Eqv.finPart_sigR, hzf, RingHom.map_zero, add_zero]
  rw [psi_eq_of_fin hθ hl _ hfin, incl_trA]
  have hs : ∑ τ', (l τ' : ℂ) * psiT D τ' (z + cA D z) = (l τ : ℂ) * (2 * ((psiT D τ z).re : ℂ)) := by
    rw [Finset.sum_eq_single τ]
    · rw [RingHom.map_add (f := _), cA, psiT_sigR, Complex.add_conj]; push_cast; ring
    · intro τ' _ hne
      rw [RingHom.map_add (f := _), cA, psiT_sigR, hz τ' hne, map_zero, add_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h
  rw [hs]
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

