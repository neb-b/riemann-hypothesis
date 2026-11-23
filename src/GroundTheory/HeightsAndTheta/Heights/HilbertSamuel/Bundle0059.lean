module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnRes P J e)

theorem ram_null' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_brQ R Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_brQ_chart R Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (R.mem x0 x0 (R.mem_U x0))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.lift x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.lift x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_brQ R Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (brQ R Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, brQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.lift ((R.A.chart j).symm w) ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end FibreNormCharpoly

namespace ProjLine

open ProjLine

end ProjLine

namespace FibreNormCharpoly

open ProjLine

end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ArithmeticVolumeDimensionOne.proof (hG6 : ArithmeticVolumeBigDimensionOne.Statement) : ArithmeticVolumeDimensionOne.Statement := by
  intro K _ ι _ Ω _ _ y M P0 II hII har hb hM hpos
  set T := II K ι (mCoordIdeal y) 1 (fun _ => M)
  set g := geomDeg (mCoordIdeal y) M 0
  have hden : 0 < 2 * (|g| + 1) := by positivity
  set η := T / (2 * (|g| + 1))
  have hη0 : 0 < η := div_pos hpos hden
  have he : η * (2 * (|g| + 1)) = T := div_mul_cancel₀ T hden.ne'
  have hηlt : η * g < T := by
    have h1 : η * g ≤ η * |g| := mul_le_mul_of_nonneg_left (le_abs_self g) hη0.le
    nlinarith
  have hshift := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) 0 M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) := by
    have e : II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) = T - ((0 : ℕ) + 1 : ℝ) * η * g :=
      hshift
    rw [e]
    push_cast
    linarith
  have hvol := hG6 K ι Ω y (HermLine.constShift M η) P0 II hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g' h z hg hh hdeg heq hz
    have hle := hsmall dg dh g' h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1GenAmple.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsMultiHomogIdeal V → H1GenAmple S V N →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → KH.GeneratedV S V (e + c • N)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KleimanVarietyH1Generation.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (Q : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiProjPrime Q → KH.NefOnF I Q α → 1 ≤ b → 1 ≤ a →
    H1GenAmple F Q (b • α + fun _ => (a : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

theorem TensorPowerL2Degree.proof (hDat : PowerBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hChi : BlockChiCovolume.Statement) (hHS : TheoremHSMBlock.Statement) : TensorPowerL2Degree.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD1 hII har hb hA hc
  classical
  obtain ⟨m, N, v, d, μ, hm, hdy, hk, hv, hgen, hmet, hlat, hμ, hnull, hZ, hnorm⟩ :=
    hDat K ι Ω y D A P0 hD1 har hb hA hc
  have htop : II (Option K) (addIdx ι N) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) := by
    rw [hdy]
    refine hTop K ι Ω y D A m N v d.A II hII har hA.semipos.1 hm hv hgen (by rw [d.deg, hk]) d.semipos.1 ?_
    rw [← hdy]
    exact hmet
  obtain ⟨hdef, -⟩ := hHS D (Option K) (addIdx ι N) Ω II d hII
  refine ⟨μ, m, hμ, hnull, hZ, hm, fun ε hε => ?_⟩
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast hm) _
  have hc' : 0 < ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hdef.bound hc', hlat] with q hq hl
  intro r ψ hψ hiso _ _
  have hcov := hChi D (Option K) (addIdx ι N) Ω d q (chartLat y A.a (m * q)) (by rw [hk]; exact hl) r ψ hψ
    (fun s f hf hs => by
      rw [hk] at hf
      rw [hiso, ← hs]
      exact hnorm q f hf)
  rw [hcov]
  rw [htop] at hq
  simp only [hsDefect, pw, Real.norm_eq_abs] at hq
  have hq' := (abs_le.mp hq).2
  rw [abs_of_nonneg (by positivity)] at hq'
  push_cast
  rw [mul_pow]
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
      ((m : ℝ) ^ (D + 1) * (q : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      (m : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => A) * (q : ℝ) ^ (D + 1) /
          ((D + 1).factorial : ℝ) +
        ε * (m : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) * (q : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenerationOfH1Vanishing.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1GenerationDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S → (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → H1GenAmple S P N) →
    H1GenAmple S V N

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1VanishingDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι (KH.quotPart S P) (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem CovolumeLeGram.proof : CovolumeLeGram.Statement := by
  intro n L _ _ ι _ _ x hxL hx hcard
  have hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hcard, finrank_euclideanSpace_fin]
  let B : Basis ι ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank' x hx hcard'
  have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hML : Submodule.span ℤ (Set.range B) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)
  have hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]
    congr 3
    funext i
    simp [Basis.restrictScalars_apply, hB]
  have hdiv := ZLattice.covolume_div_covolume_eq_relIndex' _ L hML
  have hposM := ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))
  have hposL := ZLattice.covolume_pos L
  have hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hdiv
    exact (div_pos hposM hposL).ne' hdiv
  have h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L := by
    rw [hdiv]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  rw [← hcovM]
  rwa [le_div_iff₀ hposL, one_mul] at h1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

