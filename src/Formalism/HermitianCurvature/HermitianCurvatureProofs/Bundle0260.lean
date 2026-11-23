module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0259
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0250
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusPosOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGRadProper
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0148
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0247
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0253

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSmooth
section
noncomputable section

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

open Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lemmas

variable {k : ℕ}

theorem contDiff_castM {a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact contDiff_id

theorem ms_mMap {r : ℕ} (q₀ : (Fin r → Fin r → ℂ) × Mt k (r - r)) (h₀ : (Matrix.of q₀.1).det ≠ 0) :
    MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ := by
  have hZ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.1) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_fst
  have hμ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.2) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_snd
  have hZi : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr h₀)
  unfold U.mMap
  exact Formalism.FourierDecayAlt.P.PBI.measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
    (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)

theorem contDiffOn_xT (r : ℕ) :
    ContDiffOn ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => xT k r (Matrix.of q.1) (Matrix.of q.2))
      {q | (Matrix.of q.1).det ≠ 0} := by
  intro q₀ h₀
  have hm := ms_mMap q₀ h₀
  have hc : ContDiffAt ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hm i l
  exact ((contDiff_castM (k := k) (by omega : r + (r - r) = r)).contDiffAt.comp q₀ hc).contDiffWithinAt

theorem dmin_xT (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) :
    Dmin k r z z' (xT k r Z μ) ⟨r, by omega⟩ = Z.det := by
  unfold xT
  rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM (by omega) z z' _ r (by omega) (by omega),
    Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r (r - r)]
  have e := Formalism.FourierDecayAlt.P.hat_z_on_slice k r (r - r) 0 0 Z μ
  rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
  unfold U.DjU
  rw [e]

theorem xT_GV (r : ℕ) {Z : Matrix (Fin r) (Fin r) ℂ} {μ : B.Mat k (r - r)} (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k (r - r)) :
    xT k r Z μ ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV _ ((Formalism.FourierDecayAlt.P.slice_membership k r (r - r)).1 Z μ hZ hμ)

theorem gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem inWb_castV {a b : ℕ} (e : a = b) {z : Fin (2 * a + k + 1) → ℂ} (h : inWb k a z) : inWb k b (D.castV e z) := by
  subst e
  rwa [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

end lemmas

theorem pullback_smooth_formula : PbSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p G hG q₀ hq₀ hG₀
  obtain ⟨⟨hsm, ⟨R, hR⟩, -⟩, -⟩ := hG
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hHC : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → G g = 0 := by
    intro g hg hn
    by_contra hne
    exact hn (hR g hg hne)
  have hΩ := PBQ.isOpen_domP P.k P.r P.r p.T.base.z p.T.base.z'
  have hP := proper_left_variables_domain Wp Wq P p P.r le_rfl _ hCs
  have hG₀' : Matrix.of q₀.2 ∈ B.GV P.k (P.r - P.r) := hG₀.1
  have hgf : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2)) := by
    unfold xT
    rw [gf_castM]
    have e := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r)
      (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z) (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z')
      (inWb_castV _ p.T.base.z_mem) (inWb_castV _ p.T.base.z'_mem) 0 0 (Matrix.of q₀.1) (Matrix.of q₀.2)
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
    rw [e, MkCptPf.lowV_top p.T _, MkCptPf.lowV_top' p.T _, MkCptPf.gf_eq_ggl (by omega)]
    exact mul_pos (Complex.normSq_pos.2 hq₀.1) hq₀.2
  have hyΩ : xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2) ∈ PBQ.domP P.k P.r P.r p.T.base.z p.T.base.z' := by
    refine ⟨fun l hl1 hl2 => ?_, hgf⟩
    have hl : l = ⟨P.r, by omega⟩ := Fin.ext (by show (l : ℕ) = P.r; omega)
    rw [hl, dmin_xT]; exact hq₀.1
  have hyG := xT_GV P.r hq₀.1 hG₀'
  have hz : p.T.base.z = D.castV (by omega : P.r + (P.r - P.r) = P.r) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) :=
    (p.T.z_lev P.r le_rfl).symm
  obtain ⟨V, f', hV, hyV, hf', hag⟩ := partial_bessel_smooth_compact_support P.k P.r (P.r - P.r) P.r Wp Wq (p.T.bs P.r) p.T.base
    (by omega) hz G _ hsm hCs hHC _ hΩ hP _ hyΩ hyG
  have hxc := contDiffOn_xT (k := P.k) P.r
  have hOD : IsOpen {q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (continuous_fst)) continuous_const
  refine ⟨{q | (Matrix.of q.1).det ≠ 0} ∩
      (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)) ⁻¹' V,
    fun q => f' (xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)), hxc.continuousOn.isOpen_inter_preimage hOD hV,
    ⟨hq₀.1, hyV⟩, hf'.comp (hxc.mono Set.inter_subset_left) (fun q hq => hq.2), fun q hq hqG => ?_⟩
  exact hag _ hq.2 (xT_GV P.r hq.1 hqG.1)

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem pullback_smooth : CutEX.PbSmooth := CutEX.pullback_smooth_formula

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

theorem hpk_zero (k : ℕ) : Hpk k 0 = diagonal (dS (2 * 0 + k)) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, diagonal_apply, dS, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tz_sum (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i : Fin (2 * 0 + k), ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last _)‖ ^ 2 - Tz k 0 z := by
  have e : ∀ w : ℂ, (starRingEnd ℂ w * w).re = ‖w‖ ^ 2 := by
    intro w
    rw [Complex.conj_mul']
    norm_cast
  unfold Tz herm
  rw [hpk_zero]
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_castSucc, Pi.star_apply, Complex.star_def]
  have h1 : ∀ i : Fin (2 * 0 + k), dS (2 * 0 + k) i.castSucc = 1 := fun i => by
    unfold dS
    rw [if_neg (Fin.castSucc_lt_last i).ne]
  have h2 : dS (2 * 0 + k) (Fin.last (2 * 0 + k)) = -1 := by
    unfold dS
    rw [if_pos rfl]
  simp only [h1, h2, one_mul, neg_one_mul, mul_neg, Complex.add_re, Complex.neg_re, Complex.re_sum, e]
  ring

theorem gf_eq_GGl (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  unfold Gf Q.GGl Dmin
  rw [Matrix.det_fin_zero, Matrix.det_fin_one]
  simp only [Complex.normSq_one, mul_one]
  rfl

theorem mu_bound (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (hT : 0 < Tz k ρ z) (hT' : 0 < Tz k ρ z')
    (μ : B.Mat k ρ) (hμ : μ ∈ Q.Glev k ρ (Fin.last ρ)) (i j : Fin (2 * ρ + k + 1)) :
    ‖μ i j‖ * (Tz k ρ z * Tz k ρ z') ≤ 4 * ‖z ⟨2 * ρ + k, by omega⟩‖ * ‖z' ⟨2 * ρ + k, by omega⟩‖ *
      ‖Q.zetaL k ρ z z' (Fin.last ρ) μ‖ := by
  subst hρ
  have hU : μᴴ * diagonal (dS (2 * 0 + k)) * μ = diagonal (dS (2 * 0 + k)) := by
    have h := hμ.1
    rw [hpk_zero] at h
    exact h
  have hζ : Q.zetaL k 0 z z' (Fin.last 0) μ = star z ⬝ᵥ (diagonal (dS (2 * 0 + k)) *ᵥ (μ *ᵥ z')) := by
    unfold Q.zetaL herm
    rw [hpk_zero]
    simp [fvec]
  rw [hζ]
  exact entry_bound μ hU z z' _ _ hT hT' (tz_sum k z) (tz_sum k z') i j

end Formalism.FourierDecayAlt.P.CutEXPbSupp

namespace Formalism.FourierDecayAlt.P

open CutEX CutEXPbSupp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem pullback_support : CutEX.PbSupp := by
  intro Wp Wq _ _ _ _ _ _ P p G hG
  obtain ⟨⟨_, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, K0, hK0c, h0K0, hK0⟩ := hG

  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K0, δ ≤ ‖w‖ := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK0c.isClosed.isOpen_compl 0 h0K0
    refine ⟨δ, hδ, fun w hw => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hw

  obtain ⟨M1, hM1⟩ := hK0c.isBounded.exists_norm_le
  set M0 : ℝ := max M1 1 with hM0
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)

  set SR : Set (B.Mat P.k P.r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
    with hSRdef
  have hSR : IsCompact SR := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨Cg, hCg⟩ := hSR.exists_bound_of_continuousOn
    (f := fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g)
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous.continuousOn

  set zr := (p.T.bs P.r).z with hzr
  set zr' := (p.T.bs P.r).z' with hzr'
  have hT : 0 < Tz P.k (P.r - P.r) zr := (p.T.bs P.r).T_pos
  have hT' : 0 < Tz P.k (P.r - P.r) zr' := (p.T.bs P.r).T'_pos
  set TT : ℝ := Tz P.k (P.r - P.r) zr * Tz P.k (P.r - P.r) zr' with hTT
  have hTTpos : 0 < TT := mul_pos hT hT'
  set Zb : ℝ := Real.sqrt (Cg / δ ^ 2 + TT) with hZb
  set Bμ : ℝ := 4 * ‖zr ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * ‖zr' ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * Zb / TT
    with hBμ
  set c : ℝ := ε / M0 ^ 2 with hc
  have hcpos : 0 < c := div_pos hε (by positivity)
  set Bset : Set (Mt P.k (P.r - P.r)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) Bμ with hBset
  set Aset : Set (Fin P.r → Fin P.r → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hAset
  have hA : IsCompact Aset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hB : IsCompact Bset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨(Aset ×ˢ Bset) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) ⁻¹' K0) ∩
      ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.2 : B.Mat P.k (P.r - P.r))) ⁻¹'
        Q.Glev P.k (P.r - P.r) (Fin.last _)) ∩
      {q | c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)}, ?_, ?_, ?_⟩
  · refine (((hA.prod hB).inter_right ?_).inter_right ?_).inter_right ?_
    · exact hK0c.isClosed.preimage (Continuous.matrix_det continuous_fst)
    · exact (Formalism.FourierDecayAlt.P.JCTx5.glev_closed _ _ _).preimage continuous_snd
    · exact isClosed_le continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_snd)
  · rintro q ⟨⟨⟨_, hq1⟩, _⟩, hq3⟩
    refine ⟨fun h0 => h0K0 ?_, lt_of_lt_of_le hcpos hq3⟩
    have : (Matrix.of q.1).det ∈ K0 := hq1
    rwa [h0] at this
  · intro q hdet hμ hpb
    obtain ⟨g, hg, hGg, u, hu, hb, hD, hGf⟩ := CutEXPbSupp.orbit_point p G (Matrix.of q.1) (Matrix.of q.2) hdet hμ hpb
    have hgR : B.gN g ≤ R := hR g hg hGg
    have hDK : (Matrix.of q.1).det ∈ K0 := hD ▸ hK0 g hg hGg
    have hdetδ : δ ≤ ‖(Matrix.of q.1).det‖ := hδK _ hDK
    have hdetM : ‖(Matrix.of q.1).det‖ ≤ M0 := (hM1 _ hDK).trans (le_max_left _ _)
    have hGε : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hεG g hg hGg
    have hgSR : g ∈ SR := by
      rw [hSRdef]
      exact fun a _ b _ => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (CutEXPbSupp.norm_entry_le_gN g a b).trans hgR
    have hGC : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ Cg := (le_abs_self _).trans (hCg g hgSR)
    set Gr := Gf P.k (P.r - P.r) zr zr' (Matrix.of q.2) with hGr
    have hns : Complex.normSq (Matrix.of q.1).det = ‖(Matrix.of q.1).det‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have hGr_pos : 0 < Gr := by
      by_contra hle
      push Not at hle
      have : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ 0 := by
        rw [hGf]; exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
      linarith
    have hGGl : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Gr :=
      (CutEXPbSupp.gf_eq_GGl P.k (P.r - P.r) (Nat.sub_self _) zr zr' _).symm
    have hδ2 : δ ^ 2 ≤ Complex.normSq (Matrix.of q.1).det := by
      rw [hns]; exact pow_le_pow_left₀ hδ.le hdetδ 2
    have hM2 : Complex.normSq (Matrix.of q.1).det ≤ M0 ^ 2 := by
      rw [hns]; exact pow_le_pow_left₀ (norm_nonneg _) hdetM 2
    have hGr_up : Gr ≤ Cg / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc Gr * δ ^ 2 ≤ Gr * Complex.normSq (Matrix.of q.1).det := mul_le_mul_of_nonneg_left hδ2 hGr_pos.le
        _ = Gf P.k P.r p.T.base.z p.T.base.z' g := by rw [hGf, mul_comm]
        _ ≤ Cg := hGC
    have hGr_lo : c ≤ Gr := by
      rw [hc, div_le_iff₀ (by positivity)]
      calc ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hGε
        _ = Complex.normSq (Matrix.of q.1).det * Gr := hGf
        _ ≤ M0 ^ 2 * Gr := mul_le_mul_of_nonneg_right hM2 hGr_pos.le
        _ = Gr * M0 ^ 2 := mul_comm _ _
    have hζ : ‖Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)‖ ≤ Zb := by
      rw [Complex.norm_def, hZb]
      refine Real.sqrt_le_sqrt ?_
      have e : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) =
          Complex.normSq (Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)) - TT := rfl
      linarith
    refine ⟨u, hu, ⟨⟨⟨?_, ?_⟩, hμ⟩, ?_⟩⟩
    · refine ⟨?_, ?_⟩
      · simp only [hAset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        exact fun a b => (hb a b).trans hgR
      · simp only [hBset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        intro a b
        have hm := CutEXPbSupp.mu_bound P.k (P.r - P.r) (Nat.sub_self _) zr zr' hT hT' (Matrix.of q.2) hμ a b
        rw [hBμ, le_div_iff₀ hTTpos]
        refine hm.trans ?_
        exact mul_le_mul_of_nonneg_left hζ (by positivity)
    · show (Matrix.of (Matrix.of.symm (Matrix.of q.1 * u))).det ∈ K0
      rw [Equiv.apply_symm_apply, Matrix.det_mul, Formalism.DoubleCosetMeasures.isUpUni_det ℂ hu, mul_one]
      exact hDK
    · show c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)
      rw [hGGl]; exact hGr_lo

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFinal
section
namespace Formalism.FourierDecayAlt.P.CutHL

theorem head_letter_of_minus_positive : LevelPointCoordinates.HeadLetter :=
  headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts

end Formalism.FourierDecayAlt.P.CutHL

theorem Formalism.FourierDecayAlt.P.head_letter_identity : Formalism.FourierDecayAlt.P.LevelPointCoordinates.HeadLetter := Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSMeas
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section MeasJ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapS (l : Fin r) (c : Fin r → ℂ) (q : (ℂ × Cf r l.succ) × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue l.succ (Function.update c l q.1.1) q.1.2, Matrix.of q.2)

theorem glueMapS_continuous (l : Fin r) (c : Fin r → ℂ) : Continuous (glueMapS (k := k) l c) := by
  unfold glueMapS
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun m => ?_
    by_cases h : (l.succ : Fin (r + 1)).val ≤ m.val
    · simp only [glue, h, dif_pos]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · simp only [glue, h, dif_neg, not_false_eq_true, Function.update_apply]
      by_cases hm : m = l
      · simp only [hm, eq_self_iff_true, if_true, ite_true] <;> fun_prop
      · simp only [hm, if_false, ite_false] <;> fun_prop
  · exact continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop

theorem measurableSet_glueMapS_DomR (l : Fin r) (c : Fin r → ℂ) :
    MeasurableSet (glueMapS (k := k) l c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapS_continuous l c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapS_continuous l c)).measurableSet

end MeasJ

theorem spectral_measurability : JSMeas := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' l c Φ Ψ
  have hmaps : Set.MapsTo (glueMapS (k := k) l c) (glueMapS (k := k) l c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapS_continuous l c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapS_continuous l c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapS_DomR l c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2) = 0 :=
    radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.1.1) q.1.2) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSRadLocCut
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

def FamCCUnif : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    CutSH.GoodFam T j G → ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∀ (A : ℝ) (m : ℕ),
      ∃ c : ℝ, ∀ t ∈ K, B.CCle A m (G t) c

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamGood
section
namespace Formalism.FourierDecayAlt.P

theorem slice_family_good : CutSH.SliceFamGood :=
  CutSH.cutSH_sliceFamGood_of CutSH.SFG.gram_function_induction CutSH.SFG.radial_proper
    CutSH.SFG.parameter_smooth CutSH.SFG.point_smooth

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateBound
section
theorem Formalism.FourierDecayAlt.P.germ_rate_bound : Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfBdd
section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_bdd (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (hBdd : JA.JABddOpQQ) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_hat hJ hG hat_quadratic_operator_holds hBdd

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordSmoothPartialBessel
section
namespace Formalism.FourierDecayAlt.P

theorem word_smooth_partial_bessel : CutHB.WordSmooth := PartialBesselWordSmoothness.wordSmooth_of proper_left_variables_domain

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnly
section
namespace Formalism.FourierDecayAlt.P

theorem z_only : LevelPointCoordinates.ZOnly :=
  z_only_of_levi_curve levi_curve hermitian_part_levi

end Formalism.FourierDecayAlt.P
end

