module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagFix

open Formalism.QuantumDeterminants

theorem wedge_eq_of_mul {n l : ℕ} (f f' : Fin l → Fin n → ℂ) (U : Matrix (Fin l) (Fin l) ℂ)
    (hU0 : ∀ c a, a < c → U c a = 0) (hU1 : ∀ c, U c c = 1)
    (h : ∀ i a, f' a i = ∑ c, f c i * U c a) : wedge f' = wedge f := by
  have dU : U.det = 1 := by
    have ht : U.IsUpperTriangular := fun i j hij => hU0 i j hij
    rw [det_of_isUpperTriangular ht]
    exact Finset.prod_eq_one (fun i _ => hU1 i)
  funext I
  have e : (Matrix.of fun a b : Fin l => f' b (I.1.orderEmbOfFin I.2 a)) =
      (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a)) * U := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, h]
  simp only [wedge]
  rw [e, det_mul, dU, mul_one]

theorem flat_eq (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : flat k r f = star f ᵥ* Hpk k r := by
  funext c
  simp only [flat, herm]
  rw [dotProduct_mulVec, dotProduct_single, mul_one]

theorem dual_fix (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : sᴴ * Hpk k r * s = Hpk k r)
    (hf : s *ᵥ f = f) : dualM s *ᵥ flat k r f = flat k r f := by
  have h2 : Hpk k r * Hpk k r = 1 := (hermitian_pos_facts_hold k r).2.1
  have hl : (Hpk k r * sᴴ * Hpk k r) * s = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc sᴴ, hs, h2]
  rw [flat_eq, dualM, mulVec_transpose, Matrix.inv_eq_left_inv hl, vecMul_vecMul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, ← vecMul_vecMul, ← star_mulVec, hf]

theorem fixes_wedge_and_form : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z,
      cmp (r + 1) s *ᵥ (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (wedge (Formalism.QuantumDeterminants.fvec k r z)) ∧
      dualM s *ᵥ (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) = (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) := by
  intro k r z hz s hs
  obtain ⟨U, hU0, hU1, hF⟩ := S_F hz hs
  have key : ∀ i a, (s *ᵥ fvec k r z a) i = ∑ c, fvec k r z c i * U c a := by
    intro i a
    have := congrFun (congrFun hF i) a
    simpa [Matrix.mul_apply, Fm, mulVec, dotProduct] using this
  refine ⟨?_, dual_fix k r _ s (Sset_UH hs) ?_⟩
  · rw [(_root_.GlobalTheory.compound_properties _ (r + 1) s s).2.2.2]
    exact wedge_eq_of_mul _ _ U hU0 hU1 key
  · funext i
    rw [key, Finset.sum_eq_single 0, hU1, mul_one]
    · intro c _ hc
      rw [hU0 c 0 (Fin.pos_of_ne_zero hc), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.FlagFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlowProgrammeBoundsAndLowLevelOptimum
section
open Formalism.IncomingBounds

namespace GlobalTheory.FlowProgrammeFacts

variable {l d : ℕ} [NeZero d]

lemma succ_mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ}
    (hx : IsFlow l d D x) : ((l : ℝ) + 1) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) * flowVal d x ≤ ∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    unfold flowVal
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  have h2 : ∑ a : ZMod d, ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i = flowVal d x := by
    unfold flowVal
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)
  have h3 := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hx.2 a
  rw [Finset.sum_add_distrib, h2] at h3
  linarith

lemma rho_mul_le_Fnum (hl : 2 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hp : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hm : maxFlow l d D ≤ (∑ a, D a) / ((l : ℝ) + 1) :=
    GlobalTheory.FlowScaling.maxFlow_le hD fun x hx => by
      rw [le_div_iff₀ hp, mul_comm]
      exact succ_mul_flowVal_le (by omega) hx
  have hq : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have e : Formalism.IncomingBounds.gam l * ∑ a, D a - (∑ a, D a) / ((l : ℝ) + 1)
      = Formalism.IncomingBounds.rho l * ∑ a, D a := by
    unfold Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho
    field_simp
    ring
  unfold Fnum
  linarith

theorem main : ∀ (l d : ℕ) [NeZero d] (D : ZMod d → ℝ), 2 ≤ l → (∀ a, 0 ≤ D a) →
    Formalism.IncomingBounds.rho l * ∑ a, D a ≤ Fnum l d D ∧
    (∀ t : ℝ, 0 ≤ t → Fnum l d (fun a => t * D a) = t * Fnum l d D) ∧
    Formalism.BasicNotions.lpF l d D = Fnum l d D ∧
    ∀ i₀ : ℕ, ∃ x : ZMod d → ℕ → ℝ, IsFlow l d D x ∧ (∀ a i, i₀ ≤ i → x a i = 0) ∧
      Formalism.IncomingBounds.gam l * ∑ a, D a - flowVal d x ≤
        Fnum l d D + ((l : ℝ) ^ i₀)⁻¹ * ∑ a, D a := by
  intro l d _ D hl hD
  refine ⟨rho_mul_le_Fnum hl hD, fun t ht => ?_, GlobalTheory.LevelsOrbits.lpF_eq l d D, fun i₀ => ?_⟩
  · unfold Fnum
    rw [GlobalTheory.FlowScaling.maxFlow_mul (by omega) ht hD, ← Finset.mul_sum]
    ring
  · obtain ⟨x, ⟨hx, hx0⟩, hmax⟩ := GlobalTheory.BasicFlow.low_optimum l d hl D hD i₀
    have hm : maxFlow l d D ≤ flowVal d x + (∑ a, D a) / (l : ℝ) ^ i₀ :=
      GlobalTheory.FlowScaling.maxFlow_le hD fun z hz => by
        obtain ⟨z', h1, h2, h3⟩ := GlobalTheory.BasicFlow.truncate l d hl D i₀ z hz
        linarith [hmax z' h1 h2]
    refine ⟨x, hx, fun a i h => hx0 a i (Or.inl h), ?_⟩
    rw [div_eq_inv_mul] at hm
    unfold Fnum
    linarith

end GlobalTheory.FlowProgrammeFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.gN_rpow_neg_integrable_haar : _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG
  intro k r μG A hμ hA
  have hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG :=
    (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ
  have hvol := _root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
  unfold _root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol
  obtain ⟨C, hC⟩ := hvol k r μG hW
  have hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := by
    unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hμ
    exact ae_iff.2 hμ.2.2.1
  set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef
  have hNcont : Continuous N := by
    simp only [hNdef]
    unfold _root_.Formalism.FourierDecayAlt.B.gN
    fun_prop
  have hNm : Measurable N := hNcont.measurable
  have h1 : ∀ᵐ x ∂μG, 1 ≤ N x := hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1) := by positivity
  have hAd : 2 * ((k:ℝ) + r) * (r + 1) < A := by
    have : _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring
    rw [this] at hA
    linarith
  set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := (2:ℝ) ^ (d - A) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)} := fun n ↦
    measurableSet_le hNm measurable_const
  have hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)}
      ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d) := by
    intro n
    refine (hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d)
      = C' * 2 ^ d * q ^ n := by
    intro n
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq,
      ← Real.rpow_mul_natCast (by norm_num)]
    have e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)
        = 2 ^ d * 2 ^ ((d - A) * n) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc ((2:ℝ) ^ ((n:ℝ) * -A)) * (C' * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d))
        = C' * ((2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)) := by ring
      _ = C' * 2 ^ d * 2 ^ ((d - A) * n) := by rw [e]; ring
  have hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ,
      {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))
  refine ⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖_root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)‖ₑ ∂μG
      = ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μG := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.enorm_eq_ofReal
          (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]
    _ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator
          (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← hkey n, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hvolS n
    _ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselDegree

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem isDS_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    PI.UpqRep.IsDS ε lam σ ↔ Formalism.MainNotions.S.IsDS ε lam σ := Iff.rfl

theorem haar_eq_smul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r} (hP : IsUnit P.det)
    (hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hν : PI.BesselPeriodGGP.IsHaarOn (GG k r) ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (Formalism.REAL.muG ε).map (phi ε P) := by
  have hE := Formalism.REAL.isClosedEmbeddingMatrix
  have hC := Formalism.QuantumDeterminants.uHConj
  obtain ⟨hσ, h0, hconc, hleft⟩ := hν
  have hm := phi_measurable (ε := ε) hE hP
  have hce := phi_closedEmbedding (ε := ε) hE hP
  have hme : MeasurableEmbedding (phi ε P) := hce.measurableEmbedding
  have hr := phi_range hE hC hP hH
  have h2 : (ν.comap (phi ε P)).map (phi ε P) = ν := by
    rw [hme.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hr]
    exact hconc
  have hsf : SigmaFinite (ν.comap (phi ε P)) :=
    SigmaFinite.of_map _ hm.aemeasurable (by rw [h2]; exact hσ)
  have hinv : (ν.comap (phi ε P)).IsMulLeftInvariant := ⟨fun u => by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul u) hs, hme.comap_apply, hme.comap_apply]
    have hu : Matrix.of (phi ε P u) ∈ GG k r := (phi_range_iff hE hC hP hH _).1 ⟨u, rfl⟩
    have h1 := hleft _ hu
    have hs' : MeasurableSet (phi ε P '' s) := hme.measurableSet_image.2 hs
    conv_rhs => rw [← h1, Measure.map_apply (lmul_cont _).measurable hs']
    congr 1
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨u * w, hw, (lmul_phi hP u w).symm⟩
    · rintro ⟨v, hv, hx⟩
      refine ⟨u⁻¹ * v, by simpa using hv, ?_⟩
      have h2 : Formalism.QuantumDeterminants.lmulM (phi ε P u⁻¹) (Formalism.QuantumDeterminants.lmulM (phi ε P u) x) = x := by
        have h3 : (Matrix.of (phi ε P u⁻¹) : Mx k r) * Matrix.of (phi ε P u) = 1 := by
          have := lmul_phi hP u⁻¹ u
          rw [inv_mul_cancel] at this
          refine Eq.trans this ?_
          show P⁻¹ * (1 : Mx k r) * P = 1
          rw [Matrix.mul_one, Matrix.nonsing_inv_mul P hP]
        show (Matrix.of (phi ε P u⁻¹) : Mx k r) * (Matrix.of (phi ε P u) * Matrix.of x) = Matrix.of x
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
      rw [← lmul_phi hP, hx]; exact h2⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have e1 := Measure.haarMeasure_unique (ν.comap (phi ε P)) K
  have e2 := Measure.haarMeasure_unique (Formalism.REAL.muG ε) K
  have hb0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hbt : Formalism.REAL.muG ε K ≠ ∞ := K.isCompact.measure_lt_top.ne
  set a := (ν.comap (phi ε P)) K with ha
  set b := Formalism.REAL.muG ε K with hb
  have e3 : ν.comap (phi ε P) = (a / b) • Formalism.REAL.muG ε := by
    rw [e1, e2, smul_smul, ENNReal.div_mul_cancel hb0 hbt]
  have hc0 : a / b ≠ 0 := by
    intro h
    rw [h, zero_smul] at e3
    rw [e3, Measure.map_zero] at h2
    exact h0 h2.symm
  have hct : a / b ≠ ∞ := by
    intro h
    have hz : ∀ i, Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) = 0 := by
      intro i
      have h4 := measure_spanningSets_lt_top (ν.comap (phi ε P)) i
      have h5 : (ν.comap (phi ε P)) (spanningSets (ν.comap (phi ε P)) i) =
          ∞ * Formalism.REAL.muG ε (spanningSets (ν.comap (phi ε P)) i) := by
        have := congrArg (fun m : Measure (Formalism.REAL.UJ ε) => m (spanningSets (ν.comap (phi ε P)) i)) e3
        simpa only [h, Measure.smul_apply, smul_eq_mul] using this
      by_contra hne
      rw [h5, ENNReal.top_mul hne] at h4
      exact lt_irrefl _ h4
    have h6 := measure_iUnion_null hz
    rw [iUnion_spanningSets] at h6
    exact hb0 (measure_mono_null (Set.subset_univ _) h6)
  refine ⟨a / b, hc0, hct, ?_⟩
  rw [← Measure.map_smul, ← e3, h2]
  exact hm.aemeasurable

theorem schur_fdeg : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧ ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : GlobalTheory.FormalDegree.HarishChandra := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := haar_eq_smul hP hH μG hμ
  obtain ⟨c, hc, hF⟩ := hHC.chamber _ ε
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (phi ε Q) :=
    (phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (isDS_iff _ _ _).1 ((GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hR Q hQ)
  obtain ⟨hd, hS⟩ := hF mu hR.1 R.H _ hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

end GlobalTheory.BesselDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_dual_standard_unitaryRep : ∀ (k r : ℕ), IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  first | exact @GlobalTheory.isFRep_dualM | exact GlobalTheory.isFRep_dualM | (intros; apply GlobalTheory.isFRep_dualM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeFRep

theorem entry_le_hs {k r : ℕ} (g : Mx k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem isFRep_cmp (k r l : ℕ) :
    IsFRep (k := k) (r := r) (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) l := by
  have hm : ∀ g h : Mx k r, cmp l (g * h) = cmp l g * cmp l h := fun g h => (_root_.GlobalTheory.compound_properties _ l g h).1
  have hc : ∀ g : Mx k r, cmp l gᴴ = (cmp l g)ᴴ := fun g => (_root_.GlobalTheory.compound_properties _ l g g).2.1
  have h1 : cmp l (1 : Mx k r) = 1 := (_root_.GlobalTheory.compound_properties _ l 1 1).2.2.1
  refine ⟨?_, ?_, h1, fun g _ h _ => hm g h, ?_, ?_, ⟨(l.factorial : ℝ), ?_⟩, ?_⟩
  · rw [← hc, PI.StabPairsW.hpk_conjTranspose]
  · rw [← hm, PI.StabPairsW.hpk_mul_self, h1]
  · intro g hg
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    rw [← hc, ← hm, ← hm, hg']
  · intro I J
    apply Continuous.continuousOn
    unfold BranchingSupport.cmp
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · intro g _ I J
    have := Matrix.det_le (A := g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2))
      (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (x := B.gN g) (fun i j => entry_le_hs g _ _)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  · intro g _ hu
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← hc, ← hm, hu, h1]

end GlobalTheory.WedgeFRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLeStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_integral_inner_weight_le : ∀ (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ), AEStronglyMeasurable f ν → AEStronglyMeasurable g ν → AEStronglyMeasurable ph ν → ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤ (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  first | exact @GlobalTheory.norm_sq_integral_inner_smul_le | exact GlobalTheory.norm_sq_integral_inner_smul_le | (intros; apply GlobalTheory.norm_sq_integral_inner_smul_le <;> assumption)
end

