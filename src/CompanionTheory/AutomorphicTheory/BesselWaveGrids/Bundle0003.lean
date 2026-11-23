module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bridge
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0003
public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001
public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.TypeHW
public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.IsData
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive
section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

noncomputable def gridY (P : M.Par) (l N : ℕ) : Finset ℝ := progY (2 - max (P.u l) (P.u' l)) (N * (2 * P.r + 1))

noncomputable def gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : ℝ :=
  max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))))

theorem one_le_gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : 1 ≤ gridΛ P b N := by
  unfold gridΛ
  exact le_max_left _ _

theorem gridΛ_sq (P : M.Par) (b : ℝ) (N : ℕ) (hb : 0 ≤ b) (hTT : 0 < P.T * P.T') :
    (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ gridΛ P b N ^ 2 := by
  unfold gridΛ
  have hX : 0 ≤ (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg hb _) hTT.le)
  calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))
      = Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) ^ 2 := (Real.sq_sqrt hX).symm
    _ ≤ max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

theorem gridΛ_le (P : M.Par) (b CT : ℝ) (N : ℕ) (hN : N ≤ 3 * (P.r + 1)) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT0 : 0 < P.T * P.T') (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    gridΛ P b N ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hm' : (((2 * P.r + 2 : ℕ) : ℝ)) = 2 * (P.r : ℝ) + 2 := by push_cast; ring
  set m : ℝ := (((2 * P.r + 2 : ℕ) : ℝ)) with hm
  have hm0 : 0 ≤ m := by rw [hm']; linarith
  have hCm : 0 ≤ CT * m := mul_nonneg hCT hm0
  have hinv : (P.T * P.T')⁻¹ ≤ b ^ (CT * m) := by
    have h1 : 0 < b ^ (CT * m) := Real.rpow_pos_of_pos hb0 _
    rw [Real.rpow_neg hb0.le] at hTT
    exact (inv_le_comm₀ h1 hTT0).mp hTT
  have h43 : (4 / 3 : ℝ) ^ N ≤ b ^ (3 * (P.r + 1)) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by linarith) N) (pow_le_pow_right₀ hb1 hN)
  have hpow : b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20) ≤ b ^ (12 * m) := by
    rw [← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    rw [hm']
    push_cast
    linarith
  have hX : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ b ^ (12 * m) * b ^ (CT * m) := by
    rw [div_eq_mul_inv]
    calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) * (P.T * P.T')⁻¹)
        ≤ b ^ (3 * (P.r + 1)) * (b ^ (8 * P.r + 20) * b ^ (CT * m)) :=
          mul_le_mul h43 (mul_le_mul_of_nonneg_left hinv (pow_nonneg hb0.le _))
            (mul_nonneg (pow_nonneg hb0.le _) (inv_nonneg.mpr hTT0.le)) (pow_nonneg hb0.le _)
      _ = (b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20)) * b ^ (CT * m) := by ring
      _ ≤ b ^ (12 * m) * b ^ (CT * m) := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb0.le _)
  have hy : (b ^ ((6 + CT) * m)) ^ 2 = b ^ (12 * m) * b ^ (2 * (CT * m)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  have hX' : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ (b ^ ((6 + CT) * m)) ^ 2 := by
    rw [hy]
    refine le_trans hX (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hb0.le _))
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  unfold gridΛ
  refine max_le (Real.one_le_rpow hb1 (mul_nonneg (by linarith) hm0)) ?_
  calc Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))
      ≤ Real.sqrt ((b ^ ((6 + CT) * m)) ^ 2) := Real.sqrt_le_sqrt hX'
    _ = b ^ ((6 + CT) * m) := Real.sqrt_sq (Real.rpow_nonneg hb0.le _)

theorem onCut_of_minmax (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) (h1 : min (u l) (u' l) + 2 ≤ -Y)
    (h2 : -Y ≤ max (u l) (u' l) - 2) : I.OnCut u u' l Y := by
  unfold Formalism.FourierDecayAlt.I.OnCut
  rcases le_total (u l) (u' l) with h | h
  · left
    rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact ⟨h1, h2⟩
  · right
    rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact ⟨h1, h2⟩

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gridY_cut (P : M.Par) (l N : ℕ) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u l - P.u' l|) :
    ∀ y ∈ gridY P l N, I.OnCut P.u P.u' l y ∧ I.OnCut P.u P.u' l (y + 1) := by
  intro y hy
  have hlen' : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ max (P.u l) (P.u' l) - min (P.u l) (P.u' l) := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
    exact hlen
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := progY_cut (min (P.u l) (P.u' l)) (max (P.u l) (P.u' l)) _ hlen' y hy
  exact ⟨onCut_of_minmax _ _ _ _ h1 h2, onCut_of_minmax _ _ _ _ h3 h4⟩

private theorem exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters {S : Type} (q : ℂ → ℂ) (y : ℝ) :
    ∀ L : List (Formalism.FourierDecayAlt.Wd.Letter ℂ S),
      (∀ l ∈ L, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
        (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ)))) →
      ∃ t : ℝ, (4 / 5 : ℝ) ^ L.length ≤ t ∧ Formalism.FourierDecayAlt.Wd.qw q L (y : ℂ) = (t : ℂ) * q (y : ℂ) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨1, by simp, by simp [Formalism.FourierDecayAlt.Wd.qw]⟩
  | cons l L ih =>
    intro h
    obtain ⟨t, ht, heq⟩ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨d, hd, hcase⟩ := h l (by simp)
    have ht0 : 0 ≤ t := le_trans (pow_nonneg (by norm_num) _) ht
    rcases hcase with ⟨hp, hpt⟩ | ⟨hp, hpt⟩
    · refine ⟨t * ((y - (y - d) + 1) / (y - (y - d))), ?_, ?_⟩
      · have e : (y - (y - d) + 1) / (y - (y - d)) = (d + 1) / d := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (d + 1) / d := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff₀ (by linarith)]
            linarith
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, if_true, heq, hpt]
        push_cast
        ring
    · refine ⟨t * ((y - d + 1 - y) / (y - d + 1 - y - 1)), ?_, ?_⟩
      · have e : (y - d + 1 - y) / (y - d + 1 - y - 1) = (1 - d) / (-d) := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (1 - d) / (-d) := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
          · rw [le_div_iff₀ (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, Bool.false_eq_true, ↓reduceIte, heq, hpt]
        push_cast
        ring

theorem freeBound_text (p : KB.Pl P Wp Wq) (K N : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) (hL : PairData P p.l0 lam c g b)
    (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    FreeBound p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hl2, hk2⟩ := p.hl
  have hTT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  have hb : 0 ≤ b := by linarith [hL.b_ge_three]
  have hc := hL.c_pos
  have hPst : ∀ Y : ℝ, 0 < GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c Y := by
    intro Y
    unfold GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst
    exact Finset.prod_pos (fun s _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc)
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  intro w _ hwlen y hy hlet
  have hlet' : ∀ l ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
      (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ))) := by
    intro l hl
    unfold Formalism.FourierDecayAlt.D.positionted at hl
    rw [List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    obtain ⟨y', hy', hne, hcase⟩ := hlet (w.get a) (by simp [List.get_eq_getElem])
    refine ⟨y - y', hsep y hy y' hy' (Ne.symm hne), ?_⟩
    rcases hcase with h | h
    · left
      refine ⟨by show (w.get a).1 = true; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
    · right
      refine ⟨by show (w.get a).1 = false; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
  obtain ⟨t, ht, heq⟩ := exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters (Formalism.FourierDecayAlt.M.qC P) y _ hlet'
  have hls : (Formalism.FourierDecayAlt.D.positionted w).length = w.length := by
    unfold Formalism.FourierDecayAlt.D.positionted
    simp
  rw [hls] at ht
  have hq := nq_onCut_pair P hOK p.l0 hl1 hl2 hk2 lam c g b hL y (hY y hy).1
  have hre : (Formalism.FourierDecayAlt.Wd.qw (Formalism.FourierDecayAlt.M.qC P) (Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re
      = t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := by
    rw [heq, Complex.re_ofReal_mul]
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos (by norm_num) _) ht
  refine ⟨⟨hPst y, hPst (y + 1), by rw [hre]; exact mul_pos ht0 hq.1⟩, ?_⟩
  rw [hre]
  have hsq := gridΛ_sq P b N hb hTT
  have h1 : 1 ≤ (4 / 3 : ℝ) ^ N * t := by
    calc (1 : ℝ) ≤ ((4 / 3 : ℝ) * (4 / 5)) ^ w.length := one_le_pow₀ (by norm_num)
      _ = (4 / 3 : ℝ) ^ w.length * (4 / 5) ^ w.length := mul_pow _ _ _
      _ ≤ (4 / 3 : ℝ) ^ N * t :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) ht (by positivity) (by positivity)
  have hR0 : 0 ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re :=
    mul_nonneg (div_nonneg (pow_nonneg hb _) hTT.le) hq.1.le
  calc GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c y
        * GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c (y + 1)
      ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := hq.2
    _ ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ((4 / 3 : ℝ) ^ N * t) :=
        le_mul_of_one_le_right hR0 h1
    _ = ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) := by ring
    _ ≤ gridΛ P b N ^ 2 * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) :=
        mul_le_mul_of_nonneg_right hsq (mul_pos ht0 hq.1).le

theorem grids_text (p : KB.Pl P Wp Wq) (K N : ℕ) (hKN : K ≤ N) (lam : ℕ → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 lam c g b) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N ∧
      TBBx5.LiftGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  have hcard : N - K + K * (2 * P.r + 1) ≤ (gridY P p.l0 N).card := by
    unfold gridY
    rw [progY_card]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hKN
    rw [Nat.add_sub_cancel_left]
    nlinarith [Nat.zero_le (j * P.r)]
  have hF := freeBound_text p K N lam c g b hL hlen
  have hB : 0 ≤ gridΛ P b N := le_trans zero_le_one (one_le_gridΛ P b N)
  exact ⟨waveGrid_of_sep p _ _ _ K N hB hY hsep hcard hF, liftGrid_of_sep p _ _ _ K N hB hY hsep hcard hF⟩

end grid

end CompanionTheory.WaveGrid
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.TypeHC
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.TypeHC

section param
open PI.UpqRep PI.HwUniqW GlobalTheory.BesselFrame GlobalTheory.SupNonzero

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem isType_of_hc {u : ℕ → ℝ} {u₀ : Fin k → ℝ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hπ : IsHCTypeW k r z u₀ π) (hu : ∀ s : Fin k, u (s.val + 1) = u₀ s) : Q.IsType k r z π u := by
  obtain ⟨p1, pmul, punit, pcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ
  have hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π := ⟨p1, pmul⟩
  have hcont : ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) := continuousOn_clm_apply.2 pcont
  obtain ⟨g, hg, h₀⟩ := hπ
  have hirr : ∀ S : Submodule ℂ W, (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS => h₀.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ (conj_mem_UW hg (by
      have := Matrix.mem_unitaryGroup_iff'.mp hx.1
      rw [Matrix.star_eq_conjTranspose] at this
      exact mem_UJset_allPos.2 this)) v hv
  obtain ⟨E, hgl, -, hE⟩ := GlobalTheory.UnitaryDerived.exists_derived_action k W _ h₀.2.2.1
  obtain ⟨v, hv, hq⟩ := qdet_eigen h₀ E hgl hE
  have hB := isFrameOf hg
  set A := g * incl k r with hA
  set B := Aᴴ * Hpk k r with hBd
  have hd : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ x, Q.dRep π (A * Z * B) x = ∑ a, ∑ b, Z a b • E a b x := by
    intro Z hZ x
    rw [← (hE Z hZ x).deriv]
    unfold Q.dRep
    congr 1
    funext t
    rw [conj_blockW hg.1, ← exp_corner _ _ (co_mul hg.1), Matrix.mul_smul, Matrix.smul_mul]
  have hH : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv Hpk_mul_self
  have hc : ∀ Y : Matrix (Fin k) (Fin k) ℂ,
      (Formalism.QuantumDeterminants.Hpk k r)⁻¹ * (A * Y * B)ᴴ * Formalism.QuantumDeterminants.Hpk k r = A * Yᴴ * B := by
    intro Y
    rw [hH, hBd]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose, ← Matrix.mul_assoc,
      Hpk_mul_self, Matrix.one_mul]
    rfl
  have hEB : Qr.EB π (fun a => g *ᵥ bvec (bl k r a)) = E := by
    funext a b
    refine LinearMap.ext fun x => ?_
    have hl := P.QrD.frame_lie hB a b
    show P.QrD.ecOp π _ x = _
    rw [← P.QrD.ecRep_eq hrep hcont hl.1 hl.2, unitB_eq]
    unfold Q.EcRep Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [← hA, ← hBd, hc, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul,
      ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, hd, hd]
    · simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
      have e : ∀ c d, ((1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - (Matrix.single a b (1 : ℂ))ᴴ)) c d +
          Complex.I * ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a b (1 : ℂ) + (Matrix.single a b (1 : ℂ))ᴴ)) c d =
          Matrix.single a b (1 : ℂ) c d := by
        intro c d
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
        field_simp
        ring
      simp only [e]
      simp [Matrix.single, ite_and, ite_smul]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, ← neg_smul, add_comm]
      congr 1
      simp [Complex.conj_ofNat]
    · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, ← smul_neg, neg_sub]
      congr 1
      simp
  let K : Submodule ℂ W :=
    { carrier := {x | ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((k : ℂ) - 1) / 2) x = (∏ s, (Y + (u₀ s : ℂ))) • x}
      add_mem' := fun ha hb w => by rw [map_add (f := _), ha w, hb w, smul_add]
      zero_mem' := fun w => by simp
      smul_mem' := fun s x hx w => by rw [map_smul, hx w, smul_comm] }
  have hKs : Qr.Stab (Qr.EB π (fun a => g *ᵥ bvec (bl k r a))) K := by
    rw [hEB]
    intro a b x hx w
    have := congrArg (fun T : Module.End ℂ W => T x) (Formalism.REAL.qDetCentral _ k _ hgl (w + ((k : ℂ) - 1) / 2) a b)
    simp only [Module.End.mul_apply] at this
    rw [this, hx w, map_smul]
  have hK := P.lie_stabilizer W k r z π _ hz hT ⟨hrep, hcont⟩ hB K hKs
  have hKt : K = ⊤ := (hirr K hK).resolve_left ((Submodule.ne_bot_iff K).2 ⟨v, hq, hv⟩)
  refine ⟨h₀.1, hrep, hcont, punit, hirr, fun Bs hBs w x => ?_⟩
  have hx : x ∈ K := hKt ▸ Submodule.mem_top
  have e := hx (w - ((k : ℂ) - 1) / 2)
  rw [sub_add_cancel] at e
  rw [(P.frame_general_linear W k r k z π Bs ⟨hrep, hcont⟩ hBs).2, P.QrCap.capChange hz hT ⟨hrep, hcont⟩ hBs hB, hEB, e,
    CompanionTheory.D.Inhab.TypeHW.prod_Icc]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hu]
  ring

end param

theorem exists_place : ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (μW μW' : Measure (Formalism.QuantumDeterminants.Mt P.k P.r)) (l0 : ℕ), Q.IsPlace P z z' π π' → 2 ≤ P.k → 1 ≤ l0 → l0 ≤ P.k →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z) μW → μW Set.univ = 1 →
    B.IsHaarOn (Formalism.QuantumDeterminants.UWset P.k P.r z') μW' → μW' Set.univ = 1 →
    ∃ p : KB.Pl P Wp Wq, p.l0 = l0 ∧ p.T.base.z = z ∧ p.T.base.z' = z' ∧ p.T.base.π = π ∧ p.T.base.π' = π' ∧
      p.T.base.μW = μW ∧ p.T.base.μN = D.muN P.k P.r ∧ p.T.base.μW' = μW' ∧
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P z z' π π' μW μW' l0 hP hk hl1 hl2 hW hW1 hW' hW1'
  obtain ⟨μ, hμ⟩ := CompanionTheory.D.Inhab.IsDataInh.haar_glev_last P.k P.r
  obtain ⟨hOK, hz, hz', hT, hT', ⟨-, hr, hc, hu, -, -⟩, ⟨-, hr', hc', hu', -, -⟩⟩ := id hP
  obtain ⟨B0, e1, e2, e3, e4, -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists P.k P.r Wp Wq z z' π π' hOK.k_pos hz hz'
    (by rw [hT]; exact hOK.T_pos) (by rw [hT']; exact hOK.T'_pos) hr hr' hu hu' hc hc'
  obtain ⟨T0, -, -, -, -, hN0⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq B0
  have hmuN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset P.k P.r) (D.muN P.k P.r) := by
    have h := (hN0 0 (Nat.zero_le _)).2.2
    have h' : T0.base.μN = D.muN P.k P.r := (by simpa using h : (T0.bs 0).μN = D.muN P.k P.r)
    exact h' ▸ T0.base.haarN
  subst e1 e2 e3 e4
  let Bs : B.RealPlaceData P.k P.r Wp Wq :=
    { B0 with μW := μW, μN := D.muN P.k P.r, μW' := μW', haarW := hW, haarN := hmuN, haarW' := hW' }
  obtain ⟨T, hTb, hTN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower P.k P.r Wp Wq Bs hW1 hW1' rfl
  have hPl : Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π' := by
    rw [hTb]; exact hP
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of T.base
  obtain ⟨X, L, st, hD⟩ := CompanionTheory.D.Inhab.IsDataInh.isData_of_place P _ _ _ _ hPl μ hμ l0
  obtain ⟨Θ, hI, hDD⟩ := hTL Wp Wq P T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P T.base.z T.base.z' T.base.π T.base.π' (m₀ *ᵥ ν') hPl
    f1 f2 f3
  refine ⟨⟨l0, T, ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hTN, hF, hPl, ⟨X, μ, L, st, hD, hI⟩⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDD⟩
  · change T.base.z = B0.z; rw [hTb]
  · change T.base.z' = B0.z'; rw [hTb]
  · change T.base.π = B0.π; rw [hTb]
  · change T.base.π' = B0.π'; rw [hTb]
  · change T.base.μW = μW; rw [hTb]
  · change T.base.μN = D.muN P.k P.r; rw [hTb]
  · change T.base.μW' = μW'; rw [hTb]

end CompanionTheory.WaveGrid.TypeHC
end
end

