module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeasSset
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem exists_isQuotMeas_Sset : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (GG k r) μG → IsHaarOn (Sset k r z) μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r z μG μS hz hT hG hS
  obtain ⟨μW, hW⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩
  obtain ⟨hSg, hsub, hH, hR⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT
    (conv hW) (conv hN)
  have hS' : PI.IsHaarOnM (Sset k r z) μS := hS
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'
  have hR' : PI.IsRightInvM (Sset k r z) μS := by
    intro s hs
    rw [hc, Measure.map_smul, hR s hs]
    exact (GlobalTheory.ProdHaar.measurable_rmulQ s).aemeasurable
  obtain ⟨hGg, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinates
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCovSec

open GlobalTheory.NilCov

variable {n : ℕ}

def jInv (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Jm ε * Xᴴ * Jm ε

variable (ε : Fin n → Bool)

theorem jInv_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : jInv ε (X - Y) = jInv ε X - jInv ε Y := by
  simp only [jInv, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem jInv_smul (a : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (a • X) = a • jInv ε X := by
  simp [jInv, conjTranspose_smul]

theorem jInv_jInv_mul (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (jInv ε X * X) = jInv ε X * X := by
  simp only [jInv, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]

theorem continuous_jInv : Continuous (jInv ε) := by
  exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

def iter (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Nat.rec Y (fun _ X => Y - (1 / 2 : ℝ) • (jInv ε X * X)) k

theorem continuous_iter (k : ℕ) : Continuous fun Y => iter ε Y k := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    exact continuous_id.sub ((((continuous_jInv ε).comp ih).matrix_mul ih).const_smul (1 / 2 : ℝ))

variable {ε} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}

theorem iter_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y k ∈ A 0 := by
  induction k with
  | zero => exact hY
  | succ k ih =>
    exact (A 0).sub_mem hY ((A 0).smul_mem _ (hle 0 (hmul 0 _ (hinv 0 _ ih) _ ih).1))

theorem iter_sub_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y (k + 1) - iter ε Y k ∈ A k := by
  have hm := iter_mem hmul hle hinv hY
  induction k with
  | zero => exact (A 0).sub_mem (hm 1) (hm 0)
  | succ k ih =>
    have e : iter ε Y (k + 1 + 1) - iter ε Y (k + 1) =
        (-(1 / 2) : ℝ) • (jInv ε (iter ε Y (k + 1) - iter ε Y k) * iter ε Y (k + 1) +
          jInv ε (iter ε Y k) * (iter ε Y (k + 1) - iter ε Y k)) := by
      have e1 : iter ε Y (k + 1 + 1) =
        Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y (k + 1)) * iter ε Y (k + 1)) := rfl
      have e2 : iter ε Y (k + 1) = Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y k) * iter ε Y k) := rfl
      rw [e1]
      generalize iter ε Y (k + 1) = P at e2 ⊢
      generalize iter ε Y k = Q at e2 ⊢
      rw [jInv_sub, Matrix.sub_mul, Matrix.mul_sub]
      nth_rewrite 3 [e2]
      module
    rw [e]
    exact (A _).smul_mem _ ((A _).add_mem (hmul k _ (hinv k _ ih) _ (hm _)).1
      (hmul k _ ih _ (hinv 0 _ (hm _))).2)

theorem one_add_mul_of_fixed {X Y : Matrix (Fin n) (Fin n) ℂ} (hY : jInv ε Y = -Y)
    (h : X = Y - (1 / 2 : ℝ) • (jInv ε X * X)) : (1 + jInv ε X) * (1 + X) = 1 := by
  have h2 : jInv ε X = -Y - (1 / 2 : ℝ) • (jInv ε X * X) := by
    conv_lhs => rw [h]
    rw [jInv_sub, jInv_smul, jInv_jInv_mul, hY]
  have h3 : X + jInv ε X + jInv ε X * X = 0 := by
    generalize jInv ε X * X = P at h h2 ⊢
    rw [h2, h]
    module
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  calc 1 + X + (jInv ε X + jInv ε X * X) = 1 + (X + jInv ε X + jInv ε X * X) := by abel
    _ = 1 := by rw [h3, add_zero]

theorem inUJ_of_one_add_mul {X : Matrix (Fin n) (Fin n) ℂ} (h : (1 + jInv ε X) * (1 + X) = 1) :
    (1 + X)ᴴ * Jm ε * (1 + X) = Jm ε := by
  have e : (1 + X)ᴴ * Jm ε = Jm ε * (1 + jInv ε X) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, jInv, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.mul_assoc, h, Matrix.mul_one]

theorem exists_continuous_section (n d m : ℕ) (ε : Fin n → Bool)
    (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : A m = ⊥) (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c)
    (hinv : ∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hG : ∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) :
    ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧
      ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  let Y : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => ∑ i, x i • E i
  have hYc : Continuous Y := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  have hY0 : ∀ x, Y x ∈ A 0 := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hG i).1
  have hYθ : ∀ x, jInv ε (Y x) = -Y x := fun x => by
    simp only [jInv, Y, conjTranspose_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := jInv_smul ε (x i) (E i)
    unfold jInv at this
    rw [this, inv_eq_neg_of_inG (hG i).2, smul_neg]
  let X : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => iter ε (Y x) m
  have hXc : Continuous X := (continuous_iter ε m).comp hYc
  have hfix : ∀ x, X x = Y x - (1 / 2 : ℝ) • (jInv ε (X x) * X x) := fun x => by
    have h := iter_sub_mem hmul hle hinv (hY0 x) m
    rw [hA, Submodule.mem_bot, sub_eq_zero] at h
    exact h.symm
  have h1 : ∀ x, (1 + jInv ε (X x)) * (1 + X x) = 1 := fun x => one_add_mul_of_fixed (hYθ x) (hfix x)
  let u : (Fin d → ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun x =>
    ⟨1 + X x, 1 + jInv ε (X x), mul_eq_one_comm.1 (h1 x), h1 x⟩
  have huc : Continuous u := Units.continuous_iff.2
    ⟨continuous_const.add hXc, continuous_const.add ((continuous_jInv ε).comp hXc)⟩
  have hu : ∀ x, u x ∈ UJ ε := fun x => inUJ_of_one_add_mul (h1 x)
  refine ⟨fun x => ⟨u x, hu x⟩, huc.subtype_mk hu, fun x => ?_⟩
  have e : uMat (⟨u x, hu x⟩ : UJ ε) - 1 = X x := by
    change 1 + X x - 1 = X x
    abel
  rw [e]
  refine ⟨iter_mem hmul hle hinv (hY0 x) m, fun i => ?_⟩
  have h0 : ipL (E i) (jInv ε (X x) * X x) = 0 := by
    have h := ipL_inv (hG i).2 (jInv ε (X x) * X x)
    have h' : ipL (E i) (jInv ε (jInv ε (X x) * X x)) = -ipL (E i) (jInv ε (X x) * X x) := h
    rw [jInv_jInv_mul] at h'
    linarith
  rw [← ipL_apply, hfix x, map_sub, map_smul, h0, smul_zero, sub_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Y, map_sum, map_smul, ipL_apply, hE, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end GlobalTheory.NilCovSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FarTermsModerateRegionOfFlagBound
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem farModerate_e_one_nonneg (B : RowsAut) : 0 ≤ (B.e 1).re := by
  obtain ⟨-, -, -, hpos, -⟩ := B.e_adm
  have h := hpos 1 (fun _ => 1) (fun _ => 1)
  simp at h
  simpa using (Complex.le_def.1 h).1

private theorem epN_pos_and_le_inv_sqrt_and_mul_le_log_two (n f q : ℕ) (hn : 8 ≤ n) (hf : 1 ≤ f) (hq : 1 ≤ q)
    (hqn : q ^ 2 ≤ n) :
    0 < 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ∧
      1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / Real.sqrt (2 * (q : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) ≤ Real.log 2 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
    exact_mod_cast this
  have hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by positivity
  have hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hf'
  have hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by nlinarith
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q :=
      calc Real.sqrt (2 * (q : ℝ)) ≤ Real.sqrt ((2 * (q : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * q := Real.sqrt_sq (by linarith)
    have hspos : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    calc 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / (2 * q) := by
          rw [div_le_div_iff₀ hD (by linarith)]
          nlinarith
      _ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs
  · have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 := (div_le_one hD).2 hnD
    have h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) =
        2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) := by ring
    rw [h2]
    linarith

theorem farModerate_of_farBound :
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  intro hFM hFB Cg hCg
  refine ⟨8, fun B d p q b hq hCH => ?_⟩
  obtain ⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH
  obtain ⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩ := hCH
  have htq' : tauStar B q b < 1 / 2 := (htq hq).1
  have he1 : 0 ≤ (B.e 1).re := farModerate_e_one_nonneg B
  have hK : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hdpos.le he1
  obtain ⟨hep0, hepq, heplog⟩ := epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h
    (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le
  obtain ⟨-, -, hfin, -⟩ := hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤
      ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
    intro x hx
    obtain ⟨hs, hsum⟩ := hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x
    have hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal
        (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp only [ofReal_norm]
      rfl
    have hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤
        (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by
      have ht1 : tauStar B q b ≤ tau1 B.I x := le_min htq'.le hx.2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2)
        (pow_le_pow_left₀ htpos.le ht1 2)
    have hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)) := by positivity
    rw [hx1]
    apply ENNReal.ofReal_le_ofReal
    calc ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖
        ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) := hsum
      _ ≤ (∏ v, d v) * (B.e 1).re *
            (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlat hK) hC0
      _ = (∏ v, d v) * (B.e 1).re *
            ((3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)))) := by ring
      _ ≤ (∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) :=
          mul_le_mul_of_nonneg_left hC hK
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b,
          ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))
          ∂(B.I.muA B.μf) := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf B.fund := mul_le_mul_of_nonneg_left (measure_mono fun x hx => hx.1) (by simp)
    _ = ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d) := by
      rw [← ENNReal.ofReal_toReal hfin.ne,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      congr 1
      show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) *
        ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)
      ring

end GlobalTheory.Deep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGradedPieceSizesStabiliserMul
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSizeInv

open GlobalTheory.PointEquivariance

theorem mem_span_of_image {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (s : Set (Fin n → E)) (z : Fin n → E)
    (h : (fun l => φ (z l)) ∈ Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s)) :
    z ∈ Submodule.span E s := by
  by_contra hz
  obtain ⟨f, hfz, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  have hf0 : ∀ y ∈ s, f y = 0 := fun y hy => by
    have hm : f y ∈ (Submodule.span E s).map f := Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at hm
    simpa using hm
  have hfx : ∀ y : Fin n → E, f y = ∑ l, y l * f (fun j => if l = j then 1 else 0) := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [smul_eq_mul]
  let F : (Fin n → ℂ) →ₗ[ℂ] ℂ := ∑ l, φ (f (fun j => if l = j then 1 else 0)) • LinearMap.proj l
  have hF : ∀ y : Fin n → E, F (fun l => φ (y l)) = φ (f y) := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfx y, map_sum]
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have hle : Submodule.span ℂ ((fun y : Fin n → E => fun l => φ (y l)) '' s) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show F _ = 0
    rw [hF, hf0 y hy, map_zero]
  have h0 : φ (f z) = 0 := by
    rw [← hF]
    exact LinearMap.mem_ker.1 (hle h)
  exact hfz ((map_eq_zero_iff φ φ.injective).1 h0)

theorem mulVec_mem_span (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : InfinitePlace I.F) (k : Fin (a + 1)) (γ : Matrix (Fin I.n) (Fin I.n) I.E)
    (h : ∀ y ∈ flagAt I S v k, ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ y ∈ flagAt I S v k)
    (y : Fin I.n → I.E) (hy : y ∈ S k) : γ *ᵥ y ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hmem : (I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l)) ∈ flagAt I S v k := by
    unfold flagAt
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h1 := h _ hmem
  have hcomp : ((I.P v)⁻¹ * γ.map (I.φ v) * I.P v) *ᵥ ((I.P v)⁻¹ *ᵥ (fun l => I.φ v (y l))) =
      (I.P v)⁻¹ *ᵥ (fun l => I.φ v ((γ *ᵥ y) l)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
      ← Matrix.mulVec_mulVec]
    congr 1
    funext l
    exact (RingHom.map_mulVec (I.φ v) γ y l).symm
  rw [hcomp] at h1
  unfold flagAt at h1
  have h2 := Submodule.mem_map_of_mem (f := Matrix.toLin' (I.P v)) h1
  rw [Submodule.map_span, Set.image_image] at h2
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mulVec] at h2
  exact mem_span_of_image (I.φ v) _ _ h2

theorem ratIso_eq (I : AutInst) (γ : GL (Fin I.n) I.E) (Λ N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hΛ : ratIso I γ Λ = Λ) (hN : ∀ y, y ∈ N ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E)))
    (h : ∀ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) :
    ratIso I γ N = N := by
  rw [ratIso_apply] at hΛ ⊢
  have hinj : Function.Injective (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
    intro y y' hyy
    have hc := congrArg (Matrix.toLin' ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)) hyy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hc
  have hWle : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro y hy
    exact h y hy
  have hW : (Submodule.span I.E (N : Set (Fin I.n → I.E))).map
      (Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)) = Submodule.span I.E (N : Set (Fin I.n → I.E)) := by
    refine Submodule.eq_of_le_of_finrank_eq hWle ?_
    have e := LinearEquiv.finrank_map_eq (ratEquiv I γ) (Submodule.span I.E (N : Set (Fin I.n → I.E)))
    exact e
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    have hy' := (hN y).1 hy
    refine (hN _).2 ⟨?_, h y hy⟩
    rw [← hΛ]
    exact ⟨y, hy'.1, by simp⟩
  · intro y hy
    obtain ⟨hyΛ, hyW⟩ := (hN y).1 hy
    rw [← hΛ] at hyΛ
    obtain ⟨y', hy'Λ, hy'⟩ := hyΛ
    rw [← hW] at hyW
    obtain ⟨y'', hy''W, hy''⟩ := hyW
    have hyy : y'' = y' := hinj (by rw [hy'', ← hy']; rfl)
    subst hyy
    exact ⟨y'', (hN y'').2 ⟨hy'Λ, hy''W⟩, hy'⟩

theorem sizesAt_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S →
    ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  intro I xf a j S hS γ hγ g
  obtain ⟨⟨δ, hδ, hδ1, hδK⟩, hkeep⟩ := hγ
  obtain ⟨c, -, hc1, hc2⟩ := hδ
  unfold IsSatFlag at hS
  obtain ⟨-, -, -, hsat, -⟩ := hS
  have hL : lamX I (δ * (1, xf)) = lamX I (1, xf) := by
    have hk := (lamX_mul_eq_iff I (1, xf) (1, xf⁻¹ * δ.2 * xf)).1 hδK
    have h2 : (δ * (1, xf)).2 = ((1, xf) * (1, xf⁻¹ * δ.2 * xf) : I.GA).2 := by
      simp [mul_assoc]
    rw [← hk, lamX_eq, lamX_eq, h2]
  have hlat : ratIso I c (lamX I (1, xf)) = lamX I (1, xf) := by
    rw [← lamX_rat I (1, xf) δ c hc2, hL]
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hfix : ∀ k, ratIso I c (S k) = S k := fun k =>
    ratIso_eq I c _ (S k) hlat (hsat k) fun y hy =>
      mulVec_mem_span I S v₀ k (c : Matrix (Fin I.n) (Fin I.n) I.E)
        (fun x hx => by rw [← hc1 v₀, hδ1]; exact hkeep v₀ k x hx) y hy
  have hcond : ∀ v, uMat (((γ, 1) : I.GA).1 v) =
      (I.P v)⁻¹ * (c : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := fun v => by
    show uMat (γ v) = _
    rw [← hδ1]
    exact hc1 v
  have hax : ((γ, 1) : I.GA) * (g, xf) = (γ * g, xf) := by simp
  unfold sizesAt
  funext i
  have key := sizeQ_eq (bas I) (frm I (g, xf)) (frm I (γ * g, xf)) (ratIso I c)
    (fun N => by rw [← hax]; exact zl_ratIso I (g, xf) (γ, 1) c hcond N) (rkK_ratIso I c)
    (S i.succ) (S i.castSucc)
  rw [hfix, hfix] at key
  exact key

end GlobalTheory.FlagSizeInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagRareOfNonzeroFlagBound
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
end

