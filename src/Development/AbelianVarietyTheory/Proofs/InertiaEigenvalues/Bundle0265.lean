module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0202
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandard
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZero
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem acris_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  intro l _ x y hxy
  have hl : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hρ0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr hl0
  have hG := isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1
  have hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹ := by
    rw [hG.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ0.le
  have h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0 := by
    have h := hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))
    rw [zero_mul, hc] at h
    have : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · linarith
  by_contra h
  push_neg at h
  have hx := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x h.1 (l : ℝ)⁻¹ le_rfl hρ1
  have hy := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l y h.2 (l : ℝ)⁻¹ le_rfl hρ1
  have hm := hG.2.2.2.1 x y
  rw [hxy, h0] at hm
  have := mul_pos hx hy
  linarith

end GlobalTheory.PMon.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisSeriesTermsMemPrimePow
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem pw_natCast_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  unfold pw
  rw [zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ,
      mul_comm]

theorem two_mul_succ_le_pow (l k h : ℕ) (hl : 2 ≤ l) (hh : 2 ≤ h) :
    2 * (k + 1) ≤ l ^ ((k + 1) * h - 1) := by
  have h1 : 2 * k + 1 < 2 ^ (2 * k + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * k + 1) ≤ l ^ (2 * k + 1) := Nat.pow_le_pow_left hl _
  have h3 : (k + 1) * 2 ≤ (k + 1) * h := Nat.mul_le_mul_left _ hh
  have h4 : l ^ (2 * k + 1) ≤ l ^ ((k + 1) * h - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem terms_mem (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l) (hh : 2 ≤ h)
    (hx : ‖sh x‖ ≤ ‖(l : ℂ_[l])‖) :
    ∃ c : ℤ → Acris l, (∀ n : ℤ, (l : Acris l) ^ n.natAbs ∣ c n) ∧ ∀ n : ℤ,
      (l : Acris l) ^ n.toNat * c n =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
  have key : ∀ n : ℤ, ∃ c : Acris l, (l : Acris l) ^ n.natAbs ∣ c ∧
      (l : Acris l) ^ n.toNat * c =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · cases m with
      | zero => exact ⟨algebraMap (Ainf l) (Acris l) (tm (pw (0 * h) x)), by simp, by simp⟩
      | succ k =>
        have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
        obtain ⟨d, hd⟩ := tm_pow_dvd l x hx
        set y := algebraMap (Ainf l) (Acris l) (tm x)
        set M := l ^ ((k + 1) * h - 1)
        have hM := two_mul_succ_le_pow l k h hl2 hh
        have hN : l ^ ((k + 1) * h) = l * M := by
          have : (k + 1) * h = ((k + 1) * h - 1) + 1 := by
            have : 2 ≤ (k + 1) * h := le_trans hh (Nat.le_mul_of_pos_left h (Nat.succ_pos k))
            omega
          rw [this, pow_succ, mul_comm]
        have hpow : algebraMap (Ainf l) (Acris l) (tm (pw (((k + 1 : ℕ) : ℤ) * h) x)) =
            (l : Acris l) ^ (2 * (k + 1)) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M) := by
          have e1 : (((k + 1 : ℕ) : ℤ) * (h : ℤ)) = (((k + 1) * h : ℕ) : ℤ) := by push_cast; ring
          rw [e1, pw_natCast_eq_pow, show tm (x ^ l ^ ((k + 1) * h)) = tm x ^ l ^ ((k + 1) * h) from
            map_pow (WittVector.teichmuller l) x _, map_pow, hN, pow_mul, hd, mul_pow, ← mul_assoc,
            ← pow_add, Nat.add_sub_cancel' hM]
        refine ⟨(l : Acris l) ^ (k + 1) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M), ?_, ?_⟩
        · have e4 : (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by omega
          rw [e4]
          exact Dvd.intro _ rfl
        · have e2 : (-((k + 1 : ℕ) : ℤ)).toNat = 0 := by omega
          have e3 : (((k + 1 : ℕ) : ℤ)).toNat = k + 1 := by omega
          rw [e2, e3, pow_zero, one_mul, hpow, ← mul_assoc, ← pow_add]
          ring_nf
    · refine ⟨(l : Acris l) ^ m * algebraMap (Ainf l) (Acris l) (tm (pw (-(m : ℤ) * h) x)),
        ?_, ?_⟩
      · have e4 : (-(m : ℤ)).natAbs = m := by omega
        rw [e4]
        exact Dvd.intro _ rfl
      · have e2 : (-(m : ℤ)).toNat = 0 := by omega
        have e3 : (-(-(m : ℤ))).toNat = m := by omega
        rw [e2, e3, pow_zero, one_mul]
  choose c hc1 hc2 using key
  exact ⟨c, hc1, hc2⟩

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLaws
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable (l : ℕ) [Fact l.Prime]

lemma vrlaw_one_lt : (1 : ℝ) < l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt

lemma vrlaw_rad (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl := vrlaw_one_lt l
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

lemma vrlaw_gC_zero (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hG := isGauss_gC_target l ρ h0 h1
  have hm := hG.2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (_root_.GlobalTheory.PMon.Gauss.gC_basic_values l ρ h0 h1).2.1] at hm
  have : gC l ρ 0 * (1 - ρ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by linarith)

theorem vr_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 →
    (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧
    (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧
    (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧
    ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  intro l _ r hr0 hr1
  have hl := vrlaw_one_lt l
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨hρ0, hρ1⟩ := vrlaw_rad l r hr0 hr1
  set ρ : ℝ := (l : ℝ) ^ (-r) with hρ
  have hG := isGauss_gC_target l ρ hρ0 hρ1
  have hpos : ∀ x : Formalism.Per.Acris l, x ≠ 0 → 0 < gC l ρ x := fun x hx => _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx ρ hρ0 hρ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    simp only [vr]
    rw [← hρ, hG.2.2.2.1 x y, Real.logb_mul (hpos x hx).ne' (hpos y hy).ne']
    ring
  · intro x hx
    have hl' : (0 : ℝ) < l := hl0
    have hrl0 : 0 < r / l := div_pos hr0 hl'
    have hrl1 : r / l ≤ 1 := by
      rw [div_le_one hl']; linarith
    obtain ⟨hσ0, hσ1⟩ := vrlaw_rad l (r / l) hrl0 hrl1
    have he : ρ ^ ((1 : ℝ) / l) = (l : ℝ) ^ (-(r / l)) := by
      rw [hρ, ← Real.rpow_mul hl0.le]
      congr 1
      ring
    have hF := _root_.GlobalTheory.PMon.Gauss.gC_phi l ρ hρ0 hρ1 x
    rw [he] at hF
    have hxp : 0 < gC l ((l : ℝ) ^ (-(r / l))) x := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ hσ0 hσ1
    refine ⟨?_, ?_⟩
    · intro h0
      rw [h0, vrlaw_gC_zero l ρ hρ0 hρ1] at hF
      exact (pow_pos hxp l).ne' hF.symm
    · simp only [vr]
      rw [← hρ, hF, Real.logb_pow]
      ring
  · intro x n hx
    have hpow : ∀ m : ℕ, gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', mul_assoc, hG.2.2.2.1, ih, (_root_.GlobalTheory.PMon.Gauss.gC_basic_values l ρ hρ0 hρ1).2.1]
        ring
    simp only [vr]
    rw [← hρ, hpow n, Real.logb_mul (pow_pos (by rw [hρ]; exact Real.rpow_pos_of_pos hl0 _) n).ne' (hpos x hx).ne', Real.logb_pow,
      hρ, Real.logb_rpow hl0 hl.ne']
    ring
  · intro x _
    rfl

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActVdRMemTensorDeRhamFiltration
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilStable

theorem actVdR_mem_FilV : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (a : ℤ) (g : ↥(GK K))
    (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a →
      actVdR (P.PD K) ρ g y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a := by
  intro l _ P K V _ _ ρ a g y hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[ℚ_[l]] ⟨(P.PD K).actdR g b.1, (P.PD K).Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.FilStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocycleNegCharPowerMemCoboundaries
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.CharSplit

theorem admissibleCocycle_negCharPower_mem_coboundaries : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 1 ≤ e → e < Dt.t → ∀ z ∈ M.twistedModelAdmissibleCocycles (chr (M.ω ^ (-e))), z ∈ cob (chr (M.ω ^ (-e))) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he1 het z hz
  obtain ⟨N, b, g, hmod, hrep, hzz⟩ := _root_.GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ F M h1 h2 h3 _ z hz
  have hN : N = M.Nχ e := _root_.GlobalTheory.Models.CharModel.model_chr_eq F M h1 h2 h3 e (by omega) het N hmod
  subst hN
  apply _root_.GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB F _ z b g hrep

  have hlat := fun i => M.χ_lat e (by omega) het i

  set J : ZMod n → ℕ := fun i =>
    if Dt.ty i = LType.G then (Dt.w i).toNat else (Dt.wst i - e).toNat with hJ
  have hJG : ∀ i, Dt.ty i = LType.G → J i = (Dt.w i).toNat := fun i h => by simp [hJ, h]
  have hJB : ∀ i, Dt.ty i = LType.Bd → J i = (Dt.wst i - e).toNat := fun i h => by simp [hJ, h]

  have hsmall : ∀ i (j : ℕ), j ≤ J i → e + (j : ℤ) < l := by
    intro i j hj
    have hT := h1 i
    have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
    cases hty : Dt.ty i with
    | G =>
      obtain ⟨-, -, hw1, hw2⟩ := hw.2.2.1 hty
      rw [hJG i hty] at hj
      omega
    | Bd =>
      obtain ⟨-, -, hb1, hb2⟩ := hw.2.2.2 hty
      rw [hJB i hty] at hj
      omega
  obtain ⟨m, -, hm⟩ := GlobalTheory.PhiGam.cocycle_split_of_contracting R (F.D (chr (M.ω ^ (-e)))) (M.Nχ e) J
    (fun i => (hlat i).1) (fun i => (hlat i).2.1)
    (fun i => by rw [(hlat i).2.2.1]; exact sh_le_sh_of_le he1 _)
    (fun i j hj1 hjJ => by
      rw [(hlat i).2.2.2]
      unfold resCount
      classical
      simp only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Multiset.mem_singleton, forall_eq]
      intro hcast
      have h0 : ((e + (j : ℤ) : ℤ) : k) = 0 := by
        push_cast at hcast ⊢
        linear_combination hcast
      rw [CharP.intCast_eq_zero_iff k l] at h0
      have hle := Int.le_of_dvd (by omega) h0
      have := hsmall i j hjJ
      omega)
    b g (fun i => (hzz i).1) (fun i => (hzz i).2.1)
    (fun i => by
      have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
      cases hty : Dt.ty i with
      | G =>
        have hb := (hzz i).2.2.1 hty
        have h := (hw.2.2.1 hty).2.2.1
        have hJi : ((J i : ℕ) : ℤ) = Dt.w i := by
          rw [hJG i hty]
          omega
        rw [hJi]
        exact hb
      | Bd =>
        have hb := ((hzz i).2.2.2 hty).1
        have h := (hw.2.2.2 hty).2.2.1
        rw [(hlat i).2.2.1, sh_sh_eq] at hb
        have hJi : -((J i : ℕ) : ℤ) = -Dt.wst i + e := by
          rw [hJB i hty]
          omega
        rw [hJi]
        exact hb)
  rw [herrB_eq_range]
  refine ⟨m, ?_⟩
  rw [herrD_apply]
  exact Prod.ext (funext fun i => ((hm i).1).symm) (funext fun i => ((hm i).2).symm)

end GlobalTheory.CharSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocyclesCardLeSumDims
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.AdmBound

theorem inZZ_mono {k : Type} [Field k] {l n m r : ℕ} {R : RingPG k l} (D : ModPG R n (Vc k m)) (Dt : TopData n r)
    {N N' : Lats k n m} (h : ∀ i, N i ≤ N' i) {b g : ZMod n → Vc k m} (hz : InZZ D Dt N b g) :
    InZZ D Dt N' b g := by
  intro i
  obtain ⟨h0, h1, h2, h3⟩ := hz i
  refine ⟨h0, sh_le_sh 1 (h i) h1, fun hG => sh_le_sh _ (h i) (h2 hG), fun hB => ?_⟩
  obtain ⟨hb, x, hx, hx'⟩ := h3 hB
  exact ⟨sh_le_sh _ (pull_le_pull _ (h (i - 1))) hb, x, h i hx, sh_le_sh _ (h i) hx'⟩

theorem repr_sum {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {ι : Type} (z : ι → G → Fin A.m → k)
    (b g : ι → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a)) (a₀ : ι) (c : ι → k) (t : Finset ι) :
    Repr F A (∑ a ∈ t, c a • z a) (∑ a ∈ t, c a • b a) (∑ a ∈ t, c a • g a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := GlobalTheory.T.repr_smul_add F A (-1) (z a₀) (z a₀) (b a₀) (g a₀) (b a₀) (g a₀) (h a₀) (h a₀)
    simpa only [neg_one_smul, neg_add_cancel, Finset.sum_empty] using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.repr_smul_add F A (c a) (z a) _ (b a) (g a) _ _ (h a) ih

theorem indep_pairs {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {s : ℕ} (z : Fin s → G → Fin A.m → k)
    (b g : Fin s → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a))
    (hz : LinearIndependent k (fun a => (cob A).mkQ (z a))) :
    LinearIndependent k (fun a => (herrB (F.D A)).mkQ (b a, g a)) := by
  classical
  rw [linearIndependent_iff'] at hz ⊢
  intro t c hc a ha
  have e1 : ∑ a ∈ t, c a • (herrB (F.D A)).mkQ (b a, g a) =
      (herrB (F.D A)).mkQ (∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) := by
    rw [show ((∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) : (ZMod n → Vc k A.m) × (ZMod n → Vc k A.m)) =
        ∑ a ∈ t, c a • (b a, g a) by ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hcob := _root_.GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB F A _ _ _ (repr_sum F A z b g h a c t) hc
  refine hz t c ?_ a ha
  have e2 : ∑ a ∈ t, c a • (cob A).mkQ (z a) = (cob A).mkQ (∑ a ∈ t, c a • z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcob

private theorem exists_ne_zero_smul_mem_of_mem_span' (hψ : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi) {k : Type} [Field k] {l n m r : ℕ} [Fact l.Prime]
    [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n r)
    (N : Lats k n m) (hr : m = r) (hc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (habc : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧
      (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧
      (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = r ∧
        EPoly (D.γ i) (N i) (Dt.wst i + 1)))
    (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : ∀ a, InZZ D Dt N (z a).1 (z a).2)
    (hind : LinearIndependent k (fun a => (herrB D).mkQ (z a))) : s ≤ Dt.dsum := by
  subst hr
  exact _root_.GlobalTheory.Models.PolarBound.main hψ D ι Dt N hc h1 h2 h3 habc hsen s z hz hind

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hψ k G _ _ l n _ _ _ R F r Dt M ι hc h1 h2 h3 s z hz hind
  choose N b g hN hR hZ using fun a => _root_.GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ F M h1 h2 h3 M.T (z a) (hz a)
  obtain ⟨Nm, hNm, hmax⟩ := _root_.GlobalTheory.Models.exists_largest_model F M M.T M.Nstd M.std_model
  have hS := _root_.GlobalTheory.ModelCount.count F M h1 h2 h3 Nm hNm (hmax _ M.std_model)
  refine exists_ne_zero_smul_mem_of_mem_span' hψ (F.D M.T) ι Dt Nm M.T_m hc h1 h2 h3 (_root_.GlobalTheory.Models.model_obj_and_abc F M M.T Nm hNm).2
    (fun i => ⟨(hS i).1, (hS i).2.1, fun hB => ⟨(hS i).2.2 hB,
      GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 M.T Nm hNm i hB⟩⟩)
    s (fun a => (b a, g a)) (fun a => inZZ_mono _ _ (hmax _ (hN a)) (hZ a)) (indep_pairs F M.T z b g hR hind)

end GlobalTheory.Models.AdmBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexMatrixGaloisSubgroupApproxima
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_matrix : ∀ (l : ℕ) [Fact l.Prime] , ∃ c : ℝ, 0 < c ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (H : Subgroup ↥(GK K)) (Y : Matrix n n ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ∀ i j, ‖(Y.map (Formalism.Per.σC (g : GQ l)) - Y) i j‖ ≤ r) → ∃ Z : Matrix n n ℂ_[l], (∀ g ∈ H, Z.map (Formalism.Per.σC (g : GQ l)) = Z) ∧ ∀ i j, ‖(Y - Z) i j‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma_complete l
  refine ⟨c, hc, fun n _ _ K H Y r hr hY => ?_⟩
  have hent : ∀ i j, ∃ z : Om l, (∀ g ∈ H.map (GK K).subtype, g z = z) ∧
      ‖Y i j - (z : ℂ_[l])‖ ≤ c * r := by
    intro i j
    refine hax (H.map (GK K).subtype) (Y i j) r hr ?_
    rintro g' ⟨g, hg, rfl⟩
    have := hY g hg i j
    simpa [Matrix.sub_apply, Matrix.map_apply] using this
  choose z hz hzY using hent
  refine ⟨Matrix.of fun i j => (z i j : ℂ_[l]), ?_, ?_⟩
  · intro g hg
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.RingBasics.σC_coe]
    congr 1
    exact hz i j _ ⟨g, hg, rfl⟩
  · intro i j
    simpa [Matrix.sub_apply, Matrix.of_apply] using hzY i j

end GlobalTheory.AxLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H1_H0_transport_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  first | exact @GlobalTheory.GaloisTransport.card_H1_H0_transport | exact GlobalTheory.GaloisTransport.card_H1_H0_transport | (intros; apply GlobalTheory.GaloisTransport.card_H1_H0_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_ring_integers_compact_adic_properties : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first | exact @GlobalTheory.GoodCoeff.good_coeff_integers | exact GlobalTheory.GoodCoeff.good_coeff_integers | (intros; apply GlobalTheory.GoodCoeff.good_coeff_integers <;> assumption)
end

