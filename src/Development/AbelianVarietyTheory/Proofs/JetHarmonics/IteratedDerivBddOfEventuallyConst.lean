module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow {e : ℕ} {φ : ℝ → ℝ} (hφ : _root_.GlobalTheory.HatNF.CutPow e φ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) ∧
      ∀ x, φ x = x ^ e * h x := by
  unfold _root_.GlobalTheory.HatNF.CutPow at hφ
  obtain ⟨hφs, ⟨δ, hδ, hφ0⟩, a, R, hφR⟩ := hφ
  have hzero : ∀ x < δ, (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => (0 : ℝ) := fun x hx =>
    (eventually_lt_nhds hx).mono fun y hy => by
      show φ y / y ^ e = 0
      rw [hφ0 y hy, zero_div]
  have hconst : ∀ x, max R δ < x → (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => a := fun x hx =>
    (eventually_gt_nhds hx).mono fun y hy => by
      have hy0 : 0 < y := hδ.trans (lt_of_le_of_lt (_root_.le_max_right _ _) hy)
      have hy1 : φ y = a * y ^ e := hφR y ((_root_.le_max_left _ _).trans hy.le)
      simp only
      rw [hy1, mul_div_assoc, div_self (pow_ne_zero _ hy0.ne'), mul_one]
  have hsmooth : ContDiff ℝ ∞ (fun y => φ y / y ^ e) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x δ with hx | hx
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
    · exact hφs.contDiffAt.div (contDiffAt_id.pow e) (pow_ne_zero _ (hδ.trans_le hx).ne')
  refine ⟨fun y => φ y / y ^ e, hsmooth, fun q => ?_, fun x => ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ (max R δ))).exists_bound_of_continuousOn
      (hsmooth.continuous_iteratedDeriv q (WithTop.coe_le_coe.mpr le_top)).continuousOn
    refine ⟨max C (max |a| 0), fun x => ?_⟩
    rcases lt_or_ge x δ with hx | hx
    · rw [(hzero x hx).iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs <;> rw [norm_zero] <;> exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
    rcases le_or_gt x (max R δ) with hx' | hx'
    · exact (hC x ⟨hx, hx'⟩).trans (_root_.le_max_left _ _)
    · rw [(hconst x hx').iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs
      · rw [Real.norm_eq_abs]; exact (_root_.le_max_left _ _).trans (_root_.le_max_right _ _)
      · rw [norm_zero]; exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
  · rcases lt_or_ge x δ with hx | hx
    · show φ x = x ^ e * (φ x / x ^ e)
      rw [hφ0 x hx, zero_div, mul_zero]
    · have hx0 : x ^ e ≠ 0 := pow_ne_zero _ (hδ.trans_le hx).ne'
      show φ x = x ^ e * (φ x / x ^ e)
      rw [mul_comm, div_mul_cancel₀ (φ x) hx0]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem ckOn_smul_of_ckOn_infinite {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hc : ContDiff ℝ ∞ c) {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (n : ℕ∞)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : _root_.Formalism.FourierDecayAlt.B.CkOn n (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => c g • F g) := by
  unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF ⊢
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hF', hEq⟩ := hF g₀ hg₀
  refine ⟨U, fun g => c g • F' g, hU, hgU, ?_, fun g hgU hg => by simp only [hEq g hgU hg]⟩
  exact (hc.contDiffOn.smul hF').of_le (WithTop.coe_le_coe.mpr le_top)

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem inCC_real_smul_comp_Gf_of_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} {A : ℝ} {m : ℕ} (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f)
    (hA : _root_.Formalism.FourierDecayAlt.B.InCC A m f) :
    _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (r : ℝ) + 2) * m) m (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k r z z' g) : ℝ) : ℂ) • f g) := open PI.UnitaryCorollaryDerivatives Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity in by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
  have hcd : ContDiff ℝ ∞ (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hh.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z'))
  obtain ⟨M, hM⟩ := _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.poly_H (_root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k (0 + ρ) z z') m
  obtain ⟨K, hK0, hK⟩ := _root_.PI.UnitaryCorollaryDerivatives.CRH.main (fun g => _root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) h
    (fun _ => 2 * (0 + ρ) + 2) m M (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z') hh hb (fun w hw hne g hg => by
      have hp : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) w = (2 * (0 + ρ) + 2) * w.length := by
        simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, List.map_const', List.sum_replicate, smul_eq_mul]
        ring
      rw [hp]
      exact hM w hw hne g hg) m 0
  have hWB : _root_.PI.UnitaryCorollaryDerivatives.WB (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2))
      (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) (m + 0) K 0 := by
    unfold _root_.PI.UnitaryCorollaryDerivatives.WB
    intro u v hu hv huv g hg
    rw [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
    have hadm : _root_.PI.UnitaryCorollaryDerivatives.CRH.admitted m (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := ⟨u, v, hu, hv, huv, rfl⟩
    have hlen : (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ m := by
      simp only [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.length_append, List.length_map]; omega
    have hK1 := hK _ hadm hlen g hg
    simp only [iteratedDeriv_zero] at hK1
    have hn : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) ≤
        (List.map (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2)) (u ++ v)).sum := by
      simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.map_append, List.map_map, List.sum_append,
        List.sum_map_add, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul,
        List.length_map]
      omega
    calc _ ≤ K * _root_.Formalism.FourierDecayAlt.B.gN g ^ _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := hK1
      _ = K * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((_root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
          (by linarith [(Nat.cast_le (α := ℝ)).mpr hn])) hK0
  have cC_c_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ} {A : ℝ} {m : ℕ} {f : B.Mat k r → E} {c : ℝ} (hf : B.CCle A m f c) : 0 ≤ c := by
    have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)
    have h := hf.2 [] [] (by simp) (by simp) (by simp) 1 h1
    have hpos := gN_pos h1
    exact le_trans (mul_nonneg (Real.rpow_nonneg hpos.le _) (norm_nonneg _)) h

  have cC_smul_ck {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ} {m : ℕ∞} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
      {f : B.Mat k r → E} (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k r) (fun g => φ g • f g) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
    refine ⟨U, fun g => φ g • f' g, hU, hgU, ?_, fun g hg hgv => by simp only [hff g hg hgv]⟩
    exact ((hφ.of_le (WithTop.coe_le_coe.2 le_top)).contDiffOn).smul hf'

  have cC_Psi_ck {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ} {Q mm : ℕ} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
      {f : B.Mat k r → E} (hf : B.CkOn (mm : ℕ∞) (B.GV k r) f) {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
      (hQ : Q + w.length ≤ mm) : B.CkOn (Q : ℕ∞) (B.GV k r) (B.Rw w (fun g => φ g • f g)) := by
    have h := cC_smul_ck hφ hf
    have hmono : B.CkOn ((Q + w.length : ℕ) : ℕ∞) (B.GV k r) (fun g => φ g • f g) := by
      intro g₀ hg₀
      obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg₀
      exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hQ), hff⟩
    have hR : B.Rw w (fun g => φ g • f g) = Dw (wL [] ++ wR w) (fun g => φ g • f g) := by
      rw [← dLR_eq]
      rfl
    rw [hR]
    apply CkOn_Dw
    · intro x hx
      simp only [wL, wR, List.map_nil, List.nil_append, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact hw X hX
    · simpa [wL, wR] using hmono

  have cC_cost {j ρ : ℕ} {Q o d : ℕ} {u v u₁ v₁ w : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v)
      (hl : u.length + v.length ≤ Q) (hwo : w.length ≤ o) (hu₁ : u₁.Sublist u) (hv₁ : v₁.Sublist (v ++ w.map nrm)) :
      ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ) ≤ (j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) := by
    have hu0 : ∀ X ∈ u, costP k j ρ X = 0 := fun X hX => by simp [costP, (hu X hX).1]
    have hv0 : ∀ X ∈ v, costP k j ρ X = 0 := fun X hX => by simp [costP, (hv X hX).1]
    have hle : ∀ X, costP k j ρ X ≤ j := fun X => by
      unfold costP
      split_ifs <;> omega
    have hA : ((u₁ ++ v₁).map (costP k j ρ)).sum ≤ j * o := by
      rw [List.map_append, List.sum_append]
      have h1 : (u₁.map (costP k j ρ)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
        exact hu0 X (hu₁.subset hX)
      have h2 : (v₁.map (costP k j ρ)).sum ≤ ((v ++ w.map nrm).map (costP k j ρ)).sum :=
        (hv₁.map _).sum_le_sum (fun _ _ => Nat.zero_le _)
      have h3 : ((v ++ w.map nrm).map (costP k j ρ)).sum ≤ j * w.length := by
        rw [List.map_append, List.sum_append]
        have h0 : (v.map (costP k j ρ)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
          exact hv0 X hX
        rw [h0, zero_add, List.map_map]
        calc ((w.map (costP k j ρ ∘ nrm))).sum ≤ (w.map (fun _ => j)).sum :=
              List.sum_le_sum (fun X _ => hle _)
          _ = j * w.length := by simp [mul_comm]
      have h4 : j * w.length ≤ j * o := Nat.mul_le_mul_left _ hwo
      omega
    have hL : (u₁ ++ v₁).length ≤ Q + o := by
      have := hu₁.length_le
      have := hv₁.length_le
      simp only [List.length_append, List.length_map] at *
      omega
    have key : ((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum ≤ j * o + d * (Q + o) := by
      rw [List.sum_map_add]
      have hd : ((u₁ ++ v₁).map (fun _ => d)).sum = (u₁ ++ v₁).length * d := by simp
      rw [hd]
      have : (u₁ ++ v₁).length * d ≤ d * (Q + o) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hL
      omega
    exact_mod_cast key

  have cC_bound {j ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {d Q o mm₀ : ℕ} {A₀ : ℝ} {φ : B.Mat k (j + ρ) → ℂ}
      (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) {Cφ : ℝ}
      (hWB : WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) {w : List (B.Mat k (j + ρ))}
      (hw : ∀ X ∈ w, B.inLie k (j + ρ) X) (hwo : w.length ≤ o) (hQ : Q + o ≤ mm₀) :
      ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ (f : B.Mat k (j + ρ) → E) (c : ℝ), B.CCle A₀ mm₀ f c →
        ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
          ∀ g ∈ B.GV k (j + ρ), ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖ ≤
            CΨ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
    classical
    have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := j + ρ)
    have hCφ : 0 ≤ Cφ := by
      have h := hWB [] [] (by simp) (by simp) (by simp) 1 h1
      have hX := Real.rpow_pos_of_pos (gN_pos h1)
        ((0 : ℝ) + ((([] ++ [] : List (B.Mat k (j + ρ))).map (fun X => costP k j ρ X + d)).sum : ℕ))
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_neg_of_pos hneg hX
      linarith [norm_nonneg (B.dLR [] [] φ 1)]
    have hw'lie : ∀ X ∈ w.map nrm, B.unitLie k (j + ρ) X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact nrm_unit (hw Y hY)
    obtain ⟨a, ha⟩ : ∃ a : B.Mat k (j + ρ) → (E →L[ℂ] E),
        a = fun g => φ g • ContinuousLinearMap.id ℂ E := ⟨_, rfl⟩
    have ha_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
      rw [ha]
      exact hφ.smul contDiff_const
    have hφU : ∀ n : ℕ∞, B.CkOn n Set.univ φ := fun n g₀ _ =>
      ⟨Set.univ, φ, isOpen_univ, trivial, hφ.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top),
        fun _ _ _ => rfl⟩
    refine ⟨|((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ, mul_nonneg (by positivity) hCφ,
      fun f c hf u v hu hv hl g hg => ?_⟩
    have hc : 0 ≤ c := cC_c_nonneg hf
    have hgN := gN_ge_one hg
    have hgN0 := gN_pos hg
    have hG : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) (B.GV k (j + ρ))
        (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
      cC_Psi_ck hφ hf.1 (fun X hX => (hw'lie X hX).1) (by simp only [List.length_map]; omega)
    obtain ⟨V, G', hVo, hgV, hG'c, hG'eq⟩ := hG g hg
    have hGV : B.CkOn ((u.length + v.length : ℕ) : ℕ∞) V (B.Rw (w.map nrm) (fun g => φ g • f g)) :=
      fun g₀ hg₀ => ⟨V, G', hVo, hg₀, hG'c, hG'eq⟩
    have hscale := cA_Dw_clm (E' := E) ((((w.map nz).prod : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E) hVo
      (wL u ++ wR v) (fun x hx => ((cB_wP hu hv) x hx).1.1) (by simpa [wL, wR] using hGV) g hg hgV
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at hscale
    have hsplit : Dw (wL u ++ wR (v ++ w.map nrm)) (fun g => φ g • f g) =
        Dw (wL u ++ wR v) (B.Rw (w.map nrm) (fun g => φ g • f g)) := by
      rw [show wR (v ++ w.map nrm) = wR v ++ wR (w.map nrm) from List.map_append,
        ← List.append_assoc, Dw_append, Dw_wR]
    have hF : (fun g => φ g • f g) = ap a f := by
      funext g
      simp [ap, ha]
    have hW'lie : ∀ x ∈ wL u ++ wR (v ++ w.map nrm), B.inLie k (j + ρ) x.2 := by
      intro x hx
      simp only [wL, wR, List.map_append, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1.1
      · exact (hv X hX).1.1
      · exact (hw'lie X (List.mem_map.2 hX)).1
    have hlen : (wL u ++ wR (v ++ w.map nrm)).length = u.length + v.length + w.length := by
      simp [wL, wR]
      omega
    have hPr : Pr ∅ Set.univ ((wL u ++ wR (v ++ w.map nrm)).length : ℕ∞) a f := by
      refine ⟨fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial,
        ha_smooth.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top), fun _ _ _ => rfl⟩, fun g₀ hg₀ => ?_,
        fun g _ hg => absurd hg (Set.notMem_empty g)⟩
      obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf.1 g₀ hg₀
      refine ⟨U, f', hU, hgU, hf'.of_le ?_, hff⟩
      rw [hlen]
      exact_mod_cast (by omega : u.length + v.length + w.length ≤ mm₀)
    have hbound : ∀ w₁ w₂ : List (Bool × B.Mat k (j + ρ)), w₁.Sublist (wL u ++ wR (v ++ w.map nrm)) →
        w₂.Sublist (wL u ++ wR (v ++ w.map nrm)) → w₁.length + w₂.length = (wL u ++ wR (v ++ w.map nrm)).length →
        ‖Dw w₁ a g‖ * ‖Dw w₂ f g‖ ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
      intro w₁ w₂ hw₁ hw₂ _
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hw₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hw₂
      have hunit : ∀ X ∈ v ++ w.map nrm, B.unitLie k (j + ρ) X := by
        intro X hX
        rcases List.mem_append.1 hX with hX | hX
        · exact cB_unitLie hv X hX
        · exact hw'lie X hX
      have hA : ‖Dw (wL u₁ ++ wR v₁) a g‖ ≤ Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) := by
        have hDa := cA_Dw_clm (E := ℂ) (E' := E →L[ℂ] E)
          (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ContinuousLinearMap.id ℂ E))
          isOpen_univ (wL u₁ ++ wR v₁) (fun x hx => hW'lie x (hw₁.subset hx)) (hφU _) g hg trivial
        simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hDa
        rw [ha, hDa, norm_smul, ← dLR_eq]
        have hWB1 := hWB u₁ v₁ (fun X hX => cB_unitLie hu X (hu₁.subset hX))
          (fun X hX => hunit X (hv₁.subset hX))
          (by have := hu₁.length_le; have := hv₁.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
        have hcost := cC_cost hu hv hl hwo hu₁ hv₁ (d := d)
        have hexp : B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) ≤
            B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hgN (by linarith)
        calc ‖B.dLR u₁ v₁ φ g‖ * ‖ContinuousLinearMap.id ℂ E‖ ≤ ‖B.dLR u₁ v₁ φ g‖ * 1 :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
          _ ≤ Cφ * B.gN g ^ ((0 : ℝ) + ((((u₁ ++ v₁).map (fun X => costP k j ρ X + d)).sum : ℕ) : ℝ)) := by
              rw [mul_one]; exact hWB1
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp hCφ
      have hB : ‖Dw (wL u₂ ++ wR v₂) f g‖ ≤ c * B.gN g ^ (-A₀) := by
        rw [← dLR_eq]
        have h2 := hf.2 u₂ v₂ (fun X hX => cB_unitLie hu X (hu₂.subset hX))
          (fun X hX => hunit X (hv₂.subset hX))
          (by have := hu₂.length_le; have := hv₂.length_le; simp only [List.length_append, List.length_map] at *; omega) g hg
        rw [Real.rpow_neg hgN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgN0 _), mul_comm]
        exact h2
      calc ‖Dw (wL u₁ ++ wR v₁) a g‖ * ‖Dw (wL u₂ ++ wR v₂) f g‖
          ≤ (Cφ * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ))) * (c * B.gN g ^ (-A₀)) :=
            mul_le_mul hA hB (norm_nonneg _) (mul_nonneg hCφ (Real.rpow_nonneg hgN0.le _))
        _ = Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by
            rw [sub_eq_add_neg, Real.rpow_add hgN0 ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ)) (-A₀)]
            ring
    have hleib := leib_bound isOpen_empty (fun g _ => Or.inr trivial) g hg
      (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀)) (wL u ++ wR (v ++ w.map nrm)) a f
      hW'lie hPr hbound
    have hM : 0 ≤ Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) :=
      mul_nonneg (mul_nonneg hCφ hc) (Real.rpow_nonneg hgN0.le _)
    have hpow : (2 : ℝ) ^ (wL u ++ wR (v ++ w.map nrm)).length ≤ 2 ^ (Q + o) :=
      pow_le_pow_right₀ (by norm_num) (by rw [hlen]; omega)
    calc ‖B.dLR u v (B.Rw w (fun g => φ g • f g)) g‖
        = |((w.map nz).prod : ℝ)| * ‖Dw (wL u ++ wR (v ++ w.map nrm)) (ap a f) g‖ := by
          rw [Rw_scale, dLR_eq, hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← hF, hsplit]
      _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (wL u ++ wR (v ++ w.map nrm)).length *
            (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
          mul_le_mul_of_nonneg_left hleib (abs_nonneg _)
      _ ≤ |((w.map nz).prod : ℝ)| * (2 ^ (Q + o) *
            (Cφ * c * B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hM) (abs_nonneg _)
      _ = |((w.map nz).prod : ℝ)| * 2 ^ (Q + o) * Cφ * c *
            B.gN g ^ ((j : ℝ) * o + d * ((Q + o : ℕ) : ℝ) - A₀) := by ring
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := cC_bound (j := 0) (ρ := ρ) (E := Wq →L[ℂ] Wp) (Q := m) (o := 0)
    (mm₀ := m) (A₀ := A) hcd hWB (w := []) (fun X hX => nomatch hX) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨c, hc⟩ := id hA
  have hc' := hc
  unfold _root_.Formalism.FourierDecayAlt.B.InCC
  refine ⟨CΨ * c, ?_⟩
  unfold _root_.Formalism.FourierDecayAlt.B.CCle at hc ⊢
  refine ⟨ckOn_smul_of_ckOn_infinite hcd _ hf, fun u v hu hv huv g hg => ?_⟩
  have hIW : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k (0 + ρ)), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.unitLie k (0 + ρ) X) → _root_.Formalism.FourierDecayAlt.U.unitP k 0 ρ w :=
    fun w hw X hX => ⟨⟨(hw X hX).1, fun i b hb' _ => absurd hb' (Nat.not_lt_zero _)⟩, (hw X hX).2⟩
  have hB : ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖ ≤
      CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) :=
    hCΨ f c hc' u v (hIW u hu) (hIW v hv) huv g hg
  have hpos := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
  calc _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖
      ≤ _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        (CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A)) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hpos.le _)
    _ = CΨ * c := by
        rw [mul_comm, mul_assoc, ← Real.rpow_add hpos]
        have h0 : ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) +
            (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) = 0 := by
          simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [h0, Real.rpow_zero, mul_one]


open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem _root_.GlobalTheory.HatNF.mulG_ckOn_inCC : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), ∀ (e m : ℕ) (φ : ℝ → ℝ)
    (f : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.GlobalTheory.HatNF.CutPow e φ →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) f → _root_.Formalism.FourierDecayAlt.B.InCC A m f →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (_root_.GlobalTheory.HatNF.mulG Bs φ f) ∧
      _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m (_root_.GlobalTheory.HatNF.mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e m φ f A hφ hf hA
  have hval : _root_.GlobalTheory.HatNF.mulG Bs φ f =
      fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g := rfl
  obtain ⟨h, hh, hb, hφh⟩ := exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow hφ
  have hφs : ContDiff ℝ ∞ φ := by
    unfold _root_.GlobalTheory.HatNF.CutPow at hφ
    exact hφ.1
  have hfun : _root_.GlobalTheory.HatNF.mulG Bs φ f = fun g =>
      ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) •
        (((h (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g) := by
    rw [hval]
    funext g
    rw [smul_smul, ← Complex.ofReal_mul, ← hφh]
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact ckOn_smul_of_ckOn_infinite (c := fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hφs.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))) ⊤ hf
  · rw [hfun]
    obtain ⟨c, hc⟩ := inCC_real_smul_comp_Gf_of_inCC Bs.z Bs.z' hh hb hf hA
    have hpd := (show (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F →
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r)
          (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g)) ∧
      ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (b : ℝ),
        _root_.Formalism.FourierDecayAlt.B.CCle (A' + (((2 * P.r + 2) * e : ℕ) : ℝ)) m' F b →
          _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g) (K * b) from
      _root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow (Wp := Wp) (Wq := Wq) Bs.z Bs.z' e).2
    obtain ⟨K, -, hK⟩ := hpd (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m
    refine ⟨K * c, hK _ c ?_⟩
    have hA' : A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m) + (((2 * P.r + 2) * e : ℕ) : ℝ) =
        A - (2 * (P.r : ℝ) + 2) * m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hA']
    exact hc

end

end GlobalTheory.HatNF
