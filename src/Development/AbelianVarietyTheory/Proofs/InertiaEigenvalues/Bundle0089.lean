module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNorm
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Pw

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_pw_natCast (n : ℕ) (x : F) : pw p (n : ℤ) x = x ^ p ^ n := by
  simp [pw]

theorem coefDet_pw_pow_p (k : ℤ) (x : F) : pw p k x ^ p = pw p (k + 1) x := by
  unfold pw
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos (by omega), ← pow_mul, ← pow_succ]
    congr 2; omega
  · rw [if_neg hk]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-k).toNat = n + 1 := ⟨(-k).toNat - 1, by omega⟩
    rw [hn, Function.iterate_succ_apply']
    have e : ((frobeniusEquiv F p).symm (((frobeniusEquiv F p).symm)^[n] x)) ^ p =
        ((frobeniusEquiv F p).symm)^[n] x := by
      have := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[n] x)
      rwa [frobenius_def] at this
    rw [e]
    by_cases hk1 : 0 ≤ k + 1
    · rw [if_pos hk1]
      have hn0 : n = 0 := by omega
      have h0 : (k + 1).toNat = 0 := by omega
      rw [hn0, h0]; simp
    · rw [if_neg hk1]; congr 1; omega

theorem coefDet_pw_pow (k : ℤ) (x : F) (a : ℕ) : pw p k x ^ p ^ a = pw p (k + a) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, coefDet_pw_pow_p]
    congr 1; push_cast; ring

end Pw

section Det

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem coefDet_det_scaled {h : ℕ} (a lam y : Fin h → F) :
    (Matrix.of fun r j : Fin h => (a r * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))).det =
      (∏ r, a r ^ p ^ (h - (r : ℕ))) * ((∏ j, y j ^ p ^ h) *
        (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det) := by
  rw [← Matrix.det_mul_row (fun j => y j ^ p ^ h), ← Matrix.det_mul_column (fun r => a r ^ p ^ (h - (r : ℕ)))]
  congr 1; ext r j
  simp only [Matrix.of_apply]
  have key : (y j ^ p ^ (r : ℕ)) ^ p ^ (h - (r : ℕ)) = y j ^ p ^ h := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le]
  rw [mul_pow, mul_pow, key]
  ring

theorem coefDet_det_rev {h : ℕ} (lam : Fin h → F) :
    (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin h)) : ℤ) : F) *
        (Matrix.of fun r j : Fin h => (lam j ^ p) ^ p ^ (r : ℕ)).det := by
  rw [← Matrix.det_permute]
  congr 1; ext r j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.revPerm_apply, Fin.val_rev, id]
  rw [← pow_mul, ← pow_succ']
  congr 2; have := r.isLt; omega

theorem coefDet_orth_pow {h : ℕ} (lam : Fin h → F) (hO : Orth p lam) : Orth p (fun j => lam j ^ p) := by
  intro c j hc
  have h1 := hO c j hc
  have e : (∑ i, (c i : F) * lam i) ^ p = ∑ i, (c i : F) * lam i ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← frobenius_def (R := F) p, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, frobenius_def]
  show ‖lam j ^ p‖ ≤ ‖∑ i, (c i : F) * lam i ^ p‖
  rw [← e, norm_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 p

theorem coefDet_norm_sign_cast {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) :
    ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

end Det

end GlobalTheory.PMonE

end

namespace GlobalTheory.PMonE
open Finset

theorem coefB_det (F : Type) [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] (h : ℕ) (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hl : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hA : Antitone (fun j => ‖lam j‖)) (hO : Orth p lam) (L U : ℕ) :
    ‖(coefB p ϖ lam π L U L).det‖ = 1 ∧ (coefB p ϖ lam π L U 0).det ≠ 0 := by
  set c : Fin h → F := fun r => lam r * π r ^ p ^ (r : ℕ) with hc
  have hc0 : ∀ r, c r ≠ 0 := fun r => mul_ne_zero (hl r) (pow_ne_zero _ (hπ r))
  have hA' : Antitone (fun j => ‖(fun j => lam j ^ p) j‖) := fun i j hij => by
    simp only [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hA hij) p
  have hDn : ‖(Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det‖ =
      ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
    rw [coefDet_det_rev, norm_mul, coefDet_norm_sign_cast, one_mul]
    have hM := mooreNorm F p h (fun j => lam j ^ p) hA' (coefDet_orth_pow p lam hO)
    rw [hM]
    refine prod_congr rfl fun j _ => ?_
    rw [norm_pow, ← pow_mul, ← pow_succ']; congr 2; have := j.isLt; omega
  have hD0 : (Matrix.of fun r j : Fin h => lam j ^ p ^ (h - (r : ℕ))).det ≠ 0 := by
    rw [← norm_ne_zero_iff, hDn]
    exact (prod_pos fun j _ => pow_pos (norm_pos_iff.mpr (hl j)) _).ne'
  constructor
  · have e : coefB p ϖ lam π L U L = Matrix.of fun r j : Fin h =>
        ((c r)⁻¹ * (lam j * π j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, le_add_iff_nonneg_right, zero_le, if_true, sub_self, neg_zero,
        zpow_zero, mul_one, zero_mul, add_zero, coefDet_pw_natCast, hc]
      rw [div_eq_inv_mul]
    rw [e, coefDet_det_scaled, norm_mul, norm_mul, norm_prod, norm_prod, hDn]
    have hX : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) =
        (∏ j : Fin h, ‖π j‖ ^ p ^ h) * ∏ j : Fin h, ‖lam j‖ ^ p ^ (h - (j : ℕ)) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun r _ => ?_
      rw [hc]
      simp only
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' r.isLt.le, mul_comm]
    have hX0 : ∏ r : Fin h, ‖c r‖ ^ p ^ (h - (r : ℕ)) ≠ 0 :=
      (prod_pos fun r _ => pow_pos (norm_pos_iff.mpr (hc0 r)) _).ne'
    simp only [norm_pow, norm_inv, inv_pow]
    rw [prod_inv_distrib, ← hX, inv_mul_cancel₀ hX0]
  · set y : Fin h → F := fun j => pw p (-((L : ℤ) * h)) (π j) with hy
    have hy0 : ∀ j, y j ≠ 0 := by
      intro j hyj
      have h1 := coefDet_pw_pow p (-((L : ℤ) * h)) (π j) (L * h)
      have h0 : pw p (0 : ℤ) (π j) = π j := by simp [pw]
      rw [show pw p (-((L : ℤ) * h)) (π j) = y j from rfl, hyj,
        zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
      push_cast at h1
      rw [neg_add_cancel, h0] at h1
      exact hπ j h1.symm
    have e : coefB p ϖ lam π L U 0 = Matrix.of fun r j : Fin h =>
        ((ϖ ^ L / c r) * (lam j * y j ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) := by
      ext r j
      simp only [coefB, Matrix.of_apply, term, zero_le, if_true, hc, hy, coefDet_pw_pow]
      have e1 : ((r : ℕ) : ℤ) + (((0 : ℕ) : ℤ) - L) * h = -((L : ℤ) * h) + ((r : ℕ) : ℤ) := by
        push_cast; ring
      have e2 : ϖ ^ (-(((0 : ℕ) : ℤ) - L)) = ϖ ^ L := by
        rw [show -(((0 : ℕ) : ℤ) - L) = (L : ℤ) by push_cast; ring, zpow_natCast]
      rw [e1, e2]
      congr 1
      ring
    rw [e, coefDet_det_scaled]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hϖ) (hc0 r)))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)) hD0)

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicator
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourGUnit

variable {F : Type} [NontriviallyNormedField F]

theorem integral_ball_char {r : ℕ} [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] [ProperSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) (v : Fin r → F) :
    ∫ x, {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => μ) =
      {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator 1 v := by
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  have hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1 := by
    ext x; simp [S, Metric.mem_closedBall]
  have hSm : MeasurableSet S := hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, integral_indicator hSm,
      setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]
    · rw [Measure.real, hS, Measure.pi_pi]
      simp [hvol]
    · apply hψ.1
      rw [dotProduct]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro i _
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hv i)
  · rw [Set.indicator_of_notMem hv]
    obtain ⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by
      simp only [S, Set.mem_setOf_eq, not_forall, not_le] at hv; exact hv
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    have hvi : v i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; linarith
    set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def
    have hz₀ : z₀ ∈ S := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hz₀def, Pi.single_eq_same]
        apply hx₀'
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hi
      · rw [hz₀def, Pi.single_eq_of_ne hj, norm_zero]; exact zero_le_one
    have hχ : ψ (z₀ ⬝ᵥ v) ≠ 1 := by
      rw [hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]
      exact hx₀
    have hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S := fun a b ha hb i =>
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    have key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) =
        S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v) := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct,
          AddChar.map_add_eq_mul]
      · have hneg : -z₀ ∈ S := fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j
        have : z + z₀ ∉ S := fun h => hz (by simpa using hadd _ _ h hneg)
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]
    have h := integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ)
      (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀
    simp only [key, integral_mul_const] at h
    have h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hχ

end GlobalTheory.JR.FourGUnit

namespace GlobalTheory.JR


open FourGUnit in
theorem fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]

end GlobalTheory.JR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstant
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourU_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f →
    (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by
  intro F E _ _ _ _ hU r M ψ hψ htr f hf ⟨U, hU0, hUf⟩
  haveI : IsUltrametricDist E := Unram.ultraE (F := F)

  have htr1 : ∀ d : E, ‖d‖ ≤ 1 → ψ (Algebra.trace F E d) = 1 := by
    intro d hd
    apply hψ.1
    have h1 : ‖algebraMap F E (Algebra.trace F E d)‖ ≤ 1 := by
      rw [htr]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd ?_)
      rw [Unram.norm_star (F := F)]; exact hd
    rwa [norm_algebraMap'] at h1

  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin r → E)).1
    ((hf.2.isCompact.image (continuous_fst.comp continuous_snd)).isBounded)
  set R' : ℝ := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro X₀
  have hcont : Continuous fun X : Hn r F E => ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) :=
    (continuous_fst.sub continuous_const).prodMk (continuous_const.prodMk
      ((continuous_snd.comp continuous_snd).sub continuous_const))
  have hV1 : ∀ᶠ X in 𝓝 X₀, ((X.1 - X₀.1, (0 : Fin r → E), X.2.2 - X₀.2.2) : Hn r F E) ∈ U := by
    have : ((X₀.1 - X₀.1, (0 : Fin r → E), X₀.2.2 - X₀.2.2) : Hn r F E) = 0 := by
      ext <;> simp
    exact hcont.continuousAt.preimage_mem_nhds (by rw [this]; exact hU0)
  have hV2 : ∀ᶠ X in 𝓝 X₀, X.2.1 ∈ Metric.closedBall X₀.2.1 (1 / R') :=
    (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ (by positivity))
  filter_upwards [hV1, hV2] with X hX1 hX2
  unfold fourU
  congr 1
  funext c
  have hfe : f (X.1, c, X.2.2) = f (X₀.1, c, X₀.2.2) := by
    have := hUf (X₀.1, c, X₀.2.2) _ hX1
    rw [← this]; congr 1; ext <;> simp
  rw [hfe]
  by_cases h0 : f (X₀.1, c, X₀.2.2) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hc : ‖c‖ ≤ R := by
    have hmem : c ∈ (fun X : Hn r F E => X.2.1) '' tsupport f :=
      ⟨(X₀.1, c, X₀.2.2), subset_tsupport _ h0, rfl⟩
    simpa using hR hmem
  have hs : ‖star c ⬝ᵥ (X.2.1 - X₀.2.1)‖ ≤ 1 := by
    have hd : ‖X.2.1 - X₀.2.1‖ ≤ 1 / R' := by rw [← dist_eq_norm]; exact hX2
    unfold dotProduct
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, Pi.star_apply, Unram.norm_star (F := F)]
    have h1 : ‖c i‖ ≤ R' := (norm_le_pi_norm c i).trans (hc.trans (le_max_left _ _))
    have h2 : ‖(X.2.1 - X₀.2.1) i‖ ≤ 1 / R' := (norm_le_pi_norm _ i).trans hd
    calc ‖c i‖ * ‖(X.2.1 - X₀.2.1) i‖ ≤ R' * (1 / R') :=
          mul_le_mul h1 h2 (norm_nonneg _) hR'pos.le
      _ = 1 := by field_simp
  have hsplit : star c ⬝ᵥ X.2.1 = star c ⬝ᵥ X₀.2.1 + star c ⬝ᵥ (X.2.1 - X₀.2.1) := by
    rw [dotProduct_sub]; ring
  rw [hsplit, map_add (f := _), AddChar.map_add_eq_mul, htr1 _ hs, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjectiveStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => Img.isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← Img.map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← Img.map_sh, ← Img.map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← Img.map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem
section
noncomputable section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Sat
variable {k : Type} [Field k]

section
variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}

end

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]
  {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem comap_sh (f : W →ₗ[k⸨X⸩] V) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).comap (f.restrictScalars k⟦X⟧) = sh a (N.comap (f.restrictScalars k⟦X⟧)) := by
  ext x
  simp [mem_sh_iff_smul_mem]

theorem isLat_comap (f : W →ₗ[k⸨X⸩] V) (hf : Function.Injective f) {N : Submodule k⟦X⟧ V} (hN : IsLat N) :
    IsLat (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.LatticeComap.main f hf hN

variable [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}

theorem comap_pull (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (hf : Function.Injective f) (hg : Function.Injective g) (hφ : ∀ x, g (D'.φ i x) = D.φ i (f x))
    {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) :=
  _root_.GlobalTheory.IndependentSpanDual.comap_pull D D' i f g hf hg hφ hN

theorem main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
    {n : ℕ} [NeZero n]
    {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V]
    {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
    [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
    [FiniteDimensional k⸨X⸩ W]
    (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V),
    (∀ i, Function.Injective (f i)) →
    (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) →
    (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) →
    ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
      (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
      (∀ i, IsLat ((N i).comap ((f i).restrictScalars k⟦X⟧))) ∧
      CondAB D'.φ w w' (fun i => (N i).comap ((f i).restrictScalars k⟦X⟧)) ∧
      ∀ i, CondC (D'.γ i) ((N i).comap ((f i).restrictScalars k⟦X⟧)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC
  refine ⟨fun i => isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    rw [← h, ← comap_sh, ← comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · rw [← comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx

end GlobalTheory.PhiGam.Sat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusEqOneIffStatement
section
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_eq_one_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ t : T, ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  first | exact @GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | exact GlobalTheory.TorusKer.valsAt_torus_eq_one_iff | (intros; apply GlobalTheory.TorusKer.valsAt_torus_eq_one_iff <;> assumption)
end

