module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound
section
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

noncomputable section

namespace GlobalTheory.PhaseLipschitz

def psi (k : ℝ) : ℝ → ℂ := fun t =>
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) - 1

theorem eChar_sub_one_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (k : ℝ) :
    (fun y => eChar (L y + k) - 1) = psi k ∘ ⇑L := by
  funext y
  simp only [psi, Function.comp_apply, eChar_apply, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem contDiff_psi (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi k) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold psi; fun_prop

theorem norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by
  have e : psi k t = Complex.exp (Complex.I * ((2 * Real.pi * (t + k) : ℝ) : ℂ)) - 1 := by
    simp only [psi, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]

theorem iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (psi k) = fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * (2 * Real.pi * Complex.I) ^ (j + 1) *
        Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ)) := by
  rw [iteratedDeriv_succ']
  have hd : deriv (psi k) = deriv (fun t : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp ((2 * Real.pi * Complex.I) * (t : ℂ))) := by
    unfold psi; exact deriv_sub_const_fun _
  rw [hd, ← iteratedDeriv_succ', GlobalTheory.LinPhaseSeminorm.iteratedDeriv_const_mul_cexp]

theorem norm_iteratedDeriv_psi_succ (k : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedDeriv (j + 1) (psi k) t‖ = (2 * Real.pi) ^ (j + 1) := by
  rw [iteratedDeriv_psi_succ]
  have h1 : ∀ r : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
    intro r
    rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simp only [norm_mul, norm_pow, h1]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_psi_comp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) {N i : ℕ} (hi : i ≤ N) (x : V) :
    ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ ≤
      (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * (1 + ‖x‖) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL := norm_nonneg L
  have hx := norm_nonneg x
  have hk := abs_nonneg k
  have h1N : (1 : ℝ) ≤ (1 + ‖L‖) ^ N := one_le_pow₀ (by linarith)
  rcases i with _ | j
  · rw [norm_iteratedFDeriv_zero, Function.comp_apply]
    refine (norm_psi_le k (L x)).trans ?_
    have h2 : |L x + k| ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by
      have h3 : |L x| ≤ ‖L‖ * ‖x‖ := by simpa [Real.norm_eq_abs] using L.le_opNorm x
      calc |L x + k| ≤ |L x| + |k| := abs_add_le _ _
        _ ≤ ‖L‖ * ‖x‖ + |k| := by linarith
        _ ≤ (‖L‖ + |k|) * (1 + ‖x‖) := by nlinarith
    have h4 : 2 * Real.pi ≤ (2 * Real.pi) ^ (N + 1) := le_self_pow₀ hpi (by omega)
    calc 2 * Real.pi * |L x + k| ≤ 2 * Real.pi * ((‖L‖ + |k|) * (1 + ‖x‖)) := by gcongr
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * 1) * (1 + ‖x‖) := by
          rw [mul_one]; rw [← mul_assoc]; gcongr
      _ ≤ _ := by gcongr
  · rw [L.iteratedFDeriv_comp_right (contDiff_psi k) x (i := j + 1) (by exact_mod_cast le_top)]
    have h5 : (2 * Real.pi) ^ (j + 1) ≤ (2 * Real.pi) ^ (N + 1) := pow_le_pow_right₀ hpi (by omega)
    have h6 : ‖L‖ ^ (j + 1) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by
      rw [pow_succ']
      gcongr
      · linarith
      · calc ‖L‖ ^ j ≤ (1 + ‖L‖) ^ j := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ N := pow_le_pow_right₀ (by linarith) (by omega)
    calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (psi k) (L x)‖ * ∏ _j : Fin (j + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = (2 * Real.pi) ^ (j + 1) * ‖L‖ ^ (j + 1) := by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_psi_succ]; simp
      _ ≤ (2 * Real.pi) ^ (N + 1) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * 1 := by
          rw [mul_one]; gcongr
      _ ≤ _ := by gcongr; linarith

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) : Function.HasTemperateGrowth (fun y => eChar (L y + k)) :=
  hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))

theorem coe_smulLeft_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    ⇑(SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) = fun y => (psi k ∘ ⇑L) y * f y := by
  funext y
  rw [SchwartzMap.sub_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L k), smul_eq_mul,
    ← congrFun (eChar_sub_one_eq L k) y]
  ring

theorem seminorm_smulLeft_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A N a n : ℕ} (ha : a ≤ A) (hn : n ≤ N) (L : V →L[ℝ] ℝ) (k : ℝ) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ a n (SchwartzMap.smulLeftCLM ℂ (fun y => eChar (L y + k)) f - f) ≤
      ((N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1)) * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) *
        (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f := by
  set S := (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hS
  set P := (‖L‖ + |k|) * (1 + ‖L‖) ^ N with hP
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hP0 : 0 ≤ P := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ a n _ (by positivity) fun x => ?_
  rw [coe_smulLeft_sub]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_psi k).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hx := norm_nonneg x
  have hf : ∀ j ≤ N, ‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j f x‖ ≤ 2 ^ (A + 1) * S := by
    intro j hj
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (A + 1, N)) (k := a + 1) (n := j)
      (by simp; omega) hj f x
    have h' : ‖x‖ ^ a * (1 + ‖x‖) ≤ (1 + ‖x‖) ^ (a + 1) := by
      rw [pow_succ]; gcongr; linarith
    calc _ ≤ (1 + ‖x‖) ^ (a + 1) * ‖iteratedFDeriv ℝ j f x‖ := by gcongr
      _ ≤ _ := h
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_psi_comp_le L k (N := N) (i := i) (by omega) x
    have h2 := hf (n - i) (by omega)
    have hc : (n.choose i : ℝ) ≤ 2 ^ N :=
      (by exact_mod_cast Nat.choose_le_two_pow n i : (n.choose i : ℝ) ≤ 2 ^ n).trans
        (pow_le_pow_right₀ (by norm_num) hn)
    calc ‖x‖ ^ a * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        ≤ ‖x‖ ^ a * ((2 ^ N : ℝ) * ((2 * Real.pi) ^ (N + 1) * P * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - i) f x‖) := by gcongr
      _ = 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) *
          (‖x‖ ^ a * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ _ := by gcongr
  calc ‖x‖ ^ a * ‖iteratedFDeriv ℝ n (fun y => (psi k ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ a * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ a * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (psi k ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), 2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S) :=
        Finset.sum_le_sum hterm
    _ = ((n : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by simp
    _ ≤ ((N : ℝ) + 1) * (2 ^ N * ((2 * Real.pi) ^ (N + 1) * P) * (2 ^ (A + 1) * S)) := by
        gcongr
    _ = _ := by ring

theorem continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm

theorem seminorm_smulLeft_eChar_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤
        (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set A := s.sup Prod.fst with hA
  set N := s.sup Prod.snd with hN
  set K : ℝ := (N + 1) * 2 ^ N * (2 * Real.pi) ^ (N + 1) * 2 ^ (A + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  set Q : Seminorm ℂ (SchwartzMap V ℂ) :=
    (Finset.Iic (A + 1, N)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) with hQ
  refine ⟨(C * ⟨K, hK0⟩ : NNReal) • Q, N, ?_, ?_⟩
  · exact (continuous_finset_sup_seminorm
      (fun i => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i) _).const_smul _
  · intro L k f
    set g := SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f
    have hP0 : 0 ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ N := by positivity
    have hQ0 : 0 ≤ Q f := apply_nonneg _ _
    have hs : (s.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f := by
      refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
      exact seminorm_smulLeft_sub_le (Finset.le_sup (f := Prod.fst) hi) (Finset.le_sup (f := Prod.snd) hi) L k f
    calc p g ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) g := hC g
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) g := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
      _ ≤ (C : ℝ) * (K * ((‖L‖ + |k|) * (1 + ‖L‖) ^ N) * Q f) := by gcongr
      _ = (‖L‖ + |k|) * (1 + ‖L‖) ^ N * (((C * ⟨K, hK0⟩ : NNReal) • Q) f) := by
          rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
          change (C : ℝ) * _ = _ * (((C : ℝ) * K) * Q f)
          ring

end GlobalTheory.PhaseLipschitz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
section
open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic

namespace GlobalTheory.SchwartzTranslateLip

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f := by
    funext z; simp
  have eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x
      = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    rw [efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
      (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by
    intro s hs
    set y := x + s • a with hy
    have hsa : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hx : ‖x‖ ≤ ‖y‖ + ‖a‖ := by
      have h4 := norm_sub_le y (s • a)
      rw [show y - s • a = x by simp [hy]] at h4
      linarith
    have hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]
    have ha1 : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k := by
      calc ‖x‖ ^ k ≤ ((1 + ‖a‖) * (1 + ‖y‖)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hx2 k
        _ = (1 + ‖a‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖ := by
      rw [← norm_fderiv_iteratedFDeriv]; exact (fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k)
      (n := n + 1) hk (by simp; omega) f y
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖
        ≤ ((1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k) * (‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖) := by gcongr
      _ = ‖a‖ * (1 + ‖a‖) ^ K * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by ring
      _ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by gcongr
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

theorem translate_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set K := s.sup Prod.fst
  set N := s.sup Prod.snd
  refine ⟨(C * 2 ^ K) • (Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2,
    K, ?_, fun a f => ?_⟩
  · have h : Continuous ⇑((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) :=
      Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
    rw [Seminorm.coe_smul]
    exact h.const_smul _
  set S := ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    exact seminorm_translate_sub_le K N i.1 i.2 (Finset.le_sup (f := Prod.fst) hi)
      (Finset.le_sup (f := Prod.snd) hi) a f
  have h2 := hC (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  push_cast
  calc p (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f) := h2
    _ ≤ (C : ℝ) * (‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S)) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateLip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem theta_bijective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens) :
    Function.Bijective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have P₁ := CommRingCat.isPushout_tensorProduct A Γ(T, U) B
  have P₂ : IsPushout (CommRingCat.ofHom (algebraMap A Γ(T, U)))
      (CommRingCat.ofHom (algebraMap A B))
      ((pullback.snd (str A B) g).app U)
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (pullback.fst (str A B) g).appLE ⊤ W (by simp)) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Iso.inv_comp_eq]; rfl
    · have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
      rw [← h1, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    · rw [Scheme.Hom.app_eq_appLE]; rfl
    · simp
  have e : CommRingCat.ofHom (theta A B g U) = (P₁.isoIsPushout _ _ P₂).hom := by
    apply P₁.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]
      ext c
      have := theta_tmul A B g U c 1
      simp only [map_one, mul_one] at this
      exact this
    · rw [IsPushout.inr_isoIsPushout_hom]
      ext b
      have := theta_tmul A B g U 1 b
      simp only [map_one, one_mul] at this
      exact this
  have : IsIso (CommRingCat.ofHom (theta A B g U)) := by rw [e]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (theta A B g U))

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem sections_isDomain_isFractionRing_stalk : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ _ U hU hUr h
  set ζ := genPt π with hζ
  have hcl : (U : Set Z) ⊆ closure {ζ} := by
    rintro _ hx
    obtain ⟨y, rfl⟩ := hUr hx
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map π.continuous)
  have hirr : IsIrreducible (U : Set Z) :=
    ⟨⟨ζ, h⟩, (isIrreducible_singleton.closure).isPreirreducible.open_subset U.isOpen hcl⟩
  obtain ⟨hD, -⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hirr
  refine ⟨hD, ?_⟩
  letI := algAK π U h
  have hl := hU.isLocalization_stalk ⟨ζ, h⟩
  have hbot : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal = ⊥ := by
    let q : PrimeSpectrum Γ(Z, U) := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : hU.fromSpec q ∈ U := hU.range_fromSpec.le ⟨_, rfl⟩
    have hs : hU.fromSpec (hU.primeIdealOf ⟨ζ, h⟩) ⤳ hU.fromSpec q := by
      rw [hU.fromSpec_primeIdealOf]
      exact specializes_iff_mem_closure.mpr (hcl hq)
    have hs' := hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.mp hs
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ q).mpr hs')
  have hc : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal.primeCompl = nonZeroDivisors Γ(Z, U) := by
    ext x; simp [hbot, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime at hl
  rw [hc] at hl
  exact hl

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussian
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem siegelGauss_pair_standard (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ) (hτ : GlobalTheory.IsSiegel τ) :
    (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef
  have hσ : GlobalTheory.IsSiegel σ := by
    refine ⟨?_, ?_⟩
    · exact hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])
    · have : σ.map Complex.im = τ.map Complex.im + 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [σ, Matrix.one_apply]
        · simp [σ, Matrix.one_apply, hij]
      rw [this]
      exact hτ.2.add_posSemidef Matrix.PosSemidef.one
  have hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))
      = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ)))) := by
    intro x
    rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    have e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct]
    rw [e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [map_mul, map_neg, conj_ofReal, smul_eq_mul]
    have : conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [dotProduct, map_sum]
    rw [this]
    ring_nf
    simp [I_sq]
    ring
  have hdet : (1 - I • τ) = -I • σ := by
    rw [hσdef, smul_add, smul_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [hint]
  rw [integral_const_mul, hdet, mul_pow, mul_assoc]
  have := hσ.siegelGaussIntegral_sq_mul_det
  rw [siegelGaussIntegral] at this
  rw [this, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTop
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem hom_ext_of_span_eq_top (S : Type) [CommRing S] (ι : Type) (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (Y : Scheme.{0}) (a b : Sp S ⟶ Y)
    (h : ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a =
      spMap (algebraMap S (Localization.Away (s i))) ≫ b) :
    a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) s hs).openCover
    a b h

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibreStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre : GlobalTheory.LocAcyc.KeyOrigin → GlobalTheory.LocAcyc.KeyClosedPts := by
  first | (exact @GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (exact GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin) | (intros; apply GlobalTheory.LocAcyc.Translate.keyClosedPts_of_keyOrigin  <;> assumption)
end

