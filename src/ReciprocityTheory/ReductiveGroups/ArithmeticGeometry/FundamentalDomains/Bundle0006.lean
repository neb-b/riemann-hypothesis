module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem d4l2_dual_int (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ ((NumberField.discr E : E) * t) := by
  classical
  have ht : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := h γ
    refine RingHom.mem_range.2 ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hk.symm
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
    rw [NumberField.integralBasis_apply]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have key := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 ht
  have e : Algebra.discr ℚ (NumberField.integralBasis E) • (1 : E) * t =
      (NumberField.discr E : E) * t := by
    rw [← NumberField.coe_discr, Algebra.smul_def, mul_one]
    simp
  rwa [e] at key

theorem d4l2_dual_int' (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * t) := by
  have key := d4l2_dual_int t h
  rcases Int.natAbs_eq (NumberField.discr E) with hd | hd
  · have e : ((NumberField.discr E).natAbs : E) = (NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e]
    exact key
  · have e : ((NumberField.discr E).natAbs : E) = -(NumberField.discr E : E) := by
      conv_rhs => rw [hd]
      simp
    rw [e, neg_mul]
    exact key.neg

namespace Data

variable {r : ℕ} (X : Data E r)

theorem conjugate_conjugate' (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem conj_mem_iff (φ : E →+* ℂ) : ComplexEmbedding.conjugate φ ∈ X.Ψ ↔ φ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate φ), conjugate_conjugate']

theorem sum_emb_split (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have h2 : ∑ φ ∈ X.Ψ, f (ComplexEmbedding.conjugate φ) = ∑ φ ∈ X.Ψᶜ, f φ :=
    Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate
      (fun a ha => Finset.mem_compl.2 fun hc => (X.conj_mem_iff a).1 hc ha)
      (fun a ha => (X.conj_mem_iff a).2 (Finset.mem_compl.1 ha))
      (fun a _ => conjugate_conjugate' a) (fun a _ => conjugate_conjugate' a) (fun a _ => rfl)
  have h2' : ∑ x : X.Ψ, f (ComplexEmbedding.conjugate x.1) = ∑ φ ∈ X.Ψᶜ, f φ := by
    rw [← h2]
    exact Finset.sum_coe_sort X.Ψ (fun φ => f (ComplexEmbedding.conjugate φ))
  rw [Finset.sum_add_distrib, h2', Finset.sum_coe_sort X.Ψ f, Finset.sum_add_sum_compl]

theorem trace_eq_Psi (y : E) :
    ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ τ : X.Ψ, (τ.1 y + conj (τ.1 y)) := by
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ y := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := y)
    rw [eq_ratCast] at h
    rw [h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ fun σ => rfl
  rw [h1, X.sum_emb_split (fun φ => φ y)]
  rfl

theorem re_sum_Psi (y : E) : (∑ τ : X.Ψ, τ.1 y).re = (Algebra.trace ℚ E y : ℝ) / 2 := by
  have h := congrArg Complex.re (X.trace_eq_Psi y)
  simp only [Complex.ratCast_re, Complex.re_sum, Complex.add_re, Complex.conj_re] at h
  rw [Complex.re_sum, h, Finset.sum_add_distrib]
  ring

theorem card_Psi : 2 * Fintype.card X.Ψ = finrank ℚ E := by
  have h := X.sum_emb_split (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ]
  have h' : ((Fintype.card (E →+* ℂ) : ℕ) : ℂ) = ((2 * Fintype.card X.Ψ : ℕ) : ℂ) := by
    push_cast
    linear_combination h
  exact (Nat.cast_injective h').symm

theorem exists_emb_eq (z : X.Ψ → ℂ)
    (hz : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q) :
    ∃ ω : E, ∀ τ : X.Ψ, z τ = τ.1 ω := by
  classical
  let P : (X.Ψ → ℂ) → E →ₗ[ℚ] ℝ := fun w =>
    { toFun := fun x => (∑ τ : X.Ψ, w τ * τ.1 x).re
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun q x => by
        simp only [Rat.smul_def, map_mul, map_ratCast, RingHom.id_apply]
        rw [show ∑ τ : X.Ψ, w τ * ((q : ℂ) * τ.1 x) = (q : ℂ) * ∑ τ : X.Ψ, w τ * τ.1 x by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by ring]
        rw [← Complex.ofReal_ratCast, Complex.re_ofReal_mul] }
  set b := NumberField.integralBasis E with hbdef
  have hnd := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hnd b with hddef
  choose q hq using fun i => hz (NumberField.RingOfIntegers.basis E i)
  set ω : E := ∑ i, (2 * q i) • d i with hωdef
  have htr : ∀ j, Algebra.trace ℚ E (ω * b j) = 2 * q j := by
    intro j
    have h : Algebra.traceForm ℚ E ω (b j) = 2 * q j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hωdef, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hddef,
        LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simpa [Algebra.traceForm_apply] using h
  have hbj : ∀ j, (b j : E) = ((NumberField.RingOfIntegers.basis E j : 𝓞 E) : E) := fun j => by
    rw [hbdef, NumberField.integralBasis_apply]
  set w : X.Ψ → ℂ := fun τ => z τ - τ.1 ω with hwdef
  have hPb : ∀ j, P w (b j) = 0 := by
    intro j
    show (∑ τ : X.Ψ, (z τ - τ.1 ω) * τ.1 (b j)).re = 0
    simp only [sub_mul, Finset.sum_sub_distrib, Complex.sub_re]
    have e1 : (∑ τ : X.Ψ, z τ * τ.1 (b j)).re = q j := by
      rw [hbj]
      exact hq j
    have e2 : (∑ τ : X.Ψ, τ.1 ω * τ.1 (b j)).re = q j := by
      rw [show ∑ τ : X.Ψ, τ.1 ω * τ.1 (b j) = ∑ τ : X.Ψ, τ.1 (ω * b j) from
        Finset.sum_congr rfl fun τ _ => (map_mul τ.1 ω (b j)).symm]
      rw [X.re_sum_Psi, htr]
      push_cast
      ring
    rw [e1, e2, sub_self]
  have hP0 : P w = 0 := b.ext fun j => by rw [hPb j, LinearMap.zero_apply]
  have hPw : ∀ x : E, (∑ τ : X.Ψ, w τ * τ.1 x).re = 0 := fun x => LinearMap.congr_fun hP0 x
  let W : (E →+* ℂ) → ℂ := fun φ =>
    if h : φ ∈ X.Ψ then w ⟨φ, h⟩ else conj (w ⟨ComplexEmbedding.conjugate φ, (X.conj_mem_iff φ).2 h⟩)
  have hW1 : ∀ τ : X.Ψ, W τ.1 = w τ := fun τ => by
    simp only [W, dif_pos τ.2]
  have hW2 : ∀ τ : X.Ψ, W (ComplexEmbedding.conjugate τ.1) = conj (w τ) := fun τ => by
    have hn : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := fun hc => (X.conj_mem_iff τ.1).1 hc τ.2
    simp only [W, dif_neg hn]
    exact congrArg (fun σ : X.Ψ => conj (w σ)) (Subtype.ext (conjugate_conjugate' τ.1))
  have hW : ∀ x : E, ∑ φ : E →+* ℂ, W φ * φ x = 0 := by
    intro x
    rw [X.sum_emb_split (fun φ => W φ * φ x)]
    simp only [hW1, hW2, ComplexEmbedding.conjugate_coe_eq, ← map_mul (starRingEnd ℂ),
      Complex.add_conj]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, hPw x, mul_zero,
      Complex.ofReal_zero]
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => (φ : E →* ℂ))
      (fun a a' h => RingHom.ext fun x => congrArg (fun f : E →* ℂ => f x) h)
  have hsumfun : ∑ φ : E →+* ℂ, W φ • (φ : E → ℂ) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hW x
  refine ⟨ω, fun τ => ?_⟩
  have h0 := Fintype.linearIndependent_iff.1 hli W hsumfun τ.1
  rw [hW1] at h0
  exact sub_eq_zero.1 h0

theorem nonempty_Psi : Nonempty X.Ψ := by
  have h := X.card_Psi
  have hpos : 0 < finrank ℚ E := Module.finrank_pos
  rw [← Fintype.card_pos_iff]
  omega

theorem exists_emb_int (z : X.Ψ → ℂ) (g : ℕ) (hg : 0 < g)
    (hz : ∀ γ : 𝓞 E, ∃ k : ℤ, ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) *
      (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = k) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  have hN : ∀ γ : 𝓞 E, ∃ q : ℚ, (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re = q := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    have hne : ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero hg.ne')
        (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)))
    refine ⟨(k : ℚ) / ((2 * g * (NumberField.discr E).natAbs : ℕ) : ℚ), ?_⟩
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff hne, mul_comm]
    exact hk
  obtain ⟨ω, hω⟩ := X.exists_emb_eq z hN
  refine ⟨ω, hω, ?_⟩
  have key : ∀ γ : 𝓞 E, ∃ k : ℤ,
      Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) = k := by
    intro γ
    obtain ⟨k, hk⟩ := hz γ
    refine ⟨k, ?_⟩
    have hs : ∑ τ : X.Ψ, z τ * τ.1 (γ : E) = ∑ τ : X.Ψ, τ.1 (ω * γ) :=
      Finset.sum_congr rfl fun τ _ => by rw [hω τ, map_mul]
    rw [hs, X.re_sum_Psi] at hk
    have htr : Algebra.trace ℚ E (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω * γ) =
        ((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) := by
      rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    rw [htr]
    have h2 : ((((g * (NumberField.discr E).natAbs : ℕ) : ℚ) * Algebra.trace ℚ E (ω * γ) : ℚ) : ℝ) =
        ((k : ℚ) : ℝ) := by
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast h2
  have hint := d4l2_dual_int' (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) key
  have e : (((g * (NumberField.discr E).natAbs ^ 2 : ℕ)) : E) * ω =
      ((NumberField.discr E).natAbs : E) * (((g * (NumberField.discr E).natAbs : ℕ) : E) * ω) := by
    push_cast
    ring
  rw [e]
  exact hint

end Data

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CountingExponentialSumHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Finset

theorem pow_le_exp_of_log_bound {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have hm0 : 0 < m := by linarith
  have hKm : 0 < K * m := mul_pos hK0 hm0
  have h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : N * (m / (2 * N)) = m / 2 := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hN0.le
  rw [Real.rpow_def_of_pos hKm]
  apply Real.exp_le_exp.mpr
  rw [h1]
  nlinarith

theorem counting_exponential_sum_holds : CountingExponentialSum := by
  intro K N w hK hN hw ι t ht hcount
  classical
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have ht3 : ∀ j, 3 < t j := fun j => by linarith [ht j]
  have hpi := Real.pi_gt_three
  set q : ℝ := Real.exp (2 - Real.pi) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    have h2 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hq12 : q < 1 / 2 := lt_trans hq1 he1
  have hbound : ∀ s : Finset ι, ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤
      Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
    intro s
    obtain ⟨mj, hmj⟩ : ∃ mj : ι → ℕ, mj = fun j => ⌈t j⌉₊ := ⟨_, rfl⟩
    have hmj_ge : ∀ j, t j ≤ (mj j : ℝ) := fun j => by rw [hmj]; exact Nat.le_ceil _
    have hmj_lt : ∀ j, (mj j : ℝ) < t j + 1 := fun j => by
      rw [hmj]; exact Nat.ceil_lt_add_one (by linarith [ht3 j])
    have hmj4 : ∀ j, 4 ≤ mj j := fun j => by
      have h1 : (3 : ℝ) < mj j := lt_of_lt_of_le (ht3 j) (hmj_ge j)
      have h2 : (3 : ℕ) < mj j := by exact_mod_cast h1
      omega
    have step1 : ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
      Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr (by have := hmj_lt j; nlinarith [Real.pi_pos]))
    have step2 : ∀ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y),
        Real.exp (-Real.pi * ((mj j : ℝ) - 1)) ≤ Real.exp (Real.pi - w - 2) * q ^ y := by
      intro y hy
      obtain ⟨j0, _, hj0y⟩ := Finset.mem_image.mp hy
      have hyT : w + N * Real.log (2 * K * N) + N + 2 ≤ (y : ℝ) := by
        rw [← hj0y]; linarith [ht j0, hmj_ge j0]
      have hy1 : (1 : ℝ) ≤ y := by linarith
      have hsum : ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) =
          ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1)) := by
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const,
          nsmul_eq_mul]
      have hcard : ((s.filter (fun j => mj j = y)).card : ℝ) ≤ Real.exp (2 * y - w - 2) := by
        obtain ⟨hfin, hle⟩ := hcount y hy1
        have hsub : ((s.filter (fun j => mj j = y) : Finset ι) : Set ι) ⊆ {j | t j ≤ (y : ℝ)} := by
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          show t j ≤ (y : ℝ)
          rw [← hj'.2]
          exact hmj_ge j
        have h1 : (s.filter (fun j => mj j = y)).card ≤ {j | t j ≤ (y : ℝ)}.ncard := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub hfin
        calc ((s.filter (fun j => mj j = y)).card : ℝ) ≤ ({j | t j ≤ (y : ℝ)}.ncard : ℝ) := by
              exact_mod_cast h1
          _ ≤ (K * y) ^ N := hle
          _ ≤ Real.exp (2 * y - w - 2) := pow_le_exp_of_log_bound hK hN hw hyT
      rw [hsum]
      calc ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1))
          ≤ Real.exp (2 * y - w - 2) * Real.exp (-Real.pi * ((y : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = Real.exp (Real.pi - w - 2) * q ^ y := by
            rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    have step3 : ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y ≤
        Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc ∑ y ∈ s.image mj, q ^ y ≤ ∑ y ∈ Finset.Ico 4 (s.sup mj + 1), q ^ y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro y hy
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
              rw [Finset.mem_Ico]
              exact ⟨hmj4 j, Nat.lt_succ_of_le (Finset.le_sup hj)⟩
            · intro y _ _
              exact pow_nonneg hq0 y
        _ ≤ q ^ 4 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    calc ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) := step1
      _ = ∑ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
          (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem mj hj) _).symm
      _ ≤ ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y := Finset.sum_le_sum step2
      _ ≤ _ := step3
  have hnn : ∀ j, 0 ≤ Real.exp (-Real.pi * t j) := fun j => (Real.exp_pos _).le
  have hsumm : Summable (fun j => Real.exp (-Real.pi * t j)) := summable_of_sum_le hnn hbound
  refine ⟨hsumm, ?_⟩
  have htsum : ∑' j, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) :=
    hsumm.tsum_le_of_sum_le hbound
  have h2w : (2 : ℝ) ^ (w / 2) ≤ Real.exp w := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log 2 < 2 := by linarith [Real.log_two_lt_d9]
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have hq4 : q ^ 4 = Real.exp (8 - 4 * Real.pi) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpos : 0 < 1 - q := by linarith
  calc (2 : ℝ) ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j)
      ≤ Real.exp w * (Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))) :=
        mul_le_mul h2w htsum (tsum_nonneg hnn) (Real.exp_pos _).le
    _ = Real.exp (6 - 3 * Real.pi) / (1 - q) := by
        rw [hq4, show Real.exp (6 - 3 * Real.pi) =
          Real.exp w * (Real.exp (Real.pi - w - 2) * Real.exp (8 - 4 * Real.pi)) by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
        ring
    _ < 1 / 2 := by
        have h4 : Real.exp (6 - 3 * Real.pi) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
        have h5 : 4 < Real.exp 3 := by linarith [Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)]
        have h7 : Real.exp (-3) < 1 / 4 := by
          rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 3) (by norm_num)]
          linarith
        rw [div_lt_div_iff₀ hpos (by norm_num)]
        linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_two_mul_half_degree : (Module.finrank ℚ E : ℝ) = 2 * (fdeg E : ℝ) := by
  have hf : fdeg E = Module.finrank ℚ E / 2 := rfl
  rw [hf, NumberField.IsTotallyComplex.finrank (K := E), Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

theorem one_le_field_half_degree : 1 ≤ (fdeg E : ℝ) := by
  have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h0' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast h0
  have hr : (0 : ℝ) < fdeg E := by
    have := finrank_eq_two_mul_half_degree (E := E)
    linarith
  have hn : 0 < fdeg E := by exact_mod_cast hr
  exact_mod_cast Nat.succ_le_of_lt hn

theorem field_discr_constant_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := E))

theorem rootDiscriminant_eq_rpow : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by
  unfold rdE
  rw [finrank_eq_two_mul_half_degree]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem orthogonal_component_apply (z : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) :
    X.ucomp z ξ (X.embV x) τ = Data.emb τ.1 x -
      (X.Hf z τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := rfl

theorem orthogonal_component_ne_zero (z : Frame X.Ψ r) {ξ x : Fin r → E} (hξ : ξ ≠ 0) (hx : ∀ e : E, x ≠ e • ξ)
    (τ : X.Ψ) : X.ucomp z ξ (X.embV x) τ ≠ 0 := by
  intro h
  rw [orthogonal_component_apply] at h

  obtain ⟨c, hb⟩ : ∃ c : ℂ, ∀ b, τ.1 (x b) = c * τ.1 (ξ b) := ⟨_, fun b => by
    have hb := congrFun h b
    simp only [Data.emb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
    exact sub_eq_zero.mp hb⟩
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ (funext hcon)
  have hτa : τ.1 (ξ a) ≠ 0 := (map_ne_zero τ.1).mpr ha

  apply hx (x a / ξ a)
  funext b
  apply τ.1.injective
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hb a, hb b]
  field_simp

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def CuspCoefficientBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ ν : X.Ψ → ℝ,
      DifferentiableOn ℂ (X.fj la (u 0) ν P) X.dom ∧
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fj la (u 0) ν P (rmul x b) = bchar la b * X.fj la (u 0) ν P x) ∧
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, X.fj la (u 0) ν P (X.Zb u b x) = X.fj la (u 0) ν P x

def FlowCoefficientDecay : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P)) z ≤
        2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
          sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

end

end ReciprocityTheory.ChartRestriction.G.FD
end

