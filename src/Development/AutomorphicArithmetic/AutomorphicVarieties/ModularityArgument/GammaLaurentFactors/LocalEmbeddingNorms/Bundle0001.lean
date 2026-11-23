module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CrossGOf
section
noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Inf

private lemma zero_of_open {f : ℂ → ℂ} (hf : Differentiable ℂ f) {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (h : ∀ s ∈ U, f s = 0) : f = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have h0 : f =ᶠ[nhds z] 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h
  funext s
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ s)

private lemma zero_of_left {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, s.re < c → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | s.re < c}) (isOpen_lt Complex.continuous_re continuous_const)
    (z := ((c - 1 : ℝ) : ℂ)) (by simp) h

private lemma zero_of_right {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ) (h : ∀ s : ℂ, c < s.re → f s = 0) : f = 0 :=
  zero_of_open hf (U := {s : ℂ | c < s.re}) (isOpen_lt continuous_const Complex.continuous_re)
    (z := ((c + 1 : ℝ) : ℂ)) (by simp) h

private lemma mul_ne {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (f0 : f ≠ 0) (g0 : g ≠ 0) :
    (fun s => f s * g s) ≠ 0 := by
  intro h
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f0
  refine g0 (zero_of_open hg (U := {s | f s ≠ 0}) (isOpen_ne_fun hf.continuous continuous_const) hz fun s hs => ?_)
  exact (mul_eq_zero.mp (congrFun h s)).resolve_left hs

private lemma shift_ne {f : ℂ → ℂ} (f0 : f ≠ 0) : (fun s => f (s + 1)) ≠ 0 := by
  intro h
  apply f0
  funext s
  simpa using congrFun h (s - 1)

private lemma cpow_eq {q : ℝ} (hq : 1 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) = Complex.exp (((-Real.log q : ℝ) : ℂ) * (s + 0)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (by linarith)]
  congr 1
  push_cast
  ring

private lemma poly_zero {q : ℝ} (hq : 1 < q) (Q : ℂ[X]) (h : ∀ s : ℂ, Q.eval ((q : ℂ) ^ (-s)) = 0) : Q = 0 := by
  have hl : ((Real.log q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
  refine (Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun x hx => ?_
  have hx' : x ≠ 0 := hx
  have := h (-(Complex.log x / (Real.log q : ℝ)))
  rw [cpow_eq hq] at this
  have e : ((-Real.log q : ℝ) : ℂ) * (-(Complex.log x / (Real.log q : ℝ)) + 0) = Complex.log x := by
    rw [Complex.ofReal_neg]
    field_simp
    ring
  rw [e, Complex.exp_log hx'] at this
  exact this

private lemma poly_fun_ne {β : ℂ[X]} (h : β ≠ 0) : (fun s : ℂ => β.eval s) ≠ 0 := fun h0 =>
  h (Polynomial.funext fun s => by simpa using congrFun h0 s)

private lemma fac_eq {q : ℝ} (hq : 1 < q) (c : ℂ) (t : ℝ) (P : ℂ[X]) (s : ℂ) :
    fac c t q P s = c * Complex.exp (t * s) * P.eval ((q : ℂ) ^ (-s)) / P.eval ((q : ℂ) * (q : ℂ) ^ (-s)) ∧
    fac c t q P (s + 1) = c * (Complex.exp (t * s) * Complex.exp t) * P.eval ((q : ℂ)⁻¹ * (q : ℂ) ^ (-s)) /
      P.eval ((q : ℂ) ^ (-s)) := by
  have h0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  constructor
  · rw [fac, sub_eq_add_neg, Complex.cpow_add _ _ h0, Complex.cpow_one]
  · rw [fac, mul_add, mul_one, Complex.exp_add, show (1 : ℂ) - (s + 1) = -s by ring,
      show -(s + 1) = -1 + -s by ring, Complex.cpow_add _ _ h0, Complex.cpow_neg_one]

theorem crossGOf : CrossGOf := by
  rintro ⟨hd, hmul, hc, -, hpe⟩ hind hsec L L' β β' q P P' hq β0 β'0 P1 P'1
    ⟨Z₀, W₀, A₀, B₀, k₀, l₀, m₀, t₀, c₀, dZ₀, dW₀, Z₀0, k₀0, l₀0, hr₀, hl₀⟩
    ⟨Z₁, W₁, A₁, B₁, k₁, l₁, m₁, t₁, c₁, dZ₁, dW₁, Z₁0, k₁0, l₁0, hr₁, hl₁⟩
  have dsh : ∀ {f : ℂ → ℂ}, Differentiable ℂ f → Differentiable ℂ fun s => f (s + 1) := fun hf =>
    hf.comp (differentiable_id.add_const 1)
  have eP : ∀ Q : ℂ[X], IsExp fun s : ℂ => Q.eval ((q : ℂ) ^ (-s)) := fun Q => by
    simp only [cpow_eq hq]
    exact hpe Q _ 0
  have nP : ∀ Q : ℂ[X], Q.eval 0 ≠ 0 → (fun s : ℂ => Q.eval ((q : ℂ) ^ (-s))) ≠ 0 := fun Q hQ h =>
    hQ (by rw [poly_zero hq Q fun s => congrFun h s]; simp)
  have hR : (fun s => k₁ * β'.eval s * W₀ s * Z₁ s - k₀ * β.eval s * W₁ s * Z₀ s) = 0 := by
    refine zero_of_right ?_ (max c₀ c₁) fun s hs => ?_
    · have := β.differentiable
      have := β'.differentiable
      fun_prop
    · obtain ⟨a1, a2⟩ := hr₀ s (lt_of_le_of_lt (le_max_left _ _) hs)
      obtain ⟨b1, b2⟩ := hr₁ s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [a1, a2, b1, b2]
      ring
  set R : ℂ[X] := P.comp (C (q : ℂ)⁻¹ * X) * P.comp (C (q : ℂ) * X) * P' ^ 2 with hRdef
  set R' : ℂ[X] := P'.comp (C (q : ℂ)⁻¹ * X) * P'.comp (C (q : ℂ) * X) * P ^ 2 with hR'def
  set E : ℂ[X] := P * P.comp (C (q : ℂ) * X) * P' * P'.comp (C (q : ℂ) * X) with hEdef
  set a : ℂ := k₁ * l₀ * Complex.exp t₀ with ha
  set b : ℂ := k₀ * l₁ * Complex.exp t₁ with hb
  have a0 : a ≠ 0 := mul_ne_zero (mul_ne_zero k₁0 l₀0) (Complex.exp_ne_zero _)
  set U : ℂ → ℂ := fun s => (C a * R).eval ((q : ℂ) ^ (-s)) with hU
  set V : ℂ → ℂ := fun s => (C b * R').eval ((q : ℂ) ^ (-s)) with hV
  have eU : IsExp U := eP _
  have eV : IsExp V := eP _
  have U0 : U ≠ 0 := nP _ (by simpa [hRdef, eval_comp, P1, P'1] using a0)
  have E0 := nP E (by simp [hEdef, eval_comp, P1, P'1])
  have dE := hd _ (eP E)
  set c : ℝ := -(max c₀ c₁) - 1 with hcdef
  have l0 : ∀ s : ℂ, s.re < c → s.re < -c₀ ∧ s.re < -c₁ ∧ (s + 1).re < -c₁ := fun s hs => by
    have := le_max_left c₀ c₁
    have := le_max_right c₀ c₁
    simp only [Complex.add_re, Complex.one_re]
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  have dF : Differentiable ℂ fun s => β'.eval s * U s - β.eval s * V s :=
    (β'.differentiable.mul (hd _ eU)).sub (β.differentiable.mul (hd _ eV))
  have dG : Differentiable ℂ fun s => Z₀ s * Z₁ s * Z₁ (s + 1) := (dZ₀.mul dZ₁).mul (dsh dZ₁)
  have G0 : (fun s => Z₀ s * Z₁ s * Z₁ (s + 1)) ≠ 0 :=
    mul_ne (dZ₀.mul dZ₁) (dsh dZ₁) (mul_ne dZ₀ dZ₁ Z₀0 Z₁0) (shift_ne Z₁0)
  have hF : (fun s => β'.eval s * U s - β.eval s * V s) = 0 := by
    by_contra F0
    refine mul_ne (dG.mul dE) dF (mul_ne dG dE G0 E0) F0 (zero_of_left ((dG.mul dE).mul dF) c fun s hs => ?_)
    obtain ⟨s1, s3, s4⟩ := l0 s hs
    obtain ⟨a3, a4⟩ := hl₀ s s1
    obtain ⟨b3, b4⟩ := hl₁ s s3
    obtain ⟨e3, -⟩ := hl₁ (s + 1) s4
    have h := congrFun hR s
    by_contra hne
    simp only [Pi.mul_apply, mul_eq_zero, not_or] at hne
    obtain ⟨⟨⟨⟨n0, n1⟩, n2⟩, n3⟩, n4⟩ := hne
    apply n4
    have y1 : L' (s + 1) ≠ 0 := fun h0 => n2 (by rw [e3, h0]; simp)
    have y2 : L' s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y3 : B₀ s ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp)
    have y4 : B₁ s ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp)
    have y5 : m₀ ≠ 0 := fun h0 => n0 (by rw [a3, h0]; simp [fac])
    have y6 : m₁ ≠ 0 := fun h0 => n1 (by rw [b3, h0]; simp [fac])
    have y7 := Complex.exp_ne_zero (t₀ * s)
    have y8 := Complex.exp_ne_zero (t₁ * s)
    simp only [hEdef, eval_mul, eval_comp, eval_C, eval_X, mul_eq_zero, not_or] at n3
    obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩ := n3
    simp only [a3, a4, b3, b4, Pi.zero_apply, (fac_eq hq _ _ _ s).1, (fac_eq hq _ _ _ s).2] at h
    simp only [hU, hV, hRdef, hR'def, ha, hb, eval_mul, eval_comp, eval_C, eval_X, eval_pow]
    generalize (q : ℂ) ^ (-s) = x at *
    generalize P.eval x = p1 at *
    generalize P'.eval x = p2 at *
    generalize P.eval ((q : ℂ) * x) = p3 at *
    generalize P'.eval ((q : ℂ) * x) = p4 at *
    generalize P.eval ((q : ℂ)⁻¹ * x) = p5 at *
    generalize P'.eval ((q : ℂ)⁻¹ * x) = p6 at *
    have y : L' (s + 1) * L' s * B₀ s * B₁ s * m₀ * m₁ * Complex.exp (t₀ * s) * Complex.exp (t₁ * s) ≠ 0 := by
      simp [y1, y2, y3, y4, y5, y6]
    refine mul_left_cancel₀ y ?_
    have h2 := congrArg (· * (p1 * p2 * p3 * p4)) h
    simp only [zero_mul] at h2
    rw [mul_zero, ← h2]
    field_simp
  obtain ⟨u, v, u0, huv⟩ := hind β' β U V eU eV U0 fun s => sub_eq_zero.mp (congrFun hF s)
  have v0 : v ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (C_ne_zero.mpr u0) β'0 (by simpa using huv)
  have hK : (fun s : ℂ => (C v * (C a * R) - C u * (C b * R')).eval ((q : ℂ) ^ (-s))) = 0 := by
    by_contra K0
    refine mul_ne β.differentiable (hd _ (eP _)) (poly_fun_ne β0) K0 (funext fun s => ?_)
    have h1 := congrFun hF s
    have h2 := congrArg (Polynomial.eval s) huv
    simp only [hU, hV, eval_mul, eval_C, eval_sub, Pi.zero_apply] at h1 h2 ⊢
    linear_combination u * h1 - (a * R.eval ((q : ℂ) ^ (-s))) * h2
  have hK' := poly_zero hq _ fun s => congrFun hK s
  refine hsec q hq P P' (u * b / (v * a)) P1 P'1 ?_
  have hva : (C (v * a) : ℂ[X]) ≠ 0 := C_ne_zero.mpr (mul_ne_zero v0 a0)
  change R = C _ * R'
  clear_value R R' U V a b
  refine mul_left_cancel₀ hva ?_
  rw [← mul_assoc (C (v * a)), ← C_mul, mul_div_cancel₀ _ (mul_ne_zero v0 a0), C_mul (a := v), C_mul (a := u)]
  linear_combination hK'

end UpperTheory.V.Z.Gam
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
section
noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

private theorem ne_zero_sub {f : ℂ → ℂ} (h : f ≠ 0) (z : ℂ) : (fun s => f (s - z)) ≠ 0 := by
  intro h0
  apply h
  funext s
  have := congrFun h0 (s + z)
  simpa using this

private theorem mul_ne_zero_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  intro hfg
  apply hg0
  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf0 (funext hcon)
  have hev : ∀ᶠ z in nhds z₀, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hg_ev : g =ᶠ[nhds z₀] 0 := hev.mono fun z hz => by
    have hz' := congrFun hfg z
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hz'
    exact hz'.resolve_left hz
  have han : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hg_ev
  funext z
  exact heq (Set.mem_univ z)

private theorem fac_mul (c c' : ℂ) (t t' q : ℝ) (P P' : ℂ[X]) (s : ℂ) :
    fac (c * c') (t + t') q (P * P') s = fac c t q P s * fac c' t' q P' s := by
  simp only [fac, eval_mul]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

private theorem fac_sub (c : ℂ) (t : ℝ) {q : ℝ} (hq : 1 < q) (P : ℂ[X]) (z s : ℂ) :
    fac (c * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) s = fac c t q P (s - z) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  unfold fac
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  rw [← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0, mul_assoc c (Complex.exp _), ← Complex.exp_add]
  have e1 : z + -s = -(s - z) := by ring
  have e2 : z + (1 - s) = 1 - (s - z) := by ring
  have e3 : -((t : ℂ) * z) + t * s = t * (s - z) := by ring
  rw [e1, e2, e3]

theorem pairGOps : PairGOps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1, 0, 0, differentiable_const _,
      differentiable_const _, ?_, one_ne_zero, one_ne_zero, ?_, ?_⟩
    · intro h
      simpa using congrFun h 0
    · intro s _
      simp [fac]
    · intro s _
      simp [fac]
  · intro L₁ L₁' L₂ L₂' β₁ β₂ q P₁ P₂ h₁ h₂
    obtain ⟨Z₁, W₁, A₁, B₁, k₁, k₁', c₁, t₁, d₁, hZ₁, hW₁, hZ₁0, hk₁, hk₁', hu₁, hl₁⟩ := h₁
    obtain ⟨Z₂, W₂, A₂, B₂, k₂, k₂', c₂, t₂, d₂, hZ₂, hW₂, hZ₂0, hk₂, hk₂', hu₂, hl₂⟩ := h₂
    refine ⟨Z₁ * Z₂, W₁ * W₂, A₁ * A₂, B₁ * B₂, k₁ * k₂, k₁' * k₂', c₁ * c₂, t₁ + t₂, max d₁ d₂,
      hZ₁.mul hZ₂, hW₁.mul hW₂, mul_ne_zero_entire hZ₁ hZ₂ hZ₁0 hZ₂0, mul_ne_zero hk₁ hk₂,
      mul_ne_zero hk₁' hk₂', ?_, ?_⟩
    · intro s hs
      obtain ⟨e₁, f₁⟩ := hu₁ s (lt_of_le_of_lt (le_max_left _ _) hs)
      obtain ⟨e₂, f₂⟩ := hu₂ s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [Pi.mul_apply, eval_mul, e₁, e₂, f₁, f₂]
      constructor <;> ring
    · intro s hs
      have hs₁ : s.re < -d₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have hs₂ : s.re < -d₂ := lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))
      obtain ⟨e₁, f₁⟩ := hl₁ s hs₁
      obtain ⟨e₂, f₂⟩ := hl₂ s hs₂
      simp only [Pi.mul_apply, fac_mul, e₁, e₂, f₁, f₂]
      constructor <;> ring
  · intro L L' L₁ L₁' β q P c h hL hL'
    obtain ⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩ := h
    refine ⟨Z, W, A, B, k, k', c₀, t, max d (c + 1), hZ, hW, hZ0, hk, hk', ?_, ?_⟩
    · intro s hs
      have h1 : d < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have h2 : c + 1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
      obtain ⟨e, f⟩ := hu s h1
      have h3 : c < (s + 1).re := by
        rw [Complex.add_re, Complex.one_re]
        linarith
      exact ⟨by rw [e, hL s (by linarith)], by rw [f, hL (s + 1) h3]⟩
    · intro s hs
      have h1 : s.re < -d := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have h2 : s.re < -(c + 1) := lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))
      obtain ⟨e, f⟩ := hl s h1
      have h3 : (s + 1).re < -c := by
        rw [Complex.add_re, Complex.one_re]
        linarith
      exact ⟨by rw [e, hL' s (by linarith)], by rw [f, hL' (s + 1) h3]⟩
  · intro L L' β q P z hq h
    obtain ⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩ := h
    have hsh : Differentiable ℂ (fun s : ℂ => s - z) := differentiable_id.sub_const z
    refine ⟨fun s => Z (s - z), fun s => W (s - z), fun s => A (s - z), fun s => B (s - z), k, k',
      c₀ * Complex.exp (-(t * z)), t, d + |z.re|, hZ.comp hsh, hW.comp hsh, ne_zero_sub hZ0 z, hk,
      hk', ?_, ?_⟩
    · intro s hs
      have h1 : d < (s - z).re := by
        rw [Complex.sub_re]
        linarith [le_abs_self z.re]
      obtain ⟨e, f⟩ := hu (s - z) h1
      refine ⟨e, ?_⟩
      show W (s - z) = k * L (s + 1 - z) * eval s (β.comp (X - C z)) * A (s - z)
      rw [f, eval_comp]
      simp only [eval_sub, eval_X, eval_C]
      rw [show s - z + 1 = s + 1 - z by ring]
    · intro s hs
      have h1 : (s - z).re < -d := by
        rw [Complex.sub_re]
        linarith [neg_abs_le z.re]
      obtain ⟨e, f⟩ := hl (s - z) h1
      constructor
      · show Z (s - z) = L' (s - z) * B (s - z) *
          fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) s
        rw [e, fac_sub c₀ t hq P z s]
      · show W (s - z) = k' * L' (s + 1 - z) * B (s - z) *
          fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) (s + 1)
        rw [f, fac_sub c₀ t hq P z (s + 1), show s - z + 1 = s + 1 - z by ring]

end UpperTheory.V.Z.Gam
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SecDiff
section
private theorem comp_C_mul_X_ne_zero_and_rootMultiplicity {P : Polynomial ℂ} (hP : P ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    P.comp (Polynomial.C r * Polynomial.X) ≠ 0 ∧
      ∀ z, (P.comp (Polynomial.C r * Polynomial.X)).rootMultiplicity z = P.rootMultiplicity (r * z) := by
  refine ⟨fun h0 => hP ((Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hr)).mp h0),
    fun z => ?_⟩
  have := Polynomial.rootMultiplicity_comp_C_mul_X_add_C P r 0 z (isUnit_iff_ne_zero.mpr hr)
  simpa using this

open Polynomial in
theorem UpperTheory.V.Z.Gam.secDiff :
    UpperTheory.V.Z.Gam.SecDiff := by
  classical
  intro q hq P P' c hP hP' h
  have hqpos : (0 : ℝ) < q := by linarith
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hqi : ((q : ℂ))⁻¹ ≠ 0 := inv_ne_zero hq0
  have hc : c = 1 := by
    have h0 := congrArg (Polynomial.eval 0) h
    simp [Polynomial.eval_comp, hP, hP'] at h0
    first
      | exact h0.symm
      | exact h0
  subst hc
  have hPne : P ≠ 0 := by
    rintro rfl
    simp at hP
  have hP'ne : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  obtain ⟨hA, mA⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hqi
  obtain ⟨hB, mB⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hPne hq0
  obtain ⟨hA', mA'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hqi
  obtain ⟨hB', mB'⟩ := comp_C_mul_X_ne_zero_and_rootMultiplicity hP'ne hq0
  rw [map_one, one_mul] at h
  have key : ∀ z : ℂ, P.rootMultiplicity ((q : ℂ)⁻¹ * z) + P.rootMultiplicity ((q : ℂ) * z) +
      (P'.rootMultiplicity z + P'.rootMultiplicity z) =
      P'.rootMultiplicity ((q : ℂ)⁻¹ * z) + P'.rootMultiplicity ((q : ℂ) * z) +
      (P.rootMultiplicity z + P.rootMultiplicity z) := by
    intro z
    have hz := congrArg (Polynomial.rootMultiplicity z) h
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hB) (pow_ne_zero 2 hP'ne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA' hB') (pow_ne_zero 2 hPne)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA hB),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA' hB'), sq, sq,
      Polynomial.rootMultiplicity_mul (mul_ne_zero hP'ne hP'ne),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hPne hPne), mA, mB, mA', mB'] at hz
    omega
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℤ, ∀ z, d z = (P.rootMultiplicity z : ℤ) - P'.rootMultiplicity z :=
    ⟨_, fun z => rfl⟩
  have rel : ∀ z, d ((q : ℂ)⁻¹ * z) + d ((q : ℂ) * z) = 2 * d z := by
    intro z
    have := key z
    simp only [hd]
    omega
  have p0 : P.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP] at this)
  have p0' : P'.rootMultiplicity 0 = 0 := Polynomial.rootMultiplicity_eq_zero (by
    intro hr
    have := hr.eq_zero
    simp [hP'] at this)
  have d0 : d 0 = 0 := by simp [hd, p0, p0']
  have supp : ∀ z, d z ≠ 0 → z ∈ (P * P').roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (mul_ne_zero hPne hP'ne)]
    change Polynomial.eval z (P * P') = 0
    rw [Polynomial.eval_mul]
    by_contra hne
    apply hz
    have r1 : P.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, zero_mul]))
    have r2 : P'.rootMultiplicity z = 0 := Polynomial.rootMultiplicity_eq_zero (by
      intro hr
      exact hne (by rw [hr.eq_zero, mul_zero]))
    simp [hd, r1, r2]
  have hdz : ∀ z, d z = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨z1, hz1⟩ := hne
    set S := (P * P').roots.toFinset.filter (fun z => d z ≠ 0) with hS
    have hSne : S.Nonempty := ⟨z1, Finset.mem_filter.mpr ⟨supp z1 hz1, hz1⟩⟩
    obtain ⟨z0, hz0S, hmax⟩ := S.exists_max_image (fun z => ‖z‖) hSne
    have hz0 : d z0 ≠ 0 := (Finset.mem_filter.mp hz0S).2
    have hz00 : z0 ≠ 0 := by
      rintro rfl
      exact hz0 d0
    have hnz0 : 0 < ‖z0‖ := norm_pos_iff.mpr hz00
    have hnorm : ∀ k : ℕ, ‖(q : ℂ)⁻¹ ^ k * z0‖ = q⁻¹ ^ k * ‖z0‖ := by
      intro k
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    have hup : d ((q : ℂ) * z0) = 0 := by
      by_contra hne2
      have hm := hmax _ (Finset.mem_filter.mpr ⟨supp _ hne2, hne2⟩)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos] at hm
      nlinarith
    have step : ∀ k : ℕ, d ((q : ℂ)⁻¹ ^ k * z0) = (k + 1) * d z0 ∧
        d ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (k + 2) * d z0 := by
      intro k
      induction k with
      | zero =>
        have r0 := rel z0
        rw [hup] at r0
        refine ⟨by simp, ?_⟩
        simp only [zero_add, pow_one, Nat.cast_zero]
        linarith
      | succ k ih =>
        refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
        have r1 := rel ((q : ℂ)⁻¹ ^ (k + 1) * z0)
        have e1 : (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ (k + 1 + 1) * z0 := by ring
        have e2 : (q : ℂ) * ((q : ℂ)⁻¹ ^ (k + 1) * z0) = (q : ℂ)⁻¹ ^ k * z0 := by
          rw [pow_succ]
          linear_combination ((q : ℂ)⁻¹ ^ k * z0) * mul_inv_cancel₀ hq0
        rw [e1, e2, ih.1, ih.2] at r1
        push_cast
        linear_combination r1
    have hmem : ∀ k : ℕ, (q : ℂ)⁻¹ ^ k * z0 ∈ (S : Set ℂ) := by
      intro k
      have hk : d ((q : ℂ)⁻¹ ^ k * z0) ≠ 0 := by
        rw [(step k).1]
        exact mul_ne_zero (by positivity) hz0
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨supp _ hk, hk⟩)
    have hinj : Function.Injective (fun k : ℕ => (q : ℂ)⁻¹ ^ k * z0) := by
      intro a b hab
      have hn := congrArg norm hab
      simp only [hnorm] at hn
      have hab' := mul_right_cancel₀ hnz0.ne' hn
      refine pow_right_injective₀ (inv_pos.mpr hqpos) ?_ hab'
      intro h1
      simp at h1
      linarith
    exact Set.infinite_of_injective_forall_mem hinj hmem S.finite_toSet
  have hm : ∀ z, P.rootMultiplicity z = P'.rootMultiplicity z := by
    intro z
    have := hdz z
    rw [hd] at this
    omega
  have hroots : P.roots = P'.roots := by
    ext z
    rw [Polynomial.count_roots, Polynomial.count_roots, hm]
  have e1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
    IsAlgClosed.card_roots_eq_natDegree
  have e2 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P')
    IsAlgClosed.card_roots_eq_natDegree
  rw [hroots] at e1
  have v1 := congrArg (Polynomial.eval 0) e1
  have v2 := congrArg (Polynomial.eval 0) e2
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP] at v1
  rw [Polynomial.eval_mul, Polynomial.eval_C, hP'] at v2
  have hlc : P.leadingCoeff = P'.leadingCoeff := by
    have hne : Polynomial.eval 0
        (Multiset.map (fun a => Polynomial.X - Polynomial.C a) P'.roots).prod ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at v2
      exact zero_ne_one v2
    exact mul_right_cancel₀ hne (v1.trans v2.symm)
  rw [hlc] at e1
  exact e1.symm.trans e2
end

