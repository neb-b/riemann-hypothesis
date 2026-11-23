module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLev
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalCongruenceFunctionMemAdjoinJSiegelUnits

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.Bcompl
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.BoundedComplement

section Abs

variable {R : Type*} [CommRing R] (p : R) {M : Type*} [AddCommGroup M] [Module R M]

private theorem memP (n : ℕ) (x : M) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R M)) ↔ ∃ y : M, x = p ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

private def IsS (x : ℕ → M) (s : M) : Prop :=
  ∀ n, ∃ y : M, s = ∑ k ∈ Finset.range n, p ^ k • x k + p ^ n • y

private theorem splt (x : ℕ → M) (m j : ℕ) :
    ∑ k ∈ Finset.range (m + j), p ^ k • x k =
      ∑ k ∈ Finset.range m, p ^ k • x k + p ^ m • ∑ i ∈ Finset.range j, p ^ i • x (m + i) := by
  rw [Finset.sum_range_add, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_smul]

private theorem IsS.eq' [IsHausdorff (Ideal.span {p}) M] {x : ℕ → M} {s t : M}
    (hs : IsS p x s) (ht : IsS p x t) : s = t := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {p}) inferInstance _ fun n => ?_
  rw [SModEq.zero, memP]
  obtain ⟨y, hy⟩ := hs n
  obtain ⟨z, hz⟩ := ht n
  exact ⟨y - z, by rw [hy, hz, smul_sub]; abel⟩

private theorem IsS.ex [IsPrecomplete (Ideal.span {p}) M] (x : ℕ → M) : ∃ s, IsS p x s := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {p}) (inferInstance : IsPrecomplete (Ideal.span {p}) M)
    (f := fun n => ∑ k ∈ Finset.range n, p ^ k • x k) (by
      intro m n hmn
      rw [SModEq.sub_mem, memP]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨-∑ i ∈ Finset.range j, p ^ i • x (m + i), ?_⟩
      simp only [splt p x m j, smul_neg]
      abel)
  refine ⟨L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, memP] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨-y, by rw [smul_neg, ← hy]; abel⟩

private theorem IsS.shift {x : ℕ → M} {t : M} (n : ℕ) (ht : IsS p (fun k => x (n + k)) t) :
    IsS p x (∑ k ∈ Finset.range n, p ^ k • x k + p ^ n • t) := by
  intro m
  obtain ⟨y, hy⟩ := ht m
  refine ⟨∑ i ∈ Finset.range n, p ^ i • x (m + i) + p ^ n • y, ?_⟩
  have e1 := splt p x n m
  have e2 := splt p x m n
  rw [Nat.add_comm m n] at e2
  rw [hy, smul_add, ← add_assoc, ← e1, e2, smul_add (p ^ m), smul_comm (p ^ m) (p ^ n) y, add_assoc]

private theorem IsS.map {x : ℕ → M} {s : M} (φ : M →ₗ[R] M) (h : IsS p x s) :
    IsS p (fun k => φ (x k)) (φ s) := by
  intro n
  obtain ⟨y, hy⟩ := h n
  exact ⟨φ y, by rw [hy]; simp [map_sum]⟩

private theorem IsS.fsum {ι : Type*} (S : Finset ι) {x : ι → ℕ → M} {s : ι → M}
    (h : ∀ i ∈ S, IsS p (x i) (s i)) :
    IsS p (fun k => ∑ i ∈ S, x i k) (∑ i ∈ S, s i) := by
  intro n
  choose! y hy using fun i (hi : i ∈ S) => h i hi n
  refine ⟨∑ i ∈ S, y i, ?_⟩
  rw [Finset.sum_congr rfl hy, Finset.sum_add_distrib, Finset.smul_sum]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem IsS.smul {x : ℕ → M} {s : M} (r : R) (h : IsS p x s) :
    IsS p (fun k => r • x k) (r • s) := h.map p (r • LinearMap.id)

end Abs

section Conc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem khat_complete (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] : IsAdicComplete (idl l) (X.Khat l) :=
  AdicCompletion.isAdicComplete ⟨{(l : ℤ_[l])}, by simp⟩

private theorem memA (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {x : ℕ → X.Khat l} {s : X.Khat l}
    (hx : ∀ k, x k ∈ X.A l) (hs : IsS (l : ℤ_[l]) x s) : s ∈ X.A l := by
  refine Submodule.subset_span fun n => ?_
  obtain ⟨y, hy⟩ := hs n
  obtain ⟨φ, hφ, hd⟩ := X.j_hol
  obtain ⟨f, hf, e⟩ := _root_.GlobalTheory.KZ.ES.exists_un_eval_eq_cls ε X ⟨φ, hd, hφ⟩ l n
    (∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k • x k)
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k))
  refine ⟨f, hf, ?_⟩
  rw [hy, map_add (f := _), e, map_smul]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n y)
  rw [← hz, ← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2 ((memP _ n _).2 ⟨z, rfl⟩), add_zero]

private theorem bset_of_mem (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) {b : X.Fn l}
    (hb : b ∈ X.B N l w) : b ∈ X.BSet N l w := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨⟨fun _ => 0, fun _ => Submodule.zero_mem _, fun u => by simp⟩, fun γ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨⟨c, hc, ec⟩, ix⟩ := hx
    obtain ⟨⟨d, hd, ed⟩, iy⟩ := hy
    refine ⟨⟨fun i => c i + d i, fun i => Submodule.add_mem _ (hc i) (hd i), fun u => ?_⟩,
      fun γ hγ => by rw [map_add (f := _), ix γ hγ, iy γ hγ]⟩
    simp only [Pi.add_apply, ec, ed, smul_add, Finset.sum_add_distrib]
  | smul r x _ hx =>
    obtain ⟨⟨c, hc, ec⟩, ix⟩ := hx
    refine ⟨⟨fun i => r • c i, fun i => Submodule.smul_mem _ _ (hc i), fun u => ?_⟩,
      fun γ hγ => by rw [map_smul, ix γ hγ]⟩
    simp only [Pi.smul_apply, ec, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem sfun (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ) (d : ℕ → X.Fn l)
    (hd : ∀ k, d k ∈ X.BSet N l w) :
    ∃ t ∈ X.BSet N l w, ∀ u, IsS (l : ℤ_[l]) (fun k => d k u) (t u) := by
  haveI := khat_complete X l
  choose c hcA hc using fun k => (hd k).1
  choose s hs using fun i => IsS.ex (l : ℤ_[l]) (fun k => c k i)
  have hsum : ∀ u : Fin 2 → ℤ_[l], IsS (l : ℤ_[l]) (fun k => d k u)
      (∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i) := fun u => by
    have h := IsS.fsum (l : ℤ_[l]) (Finset.univ : Finset (Fin (w + 1)))
      (x := fun i k => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c k i)
      (s := fun i => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i)
      (fun i _ => (hs i).smul _ _)
    simpa only [hc] using h
  refine ⟨fun u => ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • s i,
    ⟨⟨s, fun i => memA X l (fun k => hcA k i) (hs i), fun u => rfl⟩, fun γ hγ => ?_⟩, hsum⟩
  funext u
  have h1 := (hsum (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)).map (l : ℤ_[l])
    (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv)
  have e : (fun k => X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (d k (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))) = fun k => d k u :=
    funext fun k => congrFun ((hd k).2 γ hγ) u
  rw [e] at h1
  exact h1.eq' _ (hsum u)

end Conc

end UpperTheory.Kd.K4.BoundedComplement

open UpperTheory.Kd.K4.BoundedComplement in
theorem UpperTheory.Kd.K4.bcompl :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w : ℕ), IsAdicComplete (idl l) (X.B N l w) := by
  intro Ω _ _ _ ε X l _ N w
  haveI := khat_complete X l
  have hH : IsHausdorff (idl l) (X.B N l w) := ⟨fun x hx => by
    refine Subtype.ext (funext fun u => ?_)
    show (x : X.Fn l) u = 0
    refine IsHausdorff.haus (I := idl l) (inferInstance : IsHausdorff (idl l) (X.Khat l)) _ fun n => ?_
    have h := hx n
    rw [SModEq.zero, memP] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨(y : X.Fn l) u, by rw [hy]; rfl⟩⟩
  have hP : IsPrecomplete (idl l) (X.B N l w) := ⟨fun {f} hf => by
    have hstep : ∀ k, ∃ y : X.B N l w, f k - f (k + 1) = (l : ℤ_[l]) ^ k • y := fun k => by
      have h := hf (Nat.le_succ k)
      rwa [SModEq.sub_mem, memP] at h
    choose d hd using hstep
    have hB : ∀ k, (d k : X.Fn l) ∈ X.BSet N l w := fun k => bset_of_mem X l N w (d k).2
    have mkB : ∀ {b : X.Fn l}, b ∈ X.BSet N l w → b ∈ X.B N l w := fun h => Submodule.subset_span h
    obtain ⟨t0, ht0, hs0⟩ := sfun X l N w (fun k => (d k : X.Fn l)) hB
    have hfn : ∀ n, f n = f 0 - ∑ k ∈ Finset.range n, (l : ℤ_[l]) ^ k • d k := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ← hd n, ih]
        abel
    refine ⟨f 0 - ⟨t0, mkB ht0⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, memP]
    obtain ⟨tn, htn, hsn⟩ := sfun X l N w (fun k => (d (n + k) : X.Fn l)) fun k => hB _
    refine ⟨⟨tn, mkB htn⟩, ?_⟩
    rw [hfn n]
    ext u
    have e := (hs0 u).eq' _ ((hsn u).shift (l : ℤ_[l]) n (x := fun k => (d k : X.Fn l) u))
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, Submodule.coe_sum, Finset.sum_apply, e]
    abel_nf⟩
  exact ⟨⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.BddOrder
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4.BoundedOrderUnits

open Filter Topology

private theorem near_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : ℂ → ℂ)
    (hφ : X.an X.jK = (φ : Mero)) (hφc : ContinuousOn φ Hs) :
    ∃ t : ℝ, 0 < t ∧ ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2 := by
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp X.jK
  have hinj : Function.Injective (fun n : ℕ => (n : ℚ) - 1) := fun a b h => by simpa using h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (Complex.exp (2 * Real.pi * Complex.I * z) * φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← hinj.hasSum_iff] at h1
    · have h2 := h1.mul_left (Complex.exp (2 * Real.pi * Complex.I * z))
      have e : (fun n : ℕ => ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) = fun n : ℕ =>
          Complex.exp (2 * Real.pi * Complex.I * z) * (ε ((X.exp X.jK).coeff ((n : ℚ) - 1)) *
            Complex.exp (2 * Real.pi * Complex.I * (((n : ℚ) - 1 : ℚ) : ℂ) * z)) := by
        funext n
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [e]
      exact h2
    · intro r hr
      have : (X.exp X.jK).coeff r = 0 := by
        by_contra hne
        obtain ⟨m, rfl⟩ := GlobalTheory.K4.LevFin.exponent_int X X.jK (X.j_inv _) r hne
        have hm : -1 ≤ m := by
          by_contra hm
          exact hne (X.j_exp.2.1 _ (by exact_mod_cast (not_le.1 hm)))
        refine hr ⟨(m + 1).toNat, ?_⟩
        show (((m + 1).toNat : ℕ) : ℚ) - 1 = m
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
        push_cast
        ring
      simp [this]
  obtain ⟨B, t, hB⟩ := GlobalTheory.KZ.ExpBound.series_bound _ _ C hsumN
  simp only [Nat.cast_zero, zero_sub, X.j_exp.1, map_one] at hB
  have ht : Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) atTop atTop := by
      apply Tendsto.const_mul_atTop Real.two_pi_pos
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
  obtain ⟨s, hs⟩ := eventually_atTop.1 (ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨max (max s t) 1, lt_max_of_lt_right one_pos, fun z hz => ?_⟩
  have hzH : z ∈ Hs := lt_trans (lt_max_of_lt_right one_pos) hz
  have hev : φ =ᶠ[codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hzH
  have hHs : Hs ∈ 𝓝 z := SiegelModel.isOpen_Hs.mem_nhds hzH
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | max (max s t) 1 < w.im} ∈ 𝓝[≠] z :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  have hc : ContinuousAt (fun w => ‖Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1‖) z := by
    have := hφc.continuousAt hHs
    fun_prop
  refine le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    simp only [Set.mem_setOf_eq, max_lt_iff] at hw3
    exact (hB w hw3.1.2).trans (hs _ hw3.1.1.le)
  · exact absurd hw2 e

private theorem deriv_ne (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (t : ℝ) (ht : 0 < t)
    (h : ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2)
    (z : ℂ) (hz : t + 1 < z.im) : deriv φ z ≠ 0 := by
  intro h0
  have hsub : ∀ w ∈ Metric.closedBall z 1, t < w.im := by
    intro w hw
    have h1 : ‖w - z‖ ≤ 1 := by simpa [dist_eq_norm] using hw
    have h2 := (Complex.abs_im_le_norm (w - z)).trans h1
    rw [Complex.sub_im, abs_le] at h2
    linarith [h2.1]
  have hG : DifferentiableOn ℂ (fun w => Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1) Hs :=
    (DifferentiableOn.mul (by fun_prop) hd).sub_const 1
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := 1 / 2) one_pos
    (hG.diffContOnCl_ball (fun w hw => lt_trans ht (hsub w hw)))
    (fun w hw => h w (hsub w (Metric.sphere_subset_closedBall hw)))
  have hzH : z ∈ Hs := show 0 < z.im by linarith
  have hφ : HasDerivAt φ 0 z := h0 ▸ (hd.differentiableAt (SiegelModel.isOpen_Hs.mem_nhds hzH)).hasDerivAt
  have he : HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * w))
      (Complex.exp (2 * Real.pi * Complex.I * z) * (2 * Real.pi * Complex.I)) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I : ℂ)).cexp
  have hD : HasDerivAt (fun w => Complex.exp (2 * Real.pi * Complex.I * w) * φ w - 1) _ z := (he.mul hφ).sub_const 1
  rw [hD.deriv, mul_zero, add_zero, mul_right_comm, norm_mul] at hb
  have h1 := h z (by linarith)
  have h2 := norm_sub_norm_le (1 : ℂ) (Complex.exp (2 * Real.pi * Complex.I * z) * φ z)
  rw [norm_one, norm_sub_rev] at h2
  have h3 : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [h3] at hb
  nlinarith [Real.pi_gt_three]

private theorem onto (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs)
    (hinv : ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) (t : ℝ) (ht : 0 < t)
    (h : ∀ z : ℂ, t < z.im → ‖Complex.exp (2 * Real.pi * Complex.I * z) * φ z - 1‖ ≤ 1 / 2)
    (a : ℂ) : ∃ τ ∈ Hs, φ τ = a := by
  by_contra hc
  push Not at hc
  have hne : ∀ τ ∈ Hs, φ τ - a ≠ 0 := fun τ hτ => sub_ne_zero.2 (hc τ hτ)
  obtain ⟨c, hcc⟩ := _root_.GlobalTheory.KZ.LevelOne.const_of_invariant_bounded (fun w => (φ w - a)⁻¹) ((hd.sub_const a).inv hne)
    (fun γ z hz => by simp only [hinv γ z hz]) ⟨1, max t (‖a‖ + 1), fun z hz hzt => by
      rw [max_lt_iff] at hzt
      have h1 := h z hzt.1
      have h2 := norm_sub_norm_le (1 : ℂ) (Complex.exp (2 * Real.pi * Complex.I * z) * φ z)
      rw [norm_one, norm_sub_rev, norm_mul, Complex.norm_exp] at h2
      have e : (2 * Real.pi * Complex.I * z : ℂ).re = -(2 * Real.pi * z.im) := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [e, Real.exp_neg] at h2
      have h3 := Real.add_one_le_exp (2 * Real.pi * z.im)
      have h4 := Real.exp_pos (2 * Real.pi * z.im)
      have h5 : 1 / 2 * Real.exp (2 * Real.pi * z.im) ≤ ‖φ z‖ := by
        rw [← le_div_iff₀ h4, div_eq_inv_mul ‖φ z‖]; linarith
      have h6 := norm_sub_norm_le (φ z) a
      have h7 : 0 < z.im := hz
      rw [norm_inv]
      apply inv_le_one_of_one_le₀
      nlinarith [Real.pi_gt_three]⟩
  have hzH : ((t + 2 : ℝ) : ℂ) * Complex.I ∈ Hs := by simp [Hs]; linarith
  refine deriv_ne φ hd t ht h (((t + 2 : ℝ) : ℂ) * Complex.I) (by simp) ?_
  have hev : φ =ᶠ[𝓝 (((t + 2 : ℝ) : ℂ) * Complex.I)] fun _ => c⁻¹ + a := by
    filter_upwards [SiegelModel.isOpen_Hs.mem_nhds hzH] with w hw
    rw [← hcc w hw]
    simp
  rw [hev.deriv_eq, deriv_const]

private theorem bdd_order (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g Hs) (z0 : ℂ) (hz0 : z0 ∈ Hs) (h0 : g z0 ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ Hs) : ∃ E : ℕ, ∀ τ ∈ K, analyticOrderAt g τ ≤ E := by
  refine hK.induction_on (p := fun S => ∃ E : ℕ, ∀ τ ∈ S, analyticOrderAt g τ ≤ E) ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro s u hsu ⟨E, hE⟩
    exact ⟨E, fun τ hτ => hE τ (hsu hτ)⟩
  · rintro s u ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨max E F, ?_⟩
    rintro τ (hτ | hτ)
    · exact (hE τ hτ).trans (by exact_mod_cast le_max_left _ _)
    · exact (hF τ hτ).trans (by exact_mod_cast le_max_right _ _)
  · intro x hx
    have hnz : ¬ ∀ᶠ w in 𝓝 x, g w = 0 := fun hz =>
      h0 (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero GlobalTheory.FN.isPreconnected_Hs (hKH hx) hz hz0)
    have hne := (hg x (hKH hx)).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (fun h => hnz (analyticOrderAt_eq_top.1 h))
    rw [eventually_nhdsWithin_iff] at hne
    refine ⟨_, mem_nhdsWithin_of_mem_nhds hne, n, fun τ hτ => ?_⟩
    by_cases e : τ = x
    · rw [e, hn]
    · rw [analyticOrderAt_eq_zero.2 (Or.inr (hτ e))]
      exact zero_le

private theorem order_inv (φ : ℂ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) (γ : SL(2, ℤ)) (τ : ℂ) (hτ : τ ∈ Hs) :
    analyticOrderAt (fun s => φ s - φ τ) τ =
      analyticOrderAt (fun s => φ s - φ (mob (ofSL γ) τ)) (mob (ofSL γ) τ) := by
  have hden := GlobalTheory.KZ.InvFun.mob_ofSL_den_ne_zero γ hτ
  have han : AnalyticAt ℂ (mob (ofSL γ)) τ := by
    unfold mob
    exact AnalyticAt.div (by fun_prop) (by fun_prop) hden
  have hdet : (ent (ofSL γ) 0 0 : ℂ) * ent (ofSL γ) 1 1 - ent (ofSL γ) 0 1 * ent (ofSL γ) 1 0 = 1 := by
    have he : ∀ i j, ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := fun _ _ => rfl
    have h1 := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h1
    simp only [he]
    exact_mod_cast h1
  have hD : HasDerivAt (mob (ofSL γ)) _ τ :=
    (((hasDerivAt_id τ).const_mul (ent (ofSL γ) 0 0 : ℂ)).add_const (ent (ofSL γ) 0 1 : ℂ)).div
      (((hasDerivAt_id τ).const_mul (ent (ofSL γ) 1 0 : ℂ)).add_const (ent (ofSL γ) 1 1 : ℂ)) hden
  have hD0 : deriv (mob (ofSL γ)) τ ≠ 0 := by
    rw [hD.deriv]
    refine div_ne_zero ?_ (pow_ne_zero _ hden)
    simp only [id]
    intro h
    apply one_ne_zero (α := ℂ)
    rw [← hdet, ← h]
    ring
  rw [← analyticOrderAt_comp_of_deriv_ne_zero han hD0]
  apply analyticOrderAt_congr
  filter_upwards [SiegelModel.isOpen_Hs.mem_nhds hτ] with w hw
  simp only [Function.comp_apply, hinv γ w hw, hinv γ τ hτ]

end UpperTheory.Kd.K4.BoundedOrderUnits

open UpperTheory.Kd.K4.BoundedOrderUnits in
theorem UpperTheory.Kd.K4.jan :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∃ (φ : ℂ → ℂ) (E : ℕ), X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs ∧ (∀ z : ℂ, ∃ τ ∈ Hs, φ τ = z) ∧
      ∀ τ ∈ Hs, analyticOrderAt (fun s => φ s - φ τ) τ ≤ E := by
  intro Ω _ _ _ ε X
  obtain ⟨φ, hφ, hd⟩ := X.j_hol
  have hinv := _root_.GlobalTheory.KZ.InvFun.fun_inv X X.jK φ hd.continuousOn hφ X.j_inv
  obtain ⟨t, ht, h⟩ := near_one X φ hφ hd.continuousOn
  have hne := deriv_ne φ hd t ht h
  have han := hd.analyticOnNhd SiegelModel.isOpen_Hs
  obtain ⟨E, hE⟩ := bdd_order (deriv φ) han.deriv (((t + 2 : ℝ) : ℂ) * Complex.I) (by simp [Hs]; linarith)
    (hne _ (by simp)) (Set.Icc (-1) 1 ×ℂ Set.Icc (1 / 2) (t + 1)) (isCompact_Icc.reProdIm isCompact_Icc)
    (fun z hz => lt_of_lt_of_le (by norm_num) hz.2.1)
  refine ⟨φ, E + 1, hφ, hd, onto φ hd hinv t ht h, fun τ hτ => ?_⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd ⟨τ, hτ⟩
  have hm : mob (ofSL γ) τ = ((γ • (⟨τ, hτ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    SiegelModel.mob_ofSL γ ⟨τ, hτ⟩
  rw [order_inv φ hinv γ τ hτ, hm]
  generalize γ • (⟨τ, hτ⟩ : UpperHalfPlane) = σ at hγ
  rw [← (han σ σ.2).analyticOrderAt_deriv_add_one]
  push_cast
  gcongr
  by_cases hσ : t + 1 < (σ : ℂ).im
  · rw [analyticOrderAt_eq_zero.2 (Or.inr (hne _ hσ))]
    exact zero_le
  · have h1 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
    have h2 := abs_le.1 hγ.2
    have h3 := σ.im_pos
    refine hE _ ⟨⟨?_, ?_⟩, ?_, not_lt.1 hσ⟩
    · show -1 ≤ σ.re
      linarith [h2.1]
    · show σ.re ≤ 1
      linarith [h2.2]
    · show 1 / 2 ≤ σ.im
      nlinarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.ExistsOfFixed
section
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem exists_of_fixed {E : Type} [Field E] (G : Type) [Group G] [Finite G] [MulSemiringAction G E] (σ : E ≃+* E)
    (h : ∀ x ∈ FixedPoints.subfield G E, σ x = x) : ∃ g : G, ∀ x : E, g • x = σ x := by
  let σ' : E ≃ₐ[FixedPoints.subfield G E] E := AlgEquiv.ofRingEquiv (f := σ) fun x => h x x.2
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective G E σ'
  refine ⟨g, fun x => ?_⟩
  exact DFunLike.congr_fun hg x

theorem UpperTheory.Kd.K4.faith :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H' : Subgroup SL(2, ℤ)) (M : ℕ), 0 < M → CongruenceSubgroup.Gamma M ≤ H' → ∀ γ : SL(2, ℤ), (∀ f ∈ lev X H', X.sl (ofSL γ) f = f) → γ ∈ H' ∨ -γ ∈ H' := by
  intro Ω _ _ _ ε X H' M hM hle γ hγ
  have hfin : Finite (H'.map (GlobalTheory.KZ.FracGen.rhoF X M)) := by
    haveI := GlobalTheory.KZ.FracGen.finite_range X M hM
    have hr : H'.map (GlobalTheory.KZ.FracGen.rhoF X M) ≤ (GlobalTheory.KZ.FracGen.rhoF X M).range := by
      rintro _ ⟨δ, -, rfl⟩
      exact ⟨δ, rfl⟩
    exact Finite.of_injective _ (Subgroup.inclusion_injective hr)
  obtain ⟨s, hs⟩ := exists_of_fixed (H'.map (GlobalTheory.KZ.FracGen.rhoF X M))
    (GlobalTheory.KZ.FracGen.rhoF X M γ⁻¹).toRingEquiv (by
      intro x hx
      apply Subtype.ext
      show X.sl (ofSL γ⁻¹⁻¹) x = x
      rw [inv_inv]
      refine hγ _ ((mem_lev_iff X H' _).2 fun δ hδ => ?_)
      have h1 := hx ⟨GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹, ⟨δ⁻¹, inv_mem hδ, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      have h3 : ((GlobalTheory.KZ.FracGen.rhoF X M δ⁻¹ x : GlobalTheory.KZ.FracGen.FM X M) : X.K) = X.sl (ofSL δ⁻¹⁻¹) x :=
        GlobalTheory.KZ.FracGen.rhoF_apply X M δ⁻¹ x
      rw [inv_inv] at h3
      rw [← h3]
      exact h2)
  obtain ⟨_, ⟨δ, hδ, rfl⟩⟩ := s

  have hact : ∀ x : GlobalTheory.KZ.FracGen.FM X M, X.sl (ofSL δ⁻¹) x = X.sl (ofSL γ) x := by
    intro x
    have h1 := congrArg Subtype.val (hs x)
    have h2 := GlobalTheory.KZ.FracGen.rhoF_apply X M δ x
    have h3 := GlobalTheory.KZ.FracGen.rhoF_apply X M γ⁻¹ x
    rw [inv_inv] at h3
    rw [← h2, ← h3]
    exact h1
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by simp
  have hcM : 6 * M + 1 ≡ 1 [MOD M] := by
    simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left]
  have hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
      X.sl (ofSL (δ⁻¹ * γ⁻¹)) (siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M]) =
        siegel X (6 * M + 1) ![(a : ℚ) / M, (b : ℚ) / M] := by
    intro a b hab
    have hmem := (GlobalTheory.KZ.FracGen.mem_FM X M _).2 (GlobalTheory.KZ.FracGen.siegel_inv X M _ hM hc1 hc6 hcM a b hab)
    have h1 := hact ⟨_, hmem⟩
    rw [map_mul, X.sl_mul]
    refine (congrArg (X.sl (ofSL γ⁻¹)) h1).trans ?_
    rw [← X.sl_mul, ← map_mul, mul_inv_cancel, map_one]
    exact X.sl_one _
  rcases _root_.GlobalTheory.SiegSep.fix_siegel_pm_one ε X M (6 * M + 1) (δ⁻¹ * γ⁻¹) hM hc1 hc6 hcM hfix with h | h
  · left
    have e : γ = (δ * (δ⁻¹ * γ⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
  · right
    have e : -γ = (δ * -(δ⁻¹ * γ⁻¹))⁻¹ := by
      rw [mul_neg, inv_neg]
      congr 1
      group
    rw [e]
    exact inv_mem (mul_mem hδ (hle h))
end

