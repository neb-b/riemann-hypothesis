module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar
section
noncomputable section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

def expChar (c : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (c * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem lagrange (C : Finset ℂ) (c : ℂ) : ∃ (τs : Finset ℝ) (a : ℝ → ℂ), ∀ c' ∈ C,
    ∑ t ∈ τs, a t * Complex.exp (c' * t) = if c' = c then 1 else 0 := by
  classical
  have expChar_injective : Function.Injective expChar := by
    intro c c' h
    have hd : ∀ d : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (d * (t : ℂ))) d 0 := by
      intro d
      have h1 : HasDerivAt (fun t : ℝ => d * (t : ℂ)) (d * 1) 0 :=
        ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul d
      have h2 := h1.cexp
      simpa using h2
    have hf : (fun t : ℝ => Complex.exp (c * (t : ℂ))) = fun t : ℝ => Complex.exp (c' * (t : ℂ)) := by
      funext t
      have := DFunLike.congr_fun h (Multiplicative.ofAdd t)
      simpa [expChar] using this
    have e := hd c
    rw [hf] at e
    exact e.unique (hd c')
  let v : ℝ → (C → ℂ) := fun t c' => Complex.exp ((c' : ℂ) * t)
  have hli : LinearIndependent ℂ (fun c' : C => (expChar (c' : ℂ) : Multiplicative ℝ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp (fun c' : C => expChar (c' : ℂ))
      (expChar_injective.comp Subtype.val_injective)
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hw : ∀ i : C, f (Pi.single i 1) = 0 := by
      have hsum : ∑ i : C, f (Pi.single i 1) • (expChar (i : ℂ) : Multiplicative ℝ → ℂ) = 0 := by
        funext x
        have hx : f (v (Multiplicative.toAdd x)) = 0 := hle (Submodule.subset_span ⟨_, rfl⟩)
        have hv : v (Multiplicative.toAdd x) = ∑ i : C, (v (Multiplicative.toAdd x) i) • Pi.single i 1 := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hv, map_sum] at hx
        simp only [map_smul, smul_eq_mul] at hx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hx]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [expChar, v, mul_comm]
      exact fun i => Fintype.linearIndependent_iff.1 hli _ hsum i
    exact (Pi.basisFun ℂ C).ext fun i => by simpa using hw i
  have hmem : (fun c' : C => if (c' : ℂ) = c then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range v) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨a.support, a, fun c' hc' => ?_⟩
  have := congrFun ha ⟨c', hc'⟩
  rw [Finsupp.sum, Finset.sum_apply] at this
  simpa [v] using this

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogOde
section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

def pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ := p.sum fun k a => a * f k t

def pevL (f : ℕ → ℝ → ℂ) (t : ℝ) : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.lsum fun n => f n t • LinearMap.id

theorem pev_eq (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev p f t = pevL f t p := by
  simp only [pev, pevL, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  exact congrArg p.sum (funext fun k => funext fun a => mul_comm _ _)

theorem pev_add (p q : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (p + q) f t = pev p f t + pev q f t := by
  simp only [pev_eq, map_add (f := _)]

theorem pev_C_mul (c : ℂ) (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (C c * p) f t = c * pev p f t := by
  simp only [pev_eq, Polynomial.C_mul', map_smul, smul_eq_mul]

theorem pev_sum {ι : Type} (s : Finset ι) (p : ι → ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) :
    pev (∑ i ∈ s, p i) f t = ∑ i ∈ s, pev (p i) f t := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pev_eq, map_sum]

theorem pev_monomial (n : ℕ) (a : ℂ) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (monomial n a) f t = a * f n t := by
  simp only [pev]
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem pev_one (f : ℕ → ℝ → ℂ) (t : ℝ) : pev 1 f t = f 0 t := by
  rw [← Polynomial.monomial_zero_one, pev_monomial, one_mul]

theorem pev_X_mul (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (X * p) f t = pev p (fun k => f (k + 1)) t := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, pev_add, pev_add, hp, hq]
  | monomial n a => rw [Polynomial.X_mul_monomial, pev_monomial, pev_monomial]

theorem hasDerivAt_pev (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (t : ℝ) :
    HasDerivAt (fun t => pev p f t) (pev p (fun k => f (k + 1)) t) t := by
  simp only [pev, Polynomial.sum_def]
  exact HasDerivAt.fun_sum fun n _ => (hf n t).const_mul (p.coeff n)

theorem iteratedDeriv_chain (f : ℕ → ℝ → ℂ) (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (k : ℕ) :
    iteratedDeriv k (f 0) = f k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hf k t).deriv

theorem eq_exp_of_hasDerivAt {P : ℝ → ℂ} {v : ℂ} (hP : ∀ t, HasDerivAt P (v * P t) t) (t : ℝ) :
    P t = Complex.exp (v * t) * P 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(v * t)) * P t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(v * (t : ℂ))) (-(v * 1)) t :=
      ((hasDerivAt_id t).ofReal_comp.const_mul v).neg
    have he := h1.cexp
    exact (he.fun_mul (hP t)).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem ode_decomp (S : Finset ℂ) : ∃ L : ℂ → ℂ[X], ∀ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) →
    (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) →
    (∀ t, f 0 t = ∑ v ∈ S, pev (L v) f t) ∧ ∀ v ∈ S, ∀ t, pev (L v) f t = Complex.exp (v * t) * pev (L v) f 0 := by
  classical
  refine ⟨fun v => Lagrange.basis S id v, fun f hf hq => ?_⟩
  have hq1 : ∀ v ∈ S, (X - C v) * Lagrange.basis S id v =
      C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S, (X - C μ) := by
    intro v hv
    have e : Lagrange.basis S id v = C (∏ μ ∈ S.erase v, (v - μ))⁻¹ * ∏ μ ∈ S.erase v, (X - C μ) := by
      simp only [Lagrange.basis, Lagrange.basisDivisor, id, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]
    rw [e, mul_left_comm, Finset.mul_prod_erase S (fun μ => X - C μ) hv]
  refine ⟨fun t => ?_, fun v hv t => ?_⟩
  · rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      have h := hq t
      simp only [Finset.prod_empty, pev_one] at h
      simp [h]
    · rw [← pev_one f t, ← Lagrange.sum_basis (Set.injOn_id _) hS, pev_sum]
  · refine eq_exp_of_hasDerivAt (fun t => ?_) t
    have h := hasDerivAt_pev (Lagrange.basis S id v) f hf t
    convert h using 1
    rw [← pev_X_mul]
    have e : X * Lagrange.basis S id v = (X - C v) * Lagrange.basis S id v + C v * Lagrange.basis S id v := by ring
    rw [e, pev_add, hq1 v hv, pev_C_mul, pev_C_mul, hq t]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSepFac
section
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A]

def IsSS (x : A) : Prop := ∃ s : Finset ℂ, aeval x (∏ v ∈ s, (X - C v)) = 0

theorem aeval_mul_of_mul_eq {z m : A} {c : ℂ} (h : z * m = c • m) (R : ℂ[X]) :
    aeval z R * m = R.eval c • m := by
  have hp : ∀ n : ℕ, z ^ n * m = c ^ n • m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, ← pow_succ']
  induction R using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), add_mul, hp', hq', eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, eval_monomial, mul_assoc, hp n, ← Algebra.smul_def, smul_smul]

theorem commute_aeval {x y : A} (h : Commute x y) (R : ℂ[X]) : Commute (aeval x R) y := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_left a y).mul_left (h.pow_left n)

theorem isSS_of_decomp {κ : Type} {x : A} (ι : Finset κ) (e : κ → A) (c : κ → ℂ) (hsum : ∑ i ∈ ι, e i = 1)
    (hx : ∀ i ∈ ι, x * e i = c i • e i) : IsSS x := by
  classical
  refine ⟨ι.image c, ?_⟩
  calc aeval x (∏ v ∈ ι.image c, (X - C v)) = aeval x (∏ v ∈ ι.image c, (X - C v)) * ∑ i ∈ ι, e i := by
        rw [hsum, mul_one]
    _ = ∑ i ∈ ι, (∏ v ∈ ι.image c, (X - C v)).eval (c i) • e i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => aeval_mul_of_mul_eq (hx i hi) _
    _ = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [eval_prod, Finset.prod_eq_zero (Finset.mem_image_of_mem c hi) (by simp), zero_smul]

theorem IsSS.exists_decomp {x : A} (hx : IsSS x) : ∃ (s : Finset ℂ) (e : ℂ → A), ∑ v ∈ s, e v = 1 ∧
    (∀ v ∈ s, x * e v = v • e v) ∧ ∀ v, ∀ y : A, Commute x y → Commute (e v) y := by
  classical
  obtain ⟨s, hs⟩ := hx
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h10 : (1 : A) = 0 := by simpa using hs
    have : Subsingleton A := subsingleton_of_zero_eq_one h10.symm
    exact ⟨{0}, fun _ => 1, by simp, fun _ _ => Subsingleton.elim _ _, fun _ _ _ => Commute.one_left _⟩
  refine ⟨s, fun v => aeval x (Lagrange.basis s id v), ?_, fun v hv => ?_, fun v y h => commute_aeval h _⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, Lagrange.sum_basis (Set.injOn_id _) hne, map_one]
  · have key : (X - C v) * Lagrange.basis s id v = (∏ j ∈ s.erase v, C (v - j)⁻¹) * ∏ j ∈ s, (X - C j) := by
      rw [← Finset.mul_prod_erase s (fun j => X - C j) hv, Lagrange.basis]
      simp only [Lagrange.basisDivisor, id, Finset.prod_mul_distrib]
      ring
    have h0 : aeval x ((X - C v) * Lagrange.basis s id v) = 0 := by
      rw [key, map_mul, hs, mul_zero]
    rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, ← Algebra.smul_def] at h0
    exact h0

theorem IsSS.add {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x + y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 + p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    simp only
    rw [add_mul, ← mul_assoc, hxe v hvw.1, ← mul_assoc, hey, mul_assoc, hyf w hvw.2, smul_mul_assoc,
      mul_smul_comm, add_smul]

theorem IsSS.mul {x y : A} (hx : IsSS x) (hy : IsSS y) (h : Commute x y) : IsSS (x * y) := by
  obtain ⟨s, e, hse, hxe, hce⟩ := hx.exists_decomp
  obtain ⟨t, f, htf, hyf, -⟩ := hy.exists_decomp
  refine isSS_of_decomp (s ×ˢ t) (fun p => e p.1 * f p.2) (fun p => p.1 * p.2) ?_ ?_
  · rw [Finset.sum_product, ← hse]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only
    rw [← Finset.mul_sum, htf, mul_one]
  · rintro ⟨v, w⟩ hvw
    rw [Finset.mem_product] at hvw
    have hey : y * e v = e v * y := ((hce v y h).eq).symm
    calc x * y * (e v * f w) = x * ((y * e v) * f w) := by simp only [mul_assoc]
      _ = x * (e v * (y * f w)) := by rw [hey, mul_assoc]
      _ = x * (e v * (w • f w)) := by rw [hyf w hvw.2]
      _ = w • ((x * e v) * f w) := by rw [mul_smul_comm, mul_smul_comm, mul_assoc]
      _ = (v * w) • (e v * f w) := by rw [hxe v hvw.1, smul_mul_assoc, smul_smul, mul_comm w v]

theorem IsSS.smul {x : A} (hx : IsSS x) (c : ℂ) : IsSS (c • x) := by
  obtain ⟨s, e, hse, hxe, -⟩ := hx.exists_decomp
  refine isSS_of_decomp s e (fun v => c * v) hse fun v hv => ?_
  rw [smul_mul_assoc, hxe v hv, smul_smul]

theorem isSS_algebraMap (c : ℂ) : IsSS (algebraMap ℂ A c) :=
  isSS_of_decomp ({()} : Finset Unit) (fun _ => 1) (fun _ => c) (by simp) fun _ _ => by
    rw [mul_one, Algebra.algebraMap_eq_smul_one]

theorem isSS_zero : IsSS (0 : A) := by simpa using isSS_algebraMap (A := A) 0

theorem IsSS.sum {κ : Type} (ι : Finset κ) (x : κ → A) (hx : ∀ i ∈ ι, IsSS (x i))
    (hc : ∀ i ∈ ι, ∀ j ∈ ι, Commute (x i) (x j)) : IsSS (∑ i ∈ ι, x i) := by
  classical
  induction ι using Finset.induction_on with
  | empty => simpa using isSS_zero
  | insert a ι ha ih =>
    rw [Finset.sum_insert ha]
    refine (hx a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
        fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) ?_
    exact Commute.sum_right _ _ _ fun j hj =>
      hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)

end Ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac

end
end

