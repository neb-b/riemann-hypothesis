module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeSt
section
noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def Ym (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • Matrix.of B)⁻¹

def Yp (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • Matrix.of B)⁻¹

def vals (s : ℂ) (B : MC n) : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then Yp s B k.2.1 k.2.2 else Ym s B k.2.1 k.2.2

def evQ (s z : ℂ) (Q : Fm n) (B : MC n) : ℂ :=
  MvPolynomial.eval (vals s B) (MvPolynomial.map (Polynomial.evalRingHom z) Q)

def fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B : MC n) : ℂ := clsC s z m 0 1 B * evQ s z Q B

def HYm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 - (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Ym s (x + t • v) a d) (((Complex.I * s) • (Ym s x * Matrix.of v * Ym s x)) a d) 0

def HYp : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 + (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Yp s (x + t • v) a d) ((-(Complex.I * s) • (Yp s x * Matrix.of v * Yp s x)) a d) 0

def HCls : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (z : ℂ) (m : ℕ) (x v : MC n), x ∈ OmS s →
    HasDerivAt (fun t : ℂ => clsC s z m 0 1 (x + t • v))
      (clsC s z m 0 1 x * (Complex.I * s * ((m : ℂ) + z) * (Ym s x * Matrix.of v).trace -
        Complex.I * s * z * (Yp s x * Matrix.of v).trace)) 0

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivA
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

abbrev wz (n i : ℕ) : Fm n := MvPolynomial.C (Polynomial.X ^ i)

theorem divZ_iff (i : ℕ) (Q : Fm n) : DivZ i Q ↔ ∃ R : Fm n, Q = R * wz n i := by
  constructor
  · intro h
    have hmem : Q ∈ Ideal.map (MvPolynomial.C : Polynomial ℂ →+* Fm n)
        (Ideal.span {(Polynomial.X ^ i : Polynomial ℂ)}) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro e
      exact Ideal.mem_span_singleton.mpr (h e)
    rw [Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨a, ha.symm⟩
  · rintro ⟨R, rfl⟩ e
    rw [mul_comm, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right _ _

theorem divZ_zero (i : ℕ) : DivZ i (0 : Fm n) := fun e => by simp

theorem divZ_add {i : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ i Q) : DivZ i (P + Q) := fun e => by
  rw [MvPolynomial.coeff_add]; exact dvd_add (hP e) (hQ e)

theorem divZ_mul {i j : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ j Q) : DivZ (i + j) (P * Q) := by
  obtain ⟨R₁, rfl⟩ := (divZ_iff i P).1 hP
  obtain ⟨R₂, rfl⟩ := (divZ_iff j Q).1 hQ
  refine (divZ_iff _ _).2 ⟨R₁ * R₂, ?_⟩
  simp only [wz, pow_add, map_mul]
  ring

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def aa (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    opH s m b k l Q = (-(cc s b)) • (MvPolynomial.C (aa m b) * yv b l k * Q) +
      ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * pderiv (b, a, d) Q) := by
  cases b <;>
  simp only [opH, cc, aa, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Bool.false_eq_true, if_true, if_false]

def RCP (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ (R : Fm n) (q : Polynomial ℂ), T (R * MvPolynomial.C q) = T R * MvPolynomial.C q

theorem opH_rcp (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : RCP (opH s m b k l) := by
  intro R q
  have hd : ∀ v, pderiv v (R * MvPolynomial.C q) = pderiv v R * MvPolynomial.C q := by
    intro v
    rw [Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [opH_apply, opH_apply]
  simp only [hd, add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc]

theorem rcp_comp {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T ∘ₗ U) := fun R q => by
  simp only [LinearMap.comp_apply, hU R q, hT _ q]

theorem rcp_add {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T + U) := fun R q => by
  simp only [LinearMap.add_apply, hT R q, hU R q, add_mul]

theorem divZ_of_rcp {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) {i : ℕ} {Q : Fm n} (hQ : DivZ i Q) : DivZ i (T Q) := by
  obtain ⟨R, rfl⟩ := (divZ_iff i Q).1 hQ
  exact (divZ_iff i _).2 ⟨T R, hT R _⟩

def LCP (Q' : Fm n) (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ R : Fm n, T (Q' * R) = Q' * T R

theorem opH_false_lcp (s : ℂ) (m : ℕ) (k l : Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (opH s m false k l) := by
  intro R
  have hd : ∀ a d : Fin n, pderiv (false, a, d) (Q' * R) = Q' * pderiv (false, a, d) R := by
    intro a d
    rw [Derivation.leibniz, hQ a d, smul_zero, add_zero, smul_eq_mul]
  rw [opH_apply, opH_apply, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_smul_comm]; exact congrArg _ (by ring)
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hd, mul_smul_comm]; exact congrArg _ (by ring)

theorem lcp_comp {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T ∘ₗ U) := fun R => by
  simp only [LinearMap.comp_apply, hU R, hT _]

theorem lcp_add {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T + U) := fun R => by
  simp only [LinearMap.add_apply, hT R, hU R, mul_add]

theorem lcp_smul {Q' : Fm n} (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) : LCP Q' (c • T) := fun R => by
  simp only [LinearMap.smul_apply, hT R, mul_smul_comm]

theorem lcp_id {Q' : Fm n} : LCP Q' (LinearMap.id : Fm n →ₗ[ℂ] Fm n) := fun _ => rfl

theorem lcp_sum {Q' : Fm n} {ι : Type*} (t : Finset ι) (T : ι → Fm n →ₗ[ℂ] Fm n) (hT : ∀ i ∈ t, LCP Q' (T i)) :
    LCP Q' (∑ i ∈ t, T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro R; simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact lcp_add (hT a (Finset.mem_insert_self a t)) (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))

theorem lcp_foldr {Q' : Fm n} {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k, LCP Q' (f k)) (L : List (Fin ρ)) :
    LCP Q' (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) := by
  induction L with
  | nil => exact lcp_id
  | cons a L ih => exact lcp_comp (hf a) ih

theorem lcp_iterate {Q' : Fm n} {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (N : ℕ) (R : Fm n) :
    T^[N] (Q' * R) = Q' * T^[N] R := by
  induction N generalizing R with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT R, ih]

theorem minorOp_false_lcp (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (minorOp s m false I J) := by
  unfold minorOp
  refine lcp_sum _ _ fun σ _ => lcp_smul _ (lcp_foldr _ (fun k => opH_false_lcp s m _ _ hQ) _)

def AT (n : ℕ) : Subalgebra (Polynomial ℂ) (Fm n) :=
  Algebra.adjoin (Polynomial ℂ) (Set.range fun v : Fin n × Fin n => (MvPolynomial.X (true, v.1, v.2) : Fm n))

theorem pderiv_false_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (false, a, d) Q = 0 := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact pderiv_X_of_ne (by simp)
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

theorem pderiv_true_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (true, a, d) Q ∈ AT n := by
  classical
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx' hy) (Subalgebra.mul_mem _ hy' hx)

theorem smul_mem_AT (c : ℂ) {Q : Fm n} (hQ : Q ∈ AT n) : c • Q ∈ AT n := by
  rw [← algebraMap_smul (Polynomial ℂ) c Q]
  exact Subalgebra.smul_mem _ hQ _

theorem yv_true_mem (i j : Fin n) : yv true i j ∈ AT n := Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem opH_true_AT (s : ℂ) (m : ℕ) (k l : Fin n) {Q : Fm n} (hQ : Q ∈ AT n) : opH s m true k l Q ∈ AT n := by
  rw [opH_apply]
  refine Subalgebra.add_mem _ (smul_mem_AT _ ?_) (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun d _ =>
    smul_mem_AT _ ?_)
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (yv_true_mem _ _)) hQ
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (yv_true_mem _ _) (yv_true_mem _ _)) (pderiv_true_AT hQ a d)

theorem foldr_AT {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k Q, Q ∈ AT n → f k Q ∈ AT n) (L : List (Fin ρ))
    {Q : Fm n} (hQ : Q ∈ AT n) : (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) Q ∈ AT n := by
  induction L with
  | nil => exact hQ
  | cons a L ih => exact hf a _ ih

theorem minorOp_true_AT (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q : Fm n} (hQ : Q ∈ AT n) :
    minorOp s m true I J Q ∈ AT n := by
  unfold minorOp
  rw [LinearMap.sum_apply]
  exact Subalgebra.sum_mem _ fun σ _ => by
    rw [LinearMap.smul_apply]
    exact smul_mem_AT _ (foldr_AT _ (fun k Q hQ => opH_true_AT s m _ _ hQ) _ hQ)

theorem iterate_AT {T : Fm n →ₗ[ℂ] Fm n} (hT : ∀ Q, Q ∈ AT n → T Q ∈ AT n) (N : ℕ) {Q : Fm n} (hQ : Q ∈ AT n) :
    T^[N] Q ∈ AT n := by
  induction N generalizing Q with
  | zero => exact hQ
  | succ N ih => rw [Function.iterate_succ_apply]; exact ih (hT Q hQ)

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DerivationConstantVanishes
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

namespace CommPf

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def al (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def k0 (s : ℂ) (b : Bool) : Fm n := MvPolynomial.C (Polynomial.C (-(cc s b)))

def mm (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n := k0 s b * (MvPolynomial.C (al m b) * yv b l k)

def dl (s : ℂ) (b : Bool) (k l : Fin n) : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
  MvPolynomial.mkDerivation (Polynomial ℂ)
    (fun v => if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0)

theorem dl_X (s : ℂ) (b : Bool) (k l : Fin n) (v : Bool × Fin n × Fin n) :
    dl s b k l (X v) = if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0 := by
  simp [dl, MvPolynomial.mkDerivation_X]

theorem smul_eq (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

theorem sum_eq (s : ℂ) (b : Bool) (k l : Fin n) (p : Fm n) :
    (∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) p)) = dl s b k l p := by
  let D : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
    ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)
  have hD : ∀ q : Fm n, D q = ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) q) := by
    intro q
    have : (D : Fm n → Fm n) = fun q => ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) q := by
      funext q
      simp only [D]
      rw [show ((∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d) :
          Derivation (Polynomial ℂ) (Fm n) (Fm n)) q) =
          Derivation.coeFnAddMonoidHom (∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)) q from rfl]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
    rw [this]
    simp only [smul_eq, k0]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hDl : D = dl s b k l := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [dl_X]
    have : (D : Fm n → Fm n) (X v) = ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) (X v) := by
      rw [hD]
      simp only [smul_eq, k0]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [this]
    obtain ⟨b0, a0, d0⟩ := v
    simp only [MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single d0]
      · simp
      · intro d _ hd; simp [Prod.ext_iff, Ne.symm hd]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha; apply Finset.sum_eq_zero; intro d _; simp [Prod.ext_iff, Ne.symm ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hb]
      apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro d _
      have : ¬ ((b0, a0, d0) = (b, a, d)) := fun h => hb (congrArg Prod.fst h)
      simp only [Pi.single_apply, this, if_false, mul_zero]
  rw [← hD, hDl]

theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (p : Fm n) :
    opH s m b k l p = mm s m b k l * p + dl s b k l p := by
  rw [← sum_eq]
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  rw [smul_eq]
  simp only [mm, k0, cc, al]
  congr 1
  split_ifs <;> ring

theorem dl_other (s : ℂ) (b b' : Bool) (h : b ≠ b') (k l a d : Fin n) : dl s b k l (yv b' a d) = 0 := by
  rw [yv, dl_X]; simp [Ne.symm h]

theorem dl_C (s : ℂ) (b : Bool) (k l : Fin n) (r : Polynomial ℂ) : dl s b k l (MvPolynomial.C r) = 0 :=
  MvPolynomial.derivation_C _ r

theorem derivation_constant_vanishes (s : ℂ) (b b' : Bool) (k l : Fin n) : dl s b k l (k0 s b' : Fm n) = 0 := dl_C _ _ _ _ _

theorem dl_yv (s : ℂ) (b : Bool) (k l a d : Fin n) : dl s b k l (yv b a d) = k0 s b * (yv b a k * yv b l d) := by
  rw [yv, dl_X]; simp

theorem key1 (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n) :
    dl s b k l (mm s m b' k' l') = dl s b' k' l' (mm s m b k l) := by
  simp only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]
  by_cases h : b = b'
  · subst h
    rw [dl_yv, dl_yv]; ring
  · rw [dl_other s b b' h, dl_other s b' b (Ne.symm h)]; ring

theorem key2 (s : ℂ) (b b' : Bool) (k l k' l' : Fin n) : ⁅dl s b k l, dl s b' k' l'⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [Derivation.commutator_apply, dl_X, dl_X]
  obtain ⟨b0, a0, d0⟩ := v
  by_cases h1 : b0 = b' <;> by_cases h2 : b0 = b
  · subst h1; subst h2
    simp only [if_true, Derivation.leibniz, derivation_constant_vanishes, dl_yv, smul_zero, add_zero, smul_eq_mul]
    simp
    ring
  · subst h1
    simp only [if_true, if_neg h2, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b b0 (Ne.symm h2)]
    simp
  · subst h2
    simp only [if_true, if_neg h1, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b' b0 (Ne.symm h1)]
    simp
  · simp [if_neg h1, if_neg h2]

end CommPf


open CommPf in
theorem comm : Comm := by
  intro n s m b b' k l k' l'
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, CommPf.opH_apply, Derivation.leibniz, map_add (f := _), smul_eq_mul]
  have h2 : CommPf.dl s b k l (CommPf.dl s b' k' l' p) = CommPf.dl s b' k' l' (CommPf.dl s b k l p) := by
    have := congrArg (fun D : Derivation (Polynomial ℂ) (Fm n) (Fm n) => D p) (CommPf.key2 s b b' k l k' l')
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  rw [h2, CommPf.key1 s m b b' k l k' l']
  ring

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DifferentiableClassFunctionParam
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem differentiable_class_function_param (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) :
    Differentiable ℂ (fun z : ℂ => clsC s z p q R B) := by
  unfold clsC
  fun_prop

theorem factor (hE : Ext) (hCh : Chain) (hBr : Bridge) {s : ℂ} (hs : s = 1 ∨ s = -1) (m N r : ℕ)
    (hdiv : DivZ r ((cayF (n := n) s m)^[N] 1)) (y : E n) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, (Delta^[N] (cls s z m 0 1)) y = z ^ r * q z := by
  obtain ⟨hO, hherm, han⟩ := hE n s hs
  set P : Fm n := (cayF (n := n) s m)^[N] 1 with hP
  choose d hd using hdiv
  set v : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2
    else (1 - (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2 with hv
  refine ⟨fun z => clsC s z m 0 1 (herm y) * ∑ e ∈ P.support, (d e).eval z * ∏ i ∈ e.support, v i ^ e i, ?_, ?_⟩
  · refine (differentiable_class_function_param s m 0 1 _).mul ?_
    exact Differentiable.fun_sum fun e _ => (Polynomial.differentiable _).mul (differentiable_const _)
  · intro z
    have hcls : cls s z m 0 1 = fun y : E n => clsC s z m 0 1 (herm y) := funext fun y => ((han z m 0 1).2 y).symm
    rw [hcls, hCh n (OmS s) (clsC s z m 0 1) hO hherm (han z m 0 1).1 N y, hBr n s hs m N z (herm y) (hherm y)]
    rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
    simp only [← hv, ← hP, Polynomial.coe_evalRingHom]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hd e, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorZ
section
noncomputable section

namespace PositivityTheory.Rg.Sw.SP

open Polynomial

theorem divZ_C_mul {n : ℕ} (i : ℕ) (p : Polynomial ℂ) (R : Fm n) (h : (X : Polynomial ℂ) ^ i ∣ p) :
    DivZ i (MvPolynomial.C p * R) := by
  intro e
  rw [MvPolynomial.coeff_C_mul]
  exact Dvd.dvd.mul_right h _

theorem pow_dvd_prod (N ρ i : ℕ) (f : ℕ → ℕ → Polynomial ℂ) (hi : i ≤ N)
    (hf : ∀ l < i, ∃ i' < ρ, f l i' = -X) :
    (X : Polynomial ℂ) ^ i ∣ ∏ l ∈ Finset.range N, ∏ i' ∈ Finset.range ρ, f l i' := by
  have h1 : (X : Polynomial ℂ) ^ i = ∏ _l ∈ Finset.range i, (X : Polynomial ℂ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h1]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun l hl => ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hi))
  obtain ⟨i', hi', he⟩ := hf l (Finset.mem_range.1 hl)
  have h2 : f l i' ∣ ∏ i' ∈ Finset.range ρ, f l i' := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi')
  rw [he] at h2
  exact dvd_trans (dvd_neg.2 dvd_rfl) h2

theorem minorZ_of (hF : MinorFormula) : MinorZ := by
  intro n s hs m i N hiN I J
  rw [hF n s hs m false (m + i) N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N (m + i) i _ hiN
  intro l hl
  refine ⟨m + l, by omega, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, map_sub, map_add (f := _)]
  ring

theorem minorZ'_of (hF : MinorFormula) : MinorZ' := by
  intro n s hs m j N hjN I J
  rw [hF n s hs m true j N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N j j _ hjN
  intro l hl
  refine ⟨l, hl, ?_⟩
  simp only [↓reduceIte, sub_self, map_zero, sub_zero]

end PositivityTheory.Rg.Sw.SP
end
end

