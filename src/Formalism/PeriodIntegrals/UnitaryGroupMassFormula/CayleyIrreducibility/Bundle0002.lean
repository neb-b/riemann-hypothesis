module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.DivClosedOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.HighExistenceHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open MvPolynomial

section Grade

variable {σ : Type*}

def TGood (w : σ → ℕ) (c d : ℕ) (F : Polynomial (MvPolynomial σ ℂ)) : Prop :=
  ∀ j m, AddMonoidAlgebra.coeff (F.coeff j) m ≠ 0 → Finsupp.weight w m + j * c = d

theorem tgood_CC (w : σ → ℕ) (c : ℕ) (r : ℂ) : TGood w c 0 (Polynomial.C (C r)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_C] at h
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, coeff_C] at h
    by_cases hm : 0 = m
    · subst hm; simp
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [if_neg hj, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h; exact absurd rfl h

theorem tgood_mul (w : σ → ℕ) (c : ℕ) {d₁ d₂ : ℕ} {F G : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d₁ F) (hG : TGood w c d₂ G) : TGood w c (d₁ + d₂) (F * G) := by
  classical
  intro j m h
  rw [Polynomial.coeff_mul, coeff_sum] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at hx0
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul hy0)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul hy0)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  rw [← hx, ← hy, map_add (f := _), ← h1, ← h2]
  ring

theorem tgood_one (w : σ → ℕ) (c : ℕ) : TGood w c 0 (1 : Polynomial (MvPolynomial σ ℂ)) := by
  have := tgood_CC w c 1
  rwa [C_1, Polynomial.C_1] at this

theorem tgood_pow (w : σ → ℕ) (c : ℕ) {d : ℕ} {F : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d F) (k : ℕ) : TGood w c (k * d) (F ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact tgood_one w c
  | succ k ih => rw [pow_succ, Nat.succ_mul]; exact tgood_mul w c ih hF

theorem tgood_prod {α : Type*} (w : σ → ℕ) (c : ℕ) (s : Finset α) (d : α → ℕ)
    (F : α → Polynomial (MvPolynomial σ ℂ)) (h : ∀ i ∈ s, TGood w c (d i) (F i)) :
    TGood w c (∑ i ∈ s, d i) (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact tgood_one w c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact tgood_mul w c (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tgood_aeval_monomial (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (m : σ →₀ ℕ) (r : ℂ) :
    TGood w c (Finsupp.weight w m) (aeval f (monomial m r)) := by
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  have h1 := tgood_CC w c r
  have h2 := tgood_prod w c m.support (fun i => m i • w i) (fun i => f i ^ m i)
    (fun i _ => by simpa only [smul_eq_mul] using tgood_pow w c (hf i) (m i))
  have := tgood_mul w c h1 h2
  rwa [zero_add] at this

theorem aeval_support (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (P : MvPolynomial σ ℂ) (j : ℕ) (m' : σ →₀ ℕ)
    (h : AddMonoidAlgebra.coeff ((aeval f P).coeff j) m' ≠ 0) :
    ∃ m, AddMonoidAlgebra.coeff P m ≠ 0 ∧ Finsupp.weight w m' + j * c = Finsupp.weight w m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨m, mem_support_iff.mp hm, tgood_aeval_monomial w c f hf m _ j m' hm0⟩

end Grade

theorem tgood_gen {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b)
    (v : ι × Fin n × Fin n) :
    TGood (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) ((b : ℕ) - a) (v.2.1 : ℕ)
      (Polynomial.C (X v) + (if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0)) := by
  classical
  intro j m h
  rw [Polynomial.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  by_cases hj : j = 0
  · subst hj
    have h0 : AddMonoidAlgebra.coeff ((if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2))
        else 0 : Polynomial (MvPolynomial (ι × Fin n × Fin n) ℂ)).coeff 0) m = 0 := by
      split_ifs <;> simp
    rw [h0, add_zero, Polynomial.coeff_C_zero, coeff_X] at h
    by_cases hm : Finsupp.single v 1 = m
    · subst hm; simp [Finsupp.weight_single]
    · rw [if_neg hm] at h; exact absurd rfl h
  · rw [Polynomial.coeff_C, if_neg hj, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_add] at h
    by_cases hc : v.1 = τ ∧ v.2.1 = b
    · rw [if_pos hc, Polynomial.X_mul_C, Polynomial.coeff_C_mul_X] at h
      by_cases hj1 : j = 1
      · subst hj1
        rw [if_pos rfl, coeff_X] at h
        by_cases hm : Finsupp.single (τ, a, v.2.2) 1 = m
        · subst hm
          rw [Finsupp.weight_single, smul_eq_mul, one_mul, one_mul]
          have hb : (v.2.1 : ℕ) = b := congrArg Fin.val hc.2
          have hab' : (a : ℕ) < b := hab
          dsimp only
          omega
        · rw [if_neg hm] at h; exact absurd rfl h
      · rw [if_neg hj1, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h; exact absurd rfl h
    · rw [if_neg hc, Polynomial.coeff_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h; exact absurd rfl h

theorem bigDiv_support {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (m' : ι × Fin n × Fin n →₀ ℕ)
    (h : AddMonoidAlgebra.coeff (bigDiv τ a b k P) m' ≠ 0) :
    ∃ m, AddMonoidAlgebra.coeff P m ≠ 0 ∧ Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m' + k * ((b : ℕ) - a)
      = Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m :=
  aeval_support _ _ _ (tgood_gen τ a b hab) P k m' h

theorem high_existence_holds : HiEx := by
  intro ι _ _ n M hM hne
  classical
  have key : ∀ e : ℕ, ∀ P ∈ M, P ≠ 0 →
      (∀ m, AddMonoidAlgebra.coeff P m ≠ 0 → Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m < e) →
      ∃ Q ∈ M, Q ≠ 0 ∧ ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0 := by
    intro e
    induction e with
    | zero =>
      intro P _ hP0 hb
      obtain ⟨m, hm⟩ := ne_zero_iff.mp hP0
      exact absurd (hb m hm) (Nat.not_lt_zero _)
    | succ e ih =>
      intro P hPM hP0 hb
      by_cases hall : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k P = 0
      · exact ⟨P, hPM, hP0, hall⟩
      · push Not at hall
        obtain ⟨τ, a, b, hab, k, hk, hQ⟩ := hall
        refine ih _ (hM τ a b k P hPM) hQ ?_
        intro m' hm'
        obtain ⟨m, hm, heq⟩ := bigDiv_support τ a b hab k P m' hm'
        have h1 := hb m hm
        have hab' : (a : ℕ) < b := hab
        have h2 : 1 ≤ k * ((b : ℕ) - a) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        generalize k * ((b : ℕ) - a) = t at heq h2
        omega
  obtain ⟨P, hPM, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact key (P.support.sup (Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ))) + 1) P hPM hP0
    fun m hm => Nat.lt_succ_of_le (Finset.le_sup (mem_support_iff.mpr hm))

end Formalism.L2.SG.Pf.ColDictValCPf
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CayleyIrreducibility.IsUnitDetOfUnitary
section
noncomputable section

namespace Formalism.L2.SG.Pf.ColDictValCPf

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder

section Transfer

variable {ι : Type} [Fintype ι] {n : ℕ}

lemma fnOfV_one_apply (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : FramesV G) :
    fnOfV G s 1 P y = (∏ τ, (y.1 τ).det ^ s τ) * eval (fun x => y.1 x.1 x.2.1 x.2.2) P := by
  simp [fnOfV]

lemma eval_famAct (g : ι → Matrix (Fin n) (Fin n) ℂ) (x : ι × Fin n × Fin n → ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    eval x (famAct g P) = eval (fun v => ∑ c : Fin n, g v.1 v.2.1 c * x (v.1, c, v.2.2)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [famAct]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul]; simp [famAct]

def detBlocks : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det

lemma eval_detBlocks (x : ι × Fin n × Fin n → ℂ) :
    eval x (detBlocks (ι := ι) (n := n)) = ∏ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det := by
  rw [detBlocks, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

lemma detBlocks_ne_zero : (detBlocks (ι := ι) (n := n)) ≠ 0 := by
  intro h
  have hx := eval_detBlocks (ι := ι) (n := n) (fun v => (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
  rw [h, map_zero] at hx
  have h1 : ∀ τ : ι, (Matrix.of fun a b : Fin n => (fun v : ι × Fin n × Fin n =>
      (1 : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2) (τ, a, b)) = 1 := fun τ => by
    ext a b
    simp
  simp [h1] at hx

lemma fnOfV_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (h : fnOfV G s 1 P = 0) : P = 0 := by
  have hz : detBlocks (ι := ι) (n := n) * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, eval_detBlocks]
    by_cases hx : ∀ τ, (Matrix.of fun a b : Fin n => x (τ, a, b)).det ≠ 0
    · obtain ⟨y0, hy0⟩ : ∃ y0 : FramesV G, ∀ τ, y0.1 τ = Matrix.of fun a b => x (τ, a, b) :=
        ⟨⟨fun τ => Matrix.of fun a b => x (τ, a, b), fun τ => (hx τ).isUnit⟩, fun _ => rfl⟩
      have hy : fnOfV G s 1 P y0 = 0 := by rw [h]; rfl
      rw [fnOfV_one_apply] at hy
      simp only [hy0, Matrix.of_apply] at hy
      rcases mul_eq_zero.mp hy with h0 | h0
      · exact absurd h0 (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ))
      · exact mul_eq_zero_of_right _ h0
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul]
  simpa [detBlocks_ne_zero] using hz

lemma isUnit_det_of_unitary {G g : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef)
    (hg : gᴴ * G * g = G) : IsUnit g.det := by
  have hGd : G.det ≠ 0 := by
    rcases hG with h | h
    · exact h.det_pos.ne'
    · have h2 := h.det_pos.ne'
      rw [Matrix.det_neg] at h2
      intro h0
      apply h2
      rw [h0, mul_zero]
  rw [isUnit_iff_ne_zero]
  intro hg0
  have h3 := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hg0, mul_zero] at h3
  exact hGd h3.symm

theorem transfer_holds : Transfer := by
  intro ι _ n G hG lam W hW hne hinv
  set φ := fnOfV G (shiftOfV lam) 1 with hφ
  have hinj : Function.Injective φ := fun P Q hPQ => by
    have h0 : φ (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
    exact sub_eq_zero.mp (fnOfV_injective G _ _ h0)
  refine ⟨W.comap φ ⊓ CSpanV lam, inf_le_right, ?_, ?_, ?_⟩
  · obtain ⟨F, hFW, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨P, hP, rfl⟩ := hW hFW
    intro hbot
    have hPM : P ∈ W.comap φ ⊓ CSpanV lam := Submodule.mem_inf.mpr ⟨hFW, hP⟩
    rw [hbot, Submodule.mem_bot] at hPM
    exact hF0 (by rw [hPM, map_zero])
  · intro g hg P hPM
    obtain ⟨hPW, hPC⟩ := Submodule.mem_inf.mp hPM
    have hPW' : φ P ∈ W := Submodule.mem_comap.mp hPW
    obtain ⟨F', hF'W, hF'⟩ := hinv g hg (φ P) hPW'
    have hdet : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_det_of_unitary (hG τ) (hg τ)
    set cst : ℂ := ∏ τ, (g τ).det ^ (shiftOfV lam τ) with hcst
    have hcst0 : cst ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hdet τ).ne_zero
    have key : φ (famAct g P) = cst⁻¹ • F' := by
      funext y
      obtain ⟨y', hy'0⟩ : ∃ y' : FramesV G, ∀ τ, y'.1 τ = g τ * y.1 τ :=
        ⟨⟨fun τ => g τ * y.1 τ, fun τ => by
          rw [Matrix.det_mul]
          exact (hdet τ).mul (y.2 τ)⟩, fun _ => rfl⟩
      have hy' := hF' y y' hy'0
      show _ = cst⁻¹ * F' y
      rw [hy', hφ, fnOfV_one_apply, fnOfV_one_apply, eval_famAct]
      simp only [hy'0, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
      rw [← hcst]
      field_simp
    have hmemW : φ (famAct g P) ∈ W := by
      rw [key]
      exact W.smul_mem _ hF'W
    obtain ⟨P', hP'C, hP'⟩ := hW hF'W
    have hfam : famAct g P = cst⁻¹ • P' := hinj (by rw [key, map_smul, hP'])
    refine Submodule.mem_inf.mpr ⟨hmemW, ?_⟩
    rw [hfam]
    exact (CSpanV lam).smul_mem _ hP'C
  · intro hle
    apply le_antisymm hW
    rintro F ⟨P, hP, rfl⟩
    exact (Submodule.mem_inf.mp (hle hP)).1

end Transfer

end Formalism.L2.SG.Pf.ColDictValCPf
end
end

