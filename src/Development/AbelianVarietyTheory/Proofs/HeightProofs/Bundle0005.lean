module

public import Mathlib
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonal
section
open Matrix

namespace GlobalTheory.MonomialDiag

private theorem star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      if 0 < x then (1 : ℂ) else -1 := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [star_inv₀, hst,
    show ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ * (x : ℂ) * ((Real.sqrt |x| : ℝ) : ℂ)⁻¹ =
      ((x / (Real.sqrt |x| * Real.sqrt |x|) : ℝ) : ℂ) by push_cast; ring, hs]
  split_ifs with h
  · rw [abs_of_pos h, div_self hx, Complex.ofReal_one]
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx), div_neg_self hx]
    push_cast
    ring

private theorem star_sqrt_abs_mul_sign_mul_sqrt_abs_eq (x : ℝ) (hx : x ≠ 0) :
    star ((Real.sqrt |x| : ℝ) : ℂ) * (if 0 < x then (1 : ℂ) else -1) * ((Real.sqrt |x| : ℝ) : ℂ) =
      (x : ℂ) := by
  have hst : star ((Real.sqrt |x| : ℝ) : ℂ) = ((Real.sqrt |x| : ℝ) : ℂ) := Complex.conj_ofReal _
  have hs : Real.sqrt |x| * Real.sqrt |x| = |x| := Real.mul_self_sqrt (abs_nonneg x)
  rw [hst]
  split_ifs with h
  · rw [mul_one, ← Complex.ofReal_mul, hs, abs_of_pos h]
  · rw [mul_neg_one, neg_mul, ← Complex.ofReal_mul, hs, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]
    push_cast
    ring

private theorem Jpq_equiv_apply_eq_ite_sign {n p q : ℕ} (d : Fin n → ℝ) (e : Fin n ≃ Fin p ⊕ Fin q)
    (he : ∀ i, 0 < d i ↔ (e i).isLeft = true) (i j : Fin n) :
    Formalism.UG.Jpq p q (e i) (e j) = if i = j then (if 0 < d i then (1 : ℂ) else -1) else 0 := by
  unfold Formalism.UG.Jpq
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hi := he i
    revert hi
    generalize e i = x
    rcases x with a | a <;> intro hi <;> simp_all
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    rw [if_neg hij]
    revert hne
    generalize e i = x
    generalize e j = y
    rcases x with a | a <;> rcases y with b | b <;> intro hne <;> simp_all

private theorem conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (C : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ i a, C i a = if i = e.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) :
    Cᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * C = Formalism.UG.Jpq p q := by
  ext a b
  have key := Jpq_equiv_apply_eq_ite_sign d e he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at key
  rw [key, Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, hC, hC]
    simp only [↓reduceIte]
    by_cases hab : e.symm a = e.symm b
    · rw [if_pos hab.symm, if_pos hab, hab]
      exact star_inv_sqrt_abs_mul_mul_inv_sqrt_abs_eq_sign _ (hd _)
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero, zero_mul, zero_mul]
  · intro i _ hi
    rw [hC i b, if_neg hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal {n p q : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0)
    (e : Fin n ≃ Fin p ⊕ Fin q) (he : ∀ i, 0 < d i ↔ (e i).isLeft = true)
    (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : ∀ a i, B a i = if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0) :
    Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (e i)]
    · rw [Matrix.conjTranspose_apply, hB, hB]
      simp only [↓reduceIte]
      rw [Jpq_equiv_apply_eq_ite_sign d e he, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte]
        exact star_sqrt_abs_mul_sign_mul_sqrt_abs_eq _ (hd _)
      · rw [if_neg hij, if_neg hij, mul_zero, zero_mul]
    · intro b _ hb
      rw [Matrix.conjTranspose_apply, hB, if_neg hb, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    rw [hB a j, if_neg ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_monomial : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by
  intro n p q G Q d hG hQ hd hQG
  classical
  obtain ⟨hcard, Q₁, hQ₁⟩ := Formalism.UG.P.sig_data G p q hG
  rw [Fintype.card_fin] at hcard

  let e₀ : Fin n ≃ Fin (Fintype.card {i // 0 < d i}) ⊕ Fin (Fintype.card {i // ¬ 0 < d i}) :=
    (Equiv.sumCompl (fun i => 0 < d i)).symm.trans
      (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))
  have he₀ : ∀ i, 0 < d i ↔ (e₀ i).isLeft = true := by
    intro i
    by_cases h : 0 < d i
    · simp [e₀, h]
    · simp [e₀, h]
  have hn₀ : n = Fintype.card {i // 0 < d i} + Fintype.card {i // ¬ 0 < d i} := by
    simpa using Fintype.card_congr e₀

  have h₂ : (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
      G * (Q * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0)) =
      Formalism.UG.Jpq _ _ := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0))ᴴ *
          (Qᴴ * G * Q) * Matrix.of (fun i a => if i = e₀.symm a then ((Real.sqrt |d i| : ℝ) : ℂ)⁻¹ else 0) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hQG]
          exact conjTranspose_mul_diagonal_mul_inv_sqrt_eq_Jpq d hd e₀ he₀ _ (fun i a => rfl)
  have i1 := Formalism.UG.P.sig_dim G Q₁ hQ₁ _ h₂
  have i2 := Formalism.UG.P.sig_dim G _ h₂ Q₁ hQ₁
  rw [Fintype.card_fin] at i1 i2
  have hp : Fintype.card {i // 0 < d i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < d i} = q := by omega
  let e : Fin n ≃ Fin p ⊕ Fin q := e₀.trans (Equiv.sumCongr (finCongr hp) (finCongr hq))
  have he : ∀ i, 0 < d i ↔ (e i).isLeft = true := by
    intro i
    rw [he₀ i]
    simp only [e, Equiv.trans_apply]
    cases e₀ i <;> rfl
  let B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
    Matrix.of (fun a i => if a = e i then ((Real.sqrt |d i| : ℝ) : ℂ) else 0)
  have hB : Bᴴ * Formalism.UG.Jpq p q * B = Matrix.diagonal (fun i => (d i : ℂ)) :=
    conjTranspose_mul_Jpq_mul_sqrt_eq_diagonal d hd e he B (fun a i => rfl)
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hQQ : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQu
  have hQQ' : (Q⁻¹)ᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  refine ⟨B * Q⁻¹, ?_, ?_⟩
  · calc (B * Q⁻¹)ᴴ * Formalism.UG.Jpq p q * (B * Q⁻¹) = (Q⁻¹)ᴴ * (Bᴴ * Formalism.UG.Jpq p q * B) * Q⁻¹ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Q⁻¹)ᴴ * (Qᴴ * G * Q) * Q⁻¹ := by rw [hB, hQG]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * G * (Q * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hQQ', hQQ, Matrix.one_mul, Matrix.mul_one]
  · intro a i j hi hj
    have hBQ : B * Q⁻¹ * Q = B := by
      rw [Matrix.mul_assoc, Q.nonsing_inv_mul hQu, Matrix.mul_one]
    rw [hBQ] at hi hj
    have hai : a = e i := by
      by_contra h
      exact hi (by simp [B, h])
    have haj : a = e j := by
      by_contra h
      exact hj (by simp [B, h])
    exact e.injective (hai.symm.trans haj)

end GlobalTheory.MonomialDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdjoinGlActionOfCommuteTensorPerm
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SymmTensor

variable {n d : ℕ}

def tens (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  Matrix.of fun I K => ∏ p, X p (I p) (K p)

def sym (X : Fin d → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  ∑ π : Equiv.Perm (Fin d), tens (X ∘ π)

theorem tens_mul (X Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : tens X * tens Y = tens (X * Y) := by
  ext I K
  simp only [tens, Matrix.mul_apply, Matrix.of_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem tens_one : tens (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext I K
  simp only [tens, Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem tens_single_apply (p : Fin d) (Y : Matrix (Fin n) (Fin n) ℂ) (I K : Fin d → Fin n) :
    tens (Pi.mulSingle p Y) I K = if ∀ q, q ≠ p → I q = K q then Y (I p) (K p) else 0 := by
  simp only [tens, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), Pi.mulSingle_eq_same]
  have : ∀ q ∈ Finset.univ.erase p, (Pi.mulSingle p Y : Fin d → Matrix (Fin n) (Fin n) ℂ) q (I q) (K q)
      = if I q = K q then 1 else 0 := fun q hq => by
    rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hq), Matrix.one_apply]
  rw [Finset.prod_congr rfl this, Finset.prod_ite_zero]
  simp

theorem sum_tens_single (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ a, ∑ b, Y a b • polar n d a b := by
  ext I K
  simp only [Matrix.sum_apply, tens_single_apply, polar, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : ∀ q, q ≠ p → I q = K q
  · simp [eq_true h, ite_and]
  · simp [eq_false h]

theorem sym_comp (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin d)) : sym (X ∘ σ) = sym X :=
  Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun _ => rfl

theorem sym_mul (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    sym X * ∑ p : Fin d, tens (Pi.mulSingle p Y) = ∑ i : Fin d, sym (X * Pi.mulSingle i Y) := by
  simp only [sym, Finset.sum_mul, Finset.mul_sum, tens_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => Fintype.sum_equiv π _ _ fun p => ?_
  congr 1
  funext q
  by_cases h : q = p
  · subst h; simp
  · have : π q ≠ π p := fun e => h (π.injective e)
    simp [h, this]

theorem sym_mem (X : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    sym X ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  suffices H : ∀ s : Finset (Fin d), ∀ X : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i ∉ s, X i = 1) → sym X ∈ A from
    H Finset.univ X (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X hX
    obtain rfl : X = 1 := funext fun i => hX i (by simp)
    refine A.sum_mem fun π _ => ?_
    rw [show (1 : Fin d → Matrix (Fin n) (Fin n) ℂ) ∘ π = 1 from rfl, tens_one]
    exact A.one_mem
  | insert j s hj ih =>
    intro X hX
    set Z := Function.update X j 1 with hZ
    have hZ1 : ∀ i ∉ s, Z i = 1 := fun i hi => by
      by_cases h : i = j
      · subst h; simp [hZ]
      · rw [hZ, Function.update_of_ne h]; exact hX i (by simp [h, hi])
    have hP : ∑ p : Fin d, tens (Pi.mulSingle p (X j)) ∈ A := by
      rw [sum_tens_single]
      exact A.sum_mem fun a _ => A.sum_mem fun b _ => A.smul_mem (Algebra.subset_adjoin ⟨(a, b), rfl⟩) _
    have h1 := A.mul_mem (ih Z hZ1) hP
    rw [sym_mul, ← Finset.sum_add_sum_compl s] at h1
    have h2 : ∑ i ∈ s, sym (Z * Pi.mulSingle i (X j)) ∈ A := A.sum_mem fun i hi => ih _ fun k hk => by
      have : k ≠ i := fun e => hk (e ▸ hi)
      simp [hZ1 k hk, this]
    have h3 := A.sub_mem h1 h2
    have h4 : ∀ i ∈ sᶜ, sym (Z * Pi.mulSingle i (X j)) = sym X := fun i hi => by
      have hi : i ∉ s := by simpa using hi
      rw [← sym_comp X (Equiv.swap i j)]
      congr 1
      funext k
      by_cases hki : k = i
      · subst hki; simp [hZ1 k hi]
      · by_cases hkj : k = j
        · subst hkj
          simp [hZ, hki, hX i (by simp [hi, Ne.symm hki])]
        · simp [hZ, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [add_sub_cancel_left, Finset.sum_congr rfl h4, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h3
    have h5 : ((sᶜ.card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨j, by simpa using hj⟩)
    have := A.smul_mem h3 ((sᶜ.card : ℕ) : ℂ)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

theorem tens_unit_apply (I K I' K' : Fin d → Fin n) (π : Equiv.Perm (Fin d)) :
    tens ((fun p => Matrix.single (I p) (K p) (1 : ℂ)) ∘ π) I' K' =
      if I = I' ∘ π.symm then if K = K' ∘ π.symm then 1 else 0 else 0 := by
  simp only [tens, Matrix.of_apply, Function.comp_apply, Matrix.single_apply]
  rw [Finset.prod_ite_zero, ← ite_and]
  simp only [Finset.mem_univ, forall_const, Finset.prod_const_one, forall_and, funext_iff, Function.comp_apply]
  refine if_congr (and_congr ?_ ?_) rfl rfl <;>
  exact ⟨fun h q => by simpa using h (π.symm q), fun h q => by simpa using h (π q)⟩

theorem mem_adjoin_polar (n d : ℕ) (T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ)
    (hT : ∀ π, T * permMat n d π = permMat n d π * T) :
    T ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) := by
  set A := Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
  have h1 : ∀ (π : Equiv.Perm (Fin d)) I K, T (I ∘ π) (K ∘ π) = T I K := fun π I K => by
    have := congrFun (congrFun (hT π) (I ∘ π)) K
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      π.surjective.injective_comp_right.eq_iff] at this
    simpa using this
  have h2 : ∑ I, ∑ K, T I K • sym (fun p => Matrix.single (I p) (K p) (1 : ℂ)) = ((d.factorial : ℕ) : ℂ) • T := by
    ext I' K'
    simp only [sym, Matrix.sum_apply, Matrix.smul_apply, tens_unit_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp [h1, Fintype.card_perm]
  have h3 : ((d.factorial : ℕ) : ℂ) • T ∈ A :=
    h2 ▸ A.sum_mem fun I _ => A.sum_mem fun K _ => A.smul_mem (sym_mem _) _
  have h5 : ((d.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have := A.smul_mem h3 ((d.factorial : ℕ) : ℂ)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ h5, one_smul] at this

end GlobalTheory.SymmTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalAnisotropicFrameBoundedCM
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_small_anisotropic_mem {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E}
    {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B₀ : ℝ} (H : Sized h Λ N ν B₀) {B : ℝ} (hB : 2 ≤ B)
    {W : Submodule E V} (hW : W ≠ ⊥) (hnd : ∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0)
    (hsp : W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}) :
    ∃ v, v ∈ Λ ∧ v ∈ W ∧ h v v ≠ 0 ∧ ν v ≤ B ^ 4 := by
  have hB1 : B ≤ B ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx0⟩ : ∃ x ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (le_bot_iff.1 (hsp.trans (Submodule.span_eq_bot.2 hc).le))
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hxy⟩ : ∃ y ∈ {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B}, h x y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hx0 (hnd x hx2 fun z hz => ?_)
    have : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun z hz => hc z hz
    exact this (hsp hz)
  by_cases hxx : h x x = 0
  swap
  · exact ⟨x, hx1, hx2, hxx, hx3.trans hB1⟩
  by_cases hyy : h y y = 0
  swap
  · exact ⟨y, hy1, hy2, hyy, hy3.trans hB1⟩
  refine ⟨x + h x y • y, Λ.add_mem hx1 (H.stable _ (H.int x hx1 y hy1) y hy1),
    W.add_mem hx2 (W.smul_mem _ hy2), ?_, ?_⟩
  · have : h (x + h x y • y) (x + h x y • y) = 2 * (h x y * star (h x y)) := by
      simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, hxx, hyy, H.symm x y,
        smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
      ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hxy (star_ne_zero.2 hxy))
  · have h0 : (0 : ℝ) ≤ B := by linarith
    have h1 : house (h x y) ≤ B * B := (H.form_le x y).trans (mul_le_mul hx3 hy3 (H.nonneg _) h0)
    have h2 : ν (h x y • y) ≤ B * B * B :=
      (H.smul_le _ _).trans (mul_le_mul h1 hy3 (H.nonneg _) (by positivity))
    have h3 : B ≤ B ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : 2 * B ^ 3 ≤ B * B ^ 3 := mul_le_mul_of_nonneg_right hB (by positivity)
    have := H.add_le x (h x y • y)
    nlinarith

theorem exists_small_frame_mem (n : ℕ) : ∃ k : ℕ, ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V) (N : ℤ) (ν : V → ℝ) (B₀ : ℝ), Sized h Λ N ν B₀ →
    ∀ B : ℝ, 2 ≤ B → ∀ W : Submodule E V, Module.finrank E W = n → (∀ y ∈ W, (∀ x ∈ W, h y x = 0) → y = 0) →
    W ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} →
    ∃ v : Fin n → V, (∀ i, v i ∈ Λ ∧ v i ∈ W) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
      ∀ i, h (v i) (v i) ≠ 0 ∧ ν (v i) ≤ B ^ k := by
  induction n with
  | zero => exact ⟨0, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    obtain ⟨k, ih⟩ := ih
    refine ⟨10 * k + 4, fun V _ _ _ h Λ N ν B₀ H B hB W hn hnd hsp => ?_⟩
    have hW : W ≠ ⊥ := by
      rintro rfl
      simp at hn
    have h0 : (0 : ℝ) ≤ B := by linarith
    have hB1 : (1 : ℝ) ≤ B := by linarith
    obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_small_anisotropic_mem H hB hW hnd hsp
    let g : W →ₗ[E] E := (h.flip v).domRestrict W
    let W' : Submodule E V := (LinearMap.ker g).map W.subtype
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x v = 0 := fun x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have hrank : Module.finrank E W' = n := by
      have h1 := g.finrank_range_add_finrank_ker
      have h2 : LinearMap.range g = ⊤ := by
        rw [eq_top_iff]
        intro c _
        refine ⟨(c / h v v) • ⟨v, hv2⟩, ?_⟩
        rw [map_smul]
        change (c / h v v) * h v v = c
        field_simp
      rw [h2, hn, finrank_top, Module.finrank_self] at h1
      rw [Submodule.finrank_map_subtype_eq]
      omega
    let P : V →ₗ[E] V := h v v • LinearMap.id - (h.flip v).smulRight v
    have hP : ∀ x, P x = h v v • x + (-h x v) • v := fun x => by
      simp [P, sub_eq_add_neg]
    have hPW : ∀ x ∈ W, P x ∈ W' := fun x hx => by
      rw [hmem, hP]
      refine ⟨W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hv2), ?_⟩
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have hnd' : ∀ y ∈ W', (∀ x ∈ W', h y x = 0) → y = 0 := fun y hy hy0 => by
      obtain ⟨hy1, hy2⟩ := (hmem y).1 hy
      refine hnd y hy1 fun x hx => ?_
      have h1 := hy0 _ (hPW x hx)
      rw [hP] at h1
      simp only [map_add (f := _), map_smulₛₗ, hy2, smul_eq_mul, mul_zero, add_zero, starRingEnd_apply] at h1
      exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 hv3)
    have hsp' : W' ≤ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := by
      have h1 : Submodule.span E {x | x ∈ Λ ∧ x ∈ W ∧ ν x ≤ B} ≤
          (Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10}).comap P := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨hx1, hx2, hx3⟩
        refine Submodule.subset_span ⟨?_, hPW x hx2, ?_⟩
        · rw [hP]
          exact Λ.add_mem (H.stable _ (H.int v hv1 v hv1) x hx1) (H.stable _ (H.int x hx1 v hv1).neg v hv1)
        · rw [hP]
          have a1 : house (h v v) ≤ B ^ 4 * B ^ 4 :=
            (H.form_le v v).trans (mul_le_mul hv4 hv4 (H.nonneg _) (by positivity))
          have a2 : house (-h x v) ≤ B * B ^ 4 := by
            have : house (-h x v) = house (h x v) := by simp [house]
            rw [this]
            exact (H.form_le x v).trans (mul_le_mul hx3 hv4 (H.nonneg _) h0)
          have a3 : ν (h v v • x) ≤ B ^ 4 * B ^ 4 * B :=
            (H.smul_le _ _).trans (mul_le_mul a1 hx3 (H.nonneg _) (by positivity))
          have a4 : ν ((-h x v) • v) ≤ B * B ^ 4 * B ^ 4 :=
            (H.smul_le _ _).trans (mul_le_mul a2 hv4 (H.nonneg _) (by positivity))
          have a5 : 2 * B ^ 9 ≤ B * B ^ 9 := mul_le_mul_of_nonneg_right hB (by positivity)
          calc _ ≤ _ := H.add_le _ _
            _ ≤ _ := add_le_add a3 a4
            _ = 2 * B ^ 9 := by ring
            _ ≤ B * B ^ 9 := a5
            _ = B ^ 10 := by ring
      intro x hx
      obtain ⟨hx1, hx2⟩ := (hmem x).1 hx
      have h2 : P x ∈ Submodule.span E {x | x ∈ Λ ∧ x ∈ W' ∧ ν x ≤ B ^ 10} := h1 (hsp hx1)
      rw [hP, hx2, neg_zero, zero_smul, add_zero] at h2
      exact (Submodule.smul_mem_iff _ hv3).1 h2
    obtain ⟨w, hw1, hw2, hw3⟩ := ih V h Λ N ν B₀ H (B ^ 10)
      (hB.trans (le_self_pow₀ hB1 (by norm_num))) W' hrank hnd' hsp'
    have hwv : ∀ i, h (w i) v = 0 := fun i => ((hmem _).1 (hw1 i).2).2
    refine ⟨Fin.cons v w, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ⟨hv1, hv2⟩ (fun i => ?_) i
      exact ⟨(hw1 i).1, ((hmem _).1 (hw1 i).2).1⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [H.symm, hwv, star_zero]
      · intro _
        simpa using hwv i
      · intro hij
        simpa using hw2 i j fun e => hij (by rw [e])
    · intro i
      refine Fin.cases ⟨hv3, hv4.trans (pow_le_pow_right₀ hB1 (by omega))⟩ (fun i => ?_) i
      refine ⟨(hw3 i).1, (hw3 i).2.trans ?_⟩
      rw [← pow_mul]
      exact pow_le_pow_right₀ hB1 (by omega)

theorem frameSmall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  intro E _ _ _ n
  obtain ⟨k, hk⟩ := exists_small_frame_mem (E := E) n
  refine ⟨k, fun V _ _ _ h Λ N ν B hn H => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := hk V h Λ N ν B H B H.two_le ⊤ (by rw [finrank_top, hn])
    (fun y _ hy => H.nondeg y fun x => hy x trivial) (by simp [H.span])
  exact ⟨v, fun i => (h1 i).1, h2, h3⟩

end GlobalTheory.SmoothForms
end

