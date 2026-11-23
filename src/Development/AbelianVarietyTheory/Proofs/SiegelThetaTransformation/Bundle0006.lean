module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionProperties
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker

namespace GlobalTheory.Phase.Doubling

noncomputable section

variable {n g : ℕ}

def rowM (j : Fin 2) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : Matrix (Fin n) (Fin g) ℚ :=
  Matrix.of fun k i => x j (k, i)

def glue (a b : Matrix (Fin n) (Fin g) ℚ) : Matrix (Fin 2) (Fin n × Fin g) ℚ :=
  Matrix.of fun j p => if j = 0 then a p.1 p.2 else b p.1 p.2

theorem rowM_glue_zero (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 0 (glue a b) = a := by
  ext k i; simp [rowM, glue]

theorem rowM_glue_one (a b : Matrix (Fin n) (Fin g) ℚ) : rowM 1 (glue a b) = b := by
  ext k i; simp [rowM, glue]

theorem glue_rowM (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) : glue (rowM 0 x) (rowM 1 x) = x := by
  ext j p; fin_cases j <;> simp [rowM, glue]

theorem dup_apply (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    dup φ x = φ (rowM 0 x) * φ (rowM 1 x) := rfl

theorem rowM_add (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x + y) = rowM j x + rowM j y := rfl

theorem rowM_sub (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x - y) = rowM j x - rowM j y := rfl

theorem rowM_smul (j : Fin 2) (c : ℚ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (c • x) = c • rowM j x := rfl

def rowEquiv (n g : ℕ) : Matrix (Fin 2) (Fin n × Fin g) ℚ ≃
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun x := (rowM 0 x, rowM 1 x)
  invFun p := glue p.1 p.2
  left_inv x := glue_rowM x
  right_inv p := by simp [rowM_glue_zero, rowM_glue_one]

theorem dot_row (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    x j ⬝ᵥ y j = ∑ k, rowM j x k ⬝ᵥ rowM j y k := by
  simp [dotProduct, rowM, Fintype.sum_prod_type]

def comp (j : Fin 2) : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ →+
    Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ where
  toFun y := (rowM j y.1, rowM j y.2)
  map_zero' := rfl
  map_add' _ _ := rfl

def glueP : (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) ×
    (Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) →+
    Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ where
  toFun z := (glue z.1.1 z.2.1, glue z.1.2 z.2.2)
  map_zero' := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> simp [glue]
  map_add' a b := by
    refine Prod.ext ?_ ?_ <;> ext j p <;> fin_cases j <;> simp [glue]

theorem comp_glueP_zero (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 0 (glueP (a, b)) = a := by
  show (rowM 0 (glue a.1 b.1), rowM 0 (glue a.2 b.2)) = a
  simp [rowM_glue_zero]

theorem comp_glueP_one (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 1 (glueP (a, b)) = b := by
  show (rowM 1 (glue a.1 b.1), rowM 1 (glue a.2 b.2)) = b
  simp [rowM_glue_one]

theorem glueP_comp (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    glueP (comp 0 y, comp 1 y) = y := by
  show (glue (rowM 0 y.1) (rowM 1 y.1), glue (rowM 0 y.2) (rowM 1 y.2)) = y
  simp [glue_rowM]

theorem om_eq (y y' : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    om y y' = om (comp 0 y) (comp 0 y') + om (comp 1 y) (comp 1 y') := by
  simp only [om, Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib]
  exact add_sub_add_comm _ _ _ _

theorem om_zero_right (y : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) : om y 0 = 0 := by
  simp [om, dotProduct]

theorem heisS_dup (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ)
    (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    heisS y.1 y.2 (dup φ) x = heisS (comp 0 y).1 (comp 0 y).2 φ (rowM 0 x) *
      heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x) := by
  have h : (∑ k, (2 * (x k ⬝ᵥ y.1 k) - y.1 k ⬝ᵥ y.2 k) : ℚ) =
      (∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) +
      (∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) := by
    simp only [Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib, Finset.mul_sum]
    exact add_sub_add_comm _ _ _ _
  unfold heisS
  rw [h, Rat.cast_add, mul_add, Complex.exp_add, dup_apply, rowM_sub, rowM_sub]
  show _ = (φ (rowM 0 x - rowM 0 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 0 x k ⬝ᵥ rowM 0 y.1 k) - rowM 0 y.1 k ⬝ᵥ rowM 0 y.2 k) : ℚ) : ℂ))) *
    (φ (rowM 1 x - rowM 1 y.2) * cexp (Real.pi * I *
    ((∑ k, (2 * (rowM 1 x k ⬝ᵥ rowM 1 y.1 k) - rowM 1 y.1 k ⬝ᵥ rowM 1 y.2 k) : ℚ) : ℂ)))
  ring

theorem isSB_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) : IsSB (dup φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx j p => ?_, fun x y hy => ?_⟩
  · rw [dup_apply] at hx
    fin_cases j
    · exact h1 _ (left_ne_zero_of_mul hx) p.1 p.2
    · exact h1 _ (right_ne_zero_of_mul hx) p.1 p.2
  · rw [dup_apply, dup_apply, rowM_add, rowM_add, rowM_smul, rowM_smul,
      h2 _ (rowM 0 y) (fun k i => hy 0 (k, i)), h2 _ (rowM 1 y) (fun k i => hy 1 (k, i))]

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨k, hk, hb⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m k,
    pow_mul b, hb, ← pow_mul]

theorem pv_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : PV φ) : PV (dup φ) := by
  obtain ⟨⟨A, ε, hV⟩, hP⟩ := h
  refine ⟨⟨(A.prod A).map glueP, fun y => ε (comp 0 y) * ε (comp 1 y), ?_⟩,
    fun x => ph_mul (hP _) (hP _)⟩
  have mem : ∀ y, y ∈ (A.prod A).map glueP ↔ comp 0 y ∈ A ∧ comp 1 y ∈ A := by
    intro y
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      rw [comp_glueP_zero, comp_glueP_one]
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨(comp 0 y, comp 1 y), ⟨ha, hb⟩, glueP_comp y⟩
  refine ⟨?_, fun y => ?_, fun y hy => ?_, fun y hy y' hy' => ?_, ?_, isSB_dup hV.sb, fun y hy => ?_⟩
  · have := (hV.fg.prod hV.fg)
    rw [AddSubgroup.fg_iff] at this ⊢
    obtain ⟨S, hS, hf⟩ := this
    exact ⟨glueP '' S, by rw [← hS, AddMonoidHom.map_closure], hf.image _⟩
  · constructor
    · intro hy y' hy'
      rw [mem] at hy hy'
      obtain ⟨m, hm⟩ := (hV.dual _).1 hy.1 _ hy'.1
      obtain ⟨k, hk⟩ := (hV.dual _).1 hy.2 _ hy'.2
      exact ⟨m + k, by rw [om_eq, hm, hk, Int.cast_add]⟩
    · intro hy
      rw [mem]
      constructor
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (a, 0)) ⟨(a, 0), ⟨ha, A.zero_mem⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, add_zero] at this
      · refine (hV.dual _).2 fun a ha => ?_
        have := hy (glueP (0, a)) ⟨(0, a), ⟨A.zero_mem, ha⟩, rfl⟩
        rwa [om_eq, comp_glueP_zero, comp_glueP_one, om_zero_right, zero_add] at this
  · rw [mem] at hy
    rw [norm_mul, hV.norm _ hy.1, hV.norm _ hy.2, one_mul]
  · rw [mem] at hy hy'
    rw [map_add (f := _), map_add (f := _), hV.semi _ hy.1 _ hy'.1, hV.semi _ hy.2 _ hy'.2, om_eq y y',
      Rat.cast_add, mul_add, Complex.exp_add]
    ring
  · obtain ⟨m, hm, h⟩ := hV.ord
    refine ⟨m, hm, fun y hy => ?_⟩
    rw [mem] at hy
    rw [map_nsmul, map_nsmul, h _ hy.1, h _ hy.2, one_mul]
  · rw [mem] at hy
    funext x
    have h0 := congrFun (hV.fix _ hy.1) (rowM 0 x)
    have h1 := congrFun (hV.fix _ hy.2) (rowM 1 x)
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    rw [heisS_dup, dup_apply, ← h0, ← h1]
    rw [h0, h1]
    linear_combination (ε (comp 1 y) * heisS (comp 1 y).1 (comp 1 y).2 φ (rowM 1 x)) * h0 +
      φ (rowM 0 x) * h1

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) : blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]

theorem blk_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · ext p q
    have := h.1.apply p.2 q.2
    by_cases hpq : p.1 = q.1
    · simp [blk, hpq, this]
    · simp [blk, hpq, Ne.symm hpq]
  · have : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (τ.map Complex.im) := by
      ext p q
      by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [this]
    exact Matrix.PosDef.one.kronecker h.2

theorem blk_inv (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  have : ((blk n τ).map fun z => (z.im : ℂ)) = blk n (τ.map fun z => (z.im : ℂ)) := by
    ext p q
    by_cases h : p.1 = q.1 <;> simp [blk, h]
  rw [this, blk_eq, blk_eq, Matrix.inv_kronecker, inv_one]

theorem expo_row (τ : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin 2 → Fin n × Fin g → ℂ) (j : Fin 2)
    (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    qv (x j) ⬝ᵥ blk n τ *ᵥ qv (x j) + 2 * (qv (x j) ⬝ᵥ ζ j) =
      ∑ k, (qv (rowM j x k) ⬝ᵥ τ *ᵥ qv (rowM j x k) +
        2 * (qv (rowM j x k) ⬝ᵥ (fun k i => ζ j (k, i)) k)) := by
  simp [dotProduct, mulVec, qv, rowM, blk, Fintype.sum_prod_type, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem thS_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin 2 → Fin n × Fin g → ℂ) :
    thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i)) := by
  have s0 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 0 (k, i))
  have s1 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 1 (k, i))
  unfold thS
  rw [tsum_mul_tsum_of_summable_norm s0 s1, ← (rowEquiv n g).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Fin.sum_univ_two, expo_row, expo_row, mul_add, Complex.exp_add, dup_apply]
  simp only [rowEquiv, Equiv.coe_fn_mk]
  ring

theorem doubling : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  intro n g φ
  refine ⟨pv_dup, fun h h' => h ?_, isSB_dup, fun u => ?_, fun τ hτ =>
    ⟨blk_siegel hτ, fun h ζ => thS_dup h hτ ζ, blk_inv τ⟩⟩
  · funext a
    have := congrFun h' (glue a a)
    rw [dup_apply, rowM_glue_zero, rowM_glue_one] at this
    exact mul_self_eq_zero.1 this
  · funext x
    simp only [dup_apply, Pi.smul_apply, smul_eq_mul]
    ring

end

end GlobalTheory.Phase.Doubling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSum
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.GaussSum

theorem twist {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by
  by_cases hz : ∑ x, e (Q x) = 0
  · exact Or.inl hz
  right
  have hsq : (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) := by
    calc (∑ x, e (Q x)) * (∑ x, e (Q x)) = ∑ x, e (ψ x - Q x) * ∑ y, e (Q y) := by
          rw [← Finset.sum_mul, ← hT]
      _ = ∑ x, ∑ z, e (Q z) * e (ψ x + B x z) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Equiv.sum_comp (Equiv.addLeft x), Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← he, ← he, Equiv.coe_addLeft, hQ]
          congr 1
          abel
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
  have hne : ∑ z, e (Q z) * ∑ x, e (ψ x + B x z) ≠ 0 := hsq ▸ mul_ne_zero hz hz
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have ha' := right_ne_zero_of_mul ha
  have h1 : ∀ y, e (ψ y + B y a) = 1 := by
    intro y
    have : ∑ x, e (ψ x + B x a) = e (ψ y + B y a) * ∑ x, e (ψ x + B x a) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addLeft y)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← he, Equiv.coe_addLeft]
      congr 1
      simp only [map_add (f := _), AddMonoidHom.add_apply]
      abel
    exact (mul_eq_right₀ ha').1 this.symm
  refine ⟨a, ?_⟩
  conv_lhs => rw [hT]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Equiv.sum_comp (Equiv.addRight a) (fun x => conj (e (Q x))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, ← he, Equiv.coe_addRight, hQ, ← mul_one (e (Q a + _)), ← h1 x, ← he]
  congr 1
  abel

def quat {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) : Fin 4 → M :=
  ![a • x 0 + (-b) • x 1 + (-c) • x 2 + (-d) • x 3,
    b • x 0 + a • x 1 + (-d) • x 2 + c • x 3,
    c • x 0 + d • x 1 + a • x 2 + (-b) • x 3,
    d • x 0 + (-c) • x 1 + b • x 2 + a • x 3]

theorem quat_add {M : Type} [AddCommGroup M] (a b c d : ℤ) (x y : Fin 4 → M) :
    quat a b c d (x + y) = quat a b c d x + quat a b c d y := by
  funext i
  fin_cases i <;> simp [quat] <;> module

theorem quat_conj {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) (i : Fin 4) :
    quat a (-b) (-c) (-d) (quat a b c d x) i = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • x i := by
  fin_cases i <;> simp [quat] <;> module

theorem quat_form {M W : Type} [AddCommGroup M] [AddCommGroup W] (β : M →+ M →+ W) (a b c d : ℤ)
    (x y : Fin 4 → M) :
    ∑ i, β (quat a b c d x i) (quat a b c d y i) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • ∑ i, β (x i) (y i) := by
  simp only [Fin.sum_univ_four, quat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply]
  module

theorem pow_four {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by
  classical
  set n := Fintype.card M with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  have hnx : ∀ x : M, (n : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares (n - 1)
  have hm : ((a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2) = (n : ℤ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℤ)) habcd
    push_cast [Nat.cast_sub hn1] at h
    exact h
  have hinj : Function.Injective (quat (M := M) (a : ℤ) b c d) := by
    intro x y hxy
    funext i
    have hx := quat_conj (a : ℤ) b c d x i
    have hy := quat_conj (a : ℤ) b c d y i
    rw [hm, sub_smul, hnx, one_smul, zero_sub] at hx hy
    rw [← neg_inj, ← hx, ← hy, hxy]
  have hbij := hinj.bijective_of_finite
  have hprod : ∀ y : Fin 4 → W, e (∑ i, y i) = ∏ i, e (y i) := by
    intro y; simp only [Fin.sum_univ_four, Fin.prod_univ_four, he]
  have hS4 : (∑ x, e (q x)) ^ 4 = ∑ x : Fin 4 → M, e (∑ i, q (x i)) := by
    rw [Finset.sum_pow', Fintype.piFinset_univ]
    exact Finset.sum_congr rfl (fun x _ => (hprod (fun i => q (x i))).symm)
  let B : (Fin 4 → M) →+ (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ∑ i, β (x i) (y i))
      (fun y z => by simp [Finset.sum_add_distrib]))
    (fun x y => by ext z; simp [Finset.sum_add_distrib])
  have hB : ∀ x y, B x y = ∑ i, β (x i) (y i) := fun _ _ => rfl
  have hQ : ∀ x y : Fin 4 → M, ∑ i, q ((x + y) i) = ∑ i, q (x i) + ∑ i, q (y i) + B x y := by
    intro x y
    simp only [hB, Pi.add_apply, hq, Finset.sum_add_distrib]
  have hnB : ∀ x y, (n : ℤ) • B x y = 0 := by
    intro x y
    rw [← map_zsmul]
    have : (n : ℤ) • y = 0 := funext fun i => hnx (y i)
    rw [this, map_zero]
  let ψ : (Fin 4 → M) →+ W := AddMonoidHom.mk'
    (fun x => ∑ i, q (quat (a : ℤ) b c d x i) + ∑ i, q (x i)) (by
      intro x y
      rw [quat_add, hQ, hQ, hB (quat _ _ _ _ _), quat_form, hm, ← hB, sub_smul, hnB, one_smul]
      abel)
  have := twist e he hc h0 (fun x : Fin 4 → M => ∑ i, q (x i)) B hQ ψ (by
    rw [← hbij.sum_comp (fun x => e (∑ i, q (x i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    simp [ψ])
  rw [← hS4] at this
  simpa only [hprod] using this

theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, h⟩ := ha
  obtain ⟨k, hk, h'⟩ := hb
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [mul_pow, pow_mul, h, mul_comm m, pow_mul, h']; simp

theorem isMu_norm {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this

theorem ph_sum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  intro M _ _ f ⟨h1, h3⟩
  have hmu : ∀ x, IsMu (f x) := fun x => h1 x trivial
  let u : M → Circle := fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (isMu_norm (hmu x))⟩
  let p : M → Additive Circle := fun x => Additive.ofMul (u x)
  have hp : ∀ x y z, p (x + y + z) + p x + p y + p z = p (x + y) + p (y + z) + p (x + z) + p 0 := by
    intro x y z
    have : u (x + y + z) * u x * u y * u z = u (x + y) * u (y + z) * u (x + z) * u 0 :=
      Circle.ext (by simp only [Circle.coe_mul]; exact h3 x trivial y trivial z trivial)
    exact congrArg Additive.ofMul this
  let β : M →+ M →+ Additive Circle := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => p (x + y) - p x - p y + p 0)
      (fun y z => by
        have := hp x y z
        rw [← add_assoc]
        rw [← sub_eq_zero] at this ⊢; rw [← this]; abel))
    (fun x y => by
      ext1 z
      have := hp x y z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← sub_eq_zero] at this ⊢; rw [← this]; abel)
  let e : Additive Circle → ℂ := fun t => ((Additive.toMul t : Circle) : ℂ)
  have he : ∀ s t, e (s + t) = e s * e t := fun s t => by simp [e]
  have hc : ∀ t, e (-t) = conj (e t) := fun t => by
    simp only [e, toMul_neg]; exact Circle.coe_inv_eq_conj _
  have hf : ∀ x, f x = f 0 * e (p x - p 0) := by
    intro x
    have : e (p 0 + (p x - p 0)) = e (p x) := by congr 1; abel
    rw [he] at this
    exact this.symm
  have hmu' : ∀ x, IsMu (e (p x - p 0)) := by
    intro x
    rw [sub_eq_add_neg, he, hc]
    refine isMu_mul (hmu x) ?_
    obtain ⟨m, hm, h⟩ := hmu 0
    exact ⟨m, hm, by rw [← map_pow]; change conj (f 0 ^ m) = 1; rw [h, map_one]⟩
  have hsum : ∑ x, f x = f 0 * ∑ x, e (p x - p 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => hf x
  rw [hsum]
  rcases pow_four e he hc (by simp [e]) (fun x => p x - p 0) β (fun x y => by
    simp only [β, AddMonoidHom.mk'_apply]; abel) with h | ⟨a, h⟩
  · rw [pow_eq_zero_iff (by norm_num)] at h
    rw [h, mul_zero]; exact ph_zero
  · set S := ∑ x, e (p x - p 0)
    have hz : IsMu (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) := by
      refine isMu_mul ?_ ?_
      · obtain ⟨m, hm, h⟩ := hmu 0
        exact ⟨m, hm, by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]⟩
      · rw [Fin.prod_univ_four]
        exact isMu_mul (isMu_mul (isMu_mul (hmu' _) (hmu' _)) (hmu' _)) (hmu' _)
    obtain ⟨m, hm, hz⟩ := hz
    refine ⟨8 * m, by omega, ?_⟩
    have h8 : (f 0 * S) ^ 8 = (f 0 ^ 8 * ∏ i, e (p (a i) - p 0)) * ((‖f 0 * S‖ : ℝ) : ℂ) ^ 8 := by
      have hn : ((‖S‖ : ℝ) : ℂ) ^ 8 = S ^ 4 * conj (S ^ 4) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]; push_cast; ring
      rw [norm_mul, isMu_norm (hmu 0), one_mul, hn]
      linear_combination f 0 ^ 8 * S ^ 4 * h
    rw [pow_mul, h8, mul_pow, hz, one_mul, pow_mul]

end GlobalTheory.Phase.GaussSum
end

