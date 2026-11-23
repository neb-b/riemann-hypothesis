module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommPowEntry
section
namespace GlobalTheory.CommutatorPowerEntry

open Finset

theorem comm_pow_entry (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) :
    ∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b =
      (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A) := by
  induction k with
  | zero =>
    intro a b c d
    simp only [pow_zero, Matrix.one_apply]
    by_cases hcd : c = d <;> by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp_all [eq_comm]
  | succ k ih =>
    intro a b c d
    have h' : ∀ c d : Fin N, E a b * E c d - E c d * E a b =
        (if b = c then E a d else 0) - (if d = a then E c b else 0) := h a b
    have key : ∀ x y : A, E a b * (x * y) - (x * y) * E a b =
        (E a b * x - x * E a b) * y + x * (E a b * y - y * E a b) := by
      intro x y; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key, ih, h']
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false,
      Finset.sum_const_zero] <;> abel

theorem comm_trace_pow (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A)
    (h : GlobalTheory.Alc.GlRel E) (k : ℕ) (a b : Fin N) :
    E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    comm_pow_entry A N E h k]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem main : ∀ (A : Type) [inst : Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlobalTheory.Alc.GlRel E → ∀ (k : ℕ), (∀ (a b c d : Fin N), E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else (0 : A)) - if d = a then (E ^ k) c b else (0 : A)) ∧ ∀ (a b : Fin N), E a b * Matrix.trace (E ^ k) = Matrix.trace (E ^ k) * E a b := by
  intro A _ N E h k
  exact ⟨comm_pow_entry A N E h k, comm_trace_pow A N E h k⟩

end GlobalTheory.CommutatorPowerEntry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommRowDivOfCommRowE
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem pol_eq_rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) :
    PI.WGL.pol R a b g = rowE R r n a b g := by
  rw [PI.WGL.pol_apply]
  simp [rowE, LinearMap.sum_apply]

theorem rowDiv_succ_smul {r n : ℕ} (a b : Fin r) (k : ℕ) (g : MvPolynomial (Fin r × Fin n) ℚ) :
    ((k : ℚ) + 1) • rowDiv ℚ a b (k + 1) g =
      rowDiv ℚ a b k (rowE ℚ r n a b g) - (if a = b then (k : ℚ) • rowDiv ℚ a b k g else 0) := by
  have h := PI.WGL.rowDiv_succ ℚ a b k g
  rw [pol_eq_rowE_apply] at h
  rw [← h]
  split_ifs <;> simp [Algebra.smul_def, mul_comm]

theorem comm_rowDiv_of_comm_rowE : ∀ (r n : ℕ) (T : Module.End ℚ (MvPolynomial (Fin r × Fin n) ℚ)),
    (∀ a b, T * rowE ℚ r n a b = rowE ℚ r n a b * T) →
      ∀ a b k f, T (rowDiv ℚ a b k f) = rowDiv ℚ a b k (T f) := by
  intro r n T hT a b k
  have hE : ∀ g, T (rowE ℚ r n a b g) = rowE ℚ r n a b (T g) := fun g => by
    have := LinearMap.congr_fun (hT a b) g
    simpa only [Module.End.mul_apply] using this
  induction k with
  | zero => intro f; rw [PI.WGL.rowDiv_zero, PI.WGL.rowDiv_zero]
  | succ k ih =>
    intro f
    have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
    apply smul_right_injective _ hne
    simp only
    rw [← map_smul, rowDiv_succ_smul, rowDiv_succ_smul, map_sub, ih, hE]
    split_ifs
    · rw [map_smul, ih]
    · rw [map_zero]

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfDominantWeightsLowestAlcoveLinked
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natCast_eq_le_prime {p n m : ℕ} (hp : 0 < p) (hn : n ≤ p) (hm : m ≤ p)
    (h : (n : ZMod p) = (m : ZMod p)) : n = m ∨ (n = 0 ∧ m = p) ∨ (n = p ∧ m = 0) := by
  have h' : n % p = m % p := (ZMod.natCast_eq_natCast_iff' n m p).1 h
  rcases hn.eq_or_lt with rfl | hn' <;> rcases hm.eq_or_lt with rfl | hm'
  · exact Or.inl rfl
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hm'] at h'
    exact Or.inr (Or.inr ⟨rfl, h'.symm⟩)
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hn'] at h'
    exact Or.inr (Or.inl ⟨h', rfl⟩)
  · rw [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hm'] at h'
    exact Or.inl h'

theorem eq_of_shifted_residues_eq :
    ∀ (p N : ℕ), p.Prime → ∀ (ν μ : Fin N → ℕ), Antitone ν → Antitone μ →
      (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) →
      (∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((ν i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card
        = (Finset.univ.filter fun i : Fin N => ((μ i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card) →
      μ = ν := by
  intro p N hp ν μ hν hμ h hc
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · funext i; exact i.elim0
  obtain ⟨h1, h2, h3⟩ := h hN
  have hp0 : 0 < p := hp.pos
  let a : Fin N → ℕ := fun i => ν i + (N - 1 - i.val)
  let b : Fin N → ℕ := fun i => μ i + (N - 1 - i.val)
  have hc' : ∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = x).card
      = (Finset.univ.filter fun i : Fin N => ((b i : ℕ) : ZMod p) = x).card := hc
  have ha : StrictAnti a := by
    intro i j hij
    have h4 := hν hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show ν j + (N - 1 - j.val) < ν i + (N - 1 - i.val)
    omega
  have hb : StrictAnti b := by
    intro i j hij
    have h4 := hμ hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show μ j + (N - 1 - j.val) < μ i + (N - 1 - i.val)
    omega
  let z : Fin N := ⟨0, hN⟩
  let l : Fin N := ⟨N - 1, by omega⟩
  have hal : a l = 0 := by
    show ν ⟨N - 1, _⟩ + (N - 1 - (N - 1)) = 0
    rw [h1]; omega
  have haz : a z ≤ p := by
    show ν ⟨0, hN⟩ + (N - 1 - 0) ≤ p
    omega
  have hbz : b z ≤ a z := by
    show μ ⟨0, hN⟩ + (N - 1 - 0) ≤ ν ⟨0, hN⟩ + (N - 1 - 0)
    omega
  have hzle : ∀ i : Fin N, z ≤ i := fun i => Nat.zero_le _
  have hap : ∀ i, a i ≤ p := fun i => (ha.antitone (hzle i)).trans haz
  have hbp : ∀ i, b i ≤ p := fun i => (hb.antitone (hzle i)).trans (hbz.trans haz)

  have two : ∀ i, a i = p → (∃ j, b j = 0) ∧ (∃ j, b j = p) := by
    intro i hi
    have hne : i ≠ l := by
      rintro rfl
      omega
    have h1lt : 1 < (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = 0).card := by
      refine Finset.one_lt_card.2 ⟨i, ?_, l, ?_, hne⟩
      · simp [hi]
      · simp [hal]
    rw [hc' 0] at h1lt
    obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.1 h1lt
    have e₁ : ((b j₁ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₁
    have e₂ : ((b j₂ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₂
    have r₁ := natCast_eq_le_prime hp0 (hbp j₁) hp0.le e₁
    have r₂ := natCast_eq_le_prime hp0 (hbp j₂) hp0.le e₂
    have hbne : b j₁ ≠ b j₂ := fun e => hj (hb.injective e)
    have s₁ : b j₁ = 0 ∨ b j₁ = p := by omega
    have s₂ : b j₂ = 0 ∨ b j₂ = p := by omega
    rcases s₁ with s₁ | s₁ <;> rcases s₂ with s₂ | s₂
    · exact absurd (s₁.trans s₂.symm) hbne
    · exact ⟨⟨j₁, s₁⟩, ⟨j₂, s₂⟩⟩
    · exact ⟨⟨j₂, s₂⟩, ⟨j₁, s₁⟩⟩
    · exact absurd (s₁.trans s₂.symm) hbne

  have sub : ∀ i, ∃ j, b j = a i := by
    intro i
    have hpos : 0 < (Finset.univ.filter fun k : Fin N => ((a k : ℕ) : ZMod p) = (a i : ZMod p)).card :=
      Finset.card_pos.2 ⟨i, by simp⟩
    rw [hc' (a i : ZMod p)] at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
    have ej : ((b j : ℕ) : ZMod p) = ((a i : ℕ) : ZMod p) := by simpa using hj
    rcases natCast_eq_le_prime hp0 (hbp j) (hap i) ej with e | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact ⟨j, e⟩
    · obtain ⟨k, hk⟩ := (two i e₂).2
      exact ⟨k, hk.trans e₂.symm⟩
    · have hbz' : b z = p := le_antisymm (hbp z) (e₁ ▸ hb.antitone (hzle j))
      have haz' : a z = p := le_antisymm haz (hbz' ▸ hbz)
      obtain ⟨k, hk⟩ := (two z haz').1
      exact ⟨k, hk.trans e₂.symm⟩
  have himg : Finset.univ.image a = Finset.univ.image b := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨j, hj⟩ := sub i
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    · rw [Finset.card_image_of_injective _ ha.injective,
        Finset.card_image_of_injective _ hb.injective]
  have hrange : Set.range b = Set.range a := by
    have := congrArg (fun s : Finset ℕ => (s : Set ℕ)) himg
    simpa using this.symm
  have hab : b = a := (StrictAnti.range_inj hb ha).1 hrange
  funext i
  have e : b i = a i := congrFun hab i
  have e' : μ i + (N - 1 - i.val) = ν i + (N - 1 - i.val) := e
  omega

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLSchemeSubmoduleStableUnderRowPerm
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.AlcPerm

theorem rowAct_permMatrix (k : Type) [Field k] (N : ℕ) (σ : Equiv.Perm (Fin N))
    (f : MvPolynomial (Fin N × Fin N) k) :
    Formalism.GradedWeylDivisibility.rowAct k (n := N) (σ.permMatrix k) f = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f := by
  have : Formalism.GradedWeylDivisibility.rowAct k (n := N) (σ.permMatrix k) = rename (fun v : Fin N × Fin N => (σ v.1, v.2)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, rename_X]
    rw [Finset.sum_eq_single (σ v.1)]
    · simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    · intro b _ hb
      simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Ne.symm hb]
    · simp
  rw [this]

theorem perm_stable : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ σ : Equiv.Perm (Fin N), ∀ f ∈ M, rename (fun v : Fin N × Fin N => (σ v.1, v.2)) f ∈ M := by
  intro k _ N lam M hM σ f hf
  have hdet : ((σ⁻¹).permMatrix k).det ≠ 0 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h]
  set g : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hg
  have h1 := hM k g f hf
  have hid : (map (algebraMap k k) : MvPolynomial (Fin N × Fin N) k →+* _) = RingHom.id _ := by
    rw [Algebra.algebraMap_self]; exact RingHom.ext fun p => map_id p
  have hspan : Submodule.span k (map (algebraMap k k) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) = M := by
    rw [hid]; simp
  rw [hspan, hid, RingHom.id_apply] at h1
  have hgT : (g : Matrix (Fin N) (Fin N) k).transpose = σ.permMatrix k := by
    rw [hg]
    show ((σ⁻¹).permMatrix k).transpose = _
    rw [Matrix.transpose_permMatrix, inv_inv]
  unfold sqAct at h1
  rw [hgT, rowAct_permMatrix] at h1
  have hu : IsUnit (detPow k N g lam.detShift) := by
    unfold detPow; exact Units.isUnit _
  rcases hu with ⟨u, hu⟩
  rw [← hu] at h1
  have := M.smul_mem ((u⁻¹ : kˣ) : k) h1
  rwa [smul_smul, Units.inv_mul, one_smul] at this

end GlobalTheory.AlcPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.MultSieve

theorem norm_sq_gaussSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  have h := GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  rw [← star_gaussSum_eq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simpa using h

theorem sum_norm_sq_char {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2
      = q.totient * ∑ b : ZMod q, if IsUnit b then ‖F b‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c)) := by
    intro χ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have := MulChar.star_apply' χ⁻¹ c
      rwa [inv_inv] at this
    rw [map_mul, this]; ring
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  by_cases hb : IsUnit b
  · have h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c
        = if b = c then (q.totient : ℂ) else 0 := by
      intro c
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      obtain ⟨u, rfl⟩ := hb
      rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp [h1, hb, Complex.mul_conj']
  · simp [hb, MulChar.map_nonunit _ hb]

theorem sum_primitive_le {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
  classical
  set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 := by
    intro χ hχ
    have hχ' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
    rw [← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]
    congr 2
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)
    rw [inv_inv] at h
    rw [mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.mulShift_apply]; ring
  have h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0)
      = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp)
      (fun b _ => by simpa using ZMod.val_lt b)
      (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_
    intro b _
    refine if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    have := ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)
    push_cast at this
    rw [this]
    congr 2
    push_cast; ring
  rw [← h2]
  have h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive}
      = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := by simp
  rw [h3, finsum_mem_coe_finset]
  refine le_of_mul_le_mul_left ?_ hq
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => by positivity).trans ?_
  rw [sum_norm_sq_char]
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
    (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)

theorem farey_spaced (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast hb)
  have hc1 : (c : ℝ) / r < 1 := (div_lt_one hr0).2 (by exact_mod_cast hc)
  have hb0 : 0 ≤ (b : ℝ) / q := by positivity
  have hc0 : 0 ≤ (c : ℝ) / r := by positivity
  have hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0 := by
    intro h
    have h1 : (k : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < k := by linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have : k = 0 := by omega
    subst this
    apply hne
    simp at h
    linarith
  have he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r) := by
    push_cast; field_simp
  rw [he] at hk ⊢
  have hm : (b * r - c * q - k * q * r : ℤ) ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  have hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
  rw [sq]
  gcongr

theorem reduced_inj {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by
  have := Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq)
    (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc)
    (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)
  omega

end GlobalTheory.MultSieve

namespace GlobalTheory

theorem multiplicative_large_sieve : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro Q M N a hQ
  classical
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set P := (Finset.range Q).sigma
    (fun q => (Finset.range (q + 1)).filter (fun b => Nat.Coprime b (q + 1))) with hP
  set φ : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) with hφ
  have hmem : ∀ p ∈ P, p.1 < Q ∧ p.2 < p.1 + 1 ∧ Nat.Coprime p.2 (p.1 + 1) := by
    intro p hp
    simpa only [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] using hp
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, b⟩ hp ⟨r, c⟩ hp' h
    obtain ⟨h1, h2⟩ := MultSieve.reduced_inj (Nat.succ_pos q) (Nat.succ_pos r)
      (hmem _ hp).2.2 (hmem _ hp').2.2 h
    obtain rfl : q = r := by omega
    obtain rfl : b = c := h2
    rfl
  have h := additive_large_sieve M N a (P.image φ) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith) ?_
  · rw [Finset.sum_image hinj, one_div_one_div, hP, Finset.sum_sigma] at h
    exact (Finset.sum_le_sum fun q _ => MultSieve.sum_primitive_le _ a).trans h
  · intro x hx y hy hxy k
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hy
    exact MultSieve.farey_spaced Q _ _ _ _ (hmem _ hp).1 (hmem _ hp').1 (hmem _ hp).2.1
      (hmem _ hp').2.1 hxy k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModule
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowDeg_dominated_of_mem_dualWeyl (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ) :
    ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support,
      (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧
      ∑ a, rowDeg m a = ∑ a, ν a := by
  classical
  intro f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm
    have h := bidetDominance k N N K sz hsz I m hm
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (support_add hm) with h | h
    · exact hx m h
    · exact hy m h
  | smul c x _ hx =>
    intro m hm
    exact hx m (support_smul hm)

end GlobalTheory.Alc
end

