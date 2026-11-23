module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.TensorActionLieRelations
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCliffordLowestVector
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.CliffModel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

def IsCAR {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] (A : M → Matrix ι ι ℂ) : Prop :=
  (∀ p r, A p * A r + A r * A p = 0) ∧
    ∀ p r, A p * (A r)ᴴ + (A r)ᴴ * A p = if p = r then 1 else 0

def annM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def parM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def vacM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

theorem annM_sq : annM * annM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_conj : annMᴴ = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.conjTranspose_apply]

theorem annM_car : annM * annMᴴ + annMᴴ * annM = 1 := by
  rw [annM_conj]
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_sq : parM * parM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_herm : parMᴴ = parM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.conjTranspose_apply]

theorem parM_annM : parM * annM + annM * parM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_vacM : annM * vacM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, vacM, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_fock (m : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (A : Fin m → Matrix ι ι ℂ) (G Q : Matrix ι ι ℂ),
    IsCAR A ∧ G * G = 1 ∧ Gᴴ = G ∧ (∀ p, G * A p + A p * G = 0) ∧ Q ≠ 0 ∧ ∀ p, A p * Q = 0 := by
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, fun p => p.elim0, 1, 1, ⟨fun p => p.elim0, fun p => p.elim0⟩,
      by simp, by simp, fun p => p.elim0, one_ne_zero, fun p => p.elim0⟩
  | succ m ih =>
    obtain ⟨ι, _, _, A, G, Q, ⟨h1, h2⟩, hG, hGh, hGA, hQ, hv⟩ := ih
    have hGAh : ∀ i, G * (A i)ᴴ + (A i)ᴴ * G = 0 := by
      intro i
      have := congrArg conjTranspose (hGA i)
      simpa [conjTranspose_add, conjTranspose_mul, hGh, add_comm] using this
    refine ⟨ι × Fin 2, inferInstance, inferInstance,
      Fin.cases (G ⊗ₖ annM) (fun i => A i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)),
      G ⊗ₖ parM, Q ⊗ₖ vacM, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_sq, kronecker_zero, add_zero]
        | succ r =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker, hGA, zero_kronecker]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, ← add_kronecker, h1,
            zero_kronecker]
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, conjTranspose_kronecker, hGh, ← mul_kronecker_mul, hG,
            ← kronecker_add, annM_car, if_true, one_kronecker_one]
        | succ r =>
          have hne : (0 : Fin (m + 1)) ≠ r.succ := (Fin.succ_ne_zero r).symm
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGAh, zero_kronecker, if_neg hne]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          have hne : p.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero p
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, hGh,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, if_neg hne]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, ← add_kronecker, h2, Fin.succ_inj]
          split_ifs <;> simp
    · rw [← mul_kronecker_mul, hG, parM_sq, one_kronecker_one]
    · rw [conjTranspose_kronecker, hGh, parM_herm]
    · intro p
      induction p using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, ← mul_kronecker_mul, hG, ← kronecker_add, parM_annM, kronecker_zero]
      | succ p =>
        simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGA,
          zero_kronecker]
    · intro h
      apply hQ
      ext i j
      have := congrFun (congrFun h (i, 0)) (j, 0)
      simpa [vacM, kroneckerMap_apply] using this
    · intro p
      induction p using Fin.cases with
      | zero => simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_vacM, kronecker_zero]
      | succ p => simp only [Fin.cases_succ, ← mul_kronecker_mul, hv, zero_kronecker]

theorem car_lin {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] {A : M → Matrix ι ι ℂ}
    (hA : IsCAR A) (x y u v : ℂ) (p r : M) :
    (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (if p = r then x * v + y * u else 0) • (1 : Matrix ι ι ℂ) := by
  obtain ⟨h1, h2⟩ := hA
  have h3 : (A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ = 0 := by
    have := congrArg conjTranspose (h1 p r)
    simpa [conjTranspose_add, conjTranspose_mul, add_comm] using this
  have key : (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (x * u) • (A p * A r + A r * A p) + (x * v) • (A p * (A r)ᴴ + (A r)ᴴ * A p) +
        (y * u) • (A r * (A p)ᴴ + (A p)ᴴ * A r) + (y * v) • ((A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    module
  rw [key, h1, h2, h2, h3]
  by_cases h : p = r
  · subst h
    simp [add_smul]
  · simp [h, Ne.symm h]

def coefA {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then 0 else if b < a then s else 1

def coefC {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then s else if b < a then 0 else 1

def modeOf {n : ℕ} (a b : Fin n) : Fin n × Fin n := (min a b, max a b)

theorem modeOf_comm {n : ℕ} (a b : Fin n) : modeOf a b = modeOf b a := by
  simp [modeOf, min_comm, max_comm]

theorem modeOf_lt {n : ℕ} {a b : Fin n} (h : a < b) : modeOf a b = (a, b) := by
  simp [modeOf, min_eq_left h.le, max_eq_right h.le]

theorem modeOf_gt {n : ℕ} {a b : Fin n} (h : b < a) : modeOf a b = (b, a) := by
  simp [modeOf, min_eq_right h.le, max_eq_left h.le]

theorem modeOf_self {n : ℕ} (a : Fin n) : modeOf a a = (a, a) := by
  simp [modeOf]

theorem coef_rel {n : ℕ} {s : ℂ} (hs : s * s = 2) (a b d e : Fin n) :
    (if modeOf a b = modeOf d e then coefA s a b * coefC s d e + coefC s a b * coefA s d e else 0) =
      if a = e ∧ b = d then 2 else 0 := by
  rcases lt_trichotomy a b with hab | rfl | hab <;> rcases lt_trichotomy d e with hde | rfl | hde
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [modeOf_lt hab, modeOf_self, h1]
  · simp only [modeOf_lt hab, modeOf_gt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    simp [hs]
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h2 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_lt hde, modeOf_self, h1, h2]
  · simp only [modeOf_self, Prod.mk.injEq, coefA, coefC, lt_irrefl, if_false, and_self]
    split_ifs <;> norm_num
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h3 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hde, modeOf_self, h1, h3]
  · simp only [modeOf_gt hab, modeOf_lt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    by_cases h : b = d ∧ a = e
    · simp [h, hs]
    · have h' : ¬ (a = e ∧ b = d) := fun g => h ⟨g.2, g.1⟩
      simp [h, h']
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    have h2 : ¬ (b = d ∧ a = d) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hab, modeOf_self, h1, h2]
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]

theorem star_coefC {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefC s a b) = coefA s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h, hs]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h]

theorem star_coefA {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefA s a b) = coefC s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h, hs]

theorem exists_cliff_model : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  intro n
  obtain ⟨ι, _, _, A0, G, Q, ⟨h1, h2⟩, -, -, -, hQ, hv⟩ :=
    exists_fock (Fintype.card (Fin n × Fin n))
  let e := Fintype.equivFin (Fin n × Fin n)
  let A : Fin n × Fin n → Matrix ι ι ℂ := fun p => A0 (e p)
  have hA : IsCAR A := ⟨fun p r => h1 _ _, fun p r => by simp [A, h2, e.injective.eq_iff]⟩
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs : s * s = 2 := by
    simp only [s, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs' : star s = s := Complex.conj_ofReal _
  refine ⟨ι, inferInstance, inferInstance,
    fun a b => coefA s a b • A (modeOf a b) + coefC s a b • (A (modeOf a b))ᴴ, ⟨?_, ?_⟩, ?_⟩
  · intro a b d e'
    rw [car_lin hA, coef_rel hs]
    split_ifs
    · simp [two_smul, one_add_one_eq_two]
    · simp
  · intro a b
    simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_conjTranspose, star_coefA hs',
      star_coefC hs', modeOf_comm a b]
    rw [add_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (by ext i j; exact h i j)
    refine ⟨fun i => Q i j, fun h => hij (congrFun h i), ?_⟩
    intro a b hab
    have hcol : ∀ M : Matrix ι ι ℂ, M * Q = 0 → M *ᵥ (fun i => Q i j) = 0 := by
      intro M hM
      funext k
      have := congrFun (congrFun hM k) j
      simpa [Matrix.mul_apply, mulVec, dotProduct] using this
    apply hcol
    simp only [coefA, coefC, hab, lt_asymm hab, if_true, if_false, zero_smul, add_zero,
      smul_mul_assoc]
    simp [A, hv]

end GlobalTheory.CompanionTheory.CliffModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModule
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Extremal

variable {n : ℕ}

def permM (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = w j then 1 else 0

theorem permM_conjTranspose (w : Equiv.Perm (Fin n)) : (permM w)ᴴ = permM w⁻¹ := by
  ext i j
  simp only [permM, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = w i
  · have h2 : i = w⁻¹ j := by subst h; simp
    rw [if_pos h, if_pos h2]; simp
  · have h2 : ¬ i = w⁻¹ j := fun e => h (by rw [e]; simp)
    rw [if_neg h, if_neg h2]; simp

theorem permM_mul_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) = Matrix.single (w c) d 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · by_cases h1 : i = w c <;> by_cases h2 : d = j
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h2, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem single_mul_permM (v : Equiv.Perm (Fin n)) (c d : Fin n) :
    Matrix.single c d (1 : ℂ) * permM v = Matrix.single c (v⁻¹ d) 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single d]
  · by_cases h1 : c = i
    · by_cases h2 : d = v j
      · subst h1 h2; simp
      · subst h1
        have h3 : ¬ v.symm d = j := fun e => h2 (by rw [← e]; simp)
        simp [h2, h3]
    · simp [h1]
  · intro b _ hb
    rw [if_neg (fun q => hb q.2.symm)]; simp
  · simp

theorem permM_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) * (permM w)ᴴ = Matrix.single (w c) (w d) 1 := by
  rw [permM_conjTranspose, permM_mul_single, single_mul_permM, inv_inv]

theorem permM_mul (w v : Equiv.Perm (Fin n)) : permM w * permM v = permM (w * v) := by
  ext i j
  simp only [Matrix.mul_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single (v j)]
  · have e : (w * v) j = w (v j) := rfl
    by_cases h : i = w (v j)
    · rw [if_pos h, if_pos rfl, if_pos (h.trans e.symm)]; simp
    · rw [if_neg h, zero_mul, if_neg (fun q => h (q.trans e))]
  · intro b _ hb
    rw [if_neg hb]; simp
  · simp

theorem permM_one : permM (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp only [permM, Matrix.of_apply, Matrix.one_apply]
  have e : (1 : Equiv.Perm (Fin n)) j = j := rfl
  by_cases h : i = j
  · rw [if_pos (h.trans e.symm), if_pos h]
  · rw [if_neg (fun q => h (q.trans e)), if_neg h]

theorem Jm_true : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.DS.Jm]

def permU (w : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := permM w
  inv := permM w⁻¹
  val_inv := by rw [permM_mul, mul_inv_cancel, permM_one]
  inv_val := by rw [permM_mul, inv_mul_cancel, permM_one]

theorem permM_unitary (w : Equiv.Perm (Fin n)) : permM w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permM_conjTranspose, permM_mul,
    mul_inv_cancel, permM_one]

def permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.KG (fun _ : Fin n => true) :=
  ⟨⟨permU w, by
      show (permM w)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) * permM w = _
      rw [Jm_true, Matrix.mul_one, permM_conjTranspose, permM_mul, inv_mul_cancel, permM_one]⟩,
    by
      show permM w ∈ ReciprocityTheory.ChartRestriction.DS.Kset (fun _ : Fin n => true)
      refine ⟨permM_unitary w, ?_⟩
      rw [Jm_true, Matrix.mul_one, Matrix.one_mul]⟩

theorem toMK_permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.toMK (permK w) = permM w := rfl

theorem conj_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε Λ)
    (k : ReciprocityTheory.ChartRestriction.DS.S7.KG ε) {c d : Fin n} (h : ε c = ε d) :
    T.op k * T.dτ (Matrix.single c d 1) * star (T.op k) =
      T.dτ (ReciprocityTheory.ChartRestriction.DS.S7.toMK k * Matrix.single c d 1 * star (ReciprocityTheory.ChartRestriction.DS.S7.toMK k)) := by
  have h1 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_hermitian_unit h)
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_skew_hermitian_unit h)
  rw [ReciprocityTheory.ChartRestriction.DS.HW.single_eq_kp c d, map_add (f := _), map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    h1, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul]

theorem unit_translate {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (fun _ : Fin n => true) Λ)
    (w : Equiv.Perm (Fin n)) (c d : Fin n) (v : T.V) :
    T.dτ (Matrix.single (w c) (w d) 1) (T.op (permK w) v) = T.op (permK w) (T.dτ (Matrix.single c d 1) v) := by
  have h := conj_single T (permK w) (c := c) (d := d) rfl
  rw [toMK_permK, Matrix.star_eq_conjTranspose, permM_single] at h
  rw [← h]
  have hu : star (T.op (permK w)) * T.op (permK w) = 1 := Unitary.coe_star_mul_self _
  have e : T.op (permK w) * T.dτ (Matrix.single c d 1) * star (T.op (permK w)) * T.op (permK w) =
      T.op (permK w) * T.dτ (Matrix.single c d 1) := by
    rw [mul_assoc _ (star _), hu, mul_one]
  exact congrArg (fun F : T.V →L[ℂ] T.V => F v) e

theorem extremal_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  intro n κ hκ s hs w
  obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists_of_dom (fun _ : Fin n => true) (fun a => κ a - s) hs
    (fun a b hab _ => sub_le_sub_right (hκ hab.le) s)
  set F := ReciprocityTheory.ChartRestriction.DS.HW.kunits T with hF
  set E := ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift F (fun _ => s) with hE
  have hEval : ∀ x y (f : T.V), E x y f = T.dτ (Matrix.single x y 1) f + (if x = y then ((s : ℝ) : ℂ) else 0) • f := by
    intro x y f
    simp only [hE, hF, ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift, ReciprocityTheory.ChartRestriction.DS.HW.kunits, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, ContinuousLinearMap.coe_coe]
  have hrel : Formalism.REAL.KRel (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kRel (ReciprocityTheory.ChartRestriction.DS.HW.KType.kRel T) (fun _ _ _ => rfl)
  have huni : Formalism.REAL.KUnit (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kUnit (ReciprocityTheory.ChartRestriction.DS.HW.KType.kUnit T) _
  have hhigh : Formalism.REAL.KHighest (fun _ => true) E κ T.w := by
    have h := ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kHighest (t := fun _ => s) (ReciprocityTheory.ChartRestriction.DS.HW.KType.kHighest_w T)
    have e : (fun a => κ a - s) + (fun _ => s) = κ := by
      funext a
      simp
    rwa [e] at h
  have hw0 := ReciprocityTheory.ChartRestriction.DS.HW.KType.w_ne_zero T
  set k := permK w with hk
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, E, T.w, T.op k T.w, fun a b c d => hrel a b c d rfl rfl,
    fun x y => huni x y rfl, hw0, hhigh, ?_, ?_, ?_, ?_⟩
  · intro W hW hu
    have hW' : ∀ a b, (fun _ : Fin n => true) a = (fun _ : Fin n => true) b → ∀ v ∈ W,
        T.dτ (Matrix.single a b 1) v ∈ W := by
      intro a b _ v hv
      have h1 := hW a b v hv
      rw [hEval] at h1
      exact (W.add_mem_iff_left (W.smul_mem _ hv)).1 h1
    rcases ReciprocityTheory.ChartRestriction.DS.HW.KType.dτ_irred T W hW' with h | h
    · rw [h, Submodule.mem_bot] at hu
      exact absurd hu hw0
    · exact h
  · intro h0
    have hu : star (T.op k) * T.op k = 1 := Unitary.coe_star_mul_self _
    have := congrArg (fun G : T.V →L[ℂ] T.V => G T.w) hu
    simp only [ContinuousLinearMap.mul_apply, h0, map_zero] at this
    exact hw0 this.symm
  · intro x
    rw [hEval, unit_translate, T.w_wt x, if_pos rfl, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · intro x y hxy
    have hne : w x ≠ w y := fun e => (ne_of_lt hxy) (w.injective e)
    rw [hEval, unit_translate, T.w_hw x y hxy rfl, if_neg hne]
    simp

end GlobalTheory.CompanionTheory.RealCount.Extremal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompact
section
open Matrix

namespace GlobalTheory.CompanionTheory.OpenCore

theorem exists_open_core {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K S : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hSo : IsOpen (S : Set G)) :
    ∃ K₁ : Subgroup G, K₁ ≤ K ∧ IsOpen (K₁ : Set G) ∧ K₁ ≤ S ∧ K₁.relIndex K ≠ 0 ∧
      ∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((S.subgroupOf K : Subgroup K) : Set K) := hSo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ S.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (S.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (((S.subgroupOf K).normalCore : Subgroup K) : Set K) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((S.subgroupOf K).normalCore_isClosed ((S.subgroupOf K).isClosed_of_isOpen hHo))
  refine ⟨(S.subgroupOf K).normalCore.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ hN
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
  · have e : ((S.subgroupOf K).normalCore.map K.subtype).relIndex K = (S.subgroupOf K).normalCore.index := by
      rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K)]
    rw [e]
    exact (inferInstance : (S.subgroupOf K).normalCore.FiniteIndex).1
  · rintro κ hκ _ ⟨x, hx, rfl⟩
    refine ⟨⟨κ, hκ⟩ * x * (⟨κ, hκ⟩ : K)⁻¹, (Subgroup.normalCore_normal _).conj_mem x hx ⟨κ, hκ⟩, ?_⟩
    simp

theorem exists_open_normal_subgroup_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧
      ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  obtain ⟨S, hSo, hSU⟩ := GlobalTheory.SmGL.ProdIrr.exists_openSubgroup_GL U hU
  obtain ⟨K₁, h1, h2, h3, h4, h5⟩ := exists_open_core (GlobalTheory.SplitWeil.KO k (Fin n)) S
    GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO hSo
  exact ⟨K₁, h1, h2, fun g hg => hSU g (h3 hg), h4, h5⟩

end GlobalTheory.CompanionTheory.OpenCore
end

