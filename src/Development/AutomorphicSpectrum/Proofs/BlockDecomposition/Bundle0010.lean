module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueCompEq
section
namespace GlobalTheory.CompanionTheory.PfCompl

open Ideal

variable {B T T₁ : Type*} [CommRing B] [CommRing T] [CommRing T₁]

theorem exists_level_hom (π : B) (g : B →+* T) (x : B →+* T₁) (M : ℕ)
    (hsurj : ∀ y : T, ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ b, g b ∈ span {g π ^ M} → b ∈ span {π ^ M}) :
    ∃ f : T →+* T₁ ⧸ (span {x π}) ^ M,
      ∀ y b, y - g b ∈ span {g π ^ M} → f y = Ideal.Quotient.mk _ (x b) := by
  have hIJ : span {π ^ M} ≤ (span {g π ^ M}).comap g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hxK : span {π ^ M} ≤ ((span {x π}) ^ M).comap x := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M
  have hinj' : Function.Injective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    refine Ideal.quotientMap_injective' ?_
    intro b hb
    exact hinj b (Ideal.mem_comap.1 hb)
  have hsurj' : Function.Surjective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hb).symm⟩
  let e := RingEquiv.ofBijective _ ⟨hinj', hsurj'⟩
  refine ⟨(Ideal.quotientMap _ x hxK).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk _)), ?_⟩
  intro y b hy
  have h1 : e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (span {g π ^ M}) y := by
    show Ideal.quotientMap _ g hIJ (Ideal.Quotient.mk _ b) = _
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 hy).symm
  have h2 : e.symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (span {π ^ M}) b := by
    rw [← h1, RingEquiv.symm_apply_apply]
  show Ideal.quotientMap _ x hxK (e.symm (Ideal.Quotient.mk _ y)) = _
  rw [h2, Ideal.quotientMap_mk]

theorem mk_eq_of_comp_eq (π : B) (g : B →+* T) (x : B →+* T₁) (ψ : T →+* T₁)
    (hψ : ψ.comp g = x) (M : ℕ) (y : T) (b : B) (hy : y - g b ∈ span {g π ^ M}) :
    Ideal.Quotient.mk ((span {x π}) ^ M) (ψ y) = Ideal.Quotient.mk _ (x b) := by
  have hb : x b = ψ (g b) := (DFunLike.congr_fun hψ b).symm
  have hπ : ψ (g π) = x π := DFunLike.congr_fun hψ π
  rw [Ideal.Quotient.eq, hb, ← map_sub]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy
  rw [← ht, map_mul, map_pow, hπ]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M)

theorem existsUnique_comp_eq (π : B) (g : B →+* T)
    (hsurj : ∀ (M : ℕ) (y : T), ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ (M : ℕ) (b : B), g b ∈ span {g π ^ M} → b ∈ span {π ^ M})
    (x : B →+* T₁) (hc : IsAdicComplete (span {x π}) T₁) :
    ∃! ψ : T →+* T₁, ψ.comp g = x := by
  have key : ∀ a c : T₁,
      (∀ n : ℕ, Ideal.Quotient.mk (span {x π} ^ n) a = Ideal.Quotient.mk _ c) → a = c := by
    intro a c h
    have h0 := IsHausdorff.haus' (I := span {x π}) (a - c) fun n => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (h n)
    exact sub_eq_zero.1 h0
  choose f hf using fun n => exists_level_hom π g x n (hsurj n) (hinj n)
  have hle : ∀ {m n : ℕ}, m ≤ n → ∀ z : T, z ∈ span {g π ^ n} → z ∈ span {g π ^ m} := by
    intro m n h z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Ideal.mem_span_singleton'.2 ⟨t * g π ^ (n - m), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow (span {x π}) h).comp (f n) = f m := by
    intro m n h
    ext y
    obtain ⟨b, hb⟩ := hsurj n y
    rw [RingHom.comp_apply, hf n y b hb, hf m y b (hle h _ hb)]
    first
      | rfl
      | exact Ideal.Quotient.factor_mk _ _
      | simp [Ideal.Quotient.factorPow]
  refine ⟨IsAdicComplete.liftRingHom _ f hcompat, ?_, ?_⟩
  · ext b
    apply key
    intro n
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom, hf n (g b) b (by simp)]
  · intro ψ hψ
    ext y
    apply key
    intro n
    rw [IsAdicComplete.mk_liftRingHom]
    obtain ⟨b, hb⟩ := hsurj n y
    rw [hf n y b hb]
    exact mk_eq_of_comp_eq π g x ψ hψ n y b hb

end GlobalTheory.CompanionTheory.PfCompl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUpperLower
section
open Matrix

namespace GlobalTheory.CompanionTheory.HeckeMult

variable {R : Type} [CommRing R]

def CongOne {n : ℕ} (I : Ideal R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I

def bordered {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
  Fin.lastCases (motive := fun _ => R)
    (Fin.lastCases (motive := fun _ => R) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => R) (c i') (M i') j) i

section bordered
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)

@[simp] theorem bordered_cc (i j : Fin n) :
    bordered M c r d i.castSucc j.castSucc = M i j := by simp [bordered]
@[simp] theorem bordered_cl (i : Fin n) :
    bordered M c r d i.castSucc (Fin.last n) = c i := by simp [bordered]
@[simp] theorem bordered_lc (j : Fin n) :
    bordered M c r d (Fin.last n) j.castSucc = r j := by simp [bordered]
@[simp] theorem bordered_ll :
    bordered M c r d (Fin.last n) (Fin.last n) = d := by simp [bordered]
end bordered

theorem one_cc {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc j.castSucc
      = (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [Matrix.one_apply]

theorem one_cl {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc (Fin.last n) = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne

theorem one_lc {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) i.castSucc = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne'

theorem CongOne.bordered {n : ℕ} {I : Ideal R} {M : Matrix (Fin n) (Fin n) R}
    {c r : Fin n → R} {d : R} (hM : CongOne I M) (hc : ∀ i, c i ∈ I) (hr : ∀ i, r i ∈ I)
    (hd : d - 1 ∈ I) : CongOne I (bordered M c r d) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using hd
    | cast j => simpa [one_lc] using hr j
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [one_cl] using hc i
    | cast j => simpa [one_cc] using hM i j

theorem exists_upper_lower (I : Ideal R) (hI : ∀ s : R, s - 1 ∈ I → IsUnit s) (n : ℕ) :
    ∀ A : Matrix (Fin n) (Fin n) R, CongOne I A →
      ∃ U L : Matrix (Fin n) (Fin n) R, CongOne I U ∧ CongOne I L ∧
        (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → L i j = 0) ∧ A = U * L := by
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    have hs1 : A (Fin.last n) (Fin.last n) - 1 ∈ I := by
      simpa using hA (Fin.last n) (Fin.last n)
    obtain ⟨t, hst⟩ := (hI _ hs1).exists_right_inv
    have hq : ∀ i : Fin n, A i.castSucc (Fin.last n) ∈ I := fun i => by
      simpa [one_cl] using hA i.castSucc (Fin.last n)
    have hr : ∀ j : Fin n, A (Fin.last n) j.castSucc ∈ I := fun j => by
      simpa [one_lc] using hA (Fin.last n) j.castSucc
    let P : Matrix (Fin n) (Fin n) R := fun i j =>
      A i.castSucc j.castSucc - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc
    have hP : CongOne I P := by
      intro i j
      have h1 := hA i.castSucc j.castSucc
      rw [one_cc] at h1
      have h2 : A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc ∈ I :=
        I.mul_mem_left _ (hr j)
      have : P i j - (1 : Matrix (Fin n) (Fin n) R) i j
          = (A i.castSucc j.castSucc - (1 : Matrix (Fin n) (Fin n) R) i j)
            - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc := by
        simp only [P]; ring
      rw [this]
      exact I.sub_mem h1 h2
    obtain ⟨U', L', hU', hL', hUt, hLt, hUL⟩ := ih P hP
    refine ⟨bordered U' (fun i => A i.castSucc (Fin.last n) * t) 0 1,
      bordered L' 0 (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)),
      hU'.bordered (fun i => I.mul_mem_right _ (hq i)) (fun _ => I.zero_mem) (by simp),
      hL'.bordered (fun _ => I.zero_mem) hr hs1, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hUt i j (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hLt i j (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [bordered_cc, bordered_cl, bordered_ll, Pi.zero_apply, mul_zero,
            Finset.sum_const_zero, zero_add]
          rw [mul_assoc, mul_comm t, hst, mul_one]
        | cast j =>
          simp only [bordered_cc, bordered_cl, bordered_lc]
          have h := congrFun (congrFun hUL i) j
          rw [Matrix.mul_apply] at h
          rw [← h]
          simp only [P]; ring

section conj
variable {K : Type} [Field K] [Algebra R K]

theorem conj_upper {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (a : Fin n → ℤ)
    (ha : Antitone a) (U : Matrix (Fin n) (Fin n) R) (hU : CongOne I U)
    (hUt : ∀ i j, j < i → U i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) * U.map (algebraMap R K)
        = V.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) := by
  refine ⟨Matrix.of fun i j => U i j * ϖ ^ (a i - a j).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero]
      have := hU i j
      rw [Matrix.one_apply_ne h.ne, sub_zero] at this
      exact I.mul_mem_right _ this
    · subst h
      simpa using hU i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero, hUt i j h, zero_mul]
      exact I.zero_mem
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge j i with h | h
    · simp [hUt i j h]
    · have hnn : 0 ≤ a i - a j := sub_nonneg.mpr (ha h)
      have : (algebraMap R K ϖ) ^ (a i) = (algebraMap R K ϖ) ^ (a i - a j).toNat * (algebraMap R K ϖ) ^ (a j) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

theorem conj_lower {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (b : Fin n → ℤ)
    (hb : Antitone b) (L : Matrix (Fin n) (Fin n) R) (hL : CongOne I L)
    (hLt : ∀ i j, i < j → L i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      L.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i))
        = Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i)) * V.map (algebraMap R K) := by
  refine ⟨Matrix.of fun i j => L i j * ϖ ^ (b j - b i).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero, hLt i j h, zero_mul]
      exact I.zero_mem
    · subst h
      simpa using hL i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      have := hL i j
      rw [Matrix.one_apply_ne h.ne', sub_zero] at this
      exact I.mul_mem_right _ this
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge i j with h | h
    · simp [hLt i j h]
    · have hnn : 0 ≤ b j - b i := sub_nonneg.mpr (hb h)
      have : (algebraMap R K ϖ) ^ (b j) = (algebraMap R K ϖ) ^ (b j - b i).toNat * (algebraMap R K ϖ) ^ (b i) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

end conj

end GlobalTheory.CompanionTheory.HeckeMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpBlockTriangular
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper


open scoped Matrix.Norms.L2Operator in
theorem blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)

theorem blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)

end GlobalTheory.CompanionTheory.Unitary.ExpUpper
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialPolynomialSolutionSpace
section
open Polynomial

namespace GlobalTheory.CompanionTheory.ConstCoeffODE

noncomputable def op (c : ℂ) (y : ℝ → ℂ) : ℝ → ℂ := deriv y - c • y

theorem op_add (c : ℂ) {a b : ℝ → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    op c (a + b) = op c a + op c b := by
  funext t
  have h : deriv (a + b) t = deriv a t + deriv b t :=
    ((ha t).hasDerivAt.add (hb t).hasDerivAt).deriv
  simp only [op, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

theorem op_smul (c k : ℂ) {a : ℝ → ℂ} (ha : Differentiable ℝ a) :
    op c (k • a) = k • op c a := by
  funext t
  have h : deriv (k • a) t = k • deriv a t :=
    ((ha t).hasDerivAt.const_smul k).deriv
  simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h]
  ring

noncomputable def step (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : Submodule ℂ (ℝ → ℂ) where
  carrier := {y | Differentiable ℝ y ∧ op c y ∈ S}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, by rw [op_add c ha hb]; exact S.add_mem ha' hb'⟩
  zero_mem' := by
    refine ⟨differentiable_const (0 : ℂ), ?_⟩
    have : op c (0 : ℝ → ℂ) = 0 := by
      funext t
      simp [op]
    rw [this]
    exact S.zero_mem
  smul_mem' := by
    rintro k a ⟨ha, ha'⟩
    exact ⟨ha.const_smul k, by rw [op_smul c k ha]; exact S.smul_mem k ha'⟩

noncomputable def stepMap (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) : step c S →ₗ[ℂ] S × ℂ where
  toFun y := (⟨op c y.1, y.2.2⟩, y.1 0)
  map_add' a b := by
    ext1
    · exact Subtype.ext (op_add c a.2.1 b.2.1)
    · rfl
  map_smul' k a := by
    ext1
    · exact Subtype.ext (op_smul c k a.2.1)
    · rfl

theorem eq_zero_of_op_eq_zero (c : ℂ) {y : ℝ → ℂ} (hy : Differentiable ℝ y)
    (h : op c y = 0) (h0 : y 0 = 0) : y = 0 := by
  have hd : ∀ t, deriv y t = c * y t := by
    intro t
    have := congrFun h t
    simp only [op, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  have he : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-c * (s : ℂ)))
      (Complex.exp (-c * (t : ℂ)) * (-c)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -c * (s : ℂ)) (-c) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)
    exact h1.cexp
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => y s * Complex.exp (-c * (s : ℂ))) 0 t := by
    intro t
    have h2 := (hy t).hasDerivAt.mul (he t)
    have h3 : deriv y t * Complex.exp (-c * (t : ℂ)) + y t * (Complex.exp (-c * (t : ℂ)) * (-c)) = 0 := by
      rw [hd]; ring
    rw [h3] at h2
    exact h2
  have hc := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv)
  funext t
  have := hc t 0
  simp only [h0, zero_mul] at this
  simpa [Complex.exp_ne_zero] using this

theorem stepMap_injective (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) :
    Function.Injective (stepMap c S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have h1 : op c y.1 = 0 := congrArg (fun p : S × ℂ => (p.1 : ℝ → ℂ)) hy
  have h2 : y.1 0 = 0 := congrArg Prod.snd hy
  exact Subtype.ext (eq_zero_of_op_eq_zero c y.2.1 h1 h2)

theorem step_finite (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (step c S) :=
  FiniteDimensional.of_injective (stepMap c S) (stepMap_injective c S)

theorem step_finrank_le (c : ℂ) (S : Submodule ℂ (ℝ → ℂ)) [FiniteDimensional ℂ S] :
    Module.finrank ℂ (step c S) ≤ Module.finrank ℂ S + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (stepMap_injective c S)
  rw [Module.finrank_prod, Module.finrank_self] at h
  exact h

theorem solutions_mem_finite :
    ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
        (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) →
          ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by
  intro l
  induction l with
  | nil =>
    refine ⟨⊥, inferInstance, by simp, ?_⟩
    intro X _ _ D ev _ x hx
    simpa using hx
  | cons c l ih =>
    obtain ⟨S, hfin, hrank, hS⟩ := ih
    refine ⟨step c S, step_finite c S, ?_, ?_⟩
    · have := step_finrank_le c S
      simp only [List.length_cons]
      omega
    · intro X _ _ D ev hD x hx
      set Q : Module.End ℂ X := D - c • (1 : Module.End ℂ X) with hQ
      set P : Module.End ℂ X := (l.map fun c => D - c • (1 : Module.End ℂ X)).prod with hP
      have hcomm : Commute Q P := by
        refine Commute.list_prod_right _ _ ?_
        intro z hz
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hz
        have hD1 : Commute D (1 : Module.End ℂ X) := Commute.one_right D
        exact ((Commute.refl D).sub_right (hD1.smul_right b)).sub_left
          ((hD1.symm.sub_right ((Commute.one_left _).smul_right b)).smul_left c)
      have h1 : ev (P (Q x)) = 0 := by
        have h2 : (Q * P) x = (P * Q) x := by rw [hcomm.eq]
        have h3 : ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod) = P := rfl
        simp only [List.map_cons, List.prod_cons] at hx
        rw [h3] at hx
        have h4 : (P * Q) x = P (Q x) := rfl
        rw [← h4, ← h2]
        exact hx
      have h5 : ev (Q x) ∈ S := hS X D ev hD (Q x) h1
      have hdiff : Differentiable ℝ (ev x) := fun t => (hD x t).differentiableAt
      refine ⟨hdiff, ?_⟩
      have h6 : op c (ev x) = ev (Q x) := by
        funext t
        simp [op, hQ, (hD x t).deriv]
      rw [h6]
      exact h5

end GlobalTheory.CompanionTheory.ConstCoeffODE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBound
section
namespace GlobalTheory.CompanionTheory.Casselman

theorem lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith

end GlobalTheory.CompanionTheory.Casselman
end

