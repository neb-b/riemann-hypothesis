module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne
section
noncomputable section

namespace Formalism.L2.Pj

open Matrix IsDedekindDomain

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


variable (V) in
abbrev valI : Valuation F (WithZero (Multiplicative ℤ)) := (IsDiscreteValuationRing.maximalIdeal V).valuation F

theorem exists_of_valI_le_one {x : F} (h : valI (V := V) x ≤ 1) : ∃ a : V, algebraMap V F a = x := by
  have hall : ∀ w : IsDedekindDomain.HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := by
    intro w
    first
    | exact IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    | (ext1; exact IsLocalRing.eq_maximalIdeal w.isMaximal)
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x
    (fun w => by rw [hall w]; exact h)
  exact ⟨a, ha⟩

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun r => valI (V := V) (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI (V := V)).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.permMatrix V
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI (V := V) (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_isLowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U := by
  intro n
  induction n with
  | zero =>
    intro A _
    exact ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) (n := n) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := ih (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem upper_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hinv : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  refine ⟨hinv, fun i => ?_, Matrix.mul_nonsing_inv U hu⟩
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul U hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hinv hlt, zero_mul]
    · rw [hU hgt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem iwasawa' {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (N : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ N.BlockTriangular id ∧
      (∀ i, N i i ≠ 0) ∧ A * N = k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, hA⟩ := iwasawa (V := V) A hA
  obtain ⟨hinv, hdinv, hUU⟩ := upper_inv U hU hd
  refine ⟨k, U⁻¹, hk, hinv, hdinv, ?_⟩
  rw [hA, Matrix.mul_assoc, hUU, Matrix.mul_one]

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

structure IsDer {A : Type*} [CommRing A] (δ : A → A) : Prop where
  add : ∀ x y, δ (x + y) = δ x + δ y
  mul : ∀ x y, δ (x * y) = x * δ y + y * δ x

namespace IsDer

variable {A : Type*} [CommRing A] {δ : A → A}

theorem der_zero (h : IsDer δ) : δ 0 = 0 := by
  have e := h.add 0 0
  rw [add_zero] at e
  linear_combination -e

theorem der_one (h : IsDer δ) : δ 1 = 0 := by
  have e := h.mul 1 1
  simp only [one_mul] at e
  linear_combination -e

theorem der_neg (h : IsDer δ) (x : A) : δ (-x) = -δ x := by
  have e := h.add x (-x)
  rw [add_neg_cancel, h.der_zero] at e
  linear_combination -e

theorem der_sub (h : IsDer δ) (x y : A) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]

theorem der_pow_succ (h : IsDer δ) (x : A) (n : ℕ) : δ (x ^ (n + 1)) = (n + 1 : A) * x ^ n * δ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), h.mul, ih]
    push_cast
    ring

theorem mul_map_pow (h : IsDer δ) (z : A) (r : ℕ) : z * δ (z ^ r) = (r : A) * z ^ r * δ z := by
  cases r with
  | zero => simp [h.der_one]
  | succ n =>
    rw [h.der_pow_succ]
    push_cast
    ring

theorem der_sum (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  exact map_sum (AddMonoidHom.mk' δ h.add) f s

theorem pow_map_mem_of_pow_mul_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    (y : A) : ∀ m r : ℕ, y ^ m * δ y ^ r ∈ I → δ y ^ (r + 2 * m) ∈ I := by
  intro m
  induction m with
  | zero => intro r hr; simpa using hr
  | succ m ih =>
    intro r hr
    have hwJ : δ y * δ (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ (hI _ hr)
    have e := h.mul_map_pow (δ y) r
    have key : δ y * δ (y ^ (m + 1) * δ y ^ r) =
        (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) + ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) := by
      rw [h.mul, h.der_pow_succ]
      linear_combination y ^ (m + 1) * e
    have h2 : ((m : A) + 1) * (y ^ m * δ y ^ (r + 2)) ∈ I := by
      have h3 : (r : A) * δ (δ y) * (y ^ (m + 1) * δ y ^ r) ∈ I := I.mul_mem_left _ hr
      have h5 := I.sub_mem hwJ h3
      rwa [key, add_sub_cancel_left] at h5
    have hu1 := hu (m + 1) (Nat.succ_pos m)
    push_cast at hu1
    have h4 : y ^ m * δ y ^ (r + 2) ∈ I := (Ideal.unit_mul_mem_iff_mem I hu1).mp h2
    have h6 := ih (r + 2) h4
    rwa [show r + 2 + 2 * m = r + 2 * (m + 1) by ring] at h6

theorem pow_mem (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A))
    {y : A} {n : ℕ} (hy : y ^ n ∈ I) : δ y ^ (2 * n) ∈ I := by
  have e := h.pow_map_mem_of_pow_mul_mem I hI hu y n 0 (by simpa using hy)
  simpa using e

theorem mem_max [IsArtinianRing A] (h : IsDer δ) (hu : ∀ n : ℕ, 0 < n → IsUnit (n : A)) (m : Ideal A)
    [hm : m.IsMaximal] {x : A} (hx : x ∈ m) : δ x ∈ m := by

  have hx' : algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m x).mpr hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime m) x) := by
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Localization.AtPrime m)
    refine ⟨k, ?_⟩
    have hj : algebraMap A (Localization.AtPrime m) x ∈ Ideal.jacobson (⊥ : Ideal (Localization.AtPrime m)) := by
      rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    have := Ideal.pow_mem_pow hj k
    rwa [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨n, hn⟩ := hnil
  rw [← map_pow] at hn
  obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) _).mp hn
  have hs' : s ∉ m := hs

  have hsx0 : (s * x) ^ (n + 1) ∈ (⊥ : Ideal A) := by
    rw [Ideal.mem_bot]
    calc (s * x) ^ (n + 1) = s ^ n * x * (s * x ^ n) := by ring
      _ = 0 := by simp only at hsx; rw [hsx, mul_zero]
  have hb : ∀ z ∈ (⊥ : Ideal A), δ z ∈ (⊥ : Ideal A) := by
    intro z hz
    rw [Ideal.mem_bot] at hz ⊢
    rw [hz, h.der_zero]
  have hd := h.pow_mem ⊥ hb hu hsx0
  rw [Ideal.mem_bot] at hd
  have hdm : δ (s * x) ∈ m := hm.isPrime.mem_of_pow_mem _ (by rw [hd]; exact m.zero_mem)
  rw [h.mul] at hdm
  have hxs : x * δ s ∈ m := m.mul_mem_right _ hx
  have hsd : s * δ x ∈ m := by
    have := m.sub_mem hdm hxs
    rwa [add_sub_cancel_right] at this
  exact (hm.isPrime.mem_or_mem hsd).resolve_left hs'

theorem quot (h : IsDer δ) (I : Ideal A) (hI : ∀ x ∈ I, δ x ∈ I) :
    ∃ δ' : A ⧸ I → A ⧸ I, IsDer δ' ∧ ∀ x, δ' (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (δ x) := by
  classical
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := Function.surjInv_eq _
  have key : ∀ x, Ideal.Quotient.mk I (δ (s (Ideal.Quotient.mk I x))) = Ideal.Quotient.mk I (δ x) := by
    intro x
    rw [Ideal.Quotient.eq, ← h.der_sub]
    exact hI _ (Ideal.Quotient.eq.mp (hs _))
  refine ⟨fun q => Ideal.Quotient.mk I (δ (s q)), ⟨fun a b => ?_, fun a b => ?_⟩, key⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add (f := _), key, key, key, h.add, map_add (f := _)]
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, key, key, h.mul, map_add (f := _), map_mul, map_mul]

theorem ofLoc {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by
  have d1 : d 1 = 0 := by
    have e := hmul 1 1
    simp only [mul_one, map_one, one_mul] at e
    linear_combination -e
  have d0 : d 0 = 0 := by
    have e := hadd 0 0
    simp only [add_zero] at e
    linear_combination -e

  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A B a) + TrivSqZeroExt.inr (d a)
      map_one' := by ext <;> simp [d1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul, TrivSqZeroExt.snd_mul]; ring
      map_zero' := by ext <;> simp [d0]
      map_add' := fun x y => by
        ext
        · simp
        · simp [hadd] }
  have hψ : ∀ s : S, IsUnit (ψ s) := by
    intro s
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa [ψ] using IsLocalization.map_units B s
  let φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hψ
  have hφ : ∀ a, φ (algebraMap A B a) = ψ a := IsLocalization.lift_eq hψ
  let fst : TrivSqZeroExt B B →+* B :=
    { toFun := TrivSqZeroExt.fst
      map_one' := rfl
      map_mul' := fun x y => TrivSqZeroExt.fst_mul x y
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hfst : ∀ x, (φ x).fst = x := by
    have e : fst.comp φ = RingHom.id B := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp only [RingHom.comp_apply, RingHom.id_apply, hφ]
      show TrivSqZeroExt.fst (ψ a) = _
      simp [ψ]
    intro x
    exact congrArg (fun f : B →+* B => f x) e
  refine ⟨fun x => (φ x).snd, ⟨fun x y => by simp, fun x y => ?_⟩, fun a => by simp [hφ, ψ]⟩
  simp only [map_mul, TrivSqZeroExt.snd_mul, hfst, smul_eq_mul, op_smul_eq_mul]
  ring

end IsDer

end Formalism.L2.Pj.GenericSectionMinimum
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n

variable {T : Type} (r : T → ℕ) (n : ℕ)

variable (k : Type) [Field k]

def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)

def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')

def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ

def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P

def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i

def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}

def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.SumEmbeddingsEq
section
noncomputable section

namespace Formalism.L2.Pj.DatLin

open NumberField ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_eq (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by
  rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

theorem trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, sum_embeddings_eq, ← Finset.sum_add_sum_compl Ψ]

  have hc : ∑ σ ∈ Ψᶜ, σ z = ∑ τ ∈ Ψ, conj (τ z) := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe, Finset.mem_compl] at hσ ⊢
      rw [hΨ, show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
      exact hσ
    · intro τ hτ
      simp only [Finset.mem_coe, Finset.mem_compl]
      exact (hΨ τ).mp hτ
    · intro σ _; exact star_star σ
    · intro τ _; exact star_star τ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hc, ← Finset.sum_add_distrib, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Complex.add_conj]

theorem sesq_repr [StarRing E] {V : Type} [AddCommGroup V] [Module E V] {ι : Type} [Fintype ι]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis ι E V) (x y : V) :
    h x y = ∑ i, ∑ j, star (b.repr x i) * h (b i) (b j) * b.repr y j := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Formalism.L2.Pj.DatLin
end
end

