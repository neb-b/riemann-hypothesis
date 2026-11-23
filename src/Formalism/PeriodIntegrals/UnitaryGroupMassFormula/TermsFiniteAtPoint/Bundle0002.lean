module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBase
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E]

def Intg {m n : Type*} (d : 𝓞 E) (M : Matrix m n E) : Prop :=
  ∃ M' : Matrix m n (𝓞 E), M'.map (algebraMap (𝓞 E) E) = (algebraMap (𝓞 E) E d) • M

theorem intg_mul {l m n : Type*} [Fintype m] {d d' : 𝓞 E} {M : Matrix l m E} {N : Matrix m n E}
    (hM : Intg d M) (hN : Intg d' N) : Intg (d * d') (M * N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' * N', ?_⟩
  rw [Matrix.map_mul, hM', hN', Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul, mul_comm]

theorem intg_sub {m n : Type*} {d : 𝓞 E} {M N : Matrix m n E} (hM : Intg d M) (hN : Intg d N) :
    Intg d (M - N) := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨N', hN'⟩ := hN
  refine ⟨M' - N', ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' i) j
  have h2 := congrFun (congrFun hN' i) j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub] at h1 h2 ⊢
  rw [h1, h2]; ring

theorem intg_dvd {m n : Type*} {a D : 𝓞 E} {M : Matrix m n E} (hM : Intg a M) (h : a ∣ D) : Intg D M := by
  obtain ⟨M', hM'⟩ := hM
  obtain ⟨k, rfl⟩ := h
  refine ⟨k • M', ?_⟩
  ext i j
  have := congrFun (congrFun hM' i) j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at this ⊢
  rw [this]; ring

theorem intg_one {n : Type*} [DecidableEq n] (d : 𝓞 E) : Intg d (1 : Matrix n n E) := by
  refine ⟨d • (1 : Matrix n n (𝓞 E)), ?_⟩
  ext i j
  by_cases h : i = j <;> simp [h]

theorem intg_zero {m n : Type*} (d : 𝓞 E) : Intg d (0 : Matrix m n E) :=
  ⟨0, by ext i j; simp⟩

theorem intg_submatrix {m n m' n' : Type*} {d : 𝓞 E} {M : Matrix m n E} (hM : Intg d M) (f : m' → m)
    (g : n' → n) : Intg d (M.submatrix f g) := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.submatrix f g, ?_⟩
  ext i j
  have h1 := congrFun (congrFun hM' (f i)) (g j)
  simpa using h1

theorem intg_fromBlocks {l m n o : Type*} {d : 𝓞 E} {A : Matrix l n E} {B : Matrix l o E}
    {C : Matrix m n E} {D : Matrix m o E} (hA : Intg d A) (hB : Intg d B) (hC : Intg d C) (hD : Intg d D) :
    Intg d (Matrix.fromBlocks A B C D) := by
  obtain ⟨A', hA'⟩ := hA
  obtain ⟨B', hB'⟩ := hB
  obtain ⟨C', hC'⟩ := hC
  obtain ⟨D', hD'⟩ := hD
  refine ⟨Matrix.fromBlocks A' B' C' D', ?_⟩
  rw [Matrix.fromBlocks_map, hA', hB', hC', hD', Matrix.fromBlocks_smul]

theorem intg_adj {k : ℕ} {d : 𝓞 E} {M : Matrix (Fin k) (Fin k) E} (hM : Intg d M) :
    Intg (d ^ (k - 1)) M.adjugate := by
  obtain ⟨M', hM'⟩ := hM
  refine ⟨M'.adjugate, ?_⟩
  have h1 := RingHom.map_adjugate (algebraMap (𝓞 E) E) M'
  simp only [RingHom.mapMatrix_apply] at h1
  rw [h1, hM', Matrix.adjugate_smul, Fintype.card_fin, map_pow]

theorem intg_of_entries {m n : Type*} {Z : Matrix m n E} (h : ∀ i j, ∃ o : 𝓞 E, (o : E) = Z i j) :
    Intg 1 Z := by
  refine ⟨fun i j => Classical.choose (h i j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, map_one, one_smul]
  exact Classical.choose_spec (h i j)

theorem exists_den (x : E) :
    ∃ m : 𝓞 E, m ≠ 0 ∧ ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = algebraMap (𝓞 E) E m * x := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  refine ⟨s, nonZeroDivisors.ne_zero s.2, a, ?_⟩
  simp only at h
  rw [← h, mul_comm]

theorem alg_ne_zero {d : 𝓞 E} (hd : d ≠ 0) : algebraMap (𝓞 E) E d ≠ 0 := by
  intro h
  exact hd ((injective_iff_map_eq_zero (algebraMap (𝓞 E) E)).mp (IsFractionRing.injective (𝓞 E) E) d h)

section Uni

variable {K : Type*} [Field K] {k : ℕ}

theorem lo_bt {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.BlockTriangular OrderDual.toDual :=
  fun i j h => (hA i j).1 (by simpa using h)

theorem lo_diag_mul {A B : Matrix (Fin k) (Fin k) K} (hA : A.BlockTriangular OrderDual.toDual)
    (hB : B.BlockTriangular OrderDual.toDual) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hB (by simpa using h), mul_zero]
    · rw [hA (by simpa using h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem lo_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) (hB : IsLoUni B) : IsLoUni (A * B) := by
  have ht := (lo_bt hA).mul (lo_bt hB)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  rw [lo_diag_mul (lo_bt hA) (lo_bt hB), (hA i i).2 rfl, (hB i i).2 rfl, one_mul]

theorem lo_det {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A (lo_bt hA)]
  exact Finset.prod_eq_one fun i _ => (hA i i).2 rfl

theorem lo_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, lo_det hA, one_smul]

theorem lo_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, lo_det hA, one_smul]

theorem lo_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsLoUni A) : IsLoUni A.adjugate := by
  letI : Invertible A.det := invertibleOfNonzero (by rw [lo_det hA]; exact one_ne_zero)
  letI : Invertible A := Matrix.invertibleOfDetInvertible A
  have hinv : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, lo_det hA, Ring.inverse_one, one_smul]
  have ht : A.adjugate.BlockTriangular OrderDual.toDual := by
    rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular (lo_bt hA)
  intro i j
  refine ⟨fun h => ht (by simpa using h), fun h => ?_⟩
  subst h
  have h1 := congrFun (congrFun (lo_mul_adj hA) i) i
  rw [lo_diag_mul (lo_bt hA) ht, (hA i i).2 rfl, one_mul, Matrix.one_apply_eq] at h1
  exact h1

theorem up_iff_lo_transpose {U : Matrix (Fin k) (Fin k) K} : IsUpUni U ↔ IsLoUni U.transpose := by
  constructor
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩
  · intro h i j
    exact ⟨fun hij => (h j i).1 hij, fun hij => (h j i).2 hij.symm⟩

theorem up_mul {A B : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.transpose_mul]; exact lo_mul hB hA

theorem up_det {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.det = 1 := by
  rw [← Matrix.det_transpose]; exact lo_det (up_iff_lo_transpose.mp hA)

theorem up_mul_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A * A.adjugate = 1 := by
  rw [Matrix.mul_adjugate, up_det hA, one_smul]

theorem up_adj_mul {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : A.adjugate * A = 1 := by
  rw [Matrix.adjugate_mul, up_det hA, one_smul]

theorem up_adj {A : Matrix (Fin k) (Fin k) K} (hA : IsUpUni A) : IsUpUni A.adjugate := by
  rw [up_iff_lo_transpose] at *
  rw [Matrix.adjugate_transpose]; exact lo_adj hA

end Uni

theorem quotFinite (c : 𝓞 E) (hc : c ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {c}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hc)

theorem fin_of_cong {α ι : Type*} [Finite ι] (X : Set α) (f : α → ι → E)
    (hf : ∀ x ∈ X, ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i) (c : 𝓞 E) (hc : c ≠ 0)
    (R : α → α → Prop)
    (hR : ∀ x ∈ X, ∀ y ∈ X,
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E o = f y i - f x i) → R x y) :
    ∃ Zs : Set α, Zs.Finite ∧ ∀ x ∈ X, ∃ y ∈ Zs, R x y := by
  have := quotFinite c hc
  let g : α → ι → (𝓞 E ⧸ Ideal.span {c}) := fun x i =>
    if h : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = f x i then Ideal.Quotient.mk _ (Classical.choose h) else 0
  haveI : Finite {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} := Subtype.finite
  refine ⟨Set.range (fun ρ : {ρ : ι → (𝓞 E ⧸ Ideal.span {c}) // ∃ x ∈ X, g x = ρ} => Classical.choose ρ.2),
    Set.finite_range _, ?_⟩
  intro x hx
  have hex : ∃ x' ∈ X, g x' = g x := ⟨x, hx, rfl⟩
  refine ⟨Classical.choose hex, ⟨⟨g x, hex⟩, rfl⟩, ?_⟩
  obtain ⟨hy, hgy⟩ := Classical.choose_spec hex
  apply hR x hx _ hy
  intro i
  have h1 := hf x hx i
  have h2 := hf _ hy i
  have hg := congrFun hgy i
  simp only [g, dif_pos h1, dif_pos h2] at hg
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hg
  obtain ⟨o, ho⟩ := hg
  refine ⟨o, ?_⟩
  rw [← map_mul, ← ho, map_sub, Classical.choose_spec h1, Classical.choose_spec h2]

end PI.TermsAtPtFiniteW.CellW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.HeisOpHolds
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.HeisW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hsym (x y : S.V) : star (S.hT x y) = S.hT y x := by
  simpa [starRingEnd_apply] using S.herm.eq x y

def kap (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) (c : Fin r) : E :=
  -S.hT (a c) v + ∑ d, s c d * S.hT (e d) v

def nilF (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) : S.V →ₗ[E] S.V :=
  ∑ c, ((S.hT (e c)).smulRight (a c) + (-(S.hT (a c)) + ∑ d, s c d • S.hT (e d)).smulRight (e c))

theorem nilF_apply (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) :
    nilF e a s v = ∑ c, (S.hT (e c) v • a c + kap e a s v c • e c) := by
  simp [nilF, kap, LinearMap.sum_apply]

theorem heis_eq (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) :
    PI.TermsAtPtFiniteW.heisFun e a s v = v + nilF e a s v := by
  rw [nilF_apply, PI.TermsAtPtFiniteW.heisFun]
  simp only [kap, add_smul, neg_smul, Finset.sum_smul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

section Nil

variable (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
  (hiso : ∀ c d, S.hT (e c) (e d) = 0) (hea : ∀ c d, S.hT (e c) (a d) = 0)
include hiso hea

omit hiso in
theorem hae (c d : Fin r) : S.hT (a c) (e d) = 0 := by
  rw [← hsym, hea, star_zero]

theorem nil_e (c : Fin r) : nilF e a s (e c) = 0 := by
  rw [nilF_apply]
  simp [kap, hiso, hae e a hea]

theorem nil_a (c : Fin r) : nilF e a s (a c) = ∑ d, kap e a s (a c) d • e d := by
  rw [nilF_apply]
  simp [hea]

theorem nil_nil (v : S.V) :
    nilF e a s (nilF e a s v) = ∑ c, S.hT (e c) v • ∑ d, kap e a s (a c) d • e d := by
  rw [nilF_apply e a s v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_smul, nil_e e a s hiso hea, nil_a e a s hiso hea, smul_zero, add_zero]

theorem nil3 (v : S.V) : nilF e a s (nilF e a s (nilF e a s v)) = 0 := by
  rw [nil_nil e a s hiso hea v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, nil_e e a s hiso hea]

end Nil

theorem alg (p q P Q : Fin r → E) (s G : Matrix (Fin r) (Fin r) E)
    (h : ∀ c d, s c d + star (s d c) = -G c d) :
    (∑ c, (p c * Q c + (-P c + ∑ d, star (s c d) * p d) * q c)) +
      (∑ c, (q c * P c + (-Q c + ∑ d, s c d * q d) * p c)) + ∑ c, ∑ d, p c * q d * G c d = 0 := by
  have e1 : ∑ c, (∑ d, star (s c d) * p d) * q c = ∑ c, ∑ d, p c * q d * star (s d c) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∑ c, (∑ d, s c d * q d) * p c = ∑ c, ∑ d, p c * q d * s c d := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have e3 : ∑ c, ∑ d, p c * q d * star (s d c) + ∑ c, ∑ d, p c * q d * s c d +
      ∑ c, ∑ d, p c * q d * G c d = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun d _ => ?_
    have := h c d
    linear_combination (p c * q d) * this
  have e4 : ∑ c, (p c * Q c + -P c * q c) + ∑ c, (q c * P c + -Q c * p c) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun c _ => by ring
  simp only [add_mul, Finset.sum_add_distrib] at e4 ⊢
  rw [e1, e2]
  linear_combination e3 + e4

section Form

variable (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
  (hiso : ∀ c d, S.hT (e c) (e d) = 0) (hea : ∀ c d, S.hT (e c) (a d) = 0)
  (hs : ∀ c d, s c d + star (s d c) = -S.hT (a c) (a d))
include hiso hea hs

theorem form_nil (x y : S.V) :
    S.hT (nilF e a s x) y + S.hT x (nilF e a s y) + S.hT (nilF e a s x) (nilF e a s y) = 0 := by
  have E1 : S.hT (nilF e a s x) y = ∑ c, (star (S.hT (e c) x) * S.hT (a c) y +
      (-star (S.hT (a c) x) + ∑ d, star (s c d) * star (S.hT (e d) x)) * S.hT (e c) y) := by
    rw [nilF_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smulₛₗ, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [kap, star_add, star_neg, star_sum, star_mul']
    all_goals ring
  have E2 : S.hT x (nilF e a s y) = ∑ c, (S.hT (e c) y * star (S.hT (a c) x) +
      (-S.hT (a c) y + ∑ d, s c d * S.hT (e d) y) * star (S.hT (e c) x)) := by
    rw [nilF_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hsym, hsym]
    simp only [kap]
    all_goals ring
  have E3 : S.hT (nilF e a s x) (nilF e a s y) =
      ∑ c, ∑ d, star (S.hT (e c) x) * S.hT (e d) y * S.hT (a c) (a d) := by
    rw [nilF_apply e a s x, nilF_apply e a s y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hiso, hea, hae e a hea, mul_zero, add_zero,
      zero_add, Finset.sum_const_zero, Finset.mul_sum, RingHom.id_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [E1, E2, E3]
  exact alg (fun c => star (S.hT (e c) x)) (fun c => S.hT (e c) y) (fun c => star (S.hT (a c) x))
    (fun c => S.hT (a c) y) s (fun c d => S.hT (a c) (a d)) hs

theorem isom_nil (x y : S.V) :
    S.hT (x + nilF e a s x) (y + nilF e a s y) = S.hT x y := by
  have h := form_nil e a s hiso hea hs x y
  simp only [map_add (f := _), LinearMap.add_apply]
  linear_combination h

end Form

theorem isO_sum {ι : Type} (t : Finset ι) (f : ι → E) (h : ∀ i ∈ t, ∃ o : 𝓞 E, (o : E) = f i) :
    ∃ o : 𝓞 E, (o : E) = ∑ i ∈ t, f i := by
  exact Finset.sum_induction f (fun z => ∃ o : 𝓞 E, (o : E) = z)
    (fun _ _ ⟨o1, h1⟩ ⟨o2, h2⟩ => ⟨o1 + o2, by
      rw [← h1, ← h2]
      first | norm_cast | simp | exact map_add (algebraMap (𝓞 E) E) o1 o2⟩)
    ⟨0, by first | simp | norm_cast⟩ h

theorem smul_memO (Λ : Submodule (𝓞 E) S.V) {k : E} (hk : ∃ o : 𝓞 E, (o : E) = k) {x : S.V} (hx : x ∈ Λ) :
    k • x ∈ Λ := by
  obtain ⟨o, rfl⟩ := hk
  have h := Λ.smul_mem o hx
  first
    | (rw [← algebraMap_smul E o x] at h; exact h)
    | simpa using h

theorem nil_mem (Λ : Submodule (𝓞 E) S.V) (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (he : ∀ c, e c ∈ Λ) (ha : ∀ c, a c ∈ Λ) (hsO : ∀ c d, ∃ o : 𝓞 E, (o : E) = s c d)
    {v : S.V} (hv : v ∈ Λ) : nilF e a s v ∈ Λ := by
  rw [nilF_apply]
  refine Submodule.sum_mem _ fun c _ =>
    Λ.add_mem (smul_memO Λ (hint _ (he c) _ hv) (ha c)) (smul_memO Λ ?_ (he c))
  obtain ⟨o1, h1⟩ := hint _ (ha c) _ hv
  obtain ⟨o2, h2⟩ := isO_sum Finset.univ (fun d => s c d * S.hT (e d) v) (fun d _ => by
    obtain ⟨x1, hx1⟩ := hsO c d
    obtain ⟨x2, hx2⟩ := hint _ (he d) _ hv
    exact ⟨x1 * x2, by
      rw [← hx1, ← hx2]
      first | norm_cast | simp | exact map_mul (algebraMap (𝓞 E) E) x1 x2⟩)
  beta_reduce at h2
  refine ⟨-o1 + o2, ?_⟩
  rw [kap, ← h1, ← h2]
  first | norm_cast | simp

end PI.TermsAtPtFiniteW.HeisW

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef HeisW

theorem heisOp_holds : HeisOp := by
  intro E _ _ _ S r T Λ F a s hint he ha hea hsO hs
  have hiso : ∀ c d, S.hT (F.fl.e c) (F.fl.e d) = 0 := F.fl.e_iso
  have h3 := nil3 F.fl.e a s hiso hea
  have hfg : (LinearMap.id + nilF F.fl.e a s) ∘ₗ
      (LinearMap.id - nilF F.fl.e a s + nilF F.fl.e a s ∘ₗ nilF F.fl.e a s) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, h3]
    abel
  have hgf : (LinearMap.id - nilF F.fl.e a s + nilF F.fl.e a s ∘ₗ nilF F.fl.e a s) ∘ₗ
      (LinearMap.id + nilF F.fl.e a s) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, h3]
    abel
  refine ⟨LinearEquiv.ofLinear _ _ hfg hgf, ?_, fun v => ?_⟩
  swap
  · simp [LinearEquiv.ofLinear_apply, heis_eq]
  simp only [NLam, Set.mem_setOf_eq, IsAutLam]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    simp only [LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply]
    exact isom_nil F.fl.e a s hiso hea hs x y
  · unfold Formalism.HermitianLatticesTheory.gmap
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro v hv
      simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply]
      exact Λ.add_mem hv (nil_mem Λ F.fl.e a s hint he ha hsO hv)
    · intro v hv
      rw [Submodule.mem_map]
      refine ⟨v - nilF F.fl.e a s v + nilF F.fl.e a s (nilF F.fl.e a s v), ?_, ?_⟩
      · have h1 := nil_mem Λ F.fl.e a s hint he ha hsO hv
        exact Λ.add_mem (Λ.sub_mem hv h1) (nil_mem Λ F.fl.e a s hint he ha hsO h1)
      · simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply,
          LinearMap.add_apply, LinearMap.id_apply, map_add, map_sub, h3]
        abel
  · intro j x hx
    have hN : nilF F.fl.e a s x = 0 := by
      have hle : F.fl.Xa (j + 1) ≤ LinearMap.ker (nilF F.fl.e a s) := by
        show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨i, -, rfl⟩
        exact LinearMap.mem_ker.2 (nil_e F.fl.e a s hiso hea i)
      exact LinearMap.mem_ker.1 (hle hx)
    simp [LinearEquiv.ofLinear_apply, hN]
  · intro x hx
    have hx' : ∀ c, S.hT (F.fl.e c) x = 0 := by
      intro c
      have hmem : F.fl.e c ∈ Xsp F := by
        show F.fl.e c ∈ Submodule.span E (Set.range F.fl.e)
        exact Submodule.subset_span ⟨c, rfl⟩
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact hx _ hmem
    simp only [LinearEquiv.ofLinear_apply, LinearMap.add_apply, LinearMap.id_apply, add_sub_cancel_left]
    rw [nilF_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [hx' c, zero_smul, zero_add]
    refine Submodule.smul_mem _ _ ?_
    show F.fl.e c ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨c, rfl⟩

end PI.TermsAtPtFiniteW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFin
section
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ndS (D : D7) : ℕ :=
  (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))) ^ D.R.rS

def FInt : Prop :=
  ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (f : Fin D.R.rS → (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ a b, (VS D).hT (f a) (f b) = 0) → (∀ a b, (VS D).hT (F0.e a) (f b) = if a = b then 1 else 0) →
    (∀ x ∈ L, ∀ a, (VS D).hT (F0.e a) x = 0 ∧ (VS D).hT (f a) x = 0) →
    Λ = latSpan (aaS D) F0.e ⊔ L ⊔ latSpan (fun a => (aaS D a)⁻¹) f →
    0 < ndS D ∧ ∀ x ∈ Λ, ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (ndS D : D.host.E) * (VS D).hT (f c) x

def ResFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V), Λ.FG → ∀ c : ℕ, 0 < c →
      ∃ (R : Type) (_ : Finite R) (ρ : V → R), ∀ x ∈ Λ, ∀ y ∈ Λ, ρ x = ρ y →
        ∃ l ∈ Λ, y - x = (c : E) • l

end PI.TermsAtPtFiniteW
end
end

