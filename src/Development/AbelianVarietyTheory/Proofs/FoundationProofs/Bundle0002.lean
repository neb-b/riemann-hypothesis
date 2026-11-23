module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordConjOfCoord
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.Sl2Ad

variable {K : Type*} [Field K]

def coord (X : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K := ![X 0 1, X 1 0, X 0 0]

def ofCoord (v : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K := !![v 2, v 0; v 1, -v 2]

def ad (A : GL (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i

def form : LinearMap.BilinForm K (Fin 3 → K) := Matrix.toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2]

theorem trace_ofCoord (v : Fin 3 → K) : (ofCoord v).trace = 0 := by
  simp [ofCoord, Matrix.trace_fin_two]

theorem ofCoord_coord {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) : ofCoord (coord X) = X := by
  rw [Matrix.trace_fin_two] at hX
  ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord, coord] <;> linear_combination -hX

theorem coord_ofCoord (v : Fin 3 → K) : coord (ofCoord v) = v := by
  ext i; fin_cases i <;> simp [ofCoord, coord]

theorem coord_add (X Y : Matrix (Fin 2) (Fin 2) K) : coord (X + Y) = coord X + coord Y := by
  ext i; fin_cases i <;> simp [coord]

theorem coord_smul (c : K) (X : Matrix (Fin 2) (Fin 2) K) : coord (c • X) = c • coord X := by
  ext i; fin_cases i <;> simp [coord]

theorem ofCoord_eq_sum (v : Fin 3 → K) : ofCoord v = ∑ j, v j • ofCoord (Pi.single j 1) := by
  ext i k; fin_cases i <;> fin_cases k <;> simp [ofCoord, Fin.sum_univ_three]

theorem coord_conj_ofCoord (A : GL (Fin 2) K) (v : Fin 3 → K) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * ofCoord v * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ v := by
  conv_lhs => rw [ofCoord_eq_sum]
  ext i
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mulVec, dotProduct, ad, Matrix.of_apply]
  rw [show ∀ (s : Finset (Fin 3)) (f : Fin 3 → Matrix (Fin 2) (Fin 2) K), coord (∑ j ∈ s, f j) i = ∑ j ∈ s, coord (f j) i from by
    intro s f; induction s using Finset.induction_on with
    | empty => simp [coord]; fin_cases i <;> rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coord_add, Pi.add_apply, ih]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coord_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem trace_conj (A : GL (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem coord_conj (A : GL (Fin 2) K) {X : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) :
    coord ((A : Matrix (Fin 2) (Fin 2) K) * X * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = ad A *ᵥ coord X := by
  conv_lhs => rw [← ofCoord_coord hX]
  exact coord_conj_ofCoord A _

theorem ad_mul (A B : GL (Fin 2) K) : ad (A * B) = ad A * ad B := by
  ext i j
  have h1 := coord_conj_ofCoord (A * B) (Pi.single j 1)
  have h2 := coord_conj_ofCoord B (Pi.single j 1)
  have h3 := coord_conj A (X := (B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (by rw [trace_conj, trace_ofCoord])
  rw [h2] at h3
  have : ((A * B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * (((A * B)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (A : Matrix (Fin 2) (Fin 2) K) * ((B : Matrix (Fin 2) (Fin 2) K) * ofCoord (Pi.single j 1) * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    simp only [mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  rw [this, h3, Matrix.mulVec_mulVec] at h1
  have := congrFun h1 i
  simpa [Matrix.mulVec_single, Matrix.mul_apply] using this.symm

theorem ad_one : ad (1 : GL (Fin 2) K) = 1 := by
  ext i j
  simp only [ad, Matrix.of_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, coord_ofCoord]
  fin_cases i <;> fin_cases j <;> rfl

def adHom : GL (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := ad
  map_one' := ad_one
  map_mul' := ad_mul

theorem form_apply (v w : Fin 3 → K) : form v w = v 0 * w 1 + v 1 * w 0 + 2 * (v 2 * w 2) := by
  simp [form, Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem form_coord {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0) (hY : Y.trace = 0) :
    form (coord X) (coord Y) = (X * Y).trace := by
  rw [Matrix.trace_fin_two] at hX hY
  rw [form_apply]
  simp [coord, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (X 0 0) * hY - (Y 1 1) * hX

end GlobalTheory.Sl2Ad

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension
section
open Polynomial

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem algebraMap_quot_bijective (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  haveI : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k (A ⧸ P)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem maximal_part (P : Ideal A) (hP : P.IsMaximal) :
    Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0 := by
  have hb := algebraMap_quot_bijective (k := k) P
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hb
  refine ⟨?_, ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩⟩
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · change u ∈ P ↔ e.symm (Ideal.Quotient.mkₐ k P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (P : Ideal A) [P.IsMaximal] (a : A) :
    ∃ c : k, a - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quot_bijective (k := k) P).2 (Ideal.Quotient.mk P a)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hc
  rw [← P.neg_mem_iff, neg_sub]
  exact hc

theorem span_sup_mul_eq (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (x : A) (hx : x ∈ I)
    (hxP : x ∉ I * P) : Ideal.span {x} ⊔ I * P = I := by
  have hKI : Ideal.span {x} ⊔ I * P ≤ I :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) Ideal.mul_le_left
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hKI
  have hPL : I * P ≤ I * L := hL ▸ le_sup_right
  have hLP : P ≤ L := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1
    (Ideal.dvd_iff_le.2 hPL))
  by_cases hLt : L = ⊤
  · rw [hL, hLt, Ideal.mul_top]
  · have := hP.eq_of_le hLt hLP
    subst this
    exact absurd (hL ▸ (le_sup_left : Ideal.span {x} ≤ _) (Ideal.mem_span_singleton_self x)) hxP

theorem rank_quot_mul_maximal (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) :
    Module.rank k (A ⧸ (I * P)) = Module.rank k (A ⧸ I) + 1 := by
  haveI := hP
  have hne : I * P ≠ I := by
    intro h
    have h2 : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact hP.ne_top (mul_left_cancel₀ (show I ≠ 0 from hI) h2)
  obtain ⟨x, hx, hxP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm Ideal.mul_le_left h)
  let f : (A ⧸ (I * P)) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_left : I * P ≤ I)).toLinearMap
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  set v : A ⧸ (I * P) := Ideal.Quotient.mk _ x with hvdef
  have hv0 : v ≠ 0 := fun h => hxP (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hker : LinearMap.ker f = k ∙ v := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hy : y ∈ I := by
        have h0 : f (Ideal.Quotient.mk _ y) = 0 := hz
        exact Ideal.Quotient.eq_zero_iff_mem.1 h0
      have hyK : y ∈ Ideal.span {x} ⊔ I * P := by
        rw [span_sup_mul_eq I P hI hP x hx hxP]; exact hy
      obtain ⟨a', ha', z', hz', hsum⟩ := Submodule.mem_sup.1 hyK
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
      obtain ⟨c, hc⟩ := exists_sub_mem (k := k) P a
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← hsum, hvdef, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        Ideal.Quotient.eq]
      have h3 : algebraMap k A c * x - (a * x + z') = -((a - algebraMap k A c) * x) - z' := by
        ring
      rw [h3]
      refine Ideal.sub_mem _ ((I * P).neg_mem ?_) hz'
      rw [mul_comm I P]
      exact Ideal.mul_mem_mul hc hx
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show f v = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  have h1 := LinearMap.rank_range_add_rank_ker f
  rw [LinearMap.range_eq_top.2 hf, rank_top, hker] at h1
  have hv1 : Module.rank k (k ∙ v) = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hv0]; simp
  rw [← h1, hv1]

end DedekindCodim
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem rank_quot_top : Module.rank k (A ⧸ (⊤ : Ideal A)) = 0 := by
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact rank_subsingleton' k _

theorem maximal_of_prime {p : Ideal A} (hp : Prime p) : p ≠ ⊥ ∧ p.IsMaximal := by
  have hne : p ≠ ⊥ := hp.ne_zero
  exact ⟨hne, ((Ideal.prime_iff_isPrime hne).1 hp).isMaximal hne⟩

theorem rank_quot_lt (J : Ideal A) (hJ : J ≠ ⊥) : Module.rank k (A ⧸ J) < Cardinal.aleph0 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top]; exact Cardinal.aleph0_pos
  | h₃ a p ha hp ih =>
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    rw [mul_comm, rank_quot_mul_maximal a p ha hpm]
    exact Cardinal.add_lt_aleph0 (ih ha) Cardinal.one_lt_aleph0

theorem rank_quot_mul (J : Ideal A) (hJ : J ≠ ⊥) : ∀ I : Ideal A, I ≠ ⊥ →
    Module.rank k (A ⧸ (I * J)) = Module.rank k (A ⧸ I) + Module.rank k (A ⧸ J) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    intro I _
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top, Ideal.mul_top, add_zero]
  | h₃ a p ha hp ih =>
    intro I hI
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    have hIa : I * a ≠ ⊥ := mul_ne_zero (show I ≠ 0 from hI) ha
    rw [show I * (p * a) = (I * a) * p by ring, rank_quot_mul_maximal _ p hIa hpm, ih ha I hI,
      mul_comm p a, rank_quot_mul_maximal a p ha hpm, add_assoc]

theorem finite_quot (I : Ideal A) (hI : I ≠ ⊥) : Module.Finite k (A ⧸ I) :=
  Module.rank_lt_aleph0_iff.1 (rank_quot_lt I hI)

theorem finrank_quot_mul (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J) := by
  haveI := finite_quot (k := k) I hI
  haveI := finite_quot (k := k) J hJ
  haveI := finite_quot (k := k) (I * J) (mul_ne_zero (show I ≠ 0 from hI) (show J ≠ 0 from hJ))
  have h := rank_quot_mul (k := k) J hJ I hI
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem eq_of_le_of_finrank_le (I J : Ideal A) (hI : I ≠ ⊥) (hIJ : I ≤ J)
    (hr : Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J)) : I = J := by
  obtain ⟨L, rfl⟩ := Ideal.dvd_iff_le.2 hIJ
  have hJ : J ≠ ⊥ := fun h => hI (by rw [h]; exact (zero_mul L : (0 : Ideal A) * L = 0))
  have hL : L ≠ ⊥ := fun h => hI (by rw [h]; exact (mul_zero J : J * (0 : Ideal A) = 0))
  rw [finrank_quot_mul J L hJ hL] at hr
  have h0 : Module.finrank k (A ⧸ L) = 0 := by omega
  haveI := finite_quot (k := k) L hL
  have hs : Subsingleton (A ⧸ L) := Module.finrank_zero_iff.1 h0
  rw [Ideal.Quotient.subsingleton_iff.1 hs, Ideal.mul_top]

theorem dedekind_finiteType_codim : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A],
    (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧
      ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J) := by
  intro k A _ _ _ _ _ _ _
  exact ⟨fun I hI => finite_quot I hI, fun P hP => maximal_part P hP,
    fun I J hI hJ => finrank_quot_mul I J hI hJ,
    fun I J hI hIJ hr => eq_of_le_of_finrank_le I J hI hIJ hr⟩

end DedekindCodim
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizer
section
namespace GlobalTheory.K5.IntFrac

open Polynomial

theorem mem_adjoin_inv_of_isIntegral' {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨p, hpm, hp⟩ := hi
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one,
    one_mul] at hp
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ?_
    rw [h, Finset.sum_range_zero, pow_zero, zero_add] at hp
    exact one_ne_zero hp
  rw [hm] at hp
  have hzn : z ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hp
  have h1 : z = z ^ (m + 1) * z⁻¹ ^ m := by
    rw [pow_succ, mul_comm (z ^ m) z, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]
  have hterm : ∀ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i * z⁻¹ ^ m =
      algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [hk, Nat.add_sub_cancel_left, mul_assoc, pow_add, ← mul_assoc (z ^ i), ← mul_pow,
      mul_inv_cancel₀ hz, one_pow, one_mul]
  have key : z = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    rw [← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← neg_mul, ← hzn]
    exact h1
  have hmem : -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) ∈
      Algebra.adjoin R {z⁻¹} := by
    refine Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) _))
    exact Set.mem_singleton _
  rw [← key] at hmem
  exact hmem

theorem mem_of_div_le_one : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  intro O Ω _ _ _ v hv B hB π hπB hπ0 hπ1 hdiv
  have hvπ : 0 < v π := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hπ0)
  have hA : ∀ n : ℕ, ∀ a ∈ B, v (a / π ^ n) ≤ 1 → a / π ^ n ∈ B := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hle
      have hlt : v a < 1 := by
        have he : v a = v (a / π ^ (k + 1)) * v π ^ (k + 1) := by
          rw [map_div₀, map_pow, div_mul_cancel₀]
          exact pow_ne_zero _ hvπ.ne'
        rw [he]
        calc v (a / π ^ (k + 1)) * v π ^ (k + 1) ≤ 1 * v π ^ (k + 1) := by gcongr
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ hvπ.le hπ1 (Nat.succ_ne_zero k)
      have he : a / π ^ (k + 1) = a / π / π ^ k := by rw [pow_succ', div_div]
      rw [he] at hle ⊢
      exact ih _ (hdiv a ha hlt) hle
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · rw [hb0, div_zero]
    exact B.zero_mem
  have hvb : 0 < v b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb0)
  have hex : ∃ n, v π ^ (n + 1) < v b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hvb hπ1
    cases m with
    | zero => exact absurd (hB b hb) (not_le.mpr (by simpa using hm))
    | succ k => exact ⟨k, hm⟩
  classical
  set n := Nat.find hex with hndef
  have hn : v π ^ (n + 1) < v b := Nat.find_spec hex
  have hle : v b ≤ v π ^ n := by
    by_cases h0 : n = 0
    · rw [h0, pow_zero]
      exact hB b hb
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1] at hmin
      exact not_lt.mp hmin
  have hvπn : 0 < v π ^ n := pow_pos hvπ n
  have hvw_le : v (b / π ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ hvπn]
    exact hle
  have hwB : b / π ^ n ∈ B := hA n b hb hvw_le
  have hvw : v (b / π ^ n) = 1 := by
    refine le_antisymm hvw_le (not_lt.mp fun hlt => ?_)
    have h2 := hB _ (hdiv _ hwB hlt)
    rw [div_div, ← pow_succ, map_div₀, map_pow, div_le_one₀ (pow_pos hvπ _)] at h2
    exact not_le.mpr hn h2
  have hw0 : b / π ^ n ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hwinv : (b / π ^ n)⁻¹ ∈ B := by
    have hint : IsIntegral O (b / π ^ n)⁻¹ := (hv _).mp (by rw [map_inv₀, hvw, inv_one])
    have hmem := mem_adjoin_inv_of_isIntegral' (inv_ne_zero hw0) hint
    rw [inv_inv] at hmem
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hwB) hmem
  have haπ : a / π ^ n ∈ B := by
    apply hA n a ha
    have he : a / π ^ n = a / b * (b / π ^ n) := by field_simp
    rw [he, map_mul, hvw, mul_one]
    exact hab
  have he : a / b = a / π ^ n * (b / π ^ n)⁻¹ := by field_simp
  rw [he]
  exact B.mul_mem haπ hwinv

end GlobalTheory.K5.IntFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfPowEqOne
section
namespace GlobalTheory.RootOfUnityEqOne

open IsLocalRing

theorem eq_one_of_pow_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ}
    (hm : V.valuation (m : F) = 1) {ζ : F} (hζ : ζ ^ m = 1)
    (h1 : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  have hζV : ζ ∈ V := by
    apply V.mem_of_valuation_le_one
    have : ζ = (ζ - 1) + 1 := by ring
    rw [this]
    refine le_trans (Valuation.map_add _ _ _) (max_le h1.le ?_)
    simp
  set z : V := ⟨ζ, hζV⟩ with hz
  have hzm : z ^ m = 1 := Subtype.ext (by simpa [hz] using hζ)
  have hz1 : z - 1 ∈ maximalIdeal V := by
    rw [V.valuation_lt_one_iff]
    simpa [hz] using h1
  have hmu : IsUnit (m : V) := by
    rw [V.valuation_eq_one_iff]
    simpa using hm
  have hmI : (m : V) ∉ maximalIdeal V := fun h => (mem_maximalIdeal _).1 h hmu

  have hdiff : ∀ n : ℕ, (∑ i ∈ Finset.range n, z ^ i) - (n : V) ∈ maximalIdeal V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hp : z ^ n - 1 ∈ maximalIdeal V := by
        have : z - 1 ∣ z ^ n - 1 := sub_one_dvd_pow_sub_one z n
        obtain ⟨c, hc⟩ := this
        rw [hc]
        exact Ideal.mul_mem_right _ _ hz1
      have : (∑ i ∈ Finset.range n, z ^ i) + z ^ n - ((n + 1 : ℕ) : V)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : V)) + (z ^ n - 1) := by
        push_cast; ring
      rw [this]
      exact Ideal.add_mem _ ih hp
  have hs : (∑ i ∈ Finset.range m, z ^ i) ≠ 0 := by
    intro h0
    apply hmI
    have := hdiff m
    rw [h0, zero_sub] at this
    simpa using (maximalIdeal V).neg_mem this
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hzm, sub_self]
  have hz0 : z - 1 = 0 := (mul_eq_zero.1 hprod).resolve_left hs
  have : z = 1 := sub_eq_zero.1 hz0
  have := congrArg (fun w : V => (w : F)) this
  simpa [hz] using this

theorem main : ∀ {F : Type} [inst : Field F] (V : ValuationSubring F) {m : ℕ},
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (↑m : F) = (1 : ValuationSubring.ValueGroup V) →
    ∀ {ζ : F}, ζ ^ m = (1 : F) →
    (ValuationSubring.valuation V : F → ValuationSubring.ValueGroup V) (ζ - (1 : F)) < (1 : ValuationSubring.ValueGroup V) →
    ζ = (1 : F) := by
  intro F _ V m hm ζ hζ h1
  exact eq_one_of_pow_eq_one V hm hζ h1

end GlobalTheory.RootOfUnityEqOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsBis
section
namespace GlobalTheory.AlgebraicIntegerNormBound

theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
end

