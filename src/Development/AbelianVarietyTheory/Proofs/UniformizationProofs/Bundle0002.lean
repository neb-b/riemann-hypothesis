module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGradedRingKernelLift
section
open Polynomial

namespace GlobalTheory

def reesShiftIdeal {R : Type} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    rw [Subalgebra.coe_add, coeff_add]
    exact Ideal.add_mem _ (hp n) (hq n)
  smul_mem' := fun p q hq n => by
    rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ e
    have e' : j + k = n := by simpa using e
    rw [← e', add_assoc, pow_add]
    exact Ideal.mul_mem_mul (p.2 j) (hq k)

theorem mem_reesShiftIdeal {R : Type} [CommRing R] {I : Ideal R} (p : reesAlgebra I) :
    p ∈ reesShiftIdeal I ↔ ∀ n, (p : R[X]).coeff n ∈ I ^ (n + 1) := Iff.rfl

theorem coeff_sum_algebraMap_mul_rees {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by
  simp [Polynomial.algebraMap_eq]

theorem exists_graded_ring_kernel_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∃ (S : Type) (_ : CommRing S) (g : R →+* S), IsNoetherianRing S ∧ (∀ x ∈ I, g x = 0) ∧ ∀ (e : ℕ) (g' : R ⧸ I ^ (e + 1 + 1) →+* S), g'.comp (Ideal.Quotient.mk _) = g → ∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) (R ⧸ I ^ (e + 1 + 1))) (D₁ : Matrix (Fin c) (Fin b) (R ⧸ I ^ (e + 1 + 1))), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g').mulVec w = 0 → ∃ v, (D₀.map g').mulVec v = w) → ∀ v' : Fin a → R ⧸ I ^ (e + 1), (D₀.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))).mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) : R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) (v k) = v' k := by
  intro R _ _ I
  refine ⟨reesAlgebra I ⧸ reesShiftIdeal I, inferInstance,
    (Ideal.Quotient.mk _).comp (algebraMap R (reesAlgebra I)), inferInstance, ?_, ?_⟩
  ·
    intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    split_ifs with hn
    · subst hn
      simpa using hx
    · exact Ideal.zero_mem _
  · intro e g' hg' a b c D₀ D₁ hD hex v' hv'
    have hg'x : ∀ x : R, g' (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk (reesShiftIdeal I) (algebraMap R (reesAlgebra I) x) := fun x => by
      have := RingHom.congr_fun hg' x
      simpa only [RingHom.comp_apply] using this

    obtain ⟨d₀, rfl⟩ : ∃ d : Matrix (Fin b) (Fin a) R, D₀ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun j k => (Ideal.Quotient.mk_surjective (D₀ j k)).choose, by
        ext j k
        simp [(Ideal.Quotient.mk_surjective (D₀ j k)).choose_spec]⟩
    obtain ⟨d₁, rfl⟩ : ∃ d : Matrix (Fin c) (Fin b) R, D₁ = d.map (Ideal.Quotient.mk _) :=
      ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (D₁ i j)).choose, by
        ext i j
        simp [(Ideal.Quotient.mk_surjective (D₁ i j)).choose_spec]⟩
    obtain ⟨r, rfl⟩ : ∃ r : Fin a → R, v' = fun k => Ideal.Quotient.mk _ (r k) :=
      ⟨fun k => (Ideal.Quotient.mk_surjective (v' k)).choose,
        funext fun k => (Ideal.Quotient.mk_surjective (v' k)).choose_spec.symm⟩

    have hs : ∀ j, ∑ k, d₀ j k * r k ∈ I ^ (e + 1) := fun j => by
      have h := congrFun hv' j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Ideal.Quotient.factor_mk,
        Pi.zero_apply] at h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa only [map_mul] using h

    have hs2 : ∀ i, ∑ j, d₁ i j * ∑ k, d₀ j k * r k ∈ I ^ (e + 1 + 1) := fun i => by
      have hrow : ∀ k, ∑ j, d₁ i j * d₀ j k ∈ I ^ (e + 1 + 1) := fun k => by
        have h := congrFun (congrFun hD i) k
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at h
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simpa only [map_mul] using h
      have heq : ∑ j, d₁ i j * ∑ k, d₀ j k * r k = ∑ k, (∑ j, d₁ i j * d₀ j k) * r k := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [heq]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hrow k)

    obtain ⟨m, hm⟩ : ∃ m : Fin b → reesAlgebra I,
        ∀ j, (m j : R[X]) = Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k) :=
      ⟨fun j => ⟨Polynomial.monomial (e + 1) (∑ k, d₀ j k * r k),
        reesAlgebra.monomial_mem.mpr (hs j)⟩, fun _ => rfl⟩

    have hW : ((d₁.map (Ideal.Quotient.mk _)).map g').mulVec
        (fun j => Ideal.Quotient.mk (reesShiftIdeal I) (m j)) = 0 := by
      funext i
      have hmem : (∑ j, algebraMap R (reesAlgebra I) (d₁ i j) * m j) ∈ reesShiftIdeal I := by
        rw [mem_reesShiftIdeal]
        intro n
        rw [coeff_sum_algebraMap_mul_rees]
        simp only [hm, Polynomial.coeff_monomial]
        by_cases hn : e + 1 = n
        · subst hn
          simpa using hs2 i
        · simp [hn]
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, Pi.zero_apply,
        map_mul] using this

    obtain ⟨V, hV⟩ := hex _ hW
    choose P hP using fun k => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (V k)
    have hdiff : ∀ j, ∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k ∈
        I ^ (e + 1 + 1) := fun j => by
      have h := congrFun hV j
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hg'x, ← hP] at h
      have h' : Ideal.Quotient.mk (reesShiftIdeal I)
          (∑ k, algebraMap R (reesAlgebra I) (d₀ j k) * P k) =
          Ideal.Quotient.mk (reesShiftIdeal I) (m j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simpa only [map_mul] using h
      rw [Ideal.Quotient.eq, mem_reesShiftIdeal] at h'
      have h'' := h' (e + 1)
      rw [Subalgebra.coe_sub, Polynomial.coeff_sub, coeff_sum_algebraMap_mul_rees, hm,
        Polynomial.coeff_monomial, Finsupp.single_eq_same] at h''
      exact h''
    refine ⟨fun k => Ideal.Quotient.mk _ (r k - (P k : R[X]).coeff (e + 1)), ?_, ?_⟩
    · funext j
      have hmem : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) ∈ I ^ (e + 1 + 1) := by
        have heq : ∑ k, d₀ j k * (r k - (P k : R[X]).coeff (e + 1)) =
            -(∑ k, d₀ j k * (P k : R[X]).coeff (e + 1) - ∑ k, d₀ j k * r k) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        rw [heq]
        exact neg_mem (hdiff j)
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, map_mul] using this
    · intro k
      simp only [Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, sub_sub_cancel_left]
      exact neg_mem ((P k).2 (e + 1))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitOfSuccessiveCorrections
section
namespace GlobalTheory.Unif

theorem exists_limit_of_successive_corrections (R : Type) [CommRing R] (a : R) (M : Type)
    [AddCommGroup M] [Module R M] [IsPrecomplete (Ideal.span {a}) M] (K : ℕ → Submodule R M)
    (hK : ∀ e, K (e + 1) ≤ K e) (ha : ∀ (e : ℕ) (x : M), a ^ (e + 1) • x ∈ K e)
    (hs : ∀ e, ∀ x ∈ K e, ∃ y : M, x - a ^ (e + 1) • y ∈ K (e + 1)) :
    ∀ e, ∀ x ∈ K e, ∃ x' y : M, (∀ e', x' ∈ K e') ∧ x - x' = a ^ (e + 1) • y := by
  intro e x hx
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R M) ↔
      ∃ y : M, z = a ^ n • y := by
    intro n z
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, h⟩
      exact ⟨y, h.symm⟩
    · rintro ⟨y, h⟩
      exact ⟨y, trivial, h.symm⟩
  choose y hy using hs
  let s : (n : ℕ) → K (e + n) := fun n =>
    Nat.rec (motive := fun n => K (e + n)) ⟨x, hx⟩
      (fun n z => ⟨z.1 - a ^ (e + n + 1) • y (e + n) z.1 z.2, hy _ _ _⟩) n
  have hs0 : (s 0 : M) = x := rfl
  have hsn : ∀ n, (s (n + 1) : M) = s n - a ^ (e + n + 1) • y (e + n) (s n).1 (s n).2 :=
    fun n => rfl
  have hd : ∀ m n, m ≤ n → ∃ z : M, (s m : M) - s n = a ^ (e + m + 1) • z := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨z + a ^ k • y (e + (m + k)) (s (m + k)).1 (s (m + k)).2, ?_⟩
      rw [hsn, smul_add, ← hz, smul_smul, ← pow_add,
        show e + m + 1 + k = e + (m + k) + 1 by ring]
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) (M := M) inferInstance
    (f := fun n => (s n : M)) (by
      intro m n hmn
      obtain ⟨z, hz⟩ := hd m n hmn
      rw [SModEq.sub_mem, hmem]
      refine ⟨a ^ (e + 1) • z, ?_⟩
      rw [hz, smul_smul, ← pow_add, show m + (e + 1) = e + m + 1 by ring])
  have hl : ∀ m, ∃ z : M, (s m : M) - L = a ^ (e + m + 1) • z := by
    intro m
    obtain ⟨z, hz⟩ := hd m (e + m + 1) (by omega)
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    obtain ⟨w, hw⟩ := h
    refine ⟨z + w, ?_⟩
    rw [smul_add, ← hz, ← hw]
    abel
  obtain ⟨z, hz⟩ := hl 0
  refine ⟨L, z, fun m => ?_, hz⟩
  obtain ⟨w, hw⟩ := hl m
  have hLe : L = (s m : M) - a ^ (e + m + 1) • w := by rw [← hw]; abel
  apply hanti (show m ≤ e + m by omega)
  rw [hLe]
  exact Submodule.sub_mem _ (s m).2 (ha _ _)

end GlobalTheory.Unif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimeHomZmodOfNeTop
section
namespace GlobalTheory

theorem exists_prime_hom_zmod_of_ne_top (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Λ : AddSubgroup X) (h : Λ ≠ ⊤) :
    ∃ l : ℕ, l.Prime ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0 := by
  have h1 : (AddSubgroup.toIntSubmodule Λ) ≠ ⊤ := by
    intro h'
    apply h
    ext x
    have : x ∈ AddSubgroup.toIntSubmodule Λ := by rw [h']; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.toIntSubmodule Λ)).resolve_left h1
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.mpr hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  obtain ⟨n, hn⟩ := (IsPrincipalIdealRing.principal I).principal
  have hn' : I = Ideal.span {((n.natAbs : ℕ) : ℤ)} := by
    rw [Int.span_natAbs]; exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hb : I = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField hb
  have hp : (n.natAbs).Prime := by
    have := hI.isPrime
    rw [hn'] at this
    have h2 := (Ideal.span_singleton_prime (by simpa using hn0)).mp this
    exact Nat.prime_iff_prime_int.mpr h2
  let g : (ℤ ⧸ I) ≃+* ZMod n.natAbs :=
    (Ideal.quotEquivOfEq hn').trans (Int.quotientSpanNatEquivZMod n.natAbs)
  refine ⟨n.natAbs, hp, g.toAddMonoidHom.comp (e.toLinearMap.toAddMonoidHom.comp M.mkQ.toAddMonoidHom), ?_, ?_⟩
  · intro h0
    apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : g (e (M.mkQ x)) = 0 := DFunLike.congr_fun h0 x
    rw [map_eq_zero_iff _ g.injective, map_eq_zero_iff _ e.injective] at hx
    exact (Submodule.Quotient.mk_eq_zero M).mp hx
  · intro x hx
    have : M.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hle hx)
    change g (e (M.mkQ x)) = 0
    rw [this, map_zero, map_zero]

theorem support_subgroup_odd_index :
    ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (S S₂ : Set X), S.Nonempty → (∀ a b, (a ∈ S ∧ b ∈ S) ↔ (a + b ∈ S₂ ∧ a - b ∈ S₂)) → (∀ x : X, ∃ z : X, x + (z + z) ∈ S₂) → S₂ = S ∧ ∃ Λ : AddSubgroup X, (Λ : Set X) = S ∧ (Λ = ⊤ ∨ ∃ l : ℕ, l.Prime ∧ Odd l ∧ ∃ f : X →+ ZMod l, f ≠ 0 ∧ ∀ x ∈ Λ, f x = 0) := by
  intro X _ _ S S₂ ⟨a, ha⟩ h hd
  have h02 : (0 : X) ∈ S₂ := by simpa using ((h a a).mp ⟨ha, ha⟩).2
  have h0 : (0 : X) ∈ S := ((h 0 0).mpr ⟨by simpa using h02, by simpa using h02⟩).1
  have heq : S₂ = S := by
    ext x
    have := h x 0
    simp only [add_zero, sub_zero, and_self, h0, and_true] at this
    exact this.symm
  subst heq
  refine ⟨rfl, ?_⟩
  let Λ : AddSubgroup X :=
    { carrier := S₂
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => ((h a b).mp ⟨ha, hb⟩).1
      neg_mem' := fun {b} hb => by simpa using ((h 0 b).mp ⟨h0, hb⟩).2 }
  refine ⟨Λ, rfl, ?_⟩
  by_cases ht : Λ = ⊤
  · exact Or.inl ht
  · right
    obtain ⟨l, hl, f, hf, hΛ⟩ := exists_prime_hom_zmod_of_ne_top X Λ ht
    refine ⟨l, hl, ?_, f, hf, hΛ⟩
    refine hl.odd_of_ne_two ?_
    rintro rfl
    apply hf
    ext x
    obtain ⟨z, hz⟩ := hd x
    have h1 := hΛ _ hz
    have h2 : f z + f z = 0 := CharTwo.add_self_eq_zero _
    rw [map_add (f := _), map_add (f := _), h2, add_zero] at h1
    simpa using h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqBilinOfAnisotropic
section
namespace GlobalTheory

theorem exists_smul_eq_bilin_of_anisotropic {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : X →+ X →+ ℤ) (hB : ∀ a, B a a = 0 → a = 0) (l : X →+ ℚ) :
    ∃ (M : ℤ) (x : X), 0 < M ∧ ∀ m, (B x m : ℚ) = M * l m := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => l (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose c hc using hint
  let φ : Module.Dual ℤ X := b.constr ℤ c
  have hφ : ∀ m, (φ m : ℚ) = d * l m := by
    have : (Algebra.linearMap ℤ ℚ).comp φ = d • l.toIntLinearMap := by
      refine b.ext fun i => ?_
      have := hc i
      simpa [φ] using this
    intro m
    have := LinearMap.congr_fun this m
    simpa using this
  let Bh : X →+ Module.Dual ℤ X :=
    { toFun := fun x => (B x).toIntLinearMap
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let BL : X →ₗ[ℤ] Module.Dual ℤ X := Bh.toIntLinearMap
  have hBL : ∀ x m, BL x m = B x m := fun _ _ => rfl
  have hinj : Function.Injective BL := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    apply hB
    rw [← hBL, ha]; rfl
  have hrk : Module.finrank ℤ (LinearMap.range BL) = Module.finrank ℤ (Module.Dual ℤ X) := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact b.toDualEquiv.finrank_eq
  have hfin : Finite (Module.Dual ℤ X ⧸ LinearMap.range BL) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ hrk
  obtain ⟨n, hn, hnφ⟩ := (isOfFinAddOrder_of_finite
    (Submodule.Quotient.mk (p := LinearMap.range BL) φ)).exists_nsmul_eq_zero
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hnφ
  obtain ⟨x, hx⟩ := hnφ
  refine ⟨n * (d * d), d • x, mul_pos (by exact_mod_cast hn) (mul_self_pos.2 hd0), fun m => ?_⟩
  have h1 : B x m = n * φ m := by
    rw [← hBL, hx]; simp
  rw [map_zsmul, AddMonoidHom.zsmul_apply, h1]
  simp only [smul_eq_mul]
  push_cast
  rw [hφ]; ring

theorem exists_rep_mod_shifted_form_small :
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (l : X →+ ℚ) (k : ℕ), 1 ≤ k → ∀ y : X, ∃ z : X, ∀ m : X, |(B (y + k • z) m : ℚ) - l m| ≤ k * Q m := by
  intro X _ _ _ Q B hadd h2 hpos l k hk y
  have hQ0 : ∀ a, 0 ≤ Q a := by
    intro a
    by_cases ha : a = 0
    · have := h2 a
      rw [ha] at this ⊢
      simp at this
      omega
    · have := hpos a ha
      omega
  have hsm : ∀ (n : ℤ) a, Q (n • a) = n * n * Q a := by
    intro n a
    have e1 := h2 (n • a)
    have e2 := h2 a
    rw [map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, ← e2] at e1
    simp only [smul_eq_mul] at e1
    linarith
  obtain ⟨M, x, hM, hx⟩ := exists_smul_eq_bilin_of_anisotropic B (fun a ha => by
    by_contra h
    have := hpos a h
    have := h2 a
    omega) l
  let F : X → ℕ := fun z => (Q (M • (y + k • z) - x)).toNat
  obtain ⟨z, hz⟩ : ∃ z, ∀ z', F z ≤ F z' :=
    ⟨Function.argmin F, fun z' => Function.argmin_le F z'⟩
  refine ⟨z, fun m => ?_⟩
  have hz' : ∀ z', Q (M • (y + k • z) - x) ≤ Q (M • (y + k • z') - x) := by
    intro z'
    have := hz z'
    have a := hQ0 (M • (y + k • z) - x)
    have b := hQ0 (M • (y + k • z') - x)
    simp only [F] at this
    omega
  have key : ∀ s : ℤ, 0 ≤ (M * k * s) * (M * k * s) * Q m
      + (M * k * s) * (M * B (y + k • z) m - B x m) := by
    intro s
    have h := hz' (z + s • m)
    have e : M • (y + k • (z + s • m)) - x = (M • (y + k • z) - x) + (M * k * s) • m := by
      module
    rw [e, hadd, hsm, map_zsmul, map_sub, map_zsmul, AddMonoidHom.sub_apply,
      AddMonoidHom.zsmul_apply] at h
    simp only [smul_eq_mul] at h
    linarith
  have k1 : (0 : ℚ) ≤ ((M * k * 1) * (M * k * 1) * Q m
      + (M * k * 1) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key 1
  have k2 : (0 : ℚ) ≤ ((M * k * (-1)) * (M * k * (-1)) * Q m
      + (M * k * (-1)) * (M * B (y + k • z) m - B x m) : ℤ) := by exact_mod_cast key (-1)
  push_cast at k1 k2
  rw [hx] at k1 k2
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hp : (0 : ℚ) < M * M * k := by positivity
  set β : ℚ := ((B (y + k • z) m : ℤ) : ℚ)
  rw [abs_le]
  constructor
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m + (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith
  · have : (0 : ℚ) ≤ M * M * k * (k * Q m - (β - l m)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hp).1 this
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPrecompleteOfLeOfPowLe
section
namespace GlobalTheory.PrecompleteOfPowLe

universe u

theorem isPrecomplete_of_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m =>
    calc I ^ ((e + 1) * m) ≤ I ^ (e * m) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right m (Nat.le_succ e))
      _ = (I ^ e) ^ m := pow_mul I e m
      _ ≤ J ^ m := Ideal.pow_right_mono he m
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ (e + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos e)
  exact (hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))

end GlobalTheory.PrecompleteOfPowLe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfIsPullbackSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.Unif

theorem locallyQuasiFinite_of_isPullback_surjective :
    ∀ (X Z X' Z' : Scheme.{0}) (φ : X ⟶ Z) (φ' : X' ⟶ Z') (a : X' ⟶ X) (p : Z' ⟶ Z),
      IsPullback a φ' φ p → Surjective p → LocallyOfFiniteType φ → QuasiCompact φ →
      LocallyQuasiFinite φ' → LocallyQuasiFinite φ := by
  intro X Z X' Z' φ φ' a p h hp _ hqc _
  have : QuasiCompact φ' := MorphismProperty.of_isPullback h hqc
  refine LocallyQuasiFinite.of_finite_preimage_singleton φ fun z => ?_
  obtain ⟨z', rfl⟩ := p.surjective z
  refine ((φ'.finite_preimage_singleton z').image a).subset fun x hx => ?_
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := p) x z' hx
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · change φ' (h.isoPullback.inv w) = z'
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw2]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw1]

end GlobalTheory.Unif
end

