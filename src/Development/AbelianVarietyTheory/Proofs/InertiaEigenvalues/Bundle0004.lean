module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotientEqOfPowSubSelfMem
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem card_quotient_eq_of_pow_sub_self_mem : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  intro R _ P _ q ζ hq hζ hprim hall
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hfix : ∀ x : R ⧸ P, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hall y
  set f : Polynomial (R ⧸ P) := X ^ q - X with hf
  have hdeg : f.natDegree = q := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, mem_roots hf0]
    simp [hf, hfix x]
  haveI : Finite (R ⧸ P) := by
    apply Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))
    intro a b h; simpa using congrArg Subtype.val h
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card (R ⧸ P) = (Finset.univ : Finset (R ⧸ P)).card := rfl
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (fun x _ => hmem x)
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  · set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz
    have hz1 : z ^ (q - 1) = 1 := by rw [hz, ← map_pow, hζ, map_one]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1
    have hord : orderOf z = q - 1 := by
      rw [orderOf_eq_iff (by omega)]
      refine ⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]
    have hinj := pow_injOn_Iio_orderOf (x := z)
    rw [hord] at hinj
    let g : Fin q → R ⧸ P := fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      apply Fin.ext
      by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab
      · omega
      · exact absurd hab.symm (pow_ne_zero _ hz0)
      · exact absurd hab (pow_ne_zero _ hz0)
      · have := hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega)
          (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab
        omega
    have := Nat.card_le_card_of_injective g hg
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesFinrankCongr
section
open scoped BigOperators

namespace GlobalTheory

open Module

theorem card_subspaces_le_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (p : Submodule k V) (j : ℕ) :
    Nat.card {U : Submodule k V // U ≤ p ∧ finrank k U = j} =
      Nat.card {U : Submodule k p // finrank k U = j} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun U => ⟨U.1.map p.subtype, Submodule.map_subtype_le p U.1, ?_⟩) ⟨?_, ?_⟩)
  · rw [Submodule.finrank_map_subtype_eq]; exact U.2
  · intro U U' h
    exact Subtype.ext (Submodule.map_injective_of_injective p.injective_subtype
      (congrArg Subtype.val h))
  · rintro ⟨U, hU, hj⟩
    have h : (U.comap p.subtype).map p.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    refine ⟨⟨U.comap p.subtype, ?_⟩, Subtype.ext h⟩
    rw [← Submodule.finrank_map_subtype_eq, h, hj]

theorem card_subspaces_finrank_congr {k V V' : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (e : V ≃ₗ[k] V') (j : ℕ) :
    Nat.card {U : Submodule k V // finrank k U = j} =
      Nat.card {U : Submodule k V' // finrank k U = j} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_)
  intro U
  have : finrank k (U.map (e : V →ₗ[k] V')) = finrank k U := LinearEquiv.finrank_map_eq e U
  change _ ↔ finrank k (U.map (e : V →ₗ[k] V')) = j
  rw [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyProductPartialSumsDvdPow
section
theorem GlobalTheory.cauchy_product_dvd_pow : ∀ {R : Type} [CommRing R] (x : R) (α β : ℕ → R) (A B : R), (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A - ∑ p ∈ Finset.range n, α p) → (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ B - ∑ q ∈ Finset.range n, β q) → ∀ r : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, x ^ r ∣ A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p) := by
  intro R _ x α β A B hA hB r
  obtain ⟨NA, hNA⟩ := hA r
  obtain ⟨NB, hNB⟩ := hB r
  have hα : ∀ p ≥ NA, x ^ r ∣ α p := by
    intro p hp
    have h1 := hNA p hp
    have h2 := hNA (p + 1) (by omega)
    have e : α p = (A - ∑ i ∈ Finset.range p, α i) - (A - ∑ i ∈ Finset.range (p + 1), α i) := by
      rw [Finset.sum_range_succ]; ring
    rw [e]; exact dvd_sub h1 h2
  refine ⟨NA + NB, fun n hn => ?_⟩
  have key : ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = ∑ p ∈ Finset.range n, α p * ∑ q ∈ Finset.range (n - p), β q := by
    rw [Finset.sum_range_diag_flip n (fun p q => α p * β q)]
    simp only [Finset.mul_sum]
  have hsplit : A * B - ∑ k ∈ Finset.range n, ∑ p ∈ Finset.range (k + 1), α p * β (k - p)
      = (A - ∑ p ∈ Finset.range n, α p) * B
        + ∑ p ∈ Finset.range n, α p * (B - ∑ q ∈ Finset.range (n - p), β q) := by
    rw [key, Finset.sum_congr rfl (fun p _ => mul_sub (α p) B _), Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit]
  refine dvd_add (dvd_mul_of_dvd_left (hNA n (by omega)) _) (Finset.dvd_sum fun p _ => ?_)
  by_cases hp' : NA ≤ p
  · exact dvd_mul_of_dvd_left (hα p hp') _
  · exact dvd_mul_of_dvd_right (hNB _ (by omega)) _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CenterMonoidAlgebraLeSpanCentralIntegral
section
namespace GlobalTheory.GroupAlg.ClassSum

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

noncomputable def classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ h, single h (if ConjClasses.mk h = C then (1 : ℤ) else 0)

theorem coeff_classSum [DecidableEq (ConjClasses G)] (C : ConjClasses G) (y : G) :
    (classSum C).coeff y = if ConjClasses.mk y = C then 1 else 0 := by
  classical
  simp [classSum, coeff_sum, coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem classSum_comm [DecidableEq (ConjClasses G)] (C : ConjClasses G) (a : MonoidAlgebra ℤ G) :
    classSum C * a = a * classSum C := by
  induction a using MonoidAlgebra.induction_on with
  | of k =>
    apply MonoidAlgebra.ext
    ext x
    simp only [MonoidAlgebra.of_apply, coeff_mul_single_apply, coeff_single_mul_apply, coeff_classSum,
      mul_one, one_mul]
    have : ConjClasses.mk (x * k⁻¹) = ConjClasses.mk (k⁻¹ * x) := by
      rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨k⁻¹, by group⟩
    rw [this]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem coeff_conj_eq {R : Type} [CommRing R] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) {a b : G} (hab : IsConj a b) :
    z.coeff a = z.coeff b := by
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  have h := congrArg (fun w => w.coeff (g * a)) (hz (single g (1 : R)))
  simp only [coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one, inv_mul_cancel_left] at h
  exact h

theorem mem_span (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) ''
      {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  classical
  haveI := Fintype.ofFinite G
  haveI : Fintype (ConjClasses G) := Fintype.ofFinite _
  let rep : ConjClasses G → G := fun C => C.exists_rep.choose
  have hrep : ∀ C, ConjClasses.mk (rep C) = C := fun C => C.exists_rep.choose_spec
  have hmap : ∀ (C : ConjClasses G) (x : G),
      (MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C)).coeff x =
        if ConjClasses.mk x = C then 1 else 0 := by
    intro C x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [classSum, map_sum, coeff_sum, coeff_single,
      Finsupp.finsetSum_apply, Finsupp.single_apply, apply_ite (Int.cast : ℤ → R)]
  have hz' : z = ∑ C, z.coeff (rep C) • MonoidAlgebra.mapRingHom G (Int.castRingHom R) (classSum C) := by
    apply MonoidAlgebra.ext
    ext x
    rw [coeff_sum, Finsupp.finsetSum_apply]
    simp only [coeff_smul, Finsupp.smul_apply, hmap, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine coeff_conj_eq z hz ?_
    rw [← ConjClasses.mk_eq_mk_iff_isConj, hrep]
  rw [hz']
  refine Submodule.sum_mem _ fun C _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨classSum C, ?_, rfl⟩)
  exact classSum_comm C

end GlobalTheory.GroupAlg.ClassSum

theorem GlobalTheory.GroupAlg.center_mem_span_classSums : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) :=
  fun R G _ _ _ z hz => GlobalTheory.GroupAlg.ClassSum.mem_span R G z hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralLinearFormPiMatrixEqSumTrace
section
namespace GlobalTheory

open Matrix

theorem linearForm_matrix_eq_smul_trace_of_comm (k : Type) [Field k] (m : ℕ)
    (t : Matrix (Fin m) (Fin m) k →ₗ[k] k) (ht : ∀ x y, t (x * y) = t (y * x)) :
    ∃ c : k, ∀ x, t x = c * x.trace := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨0, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : k, t (single (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ 1) = c := ⟨_, rfl⟩
    refine ⟨c, fun x => ?_⟩
    set o : Fin m := ⟨0, hm⟩
    have key : ∀ a b : Fin m, t (single a b 1) = if a = b then c else 0 := by
      intro a b
      split_ifs with hab
      · subst hab
        have h1 : single a a (1 : k) = single a o 1 * single o a 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single o o (1 : k) = single o a 1 * single a o 1 := by
          rw [single_mul_single_same, mul_one]
        rw [h1, ht, ← h2, hc]
      · have h1 : single a b (1 : k) = single a a 1 * single a b 1 := by
          rw [single_mul_single_same, mul_one]
        have h2 : single a b (1 : k) * single a a 1 = 0 :=
          single_mul_single_of_ne (1 : k) a b a (Ne.symm hab) 1
        rw [h1, ht, h2, map_zero]
    have hx : x = ∑ a, ∑ b, x a b • single a b (1 : k) := by
      conv_lhs => rw [matrix_eq_sum_single x]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [smul_single, smul_eq_mul, mul_one]
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]

theorem centralLinearForm_pi_matrix_eq_sum_trace :
    ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ)
      (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k),
      (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  intro k _ N n τ hτ
  have h : ∀ i, ∃ c : k, ∀ A, (τ ∘ₗ LinearMap.single k (fun i => Matrix (Fin (n i)) (Fin (n i)) k) i) A
      = c * A.trace := by
    intro i
    refine linearForm_matrix_eq_smul_trace_of_comm k (n i) _ fun A B => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Pi.single_mul, Pi.single_mul, hτ]
  choose c hc using h
  refine ⟨c, fun x => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hc i (x i)
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChainLeIInfSupPowSmulTopOfPrecomplete
section
namespace GlobalTheory

theorem mem_ideal_smul_top_pi_fin_iff {Λ : Type} [CommRing Λ] (J : Ideal Λ) {a : ℕ}
    (y : Fin a → Λ) : y ∈ J • (⊤ : Submodule Λ (Fin a → Λ)) ↔ ∀ i, y i ∈ J := by
  constructor
  · intro h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro r hr m _ i
      exact J.mul_mem_right _ hr
    · intro x z hx hz i
      exact J.add_mem (hx i) (hz i)
  · intro h
    rw [pi_eq_sum_univ y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem chain_le_iInf_sup_pow_smul_top :
    ∀ (Λ : Type) [CommRing Λ] (I : Ideal Λ) [IsPrecomplete I Λ] (a : ℕ)
      (N : ℕ → Submodule Λ (Fin a → Λ)),
  (∀ n, N (n + 1) ≤ N n) → (∀ n, I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) ≤ N n) →
  (∀ n, N n ≤ N (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ))) →
  ∀ n, N n ≤ (⨅ k, N k) ⊔ I ^ (n + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
  intro Λ _ I hI a N hanti hpow hstep n x hx
  have hA : Antitone N := antitone_nat_of_succ_le hanti
  have step : ∀ m (y : N m), ∃ z : N (m + 1),
      (y : Fin a → Λ) - z ∈ I ^ (m + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro m y
    obtain ⟨z, hz, w, hw, h⟩ := Submodule.mem_sup.1 (hstep m y.2)
    refine ⟨⟨z, hz⟩, ?_⟩
    have : (y : Fin a → Λ) - z = w := by rw [← h]; abel
    simpa [this] using hw
  choose f hf using step
  let u : ∀ j : ℕ, N (n + j) := fun j =>
    Nat.rec (motive := fun j => N (n + j)) ⟨x, hx⟩ (fun j y => f (n + j) y) j
  have hu0 : (u 0 : Fin a → Λ) = x := rfl
  have hus : ∀ j, (u j : Fin a → Λ) - u (j + 1) ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := fun j => hf (n + j) (u j)
  have htel : ∀ j j', j ≤ j' → ∀ i, (u j : Fin a → Λ) i - (u j' : Fin a → Λ) i ∈
      I ^ (n + j + 1) := by
    intro j j' hjj i
    induction j', hjj using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h1 := (mem_ideal_smul_top_pi_fin_iff _ _).1 (hus k) i
      have h2 : I ^ (n + k + 1) ≤ I ^ (n + j + 1) := Ideal.pow_le_pow_right (by omega)
      have h3 := Ideal.add_mem _ ih (h2 h1)
      simpa using h3
  have hlim : ∀ i, ∃ L : Λ, ∀ j, (u j : Fin a → Λ) i - L ∈ I ^ j := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun j => (u j : Fin a → Λ) i) (by
      intro m k hmk
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact Ideal.pow_le_pow_right (by omega) (htel m k hmk i))
    refine ⟨L, fun j => ?_⟩
    have := hL j
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using hlim
  have hdiff : ∀ j, (u j : Fin a → Λ) - L ∈
      I ^ (n + j + 1) • (⊤ : Submodule Λ (Fin a → Λ)) := by
    intro j
    rw [mem_ideal_smul_top_pi_fin_iff]
    intro i
    have h3 := Ideal.add_mem _ (htel j (n + j + 1) (by omega) i) (hL i (n + j + 1))
    simpa using h3
  have hLmem : L ∈ ⨅ k, N k := by
    rw [Submodule.mem_iInf]
    intro k
    have h1 : (u k : Fin a → Λ) - (u k - L) ∈ N (n + k) :=
      Submodule.sub_mem _ (u k).2 (hpow _ (hdiff k))
    rw [sub_sub_cancel] at h1
    exact hA (by omega) h1
  refine Submodule.mem_sup.2 ⟨L, hLmem, x - L, hdiff 0, by abel⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPowPrimeOrderEmbeddingsDifferByCoprimePower
section
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charPowPrimeOrder_embeddings_differ_by_coprime_power :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) C)
  set u : Cˣ := (ζ : Cˣ) with hu
  have hul : u ^ (l ^ n) = 1 := (mem_rootsOfUnity _ _).mp ζ.2
  set k := orderOf u with hk
  have hkd : k ∣ l ^ n := orderOf_dvd_of_pow_eq_one hul
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hkd; exact (NeZero.ne (l ^ n)) (Nat.eq_zero_of_zero_dvd hkd))
  haveI : NeZero k := ⟨hk0.ne'⟩
  have hpu : IsPrimitiveRoot (u : C) k := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)
  have h1 : IsPrimitiveRoot (e (u : C)) k := hpu.map_of_injective e.injective
  have h2 : IsPrimitiveRoot (e' (u : C)) k := hpu.map_of_injective e'.injective
  obtain ⟨i, hik, hi⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hic : i.Coprime k := (h1.pow_iff_coprime hk0 i).mp (by rw [hi]; exact h2)
  refine ⟨i + k, ?_, ?_⟩
  · have hc : (i + k).Coprime k := by simpa using hic
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).mp hkd
    rcases m with _ | m
    · simp at hm
      have : i = 0 := by omega
      subst this
      rw [hm] at hdvd
      exact hl.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))
    · have hlk : l ∣ k := by rw [hm]; exact dvd_pow_self l (Nat.succ_ne_zero m)
      have := Nat.Coprime.coprime_dvd_left hdvd hc
      have := Nat.Coprime.coprime_dvd_right hlk this
      exact hl.one_lt.ne' (by simpa using this)
  · have hEu : e' (u : C) = e (u : C) ^ (i + k) := by
      rw [pow_add, hi, h1.pow_eq_one, mul_one]
    let E : Cˣ →* ℂˣ := Units.map (e : C →* ℂ)
    let E' : Cˣ →* ℂˣ := Units.map (e' : C →* ℂ)
    have hEu' : E' u = E u ^ (i + k) := by
      ext; simp [E, E', hEu]
    intro g
    have hmem : ψ g ∈ rootsOfUnity (l ^ n) C := (mem_rootsOfUnity _ _).mpr (hψ g)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨ψ g, hmem⟩)
    have hj' : u ^ j = ψ g := by
      have := congrArg Subtype.val hj
      simpa [hu] using this
    have key : E' (ψ g) = E (ψ g ^ (i + k)) := by
      rw [← hj', map_zpow, map_pow, map_zpow, hEu', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    have := congrArg Units.val key
    simpa [E, E'] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftEqMapOfSpanningLattice
section
open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_eq_map_of_spanning_lattice (R F A S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]
    [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S]
    [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A) (hι : Function.Injective ι)
    (hspan : Submodule.span F (Set.range ι) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly =
      ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  classical
  have hRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  haveI : Module.IsTorsionFree R S := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      apply hι
      have h1 : algebraMap R F r • ι x = 0 := by
        rw [algebraMap_smul, ← map_smul, h, map_zero]
      have h2 : algebraMap R F r ≠ 0 := fun h0 => hr (hRF (by simpa using h0))
      rw [map_zero]
      exact (smul_eq_zero.mp h1).resolve_left h2
  haveI : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin (Module.finrank R S)) R S := Module.finBasis R S
  refine ⟨_, b, fun x => ?_⟩
  have hexp : ∀ y : S, ι y = ∑ i, algebraMap R F (b.repr y i) • ι (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, algebraMap_smul]
  have hliR : LinearIndependent R (fun i => ι (b i)) :=
    b.linearIndependent.map' ι.toLinearMap (LinearMap.ker_eq_bot.mpr hι)
  have hli : LinearIndependent F (fun i => ι (b i)) :=
    (LinearIndependent.iff_fractionRing R F).mp hliR
  have hsp : ⊤ ≤ Submodule.span F (Set.range (fun i => ι (b i))) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [hexp y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin (Module.finrank R S)) F A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = ι (b i) := fun i => by simp [b']
  have hM : LinearMap.toMatrix b' b' (LinearMap.mulLeft F (ι x)) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft R x)).map (algebraMap R F) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hb', ← map_mul, hexp]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map]

end GlobalTheory
end

