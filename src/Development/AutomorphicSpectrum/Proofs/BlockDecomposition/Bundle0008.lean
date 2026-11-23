module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGoodPoly
section
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

open Polynomial in
theorem deriv_aeval {R S L : Type*} [CommRing R] [CommRing S] [Field L] [Algebra R S] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] (E : Derivation ℤ L L) (I : Ideal S)
    (hI : ∀ r : R, ∃ s ∈ I, E (algebraMap R L r) = algebraMap S L s) (G : R[X]) (b : S) :
    ∃ s ∈ I, E (algebraMap S L (aeval b G)) =
      algebraMap S L s + algebraMap S L (aeval b (derivative G)) * E (algebraMap S L b) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s1, h1, e1⟩ := hp
    obtain ⟨s2, h2, e2⟩ := hq
    refine ⟨s1 + s2, I.add_mem h1 h2, ?_⟩
    simp only [map_add (f := _), derivative_add, e1, e2]
    ring
  | monomial n a =>
    obtain ⟨s, hs, es⟩ := hI a
    refine ⟨b ^ n * s, I.mul_mem_left _ hs, ?_⟩
    have h1 : algebraMap S L (aeval b (monomial n a)) = algebraMap R L a * (algebraMap S L b) ^ n := by
      rw [aeval_monomial, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap S L (aeval b (derivative (monomial n a))) =
        algebraMap R L a * ((n : L) * (algebraMap S L b) ^ (n - 1)) := by
      rw [derivative_monomial, aeval_monomial, map_mul, map_pow, map_mul, map_natCast, map_mul,
        ← IsScalarTower.algebraMap_apply, map_natCast]
      ring
    rw [h1, h2, Derivation.leibniz, Derivation.leibniz_pow, es]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_pow]
    ring

open Polynomial in
theorem exists_good_poly {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Algebra R S]
    [Algebra.IsIntegral R S] (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (P : Ideal S) (hP : P ≠ ⊤)
    (b : S) : ∃ G : R[X], aeval b G ∈ P ∧ aeval b (derivative G) ∉ P := by
  classical
  have hex : ∃ n : ℕ, ∃ G : R[X], G.Monic ∧ G.natDegree = n ∧ aeval b G ∈ P := by
    obtain ⟨G, hG, h0⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    exact ⟨_, G, hG, rfl, by
      have : aeval b G = 0 := by rw [aeval_def]; exact h0
      rw [this]; exact P.zero_mem⟩
  obtain ⟨G, hG, hdeg, hmem⟩ := Nat.find_spec hex
  refine ⟨G, hmem, fun hd => ?_⟩
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    have : G = 1 := hG.natDegree_eq_zero.1 hdeg
    rw [this, map_one] at hmem
    exact hP ((Ideal.eq_top_iff_one _).2 hmem)
  obtain ⟨u, hu⟩ := hnat n hn0
  let G1 : R[X] := C (↑u⁻¹ : R) * derivative G
  have hG1 : G1.Monic := by
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n - 1)
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [← hdeg]; exact natDegree_derivative_le G
    · have : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)
      simp only [G1, coeff_C_mul, coeff_derivative, this]
      rw [← hdeg, hG.coeff_natDegree, hdeg]
      simp only [one_mul, Nat.cast_sub (Nat.pos_of_ne_zero hn0), Nat.cast_one, sub_add_cancel]
      rw [← hu]; simp
  have hlt : G1.natDegree < n := by
    have : G1.natDegree ≤ n - 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [← hdeg]; exact natDegree_derivative_le G
    omega
  refine Nat.find_min hex hlt ⟨G1, hG1, rfl, ?_⟩
  simp only [G1, map_mul, aeval_C]
  exact P.mul_mem_left _ hd

section core
variable {R S L Γ : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S] [WfDvdMonoid S]
  [Field L] [Algebra R S] [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
  [Algebra.IsIntegral R S] [LinearOrderedCommGroupWithZero Γ]

theorem core (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (v : Valuation L Γ) (ϖ : S)
    (hS : ∀ x : S, v (algebraMap S L x) ≤ 1)
    (hlt : ∀ x : S, v (algebraMap S L x) < 1 ↔ ϖ ∣ x)
    (E : Derivation ℤ L L) (I : Ideal S)
    (hI : ∀ r : R, ∃ s ∈ I, E (algebraMap R L r) = algebraMap S L s)
    (π : S) (hπ0 : π ≠ 0) (hπ : ϖ ∣ π)
    (hEπ : ∃ s : S, E (algebraMap S L π) = algebraMap S L (π * s))
    (δ : S) (hδ : δ ≠ 0) (hδE : ∀ x : S, ∃ y : S, algebraMap S L δ * E (algebraMap S L x) = algebraMap S L y) :
    (∀ x : S, v (E (algebraMap S L x)) ≤ 1) ∧ (∀ x : S, ϖ ∣ x → v (E (algebraMap S L x)) < 1) ∧
      (I ≤ Ideal.span {ϖ} → ∀ x : S, v (E (algebraMap S L x)) < 1) := by
  classical
  have inj := IsFractionRing.injective S L
  set ι := algebraMap S L with hι
  have hne : ∀ x : S, x ≠ 0 → ι x ≠ 0 := fun x hx h => hx (inj (by simpa using h))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ0 (by simpa [h] using hπ)
  have hϖu : ¬ IsUnit ϖ := fun h => by
    have := (hlt 1).2 (h.dvd)
    simp at this
  have hone : ∀ x : S, ¬ ϖ ∣ x → v (ι x) = 1 := fun x hx =>
    le_antisymm (hS x) (not_lt.1 (fun h => hx ((hlt x).1 h)))
  set c := v (ι ϖ) with hc
  have hc1 : c < 1 := (hlt ϖ).2 dvd_rfl
  have hc0 : c ≠ 0 := by
    rw [hc, Valuation.ne_zero_iff]; exact hne _ hϖ0
  have hle_c : ∀ x : S, ϖ ∣ x → v (ι x) ≤ c := by
    rintro x ⟨z, rfl⟩
    rw [map_mul, map_mul]
    exact mul_le_of_le_one_right' (hS z)

  obtain ⟨e, w, hw, hπw⟩ := WfDvdMonoid.max_power_factor' hπ0 hϖu
  have he : e ≠ 0 := by
    rintro rfl
    apply hw
    rw [pow_zero, one_mul] at hπw
    rwa [← hπw]
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hw0 : ι w ≠ 0 := hne _ (fun h => hw (by simp [h]))
  have hvw : v (ι w) = 1 := hone w hw
  have hnatv : ∀ n : ℕ, n ≠ 0 → v (n : L) = 1 := by
    intro n hn
    have hu : IsUnit (n : S) := by
      have := (hnat n hn).map (algebraMap R S)
      simpa using this
    have : ¬ ϖ ∣ (n : S) := fun h => hϖu (isUnit_of_dvd_unit h hu)
    have := hone _ this
    simpa [hι] using this

  have stepA : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → v (E (ι ϖ)) ≤ c * T := by
    intro T hT hb
    obtain ⟨s, hs⟩ := hEπ
    have h1 : E (ι π) = (ι ϖ) ^ (e' + 1) * E (ι w) +
        ι w * (((e' + 1 : ℕ) : L) * (ι ϖ) ^ e' * E (ι ϖ)) := by
      rw [hπw, map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]
      push_cast
      ring
    have h2 : ι w * (((e' + 1 : ℕ) : L) * E (ι ϖ)) = ι ϖ * (ι w * ι s - E (ι w)) := by
      have h3 : (ι ϖ) ^ e' ≠ 0 := pow_ne_zero _ (hne _ hϖ0)
      apply mul_left_cancel₀ h3
      have h4 : ι π = (ι ϖ) ^ (e' + 1) * ι w := by rw [hπw, map_mul, map_pow]
      have h5 : E (ι π) = (ι ϖ) ^ (e' + 1) * ι w * ι s := by rw [hs, map_mul, h4]
      rw [h5] at h1
      linear_combination -h1
    have h3 := congrArg v h2
    rw [map_mul, map_mul, map_mul, hvw, hnatv _ (Nat.succ_ne_zero e'), one_mul, one_mul] at h3
    rw [h3]
    gcongr
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hb w))
    rw [map_mul, hvw, one_mul]
    exact (hS s).trans hT
  have stepB : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ y : S, ϖ ∣ y → v (E (ι y)) ≤ c * T := by
    rintro T hT hb y ⟨z, rfl⟩
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; gcongr; exact hb z
    · rw [map_mul]
      exact (mul_le_of_le_one_left' (hS z)).trans (stepA T hT hb)
  have stepC : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ b : S, v (E (ι b)) ≤ max (c * T) 1 ∧
      (I ≤ Ideal.span {ϖ} → v (E (ι b)) ≤ c * T) := by
    intro T hT hb b
    have hP : Ideal.span {ϖ} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
    obtain ⟨G, hG1, hG2⟩ := exists_good_poly (R := R) hnat (Ideal.span {ϖ}) hP b
    rw [Ideal.mem_span_singleton] at hG1 hG2
    obtain ⟨s, hsI, hs⟩ := deriv_aeval (R := R) E I hI G b
    have hu := hone _ hG2
    have h1 : v (E (ι b)) = v (E (ι (Polynomial.aeval b G)) - ι s) := by
      have : E (ι (Polynomial.aeval b G)) - ι s =
          ι (Polynomial.aeval b (Polynomial.derivative G)) * E (ι b) := by rw [hs]; ring
      rw [this, map_mul, hu, one_mul]
    constructor
    · rw [h1]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · exact (stepB T hT hb _ hG1).trans (le_max_left _ _)
      · exact (hS s).trans (le_max_right _ _)
    · intro hIle
      rw [h1]
      refine (Valuation.map_sub _ _ _).trans (max_le (stepB T hT hb _ hG1) ?_)
      have := Ideal.mem_span_singleton.1 (hIle hsI)
      exact (hle_c s this).trans (le_mul_of_one_le_right' hT)

  have hbase : ∃ m : ℕ, ∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m := by
    obtain ⟨m, δ', hδ', hδm⟩ := WfDvdMonoid.max_power_factor' hδ hϖu
    refine ⟨m, fun x => ?_⟩
    obtain ⟨y, hy⟩ := hδE x
    have h1 := congrArg v hy
    rw [map_mul, hδm, map_mul, map_mul, map_pow, map_pow, hone _ hδ', mul_one] at h1
    have h2 : v (E (ι x)) = (c⁻¹) ^ m * v (ι y) := by
      rw [← h1, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hc0)]
    rw [h2]
    exact mul_le_of_le_one_right' (hS y)
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ (zero_lt_iff.2 hc0)).2 hc1.le
  have hdesc : ∀ m : ℕ, (∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m) → ∀ x : S, v (E (ι x)) ≤ 1 := by
    intro m
    induction m with
    | zero => simpa using id
    | succ m ih =>
      intro h
      apply ih
      intro x
      have h1 := (stepC _ (one_le_pow₀ hcinv) h x).1
      have h2 : c * (c⁻¹) ^ (m + 1) = (c⁻¹) ^ m := by
        rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      rw [h2] at h1
      exact h1.trans (max_le le_rfl (one_le_pow₀ hcinv))
  obtain ⟨m, hm⟩ := hbase
  have hb1 := hdesc m hm
  refine ⟨hb1, fun x hx => ?_, fun hIle x => ?_⟩
  · have := stepB 1 le_rfl hb1 x hx
    rw [mul_one] at this
    exact this.trans_lt hc1
  · have := (stepC 1 le_rfl hb1 x).2 hIle
    rw [mul_one] at this
    exact this.trans_lt hc1
end core

end GlobalTheory.CompanionTheory.TraceJac
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftOfSurjKer
section
namespace GlobalTheory.CompanionTheory.ColimLift

variable {G : ℕ → Type} [∀ n, CommRing (G n)] (f : ∀ n, G n →+* G (n + 1))
  {L : Type} [CommRing L] (ι : ∀ n, G n →+* L)
  (t : ∀ n k, G n → G (n + k))

theorem apply_iter {T : Type} (y : ∀ n, G n → T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n k : ℕ) (x : G n) :
    y (n + k) (t n k x) = y n x := by
  induction k with
  | zero => exact congrArg (y n) (t0 n x)
  | succ k ih =>
    have h : y (n + (k + 1)) (t n (k + 1) x) = y (n + k + 1) (f (n + k) (t n k x)) :=
      congrArg (y (n + k + 1)) (tS n k x)
    rw [h, hy, ih]

theorem eq_of_same_stage {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n : ℕ) (a b : G n) (h : ι n a = ι n b) :
    y n a = y n b := by
  obtain ⟨k, hk⟩ := ker n (a - b) (by rw [map_sub, h, sub_self])
  have h1 := apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k (a - b)
  simp only [hk, map_zero, map_sub] at h1
  exact sub_eq_zero.mp h1.symm

theorem eq_of_iota_eq {T : Type} [CommRing T] (y : ∀ n, G n →+* T)
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    (hy : ∀ n x, y (n + 1) (f n x) = y n x) (n m : ℕ) (a : G n) (b : G m)
    (h : ι n a = ι m b) : y n a = y m b := by
  have up : ∀ (n m : ℕ), n ≤ m → ∀ a : G n, ∃ a' : G m, ι m a' = ι n a ∧ y m a' = y n a := by
    intro n m hnm a
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact ⟨t n k a, apply_iter f t (fun n => (ι n : G n → L)) t0 tS hι n k a,
      apply_iter f t (fun n => (y n : G n → T)) t0 tS hy n k a⟩
  obtain ⟨a', ha, hya⟩ := up n (max n m) (le_max_left _ _) a
  obtain ⟨b', hb, hyb⟩ := up m (max n m) (le_max_right _ _) b
  rw [← hya, ← hyb]
  exact eq_of_same_stage f ι t y t0 tS ker hy _ a' b' (by rw [ha, hb, h])

theorem exists_lift_of_surj_ker
    (hι : ∀ n x, ι (n + 1) (f n x) = ι n x)
    (t0 : ∀ n x, t n 0 x = x) (tS : ∀ n k x, t n (k + 1) x = f (n + k) (t n k x))
    (surj : ∀ (m : ℕ) (v : Fin m → L), ∃ n, ∃ w : Fin m → G n, ∀ i, ι n (w i) = v i)
    (ker : ∀ n x, ι n x = 0 → ∃ k, t n k x = 0)
    {T : Type} [CommRing T] (y : ∀ n, G n →+* T) (hy : ∀ n x, y (n + 1) (f n x) = y n x) :
    ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  classical
  have key := eq_of_iota_eq f ι t y hι t0 tS ker hy
  have rep : ∀ l : L, ∃ n, ∃ a : G n, ι n a = l := fun l => by
    obtain ⟨n, w, hw⟩ := surj 1 (fun _ => l)
    exact ⟨n, w 0, hw 0⟩
  choose r s hs using rep
  let z : L → T := fun l => y (r l) (s l)
  have hz : ∀ n x, z (ι n x) = y n x := fun n x => key _ _ _ _ (hs _)
  have two : ∀ l₁ l₂ : L, ∃ n, ∃ a b : G n, ι n a = l₁ ∧ ι n b = l₂ := fun l₁ l₂ => by
    obtain ⟨n, w, hw⟩ := surj 2 ![l₁, l₂]
    exact ⟨n, w 0, w 1, hw 0, hw 1⟩
  refine ⟨{ toFun := z, map_one' := ?_, map_zero' := ?_, map_mul' := ?_, map_add' := ?_ }, hz⟩
  · have := hz 0 1
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_mul, hz, hz, hz, map_mul]
  · have := hz 0 0
    simpa using this
  · intro l₁ l₂
    obtain ⟨n, a, b, rfl, rfl⟩ := two l₁ l₂
    rw [← map_add (f := _), hz, hz, hz, map_add (f := _)]

end GlobalTheory.CompanionTheory.ColimLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitian
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.HermitianCommuting

theorem exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  let S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    {a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}
  have hS : S.Nonempty := by
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · intro A hA
      rw [Submodule.mem_bot] at hA
      simp [hA]
    · intro A hA B hB
      rw [Submodule.mem_bot] at hA hB
      simp [hA, hB]
  obtain ⟨a, ha, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩
  intro Y hY hYh hYc
  have hmem : a ⊔ Submodule.span ℝ {Y} ∈ S := by
    refine ⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]
      simp
    · intro A hA B hB
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hB
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have h1 := ha.2.2 x hx x' hx'
      have h2 := hYc x hx
      have h3 := hYc x' hx'
      simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]
      rw [mul_comm d c]
      abel
  have hne : a ⊔ Submodule.span ℝ {Y} = a := by
    by_contra h
    exact hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))
  have hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)
  rwa [hne] at hYmem

end GlobalTheory.CompanionTheory.HermitianCommuting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactLatticeContaining
section
open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalLattice

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSubgroup (k : Type) [Field k] [ValuativeRel k] (n : ℕ) (γ : ValueGroupWithZero k) :
    AddSubgroup (Fin n → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ γ}
  zero_mem' := fun i => by simp
  add_mem' := fun {a b} ha hb i =>
    (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  neg_mem' := fun {a} ha i => by simpa using ha i

theorem coe_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    (ballSubgroup k n γ : Set (Fin n → k)) =
      Set.univ.pi fun _ => {x : k | valuation k x ≤ γ} := by
  ext x
  simp only [Set.mem_univ_pi, Set.mem_setOf_eq]
  rfl

theorem isCompact_ballSubgroup (n : ℕ) (γ : ValueGroupWithZero k) :
    IsCompact (ballSubgroup k n γ : Set (Fin n → k)) := by
  rw [coe_ballSubgroup]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ

theorem isOpen_ballSubgroup (n : ℕ) {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    IsOpen (ballSubgroup k n γ : Set (Fin n → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds (g := 0) _ ?_
  rw [GlobalTheory.CompanionTheory.LocalLattice.coe_ballSubgroup]
  refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2
    ⟨Units.mk0 γ hγ, fun x (hx : valuation k x < γ) => hx.le⟩

theorem exists_compact_open_addSubgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)) (hK : IsCompact K) :
    ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
      IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by
  have hne : ∀ γ : ValueGroupWithZero k, max γ 1 ≠ 0 :=
    fun γ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right γ 1))
  have hmono : Monotone fun γ : ValueGroupWithZero k =>
      (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) :=
    fun γ δ hγδ x hx i => (hx i).trans (max_le_max hγδ le_rfl)
  have hcover : K ⊆ ⋃ γ : ValueGroupWithZero k, (GlobalTheory.CompanionTheory.LocalLattice.ballSubgroup k n (max γ 1) : Set (Fin n → k)) := by
    intro x _
    obtain ⟨γ, hγ⟩ := Finite.exists_le fun i => valuation k (x i)
    exact Set.mem_iUnion.2 ⟨γ, fun i => (hγ i).trans (le_max_left γ 1)⟩
  obtain ⟨γ, hγ⟩ := hK.elim_directed_cover _
    (fun γ => GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ)) hcover hmono.directed_le
  exact ⟨_, GlobalTheory.CompanionTheory.LocalLattice.isCompact_ballSubgroup n _, GlobalTheory.CompanionTheory.LocalLattice.isOpen_ballSubgroup n (hne γ), hγ⟩

end GlobalTheory.CompanionTheory.LocalLattice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPerfectRadical
section
namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_perfect_radical (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S)
    (hp : (p : S) = 0) :
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), (p : T) = 0 ∧
      Function.Bijective (fun t : T => t ^ p) ∧
      (∀ t : T, ∃ (k : ℕ) (x : S), t ^ p ^ k = i x) ∧
      ∀ x : S, i x = 0 ↔ x ∈ I.radical := by
  by_cases htop : I.radical = ⊤
  · haveI : Subsingleton (S ⧸ I.radical) := Ideal.Quotient.subsingleton_iff.mpr htop
    refine ⟨S ⧸ I.radical, inferInstance, Ideal.Quotient.mk I.radical, Subsingleton.elim _ _,
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩, fun t => ?_,
      fun x => Ideal.Quotient.eq_zero_iff_mem⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨0, x, by simp⟩
  · haveI : Nontrivial (S ⧸ I.radical) := Ideal.Quotient.nontrivial_iff.mpr htop
    have hpQ : ((p : ℕ) : S ⧸ I.radical) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I.radical), hp, map_zero]
    haveI : CharP (S ⧸ I.radical) p := by
      first
        | exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpQ
        | exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpQ)
    haveI : ExpChar (S ⧸ I.radical) p := ExpChar.prime (Fact.out : p.Prime)
    haveI : IsReduced (S ⧸ I.radical) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical I)
    refine ⟨PerfectClosure (S ⧸ I.radical) p, inferInstance,
      (PerfectClosure.of (S ⧸ I.radical) p).comp (Ideal.Quotient.mk I.radical), ?_, ?_, ?_, ?_⟩
    · exact CharP.cast_eq_zero _ p
    · first
        | exact PerfectRing.bijective_frobenius (R := PerfectClosure (S ⧸ I.radical) p) (p := p)
        | (convert PerfectRing.bijective_frobenius (R := PerfectClosure (S ⧸ I.radical) p) (p := p) using 1
           funext t
           exact (frobenius_def _ _ t).symm)
    · intro t
      obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) t
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨n, x, hy.symm⟩
    · intro x
      constructor
      · intro h
        have hk : Ideal.Quotient.mk I.radical x ∈ RingHom.ker (PerfectClosure.of (S ⧸ I.radical) p) := h
        obtain ⟨n, hn⟩ := mem_pNilradical.mp
          (IsPRadical.ker_le (i := PerfectClosure.of (S ⧸ I.radical) p) (p := p) hk)
        exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, hn⟩)
      · intro h
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

end GlobalTheory.CompanionTheory.PerfClos
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupAddSubgroup
section
open Matrix
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Topology

theorem isCompact_addSubgroup_sup : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB

end GlobalTheory.CompanionTheory.Topology
end

