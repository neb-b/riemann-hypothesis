module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorHasSumAdicCompleteFrobenius
section
open Polynomial

namespace GlobalTheory

theorem abssum_eigen_lim : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  intro l _ A _ _ φ h w hw
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(l : A)} ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  let S : ℕ → A := fun N => ∑ k ∈ Finset.range N, (l : A) ^ k * w k
  have hS : ∀ m n, m ≤ n → (l : A) ^ m ∣ S n - S m := by
    intro m n hmn
    simp only [S]
    rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro k hk
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _
  obtain ⟨W, hW⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) (M := A) inferInstance (f := S)
    (fun {m n} hmn => by rw [SModEq.sub_mem, key]; exact dvd_sub_comm.1 (hS m n hmn))
  have hWN : ∀ N, ∃ c : A, W = S N + (l : A) ^ N * c := by
    intro N
    have h1 := SModEq.sub_mem.1 (hW N)
    rw [key] at h1
    obtain ⟨c, hc⟩ := dvd_sub_comm.1 h1
    exact ⟨c, by rw [← hc]; ring⟩
  simp only [← RingHom.coe_pow] at hw ⊢
  have hSψ : ∀ N, (φ ^ h) (S N) = (l : A) * S N := by
    intro N
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S, map_sum, map_mul, map_pow, map_natCast, hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨W, ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    obtain ⟨c, hc⟩ := hWN n
    rw [hc, map_add (f := _), map_mul, map_pow, map_natCast, hSψ]
    exact ⟨(φ ^ h) c - (l : A) * c, by ring⟩
  · intro Θ hΘ
    have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
      rw [show (l : ℂ_[l]) = (((l : ℚ_[l])) : ℂ_[l]) by simp, PadicComplex.norm_extends', Padic.norm_p]
    have hlt : ‖(l : ℂ_[l])‖ < 1 := by
      rw [hl]
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Fact.out : l.Prime).one_lt
    have hbound : ∀ k, ‖(l : ℂ_[l]) ^ k * Θ (w k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hΘ _)
    have hsum : Summable (fun k => (l : ℂ_[l]) ^ k * Θ (w k)) :=
      Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hlt) hbound
    rw [hsum.hasSum_iff_tendsto_nat]
    have hpart : ∀ N, ∑ i ∈ Finset.range N, (l : ℂ_[l]) ^ i * Θ (w i) = Θ (S N) := by
      intro N
      set_option synthInstance.maxHeartbeats 100000 in
        simp [S, map_sum, map_mul, map_pow, map_natCast]
    simp only [hpart]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt)
    obtain ⟨c, hc⟩ := hWN N
    rw [hc, map_add (f := _), sub_add_cancel_left, norm_neg, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hΘ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingIdempotentTensor
section
open TensorProduct

namespace GlobalTheory


open TensorProduct in
theorem _root_.GlobalTheory.exists_embedding_idempotent_tensor (F K L : Type) [Field F] [CharZero F] [Field K]
    [Field L] [Algebra F K] [Algebra F L] [FiniteDimensional F K] (τ : K →ₐ[F] L) :
    ∃ (m : ℕ) (c : Fin m → L) (k : Fin m → K), ∑ j, c j * τ (k j) = 1 ∧
      ∀ y : K, ∑ j, c j ⊗ₜ[F] (y * k j) = ∑ j, (τ y * c j) ⊗ₜ[F] k j := by
  classical
  have hB : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  have hsymm : (Algebra.traceForm F K).IsSymm := Algebra.traceForm_isSymm F
  let b := Module.finBasis F K
  let d := (Algebra.traceForm F K).dualBasis hB b
  have hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j
  set s : K := ∑ j, b j * d j with hs
  have hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x := by
    intro x
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hbd]
  have hs0 : s ≠ 0 := by
    intro h
    have htr : Algebra.trace F K s = (Module.finrank F K : F) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, map_sum]
      simp [hbd]
    rw [h, map_zero] at htr
    exact (Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp htr.symm)
  refine ⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩
  · calc ∑ j, τ (s⁻¹ * b j) * τ (d j) = τ (s⁻¹ * s) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]
      _ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]
  · have lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) =
        ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← hd (y * d j)]
      rw [TensorProduct.tmul_sum]
      simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i =
        ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, mul_left_comm]
      conv_lhs => rw [← hb (y * b i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.mul_sum, map_sum, TensorProduct.sum_tmul]
      simp_rw [mul_smul_comm, map_smul]
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_right_comm y (d j) (b i)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqPowMulUnit
section
namespace GlobalTheory.PowMulUnit

theorem exists_eq_pow_mul_unit {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ (0 : S)) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hex : ∃ n : ℕ, ¬ (π ^ n ∣ x) := by
    by_contra h0
    have h : ∀ n : ℕ, π ^ n ∣ x := fun n => not_not.mp (not_exists.mp h0 n)
    apply hx
    have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n := by
      refine Ideal.mem_iInf.mpr fun n => ?_
      rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [hK] at hmem
    exact hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero] at h1
    exact h1 (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdk : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨u, rfl⟩ := hdk
  refine ⟨k, u, ?_, rfl⟩
  by_contra hu
  have hum : u ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal u).mpr hu
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨w, rfl⟩ := hum
  apply Nat.find_spec hex
  rw [hk, pow_succ]
  exact ⟨w, by ring⟩

end GlobalTheory.PowMulUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeight
section
open scoped BigOperators

namespace GlobalTheory


open scoped BigOperators in
theorem _root_.GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  intro ρ S hS
  have hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y)) :=
    Pi.Lex.wellFounded _
  refine ⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩
  set m := hwf.min S hS with hm
  intro c hc a ha hne
  have hnl := hwf.not_lt_min S ha
  have hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hi]⟩
  set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef
  have hk : a k ≠ m k := (Finset.mem_filter.1 (Finset.max'_mem _ hd)).2
  have hgt : ∀ j, k < j → a j = m j := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  have hlt : m k < a k := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl
    · exact h
  have key : ∀ i, m i * c i + (if i = k then c k else 0) ≤
      a i * c i + (if i < k then m i * c i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne]
    · subst h
      simp only [if_true, lt_irrefl, if_false, add_zero]
      nlinarith
    · simp [h.ne', not_lt.2 h.le, hgt i h]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k := by ext; simp
  rw [hI] at hsum
  have := hc k
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtendCharacterTrivialOnNormal
section
namespace GlobalTheory

private lemma char_eq_of_same_coset {G M : Type} [Group G] [CommGroup M]
    (Ik H : Subgroup G) (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1)
    (g s t : G) (hs : s ∈ Ik) (ht : t ∈ Ik) (h1 : s⁻¹ * g ∈ H) (h2 : t⁻¹ * g ∈ H) :
    ψ ⟨s, hs⟩ = ψ ⟨t, ht⟩ := by
  have hmem : ((⟨s, hs⟩⁻¹ * ⟨t, ht⟩ : ↥Ik) : G) ∈ H := by
    have h3 : s⁻¹ * t = (s⁻¹ * g) * (t⁻¹ * g)⁻¹ := by group
    have h5 : s⁻¹ * t ∈ H := by
      rw [h3]
      exact H.mul_mem h1 (H.inv_mem h2)
    exact h5
  have h4 := hψ _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

theorem exists_extend_character_trivial_on_normal {G M : Type} [Group G] [CommGroup M]
    (I Ik H : Subgroup G) (hH : H.Normal) (hdec : ∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H)
    (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1) :
    ∃ χ : ↥I →* M, ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → χ g = ψ ⟨s, hs⟩ := by
  classical
  choose f hfIk hfH using hdec
  have key := char_eq_of_same_coset Ik H ψ hψ
  refine ⟨{ toFun := fun g => ψ ⟨f g g.2, hfIk g g.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ψ ⟨f _ _, _⟩ = 1
    rw [key _ _ 1 _ Ik.one_mem (hfH _ _) (by simp)]
    exact map_one ψ
  · intro a b
    show ψ ⟨f _ _, _⟩ = ψ ⟨f _ _, _⟩ * ψ ⟨f _ _, _⟩
    have hab : (f a a.2 * f b b.2)⁻¹ * ((a * b : ↥I) : G) ∈ H := by
      show (f a a.2 * f b b.2)⁻¹ * ((a : G) * b) ∈ H
      have hc := hH.conj_mem _ (hfH a a.2) (f b b.2)⁻¹
      have he : (f a a.2 * f b b.2)⁻¹ * ((a : G) * b)
          = ((f b b.2)⁻¹ * ((f a a.2)⁻¹ * a) * (f b b.2)⁻¹⁻¹) * ((f b b.2)⁻¹ * b) := by group
      rw [he]
      exact H.mul_mem hc (hfH b b.2)
    rw [key ((a * b : ↥I) : G) _ (f a a.2 * f b b.2) _ (Ik.mul_mem (hfIk a a.2) (hfIk b b.2))
      (hfH _ _) hab]
    exact map_mul ψ ⟨f a a.2, hfIk a a.2⟩ ⟨f b b.2, hfIk b b.2⟩
  · intro g s hs hsg
    exact key g _ s _ hs (hfH g g.2) hsg

theorem extend_characters_and_generator : ∀ {G F LL : Type} [Group G] [Field F] [Field LL] (I Ik H : Subgroup G), H.Normal → Ik ≤ I → (∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H) → ∀ (n : ℕ), 0 < n → ∀ (Ψ : ↥(rootsOfUnity n F) →* (↥Ik →* LLˣ)) (Y : Set F), (∀ y ∈ Y, ∃ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y) → (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1) → ∃ ch : F → (↥I →* LLˣ), (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → ch ((u : Fˣ) : F) g = Ψ u ⟨s, hs⟩) ∧ ∃ c : ↥I →* LLˣ, (∀ g, c g ^ n = 1) ∧ ∀ y ∈ Y, ∃ k : ℕ, ∀ g, ch y g = c g ^ k := by
  intro G F LL _ _ _ I Ik H hH _ hdec n hn Ψ Y hY hΨ
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let K : Subgroup ↥(rootsOfUnity n F) :=
    { carrier := {u | ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1}
      mul_mem' := fun {a b} ha hb s hs => by
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [map_mul, MonoidHom.mul_apply, ha s hs, hb s hs, mul_one]
      one_mem' := fun s _ => by rw [map_one, MonoidHom.one_apply]
      inv_mem' := fun {a} ha s hs => by
        simp only [Set.mem_ofPred_eq] at ha
        rw [map_inv, MonoidHom.inv_apply, ha s hs, inv_one] }
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := ↥K)
  obtain ⟨c, hc⟩ := exists_extend_character_trivial_on_normal I Ik H hH hdec
    (Ψ (ζ : ↥(rootsOfUnity n F))) (fun s hs => ζ.2 s hs)
  have hk : ∀ y ∈ Y, ∃ k : ℕ, ∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y →
      (ζ : ↥(rootsOfUnity n F)) ^ k = u := by
    intro y hy
    obtain ⟨u₀, hu₀⟩ := hY y hy
    have hK : u₀ ∈ K := hΨ u₀ (hu₀ ▸ hy)
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := ζ) (y := ⟨u₀, hK⟩)).mpr (hζ _)
    refine ⟨k, fun u hu => ?_⟩
    have hu' : u = u₀ := Subtype.ext (Units.ext (hu.trans hu₀.symm))
    rw [hu']
    have := congrArg (fun v : ↥K => (v : ↥(rootsOfUnity n F))) hk
    simpa using this
  choose! kk hkk using hk
  have hpow : (ζ : ↥(rootsOfUnity n F)) ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity n _).mp (ζ : ↥(rootsOfUnity n F)).2
  refine ⟨fun y => c ^ kk y, ?_, c, ?_, ?_⟩
  · intro u hu g s hs hsg
    show (c ^ kk ((u : Fˣ) : F)) g = Ψ u ⟨s, hs⟩
    rw [MonoidHom.pow_apply, hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow,
      hkk _ hu u rfl]
  · intro g
    obtain ⟨s, hs, hsg⟩ := hdec g g.2
    rw [hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow, hpow, map_one, MonoidHom.one_apply]
  · intro y _
    exact ⟨kk y, fun g => MonoidHom.pow_apply c (kk y) g⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGaloisContainsRootsOfUnits
section
open NumberField Polynomial

namespace GlobalTheory.KummerUnits

theorem exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  intro E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨S, hS⟩ := Monoid.exists_of_isMulFG (𝓞 E)ˣ
  let c : (𝓞 E)ˣ → F := fun u => algebraMap E F ((u : 𝓞 E) : E)
  let p : F[X] := ∏ s ∈ S, (X ^ M - C (c s))
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _
  let L := IntermediateField.adjoin F (p.rootSet Ω)
  have hsp : p.IsSplittingField F L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI := Polynomial.IsSplittingField.finiteDimensional L p
  haveI := Normal.of_isSplittingField (F := F) (E := L) p
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  have hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (L.algebraMap_mem ζ) i
  let φ : (𝓞 E)ˣ →* Ω :=
    ((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)
  have hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E) := fun u => rfl
  have hφc : ∀ u, φ u = algebraMap F Ω (c u) := fun u => IsScalarTower.algebraMap_apply E F Ω _
  have hφ0 : ∀ u, φ u ≠ 0 := fun u => ((Group.isUnit u).map φ).ne_zero
  intro u
  simp only [← hφ]
  have hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ) := by rw [hS]; trivial
  induction hall using Submonoid.closure_induction with
  | mem s hs =>
    intro w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    simp only [p, map_prod]
    refine Finset.prod_eq_zero hs ?_
    simp [hw, hφc]
  | one =>
    intro w hw
    exact hroot w (by rw [hw, map_one])
  | mul a b _ _ ha hb =>
    intro w hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (φ a) hM
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (φ b) hM
    have hxy : x * y ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])
      · rintro rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])
    rw [← div_mul_cancel₀ w hxy]
    refine mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))
    rw [div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]

end GlobalTheory.KummerUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquiv
section
open NumberField IsDedekindDomain

namespace GlobalTheory.PlaceTransport

theorem eq_of_forall_le_exp_neg {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  have key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ)) := fun n => by
    simpa only [WithZero.exp_le_exp] using h n
  have hkm : k ≤ m := by
    have := (key (-m).toNat).1 (by omega)
    omega
  have hmk : m ≤ k := by
    have := (key (-k).toNat).2 (by omega)
    omega
  rw [le_antisymm hmk hkm]

theorem intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl

theorem exists_place_valuation_comp_equiv :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
      (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K),
        ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  intro K L _ _ _ _ e la
  set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  refine ⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c) := fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]

end GlobalTheory.PlaceTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeightOneMem
section
namespace GlobalTheory.HeightOnePrimeMembership

open NumberField

theorem exists_heightOne_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers E),
      (p : RingOfIntegers E) ∈ w.asIdeal := by
  have hnu : ¬ IsUnit (p : RingOfIntegers E) := by
    intro hu
    have h1 : IsUnit (Algebra.norm ℤ (p : RingOfIntegers E)) := hu.map _
    have h2 : (p : RingOfIntegers E) = algebraMap ℤ (RingOfIntegers E) (p : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have hpos : Module.finrank ℤ (RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (p : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h3
  have hne : Ideal.span {(p : RingOfIntegers E)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (p : RingOfIntegers E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hp0 : (p : RingOfIntegers E) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro hb
  rw [hb] at hmem
  exact hp0 (by simpa using hmem)

end GlobalTheory.HeightOnePrimeMembership
end

