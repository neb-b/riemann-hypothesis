module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0003
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.Filtration

@[expose] public section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def cont (ϖ : O) (g f : O⟦X⟧) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ k, g}), (k : ℕ∞)

theorem Cont.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  have hb : b ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ a := by
    have h2 := (ENat.add_one_le_iff hb).2 hlt
    exact_mod_cast h2
  have h2 := h (n + 1) h1
  norm_cast at h2
  omega

theorem Cont.mem_pair_mono (ϖ : O) (g f : O⟦X⟧) {j k : ℕ} (hjk : j ≤ k)
    (h : f ∈ Ideal.span {C ϖ ^ k, g}) : f ∈ Ideal.span {C ϖ ^ j, g} := by
  refine (Ideal.span_le.2 ?_) h
  intro x hx
  rcases hx with rfl | rfl
  · have e : C ϖ ^ k = C ϖ ^ j * C ϖ ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)

theorem Cont.mem_zero (ϖ : O) (g f : O⟦X⟧) : f ∈ Ideal.span {C ϖ ^ 0, g} := by
  have h1 : (1 : O⟦X⟧) ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
  simpa using Ideal.mul_mem_left _ f h1

theorem Cont.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  unfold cont
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro hk
    by_contra hnot
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hnot (Cont.mem_zero ϖ g f)
    have hbound : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hj' : j ≤ k - 1 := by
        by_contra hjk
        push_neg at hjk
        exact hnot (Cont.mem_pair_mono ϖ g f (by omega) hj)
      exact_mod_cast hj'
    have h3 := le_trans hk hbound
    norm_cast at h3
    omega

theorem Cont.residue_unif {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit

theorem Cont.C_unif_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

theorem Cont.C_dvd_of_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧)
    (hf : f.map (IsLocalRing.residue O) = 0) : C ϖ ∣ f := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hc : ∀ n, ∃ c, PowerSeries.coeff n f = ϖ * c := by
    intro n
    have h1 : IsLocalRing.residue O (PowerSeries.coeff n f) = 0 := by
      have h2 := congrArg (PowerSeries.coeff n) hf
      simpa [PowerSeries.coeff_map] using h2
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

theorem Cont.prime_C_unif {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨Cont.C_unif_ne_zero hϖ, ?_, ?_⟩
  · intro hu
    have h1 := hu.map (PowerSeries.constantCoeff (R := O))
    rw [PowerSeries.constantCoeff_C] at h1
    exact hϖ.not_isUnit h1
  · intro f g hfg
    have hmap : (f * g).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨h, hh⟩ := hfg
      rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]
    rw [map_mul] at hmap
    rcases mul_eq_zero.1 hmap with h | h
    · exact Or.inl (Cont.C_dvd_of_map_eq_zero hϖ f h)
    · exact Or.inr (Cont.C_dvd_of_map_eq_zero hϖ g h)

theorem Cont.not_C_dvd {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) : ¬ (C ϖ ∣ g) := by
  rintro ⟨h, hh⟩
  apply hg
  rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]

theorem Cont.mem_of_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) (n : ℕ)
    (h : O⟦X⟧) (hm : C ϖ ^ n * h ∈ Ideal.span {g}) : h ∈ Ideal.span {g} := by
  induction n generalizing h with
  | zero => simpa using hm
  | succ n ih =>
    apply ih
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hm
    have hdvd : C ϖ ∣ q * g := ⟨C ϖ ^ n * h, by rw [hq, pow_succ]; ring⟩
    rcases (Cont.prime_C_unif hϖ).2.2 q g hdvd with ⟨q', rfl⟩ | hg'
    · rw [Ideal.mem_span_singleton']
      refine ⟨q', ?_⟩
      have h1 : C ϖ * (q' * g) = C ϖ * (C ϖ ^ n * h) := by
        calc C ϖ * (q' * g) = C ϖ * q' * g := by ring
          _ = C ϖ ^ (n + 1) * h := hq
          _ = C ϖ * (C ϖ ^ n * h) := by ring
      exact mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) h1
    · exact absurd hg' (Cont.not_C_dvd hϖ hg)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem C2' {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    (∃ (a : O⟦X⟧) (n : ℕ), C ϖ ^ n * (f - C ϖ ^ k * a) ∈ Ideal.span {g}) ↔
      f ∈ Ideal.span {C ϖ ^ k, g} := by
  constructor
  · rintro ⟨a, n, h⟩
    have h1 := Cont.mem_of_pow_mul_mem hϖ hg n _ h
    have h2 : f = C ϖ ^ k * a + (f - C ϖ ^ k * a) := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.span_mono (Set.subset_insert _ _) h1)
  · intro hf
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hf
    refine ⟨u, 0, ?_⟩
    rw [pow_zero, one_mul, ← huv, Ideal.mem_span_singleton']
    exact ⟨v, by ring⟩

theorem mem_iff_le_cont {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  exact Cont.mem_iff_le ϖ g f k

theorem m1 {g g' : O⟦X⟧} (hg : IsDist g) (hg' : IsDist g') (hdvd : g ∣ g') (f : O⟦X⟧) :
    cont ϖ g' f ≤ cont ϖ g f := by
  apply Cont.enat_le_of_forall
  intro k hk
  have h1 := (Cont.mem_iff_le ϖ g' f k).2 hk
  apply (Cont.mem_iff_le ϖ g f k).1
  refine (Ideal.span_le.2 ?_) h1
  intro x hx
  rcases hx with rfl | rfl
  · exact Ideal.subset_span (by simp)
  · obtain ⟨c, rfl⟩ := hdvd
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem m2 {g : O⟦X⟧} (hg : IsDist g) (k f : O⟦X⟧) : cont ϖ g f ≤ cont ϖ g (k * f) := by
  apply Cont.enat_le_of_forall
  intro j hj
  exact (Cont.mem_iff_le ϖ g _ j).1 (Ideal.mul_mem_left _ k ((Cont.mem_iff_le ϖ g f j).2 hj))


end Formalism.MainNotions.N.FrobeniusPowerSeries
