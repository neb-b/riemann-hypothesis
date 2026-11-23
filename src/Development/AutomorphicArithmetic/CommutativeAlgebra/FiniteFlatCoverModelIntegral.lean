module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.UPel.HT.EtLev

private theorem eq_zero_or_of_mul_eq_zero_of_add_reg {A : Type} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    {a b : A} (hab : a * b = 0) (hreg : a + b ∈ nonZeroDivisors A) : a = 0 ∨ b = 0 := by
  let F := FractionRing A
  have hinj : Function.Injective (algebraMap A F) := IsLocalization.injective F le_rfl
  let e : F := IsLocalization.mk' F a (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have hu : IsUnit (algebraMap A F (a + b)) := IsLocalization.map_units F (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have he : e * algebraMap A F (a + b) = algebraMap A F a := IsLocalization.mk'_spec F a ⟨a + b, hreg⟩
  have hidem : e * e = e := by
    apply hu.mul_right_cancel
    apply hu.mul_right_cancel
    have h2 : algebraMap A F a * algebraMap A F (a + b) = algebraMap A F a * algebraMap A F a := by
      rw [← map_mul, ← map_mul, mul_add, hab, add_zero]
    calc e * e * algebraMap A F (a + b) * algebraMap A F (a + b)
        = (e * algebraMap A F (a + b)) * (e * algebraMap A F (a + b)) := by ring
      _ = algebraMap A F a * algebraMap A F a := by rw [he]
      _ = algebraMap A F a * algebraMap A F (a + b) := h2.symm
      _ = e * algebraMap A F (a + b) * algebraMap A F (a + b) := by rw [he]
  have hint : IsIntegral A e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by simp)
    · simp [Polynomial.eval₂_sub, pow_two, hidem]
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hint
  have hcc : c * c = c := hinj (by rw [map_mul, hc, hidem])
  have hca : c * (a + b) = a := hinj (by rw [map_mul, hc, he])
  have h01 : c = 0 ∨ c = 1 := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · right
      exact h.mul_left_cancel (by rw [hcc, _root_.mul_one])
    · left
      have : (1 - c) * c = 0 := by rw [sub_mul, _root_.one_mul, hcc, sub_self]
      exact h.mul_right_eq_zero.1 this
  rcases h01 with rfl | rfl
  · left
    simpa using hca.symm
  · right
    simpa using hca

private theorem isDomain_of_isReduced_of_isIntegrallyClosed (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A] [IsIntegrallyClosed A] : IsDomain A := by
  classical
  by_contra hdom
  have hbot : ¬ (⊥ : Ideal A).IsPrime := fun h => hdom (IsDomain.of_bot_isPrime A)
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hzero : ∀ x : A, (∀ Q ∈ minimalPrimes A, x ∈ Q) → x = 0 := fun x hx => by
    have : x ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      exact (Submodule.mem_sInf).2 hx
    obtain ⟨n, hn⟩ := this
    exact (IsNilpotent.eq_zero ⟨n, by simpa using hn⟩)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
  have hPp : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hprime : ∀ Q ∈ minimalPrimes A, Q.IsPrime := fun Q hQ => Ideal.minimalPrimes_isPrime hQ
  have hle : ∀ Q ∈ minimalPrimes A, ∀ Q' ∈ minimalPrimes A, Q ≤ Q' → Q = Q' := fun Q hQ Q' hQ' h =>
    le_antisymm h (hQ'.2 hQ.1 h)
  let T : Finset (Ideal A) := hfin.toFinset.erase P
  have hT : ∀ Q ∈ T, Q ∈ minimalPrimes A ∧ Q ≠ P := fun Q hQ => by
    have := Finset.mem_erase.1 hQ
    exact ⟨hfin.mem_toFinset.1 this.2, this.1⟩
  have hTm : ∀ Q ∈ minimalPrimes A, Q ≠ P → Q ∈ T := fun Q hQ h =>
    Finset.mem_erase.2 ⟨h, hfin.mem_toFinset.2 hQ⟩

  obtain ⟨a, haP, ha⟩ : ∃ a ∈ P, a ∉ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), (i : Set A) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (P : Set A) ⊆ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), ((id i : Ideal A) : Set A) := hcon
    obtain ⟨Q, hQ, hPQ⟩ := (Ideal.subset_union_prime (⊥ : Ideal A) (⊥ : Ideal A)
      (fun i hi h1 _ => (hT i ((Finset.mem_insert.1 hi).resolve_left h1)).1 |> hprime i)).1 hsub
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact hbot ((le_bot_iff.1 hPQ) ▸ hPp)
    · exact (hT Q hQ).2 (hle P hP Q (hT Q hQ).1 hPQ).symm
  have ha0 : a ≠ 0 := fun h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨⊥, by simp, by simp [h]⟩)
  have haT : ∀ Q ∈ T, a ∉ Q := fun Q hQ h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨Q, by simp [hQ], h⟩)

  obtain ⟨b, hbT, hbP⟩ : ∃ b ∈ T.inf id, b ∉ P := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.inf_le' hPp).1 (show T.inf id ≤ P from hcon)
    exact (hT Q hQ).2 (hle Q (hT Q hQ).1 P hP hQP)
  have hbT' : ∀ Q ∈ T, b ∈ Q := fun Q hQ => by
    have := Finset.inf_le (f := id) hQ
    exact this hbT
  have hab : a * b = 0 := hzero _ fun Q hQ => by
    by_cases h : Q = P
    · exact h ▸ Ideal.mul_mem_right _ _ haP
    · exact Ideal.mul_mem_left _ _ (hbT' Q (hTm Q hQ h))
  have hreg : a + b ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hzero x fun Q hQ => ?_
    have hQp := hprime Q hQ
    have hx' : x * (a + b) ∈ Q := hx ▸ Q.zero_mem
    refine (hQp.mem_or_mem hx').resolve_right fun hs => ?_
    by_cases h : Q = P
    · subst h
      exact hbP ((Q.add_mem_iff_right haP).1 hs)
    · have hm := hTm Q hQ h
      exact haT Q hm ((Q.add_mem_iff_left (hbT' Q hm)).1 hs)
  rcases eq_zero_or_of_mul_eq_zero_of_add_reg hab hreg with h | h
  · exact ha0 h
  · exact hbP (h ▸ P.zero_mem)
