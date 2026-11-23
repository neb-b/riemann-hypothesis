module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0005
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial
open scoped Pointwise

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

private theorem isMultiHomog_mul_birational_geometry {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomogIdeal_mul {I I' : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I)
    (hI' : IsMultiHomogIdeal I') : IsMultiHomogIdeal (I * I') := by
  obtain ⟨S, hS, rfl⟩ := hI
  obtain ⟨S', hS', rfl⟩ := hI'
  refine ⟨S * S', ?_, Ideal.span_mul_span' S S'⟩
  rintro f ⟨x, hx, y, hy, rfl⟩
  obtain ⟨a, ha⟩ := hS x hx
  obtain ⟨b, hb⟩ := hS' y hy
  exact ⟨a + b, isMultiHomog_mul_birational_geometry ha hb⟩

private theorem isMultiHomog_finset_prod' {β : Type} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ m hm k
    rw [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm hne)] at hm
      exact hm rfl
    subst hm0
    simp
  · intro x s hx ih h
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact isMultiHomog_mul_birational_geometry (h x (Finset.mem_insert_self x s))
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

private theorem isMultiHomog_finset_sum {β : Type} (s : Finset β) (f : β → MRing ι) (a : K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
  classical
  intro m hm k
  obtain ⟨x, hx, hm'⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h x hx m hm' k

private theorem isMultiHomog_zsmul (c : ℤ) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (c • f) a := fun m hm k => h m (MvPolynomial.support_smul hm) k

private theorem isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero [DecidableEq K] (v : Σ k, ι k) {p : MRing ι} {d : K → ℕ}
    (h : IsMultiHomog p d) :
    IsMultiHomog (MvPolynomial.pderiv v p) (fun k => d k - if k = v.1 then 1 else 0) ∧
      (MvPolynomial.pderiv v p ≠ 0 → 1 ≤ d v.1) := by
  classical
  have key : ∀ m, m ∈ (MvPolynomial.pderiv v p).support → ∀ k, ∑ i, m ⟨k, i⟩ + (if k = v.1 then 1 else 0) = d k := by
    intro m hm k
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hm' : m + Finsupp.single v 1 ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      exact hm (by rw [h0, zero_mul])
    rw [← h _ hm' k]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    congr 1
    obtain ⟨k0, i0⟩ := v
    by_cases hk : k = k0
    · subst hk
      simp [Finsupp.single_apply, Sigma.mk.inj_iff]
    · simp [Finsupp.single_apply, Sigma.mk.inj_iff, Ne.symm hk, hk]
  refine ⟨fun m hm k => ?_, fun hne => ?_⟩
  · have := key m hm k
    beta_reduce
    omega
  · obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
    have := key m (MvPolynomial.mem_support_iff.mpr hm) v.1
    rw [if_pos rfl] at this
    omega

theorem isMultiHomog_det_pderiv {s c : ℕ} (G : Fin s → MRing ι) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
    (a : Fin c → Fin s) (b : Fin c → Σ k, ι k) :
    ∃ d, IsMultiHomog (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv (b j) (G (a i)))) d := by
  classical
  choose d hd using hG
  refine ⟨fun k => (∑ i, d (a i) k) - ∑ j, (if k = (b j).1 then 1 else 0), ?_⟩
  rw [Matrix.det_apply]
  refine isMultiHomog_finset_sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine isMultiHomog_zsmul _ ?_
  simp only [Matrix.of_apply]
  by_cases h0 : ∃ i, MvPolynomial.pderiv (b i) (G (a (σ i))) = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    intro m hm
    simp at hm
  · push_neg at h0
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin c)), ∀ k,
        (if k = (b i).1 then 1 else 0) ≤ d (a (σ i)) k := by
      intro i _ k
      split_ifs with hk
      · subst hk
        exact (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).2 (h0 i)
      · exact Nat.zero_le _
    have hp := isMultiHomog_finset_prod' Finset.univ (fun i => MvPolynomial.pderiv (b i) (G (a (σ i))))
      (fun i k => d (a (σ i)) k - if k = (b i).1 then 1 else 0)
      (fun i _ => (isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (b i) (hd (a (σ i)))).1)
    convert hp using 1
    funext k
    rw [Finset.sum_apply, Finset.sum_tsub_distrib _ (fun i hi => hle i hi k)]
    congr 1
    exact (Equiv.sum_comp σ (fun i => d (a i) k)).symm

theorem isMultiHomogIdeal_pC {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨map (Int.castRingHom ℂ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span (map (Int.castRingHom ℂ)) S

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_int_comp :
    (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := by
  apply RingHom.ext
  intro p
  rw [RingHom.comp_apply, MvPolynomial.map_map]
  congr 1

theorem pC_eq_extC_extQ (P : Ideal (MRing ι)) : pC P = extC (extQ P) := by
  unfold pC extC extQ
  rw [Ideal.map_map, map_int_comp]
  rfl

theorem horizontal_spec {P : Ideal (MRing ι)} (h : IsHorizontal P) :
    ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := by
  intro m hm
  have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
  unfold IsHorizontal at h
  rw [h] at h1
  exact Ideal.mem_bot.mp h1

theorem pcEquidim : PCEquidimStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [ringKrullDim_of_mem_minimalPrimes_extC (extQ P) Q hQ]
  apply withBot_eq_of_add_one
  rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]

theorem pcMinContract : PCMinContractStatement := by
  intro K _ ι _ P e hP Q hQ
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨hpr, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  rw [pC_eq_extC_extQ] at hQ
  rw [← map_int_comp, ← Ideal.comap_comap, comap_of_mem_minimalPrimes_extC (extQ P) Q hQ, hcomap]

theorem pcContract : PCContractStatement := by
  intro K _ ι _ P e hP f hf
  obtain ⟨_, hMP, hH, _⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨_, hcomap, _⟩ := extQ_spec P (horizontal_spec hH)
  rw [pC_eq_extC_extQ] at hf
  have h1 : f ∈ (extC (extQ P)).comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) := hf
  rw [← map_int_comp, ← Ideal.comap_comap, comap_extC, hcomap] at h1
  exact h1

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

