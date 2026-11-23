module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.SchemeRes
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem pC_eq_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    pC P = Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) P := rfl

theorem resExists_of_projLogRes (hL : ReciprocityTheory.AnForm.R.ProjLogResC) (hQ : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (h1 : PCRadicalStatement) (h2 : PCEquidimStatement) (h3 : PCMinContractStatement)
    (h4 : JacNotInPStatement) (h5 : PCContractStatement) : ResExistsStatement := by
  intro K _ ι _ P J e hP hJ hJP
  have hK : Nonempty K := hP.1
  have hprime : P.IsPrime := hP.2.1.1
  have hPhom : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨s, G, hGhom, hGspan, hminor⟩ := h4 K ι P e hP
  set c := Fintype.card (Σ k, ι k) - (e + Fintype.card K) with hc
  set Jac : Ideal (MRing ι) := Ideal.span (jacMinors G c) with hJac
  classical
  have isMultiHomog_mul_birational_geometry {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
      (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
    classical
    intro m hm k
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
    rw [hf m1 hm1 k, hg m2 hm2 k]


  have isMultiHomog_finset_prod' {β : Type} (s : Finset β) (f : β → MRing ι) (a : β → K → ℕ)
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

  have isMultiHomog_finset_sum {β : Type} (s : Finset β) (f : β → MRing ι) (a : K → ℕ)
      (h : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
    classical
    intro m hm k
    obtain ⟨x, hx, hm'⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    exact h x hx m hm' k

  have isMultiHomog_zsmul (c : ℤ) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
      IsMultiHomog (c • f) a := fun m hm k => h m (MvPolynomial.support_smul hm) k

  have isMultiHomog_pderiv_and_one_le_of_pderiv_ne_zero (v : Σ k, ι k) {p : MRing ι} {d : K → ℕ}
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

  have isMultiHomog_det_pderiv {s c : ℕ} (G : Fin s → MRing ι) (hG : ∀ i, ∃ a, IsMultiHomog (G i) a)
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
  have hJacHom : IsMultiHomogIdeal Jac := by
    refine ⟨jacMinors G c, ?_, rfl⟩
    rintro f ⟨a, b, rfl⟩
    exact isMultiHomog_det_pderiv G hGhom a b
  have hJ'hom : IsMultiHomogIdeal (J * Jac) := isMultiHomogIdeal_mul hJ hJacHom
  have hJ'P : ¬ J * Jac ≤ P := by
    intro h
    rcases hprime.mul_le.mp h with h1' | h1'
    · exact hJP h1'
    · exact hminor h1'
  refine ⟨J * Jac, Ideal.mul_le_left, hJ'hom, hJ'P, ?_⟩
  have hGC : ∀ i, ∃ a, ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) (G i)) a := by
    intro i
    obtain ⟨a, ha⟩ := hGhom i
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hspanC : Ideal.span (Set.range fun i => map (Int.castRingHom ℂ) (G i)) = pC P := by
    rw [pC_eq_map, ← hGspan, Ideal.map_span, ← Set.range_comp]
    rfl
  have hsing : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
      (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC P) p, eval z h = 0) →
      ¬ IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC P) p) z) →
      ∀ f ∈ pC (J * Jac), eval z f = 0 := by
    intro p z hz hnreg f hf
    have hminC : ∀ (a : Fin c → Fin s) (b : Fin c → Σ k, ι k),
        eval z (Matrix.det (Matrix.of fun i j =>
          pderiv (b j) (map (Int.castRingHom ℂ) (G (a i))))) = 0 := by
      intro a b
      by_contra hne
      exact hnreg (ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart (pC P) e (h2 K ι P e hP)
        (fun i => map (Int.castRingHom ℂ) (G i)) hGC hspanC p z hz a b hne)
    have hle : pC (J * Jac) ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) := by
      rw [pC_eq_map, Ideal.map_mul]
      refine le_trans Ideal.mul_le_right ?_
      rw [hJac, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨d, ⟨a, b, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.map_det]
      have hmat : (MvPolynomial.map (Int.castRingHom ℂ)).mapMatrix
          (Matrix.of fun i j => pderiv (b j) (G (a i))) =
          Matrix.of fun i j => pderiv (b j) (map (Int.castRingHom ℂ) (G (a i))) := by
        ext i j
        simp [pderiv_map]
      rw [hmat]
      exact hminC a b
    exact RingHom.mem_ker.mp (hle hf)
  have hcomp : ∀ Q ∈ (pC P).minimalPrimes, ReciprocityTheory.AnForm.R.IsRelevant Q →
      ¬ pC (J * Jac) ≤ Q := by
    intro Q hQ _ hle
    apply hJ'P
    rw [← h3 K ι P e hP Q hQ]
    exact le_trans Ideal.le_comap_map (Ideal.comap_mono hle)
  have hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
      (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC P) p, eval z h = 0) →
      ringKrullDim (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC P) p) z) = e :=
    fun p z hz => ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart (pC P) (isMultiHomogIdeal_pC hPhom) e
      (h2 K ι P e hP) p z hz
  obtain ⟨R⟩ := ReciprocityTheory.AnForm.R.algRes_of_logResStC hQ (pC P) (pC (J * Jac)) e
    (isMultiHomogIdeal_pC hPhom) (h1 K ι P e hP) (isMultiHomogIdeal_pC hJ'hom) hcomp hsing hdim
    (hL K ι (pC P) (pC (J * Jac)) (isMultiHomogIdeal_pC hPhom) (isMultiHomogIdeal_pC hJ'hom)
      (h1 K ι P e hP) hsing hcomp)
  exact nonempty_anLogRes_of_algRes P (J * Jac) e hJ'hom hJ'P (h5 K ι P e hP) R

theorem resExists (hC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStCR.{0}) (hQ : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (h1 : PCRadicalStatement) (h2 : PCEquidimStatement) (h3 : PCMinContractStatement)
    (h4 : JacNotInPStatement) (h5 : PCContractStatement) : ResExistsStatement :=
  resExists_of_projLogRes (ReciprocityTheory.AnForm.R.projLogResC_of_CR hC hQ) hQ h1 h2 h3 h4 h5

end ReciprocityTheory.ChartRestriction.G.Geo
