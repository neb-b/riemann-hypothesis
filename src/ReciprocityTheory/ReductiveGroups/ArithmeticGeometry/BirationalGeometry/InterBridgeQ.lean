module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem eval_eq_zero_of_mul (hM : PCMinContractStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) {u : MRing ι}
    (hu : u ∉ P) {H : MRingOver ℂ ι}
    (h : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) u) * eval z H = 0) :
    ∀ z ∈ mcPts P, eval z H = 0 := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose i hi using hP.2.1.2.2
  set m : MRing ι := ∏ k, X ⟨k, i k⟩ with hmdef
  have hm : m ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k hk
  have hv : u * m ∉ P := fun h' => (hPp.mem_or_mem h').elim hu hm
  have hvan : map (Int.castRingHom ℂ) (u * m) * H ∈ (pC P).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change eval x _ = 0
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    by_cases hb : ∀ k, x ⟨k, i k⟩ ≠ 0
    · have hxm : x ∈ mcPts P := by
        rw [mcPts_eq_pC]
        exact ⟨fun k => ⟨i k, hb k⟩, fun f hf => hx f hf⟩
      rw [map_mul, map_mul, map_mul, mul_right_comm, h x hxm, zero_mul]
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      have : eval x (map (Int.castRingHom ℂ) m) = 0 := by
        rw [hmdef, map_prod, map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      rw [map_mul, map_mul, map_mul, this, mul_zero, zero_mul]
  have hHrad : H ∈ (pC P).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.mpr fun Q hQ => ?_
    have hQp : Ideal.IsPrime Q := hQ.1.1
    have hle : (pC P).radical ≤ Q := (Ideal.IsPrime.radical_le_iff hQp).mpr hQ.1.2
    have hvQ : map (Int.castRingHom ℂ) (u * m) ∉ Q := fun h' => by
      apply hv
      rw [← hM K ι P e hP Q hQ]
      exact h'
    exact (hQp.mem_or_mem (hle hvan)).resolve_left hvQ
  intro z hz
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    MvPolynomial.mem_vanishingIdeal_iff] at hHrad
  have := hHrad z (by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    exact (by rw [mcPts_eq_pC] at hz; exact hz.2 p hp))
  exact this

theorem exists_homog_of_cone {n : ℕ} {c : MvPolynomial (Fin n) ℂ} (hc : c ≠ 0)
    {T : Set (Fin n → ℂ)} (hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun i => t * v i) ∈ T)
    (hcT : ∀ v ∈ T, eval v c = 0) :
    ∃ m, homogeneousComponent m c ≠ 0 ∧ (homogeneousComponent m c).IsHomogeneous m ∧
      ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
  have hscale : ∀ (m : ℕ) (t : ℂ) (v : Fin n → ℂ),
      eval (fun i => t * v i) (homogeneousComponent m c) = t ^ m * eval v (homogeneousComponent m c) := by
    intro m t v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have hdeg : ∑ i ∈ d.support, d i = m := by
      first
      | exact hd.2
      | (rw [← hd.2]; rfl)
      | simpa [Finsupp.degree] using hd.2
    simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring
  have hcomp : ∀ m, ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
    intro m v hv
    let Q : Polynomial ℂ := ∑ k ∈ Finset.range (c.totalDegree + 1),
      Polynomial.C (eval v (homogeneousComponent k c)) * Polynomial.X ^ k
    have hQ : ∀ t : ℂ, t ≠ 0 → Q.eval t = 0 := by
      intro t ht
      have h0 := hcT _ (hT v hv t ht)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent c, map_sum] at h0
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h0]
      exact Finset.sum_congr rfl fun k _ => by rw [hscale]; ring
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := {t : ℂ | t ≠ 0})
      · intro t ht
        exact hQ t ht
      · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
    by_cases hm : m ≤ c.totalDegree
    · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) hQ0
      simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        (by omega : m < c.totalDegree + 1)] using h1
    · rw [homogeneousComponent_eq_zero m c (by omega), map_zero]
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.range (c.totalDegree + 1), homogeneousComponent m c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [← sum_homogeneousComponent c]
    exact Finset.sum_eq_zero hcon
  exact ⟨m, hm, homogeneousComponent_isHomogeneous m c, fun v hv => hcomp m v hv⟩

theorem normPoly_of (hM : PCMinContractStatement) : NormPolyStatement := by
  intro K _ ι _ P e Ψ f a hP hΨ hf hfP
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨k1⟩ := hP.1
  choose i hi using hP.2.1.2.2
  set d := ∑ k, a k with hd
  set g : MRing ι := ∏ k, X ⟨k, i k⟩ ^ (d - a k) with hgdef
  set f' : MRing ι := f * g with hf'def
  have hgP : g ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k (hPp.mem_of_pow_mem _ hk)
  have hf'P : f' ∉ P := fun h' => (hPp.mem_or_mem h').elim hfP hgP
  have hweight (β : (Σ k, ι k) →₀ ℕ) (k : K) :
      Finsupp.weight (blkW ι) β k = ∑ j, β ⟨k, j⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [blkW, Pi.single_apply]
  have hf'h : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f') (fun _ => d) := by
    have h1 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f) a := by
      intro β hβ
      rw [coeff_map] at hβ
      have hmem : β ∈ f.support := mem_support_iff.mpr (fun h0 => hβ (by simp [h0]))
      funext k
      rw [hweight]
      exact hf β hmem k
    have h2 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) g)
        (∑ k, (d - a k) • blkW ι ⟨k, i k⟩) := by
      rw [hgdef, map_prod]
      refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
      rw [map_pow, map_X]
      exact (isWeightedHomogeneous_X ℂ _ _).pow _
    have hw : a + ∑ k, (d - a k) • blkW ι ⟨k, i k⟩ = fun _ => d := by
      funext k'
      have hle : a k' ≤ d := Finset.single_le_sum (fun k _ => Nat.zero_le (a k))
        (Finset.mem_univ k')
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blkW, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      omega
    rw [hf'def, map_mul, ← hw]
    exact h1.mul h2
  let p := map (Int.castRingHom ℂ) f'
  have hmonomial (β : (Σ k, ι k) →₀ ℕ) :
      ∃ G : MvPolynomial ((k : K) → ι k) ℂ, β ∈ p.support →
        ∀ z : (Σ k, ι k) → ℂ, ∏ q, z q ^ β q = eval (segre z) G := by
    by_cases hβ : β ∈ p.support
    · have hw := hf'h (mem_support_iff.mp hβ)
      obtain ⟨G, -, hG⟩ := diag_prod d (fun q => β q) (fun k => by
        rw [← hweight]
        exact congrFun hw k)
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => (hβ h).elim⟩
  choose G hG using hmonomial
  let F : MvPolynomial ((k : K) → ι k) ℂ :=
    ∑ β ∈ p.support, C (AddMonoidAlgebra.coeff p β) * G β
  have hF : ∀ z, eval z (map (Int.castRingHom ℂ) f') = eval (segre z) F := by
    intro z
    change eval z p = eval (segre z) F
    dsimp only [F]
    rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [eval_mul, eval_C, hG β hβ z]
  obtain ⟨n, c, hcn, hrelF⟩ := exists_monic_rel Ψ P hPh hΨ F
  have hex : ∃ k, c k ≠ 0 := ⟨n, by rw [hcn]; exact one_ne_zero⟩
  set k0 := Nat.find hex with hk0def
  have hk0 : c k0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < k0, c j = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  have hk0n : k0 ≤ n := Nat.find_min' hex (by rw [hcn]; exact one_ne_zero)
  set S := (Finset.range (n + 1)).filter (fun j => k0 ≤ j) with hSdef
  let ψ (j : Fin (e + 1)) : MRingOver ℂ ι :=
    ∑ l : (k : K) → ι k, C (Ψ (fun l' => if l = l' then 1 else 0) j) * ∏ k, X ⟨k, l k⟩
  have hψ (z : (Σ k, ι k) → ℂ) : (fun j => eval z (ψ j)) = Ψ (segre z) := by
    have hs : segre z = ∑ l : (k : K) → ι k, segre z l •
        (fun l' => if l = l' then (1 : ℂ) else 0) := by
      funext l'
      simp [Finset.sum_apply]
    funext j
    dsimp only [ψ]
    simp only [map_sum, map_mul, eval_C, map_prod, eval_X]
    conv_rhs => rw [hs]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ * segre z l = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  set H : MRingOver ℂ ι := ∑ j ∈ S,
    bind₁ ψ (c j) * (map (Int.castRingHom ℂ) f') ^ (j - k0) with hHdef
  have hbind : ∀ (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Fin (e + 1)) ℂ),
      eval z (bind₁ ψ q) = eval (Ψ (segre z)) q := by
    intro z q
    rw [eval, eval₂Hom_bind₁]
    change eval (fun j => eval z (ψ j)) q = eval (Ψ (segre z)) q
    rw [hψ]
  have hevalH : ∀ z, eval z H = ∑ j ∈ S, eval (Ψ (segre z)) (c j) * eval (segre z) F ^ (j - k0) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHdef, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hbind, hF]
  have hmul : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) (f' ^ k0)) * eval z H = 0 := by
    intro z hz
    rw [hevalH, map_pow, map_pow, hF, Finset.mul_sum, ← hrelF z hz]
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : k0 ≤ j
    · rw [if_pos hj]
      rw [show j = k0 + (j - k0) from (Nat.add_sub_cancel' hj).symm]
      rw [Nat.add_sub_cancel_left, pow_add]
      ring
    · rw [if_neg hj, hlt j (not_le.mp hj), map_zero, zero_mul]
  have hH := eval_eq_zero_of_mul hM hP (u := f' ^ k0) (fun h' => hf'P (hPp.mem_of_pow_mem _ h'))
    hmul
  set T : Set (Fin (e + 1) → ℂ) :=
    {v | ∃ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 ∧ Ψ (segre z) = v} with hTdef
  have hcT : ∀ v ∈ T, eval v (c k0) = 0 := by
    rintro _ ⟨z, hz, hfz, rfl⟩
    have h0 := hH z hz
    have hF0 : eval (segre z) F = 0 := by
      rw [← hF, hf'def, map_mul, map_mul, hfz, zero_mul]
    rw [hevalH, hF0] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa using h0
    · intro j hj hjk
      have : 0 < j - k0 := by
        have := (Finset.mem_filter.mp hj).2
        omega
      rw [zero_pow this.ne', mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩) h
  have hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun j => t * v j) ∈ T := by
    rintro _ ⟨z, hz, hfz, rfl⟩ t ht
    set cc : K → ℂ := Function.update (fun _ => (1 : ℂ)) k1 t with hccdef
    have hcc : ∀ k, cc k ≠ 0 := by
      intro k
      by_cases hk : k = k1
      · subst hk; simp [hccdef, ht]
      · simp [hccdef, Function.update_of_ne hk]
    have hpc : ∏ k, cc k = t := by
      simp [hccdef, Finset.prod_update_of_mem (Finset.mem_univ k1)]
    refine ⟨fun p => cc p.1 * z p, mcPts_smul hPh cc hcc hz, ?_, ?_⟩
    · rw [eval_smul_homog f a hf cc z, hfz, mul_zero]
    · rw [segre_smul, map_smul, hpc]
      rfl
  obtain ⟨m, hm0, hmh, hmT⟩ := exists_homog_of_cone hk0 hT hcT
  exact ⟨homogeneousComponent m (c k0), m, hm0, hmh, fun z hz hfz => hmT _ ⟨z, hz, hfz, rfl⟩⟩

end ReciprocityTheory.ChartRestriction.G.Geo
