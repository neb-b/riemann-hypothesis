module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsAwayIsDomainOfSmooth
section
set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem exists_away_isDomain_of_smooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  obtain ⟨ι, σ, _, _, ⟨Pr⟩⟩ := hstd.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K (Localization.Away g) :=
    ⟨⟨ι, σ, ‹_›, ‹_›, Pr, rfl⟩⟩
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := Pr.dimension) (R := K) (S := Localization.Away g)
  letI : Algebra (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := hφ
  haveI hq : (p.map (algebraMap A (Localization.Away g))).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨g', hg', hdom⟩ := exists_away_isDomain_of_etale
    (P := MvPolynomial (Fin Pr.dimension) K) (A := Localization.Away g)
    (p.map (algebraMap A (Localization.Away g)))
  refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem => hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hmem
  · intro S _ _ _
    haveI : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : S ≃ₐ[A] Localization.Away g' :=
      IsLocalization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g g').1)) S
        (Localization.Away g')
    exact e.toRingEquiv.toMulEquiv.isDomain

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidChartPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

open Polynomial

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext_scale (A T : Subalgebra K R) (w : R) (hwA : w ∈ A)
    (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) (g : R) (hg : IsIntegral T g) :
    ∃ N : ℕ, IsIntegral A (w ^ N * g) := by
  obtain ⟨p, hpm, hp⟩ := hg
  have hmono : ∀ (x : R) (n m : ℕ), n ≤ m → w ^ n * x ∈ A → w ^ m * x ∈ A := by
    intro x n m hnm hx
    have : w ^ m * x = w ^ (m - n) * (w ^ n * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    exact A.mul_mem (A.pow_mem hwA _) hx
  have hc : ∀ i : ℕ, ∃ n : ℕ, w ^ n * ((p.coeff i : T) : R) ∈ A := fun i =>
    hscale _ (p.coeff i).2
  choose n hn using hc
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hcN : ∀ i ≤ p.natDegree, w ^ N * ((p.coeff i : T) : R) ∈ A := by
    intro i hi
    refine hmono _ (n i) N ?_ (hn i)
    exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set P : R[X] := p.map (algebraMap T R) with hP
  have hPm : P.Monic := hpm.map _
  have hPdeg : P.natDegree = p.natDegree := hpm.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i = ((p.coeff i : T) : R) := fun i => by
    rw [hP, coeff_map]; rfl
  set Q : R[X] := P.scaleRoots (w ^ N) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hPm
  have hQlift : Q ∈ lifts (algebraMap A R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have hmem : Q.coeff i ∈ A := by
      rw [hQ, coeff_scaleRoots, hPdeg, hPcoeff]
      rcases lt_trichotomy i p.natDegree with hlt | heq | hgt
      · have h1 : (w ^ N) ^ (p.natDegree - i) = (w ^ N) ^ (p.natDegree - i - 1) * w ^ N := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, mul_comm, mul_assoc]
        exact A.mul_mem (A.pow_mem (A.pow_mem hwA _) _) (hcN i hlt.le)
      · subst heq
        have : p.coeff p.natDegree = 1 := hpm.coeff_natDegree
        rw [this, Nat.sub_self, pow_zero, mul_one]
        exact A.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact A.zero_mem
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqQ, -, hqm⟩ := lifts_and_degree_eq_and_monic hQlift hQm
  refine ⟨N, q, hqm, ?_⟩
  rw [← eval_map, hqQ, hQ, scaleRoots_eval_mul, hP, eval_map, hp, mul_zero]

theorem chart_ext_pf (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := by
  classical
  obtain ⟨t, ht⟩ := hB0FG
  obtain ⟨s, hs⟩ := hBuFG
  have hkey : ∀ g : R, ∃ N : ℕ, g ∈ Bu → IsIntegral A (w ^ N * g) := by
    intro g
    by_cases hg : g ∈ Bu
    · obtain ⟨N, hN⟩ := chart_ext_scale A T w hwA hscale g (hBuInt g hg)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose N hN using hkey
  set u : Finset R := t ∪ s.image (fun g => w ^ N g * g) with hu
  set B' : Subalgebra K R := Algebra.adjoin K (u : Set R) with hB'
  have htB' : B0 ≤ B' := by
    rw [← ht, hB']
    exact Algebra.adjoin_mono (by rw [hu, Finset.coe_union]; exact Set.subset_union_left)
  have hwB' : w ∈ B' := htB' (hAB0 hwA)
  have hgen : ∀ g ∈ s, w ^ N g * g ∈ B' := by
    intro g hg
    apply Algebra.subset_adjoin
    rw [hu, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg))
  have hsBu : ∀ g ∈ s, g ∈ Bu := fun g hg => by
    rw [← hs]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hg)

  have hpow : ∀ b ∈ Bu, ∃ L : ℕ, w ^ L * b ∈ B' := by
    intro b hb
    rw [← hs] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨N x, hgen x (Finset.mem_coe.1 hx)⟩
    | algebraMap k => exact ⟨0, by rw [pow_zero, one_mul]; exact B'.algebraMap_mem k⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x + y) = w ^ L2 * (w ^ L1 * x) + w ^ L1 * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.add_mem (B'.mul_mem (B'.pow_mem hwB' _) h1) (B'.mul_mem (B'.pow_mem hwB' _) h2)
    | mul x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x * y) = (w ^ L1 * x) * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.mul_mem h1 h2
  refine ⟨B', htB', ⟨u, hB'.symm⟩, ?_, ?_⟩
  · intro b hb
    rw [hB'] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rw [hu, Finset.coe_union] at hx
      rcases hx with hx | hx
      · apply hB0Int
        rw [← ht]
        exact Algebra.subset_adjoin hx
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hN g (hsBu g hg)
    | algebraMap k =>
      have hk : algebraMap K R k ∈ A := A.algebraMap_mem k
      have : algebraMap K R k = algebraMap A R ⟨_, hk⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  · intro r
    obtain ⟨b, hb, b', hb', hb'0, hrb⟩ := hFrac r
    obtain ⟨L1, h1⟩ := hpow b hb
    obtain ⟨L2, h2⟩ := hpow b' hb'
    refine ⟨w ^ (L1 + L2) * b, ?_, w ^ (L1 + L2) * b', ?_, ?_, ?_⟩
    · have : w ^ (L1 + L2) * b = w ^ L2 * (w ^ L1 * b) := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h1
    · have : w ^ (L1 + L2) * b' = w ^ L1 * (w ^ L2 * b') := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h2
    · exact mul_ne_zero (pow_ne_zero _ hw0) hb'0
    · rw [← hrb]; ring

end CrystallineSemistableComparison.Pb
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidResPf
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

theorem resRPf_tpow_add (t : Fin (n + 1) → Rˣ) (m m' : Fin (n + 1) → ℤ) :
    tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

theorem resRPf_tpow_negOne (t : Fin (n + 1) → Rˣ) :
    tpow t (fun _ => -1) = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  simp only [zpow_neg_one, Finset.prod_inv_distrib]

theorem resRPf_tpow_single (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    tpow t (-Pi.single k (1 : ℤ)) = (((t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem resRPf_linInd (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    LinearIndependent K (tpow t) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg m0 hm0
  set N : ℤ := ∑ m ∈ s, ∑ j, |m j| with hN
  have hbound : ∀ m ∈ s, ∀ j, 0 ≤ m j + N := by
    intro m hm j
    have h1 : |m j| ≤ ∑ j, |m j| :=
      Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |m j| ≤ N :=
      Finset.single_le_sum (f := fun m : Fin (n + 1) → ℤ => ∑ j, |m j|)
        (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hm
    have h3 := neg_abs_le (m j)
    linarith
  let e : (Fin (n + 1) → ℤ) → (Fin (n + 1) →₀ ℕ) :=
    fun m => Finsupp.equivFunOnFinite.symm (fun j => (m j + N).toNat)
  have he : ∀ m ∈ s, tpow t (m + fun _ => N) =
      MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial (e m) (1 : K)) := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    unfold tpow
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [e, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
    conv_lhs => rw [← Int.toNat_of_nonneg (hbound m hm j)]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have hmul : ∑ m ∈ s, g m • tpow t (m + fun _ => N) = 0 := by
    simp_rw [resRPf_tpow_add, ← smul_mul_assoc]
    rw [← Finset.sum_mul, hg, zero_mul]
  have hpoly : ∑ m ∈ s, MvPolynomial.monomial (e m) (g m) = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 ht
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, ← hmul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [he m hm]
    simp only [MvPolynomial.aeval_monomial, map_one, one_mul, Algebra.smul_def]
  have hinj : ∀ m ∈ s, ∀ m' ∈ s, e m = e m' → m = m' := by
    intro m hm m' hm' h
    funext j
    have h0 := DFunLike.congr_fun h j
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h0
    have h1 := hbound m hm j
    have h2 := hbound m' hm' j
    omega
  have hc := congrArg (AddMonoidAlgebra.coeff · (e m0)) hpoly
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m0] at hc
  · simpa [MvPolynomial.coeff_monomial] using hc
  · intro m hm hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hne (hinj m hm m0 hm0 h))]
  · intro h
    exact absurd hm0 h

def resRPfLogD (D : Derivation K R R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd ((((u⁻¹ : Rˣ)) : R) * D (u : R))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    have hu : (((u⁻¹ : Rˣ)) : R) * u = 1 := Units.inv_mul u
    have hv : (((v⁻¹ : Rˣ)) : R) * v = 1 := Units.inv_mul v
    simp only [mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul]
    linear_combination ((((v⁻¹ : Rˣ)) : R) * D (v : R)) * hu + ((((u⁻¹ : Rˣ)) : R) * D (u : R)) * hv

theorem resRPfLogD_apply (D : Derivation K R R) (u : Rˣ) :
    Multiplicative.toAdd (resRPfLogD D u) = (((u⁻¹ : Rˣ)) : R) * D (u : R) := rfl

theorem resRPf_logD (t : Fin (n + 1) → Rˣ) (D : Derivation K R R) (m : Fin (n + 1) → ℤ) :
    (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D (tpow t m) =
      ∑ j, m j • ((((t j)⁻¹ : Rˣ) : R) * D (t j : R)) := by
  have h := congrArg Multiplicative.toAdd (map_prod (resRPfLogD D) (fun j => t j ^ m j) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow, resRPfLogD_apply] at h
  exact h

theorem resRPf_Dk (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (k : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    D k (tpow t m) = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
  have h := resRPf_logD t (D k) m
  simp only [hD, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h
  have hU : tpow t m * (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) = 1 := Units.mul_inv _
  calc D k (tpow t m) = tpow t m * ((((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D k (tpow t m)) := by
        rw [← mul_assoc, hU, one_mul]
    _ = tpow t m * (m k • (((t k)⁻¹ : Rˣ) : R)) := by rw [h]
    _ = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
        rw [mul_smul_comm, sub_eq_add_neg, resRPf_tpow_add, resRPf_tpow_single]

theorem res_R_pf (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R))
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    ∃ res : R →ₗ[K] K, res (((∏ k, t k)⁻¹ : Rˣ) : R) = 1 ∧
      (∀ x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}), res x = 0) ∧
      ∀ k, ∀ x ∈ torusS K t Finset.univ, res (D k x) = 0 := by
  classical
  have hli := resRPf_linInd (K := K) t ht
  obtain ⟨res, hres⟩ := LinearMap.exists_extend ((Module.Basis.span hli).coord (fun _ => -1))
  have hval : ∀ m, res (tpow t m) = if m = (fun _ => -1) then 1 else 0 := by
    intro m
    have h1 : tpow t m = ((Module.Basis.span hli m : Submodule.span K (Set.range (tpow t))) : R) :=
      congrArg Subtype.val (Module.Basis.span_apply hli m).symm
    have h2 := LinearMap.congr_fun hres (Module.Basis.span hli m)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨res, ?_, ?_, ?_⟩
  · rw [← resRPf_tpow_negOne, hval, if_pos rfl]
  · intro x hx
    have hle : Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) ≤ LinearMap.ker res := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hval, if_neg hm]
    exact hle hx
  · intro k x hx
    have hx' : x ∈ Submodule.span K (Set.range (tpow t)) := by
      have h1 : x ∈ Subalgebra.toSubmodule (torusS K t Finset.univ) := hx
      rw [torusS, Algebra.adjoin_eq_span] at h1
      refine Submodule.span_mono ?_ h1
      intro y hy
      let M : Submonoid R :=
        { carrier := Set.range (tpow t)
          mul_mem' := by
            rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨a + b, resRPf_tpow_add t a b⟩
          one_mem' := ⟨0, by simp [tpow]⟩ }
      exact (Submonoid.closure_le (S := M)).2 (Set.image_subset_range _ _) hy
    have hker : Submodule.span K (Set.range (tpow t)) ≤ LinearMap.ker (res ∘ₗ (D k : R →ₗ[K] R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe,
        resRPf_Dk t D hD k m, map_zsmul, hval]
      by_cases h : m - Pi.single k (1 : ℤ) = fun _ => -1
      · have h' := congr_fun h k
        simp only [Pi.sub_apply, Pi.single_eq_same] at h'
        have h0 : m k = 0 := by omega
        rw [h0, zero_smul]
      · rw [if_neg h, smul_zero]
    have h2 := hker hx'
    rwa [LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe] at h2

end CrystallineSemistableComparison.Pb
end
end

