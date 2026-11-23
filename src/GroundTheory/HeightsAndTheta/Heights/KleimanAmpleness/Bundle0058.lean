module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Forms

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem RowSub.isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem RowSub.isMultiHomog_C (r : S) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRingOver S ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm


omit [Fintype K] in
theorem RowSub.isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · subst h
    by_cases hk : k' = k
    · subst hk
      simp [Finsupp.single_apply]
    · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
      simp [hk]
  · exact absurd rfl hm


omit [Fintype K] in
theorem RowSub.isMultiHomog_pow {f : MRingOver S ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (n : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact RowSub.isMultiHomog_mul ih hf


omit [Fintype K] in
theorem RowSub.isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f b) (a b)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact RowSub.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem RowSub.isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ d k) d := by
  classical
  have h := RowSub.isMultiHomog_prod (S := S) (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ d k)
    (fun k => d k • Pi.single k 1) fun k _ => RowSub.isMultiHomog_pow (RowSub.isMultiHomog_X k (c k)) _
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem RowSub.exists_form_of_mem_chartRingOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {z : Ω} (hz : z ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.chartRingOver S y c) :
    ∃ (m : K → ℕ) (h : MRingOver S ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h m ∧ z = aeval y h / ∏ k, y ⟨k, c k⟩ ^ m k := by
  classical
  have hP : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hPadd : ∀ m m' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ (m + m') k) =
      (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ m' k := fun m m' => by
    simp [pow_add, Finset.prod_mul_distrib]
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, RowSub.isMultiHomog_X p.1 p.2, ?_⟩
    rw [aeval_X]
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  | algebraMap r =>
    exact ⟨0, C r, RowSub.isMultiHomog_C r, by simp⟩
  | add x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    refine ⟨m + m', h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m' k + h' * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m k,
      ?_, ?_⟩
    · have h1 := RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd (S := S) c m')
      have h2 := RowSub.isMultiHomog_mul hh' (RowSub.isMultiHomog_coordProd (S := S) c m)
      rw [add_comm m' m] at h2
      intro d hd k
      rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
      · exact h1 d hd k
      · exact h2 d hd k
    · rw [hPadd, div_add_div _ _ (hP m) (hP m')]
      simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X]
      ring
  | mul x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    exact ⟨m + m', h * h', RowSub.isMultiHomog_mul hh hh', by rw [hPadd, map_mul, div_mul_div_comm]⟩

end Forms

theorem RowSub.proof : RowSub.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I hne hI t ht
  obtain ⟨n, hn⟩ := ht
  choose c hc using hne
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hc k)
  set δ : K → ℤ := γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  have h1 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hn c) hyc
  rw [Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule] at h1
  obtain ⟨m, h, hh, heq⟩ := RowSub.exists_form_of_mem_chartRingOver y c hyc h1

  set p : K → ℕ := fun k => (-δ k).toNat with hp
  set q : K → ℕ := fun k => (δ k + p k).toNat with hq
  have hpk : ∀ k, -δ k ≤ (p k : ℤ) := fun k => Int.self_le_toNat _
  have hqk : ∀ k, (q k : ℤ) = δ k + p k := fun k => Int.toNat_of_nonneg (by have := hpk k; omega)

  set T : MRingOver S ι := (∏ j ∈ J.1, (X ⟨k₀, e.symm j⟩ : MRingOver S ι)) ^ n *
    ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ (m k + p k) with hT
  set G : MRingOver S ι := h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ q k with hG
  set a : K → ℕ := n • (∑ j ∈ J.1, (Pi.single k₀ 1 : K → ℕ)) + (m + p) with ha
  have hTa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog T a := by
    refine RowSub.isMultiHomog_mul (RowSub.isMultiHomog_pow (RowSub.isMultiHomog_prod _ _ _ fun j _ =>
      RowSub.isMultiHomog_X k₀ (e.symm j)) n) ?_
    exact RowSub.isMultiHomog_coordProd c (m + p)
  have hak : ∀ k, γ k + (a k : ℤ) = δ k + p k + m k := by
    intro k
    simp only [ha, hδ, Pi.add_apply, Pi.smul_apply, Finset.sum_const, smul_eq_mul,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    by_cases hk : k = k₀
    · subst hk; simp; ring
    · simp [hk]; ring
  have hGa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun k => (γ k + a k).toNat) := by
    have e' : (fun k => (γ k + (a k : ℤ)).toNat) = m + q := by
      funext k
      rw [hak k, Pi.add_apply]
      have := hqk k
      have := hpk k
      omega
    rw [e']
    exact RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd c q)
  have hXmem : ∀ k (i : ι k), i ∈ baseCell k₀ e J.1 I k →
      (X ⟨k, i⟩ : MRingOver S ι) ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) :=
    fun k i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hTmem : T ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    refine mul_mem (pow_mem (prod_mem fun j hj => hXmem k₀ (e.symm j) ?_) n)
      (prod_mem fun k _ => pow_mem (hXmem k (c k) ?_) _)
    · unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    · unfold baseCell
      by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact Finset.mem_union_left _ (hc k)
      · rw [Function.update_of_ne hk]; exact hc k
  have hmeet : CellMeets y (baseCell k₀ e J.1 I) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact hI k i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (Kleiman.mem_support _).mp (J.2.2 hj)
    · rw [Function.update_of_ne hk] at hi; exact hI k i hi

  have hx : Kleiman.xProd J ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hPm : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hPp : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hTv : aeval y T = Kleiman.xProd J ^ n * ∏ k, y ⟨k, c k⟩ ^ (m k + p k) := by
    simp only [hT, map_mul, map_prod, map_pow, aeval_X]
    rfl
  have hGv : aeval y G = aeval y h * ∏ k, y ⟨k, c k⟩ ^ q k := by
    simp only [hG, map_mul, map_prod, map_pow, aeval_X]
  have hH : aeval y h = Kleiman.xProd J ^ n * t * (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ m k := by
    rw [eq_div_iff hPm] at heq
    exact heq.symm
  have e1 : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) = (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  have e2 : (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ q k = ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hqk k]
    congr 1
    ring
  have hval : t = aeval y G / aeval y T := by
    rw [hTv, hGv, eq_div_iff (mul_ne_zero (pow_ne_zero _ hx) hPp), hH, e1]
    linear_combination (-(Kleiman.xProd J ^ n * t * ∏ k, y ⟨k, c k⟩ ^ m k)) * e2
  show t ∈ cellSec S y γ (baseCell k₀ e J.1 I)
  unfold cellSec
  rw [if_pos hmeet]
  exact Submodule.subset_span ⟨G, T, a, hTmem, hTa, fun k => by rw [hak k]; have := hpk k; have := hqk k; omega,
    hGa, hval⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver cellMon)

namespace RowSecGlue

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [Algebra S Ω]

def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_ratioPt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (R : MRingOver S ι) :
    aeval (ratioPt y c) R ∈ chartRingOver S y c := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨R, rfl⟩

theorem aeval_eq_ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {F : MRingOver S ι} {d : K → ℕ} (hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F d) :
    aeval y F = aeval (ratioPt y c) F * ∏ k, y ⟨k, c k⟩ ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ p : (Σ k, ι k), y p ^ μ p = ratioPt y c p ^ μ p * y ⟨p.1, c p.1⟩ ^ μ p := by
    intro p
    rw [ratioPt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hc p.1))]
  have h2 : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hF μ hμ k]
  rw [Finset.prod_congr rfl fun p _ => h1 p, Finset.prod_mul_distrib, h2]
  ring

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_eq_pow (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Finset (Fin (N + 1))) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : MRingOver S ι}
    (ht : t ∈ cellMon S (baseCell k₀ e J fun k => {c k})) :
    ∃ (n : ℕ) (w : Ω), w ∈ chartRingOver S y c ∧
      w * aeval (ratioPt y c) t = (∏ j ∈ J, ratioPt y c ⟨k₀, e.symm j⟩) ^ n := by
  have hone : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k => div_self (hc k)
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
      · refine ⟨1, ∏ j' ∈ J.erase j, ratioPt y c ⟨k, e.symm j'⟩,
          prod_mem fun j' _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k, e.symm j'⟩), ?_⟩
        rw [aeval_X, pow_one]
        exact Finset.prod_erase_mul J (fun j' => ratioPt y c ⟨k, e.symm j'⟩) hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi
      exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul f g _ _ h₁ h₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := h₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := h₂
    exact ⟨n₁ + n₂, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, pow_add, ← e₁, ← e₂]; ring⟩

theorem prod_zpow_neg (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (k₀ : K) (γ : K → ℤ) (m : ℕ) :
    ∏ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = (∏ k, Y k ^ γ k)⁻¹ * (Y k₀ ^ m)⁻¹ := by
  have h : ∀ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (Y k ^ γ k)⁻¹ * (Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k))⁻¹ := by
    intro k
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_add, zpow_add₀ (hY k), zpow_neg, zpow_neg,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  have h2 : ∏ k, Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k) = Y k₀ ^ m := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [Pi.single_apply, hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, h2]

theorem exists_pow_of_mem_cellSec (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ)
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : Ω}
    (hz : z ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Kleiman.xProd J ^ n * z *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
  have hJ : ∀ j ∈ J.1, y ⟨k₀, e.symm j⟩ ≠ 0 := fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hmeet : CellMeets y (baseCell k₀ e J.1 fun k => {c k}) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact hc k
      · exact hJ j hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi; exact hc k
  unfold cellSec at hz
  rw [if_pos hmeet] at hz
  set u := ratioPt y c with hu
  set xJ := ∏ j ∈ J.1, u ⟨k₀, e.symm j⟩ with hxJdef
  have hxJ : xJ ∈ chartRingOver S y c :=
    prod_mem fun j _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k₀, e.symm j⟩)
  have hxJ0 : xJ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => div_ne_zero (hJ j hj) (hc k₀)
  have hX : Kleiman.xProd J = xJ * y ⟨k₀, c k₀⟩ ^ J.1.card := by
    rw [Kleiman.xProd, hxJdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hu, ratioPt, Function.comp, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [div_mul_cancel₀ _ (hc k₀)]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, t, a', ht, hta, hγ, hg, rfl⟩ := hz
    obtain ⟨n₀, w, hw, hwt⟩ := exists_mul_eq_pow y k₀ e J.1 c hc ht
    refine ⟨n₀, fun n hn => ?_⟩
    have ht0 : aeval u t ≠ 0 := fun h0 => pow_ne_zero n₀ hxJ0 (by rw [← hwt, h0, mul_zero])
    have hg' := aeval_eq_ratioPt y c hc hg
    have ht' := aeval_eq_ratioPt y c hc hta
    have hexp : ∏ k, y ⟨k, c k⟩ ^ (γ k + a' k).toNat = (∏ k, y ⟨k, c k⟩ ^ γ k) * ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hγ k), zpow_add₀ (hc k), zpow_natCast]
    have hW : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hA : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    rw [← hu] at hg' ht'
    have hn' : xJ ^ n = xJ ^ (n - n₀) * (w * aeval u t) := by
      rw [hwt, ← pow_add, Nat.sub_add_cancel hn]
    have key : Kleiman.xProd J ^ n * (aeval y g / aeval y t) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        xJ ^ (n - n₀) * w * aeval u g := by
      rw [prod_zpow_neg (fun k => y ⟨k, c k⟩) hc k₀ γ, hX, mul_pow, hn', hg', ht', hexp, pow_mul]
      have hp : y ⟨k₀, c k₀⟩ ^ (J.1.card * n) * (y ⟨k₀, c k₀⟩)⁻¹ ^ (J.1.card * n) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (hc k₀), one_pow]
      field_simp
      linear_combination (w * aeval u g) * hp
    rw [key]
    exact mul_mem (mul_mem (pow_mem hxJ _) hw) (aeval_ratioPt_mem y c g)
  | zero => exact ⟨0, fun n _ => by simp⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, h₂⟩ := h₂
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have := add_mem (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    rwa [← add_mul, ← mul_add] at this
  | smul r z _ h =>
    obtain ⟨n₀, h⟩ := h
    refine ⟨n₀, fun n hn => ?_⟩
    have e1 : Kleiman.xProd J ^ n * (r • z) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        algebraMap S Ω r * (Kleiman.xProd J ^ n * z *
          ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) := by
      rw [Algebra.smul_def]; ring
    rw [e1]
    exact mul_mem (Subalgebra.algebraMap_mem _ r) (h n hn)

end RowSecGlue

theorem RowSecGlue.proof : RowSecGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J a h
  have hc : ∀ c : ∀ k, ι k, ∃ n₀ : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n ≥ n₀, Kleiman.xProd J ^ n * a *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, h'⟩ := RowSecGlue.exists_pow_of_mem_cellSec y k₀ e γ J c hc (h c hc)
      exact ⟨n₀, fun _ => h'⟩
    · exact ⟨0, fun h' => absurd h' hc⟩
  choose n₀ hn₀ using hc
  refine ⟨Finset.univ.sup n₀, ?_⟩
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c hc'
  exact hn₀ c hc' _ (Finset.le_sup (Finset.mem_univ c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

