module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusGenDegreeHomToZl
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramGen

theorem exists_normalised {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Subgroup G) (F : G)
    (hF : (Subgroup.zpowers F ⊔ I).topologicalClosure = ⊤) (z : G → ℤ_[l]) (hc : Continuous z)
    (hadd : ∀ σ τ, z (σ * τ) = z σ + z τ) (hI : ∀ σ ∈ I, z σ = 0) (h0 : ∃ σ, z σ ≠ 0) :
    ∃ ν : G →* Multiplicative ℤ_[l], Continuous ν ∧ (∀ σ ∈ I, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 := by
  have h1 : z 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ σ, z σ⁻¹ = - z σ := by
    intro σ
    have h := hadd σ σ⁻¹
    rw [mul_inv_cancel, h1] at h
    linear_combination -h

  let H : Subgroup G :=
    { carrier := {σ | ‖z σ‖ ≤ ‖z F‖}
      mul_mem' := fun {a b} ha hb => by
        show ‖z (a * b)‖ ≤ ‖z F‖
        rw [hadd]
        exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
      one_mem' := by
        show ‖z 1‖ ≤ ‖z F‖
        rw [h1, norm_zero]
        exact norm_nonneg _
      inv_mem' := fun {a} ha => by
        show ‖z a⁻¹‖ ≤ ‖z F‖
        rw [hinv, norm_neg]
        exact ha }
  have hHc : IsClosed (H : Set G) := isClosed_le (continuous_norm.comp hc) continuous_const
  have hsup : Subgroup.zpowers F ⊔ I ≤ H := by
    refine sup_le ((Subgroup.zpowers_le (H := H)).2 (show ‖z F‖ ≤ ‖z F‖ from le_rfl)) ?_
    intro σ hσ
    show ‖z σ‖ ≤ ‖z F‖
    rw [hI σ hσ, norm_zero]
    exact norm_nonneg _
  have hbound : ∀ σ, ‖z σ‖ ≤ ‖z F‖ := by
    intro σ
    have hle := Subgroup.topologicalClosure_minimal _ hsup hHc
    rw [hF] at hle
    exact hle (Subgroup.mem_top σ)
  have hF0 : z F ≠ 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := h0
    apply hσ
    have := hbound σ
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hF0' : (z F : ℚ_[l]) ≠ 0 := fun h => hF0 (Subtype.ext (h.trans PadicInt.coe_zero.symm))

  let w : G → ℤ_[l] := fun σ => ⟨(z σ : ℚ_[l]) / (z F : ℚ_[l]), by
    rw [PadicInt.mem_subring_iff, norm_div, PadicInt.norm_coe, PadicInt.norm_coe,
      div_le_one (norm_pos_iff.mpr hF0)]
    exact hbound σ⟩
  have hw : ∀ σ, (w σ : ℚ_[l]) = (z σ : ℚ_[l]) / (z F : ℚ_[l]) := fun _ => rfl
  have hwadd : ∀ σ τ, w (σ * τ) = w σ + w τ := by
    intro σ τ
    apply Subtype.ext
    show (w (σ * τ) : ℚ_[l]) = ((w σ + w τ : ℤ_[l]) : ℚ_[l])
    rw [PadicInt.coe_add, hw, hw, hw, hadd, PadicInt.coe_add, add_div]
  have hwc : Continuous w :=
    Continuous.subtype_mk ((continuous_subtype_val.comp hc).div_const _) _
  let ν : G →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (w σ)) (fun σ τ => by
      rw [hwadd]
      rfl)
  refine ⟨ν, continuous_ofAdd.comp hwc, ?_, ?_⟩
  · intro σ hσ
    show Multiplicative.ofAdd (w σ) = 1
    rw [ofAdd_eq_one]
    apply Subtype.ext
    show (w σ : ℚ_[l]) = ((0 : ℤ_[l]) : ℚ_[l])
    rw [hw, hI σ hσ]
    simp
  · show Multiplicative.ofAdd (w F) = Multiplicative.ofAdd 1
    congr 1
    apply Subtype.ext
    show (w F : ℚ_[l]) = ((1 : ℤ_[l]) : ℚ_[l])
    rw [hw, div_self hF0', PadicInt.coe_one]

private theorem norm_prime_lt_one_algClosure {l : ℕ} [Fact l.Prime] : ‖(l : Om l)‖ < 1 := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem norm_pow_sub_pow_le_norm_sub {E : Type} [NormedField E] [IsUltrametricDist E] {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖y ^ i - x ^ i‖ ≤ ‖y - x‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro j _
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hy) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

private theorem fixes_root_of_unity_of_inertia_like {l : ℕ} [Fact l.Prime] (σ : GQ l)
    (hσ : ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) (n : ℕ) (hn : 0 < n) (x : Om l)
    (hx : x ^ l ^ n = x) : σ x = x := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl1
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hxq : x ^ (l ^ n - 1) = 1 := by
    have h : x ^ (l ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 h
  have hnx : ‖x‖ = 1 := by
    have h := congrArg norm hxq
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) (by omega)).mp h
  have hy : σ x ^ l ^ n = σ x := by rw [← map_pow, hx]
  have hε : ‖σ x - x‖ < 1 := hσ x hnx.le
  have hny : ‖σ x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (σ x - x) x
    rw [sub_add_cancel, hnx] at h
    exact h.trans (max_le hε.le le_rfl)
  by_contra hne
  have hne' : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  set S := ∑ i ∈ Finset.range (l ^ n), σ x ^ i * x ^ (l ^ n - 1 - i) with hSdef

  have hS : S = 1 := by
    have h := geom_sum₂_mul (σ x) x (l ^ n)
    rw [hy, hx] at h
    exact mul_right_cancel₀ hne' (h.trans (one_mul _).symm)

  have hterm : ∀ i ∈ Finset.range (l ^ n),
      ‖σ x ^ i * x ^ (l ^ n - 1 - i) - 1‖ ≤ ‖σ x - x‖ := by
    intro i hi
    have hi' : i ≤ l ^ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have h1 : (1 : Om l) = x ^ i * x ^ (l ^ n - 1 - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi', hxq]
    rw [h1, ← sub_mul, norm_mul, norm_pow, hnx, one_pow, mul_one]
    exact norm_pow_sub_pow_le_norm_sub hnx.le hny i
  have hsum : ‖S - ((l ^ n : ℕ) : Om l)‖ ≤ ‖σ x - x‖ := by
    have h : ((l ^ n : ℕ) : Om l) = ∑ i ∈ Finset.range (l ^ n), (1 : Om l) := by simp
    rw [h, hSdef, ← Finset.sum_sub_distrib]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) hterm
  have hlq : ‖((l ^ n : ℕ) : Om l)‖ < 1 := by
    rw [Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_prime_lt_one_algClosure hn.ne'
  have hq1 : ‖((l ^ n : ℕ) : Om l) - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlq.ne), norm_neg, norm_one]
    exact max_eq_right hlq.le
  have key : ‖S - 1‖ = 1 := by
    have e : S - 1 = (((l ^ n : ℕ) : Om l) - 1) + (S - ((l ^ n : ℕ) : Om l)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hq1]; exact (hsum.trans_lt hε).ne'), hq1]
    exact max_eq_left (hsum.trans hε.le)
  rw [hS, sub_self, norm_zero] at key
  exact zero_ne_one key

theorem exists_gen_degree : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l),
    ∃ (F : ↥(GK K)) (ν : ↥(GK K) →* Multiplicative ℤ_[l]), Continuous ν ∧ (∀ σ ∈ IK K, ν σ = 1) ∧
      ν F = Multiplicative.ofAdd 1 ∧
      (Subgroup.closure (insert F (IK K : Set ↥(GK K)))).topologicalClosure = ⊤ := by
  intro l _ K

  obtain ⟨φ, hφ⟩ := (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).1
  obtain ⟨z, hzc, hzadd, hzval⟩ := GlobalTheory.UnramifiedDegree.exists_degree l
    (fun n hn σ => GlobalTheory.InertiaEigenvalues.FrobPow.exists_gal_eq_pow l n hn σ)
    (GlobalTheory.Cyc.exists_frobenius_and_exponent_modEq l).2
  have hz1 : z 1 = 0 := by simpa using hzadd 1 1
  have hzφ : z φ = 1 := by
    have h := hzval φ 1 (fun n hn x hx => by rw [pow_one]; exact hφ n hn x hx)
    simpa using h
  have hzpow : ∀ m : ℕ, z (φ ^ m) = m := by
    intro m
    induction m with
    | zero => simp [hz1]
    | succ m ih =>
      rw [pow_succ, hzadd, ih, hzφ]
      push_cast
      ring

  have hfix : ∀ σ : GQ l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → z σ = 0 := by
    intro σ hσ
    have h := hzval σ 0 (fun n hn x hx => by
      rw [pow_zero, pow_one]
      exact fixes_root_of_unity_of_inertia_like σ hσ n hn x hx)
    simpa using h

  obtain ⟨N, hN, hmem⟩ : ∃ N : ℕ, 0 < N ∧ φ ^ N ∈ GK K := by
    have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
    let g : ℕ → ((K : IntermediateField ℚ_[l] (Om l)) →ₐ[ℚ_[l]] Om l) := fun m =>
      ((φ ^ m : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp (K : IntermediateField ℚ_[l] (Om l)).val
    have claim : ∀ i j, i < j → g i = g j → φ ^ (j - i) ∈ GK K := by
      intro i j hij hg
      show φ ^ (j - i) ∈ (K : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (φ ^ i) x = (φ ^ j) x := DFunLike.congr_fun hg ⟨x, hx⟩
      have h2 : φ ^ j = φ ^ i * φ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hij.le]
      rw [h2, AlgEquiv.mul_apply] at h1
      exact ((φ ^ i).injective h1).symm
    obtain ⟨i, j, hij, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, claim i j h hg⟩
    · exact ⟨i - j, by omega, claim j i h hg.symm⟩

  let z' : ↥(GK K) → ℤ_[l] := fun σ => z σ
  have hz'c : Continuous z' := hzc.comp continuous_subtype_val
  have hz'add : ∀ σ τ, z' (σ * τ) = z' σ + z' τ := fun σ τ => hzadd σ τ
  let f : ↥(GK K) →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun σ => Multiplicative.ofAdd (z' σ)) (fun σ τ => by rw [hz'add]; rfl)
  have hIK : IK K ≤ f.ker := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z σ) = 1
    rw [hfix σ hσ, ofAdd_zero]
  have hz'I : ∀ σ ∈ IK K, z' σ = 0 := by
    intro σ hσ
    have h := hIK hσ
    rw [MonoidHom.mem_ker] at h
    change Multiplicative.ofAdd (z' σ) = 1 at h
    exact ofAdd_eq_one.mp h
  have h0 : ∃ σ, z' σ ≠ 0 := ⟨⟨φ ^ N, hmem⟩, by
    show z (φ ^ N) ≠ 0
    rw [hzpow]
    exact Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨F, hF⟩ := GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia l K
  obtain ⟨ν, hνc, hνI, hνF⟩ := exists_normalised (IK K) F hF z' hz'c hz'add hz'I h0
  refine ⟨F, ν, hνc, hνI, hνF, ?_⟩
  rw [eq_top_iff, ← hF]
  refine Subgroup.topologicalClosure_mono (sup_le ?_ ?_)
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert F _))
  · intro σ hσ
    exact Subgroup.subset_closure (Set.mem_insert_of_mem F hσ)

end GlobalTheory.UnramGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbedding
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt


set_option maxHeartbeats 1000000 in
theorem exists_hodge_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  intro l _ K L P AI T C hC ξ hξ a r R hR hDR τ σ hσ
  haveI := K.2
  haveI := L.2
  haveI := (_root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K L (Fin a → ↥L.1) R).1
  obtain ⟨m, d, k, hA⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) R
    (GlobalTheory.DRFil.filSpans T K L R hDR) τ
  obtain ⟨K', hKK', hK'⟩ := exists_ext_fixing l K L σ
  obtain ⟨e, he1, he0⟩ := GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel l P σ L a
  have hid := phiS_idem l P K L τ σ hσ
  set w : Fin m → Fin a → P.R.BdR := fun i => PhiS P σ L a (d i) with hw
  have hfil : ∀ i j, w i j ∈ (P.PD K).Fil (k i) := fun i j =>
    phiS_mem_Fil l P AI T K L σ (k i) _ (GlobalTheory.DRFil.ext_mem_FilV (P.PD K) _ (hA.mem i).2)
  have hind : ∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0 := by
    intro β hβ
    have h0 : ∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) (e * ((1 : ↥L.1) ⊗ₜ β i)) (d i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.DRFil.sm_mul, GlobalTheory.DRFil.sm_one_tmul, ← map_sum]
      apply he0
      rw [PhiS_sum]
      simp only [PhiS_mulR]
      rw [← hβ]
      funext j
      simp [hw]
    funext i
    have := congrArg (phiS P σ L) (hA.indep _ h0 i)
    simpa [map_mul, hid, he1, phiS_tmul] using this
  have hspan : ∀ j, ∃ u : Fin m → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1 := by
    intro j
    obtain ⟨rr, hrr, hy⟩ := hA.span 0 (Pi.single j 1 ⊗ₜ (1 : P.R.BdR))
      (GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (P.PD K).one_mem)
    refine ⟨fun i => phiS P σ L (rr i), fun i => by simpa using phiS_mem_Fil l P AI T K L σ _ _ (hrr i), ?_⟩
    have h2 := congrArg (PhiS P σ L a) hy
    rw [PhiS_sm] at h2
    simp only [hid, one_mul, PhiS_sum, PhiS_sm] at h2
    have h3 : ∑ i, (fun i => phiS P σ L (rr i)) i • w i = ∑ x, fun i => phiS P σ L (rr x) * PhiS P σ L a (d x) i := rfl
    rw [h3, ← h2, PhiS_tmul]
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hinv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i,
      ((fun g => (r g).val.map fun x => σ (x : Om l)) g).map (algebraMap (Om l) P.R.BdR) *ᵥ
        (fun j => P.actQdR (g : GQ l) (w i j)) = w i := by
    intro g hg i
    have h1 := _root_.GlobalTheory.HodgeAt.PhiS_act l P K L σ a r R hR g (fun y => hK' g hg y) (d i)
    rw [(GlobalTheory.DRFil.mem_DdR (P.PD K) R _).1 (hA.mem i).1.1 g] at h1
    rw [Matrix.map_map]
    exact h1.symm
  have hma := _root_.GlobalTheory.card_eq_of_indep_spans_dR l P AI T a m w hind (fun j => (hspan j).imp fun u hu => hu.2)
  subst hma
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_basis_of_adapted_invariant_family l P AI T C hC ξ hξ K K' m _ w k hfil hspan hinv
  exact ⟨K', H, hKK', fun n => by rw [hH n, hA.multV_eq]⟩

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApproxStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_powerSeries_division_approx : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  first | exact @GlobalTheory.BK.DivApprox.exists_div_approx | exact GlobalTheory.BK.DivApprox.exists_div_approx | (intros; apply GlobalTheory.BK.DivApprox.exists_div_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeLayerCoverBasisModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → LinearIndependent ℚ_[l] b → (∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ c : ℕ, (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → ∀ (n N : ℕ), n ≤ N → (∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ N • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹) → ∀ (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, Continuous (ρs k)) → (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∀ cs : Fin m → Om l, (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (L k).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb P N ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  first | (exact @GlobalTheory.CovLayer.layer) | (exact GlobalTheory.CovLayer.layer) | (intros; apply GlobalTheory.CovLayer.layer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_wach_functor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → FaithH AI → WachEx AI → ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  first | exact @GlobalTheory.HWL.Assembly.exists_wach | exact GlobalTheory.HWL.Assembly.exists_wach | (intros; apply GlobalTheory.HWL.Assembly.exists_wach <;> assumption)
end

