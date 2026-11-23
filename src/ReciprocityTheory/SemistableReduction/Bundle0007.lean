module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Lemmata.GeneralBFactLeftExtra.Imports
public import ReciprocityTheory.SemistableReduction.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.ExistsTorusPointOneLeNormSum
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable abbrev unitBallRing (K : Type*) [NormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

theorem mem_unitBallRing {K : Type*} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ unitBallRing K ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]

theorem residue_eq_zero_iff_norm_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx1 : ‖(x : K)‖ ≤ 1 := (mem_unitBallRing (x : K)).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx1 fun h1 => hnu ?_
    have hx0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : K)⁻¹ ∈ unitBallRing K := by
      rw [mem_unitBallRing, norm_inv, h1, inv_one]
    have hm : x * ⟨(x : K)⁻¹, hinv⟩ = 1 := Subtype.ext (by simp [hx0])
    exact ⟨⟨x, ⟨(x : K)⁻¹, hinv⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · intro hlt hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h := congrArg (fun t : unitBallRing K => ‖(t : K)‖) hy
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, norm_mul, norm_one] at h
    have hy1 : ‖(y : K)‖ ≤ 1 := (mem_unitBallRing (y : K)).1 y.2
    nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]

theorem infinite_residues {K : Type*} [NormedField K] [IsUltrametricDist K] (K₀ : Subfield K)
    (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) :
    {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}.Infinite := by
  classical
  intro hfin
  have hrep : ∀ y ∈ {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
      (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y},
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y :=
    fun y hy => hy
  choose! r hr using hrep
  unfold ResidueFieldInfiniteOn at hK₀
  obtain ⟨x, hxK, hx1, hxs⟩ := hK₀ (insert 0 (hfin.toFinset.image fun y => (r y : K)))
  have hx0 : 1 ≤ ‖x‖ := by simpa using hxs 0 (Finset.mem_insert_self _ _)
  have hxn : ‖x‖ = 1 := le_antisymm hx1 hx0
  let xb : unitBallRing K := ⟨x, (mem_unitBallRing x).2 hx1⟩
  have hmem : IsLocalRing.residue _ xb ∈ {y : IsLocalRing.ResidueField (unitBallRing K) |
      ∃ x : unitBallRing K, (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y} :=
    ⟨xb, hxK, hxn, rfl⟩
  obtain ⟨-, -, hreq⟩ := hr _ hmem
  have h0 : IsLocalRing.residue _ (xb - r (IsLocalRing.residue _ xb)) = 0 := by
    rw [map_sub, hreq, sub_self]
  rw [residue_eq_zero_iff_norm_lt_one] at h0
  have h0' : ‖x - (r (IsLocalRing.residue _ xb) : K)‖ < 1 := by simpa [xb] using h0
  have h1 := hxs (r (IsLocalRing.residue _ xb) : K)
    (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, rfl⟩))
  linarith

theorem exists_torus_point_one_le_norm_sum {K : Type*} [NormedField K] [IsUltrametricDist K]
    (K₀ : Subfield K) (hK₀ : ResidueFieldInfiniteOn (K₀ : Set K)) {n : ℕ}
    (F : Finset (Fin n → ℤ)) (a : (Fin n → ℤ) → K) (ha : ∀ χ, ‖a χ‖ ≤ 1)
    (χ₀ : Fin n → ℤ) (hχ₀ : χ₀ ∈ F) (ha₀ : ‖a χ₀‖ = 1) :
    ∃ τ : Fin n → K, (∀ i, τ i ∈ K₀ ∧ ‖τ i‖ = 1) ∧
      1 ≤ ‖∑ χ ∈ F, a χ * ∏ i, τ i ^ χ i‖ := by
  classical
  let N : ℕ := ∑ χ ∈ F, ∑ i, (χ i).natAbs
  have hN : ∀ χ ∈ F, ∀ i, 0 ≤ χ i + N := by
    intro χ hχ i
    have h1 : (χ i).natAbs ≤ ∑ j, (χ j).natAbs :=
      Finset.single_le_sum (f := fun j => (χ j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ∑ j, (χ j).natAbs ≤ N :=
      Finset.single_le_sum (f := fun χ : Fin n → ℤ => ∑ j, (χ j).natAbs)
        (fun _ _ => Nat.zero_le _) hχ
    omega
  let e : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun χ =>
    Finsupp.equivFunOnFinite.symm (fun i => (χ i + N).toNat)
  have he : ∀ χ ∈ F, ∀ χ' ∈ F, e χ = e χ' → χ = χ' := by
    intro χ hχ χ' hχ' h
    funext i
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h3
    have h1 := hN χ hχ i
    have h2 := hN χ' hχ' i
    omega
  let aO : (Fin n → ℤ) → unitBallRing K := fun χ => ⟨a χ, (mem_unitBallRing _).2 (ha χ)⟩
  let P : MvPolynomial (Fin n) (unitBallRing K) := ∑ χ ∈ F, monomial (e χ) (aO χ)
  have hcoeff : AddMonoidAlgebra.coeff P (e χ₀) = aO χ₀ := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem χ₀ hχ₀]
    · simp
    · intro χ hχ hne
      rw [ite_eq_right]
      exact fun h => hne (he χ hχ χ₀ hχ₀ h)
  have hQ : MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P ≠ 0 := by
    intro h0
    have h4 := congrArg (AddMonoidAlgebra.coeff · (e χ₀)) h0
    rw [coeff_map, hcoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      residue_eq_zero_iff_norm_lt_one] at h4
    exact absurd ha₀ (ne_of_lt h4)
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ Set.pi Set.univ (fun _ : Fin n =>
      {y : IsLocalRing.ResidueField (unitBallRing K) | ∃ x : unitBallRing K,
        (x : K) ∈ K₀ ∧ ‖(x : K)‖ = 1 ∧ IsLocalRing.residue _ x = y}),
      eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ (funext_set _ (fun _ => infinite_residues K₀ hK₀) (fun x hx => by
      rw [hcon x hx, map_zero]))
  choose σ hσK hσ1 hσr using fun i => hy i (Set.mem_univ i)
  refine ⟨fun i => (σ i : K), fun i => ⟨hσK i, hσ1 i⟩, ?_⟩
  have hr : IsLocalRing.residue (unitBallRing K) (eval σ P) ≠ 0 := by
    have hy' : y = fun i => IsLocalRing.residue (unitBallRing K) (σ i) :=
      funext fun i => (hσr i).symm
    have h5 : eval y (MvPolynomial.map (IsLocalRing.residue (unitBallRing K)) P) =
        IsLocalRing.residue (unitBallRing K) (eval σ P) := by
      rw [eval_map, hy', MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, hom_eval₂,
        RingHom.comp_id]
    rwa [h5] at hyne
  have hge : 1 ≤ ‖((eval σ P : unitBallRing K) : K)‖ :=
    not_lt.1 fun h => hr ((residue_eq_zero_iff_norm_lt_one _).2 h)
  have hσ0 : ∀ i, (σ i : K) ≠ 0 := fun i h => by
    have h6 := hσ1 i
    rw [h, norm_zero] at h6
    exact zero_ne_one h6
  have hval : ((eval σ P : unitBallRing K) : K) =
      ∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ (χ i + N).toNat := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, eval_monomial]
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp [e, aO]
  have hterm : ∀ χ ∈ F, ∏ i, (σ i : K) ^ (χ i + N).toNat =
      (∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    intro χ hχ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN χ hχ i), zpow_add₀ (hσ0 i), zpow_natCast]
  have hsum : ((eval σ P : unitBallRing K) : K) =
      (∑ χ ∈ F, a χ * ∏ i, (σ i : K) ^ χ i) * ∏ i, (σ i : K) ^ N := by
    rw [hval, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hterm χ hχ, mul_assoc]
  have hnorm1 : ‖∏ i, (σ i : K) ^ N‖ = 1 := by
    rw [norm_prod]
    simp [norm_pow, hσ1]
  rw [hsum, norm_mul, hnorm1, mul_one] at hge
  exact hge

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.ExpTorusMeanLeL2OfLex
section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset

theorem exp_torus_mean_le_l2_of_lex {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by
  classical
  set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef
  have hsQ : s ∉ Q.support := fun h => lt_irrefl _ (hQ s h)
  have hQs : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hsQ
  have hPs : P.coeff s = 1 := by
    rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]
  have hP0 : P ≠ 0 := fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs
  have hsupp : s ∈ P.support := by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero
  have hlex : Real.log ‖P.coeff s‖ ≤ torusMean P := by
    apply hLex ι P s hsupp
    intro t ht hts
    have htQ : t ∈ Q.support := by
      by_contra h
      have h0 : P.coeff t = 0 := by
        rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts),
          MvPolynomial.notMem_support_iff.mp h, sub_zero]
      exact (MvPolynomial.mem_support_iff.mp ht) h0
    obtain ⟨i, h1, h2⟩ := hQ t htQ
    exact ⟨i, h1, h2⟩
  rw [hPs, norm_one, Real.log_one] at hlex
  have hFP : F * P ≠ 0 := mul_ne_zero hF hP0
  have hmul := (hBasic ι).2.1 F P hF hP0
  have hL := (hL2 ι (F * P)).1 hFP
  have hpos : 0 < polyL2 (F * P) := by
    unfold polyL2
    apply Real.sqrt_pos.mpr
    obtain ⟨t, hne⟩ := MvPolynomial.ne_zero_iff.mp hFP
    have ht : t ∈ (F * P).support := MvPolynomial.mem_support_iff.mpr hne
    calc (0 : ℝ) < ‖(F * P).coeff t‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      _ ≤ _ := Finset.single_le_sum (f := fun s => ‖(F * P).coeff s‖ ^ 2)
          (fun _ _ => by positivity) ht
  calc Real.exp (torusMean F) ≤ Real.exp (torusMean (F * P)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ polyL2 (F * P) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hL

def coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) : MvPolynomial ι ℂ →ₗ[ℂ] EuclideanSpace ℂ T where
  toFun P := WithLp.toLp 2 fun t : T => P.coeff t
  map_add' P Q := by ext t; simp
  map_smul' c P := by ext t; simp

theorem coeffVec_apply {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ) (t : T) :
    coeffVec T P t = P.coeff t := rfl

theorem norm_coeffVec {ι : Type*} (T : Finset (ι →₀ ℕ)) (P : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : ‖coeffVec T P‖ = polyL2 P := by
  classical
  rw [EuclideanSpace.norm_eq, polyL2]
  congr 1
  simp only [coeffVec_apply]
  rw [Finset.sum_coe_sort T (fun t => ‖P.coeff t‖ ^ 2)]
  exact (Finset.sum_subset hP (fun t _ ht => by
    rw [MvPolynomial.notMem_support_iff.mp ht, norm_zero]; ring)).symm

theorem polyInner_eq_inner {ι : Type*} (T : Finset (ι →₀ ℕ)) (P Q : MvPolynomial ι ℂ)
    (hP : P.support ⊆ T) : polyInner P Q = inner ℂ (coeffVec T Q) (coeffVec T P) := by
  classical
  rw [PiLp.inner_apply]
  simp only [coeffVec_apply, RCLike.inner_apply, polyInner]
  rw [Finset.sum_coe_sort T (fun t => P.coeff t * (starRingEnd ℂ) (Q.coeff t))]
  exact Finset.sum_subset hP (fun t _ ht => by rw [MvPolynomial.notMem_support_iff.mp ht, zero_mul])

theorem exists_lex_enum {ι : Type*} [LinearOrder ι] (S : Finset (ι →₀ ℕ)) :
    ∃ m : Fin S.card → (ι →₀ ℕ), (∀ k, m k ∈ S) ∧ Function.Injective m ∧
      ∀ j k, j < k → toLex (m k) < toLex (m j) := by
  classical
  let S' : Finset (Lex (ι →₀ ℕ)) := S.map toLex.toEmbedding
  have hc : S'.card = S.card := Finset.card_map _
  let f := S'.orderEmbOfFin hc
  refine ⟨fun k => ofLex (f (Fin.rev k)), ?_, ?_, ?_⟩
  · intro k
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (S'.orderEmbOfFin_mem hc (Fin.rev k))
    have : ofLex (f (Fin.rev k)) = a := by rw [← he]; rfl
    show ofLex (f (Fin.rev k)) ∈ S
    rw [this]; exact ha
  · intro a b h
    exact Fin.rev_injective (f.injective h)
  · intro j k hjk
    show f (Fin.rev k) < f (Fin.rev j)
    exact f.strictMono (Fin.rev_lt_rev.mpr hjk)

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
section
namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

section Gauss

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _

theorem gauss_abs_le_of_coeff_le (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2

theorem gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]

theorem gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)

theorem finite_place_sum_le {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)

theorem finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  classical
  have hGf := gauss_abs_pos_of_ne_zero w f hf
  have hGg := gauss_abs_pos_of_ne_zero w g hg
  apply le_antisymm
  · refine gauss_abs_le_of_coeff_le w _ (mul_nonneg hGf.le hGg.le) fun u => ?_
    rw [MvPolynomial.coeff_mul]
    refine finite_place_sum_le w _ _ (mul_nonneg hGf.le hGg.le) fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul (coeff_le_gauss_abs w f _) (coeff_le_gauss_abs w g _) (apply_nonneg w _) hGf.le
  ·
    set Sf := f.support.filter (fun s => w (f.coeff s) = gaussAbs w f)
    set Sg := g.support.filter (fun s => w (g.coeff s) = gaussAbs w g)
    have hSf : Sf.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    have hSg : Sg.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w g hg
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image Sf (fun s => m.toSyn s) hSf
    obtain ⟨t0, ht0, ht0max⟩ := Finset.exists_max_image Sg (fun s => m.toSyn s) hSg
    have hfs0 : w (f.coeff s0) = gaussAbs w f := (Finset.mem_filter.1 hs0).2
    have hgt0 : w (g.coeff t0) = gaussAbs w g := (Finset.mem_filter.1 ht0).2
    have hbigf : ∀ s, m.toSyn s0 < m.toSyn s → w (f.coeff s) < gaussAbs w f := by
      intro s hs
      refine lt_of_le_of_ne (coeff_le_gauss_abs w f s) fun heq => ?_
      have hmem : s ∈ Sf := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGf.ne heq
      exact absurd (hs0max s hmem) (not_le.2 hs)
    have hbigg : ∀ t, m.toSyn t0 < m.toSyn t → w (g.coeff t) < gaussAbs w g := by
      intro t ht
      refine lt_of_le_of_ne (coeff_le_gauss_abs w g t) fun heq => ?_
      have hmem : t ∈ Sg := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGg.ne heq
      exact absurd (ht0max t hmem) (not_le.2 ht)
    have hmemu : (s0, t0) ∈ Finset.HasAntidiagonal.antidiagonal (s0 + t0) := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hrest : w (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (s0 + t0)).erase (s0, t0),
        f.coeff x.1 * g.coeff x.2) < gaussAbs w f * gaussAbs w g := by
      refine finite_place_sum_lt w _ _ (mul_pos hGf hGg) fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.1 hx
      have hsum : x.1 + x.2 = s0 + t0 := Finset.HasAntidiagonal.mem_antidiagonal.1 hxmem
      have hsyn : m.toSyn x.1 + m.toSyn x.2 = m.toSyn s0 + m.toSyn t0 := by
        rw [← map_add (f := _), ← map_add (f := _), hsum]
      rw [map_mul]
      rcases lt_trichotomy (m.toSyn x.1) (m.toSyn s0) with h1 | h1 | h1
      · have h2 : m.toSyn t0 < m.toSyn x.2 := by
          by_contra h2
          have := add_lt_add_of_lt_of_le h1 (not_lt.1 h2)
          rw [hsyn] at this
          exact lt_irrefl _ this
        calc w (f.coeff x.1) * w (g.coeff x.2) ≤ gaussAbs w f * w (g.coeff x.2) :=
              mul_le_mul_of_nonneg_right (coeff_le_gauss_abs w f _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_left (hbigg _ h2) hGf
      · exfalso
        have e1 : x.1 = s0 := m.toSyn.injective h1
        have e2 : x.2 = t0 := by
          rw [e1] at hsum
          exact add_left_cancel hsum
        exact hxne (Prod.ext e1 e2)
      · calc w (f.coeff x.1) * w (g.coeff x.2) ≤ w (f.coeff x.1) * gaussAbs w g :=
              mul_le_mul_of_nonneg_left (coeff_le_gauss_abs w g _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_right (hbigf _ h1) hGg
    have hcoeff : w ((f * g).coeff (s0 + t0)) = gaussAbs w f * gaussAbs w g := by
      rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmemu]
      rw [finite_place_add_eq_of_lt w _ _ (by rwa [map_mul, hfs0, hgt0]), map_mul, hfs0, hgt0]
    rw [← hcoeff]
    exact coeff_le_gauss_abs w _ _

theorem gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg

end Gauss

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.NormValuationEqFactorization
section
namespace ReciprocityTheory.MultiplicativeHeights

open Module UniqueFactorizationMonoid

theorem normValuation_eq_factorization (hC1 : NormLengthStatement) : NormOrdStatement := by
  classical
  intro O B _ _ _ _ _ _ _ _ _ g hg
  rw [hC1 O B g hg]
  set I : Ideal B := Ideal.span {g} with hIdef
  have hI : I ≠ ⊥ := by rwa [Ne, hIdef, Ideal.span_singleton_eq_bot]
  have hfac : UniqueFactorizationMonoid.factors I = normalizedFactors I :=
    UniqueFactorizationMonoid.factors_eq_normalizedFactors I
  have hmax : ∀ P ∈ UniqueFactorizationMonoid.factors I, P.IsMaximal ∧ P ≠ ⊥ := by
    intro P hP
    have hpr : Prime P := UniqueFactorizationMonoid.prime_of_factor P hP
    exact ⟨(Ideal.isPrime_of_prime hpr).isMaximal hpr.ne_zero, hpr.ne_zero⟩
  let φ := IsDedekindDomain.quotientEquivPiFactors hI
  let ψ : (B ⧸ I) ≃ₗ[O] ((P : (UniqueFactorizationMonoid.factors I).toFinset) →
      B ⧸ (P : Ideal B) ^ Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) :=
    { φ with
      map_smul' := by
        intro o x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        change φ (Ideal.Quotient.mk I (o • b)) = o • φ (Ideal.Quotient.mk I b)
        rw [IsDedekindDomain.quotientEquivPiFactors_mk, IsDedekindDomain.quotientEquivPiFactors_mk]
        rfl }
  rw [ψ.length_eq, Module.length_pi_of_fintype]
  have hterm : ∀ P : (UniqueFactorizationMonoid.factors I).toFinset,
      Module.length O (B ⧸ (P : Ideal B) ^
        Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I)) =
      ((Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors I) *
        (P : Ideal B).inertiaDeg O : ℕ) : ℕ∞) := by
    intro P
    obtain ⟨hPm, hP0⟩ := hmax P (Multiset.mem_toFinset.mp P.2)
    rw [normOrd_length_pow O B _ hP0, normOrd_length_residue O B]
    norm_cast
  rw [Finset.sum_congr rfl (fun P _ => hterm P), ← Nat.cast_sum]
  congr 1
  rw [← hfac, Finset.sum_coe_sort (UniqueFactorizationMonoid.factors I).toFinset
    (fun P => Multiset.count P (UniqueFactorizationMonoid.factors I) * P.inertiaDeg O)]
  rw [finsum_eq_sum_of_support_subset (s := (UniqueFactorizationMonoid.factors I).toFinset.subtype
    (fun Q : Ideal B => Q.IsMaximal)) _ ?sup]
  · rw [Finset.sum_subtype_eq_sum_filter (fun Q : Ideal B =>
        Q.inertiaDeg O * Multiset.count Q (UniqueFactorizationMonoid.factors I)),
      Finset.filter_true_of_mem]
    · exact Finset.sum_congr rfl fun P _ => mul_comm _ _
    · intro P hP
      exact (hmax P (Multiset.mem_toFinset.mp hP)).1
  case sup =>
    intro Q hQ
    rw [Function.mem_support] at hQ
    rw [Finset.mem_coe, Finset.mem_subtype, Multiset.mem_toFinset]
    by_contra hn
    exact hQ (by rw [Multiset.count_eq_zero.mpr hn, mul_zero])

end ReciprocityTheory.MultiplicativeHeights
end

