module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)


omit [CharZero Ω] in
theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]


omit [CharZero Ω] in
theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric


open PullFormsGeneric in
theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullGradedAlgebraic

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

theorem blockDeg_add (m m' : (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (m + m') k = blockDeg m k + blockDeg m' k := by
  simp [blockDeg, Finset.sum_add_distrib]

theorem blockDeg_sum {α : Type} (s : Finset α) (f : α → (Σ k, ι k) →₀ ℕ) (k : K) :
    blockDeg (∑ a ∈ s, f a) k = ∑ a ∈ s, blockDeg (f a) k := by
  simp only [blockDeg, Finsupp.finsetSum_apply]
  exact Finset.sum_comm

theorem blockDeg_single [DecidableEq K] (s : Σ k, ι k) (a : ℕ) (k' : K) :
    blockDeg (Finsupp.single s a) k' = if k' = s.1 then a else 0 := by
  classical
  obtain ⟨k0, i0⟩ := s
  simp only [blockDeg]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h').2).symm
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

theorem isMultiHomog_monomial {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial m (1 : ℚ)) b := by
  intro m' hm' k
  rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm'
  subst hm'
  exact h k

theorem le_of_blockDeg {m : (Σ k, ι k) →₀ ℕ} {b : K → ℕ} (h : ∀ k, blockDeg m k = b k)
    (v : Σ k, ι k) : m v ≤ b v.1 := by
  rw [← h v.1, blockDeg]
  exact Finset.single_le_sum (f := fun i => m ⟨v.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)

def diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) : (Σ k, ι k) →₀ ℕ := ∑ k, Finsupp.single ⟨k, c k⟩ (b k)

theorem blockDeg_diagMono [Fintype K] (c : ∀ k, ι k) (b : K → ℕ) (k : K) : blockDeg (diagMono c b) k = b k := by
  classical
  rw [diagMono, blockDeg_sum, Finset.sum_eq_single k]
  · rw [blockDeg_single, if_pos rfl]
  · intro k' _ hk'
    rw [blockDeg_single, if_neg (Ne.symm hk')]
  · simp

omit [∀ k, Fintype (ι k)] in
theorem aeval_diagMono_ne_zero [Fintype K] {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℕ) : aeval y (monomial (diagMono c b) (1 : ℚ)) ≠ 0 := by
  classical
  rw [diagMono, monomial_sum_one, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by
    rw [← X_pow_eq_monomial, map_pow, aeval_X]
    exact pow_ne_zero _ (hc k)

end PullGradedAlgebraic


open PullGradedAlgebraic in
theorem PullGradedAlgebraic.proof : PullGradedAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L d₀ hy he hL hgr p q hpq
  classical
  choose c hc using hy
  obtain ⟨j₀, hw⟩ : ∃ j₀, aeval y (L j₀) ≠ 0 := by
    obtain ⟨a, -, ha⟩ := hgr d₀ (monomial (diagMono c d₀) 1)
      (isMultiHomog_monomial (blockDeg_diagMono c d₀)) (fun _ => le_rfl)
    by_contra h
    simp only [not_exists, not_not] at h
    rw [Finset.sum_eq_zero (fun j _ => by rw [h j, mul_zero])] at ha
    exact aeval_diagMono_ne_zero y c hc d₀ ha
  set F := pullField y L
  set w := aeval y (L j₀)
  set n₀ := ∑ k, d₀ k
  set T : Set Ω := {x | ∃ n ≤ n₀, ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, blockDeg m k = n * e k) ∧
    x = aeval y (monomial m (1 : ℚ)) / w ^ n} with hT
  set W : Submodule F Ω := Submodule.span F T with hW
  have hratio : ∀ j, aeval y (L j) / w ∈ F := fun j =>
    IntermediateField.subset_adjoin _ _ ⟨j, j₀, hw, rfl⟩
  have claim : ∀ n (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g (fun k => n * e k) →
      aeval y g / w ^ n ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro g hg
    by_cases hn : n ≤ n₀
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [g.as_sum, map_sum, Finset.sum_div]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hmono, map_smul, smul_div_assoc]
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨n, hn, m, fun k => hg m hm k, rfl⟩)
    · replace hn := Nat.lt_of_not_le hn
      obtain ⟨a, ha, hga⟩ := hgr (fun k => n * e k) g hg (fun k => by
        have h1 : d₀ k ≤ n₀ := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h2 := Nat.mul_le_mul_left n (he k)
        omega)
      have hdeg : (fun k => n * e k) - e = fun k => (n - 1) * e k := by
        funext k
        show n * e k - e k = (n - 1) * e k
        rw [Nat.sub_one_mul]
      rw [hga, Finset.sum_div]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 := ih (n - 1) (by omega) (a j) (by rw [← hdeg]; exact ha j)
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hj : aeval y (a j) * aeval y (L j) / w ^ (n' + 1) =
          (⟨aeval y (L j) / w, hratio j⟩ : F) • (aeval y (a j) / w ^ (n' + 1 - 1)) := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, Nat.add_sub_cancel]
        field_simp
        ring
      rw [hj]
      exact W.smul_mem _ h1
  have hTfin : T.Finite := by
    let B : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun v => n₀ * e v.1)
    refine (((Set.finite_Iic n₀).prod (Set.finite_Iic B)).image
      (fun nm : ℕ × ((Σ k, ι k) →₀ ℕ) => aeval y (monomial nm.2 (1 : ℚ)) / w ^ nm.1)).subset ?_
    rintro x ⟨n, hn, m, hm, rfl⟩
    refine ⟨(n, m), ⟨hn, fun v => ?_⟩, rfl⟩
    show m v ≤ n₀ * e v.1
    exact (le_of_blockDeg hm v).trans (Nat.mul_le_mul_right _ hn)
  have hWfg : W.FG := ⟨hTfin.toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hW0 : W ≠ ⊥ := by
    intro h
    have h1 : (1 : Ω) ∈ W := Submodule.subset_span ⟨0, Nat.zero_le _, 0, fun k => by simp [blockDeg], by simp⟩
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hint : ∀ n (m : (Σ k, ι k) →₀ ℕ), (∀ k, blockDeg m k = n * e k) →
      IsIntegral F (aeval y (monomial m (1 : ℚ)) / w ^ n) := by
    intro n m hm
    refine isIntegral_of_smul_mem_submodule W hW0 hWfg _ fun z hz => ?_
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n', -, m', hm', rfl⟩ := hx
      have hmul : monomial (m + m') (1 : ℚ) = monomial m 1 * monomial m' 1 := by
        rw [monomial_mul, one_mul]
      have hx : (aeval y (monomial m (1 : ℚ)) / w ^ n) • (aeval y (monomial m' (1 : ℚ)) / w ^ n') =
          aeval y (monomial (m + m') (1 : ℚ)) / w ^ (n + n') := by
        rw [smul_eq_mul, hmul, map_mul, pow_add]
        field_simp
      rw [hx]
      exact claim _ _ (isMultiHomog_monomial fun k => by rw [blockDeg_add, hm, hm', add_mul])
    | zero => simp
    | add x x' _ _ hx hx' => rw [smul_add]; exact W.add_mem hx hx'
    | smul a x _ hx => rw [smul_comm]; exact W.smul_mem a hx
  set n := n₀ + 1
  set μ := diagMono c (fun k' => n * e k' - if k' = p.1 then 1 else 0)
  have hdeg : ∀ s : Σ k, ι k, s.1 = p.1 → ∀ k', blockDeg (Finsupp.single s 1 + μ) k' = n * e k' := by
    intro s hs k'
    rw [blockDeg_add, blockDeg_diagMono, blockDeg_single, hs]
    have h1 := Nat.mul_le_mul (show 1 ≤ n by omega) (he k')
    generalize n * e k' = t at *
    split_ifs <;> omega
  have hval : ∀ s : Σ k, ι k, aeval y (monomial (Finsupp.single s 1 + μ) (1 : ℚ)) =
      y s * aeval y (monomial μ (1 : ℚ)) := by
    intro s
    rw [monomial_single_add, pow_one, map_mul, aeval_X]
  have hμ0 : aeval y (monomial μ (1 : ℚ)) ≠ 0 := aeval_diagMono_ne_zero y c hc _
  have hr : ∀ s : Σ k, ι k, s.1 = p.1 →
      y s * aeval y (monomial μ (1 : ℚ)) / w ^ n ∈ algebraicClosure F Ω := fun s hs => by
    rw [mem_algebraicClosure_iff, ← hval s]
    exact (hint n _ (hdeg s hs)).isAlgebraic
  have key : y p * aeval y (monomial μ (1 : ℚ)) / w ^ n / (y q * aeval y (monomial μ (1 : ℚ)) / w ^ n) =
      y p / y q := by
    rw [div_div_div_cancel_right₀ (pow_ne_zero _ hw), mul_div_mul_right _ _ hμ0]
  rw [← key, ← mem_algebraicClosure_iff]
  exact (algebraicClosure F Ω).div_mem (hr p rfl) (hr q hpq.symm)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphImage
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem VeroneseGraphImage.proof : VeroneseGraphImage.Statement := by
  intro D

  let f₀ : MRing (GlobalTheory (Fin (D + 1))) →+* Veronese.Fld D :=
    (Veronese.polyMap D).comp
      (rename (fun p : Σ _ : Unit, Fin (D + 1) => p.2) : MvPolynomial _ ℤ →ₐ[ℤ] _).toRingHom
  have hf₀ : Function.Injective f₀ := by
    refine (Veronese.polyMap_injective D).comp (rename_injective _ ?_)
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  have hf₀X : ∀ i, f₀ (X ⟨(), i⟩) = Veronese.t D i := by
    intro i
    simp [f₀, Veronese.polyMap, Veronese.t]
  let P : Ideal (MRing (GlobalTheory (Fin (D + 1)))) := ⊥
  let φ : MRing (GlobalTheory (Fin (D + 1))) ⧸ P →+* Veronese.Fld D :=
    Ideal.Quotient.lift P f₀ fun a ha => by
      rw [Ideal.mem_bot] at ha
      simp [ha]
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a = 0 := hf₀ (by rw [map_zero]; exact (Ideal.Quotient.lift_mk _ _ _).symm.trans ha)
    rw [this, map_zero]

  let ψ : Polynomial (Veronese.Fld D) →+* MvPolynomial Unit (Veronese.Fld D) :=
    Polynomial.eval₂RingHom C (X ())
  let ev : MvPolynomial Unit (Veronese.Fld D) →+* Polynomial (Veronese.Fld D) :=
    eval₂Hom Polynomial.C fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p
  let G : MRing (GlobalTheory (Veronese.Idx D)) →+* MvPolynomial Unit (Veronese.Fld D) :=
    (MvPolynomial.map φ).comp ((graphMap P (Veronese.forms D)).comp
      (rename (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) :
        MRing (GlobalTheory (Veronese.Idx D)) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ (Veronese.x D) f) := by
    have h : G = ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun
          (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ (Veronese.x D)).toRingHom).comp C)) n
      · rintro ⟨u, q⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_X]
        rw [show (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)) ⟨(), q⟩) = ⟨Sum.inr (), q⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk P (Veronese.forms D ⟨(), q⟩)) = Veronese.x D ⟨(), q⟩ from by
          rw [Ideal.Quotient.lift_mk]
          simp only [Veronese.forms, map_mul, hf₀X, Veronese.x]]
        simp [ψ]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap P (Veronese.forms D)) ↔
    f ∈ RingHom.ker (coneMap ℤ (Veronese.x D))
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap P (Veronese.forms D) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ (Veronese.x D) f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

