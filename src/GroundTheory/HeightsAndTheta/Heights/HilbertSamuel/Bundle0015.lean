module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module

noncomputable section

theorem card_le_of_separated_of_norm_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (s : Finset W) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ r) (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → lam ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 * r / lam) ^ finrank ℝ W := by
  classical
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  set μ : Measure W := (Module.finBasis ℝ W).addHaar with hμ
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set W) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    exact hsep w hw w' hw' hne
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : W) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hxw
    calc ‖x‖ = ‖w + (x - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith [hs w hw]
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ finrank ℝ W := by positivity
  have key : (1 + 2 * r / lam) ^ finrank ℝ W = ((r + lam / 2) / (lam / 2)) ^ finrank ℝ W := by
    congr 1
    field_simp
    ring
  rw [key, div_pow, le_div_iff₀ hpos]
  exact hle'

theorem finrank_span_le_finrank_int {V : Type*} [AddCommGroup V] [Module ℝ V]
    (La : Submodule ℤ V) [Module.Finite ℤ La] :
    (La : Set V) ⊆ Submodule.span ℝ (La : Set V) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (La : Set V)) ∧
      finrank ℝ (Submodule.span ℝ (La : Set V)) ≤ finrank ℤ La := by
  classical
  have : HasUniqueDiv V := HasUniqueDiv.of_isTorsionFree ℝ V
  have : IsAddTorsionFree V := inferInstance
  have : Module.IsTorsionFree ℤ La := inferInstance
  have : Module.Free ℤ La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ La
  let f : Module.Free.ChooseBasisIndex ℤ La → V := fun i => (B i : V)
  have hspan : Submodule.span ℝ (La : Set V) = Submodule.span ℝ (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      have hx'' : x = ∑ i, B.repr ⟨x, hx⟩ i • f i := by
        conv_lhs => rw [show x = ((⟨x, hx⟩ : La) : V) from rfl, ← B.sum_repr ⟨x, hx⟩]
        simp only [Submodule.coe_sum, Submodule.coe_smul, f]
      rw [SetLike.mem_coe, hx'']
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (B i).2
  refine ⟨Submodule.subset_span, ?_, ?_⟩
  · rw [hspan]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  · rw [hspan, finrank_eq_card_basis B]
    exact finrank_range_le_card f

theorem Packing.proof : Packing.Statement := by
  classical
  intro V _ _ La _ S b hb hmem hnorm hsep
  obtain ⟨hsub, hfd, hdim⟩ := finrank_span_le_finrank_int La
  set W := Submodule.span ℝ (La : Set V) with hW
  have hR0 : (0 : ℝ) ≤ Module.finrank ℤ La * (b + Real.log 3) := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]; exact hR0
  let T : Finset W := S.subtype (· ∈ W)
  have hTcard : T.card = S.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem]
    exact fun s hs => hsub (hmem s hs)
  have hδ : 0 < Real.exp (-b) := Real.exp_pos _
  have hbound := card_le_of_separated_of_norm_le T hδ zero_le_one
    (fun x hx => by
      rw [Finset.mem_subtype] at hx
      rw [Submodule.coe_norm]; exact hnorm _ hx)
    (fun x hx y hy hxy => by
      rw [Finset.mem_subtype] at hx hy
      rw [Submodule.coe_norm, Submodule.coe_sub]
      exact hsep _ hx _ hy (fun h => hxy (Subtype.ext h)))
  rw [hTcard] at hbound
  have hq : 1 + 2 * 1 / Real.exp (-b) ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    rw [Real.exp_neg, mul_one, div_inv_eq_mul]
    linarith
  have h3 : 1 ≤ 3 * Real.exp b := by
    have h1 : 1 ≤ Real.exp b := Real.one_le_exp hb
    linarith
  have hcard : (S.card : ℝ) ≤ (3 * Real.exp b) ^ Module.finrank ℤ La :=
    hbound.trans ((pow_le_pow_left₀ (by positivity) hq _).trans (pow_le_pow_right₀ h3 hdim))
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hpos
  calc Real.log S.card ≤ Real.log ((3 * Real.exp b) ^ Module.finrank ℤ La) :=
        Real.log_le_log hSpos hcard
    _ = Module.finrank ℤ La * (b + Real.log 3) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (Real.exp_pos b).ne', Real.log_exp]
        ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Cardinal

noncomputable section

theorem SegreDimGe.proof : SegreDimGe.Statement := by
  intro F _ K _ _ _ ι _ q e hq hdim
  have := hq.isPrime
  let π : MRing ι F →ₐ[F] MRing ι F ⧸ q := Ideal.Quotient.mkₐ F q
  let φ : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F ⧸ q := π.comp (segreMap F)
  let R' : Subalgebra F (MRing ι F ⧸ q) := φ.range
  choose i hi using hq.relevant
  let x : K → MRing ι F ⧸ q := fun k => π (X ⟨k, i k⟩)
  have hx0 : ∀ k, x k ≠ 0 := fun k h =>
    hi k (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [x, π, Ideal.Quotient.mkₐ_eq_mk] using h))

  have hkey : ∀ k (j : ι k), (∏ l ∈ Finset.univ.erase k, x l) * π (X ⟨k, j⟩) =
      φ (X ⟨(), Function.update i k j⟩) := by
    intro k j
    rw [AlgHom.comp_apply, segreMap_X, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  let k0 : K := Classical.arbitrary K
  let s : Set (MRing ι F ⧸ q) := x '' ↑(Finset.univ.erase k0)
  let B : Subalgebra R' (MRing ι F ⧸ q) := Algebra.adjoin R' s
  have hR'B : ∀ a ∈ R', IsAlgebraic B a := fun a ha =>
    isAlgebraic_algebraMap (⟨a, Subalgebra.algebraMap_mem B (⟨a, ha⟩ : R')⟩ : B)
  have hsB : ∀ l, l ≠ k0 → IsAlgebraic B (x l) := fun l hl =>
    isAlgebraic_algebraMap (⟨x l, Algebra.subset_adjoin
      ⟨l, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), rfl⟩⟩ : B)
  have hgen : ∀ k, (∀ l, l ≠ k → IsAlgebraic B (x l)) → ∀ j : ι k, IsAlgebraic B (π (X ⟨k, j⟩)) := by
    intro k hk j
    have hy : IsAlgebraic B (∏ l ∈ Finset.univ.erase k, x l) :=
      Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) isAlgebraic_one
        fun l hl => hk l (Finset.ne_of_mem_erase hl)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ?_) hy ?_
    · exact Finset.prod_ne_zero_iff.mpr fun l _ => hx0 l
    · rw [hkey]
      exact hR'B _ ⟨_, rfl⟩
  have hall : ∀ l, IsAlgebraic B (x l) := by
    intro l
    by_cases hl : l = k0
    · subst hl
      exact hgen _ hsB (i _)
    · exact hsB l hl
  have hA : ∀ a : MRing ι F ⧸ q, IsAlgebraic B a := by
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective F q a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.algHom_C]
      exact hR'B _ (R'.algebraMap_mem c)
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p v hp => rw [map_mul]; exact hp.mul (hgen v.1 (fun l _ => hall l) v.2)
  have : Algebra.IsAlgebraic B (MRing ι F ⧸ q) := ⟨hA⟩
  have htop : Algebra.trdeg R' (MRing ι F ⧸ q) ≤ #s := Algebra.IsAlgebraic.trdeg_le_cardinalMk R' s
  have hs : #s ≤ (Fintype.card K - 1 : ℕ) := by
    refine Cardinal.mk_image_le.trans ?_
    simp
  have : FaithfulSMul F R' :=
    (faithfulSMul_iff_algebraMap_injective F R').mpr (algebraMap F R').injective
  have : FaithfulSMul R' (MRing ι F ⧸ q) :=
    ⟨fun {r₁ r₂} h => Subtype.ext (by simpa [Subalgebra.smul_def] using h 1)⟩
  have htower := trdeg_add_eq (A := MRing ι F ⧸ q) F R'

  let g : (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) →ₐ[F] R' :=
    Ideal.Quotient.liftₐ (segrePrime F q) φ.rangeRestrict fun p hp => by
      apply Subtype.ext
      simpa [φ, π, segrePrime, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hp
  have hg : Function.Surjective g := by
    rintro ⟨y, p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have hR'le := trdeg_le_of_surjective g hg
  obtain ⟨n, hn, htn⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing ι F ⧸ q)
  obtain ⟨m, hm, htm⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := F) (A := MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)
  have hne : n = e + Fintype.card K := by
    rw [hn] at hdim
    exact_mod_cast hdim
  have hcard : (n : Cardinal) ≤ (m + (Fintype.card K - 1) : ℕ) := by
    rw [← htn, ← htower, Nat.cast_add, ← htm]
    exact add_le_add hR'le (htop.trans hs)
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hnm : n ≤ m + (Fintype.card K - 1) := by exact_mod_cast hcard
  rw [hm]
  exact_mod_cast (show e + 1 ≤ m by omega)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (F : Type) [Field F]

theorem weight_blockWeight_apply (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) e k = ∑ i, e ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem blockWeight_unit (v : Σ _ : Unit, ∀ k, ι k) :
    blockWeight (fun _ : Unit => ∀ k, ι k) v = fun _ => 1 := by
  funext u
  simp [blockWeight]


omit [∀ k, Fintype (ι k)] in
theorem segreMap_isMultiHomog {m : ℕ} {p : MRing (fun _ : Unit => ∀ k, ι k) F}
    (hp : IsWeightedHomogeneous (blockWeight (fun _ : Unit => ∀ k, ι k)) p (fun _ => m)) :
    IsWeightedHomogeneous (blockWeight ι) (segreMap F p) (fun _ => m) := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add (f := _)]; exact hp.add hq
  | monomial d r hr =>
    have hX : ∀ v : Σ _ : Unit, ∀ k, ι k,
        IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
      intro v
      have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
        (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => blockWeight ι ⟨k, v.2 k⟩)
        (fun k _ => isWeightedHomogeneous_X _ _ _)
      convert h using 1
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    have hsum : ∑ v ∈ d.support, d v = m := by
      have h := congrFun hr ()
      rw [Finsupp.weight_apply, Finsupp.sum] at h
      simpa [blockWeight_unit, Finset.sum_apply] using h
    have hdeg : (∑ v ∈ d.support, d v • (fun _ : K => 1) : K → ℕ) = fun _ => m := by
      funext k
      simp [Finset.sum_apply, hsum]
    unfold segreMap
    rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
    refine IsWeightedHomogeneous.C_mul ?_ r
    rw [← hdeg]
    exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hX v).pow _


omit [DecidableEq K] in
theorem monomial_mem_map_segreMap (m : ℕ) :
    ∀ e : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = m) →
      monomial e (1 : F) ∈ (weightedHomogeneousSubmodule F
        (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map (segreMap F).toLinearMap := by
  classical
  induction m with
  | zero =>
    intro e he
    have he0 : e = 0 := by
      ext ⟨k, i⟩
      exact (Finset.sum_eq_zero_iff.mp (he k)) i (Finset.mem_univ _)
    subst he0
    refine ⟨1, ?_, ?_⟩
    · exact isWeightedHomogeneous_one _ _
    · simp
  | succ m ih =>
    intro e he
    have hne : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => e ⟨k, i⟩) (by rw [he k]; omega)
      exact ⟨i, hi⟩
    choose f hf using hne
    set s : (Σ k, ι k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => if v.2 = f v.1 then 1 else 0) with hs_def
    have hs : ∀ k i, s ⟨k, i⟩ = if i = f k then 1 else 0 := fun k i => by simp [hs_def]
    have hse : s ≤ e := by
      rw [Finsupp.le_def]
      rintro ⟨k, i⟩
      rw [hs]
      split_ifs with h
      · subst h; exact Nat.one_le_iff_ne_zero.mpr (hf k)
      · exact Nat.zero_le _
    have hadd : e - s + s = e := tsub_add_cancel_of_le hse
    have he' : ∀ k, ∑ i, (e - s) ⟨k, i⟩ = m := fun k => by
      have h1 : ∑ i, (e - s) ⟨k, i⟩ + ∑ i, s ⟨k, i⟩ = m + 1 := by
        rw [← Finset.sum_add_distrib, ← he k]
        exact Finset.sum_congr rfl fun i _ => by rw [← Finsupp.add_apply, hadd]
      have h2 : ∑ i, s ⟨k, i⟩ = 1 := by simp [hs]
      omega
    obtain ⟨g, hg, hge⟩ := ih (e - s) he'
    have hsX : monomial s (1 : F) = ∏ k, (X ⟨k, f k⟩ : MRing ι F) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [hs]
    refine ⟨g * X ⟨(), f⟩, ?_, ?_⟩
    · have h := (show IsWeightedHomogeneous _ g _ from hg).mul
        (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ∀ k, ι k)) ⟨(), f⟩)
      rw [blockWeight_unit] at h
      exact h
    · simp only [AlgHom.toLinearMap_apply, map_mul] at hge ⊢
      rw [hge, segreMap_X, ← hsX, monomial_mul, one_mul, hadd]

theorem map_segreMap_weightedHomogeneousSubmodule (m : ℕ) :
    (weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ∀ k, ι k)) (fun _ => m)).map
        (segreMap F).toLinearMap =
      weightedHomogeneousSubmodule F (blockWeight ι) (fun _ => m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact segreMap_isMultiHomog F hp
  · intro p hp
    have hp' : IsWeightedHomogeneous (blockWeight ι) p (fun _ => m) := hp
    clear hp
    induction hp' using IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | monomial d r hr =>
      have hd : ∀ k, ∑ i, d ⟨k, i⟩ = m := fun k => by
        rw [← weight_blockWeight_apply, hr]
      have h := Submodule.smul_mem _ r (monomial_mem_map_segreMap F m d hd)
      rwa [smul_monomial, smul_eq_mul, mul_one] at h

def segreQuotMap (q : Ideal (MRing ι F)) :
    MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q →ₐ[F] MRing ι F ⧸ q :=
  Ideal.quotientMapₐ (I := segrePrime F q) q (segreMap F) fun _ h => h


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreQuotMap_injective (q : Ideal (MRing ι F)) : Function.Injective (segreQuotMap F q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk q (segreMap F x) = 0 at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp ha))

def segreGradedPieceEquiv (q : Ideal (MRing ι F)) (m : ℕ) :
    gradedPiece (segrePrime F q) (fun _ : Unit => m) ≃ₗ[F] gradedPiece q (fun _ : K => m) :=
  have hinj : Function.Injective (segreQuotMap F q).toLinearMap := segreQuotMap_injective F q
  have hmap : (gradedPiece (segrePrime F q) (fun _ : Unit => m)).map (segreQuotMap F q).toLinearMap =
      gradedPiece q (fun _ : K => m) := by
    have hc : (segreQuotMap F q).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ F (segrePrime F q)).toLinearMap =
        (Ideal.Quotient.mkₐ F q).toLinearMap ∘ₗ (segreMap F).toLinearMap :=
      LinearMap.ext fun _ => rfl
    unfold gradedPiece
    rw [← Submodule.map_comp, hc, Submodule.map_comp, map_segreMap_weightedHomogeneousSubmodule]
  (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ hmap)

theorem SegreHilb.proof : SegreHilb.Statement := by
  intro F _ K _ _ _ ι _ q n
  unfold hilbFn
  by_cases hn : 0 ≤ n
  · rw [if_pos (fun _ => hn), if_pos (fun _ => hn)]
    exact congrArg (fun x : ℕ => (x : ℤ)) (segreGradedPieceEquiv F q n.toNat).finrank_eq
  · rw [if_neg (fun h => hn (h ())), if_neg (fun h => hn (h (Classical.arbitrary K)))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

