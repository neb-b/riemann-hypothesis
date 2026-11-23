module

public import Mathlib
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0004
public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012
public import ReciprocityTheory.SemistableReduction.Bundle0017
public import ReciprocityTheory.SemistableReduction.Bundle0024

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory ReciprocityTheory.MultiplicativeHeights

noncomputable def hintPt {D n : ℕ} (t0 : Fin n → ℂ) (z : BlockSphere D n) :
    Fin (D + 1) × Fin n → ℂ :=
  fun v => Fin.cases (t0 v.2) (fun i => spherePoint (z i) v.2) v.1

theorem hint_mpSplit (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0)
      (blockSphereProb (D + 1) n) ((sphereProb n).prod (blockSphereProb D n)) := by
  unfold blockSphereProb
  exact measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => sphereProb n) 0

private theorem isProbabilityMeasure_sphereProb' (n : ℕ) (hn : 0 < n) : IsProbabilityMeasure (sphereProb n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold sphereProb
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := Module.finrank_pos
  have h1 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos.ne') (Metric.measure_ball_pos _ _ one_pos).ne'
  have h2 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite h1 h2

theorem hint_mpTail (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ)
      (blockSphereProb (D + 1) n) (blockSphereProb D n) := by
  haveI := isProbabilityMeasure_sphereProb' n hn
  haveI : SFinite (blockSphereProb D n) := by
    unfold blockSphereProb
    infer_instance
  have h := (measurePreserving_snd (μ := sphereProb n) (ν := blockSphereProb D n)).comp
    (hint_mpSplit D n hn)
  have e : (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ) =
      Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0) := by
    funext z i
    first
      | rfl
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; done)
      | (simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth]; rfl)
      | exact congrArg z (by simp)
  rw [e]
  exact h

theorem hint_blockPoint_eq {D n : ℕ} (z : BlockSphere (D + 1) n) :
    blockPoint z = hintPt (spherePoint (z 0)) (fun i : Fin D => z i.succ) := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero => simp [blockPoint, hintPt]
  | succ i => simp [blockPoint, hintPt]

theorem hint_eval_indep {D n : ℕ} {a : Fin (D + 1) → ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ}
    (hq : IsMultiHomogeneous a q) (ha : a 0 = 0) (x y : Fin (D + 1) × Fin n → ℂ)
    (hxy : ∀ v : Fin (D + 1) × Fin n, v.1 ≠ 0 → x v = y v) :
    MvPolynomial.eval x q = MvPolynomial.eval y q := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  refine Finset.sum_congr rfl fun s hs => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v.1 = 0
  · have h0 : s v = 0 := by
      have hsum := hq s hs 0
      rw [ha] at hsum
      have hle : s (0, v.2) ≤ ∑ j : Fin n, s (0, j) :=
        Finset.single_le_sum (f := fun j => s (0, j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ _)
      have hz : s (0, v.2) = 0 := by omega
      have hv' : v = (0, v.2) := Prod.ext hv rfl
      rw [hv']
      exact hz
    rw [h0, pow_zero, pow_zero]
  · rw [hxy v hv]

theorem hint_continuous_pt {D n : ℕ} (t0 : Fin n → ℂ) :
    Continuous fun z : BlockSphere D n => hintPt t0 z := by
  apply continuous_pi
  rintro ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    simp only [hintPt, Fin.cases_zero]
    exact continuous_const
  | succ i =>
    simp only [hintPt, Fin.cases_succ]
    unfold spherePoint
    fun_prop

theorem hint_logInt_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    Integrable (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) := by
  have hmeas : AEStronglyMeasurable
      (fun z : BlockSphere D n => Real.log ‖MvPolynomial.eval (hintPt t0 z) q‖)
      (blockSphereProb D n) :=
    ((continuous_norm.comp ((MvPolynomial.continuous_eval q).comp
      (hint_continuous_pt t0))).measurable.log).aestronglyMeasurable
  rw [← (hint_mpTail D n hn).integrable_comp hmeas]
  refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a q hq0 hq).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_ae_tail {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hq0 : q ≠ 0) (hq : IsMultiHomogeneous a q)
    (ha : a 0 = 0) (t0 : Fin n → ℂ) :
    ∀ᵐ z ∂(blockSphereProb D n), MvPolynomial.eval (hintPt t0 z) q ≠ 0 := by
  have hA : MeasurableSet {z : BlockSphere D n | MvPolynomial.eval (hintPt t0 z) q = 0} :=
    (isClosed_eq ((MvPolynomial.continuous_eval q).comp (hint_continuous_pt t0))
      continuous_const).measurableSet
  rw [ae_iff]
  simp only [not_not]
  rw [← (hint_mpTail D n hn).measure_preimage hA.nullMeasurableSet]
  have h0 := ae_blockSphere_eval_ne_zero (D + 1) n a q hq0 hq
  rw [ae_iff] at h0
  refine measure_mono_null (fun z hz => ?_) h0
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
  simp only [Set.mem_ofPred_eq, not_not]
  rw [hint_blockPoint_eq, hint_eval_indep hq ha _ (hintPt t0 (fun i : Fin D => z i.succ))]
  · exact hz
  rintro ⟨i, j⟩ hi
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
  rfl

theorem hint_fubini {D n : ℕ} (hn : 0 < n) {a : Fin (D + 1) → ℕ}
    {F : MvPolynomial (Fin (D + 1) × Fin n) ℂ} (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    Integrable (fun z : BlockSphere D n =>
      ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb n))
      (blockSphereProb D n) := by
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := D) hn
  set G : UnitSphereC n × BlockSphere D n → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hint : Integrable G ((sphereProb n).prod (blockSphereProb D n)) := by
    rw [← (hint_mpSplit D n hn).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (D + 1) n a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  exact hint.integral_prod_right

theorem hint_lin_ae {n : ℕ} (c : Fin n → ℂ) (hc : c ≠ 0) :
    ∀ᵐ s ∂(sphereProb n), ∑ j, c j * spherePoint s j ≠ 0 := by
  classical
  set Lc : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ :=
    ∑ j, c j • (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap with hLc
  have hL : ∀ x : EuclideanSpace ℂ (Fin n), Lc x = ∑ j, c j * WithLp.ofLp x j := by
    intro x
    simp [hLc]
  set H : Submodule ℝ (EuclideanSpace ℂ (Fin n)) := LinearMap.ker (Lc.restrictScalars ℝ) with hH
  have hHtop : H ≠ ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    intro htop
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ H := htop ▸ Submodule.mem_top
    rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL] at hmem
    simp at hmem
    exact hj hmem
  have hvol : (volume : Measure (EuclideanSpace ℂ (Fin n))) H = 0 :=
    Measure.addHaar_submodule _ H hHtop
  have hA : MeasurableSet {s : UnitSphereC n | ¬ (∑ j, c j * spherePoint s j ≠ 0)} := by
    simp only [not_not]
    exact (isClosed_eq (by unfold spherePoint; fun_prop) continuous_const).measurableSet
  rw [ae_iff]
  unfold sphereProb
  refine ProbabilityTheory.cond_absolutelyContinuous ?_
  rw [Measure.toSphere_apply' (μ := (volume : Measure (EuclideanSpace ℂ (Fin n)))) hA]
  apply mul_eq_zero_of_right
  refine measure_mono_null ?_ hvol
  rintro _ ⟨r, _, _, ⟨s, hs, rfl⟩, rfl⟩
  simp only [Set.mem_setOf_eq, not_not] at hs
  show r • (s : EuclideanSpace ℂ (Fin n)) ∈ H
  refine H.smul_mem r ?_
  rw [hH, LinearMap.mem_ker, LinearMap.restrictScalars_apply, hL]
  simpa [spherePoint] using hs

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SingleMemStandardLattice
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField
open scoped ComplexOrder

section Deg

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

def hStd (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_standardLattice_iff {x : Fin r → K} :
    x ∈ hStd K r ↔ ∀ i, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i := by
  simp [hStd, Submodule.mem_pi, Submodule.mem_one]

theorem pi_single_one_mem_hStd (i : Fin r) : (Pi.single i (1 : K) : Fin r → K) ∈ hStd K r := by
  rw [mem_standardLattice_iff]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem hStd_eq_span_pi_single : hStd K r =
    Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_standardLattice_iff] at hx
    choose y hy using hx
    have e : x = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [← hy j, Algebra.smul_def]
      · intro i _ hij
        simp [Pi.single_apply, Ne.symm hij]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact pi_single_one_mem_hStd i

theorem exists_integral_completion {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (hk : k ≤ r) :
    ∃ c : Fin (r - k) → Fin r → K, (∀ j, c j ∈ hStd K r) ∧ LinearIndependent K (Fin.append b c) ∧
      ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
  classical
  set W := Submodule.span K (Set.range b) with hW
  let T := W.mkQ
  let v : Fin r → (Fin r → K) ⧸ W := fun i => T (Pi.single i 1)
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range v)
  have hspan_top : Submodule.span K (Set.range v) = ⊤ := by
    have e1 : Set.range v = T '' Set.range (Pi.basisFun K (Fin r)) := by
      ext y
      simp [v, Set.mem_image, Set.mem_range]
    rw [e1, Submodule.span_image, (Pi.basisFun K (Fin r)).span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  have hsfin : s.Finite := (Set.finite_range v).subset hs
  haveI : Fintype s := hsfin.fintype
  have hcard : Fintype.card s = r - k := by
    have h1 : Fintype.card s = Module.finrank K ((Fin r → K) ⧸ W) := by
      rw [← Set.toFinset_card, ← finrank_span_set_eq_card hli, hspan, hspan_top, finrank_top]
    have hWk : Module.finrank K W = k := by rw [hW, finrank_span_eq_card hb, Fintype.card_fin]
    have h2 := Submodule.finrank_quotient_add_finrank W
    rw [hWk, Module.finrank_fin_fun] at h2
    omega
  let eq : Fin (r - k) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hidx : ∀ y : s, ∃ i, v i = y := fun y => hs y.2
  choose idx hidx' using hidx
  let c : Fin (r - k) → Fin r → K := fun j => Pi.single (idx (eq j)) 1
  have hTc : ∀ j, T (c j) = (eq j : (Fin r → K) ⧸ W) := fun j => hidx' (eq j)
  have hTli : LinearIndependent K (fun j => T (c j)) := by
    rw [show (fun j => T (c j)) = Subtype.val ∘ eq from funext hTc]
    exact hli.comp eq eq.injective
  have hTspan : ∀ y, y ∈ Submodule.span K (Set.range fun j => T (c j)) := by
    intro y
    have e2 : Set.range (fun j => T (c j)) = s := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩; show T (c j) ∈ s; rw [hTc]; exact (eq j).2
      · intro hz; exact ⟨eq.symm ⟨z, hz⟩, by show T (c (eq.symm ⟨z, hz⟩)) = z; rw [hTc]; simp⟩
    rw [e2, hspan, hspan_top]
    trivial
  refine ⟨c, fun j => pi_single_one_mem_hStd _, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h1 : ∑ j, g (Fin.natAdd k j) • T (c j) = 0 := by
      have := congrArg T hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_zero, map_sum, map_sum] at this
      have h0 : ∑ i, T (g (Fin.castAdd (r - k) i) • b i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [h0, zero_add] at this
      simpa using this
    have h2 := Fintype.linearIndependent_iff.mp hTli _ h1
    have h3 : ∑ i, g (Fin.castAdd (r - k) i) • b i = 0 := by
      rw [← hg]
      simp [h2]
    have h4 := Fintype.linearIndependent_iff.mp hb _ h3
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact h4 i
    · exact h2 j
  · intro x
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hTspan (T x))
    have hT0 : T (x - ∑ j, β j • c j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hβ, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hT0
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hT0
    have hx : x = ∑ i, α i • b i + ∑ j, β j • c j := by rw [hα]; abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd (r - k) i, Fin.append_left b c i⟩
    · exact Submodule.subset_span ⟨Fin.natAdd k j, Fin.append_right b c j⟩

end Deg

section Deg2

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem standardLattice_fg : (hStd K r).FG := by
  rw [hStd_eq_span_pi_single]
  exact Submodule.fg_span (Set.finite_range _)

theorem latDeg_standard_basis {n : ℕ} (h : n = r) (v : Fin n → Fin r → K)
    (hv : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) v) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) v = 0 := by
  classical
  let std : Fin n → Fin r → K := fun i => Pi.single (finCongr h i) 1
  have hstd_eq : std = ⇑(Pi.basisFun K (Fin r)) ∘ finCongr h := by
    funext i
    simp [std]
  have hrange : Set.range std = Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K) := by
    rw [hstd_eq, (finCongr h).surjective.range_comp]
    ext x
    simp
  have hstd : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) std := by
    refine ⟨fun i => pi_single_one_mem_hStd _, ?_, fun x _ => ?_⟩
    · rw [hstd_eq]
      exact (Pi.basisFun K (Fin r)).linearIndependent.comp _ (finCongr h).injective
    · rw [hstd_eq, (finCongr h).surjective.range_comp, (Pi.basisFun K (Fin r)).span_eq]
      trivial
  rw [ReciprocityTheory.MultiplicativeHeights.latDegBasis_holds K r n _ (hStd K r) v std (fun _ => PosDef.one) standardLattice_fg
    hv hstd]
  have hspan : Submodule.span (𝓞 K) (Set.range std) = hStd K r := by
    rw [hrange, hStd_eq_span_pi_single]
  have hgram : ∀ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.gramC 1 σ std = 1 := by
    intro σ
    ext i j
    simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, one_mulVec, dotProduct,
      Pi.star_apply, std, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single (finCongr h i)]
      · simp
      · intro l _ hl
        have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
      · simp
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = finCongr h i
      · have : l ≠ finCongr h j := by
          rw [hl]; exact fun e => hij ((finCongr h).injective e)
        have this' : ¬ l = Fin.cast h j := this
        simp [Pi.single_apply, this']
      · have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
  simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hspan, AddSubgroup.relIndex_self, Nat.cast_one, Real.log_one,
    hgram, det_one, Complex.one_re, Finset.sum_const_zero, mul_zero, sub_zero]

theorem latDeg_saturation {m : ℕ} (h : k + m = r) {b : Fin k → Fin r → K}
    (hbL : ∀ j, b j ∈ hStd K r) (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r)
    (hli : LinearIndependent K (Fin.append b c))
    (hsp : ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c))) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b =
      -ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c := by
  have hadd := ReciprocityTheory.MultiplicativeHeights.degAdd_holds K r k m (fun _ => 1) (hStd K r) b c (fun _ => PosDef.one)
    standardLattice_fg hbL hc hli (fun x _ => hsp x)
  have hmem : ∀ i, Fin.append b c i ∈ hStd K r := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hbL i
    · rw [Fin.append_right]; exact hc j
  have h0 := latDeg_standard_basis h (Fin.append b c) ⟨hmem, hli, fun x _ => hsp x⟩
  linarith

theorem quotGram_eq_conjTranspose_mul (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hPm σ b * hBm σ c)ᴴ * (hPm σ b * hBm σ c) := by
  have e1 : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotGramC, crossGram_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, hPm, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1]
  simp only [conjTranspose_mul, orthogonalProjector_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hPm σ b) (hPm σ b), orthogonalProjector_mul_self σ hb]

theorem quotGram_det_pos (σ : K →+* ℂ) {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hli : LinearIndependent K (Fin.append b c)) :
    0 < (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  have hinj : Function.Injective (hPm σ b * hBm σ c).mulVec := by
    intro z z' hzz
    have h0 : hPm σ b *ᵥ (hBm σ c *ᵥ (z - z')) = 0 := by
      rw [mulVec_mulVec, mulVec_sub, hzz, sub_self]
    set y := ((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ (hBm σ c *ᵥ (z - z'))) with hy
    have h1 : hBm σ c *ᵥ (z - z') - hBm σ b *ᵥ y = 0 := by
      have h2 := h0
      simp only [hPm, sub_mulVec, one_mulVec, ← mulVec_mulVec] at h2
      exact h2
    have hl := linearIndependent_map_embedding σ hli
    have h3 : ∑ i, Fin.append (-y) (z - z') i • (fun l => σ (Fin.append b c i l)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← h1, embeddingColumns_mulVec, embeddingColumns_mulVec]
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
      abel
    have h4 := Fintype.linearIndependent_iff.mp hl _ h3
    funext j
    have := h4 (Fin.natAdd k j)
    rw [Fin.append_right] at this
    exact sub_eq_zero.mp this
  have hpd := PosDef.conjTranspose_mul_self (hPm σ b * hBm σ c) hinj
  rw [← quotGram_eq_conjTranspose_mul σ hb c] at hpd
  have hpos := hpd.det_pos
  rw [← quotientGram_det_re_eq σ hb c] at hpos
  exact_mod_cast hpos

end Deg2

end ReciprocityTheory.ChartRestriction.G.T0
end

