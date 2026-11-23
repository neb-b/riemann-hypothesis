module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.AevalMemAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendence

theorem aeval_red {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) :
    aeval y (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = aeval y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]

theorem aeval_mem_adjoin {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) : aeval y g ∈ IntermediateField.adjoin (ZMod p) (Set.range y) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf =>
    simpa using mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

variable {K : Type} {ι : K → Type}

theorem ker_aeval_F {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by
  ext f
  obtain ⟨g, rfl⟩ := PointVertical.red_surjective (ι := ι) p f
  rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, ← hJ, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0) (aeval_red p y g))

theorem trdeg_adjoin [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  have h := hE K ι (ZMod p) L y
  rw [ker_aeval_F p y hp hJ, hV.2] at h
  have h' : (Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y))).toENat =
      ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h.symm
  exact Cardinal.toENat_eq_natCast.mp h'

end FibreTranscendence


open FibreTranscendence in
theorem FibreTranscendenceDegreeAlt.proof (hE : EvalKerKrullDim.Statement) : FibreTranscendenceDegreeAlt.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  classical
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hp
  have hΦp : ((p : ℕ) : G'.Φ) = 0 := by
    have h := hpI
    rw [← G'.ker_x, RingHom.mem_ker] at h
    simpa using h
  have hΦ'p : ((p : ℕ) : G'.Φ') = 0 := by
    have h := hp
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker] at h
    simpa using h
  have : CharP G'.Φ p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦp
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦ'p
  let _ : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  let _ : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq fun a =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) G'.Φ')
      ((algebraMap G'.Φ G'.Φ').comp (algebraMap (ZMod p) G'.Φ))) a

  have hx := trdeg_adjoin hE p G'.x hpI G'.ker_x
    (by rw [← PointVertical.imageVar_red p v hp]; exact hV)
  have htop : IntermediateField.adjoin (ZMod p) (Set.range G'.x) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨f, g, -, rfl⟩ := G'.gen c
    exact div_mem (aeval_mem_adjoin p _ f) (aeval_mem_adjoin p _ g)
  have hΦ : Algebra.trdeg (ZMod p) G'.Φ = ((n + Fintype.card K : ℕ) : Cardinal) := by
    rw [← hx, htop, IntermediateField.topEquiv.trdeg_eq]

  set E := IntermediateField.adjoin G'.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩) with hEdef
  have hEeq : E.restrictScalars (ZMod p) = IntermediateField.adjoin (ZMod p) (Set.range G'.x') := by
    refine le_antisymm (fun c hc => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · have hle : E.toSubfield ≤ (IntermediateField.adjoin (ZMod p) (Set.range G'.x')).toSubfield := by
        rw [hEdef, IntermediateField.adjoin_toSubfield]
        refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
        · rintro _ ⟨c, rfl⟩
          obtain ⟨f, g, -, rfl⟩ := G'.gen c
          have key : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) = aeval G'.x' (rename v f) := by
            intro f
            induction f using MvPolynomial.induction_on with
            | C a => simp
            | add f g hf hg => simp only [map_add (f := _), hf, hg]
            | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G'.compat]
          rw [map_div₀, key, key]
          exact div_mem (aeval_mem_adjoin p _ _) (aeval_mem_adjoin p _ _)
        · rintro _ ⟨q, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      exact hle hc
    · rintro _ ⟨q, rfl⟩
      show G'.x' q ∈ E
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
        rw [G'.compat]
        exact E.algebraMap_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  have hEt : Algebra.trdeg (ZMod p) E = ((n + Fintype.card K' : ℕ) : Cardinal) := by
    rw [← trdeg_adjoin hE p G'.x' hp G'.genericFibre_ker_target hW, ← hEeq]
    rfl

  have hadd := trdeg_add_eq (ZMod p) G'.Φ (A := E)
  rw [hΦ, hEt] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G'.Φ E < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd ⊢
  have : n + Fintype.card K + m = n + Fintype.card K' := by exact_mod_cast hadd
  exact_mod_cast (by omega : m = Fintype.card (FibreBlock κ))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ContinuousMinorRatioLift
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

section Minor

variable {Ω : Type} [Fintype Ω]

def minorRatio (b a : Ω → ℂ) : ℝ :=
  ‖fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1‖ / ‖a‖

theorem minorRatio_nonneg (b a : Ω → ℂ) : 0 ≤ minorRatio b a :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem minorRatio_smul (b a : Ω → ℂ) {μ : ℂ} (hμ : μ ≠ 0) : minorRatio b (μ • a) = minorRatio b a := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => (μ • a) il.1 * b il.2 - (μ • a) il.2 * b il.1) =
      μ • fun il : Ω × Ω => a il.1 * b il.2 - a il.2 * b il.1 := by
    funext il
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, norm_smul, norm_smul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hμ)

theorem minorRatio_self (b : Ω → ℂ) : minorRatio b b = 0 := by
  unfold minorRatio
  have h : (fun il : Ω × Ω => b il.1 * b il.2 - b il.2 * b il.1) = 0 := by
    funext il
    simp only [Pi.zero_apply]
    ring
  rw [h, norm_zero, zero_div]

theorem continuousAt_minorRatio (b : Ω → ℂ) {a : Ω → ℂ} (ha : a ≠ 0) :
    ContinuousAt (minorRatio b) a := by
  unfold minorRatio
  refine ContinuousAt.div ?_ continuous_norm.continuousAt (norm_ne_zero_iff.mpr ha)
  refine (continuous_norm.comp (continuous_pi fun il => ?_)).continuousAt
  exact ((continuous_apply il.1).mul continuous_const).sub ((continuous_apply il.2).mul continuous_const)

theorem eq_smul_of_minorRatio {b a : Ω → ℂ} (hb : b ≠ 0) (ha : a ≠ 0) (h : minorRatio b a = 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ a = μ • b := by
  unfold minorRatio at h
  rw [div_eq_zero_iff, or_iff_left (norm_ne_zero_iff.mpr ha), norm_eq_zero] at h
  have hm : ∀ i l, a i * b l = a l * b i := fun i l => by
    have := congrFun h (i, l)
    simp only [Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  obtain ⟨l0, hl0⟩ : ∃ l0, b l0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hb (funext hc)
  have heq : a = (a l0 / b l0) • b := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hl0]
    exact hm i l0
  refine ⟨a l0 / b l0, fun h0 => ha ?_, heq⟩
  rw [heq, h0, zero_smul]

end Minor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem continuous_segre : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
  continuous_pi fun _ => continuous_finsetProd _ fun _ _ => continuous_apply _

theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : segre z ≠ 0 := by
  choose p hp using hz
  intro h
  have := congrFun h p
  simp only [segre, Pi.zero_apply] at this
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => hp k) this

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem continuousAt_lift (x : R.X) : ContinuousAt (fun x' => R.lift x x') x := by
  obtain ⟨j, hj⟩ := R.A.cover x
  have hu : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact R.mem_U x⟩
  have h1 : ContinuousAt (fun x' => R.lift x ((R.A.chart j).symm (R.A.chart j x'))) x :=
    ContinuousAt.comp (f := R.A.chart j) (g := fun w => R.lift x ((R.A.chart j).symm w))
      (analyticAt_lift_chart R x j hu).continuousAt ((R.A.chart j).continuousAt hj)
  refine h1.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with x' hx'
  rw [(R.A.chart j).left_inv hx']

theorem continuous_minorRatio_lift [DecidableEq K'] (b : ((k : K') → ι' k) → ℂ) :
    Continuous (fun x' : R.X => minorRatio b (segre (R.lift x' x'))) := by
  refine continuous_iff_continuousAt.mpr fun x' => ?_
  have hne : segre (R.lift x' x') ≠ 0 := segre_ne_zero (R.mem x' x' (R.mem_U x')).1
  have h1 : ContinuousAt (fun x'' => minorRatio b (segre (R.lift x' x''))) x' :=
    ContinuousAt.comp (g := minorRatio b) (continuousAt_minorRatio b hne)
      (continuous_segre.continuousAt.comp (continuousAt_lift R x'))
  refine h1.congr ?_
  filter_upwards [(R.isOpen_U x').mem_nhds (R.mem_U x')] with x'' hx''
  obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (R.compat x'' x' x'' ⟨R.mem_U x'', hx''⟩)
  rw [hμeq, minorRatio_smul b _ hμ]

theorem isolated_of_not_pullBad (hv : IsBlockMap κ v)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X} (hx : x ∉ pullBad R v Ψ) :
    ∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) (pullPt R v x) →
      dist z'' (R.lift x x) < ε → SameOrbit z'' (R.lift x x) := by
  classical
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have hz' := R.mem x x (R.mem_U x)
  obtain ⟨j, hj⟩ := R.A.cover x
  have hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  obtain ⟨e, he⟩ := hasStrictFDerivAt_equiv hgood.1 hgood.2
  have hinj := (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).injOn
  set V := (R.A.chart j).source ∩
    (R.A.chart j) ⁻¹' (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).source with hVdef
  have hVo : IsOpen V := (R.A.chart j).isOpen_inter_preimage
    (he.toOpenPartialHomeomorph (pullQ R v Ψ ∘ (R.A.chart j).symm)).open_source
  have hxV : x ∈ V := ⟨hj, he.mem_toOpenPartialHomeomorph_source⟩
  have hb : segre (R.lift x x) ≠ 0 := segre_ne_zero hz'.1
  have hθc := continuous_minorRatio_lift R (segre (R.lift x x))
  have hθpos : ∀ x' ∈ Vᶜ, 0 < minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    intro x' hx'
    refine lt_of_le_of_ne (minorRatio_nonneg _ _) (Ne.symm fun h0 => hx' ?_)
    obtain ⟨μ, hμ, hμeq⟩ := eq_smul_of_minorRatio hb (segre_ne_zero (R.mem x' x' (R.mem_U x')).1) h0
    have hso : SameOrbit (R.lift x' x') (R.lift x x) := sameOrbit_of_segre hz'.1 μ hμ hμeq
    rw [← R.inj x x' hxB (sameOrbit_comm hso)]
    exact hxV
  obtain ⟨m0, hm0, hm0le⟩ : ∃ m0 : ℝ, 0 < m0 ∧
      ∀ x' ∈ Vᶜ, m0 ≤ minorRatio (segre (R.lift x x)) (segre (R.lift x' x')) := by
    rcases (Vᶜ).eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, fun x' hx' => by rw [hC] at hx'; exact absurd hx' (Set.notMem_empty x')⟩
    · obtain ⟨x1, hx1, hmin⟩ := (hVo.isClosed_compl.isCompact).exists_isMinOn hC hθc.continuousOn
      exact ⟨_, hθpos x1 hx1, fun x' hx' => isMinOn_iff.mp hmin x' hx'⟩
  have hDc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => minorRatio (segre (R.lift x x)) (segre z))
      (R.lift x x) :=
    ContinuousAt.comp (g := minorRatio (segre (R.lift x x))) (continuousAt_minorRatio _ hb)
      continuous_segre.continuousAt
  obtain ⟨ε1, hε1, hball1⟩ := Metric.continuousAt_iff.mp hDc m0 hm0
  obtain ⟨g, hgJ, hg0⟩ : ∃ g ∈ J', eval (R.lift x x) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    by_contra h
    push Not at h
    exact hxB ⟨hz'.1, h⟩
  have hgc : ContinuousAt (fun z : (Σ k', ι' k') → ℂ => eval z (map (Int.castRingHom ℂ) g))
      (R.lift x x) :=
    (MvPolynomial.continuous_eval _).continuousAt
  obtain ⟨ε2, hε2, hball2⟩ := Metric.continuousAt_iff.mp hgc _ (norm_pos_iff.mpr hg0)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun z'' hz'' hzv hd => ?_⟩
  have hd1 : dist z'' (R.lift x x) < ε1 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist z'' (R.lift x x) < ε2 := lt_of_lt_of_le hd (min_le_right _ _)
  have hzB : z'' ∉ mcPts J' := by
    intro h
    have h2 : dist (eval z'' (map (Int.castRingHom ℂ) g)) (eval (R.lift x x) (map (Int.castRingHom ℂ) g)) <
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ := hball2 hd2
    rw [h.2 g hgJ, dist_zero_left] at h2
    exact lt_irrefl _ h2
  obtain ⟨x'', hx''⟩ := R.surj z'' hz'' hzB
  have hθx'' : minorRatio (segre (R.lift x x)) (segre (R.lift x'' x'')) < m0 := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hx''
    have h1 : dist (minorRatio (segre (R.lift x x)) (segre z''))
        (minorRatio (segre (R.lift x x)) (segre (R.lift x x))) < m0 := hball1 hd1
    rw [minorRatio_self, Real.dist_eq, sub_zero] at h1
    rw [hμeq, minorRatio_smul _ _ hμ]
    exact lt_of_le_of_lt (le_abs_self _) h1
  have hx''V : x'' ∈ V := by
    by_contra hc
    exact absurd (hm0le x'' hc) (not_le.mpr hθx'')
  have hso : SameOrbit (pullPt R v x'') (pullPt R v x) :=
    sameOrbit_tr (sameOrbit_comp hv hx'') hzv
  have hq : pullQ R v Ψ x'' = pullQ R v Ψ x := by
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit hso
    funext i
    simp only [pullQ, hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hμ
  have hxx : x'' = x := by
    have h1 : (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x'') =
        (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
      simp only [Function.comp_apply, (R.A.chart j).left_inv hx''V.1, (R.A.chart j).left_inv hj, hq]
    have h2 : R.A.chart j x'' = R.A.chart j x :=
      hinj hx''V.2 hxV.2 (by rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]; exact h1)
    exact (R.A.chart j).injOn hx''V.1 hj h2
  rw [hxx] at hx''
  exact sameOrbit_comm hx''

theorem pullFib_finite (hIsol : FibreIsolFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (y : Fin n → ℂ) : (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite := by
  classical
  have hF := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  choose! uw huw using fun w (hw : w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre (imageZ v P') Ψ y) => hw
  choose T hT using fun w => hIsol K ι K' ι' κ v P' n hv hP' (uw w)
  refine (hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_
  rintro x ⟨hqx, hx⟩
  have hxB : R.lift x x ∉ mcPts J' := fun h => hx (Or.inl (Or.inl h))
  have h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Ψ h0x
  rw [show pullQ R v Ψ x = y from hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Ψ x)) :=
    sameOrbit_of_segre hu1.1 (Ψ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨ε, hε, hiso⟩ := isolated_of_not_pullBad R hv Ψ hx
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Ψ x) (R.lift x x) (R.mem x x (R.mem_U x)) hso
    ⟨ε, hε, fun z'' hz'' hzu hd => hiso z'' hz'' (sameOrbit_tr hzu (sameOrbit_comm hso)) hd⟩
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreRest
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ArithmeticIntersectionChartFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    FiniteDimensional G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def ChartNormCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    FiniteDimensional G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) →
    ∃ E : MRing ι, E ∉ imageZ v P' ∧
      ∀ w ∈ mcPts (imageZ v P'), eval w (map (Int.castRingHom ℂ) E) ≠ 0 →
        {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1}.Finite ∧
        {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = w p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1}.ncard =
          Module.finrank G.Φ (IntermediateField.adjoin G.Φ
            (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', (∀ p, z' (v p) = w p) → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTer
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDimensionZero.proof (h₁ : ArithmeticIntersectionFibreMultiHomogeneous.Statement) (h₂ : EvalKerKrullDim.Statement)
    (h₃ : FibreTranscendenceDegreeAlt.Statement) : FibreDimensionZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  refine ⟨⟨RingHom.ker_isPrime _, h₁ K ι K' ι' κ v p W' hv hp hW.1.2.1 G', fun k => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := hW.1.2.2 k.1
    refine ⟨i, fun h => hi ?_⟩
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at h
    have hX : (X ⟨k.1, i⟩ : MRing ι') ∈ W' := by
      rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
      exact h
    simpa using Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom (ZMod p))) hX
  · rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, h₂ (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ', h₃ K ι K' ι' κ v p W' n hv hp hW hV G']
    simp

end GroundTheory.Heights₂.Heights.Inter
end
end

