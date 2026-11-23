module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleIndexMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt

noncomputable section

namespace InvertibleIndexMultiplicative

variable {Ω : Type} [Field Ω]

theorem index_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨c, hc, q, hq⟩ := OrderIdealIndexExtensionAlt.exists_int_eq_mul ha
  refine OrderIdealIndexExtensionAlt.index_ne_zero_of_zsmul_mem _ hc fun x => ?_
  have e : c • x = a * (q * x) := by rw [zsmul_eq_mul, hq, mul_assoc]
  rw [Submodule.mem_toAddSubgroup, e]
  exact I.mul_mem_right _ haI

theorem relIndex_mulBy_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by
  rw [map_mul_eq, relIndex_map_subtype]
  exact index_ne_zero (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ)

theorem relIndex_mulBy_mul {B : Subring Ω} {x y : Ω} (hx : x ≠ 0) (hxB : x ∈ B) (hyB : y ∈ B) :
    (B.toAddSubgroup.map (mulBy (x * y))).relIndex B.toAddSubgroup =
      (B.toAddSubgroup.map (mulBy x)).relIndex B.toAddSubgroup *
        (B.toAddSubgroup.map (mulBy y)).relIndex B.toAddSubgroup := by
  have e : B.toAddSubgroup.map (mulBy (x * y)) = (B.toAddSubgroup.map (mulBy y)).map (mulBy x) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext z
    simp [mul_assoc]
  have h1 : B.toAddSubgroup.map (mulBy y) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hyB hz
  have h2 : B.toAddSubgroup.map (mulBy x) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hxB hz
  rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono h1) h2,
    AddSubgroup.relIndex_map_map_of_injective (f := mulBy x) _ _ (mulBy_injective hx), mul_comm]

theorem ne_bot_of_rep {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by
  intro hI
  obtain ⟨⟨x, hxX⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hX0
  obtain ⟨y, hy, hxy⟩ := (hX x).1 hxX
  rw [hI, Ideal.mem_bot] at hy
  subst hy
  have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  simp [hβL, hx] at hxy

theorem genIndex_rep [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : Ω) ≠ 0 := fun h => hδ (Subtype.ext h)
  have g := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := X) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hX x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact index_ne_zero hI)
    (relIndex_mulBy_ne_zero hδ)
  rwa [relIndex_map_subtype] at g

end InvertibleIndexMultiplicative


open InvertibleIndexMultiplicative in
theorem InvertibleIndexMul.proof (h1 : LocalGenFamily.Statement) (h2 : LocallyPrincipalCoprimeField.Statement)
    (h3 : InvertibleProductRep.Statement) (h4 : InvertibleIndexCharP.Statement) :
    InvertibleIndexMul.Statement := by
  intro Ω _ B M N P η _ g h hB hM hN hP hg0 hh0 hgc hhc hloc
  have hlocM : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B M m (g i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.1
  have hlocN : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B N m (h i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.2.1
  by_cases hc : ringChar Ω ≠ 0
  · rw [h4 Ω B M η g hc hB hM hg0 hlocM, h4 Ω B N η h hc hB hN hh0 hlocN,
      h4 Ω B P η (fun i => g i * h i) hc hB hP (fun i => mul_ne_zero (hg0 i) (hh0 i))
        (fun m hm => (hloc m hm).imp fun _ hi => hi.2.2)]
    norm_num
  push Not at hc
  have : CharP Ω 0 := ringChar.eq_iff.mp hc
  have : CharZero Ω := CharP.charP_to_charZero Ω
  have := hB
  obtain ⟨hM0, ιM, _, aM, haM, hdM, hlM⟩ := h1 Ω B M η g hB hM hg0 hgc hlocM
  obtain ⟨β, δ, I, hβ, hδ, -, hMI⟩ := h2 Ω B M ιM aM hB hM haM hdM hlM hM0 1 one_ne_zero
  have hI0 := ne_bot_of_rep hβ hM0 hMI
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨hN0, ιN, _, aN, haN, hdN, hlN⟩ := h1 Ω B N η h hB hN hh0 hhc hlocN
  obtain ⟨β', δ', J, hβ', hδ', hJt, hNJ⟩ := h2 Ω B N ιN aN hB hN haN hdN hlN hN0 t ht0
  have hJ0 := ne_bot_of_rep hβ' hN0 hNJ
  have hIJ : I ⊔ J = ⊤ := by
    rw [eq_top_iff, ← hJt, sup_comm I J]
    exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr htI) _
  have hPr := h3 Ω B M N P η g h β δ β' δ' I J hβ hδ hβ' hδ' hMI hNJ hP hloc
  have hIJ0 : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  have hidx : (I * J).toAddSubgroup.index = I.toAddSubgroup.index * J.toAddSubgroup.index :=
    cardQuot_mul_of_coprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)
  have hβL : (β : Ω) ≠ 0 := fun e => hβ (Subtype.ext e)
  have hδL : (δ : Ω) ≠ 0 := fun e => hδ (Subtype.ext e)
  rw [genIndex_rep hβ hδ hI0 hMI, genIndex_rep hβ' hδ' hJ0 hNJ,
    genIndex_rep (mul_ne_zero hβ hβ') (mul_ne_zero hδ hδ') hIJ0 hPr, hidx, Subring.coe_mul, Subring.coe_mul,
    relIndex_mulBy_mul hβL β.2 β'.2, relIndex_mulBy_mul hδL δ.2 δ'.2]
  have p1 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ)
  have p2 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ)
  have p3 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ')
  have p4 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ')
  have p5 := Nat.pos_of_ne_zero (index_ne_zero hI0)
  have p6 := Nat.pos_of_ne_zero (index_ne_zero hJ0)
  refine ⟨by positivity, by positivity, ?_⟩
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongWeightDiff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongWeightDiff.proof (hM : ChartMassCompact.Statement) : LelongWeightDiff.Statement := by
  classical
  intro n d J u g k φ hJ hdim hu hg hgc hφ hk hkpos
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons g φ i) := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (⟨Set.univ, isOpen_univ, Set.subset_univ _, hg.contDiffOn⟩ : SmoothNear (zeroSet J) g)
    · simpa using hφ j
  have hcs : ∃ i, HasCompactSupport (vecCons g φ i) := ⟨0, by simpa using hgc⟩
  by_cases hA : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · simp only [varInt, dif_neg hA, sub_self]; exact tendsto_const_nhds
  simp only [varInt, dif_pos hA]
  set A := hA.choose
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hfin : ∀ y, (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
  have hkc : ContinuousOn k (zeroSet J) := by
    obtain ⟨U, -, hU, hkU⟩ := hk; exact hkU.continuousOn.mono hU
  have hlc : Continuous fun x => ‖linEval u x‖ ^ 2 := ((contDiff_linEval u).continuous.norm).pow 2
  set D : ℝ → (Fin n → ℂ) → ℝ := fun ε x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2 - logReg u ε x
  have hWc : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (zeroSet J) := fun ε hε =>
    ((hlc.continuousOn.add (continuousOn_const.mul (hkc.pow 2))).log fun x hx => by
      exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε (pow_pos (hkpos x hx) 2))).ne').div_const 2
  have hLc : ∀ ε : ℝ, 0 < ε → ContinuousOn (logReg u ε) (zeroSet J) := fun ε hε =>
    (contDiff_logReg u hε).continuous.continuousOn
  have hint : ∀ f, ContinuousOn f (zeroSet J) → Integrable (chartDens J A f (vecCons g φ)) := fun f hf =>
    (hM n (d + 1) J A f _ hJ hdim hAf hf hψ (Or.inr hcs)).mono'
      (LelongWeightDiff.measurable_chartDens hJ hdim hAf hf hψ).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact LelongWeightDiff.abs_chartDens_le _ _ (hfin y))
  have heq : (fun ε : ℝ => ∫ y, chartDens J A (D ε) (vecCons g φ) y) =ᶠ[𝓝[>] 0]
      fun ε => chartInt J A (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
        chartInt J A (logReg u ε) (vecCons g φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [chartInt, chartInt, ← integral_sub (hint _ (hWc ε hε)) (hint _ (hLc ε hε))]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      (LelongWeightDiff.chartDens_sub _ _ _ (hfin y)).symm)
  refine Tendsto.congr' heq ?_
  obtain ⟨P, hP0, hPu⟩ := LelongWeightDiff.exists_poly_of_linEval_eq_zero J A hAf u hu
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε => chartDens J A (D ε) (vecCons g φ)) (f := fun _ => (0 : ℝ))
    (chartAbsDens J A (fun x => Real.log (k x)) (vecCons g φ)) ?_ ?_
    (hM n (d + 1) J A _ _ hJ hdim hAf (hkc.log fun x hx => (hkpos x hx).ne') hψ (Or.inr hcs)) ?_
  · rwa [integral_zero] at h
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (LelongWeightDiff.measurable_chartDens hJ hdim hAf ((hWc ε hε).sub (hLc ε hε)) hψ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (LelongWeightDiff.abs_half_log_sub_le (sq_nonneg _) hε (hkpos x hx.1)) (abs_nonneg _)
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP0] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine LelongWeightDiff.tendsto_finset_sum_zero _ _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    swap
    · simp only [dif_neg hs]; exact tendsto_const_nhds
    simp only [dif_pos hs]
    have hux : linEval u x ≠ 0 := fun h0 => hy (by rw [← hx.2]; exact hPu x hx.1 h0)
    have ha : 0 < ‖linEval u x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hux) 2
    have hc : ContinuousAt (fun ε : ℝ => D ε x) 0 := by
      simp only [D, logReg]
      refine ((ContinuousAt.log (by fun_prop) ?_).div_const 2).sub
        ((ContinuousAt.log (by fun_prop) ?_).div_const 2) <;> simp [hux]
    have h0 : D 0 x = 0 := by simp [D, logReg]
    simpa [h0] using ((hc.tendsto.mono_left nhdsWithin_le_nhds).mul_const
      (ReciprocityTheory.AnForm.maDens (fun i => vecCons g φ i ∘ hs.choose) y))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

def IsDegZeroSmooth {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z

section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isDegZeroSmooth_log {B : HermLine ι} (hB : IsSmoothHerm B) (h0 : B.a = 0) :
    IsDegZeroSmooth (fun z => Real.log (B.h z)) := by
  refine ⟨ContDiffOn.log hB fun z hz => (B.pos z hz).ne', fun c z hc => ?_⟩
  simp only [B.smul c z hc, h0, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]

theorem isDegZeroSmooth_const (a : ℝ) : IsDegZeroSmooth (ι := ι) (fun _ => a) :=
  ⟨contDiffOn_const, fun _ _ _ => rfl⟩

theorem IsDegZeroSmooth.mul {u v : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    (hv : IsDegZeroSmooth v) : IsDegZeroSmooth (fun z => u z * v z) :=
  ⟨hu.1.mul hv.1, fun c z hc => by simp only [hu.2 c z hc, hv.2 c z hc]⟩

end

def planeSq (z : (Σ k, PBlk 3 k) → ℂ) : ℝ := ∑ i : Fin 3, ‖z ⟨(), i⟩‖ ^ 2

def planeBump (z : (Σ k, PBlk 3 k) → ℂ) : ℝ :=
  Real.smoothTransition (4 * ‖z ⟨(), 0⟩‖ ^ 2 / planeSq z - 1)

end GroundTheory.Heights₂.Heights
end
end

