module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBasePtFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

namespace StandardDualBasePointFree

open DualPointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [Fintype T] [DecidableEq T] in
theorem coord_integral (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (j : Fin i) :
    ∃ α : 𝓞 K, (α : K) = (b c : Fin i → K) j := by
  obtain ⟨α, hα⟩ := (b c).2 (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨α, hα.trans (dotProduct_single_one _ _)⟩


omit [DecidableEq T] in
theorem mConeMap_lin {Ω : Type} [Field Ω] (y : (Σ _ : Unit, T) → Ω) (a : T → ℤ) :
    mConeMap y (∑ t, C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) =
      MvPolynomial.C (∑ t, (a t : Ω) * y ⟨(), t⟩) * MvPolynomial.X () := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
  ring

end StandardDualBasePointFree


open StandardDualBasePointFree DualPointsOnPlane in
theorem DualStdBasePtFree.proof : DualStdBasePtFree.Statement := by
  intro K _ _ i T _ _ b k₂ c
  cases k₂
  refine ⟨2, ?_⟩
  have hprod : (∏ k : Unit, (X ⟨k, c k⟩ : MRing (dualBlocks T))) = X ⟨(), c ()⟩ := Fintype.prod_unique _
  rw [hprod]
  choose α hα using coord_integral b (c ())
  let am := algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
  let y := dualLatticeCoord b
  let L : Fin i → MRing (dualBlocks T) := fun j => ∑ s, C (mulMat b (α j) (c ()) s) * X ⟨(), s⟩

  have hA : ∀ j, ∑ t, (dualStdCoordMat b () j t : ProjField K i) * y ⟨(), t⟩ = am (X j) := by
    intro j
    have hpoly : ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = X j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hc : ∀ l, ∑ t, (dualStdCoordMat b () j t : K) * (b t : Fin i → K) l = (Pi.single j (1 : K) : Fin i → K) l := by
        intro l
        have h := congrFun (dualStdCoordMat_sum b j) l
        simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul] using h
      have hc' : ∀ l, ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) * (C ((b t : Fin i → K) l) * X l) =
          C ((Pi.single j (1 : K) : Fin i → K) l) * X l := by
        intro l
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hc l, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [map_mul, map_intCast]
        ring
      simp only [hc']
      rw [Finset.sum_eq_single j (fun l _ hl => by simp [hl]) (by simp)]
      simp
    have h := congrArg am hpoly
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hS : ∀ j, ∑ s, (mulMat b (α j) (c ()) s : ProjField K i) * y ⟨(), s⟩ =
      am (C (α j : K)) * y ⟨(), c ()⟩ := by
    intro j
    have hlin : ∑ t, (mulMat b (α j) (c ()) t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = C (α j : K) * ∑ l, C ((b (c ()) : Fin i → K) l) * X l := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b (α j) (c ()) l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, map_intCast] at h
      rw [← mul_assoc, ← h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    have h := congrArg am hlin
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hy : y ⟨(), c ()⟩ = ∑ j, am (C (α j : K)) * am (X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, am, dualLatticeCoord, map_sum, map_mul, hα]
  have key : X ⟨(), c ()⟩ ^ 2 - ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈ dualIdeal b := by
    show _ ∈ RingHom.ker (mConeMap (dualLatticeCoord b))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_sum]
    have hl : ∀ j, mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) =
        MvPolynomial.C (am (X j)) * MvPolynomial.X () := by
      intro j
      rw [← hA j]
      exact mConeMap_lin _ _
    have hL : ∀ j, mConeMap (dualLatticeCoord b) (L j) =
        MvPolynomial.C (am (C (α j : K)) * y ⟨(), c ()⟩) * MvPolynomial.X () := by
      intro j
      rw [← hS j]
      exact mConeMap_lin _ _
    have hX : mConeMap (dualLatticeCoord b) (X ⟨(), c ()⟩ : MRing (dualBlocks T)) =
        MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X () := by
      simp only [mConeMap, aeval_X, y]
    simp only [map_mul, map_pow, hl, hL, hX]
    symm
    calc ∑ j, MvPolynomial.C (am (X j)) * MvPolynomial.X () *
          (MvPolynomial.C (am (C (α j : K))) * MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X ())
        = MvPolynomial.C ((∑ j, am (C (α j : K)) * am (X j)) * y ⟨(), c ()⟩) * MvPolynomial.X () ^ 2 := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Finset.sum_mul, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [map_mul]
          ring
      _ = _ := by
          rw [← hy, map_mul]
          ring
  have hQ : ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈
      Ideal.span (Set.range fun j : PBlk i () => linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have h := Ideal.add_mem _ (Ideal.mem_sup_left key) (Ideal.mem_sup_right hQ)
  rwa [sub_add_cancel] at h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdImageBot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace StandardDualImageBottom

open DualArithmeticVariety

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]

def genPt (K : Type) [Field K] (i : ℕ) : (Σ _ : Unit, Fin i) → ProjField K i :=
  fun q => algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X q.2)


omit [Fintype T] in
theorem aeval_eq_zero_of_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    {f : MRing (dualBlocks T)} (hf : f ∈ dualIdeal b) : aeval (dualLatticeCoord b) f = 0 := by
  have h : ∀ g : MRing (dualBlocks T),
      MvPolynomial.eval (fun _ : Unit => (1 : ProjField K i)) (mConeMap (dualLatticeCoord b) g) =
        aeval (dualLatticeCoord b) g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp]
      simp [mConeMap]
  rw [← h f, show mConeMap (dualLatticeCoord b) f = 0 from hf, map_zero]

def evalQ (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* ProjField K i :=
  eval₂Hom (Ideal.Quotient.lift _ (aeval (dualLatticeCoord b)).toRingHom
    fun _ hf => aeval_eq_zero_of_mem b hf) fun _ => 1

theorem aeval_linForm (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (q : Σ _ : Unit, Fin i) :
    aeval (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) q) = genPt K i q := by
  obtain ⟨⟨⟩, j⟩ := q
  have hs := congrArg (evalForm (K := K) i) (dualStdCoordMat_sum b j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, evalForm, Fintype.linearCombination_apply_single, one_smul, ← evalForm] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [genPt, ← hs, linForm, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, aeval_C, aeval_X, map_zsmul, ← dualLatticeCoord_eq, zsmul_eq_mul, eq_intCast]

theorem evalQ_graphMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (f : MRing (PBlk i)) :
    evalQ b (graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f)) = aeval (genPt K i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, evalQ]
  | add p q hp hq =>
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, map_mul, aeval_X, rename_X, ← aeval_linForm b q]
    simp [graphMap, inrV, evalQ]

theorem aeval_genPt_injective : Function.Injective (aeval (R := ℤ) (genPt K i)) := by
  have hK : AlgebraicIndependent ℤ fun j : Fin i =>
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) :=
    (algebraicIndependent_gen i).restrictScalars (algebraMap ℤ K).injective_int
  have h := hK.comp (fun q : Σ _ : Unit, Fin i => q.2) (by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, c⟩ h
    cases h
    rfl)
  exact algebraicIndependent_iff_injective_aeval.mp h

end StandardDualImageBottom


open StandardDualImageBottom in
theorem DualStdImageBot.proof : DualStdImageBot.Statement := by
  intro K _ _ i T _ _ b
  refine eq_bot_iff.mpr fun f hf => (Ideal.mem_bot).mpr (aeval_genPt_injective (K := K) (i := i) ?_)
  have h0 : graphMap (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))
      (rename (inrV (ι := dualBlocks T) (ι₂ := PBlk i)) f) = 0 := hf
  rw [map_zero, ← evalQ_graphMap b, h0, map_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMetricPull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField Matrix

noncomputable section

namespace StandardDualMetricPullback

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]


omit [DecidableEq T] in
theorem linApply_eq (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) (j : Fin i) :
    linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ =
      ∑ τ : K →+* ℂ, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) := by
  classical
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  have hMW : dualEmbMatrix b *ᵥ W = fun t => z ⟨(), t⟩ :=
    (LinearEquiv.ofBijective _ hb).apply_symm_apply _
  have hA : ∀ p : (K →+* ℂ) × Fin i,
      ∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p = p.1 ((Pi.single j 1 : Fin i → K) p.2) := by
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← dualStdCoordMat_sum b j, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [dualEmbMatrix, Pi.smul_apply, zsmul_eq_mul]
  calc linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩
      = ∑ t, (dualStdCoordMat b () j t : ℂ) * ∑ p, dualEmbMatrix b t p * W p := by
        simp only [linApply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← congrFun hMW t]
        rfl
    _ = ∑ p, (∑ t, (dualStdCoordMat b () j t : ℂ) * dualEmbMatrix b t p) * W p := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ τ : K →+* ℂ, W (τ, j) := by
        simp only [hA, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [Ne.symm hj']) (by simp)]
        simp

end StandardDualMetricPullback


open StandardDualMetricPullback in
theorem DualStdMetricPull.proof : DualStdMetricPull.Statement := by
  intro K _ _ i T _ _ b hb z hz
  set W := dualRecover b hb (fun t => z ⟨(), t⟩)
  obtain ⟨σ, hσ⟩ := DualPtsOnPlane.proof K i _ T b hb z hz
  have hy : ∀ j, linApply (ι₂ := PBlk i) (dualStdCoordMat b) z ⟨(), j⟩ = W (σ, j) := fun j => by
    rw [linApply_eq b hb z j]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  have hterm : ∀ τ, ((star fun j => W (τ, j)) ⬝ᵥ
      ((HermLattice.standard K i).metric τ *ᵥ fun j => W (τ, j))).re = ∑ j, ‖W (τ, j)‖ ^ 2 := by
    intro τ
    simp only [HermLattice.standard, one_mulVec, dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
    norm_cast
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = _
  rw [show dualNormSq b hb (fun t => z ⟨(), t⟩) = ∑ τ, ∑ j, ‖W (τ, j)‖ ^ 2 from
    Finset.sum_congr rfl fun τ _ => hterm τ]
  simp only [fsMulti, HermLine.ofMetrics, fsMetric, Finset.univ_unique, Finset.prod_singleton, zpow_one,
    EuclideanSpace.norm_eq]
  congr 1
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [W, hσ τ hτ]) (by simp)]
  exact Finset.sum_congr rfl fun j _ => by rw [← hy j]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualStackedDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ), F'.lattice ≤ F.lattice → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    F.withStdMetric.degree - F'.withStdMetric.degree = ∑ t, Real.log |(a t : ℝ)|

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleStacked
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

def VertPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ u : T, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) ∧
        ∀ (d : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => d) →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : K') * aeval y g = a * y ⟨(), t⟩ ^ d)

def VertPointInj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)

def VertPointSurj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal → locLen m (sectionQuot y (aeval y s)) ≠ 0 →
        ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m

def VertPointMultChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})

def SectionQuotLocal.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (t : T), m.IsPrime →
        (∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          locLen m (sectionQuot y (aeval y s)) = locLen m (curveRing y ⧸ Ideal.span {a})

end

end GroundTheory.Heights₂.Heights
end

