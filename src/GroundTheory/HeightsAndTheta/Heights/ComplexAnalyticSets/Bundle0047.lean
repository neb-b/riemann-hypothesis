module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinHenselCompletionNoetherian
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

theorem SlabBound.affine : GroundTheory.Heights₂.Heights.SlabBound.Statement := by
  intro n d J A u hJ hA hu
  classical
  set φ : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (GroundTheory.Heights₂.Heights.linProjHom J A : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J)
    with hφ
  set v : MvPolynomial (Fin n) ℂ ⧸ J := Ideal.Quotient.mk J (GroundTheory.Heights₂.Heights.linForm u) with hv
  have hv0 : v ≠ 0 := by
    rw [hv, Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral v
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpm.ne_zero 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h
    apply hq
    rw [map_zero, sub_zero]
    exact Polynomial.X_dvd_iff.mpr h
  have hqv : q.eval₂ φ v = 0 := by
    rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_zero, sub_zero] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hv0)
  refine ⟨q.coeff 0, hq0, fun R => ?_⟩
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z =>
    ∑ i ∈ Finset.range (q.divX.natDegree + 1),
      eval (A.mulVec fun j => z j) (q.divX.coeff i) * (∑ j, u j * z j) ^ i
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ ?_
    · exact (MvPolynomial.continuous_eval _).comp (by fun_prop)
    · fun_prop
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨K, fun z hz hzR => ?_⟩
  let ev : MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
    Ideal.Quotient.lift J (eval fun j => z j) (fun a ha => hz a ha)
  have hevφ : ev.comp φ = eval (A.mulVec fun j => z j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom]
    · intro i
      simp [ev, φ, GroundTheory.Heights₂.Heights.linProjHom, Matrix.mulVec, dotProduct]
  have hevv : ev v = ∑ j, u j * z j := by
    simp [ev, v, GroundTheory.Heights₂.Heights.linForm]
  have key : q.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j) = 0 := by
    have h1 := congrArg ev hqv
    rw [Polynomial.hom_eval₂, hevφ, hevv, map_zero] at h1
    exact h1
  have hsplit : eval (A.mulVec fun j => z j) (q.coeff 0) = -((∑ j, u j * z j) * g z) := by
    have h2 := congrArg (fun r => r.eval₂ (eval (A.mulVec fun j => z j)) (∑ j, u j * z j))
      (Polynomial.X_mul_divX_add q)
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      key] at h2
    rw [Polynomial.eval₂_eq_sum_range] at h2
    linear_combination h2
  have hzb : z ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin n)) R := mem_closedBall_zero_iff.mpr hzR
  rw [hsplit, norm_neg, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK z hzb) (norm_nonneg _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]


end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAffineCompletionNormal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem adicCompletion_isLocalRing_of_isMaximal {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))

theorem AffineCompletionNormal.proof (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPiece
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace AreaGraphPiece

variable {k m : ℕ}

def pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => u i) (fun i => w i))

def firstPart (p : EuclideanSpace ℝ (Fin k ⊕ Fin m)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => p (Sum.inl i))

theorem realGraphPt_eq (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := rfl

theorem firstPart_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    firstPart (pairPt u w) = u := by
  ext i
  simp [firstPart, pairPt]

theorem pairPt_add (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w + pairPt u' w' = pairPt (u + u') (w + w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_sub (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem pairPt_smul (c : ℝ) (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    c • pairPt u w = pairPt (c • u) (c • w) := by
  ext i
  rcases i with i | i <;> simp [pairPt]

theorem inner_pairPt (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    ⟪pairPt u w, pairPt u' w'⟫ = ⟪u, u'⟫ + ⟪w, w'⟫ := by
  simp [pairPt, PiLp.inner_apply, Fintype.sum_sum_type]

theorem norm_pairPt_sq (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_pairPt]

theorem norm_le_norm_pairPt (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pairPt u w‖ := by
  have h := norm_pairPt_sq u w
  nlinarith [norm_nonneg u, norm_nonneg (pairPt u w), sq_nonneg ‖w‖]

theorem norm_pairPt_zero (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by
  have h := norm_pairPt_sq (0 : EuclideanSpace ℝ (Fin k)) w
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

def graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) where
  toFun x := pairPt x (A x)
  map_add' x y := by rw [map_add (f := _), pairPt_add]
  map_smul' c x := by rw [map_smul, pairPt_smul]; rfl

theorem graphLin_apply (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : graphLin A x = pairPt x (A x) := rfl

theorem adjoint_graphLin_comp (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    LinearMap.adjoint (graphLin A) ∘ₗ graphLin A =
      (1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
        LinearMap.adjoint (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
          (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_left,
    Module.End.one_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, graphLin_apply,
    graphLin_apply, inner_pairPt]
  rfl

theorem normDet_graphLin (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  unfold graphJac
  rw [← adjoint_graphLin_comp, ← LinearMap.normDet_sq (graphLin A)]
  push_cast
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm

end AreaGraphPiece


open AreaGraphPiece in
theorem AreaGraphPiece.proof : AreaGraphPiece.Statement := by
  intro k m F A δ t hδ hF
  set L := graphLin A with hLdef
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hδ
  have hδ0 : (0 : ℝ) ≤ δ := δ.2

  have hsub : ∀ x y, realGraphPt F x - realGraphPt F y - L (x - y) =
      pairPt (0 : EuclideanSpace ℝ (Fin k)) (F x - F y - A (x - y)) := by
    intro x y
    rw [realGraphPt_eq, realGraphPt_eq, hLdef, graphLin_apply, pairPt_sub, pairPt_sub]
    simp
  have hL : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => norm_le_norm_pairPt v (A v)
  have hclose : ∀ x ∈ t, ∀ y ∈ t,
      |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖| ≤ δ * ‖L (x - y)‖ := by
    intro x hx y hy
    calc |‖realGraphPt F x - realGraphPt F y‖ - ‖L (x - y)‖|
        ≤ ‖realGraphPt F x - realGraphPt F y - L (x - y)‖ := abs_norm_sub_norm_le _ _
      _ = ‖F x - F y - A (x - y)‖ := by rw [hsub, norm_pairPt_zero]
      _ ≤ δ * ‖x - y‖ := hF x hx y hy
      _ ≤ δ * ‖L (x - y)‖ := mul_le_mul_of_nonneg_left (hL _) hδ0

  have himG : realGraphPt F '' t = (fun p => realGraphPt F (firstPart p)) '' (L '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hLdef, graphLin_apply, firstPart_pairPt]
  have hlipG : LipschitzOnWith (1 + δ) (fun p => realGraphPt F (firstPart p)) (L '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [hLdef, graphLin_apply, firstPart_pairPt, dist_eq_norm]
    rw [← graphLin_apply, ← graphLin_apply, ← map_sub, ← hLdef]
    have h := (abs_le.1 (hclose x hx y hy)).2
    push_cast
    linarith

  have himL : L '' t = (fun p => L (firstPart p)) '' (realGraphPt F '' t) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [realGraphPt_eq, firstPart_pairPt]
  have hlipL : LipschitzOnWith (1 - δ)⁻¹ (fun p => L (firstPart p)) (realGraphPt F '' t) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [realGraphPt_eq, firstPart_pairPt, dist_eq_norm]
    rw [← realGraphPt_eq, ← realGraphPt_eq, ← map_sub]
    have h := (abs_le.1 (hclose x hx y hy)).1
    rw [NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div,
      le_div_iff₀ (by linarith)]
    nlinarith

  have harea : μH[(k : ℝ)] (L '' t) =
      ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
        μH[(k : ℝ)] t := by
    have h := LinearMap.hausdorffMeasure_image L t
    rw [finrank_euclideanSpace_fin] at h
    rw [h, hLdef, normDet_graphLin]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · calc μH[(k : ℝ)] (realGraphPt F '' t)
        = μH[(k : ℝ)] ((fun p => realGraphPt F (firstPart p)) '' (L '' t)) := by rw [← himG]
      _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (L '' t) :=
          hlipG.hausdorffMeasure_image_le hk
      _ = _ := by rw [harea, ENNReal.rpow_natCast, mul_assoc]
  · have hle : μH[(k : ℝ)] (L '' t) ≤
        (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t) := by
      calc μH[(k : ℝ)] (L '' t)
          = μH[(k : ℝ)] ((fun p => L (firstPart p)) '' (realGraphPt F '' t)) := by rw [← himL]
        _ ≤ (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ (k : ℝ) * μH[(k : ℝ)] (realGraphPt F '' t) :=
            hlipL.hausdorffMeasure_image_le hk
        _ = _ := by rw [ENNReal.rpow_natCast]
    have hne : (1 - δ : ℝ≥0) ≠ 0 := (tsub_pos_of_lt hδ).ne'
    calc ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ENNReal.ofReal (graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
            μH[(k : ℝ)] t
        = ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (L '' t) := by rw [harea, mul_assoc]
      _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
          ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ k * μH[(k : ℝ)] (realGraphPt F '' t)) := by gcongr
      _ = μH[(k : ℝ)] (realGraphPt F '' t) := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one,
            one_pow, one_mul]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAuslanderBuchsbaumProjDimUpper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

theorem hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d)
    (ms : List R) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R M) n → (∀ r ∈ ms, r ∈ maximalIdeal R) →
        IsWeaklyRegular M ms → HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length) := by
  induction ms with
  | nil =>
    intro M _ _ _ _ n hM _ _
    simpa using hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le d R hd M n hM
  | cons x ms ih =>
    intro M _ _ _ _ n hM hms hreg
    simp only [List.mem_cons, forall_eq_or_imp] at hms
    rw [isWeaklyRegular_cons_iff] at hreg
    have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hms.1
    have heq : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) =
        projectiveDimension (ModuleCat.of R M) + 1 :=
      ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R M) x hreg.1 hms.1
    have hQ : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x M)) (n + 1) := by
      rw [← projectiveDimension_le_iff, heq, Nat.cast_add, Nat.cast_one]
      gcongr
      exact (projectiveDimension_le_iff _ _).mpr hM
    have hih := ih (QuotSMulTop x M) (n + 1) hQ hms.2 hreg.2
    rw [← projectiveDimension_le_iff, heq] at hih
    rw [← projectiveDimension_le_iff, List.length_cons]
    rcases Nat.eq_zero_or_pos (d - ms.length) with h0 | hpos
    · rw [h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton] at hih
      exact absurd hih (not_subsingleton M)
    · have hsplit : d - ms.length = (d - (ms.length + 1)) + 1 := by omega
      rw [hsplit, Nat.cast_add, ← Nat.cast_one (R := WithBot ℕ∞)] at hih
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp hih

theorem AuslanderBuchsbaumProjDimUpper.proof : AuslanderBuchsbaumProjDimUpper.Statement := by
  intro R _ _ _ M _ _ _ _ n d ms hM hd hms hreg
  exact hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInverseHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchInverseHolomorphic.proof (hdim : BranchFillDimension.Statement)
    (hopen : NormalOpenMapping.Statement) (hreg : BranchInverseOffHypersurface.Statement)
    (hext : NormalRiemannExtension.Statement) (hirr : NormalLocallyIrreducible.Statement) :
    BranchInverseHolomorphic.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  set Δ := Metric.ball (0 : Fin k → ℂ) r with hΔ
  have hk := hdim σ I h w k r φ B hI hh hw hφd hφi hφZ hB hfill
  set ψ : (σ → ℂ) → Fin k → ℂ := Function.invFunOn φ Δ with hψdef
  have hψφ : ∀ t ∈ Δ, ψ (φ t) = t := fun t ht => hφi.leftInvOn_invFunOn ht
  obtain ⟨O, hOo, hO⟩ := hopen σ I k Δ φ hI hIc hk Metric.isOpen_ball hφd hφi hφZ

  have hψc : ∀ z ∈ φ '' Δ, ContinuousWithinAt ψ (φ '' Δ) z := by
    rintro _ ⟨t, ht, rfl⟩
    rw [ContinuousWithinAt, hψφ t ht, tendsto_nhds]
    intro V hVo htV
    obtain ⟨O', hO'o, hO'⟩ := hopen σ I k (V ∩ Δ) φ hI hIc hk (hVo.inter Metric.isOpen_ball)
      (hφd.mono Set.inter_subset_right) (hφi.mono Set.inter_subset_right)
      (hφZ.mono_left Set.inter_subset_right)
    have hmem : φ t ∈ zeroSetIn I ∩ O' := hO' ▸ Set.mem_image_of_mem φ ⟨htV, ht⟩
    filter_upwards [inter_mem_nhdsWithin (φ '' Δ) (hO'o.mem_nhds hmem.2)] with z hz
    obtain ⟨⟨s, hs, rfl⟩, hzO'⟩ := hz
    have hs' : φ s ∈ φ '' (V ∩ Δ) := by rw [hO']; exact ⟨hφZ hs, hzO'⟩
    obtain ⟨s', hs'V, hss'⟩ := hs'
    rw [Set.mem_preimage, hψφ s hs, ← hφi hs'V.2 hs hss']
    exact hs'V.1
  obtain ⟨h', hh', hreg'⟩ := hreg σ I k hI hk
  have hψreg := hreg' Δ φ ψ Metric.isOpen_ball hφd hφi hφZ hψφ
  rw [hO] at hψreg hψc

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ O) ∧
      Set.EqOn g (fun z => ψ z j) ((zeroSetIn I ∩ O) \ {z | eval z h' = 0}) := by
    intro j
    refine hext σ I h' O (fun z => ψ z j) hI hIc hh' hOo ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψreg z hz
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq hy) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ φ '' Δ := by rw [hO]; exact hz.1
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖ψ (φ t) j‖ ≤ r
      rw [hψφ t ht]
      exact (norm_le_pi_norm t j).trans (mem_ball_zero_iff.mp ht).le
  choose g hg hgeq using hcoord

  have hgψ : ∀ j, ∀ z ∈ zeroSetIn I ∩ O, g j z = ψ z j := by
    intro j z hz
    obtain ⟨B', -, hzB', hB'O, -, hdense⟩ := hirr σ I h' z hI hIc hh' hz.1 O (hOo.mem_nhds hz.2)
    set P := (zeroSetIn I ∩ B') \ {y | eval y h' = 0} with hP
    have hPsub : P ⊆ zeroSetIn I ∩ O := fun y hy => ⟨hy.1.1, hB'O hy.1.2⟩
    have : (𝓝[P] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ⟨hz.1, hzB'⟩)
    have h1 : Tendsto (g j) (𝓝[P] z) (𝓝 (g j z)) := (((hg j).continuousWithinAt hz).mono hPsub).tendsto
    have h2 : Tendsto (fun y => ψ y j) (𝓝[P] z) (𝓝 (ψ z j)) :=
      (((continuous_apply j).continuousAt.comp_continuousWithinAt (hψc z hz)).mono hPsub).tendsto
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hgeq j ⟨hPsub hy, hy.2⟩).symm
  refine ⟨ψ, ?_, hψφ⟩
  rw [hO]
  intro z hz
  choose U hUo hzU F hF hFeq using fun j => hg j z hz
  refine ⟨⋂ j, U j, isOpen_iInter_of_finite hUo, Set.mem_iInter.mpr hzU, fun y j => F j y,
    differentiableOn_pi.mpr fun j => (hF j).mono (Set.iInter_subset _ j), fun y hy => ?_⟩
  funext j
  show ψ y j = F j y
  rw [← hgψ j y hy.1]
  exact hFeq j ⟨hy.1, Set.mem_iInter.mp hy.2 j⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

