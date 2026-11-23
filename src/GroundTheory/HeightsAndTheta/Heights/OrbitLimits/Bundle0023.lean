module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LogRegLineTensor
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem log_regLine_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι) {ε : ℝ} (hε : 0 < ε) {a : K → ℕ} (ha : ∀ k, A.a k = a k) (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (((regLine A s ε ha hs).tensor A).h z) =
      Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2 := by
  have hh : 0 < A.h z := A.pos z hz
  have hreg : Real.log ((regLine A s ε ha hs).h z) = regLog A s ε z := congrFun (log_regLine A s ε ha hs) z
  have hpos : 0 < (regLine A s ε ha hs).h z := (regLine A s ε ha hs).pos z hz
  show Real.log ((regLine A s ε ha hs).h z * A.h z) = _
  rw [Real.log_mul hpos.ne' hh.ne', hreg]
  unfold regLog normSq
  set x := ‖eval z (map (Int.castRingHom ℂ) s)‖
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hnum : 0 < x ^ 2 + ε * A.h z ^ 2 := by positivity
  have hq : (x / A.h z) ^ 2 + ε = (x ^ 2 + ε * A.h z ^ 2) / A.h z ^ 2 := by
    field_simp
  rw [hq, Real.log_div hnum.ne' (pow_pos hh 2).ne', Real.log_pow]
  push_cast
  ring

theorem PoincareLelongLimit.proof (hInt : PtsIntegrableStatement) (hLel : LelongSectionLimit.Statement) :
    PoincareLelongLimit.Statement := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hAdd := Inter.PtsAddFirst.proof hInt
  have key : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) := by
    intro ε hε
    have h1 := Inter.ptsIntegral_add_first_log hAdd (Q := P) (e := n) (L := L)
      (M := regLine A s ε ha hsa) (N := A) (D := B) hP hL (isSmoothHerm_regLine hA hε ha hsa) hA hB hBa
    rw [log_regLine] at h1
    have h2 : ptsIntegral P (Fin.cons (fun z => Real.log (((regLine A s ε ha hsa).tensor A).h z)) (pot L))
          (fun z => Real.log (B.h z)) =
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) (fun z => Real.log (B.h z)) := by
      refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
      refine Fin.cases ?_ (fun i => ?_) j
      · intro z hz
        simp only [Fin.cons_zero]
        exact log_regLine_tensor A s hε ha hsa z hz.1
      · intro z _
        simp only [Fin.cons_succ]
    rw [← h2, h1]
    ring
  exact ((hLel K ι P n L A B s hP hL hA hB hBa hs).sub_const _).congr'
    (eventually_nhdsWithin_of_forall key)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorCompare
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt divSupp_finite divSuppArith)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift
  SegreChartIntegral.Statement)

theorem segreChartSet_mono {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    segreChartSet W σ i ⊆ segreChartSet P σ i := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz1, fun f hf => hz2 f (h hf)⟩, hzi, rfl⟩

theorem ptsIntegral_eq_sum_chart (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)} {n m : ℕ}
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ} {δ : ℝ}
    {G : (Fin m → ℂ) → ℝ} {Φ : Fin n → (Fin m → ℂ) → ℝ} (hW : IsArithVar W (n + 1)) (hPW : P ≤ W)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) (hδ : 0 < δ)
    (hsupp : ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0)
    (hgerm : ∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) :
    ptsIntegral W (pot L) g = ∑ W' ∈ segreChartComponents W σ i, varInt W' n G Φ := by
  have hsub := segreChartSet_mono hPW σ i
  cases n with
  | zero => exact hPts K ι W m σ i L g δ G Φ hW hg hδ hsupp fun x hx => (hgerm x (hsub hx)).1
  | succ e => exact hInt K ι W e m σ i L g δ G Φ hW hL hg hδ (Or.inl hsupp) fun x hx => hgerm x (hsub hx)

theorem ChartDivisorCompare.proof (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    (hComp : ChartDivisorComponents.Statement) (hLen : ChartDivisorLength.Statement) :
    ChartDivisorCompare.Statement := by
  classical
  intro K _ _ ι _ P n m σ i L A s g δ G Φ hP hL hs hg hδ hsupp hgerm
  obtain ⟨hmin, hdisj⟩ := hComp K ι P n m σ i A s hP hs
  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  set S := hfin.toFinset with hS
  set T := S.biUnion fun W => segreChartComponents W σ i with hT
  have hA : ∀ J ∈ segreChartComponents P σ i,
      ∑ᶠ (W' : Ideal (MvPolynomial (Fin m) ℂ)) (_ : W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ =
        ∑ W' ∈ T, if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0 := by
    intro J hJ
    have hset : (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes = ↑(T.filter fun W' => J ≤ W') := by
      ext W'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmin J hJ W', hT, hS, Finset.mem_biUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto
    rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hB : ∀ W ∈ S, ∀ W' ∈ segreChartComponents W σ i,
      ∑ J ∈ segreChartComponents P σ i, (if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0) =
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * varInt W' n G Φ := by
    intro W hW W' hW'
    rw [Set.Finite.mem_toFinset] at hW
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← Nat.cast_sum, hLen K ι P n m σ i A s hP hs W hW.1 hW.2 W' hW']
  have hdisjT : (↑S : Set (Ideal (MRing ι))).PairwiseDisjoint fun W => segreChartComponents W σ i := by
    intro W₁ h₁ W₂ h₂ hne
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact Finset.disjoint_left.2 fun W' hW₁ hW₂ => hne (hdisj W₁ W₂ h₁ h₂ W' hW₁ hW₂)
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_biUnion hdisjT,
    Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl (hB W hW), eq_comm]
  refine (finsum_mem_eq_finite_toFinset_sum
    (fun W => (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g) hfin).trans ?_
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.mul_sum]
  rw [Set.Finite.mem_toFinset] at hW
  have hWv : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  rw [ptsIntegral_eq_sum_chart hInt hPts hWv (le_sup_left.trans hW.1.1.1.2) hL hg hδ hsupp hgerm]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

namespace ComponentsGenericCount

theorem proof : ComponentsGenericCount.Statement := by
  classical
  intro n d F A hF hinc
  have hfib : ∀ y, {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} = ⋃ J ∈ F, GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y := by
    intro y; ext x; simp only [GroundTheory.Heights₂.Heights.ComplexSets.fibre, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]; tauto
  have hcard : ∀ J ∈ F, ∀ y, (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).encard ≤ (projDegree J A : ℕ∞) := by
    intro J hJ y
    obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2 y
    rw [← hfin.cast_ncard_eq]; exact_mod_cast hle
  refine ⟨fun y => ?_, ?_⟩
  · rw [hfib, Nat.cast_sum]
    exact (encard_biUnion_le F _).trans (Finset.sum_le_sum fun J hJ => hcard J hJ y)
  obtain ⟨Δ₁, hΔ₁, hΔ₁y⟩ := exists_prod_ne_zero F
    (fun J P => ∀ y, eval y P ≠ 0 → (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite ∧ (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).ncard = projDegree J A ∧
      ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
        DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ g y' ∈ zeroSet J)
    (fun J hJ => by
      obtain ⟨P, hP, hPy⟩ :=
        ComplexSets.DiscriminantCover.full n d J A (hF J hJ).1 (hF J hJ).2.1 (hF J hJ).2.2
      refine ⟨P, hP, fun y hy => ?_⟩
      obtain ⟨hfin, hc, hsec⟩ := hPy y hy
      refine ⟨hfin, hc, fun x hx => ?_⟩
      obtain ⟨U, V, g, hU, hyU, -, -, hg, hgx, hAg, hZ⟩ := hsec x hx
      refine ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨hAg y' hy', ?_⟩⟩
      have hmem : g y' ∈ zeroSet J ∩ V := hZ ▸ Set.mem_image_of_mem g hy'
      exact hmem.1)
  obtain ⟨Δ₂, hΔ₂, hΔ₂y⟩ := exists_prod_ne_zero ((F ×ˢ F).filter fun p => p.1 ≠ p.2)
    (fun p c => ∀ x ∈ zeroSet p.1, x ∈ zeroSet p.2 → eval (A *ᵥ x) c = 0)
    (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact exists_pair_poly p.1 p.2 A (hF _ hp.1.1).1 (hF _ hp.1.1).2.2
        fun h => hp.2 (hinc _ hp.1.2 _ hp.1.1 h).symm)
  refine ⟨Δ₁ * Δ₂, mul_ne_zero hΔ₁ hΔ₂, fun y hy => ?_⟩
  rw [map_mul] at hy
  have h1 := hΔ₁y y (left_ne_zero_of_mul hy)
  have h2 := hΔ₂y y (right_ne_zero_of_mul hy)
  refine ⟨?_, ?_⟩
  · rw [hfib, Nat.cast_sum, encard_biUnion_eq]
    · refine Finset.sum_congr rfl fun J hJ => ?_
      obtain ⟨P, hP, hPy⟩ := h1 J hJ
      obtain ⟨hfin, hc, -⟩ := hP y hPy
      rw [← hfin.cast_ncard_eq, hc]
    · intro J hJ J' hJ' hne
      rw [Set.disjoint_left]
      rintro x ⟨hxJ, hxy⟩ ⟨hxJ', -⟩
      obtain ⟨c, hc, hcy⟩ := h2 (J, J') (by simp [hJ, hJ', hne])
      exact hcy (by rw [← hxy]; exact hc x hxJ hxJ')
  · rintro x ⟨J, hJ, hxJ⟩ hxy
    obtain ⟨P, hP, hPy⟩ := h1 J hJ
    obtain ⟨U, g, hU, hyU, hg, hgx, hsec⟩ := (hP y hPy).2.2 x ⟨hxJ, hxy⟩
    exact ⟨U, g, hU, hyU, hg, hgx, fun y' hy' => ⟨(hsec y' hy').1, J, hJ, (hsec y' hy').2⟩⟩

end ComponentsGenericCount

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace PointsBilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem contDiffAt_comp {D : ℕ} {u : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => u (γ y')) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ u (γ y) := hu.1.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp (hρ.comp y hc)) 2

theorem cxHessian_sum {D : ℕ} {T : Type} [Fintype T] (f : T → (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hf : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (f t) y') :
    cxHessian (fun y' => ∑ t, f t y') y = ∑ t, cxHessian (f t) y := by
  have h1 : fderiv ℝ (fun y' => ∑ t, f t y') =ᶠ[𝓝 y] fun y' => ∑ t, fderiv ℝ (f t) y' := by
    filter_upwards [eventually_all.mpr hf] with y' hy'
    exact fderiv_fun_sum fun t _ => (hy' t).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => ∑ t, f t y')) y = ∑ t, fderiv ℝ (fderiv ℝ (f t)) y := by
    rw [h1.fderiv_eq]
    exact fderiv_fun_sum fun t _ =>
      ((hf t).self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  simp only [cxHessian, h2, FunLike.coe_sum, Finset.sum_apply, Matrix.sum_apply]
  push_cast
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

theorem mixedDisc_update_sum {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_sum]

theorem cxHessian_cons {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (f v : ((Σ k, ι k) → ℂ) → ℝ)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian
        (fun y' => (Fin.cons f (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) =
      Function.update (fun k => cxHessian
        (fun y' => (Fin.cons v (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) 0
        (cxHessian (fun y' => f (γ y')) y) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Function.update_self]
    simp only [Fin.cons_zero]
  · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [Fin.cons_succ]

theorem maDensity_cons_sum {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) {T : Type} [Fintype T]
    {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ} {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => (Fin.cons (fun z => ∑ t, u t z) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y =
      ∑ t, maDensity (fun j y' => (Fin.cons (u t) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have hc : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => u t (γ y'')) y' := fun t => by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_comp (hu t) (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hH := cxHessian_sum (fun t y' => u t (γ y')) hc
  simp only [maDensity]
  rw [cxHessian_cons L _ (fun _ => 0) γ y]
  simp only [hH, mixedDisc_update_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cxHessian_cons L (u t) (fun _ => 0) γ y]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_sum_left {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h, Finset.sum_mul]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem sheetDensity_sum_right {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    {T : Type} [Fintype T] {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Fin.cons (fun z => ∑ t, u t z) (pot L)) g y w =
      ∑ t, sheetDensity P Ψ (Fin.cons (u t) (pot L)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_cons_sum L hu hγ, Finset.mul_sum]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem finsum_mem_sum_comm {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hS).symm

theorem isSmoothHerm_ofWeight {w : ((Σ k, ι k) → ℂ) → ℝ}
    (hw : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → w (fun p => c p.1 * z p) = w z)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (HermLine.ofWeight w hw) := by
  have e : (HermLine.ofWeight w hw).h = fun z => Real.exp (-w z) := rfl
  unfold IsSmoothHerm
  rw [e]
  exact Real.contDiff_exp.comp_contDiffOn hs.neg

theorem integrable_fibreSum (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by
  have hf' : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → -f (fun p => c p.1 * z p) = -f z :=
    fun c z hc => by simp only [hf.2 c z hc]
  have hF := isSmoothHerm_ofWeight (w := fun z => -f z) hf' hf.1.neg
  have hG := isSmoothHerm_ofWeight hg.2 hg.1
  have hLF : ∀ j, IsSmoothHerm ((Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero] using hF
    · simpa only [Fin.cons_succ] using hL j
  have hpot : pot (Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.cons f (pot L) := by
    funext j z
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pot, HermLine.ofWeight, Real.log_exp]
    · simp [pot]
  have hlog : logNorm (HermLine.ofWeight g hg.2) 1 = g := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  have hsec : IsSectionOn P (HermLine.ofWeight g hg.2) 1 :=
    ⟨fun _ => 0, fun k => by simp [HermLine.ofWeight], hm, h1⟩
  have := hInt K ι P (n + 1) Ψ _ _ 1 hP hΨ hLF hG hsec
  rwa [hpot, hlog] at this

end PointsBilinear


open PointsBilinear in
theorem PtsBilinear.proof (hAbs : Inter.PtsAbsIntegrable.Statement) (hMeas : PtsSumMeasurable.Statement) :
    PtsBilinear.Statement := by
  have hInt := PtsIntegrable.of_found hAbs hMeas
  intro K _ ι _ P n L T _ u v hP hL hu hv
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    have hfin := fibreFinite K ι P (n + 1) hΨ.choose hP hΨ.choose_spec
    unfold ptsIntegralAt
    constructor
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL hv (hu t)]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_left P hΨ.choose _ u y w,
        finsum_mem_sum_comm (hfin y)]
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL (hu t) hv]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_right P hΨ.choose L hu v y w,
        finsum_mem_sum_comm (hfin y)]
  · simp only [dif_neg hΨ, Finset.sum_const_zero, and_self]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeLength
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartConeLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∀ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
          W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W' →
            localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
              localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W''

end GroundTheory.Heights₂.Heights.Targets
end
end

