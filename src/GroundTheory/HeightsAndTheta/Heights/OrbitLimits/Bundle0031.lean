module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

namespace GoodChartModel

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : projChartIdeal P σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, Gx, map_sub, map_add (f := _), map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sub, map_add (f := _), map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

end GoodChartModel

theorem GoodChartModel.proof (hZ : GoodChartZeroSet.Statement) (hD : GoodChartDim.Statement) :
    GoodChartModel.Statement := by
  intro K _ ι _ P e m σ Ψ hP hΨ
  refine ⟨hZ K ι P e m σ Ψ hP.2.1.2.1, fun J hJ => ?_⟩
  have hdim := hD K ι P e m σ Ψ hP J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GoodChartModel.pow_mem hP hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets

namespace GoodChartZeroSet

section Lemmas

theorem eval_smul_of_isHomogeneous {τ : Type*} {φ : MvPolynomial τ ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : ℂ) (w : τ → ℂ) : eval (c • w) φ = c ^ n * eval w φ :=
  _root_.UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous hφ c w

theorem eval_homogenize {m : ℕ} (f : MvPolynomial (Fin m) ℂ) {D : ℕ} (hD : f.totalDegree ≤ D) (a : Fin m)
    (w : Fin m → ℂ) (hw : w a ≠ 0) :
    eval w (X a * ∑ d ∈ range (D + 1), X a ^ (D - d) * homogeneousComponent d f) =
      w a ^ (D + 1) * eval ((w a)⁻¹ • w) f := by
  have hf : f = ∑ d ∈ range (D + 1), homogeneousComponent d f := by
    conv_lhs => rw [← sum_homogeneousComponent f]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun d _ hd' => ?_
    exact homogeneousComponent_eq_zero (n := d) (φ := f) (by simp at hd'; omega)
  conv_rhs => rw [hf]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, map_sum, eval_X, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : d ≤ D := by simp at hd; omega
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d f), map_mul, map_pow, eval_X]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdD
  rw [Nat.add_sub_cancel_left]
  have hinv : w a ^ d * (w a)⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  linear_combination (-(w a * w a ^ k * eval w (homogeneousComponent d f))) * hinv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_scaleBlock [DecidableEq K] (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (scaleBlock k0 c z) = c • segre z := by
  funext j
  show ∏ k, (if k = k0 then c else 1) * z ⟨k, j k⟩ = c * ∏ k, z ⟨k, j k⟩
  rw [Finset.prod_mul_distrib]
  simp


open Classical in
def linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : MvPolynomial (Fin m) ℂ :=
  ∑ a, C (Ψ (fun i' => if σ a = i' then (1 : ℂ) else 0) 0) * X a

theorem eval_linForm {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : Fin m → ℂ) :
    eval x (linForm σ Ψ) = Ψ (fun i' => x (σ.symm i')) 0 := by
  classical
  rw [linForm]
  have hv : (fun i' => x (σ.symm i')) = ∑ a, x a • fun i' => if σ a = i' then (1 : ℂ) else 0 := by
    rw [pi_eq_sum_univ (fun i' => x (σ.symm i'))]
    exact (Equiv.sum_comp σ _).symm.trans (by simp)
  rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eval_C, eval_X]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem exists_segre_smul (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) {c : ℂ} (hc : c ≠ 0) (hK : IsEmpty K → c = 1) :
    ∃ z' ∈ mcPts P, segre z' = c • segre z := by
  classical
  by_cases h : IsEmpty K
  · exact ⟨z, hz, by rw [hK h, one_smul]⟩
  · obtain ⟨k0⟩ := not_isEmpty_iff.1 h
    exact ⟨scaleBlock k0 c z, scaleBlock_mem_zeroLocus P hP k0 hc hz, segre_scaleBlock k0 c z⟩


omit [∀ k, Fintype (ι k)] in
theorem segre_of_isEmpty (hK : IsEmpty K) (z : (Σ k, ι k) → ℂ) (j : (k : K) → ι k) : segre z j = 1 := by
  simp [segre]

end Lemmas

theorem proof : Statement := by
  intro K _ ι _ P e m σ Ψ hP
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [projChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ projChartSet P σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [projChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have ha1 : IsEmpty K → x a = 1 := fun hK => by
    have h := hv (X a - 1) (by
      rintro _ ⟨z, -, -, rfl⟩
      simp [segre_of_isEmpty hK])
    simpa [sub_eq_zero] using h

  have hzero : (x a)⁻¹ • x ∈ zeroSet (segreChartIdeal P σ (σ a)) := by
    intro f hf
    rw [segreChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul P hP hz (inv_ne_zero h0)
          (fun hK => by rw [segre_of_isEmpty hK, inv_one])
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [SegreChartZeroSet.proof K ι P m σ (σ a) hP] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul P hP hz' ha ha1
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end GoodChartZeroSet

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem LiftCountAlongMultiples.proof (hDat : LiftBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hHSM : TheoremHSMBlock.Statement) (hCount : SupBoundCount.Statement) (hPack : SmallPacking.Statement) :
    LiftCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ _ y D N P0 II a ι' _ x' hD hII harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  classical
  obtain ⟨d, hdy, hdk, hmet, hlift⟩ :=
    hDat K ι Ω y D N P0 a ι' x' hD harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  rw [hdy] at hmet hlift
  set v := liftCoords x' with hv_def
  have hv1 : ∀ j, v j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hv : ∀ j, v j ∈ chartLat y N.a a := fun j => by
    rw [← LiftBlockSections.chartLat_smul_one]
    exact hv1 j
  have hgenv : KH.GeneratesOn y (fun k => (a : ℤ) * N.a k) v := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
    rw [← hsum]
    refine Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ fun j => ?_
    simp [v, liftCoords]
  have hsmooth : IsSmoothHerm N := hsemi.1
  have hB : d.A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) := by rw [d.deg, hdk]

  have htop : II (Option K) (addIdx ι (Fintype.card ι')) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) := by
    rw [hdy]
    exact hTop K ι Ω y D N a (Fintype.card ι') v d.A II hII harith hsmooth ha hv hgenv hB d.semipos.1 hmet
  obtain ⟨hchi, C, hC⟩ := hHSM D (Option K) (addIdx ι (Fintype.card ι')) Ω II d hII
  rw [htop] at hchi
  set t := (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) with ht

  obtain ⟨hfin, -⟩ := hPack K ι Ω y D N (chartLat y N.a) harith hbir hsmooth
    (fun τ => SectionLatticeFinite.chartLat_le_nm y N.a τ)
  have htrans : ∀ n, smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * n) := by
    intro n
    refine LiftBlockSections.smallSectionCount_mono (fun s hs hsm => ⟨?_, ?_⟩) (hfin _)
    · rw [hdy, hdk] at hs
      have := LiftBlockSections.secM_le_chartLat y v (a • N.a) hv1 n hs
      rwa [smul_smul, mul_comm, LiftBlockSections.chartLat_smul_one] at this
    · rw [hdy] at hsm
      exact LiftBlockSections.isSmallH_of_lift hB hv hmet hlift hsm

  set h0 : ℕ → ℝ := fun τ => smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) τ
    with hh0
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hsq : ∀ n : ℕ, (n : ℝ) ^ ((D : ℝ) / 2) = Real.sqrt ((n : ℝ) ^ D) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  set E : ℕ → ℝ := fun n => 2 * C' ^ 2 * Real.log (Real.sqrt 2 * C' ^ 2) * (n : ℝ) ^ D +
    2 * C' ^ 2 * D * ((n : ℝ) ^ D * Real.log n) with hE_def
  have hlow : ∀ n : ℕ, 1 ≤ n → blockChi d n - E n ≤ h0 n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set c := C' * Real.sqrt ((n : ℝ) ^ D) with hc
    have hc1 : 1 ≤ c := by
      have : 1 ≤ Real.sqrt ((n : ℝ) ^ D) := Real.one_le_sqrt.mpr (one_le_pow₀ hn1)
      nlinarith
    have hc2 : c ^ 2 = C' ^ 2 * (n : ℝ) ^ D := by
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
    have hbound : ∀ f : MRing (addIdx ι (Fintype.card ι')), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) →
        ∀ z ∈ mcPts (mCoordIdeal d.y),
          ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f := by
      intro f hf z hz
      refine (hC n hn f hf z hz).trans ?_
      rw [hc, ← hsq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (Real.sqrt_nonneg _)
    obtain ⟨hr, hcnt⟩ := hCount D (Option K) (addIdx ι (Fintype.card ι')) Ω d n c (by linarith) hbound
    set r : ℝ := (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) with hr_def
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hL : 0 ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
      apply Real.log_nonneg
      have : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith
    have hrE : r * Real.log (c * Real.sqrt r) ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := by
      by_cases h0r : r = 0
      · rw [h0r, zero_mul]
        positivity
      have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0r)
      have hlog : Real.log (c * Real.sqrt r) ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
        apply Real.log_le_log (by positivity)
        have h1 : Real.sqrt r ≤ Real.sqrt 2 * c := by
          rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ c), ← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt hr
        nlinarith
      calc r * Real.log (c * Real.sqrt r) ≤ r * Real.log (Real.sqrt 2 * c ^ 2) :=
            mul_le_mul_of_nonneg_left hlog hr0
        _ ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := mul_le_mul_of_nonneg_right hr hL
    have hEn : 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) = E n := by
      have hnpos : (0 : ℝ) < n := by linarith
      have hlg : Real.log (Real.sqrt 2 * c ^ 2) = Real.log (Real.sqrt 2 * C' ^ 2) + D * Real.log n := by
        rw [hc2, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      rw [hlg, hc2]
      simp only [hE_def]
      ring
    have : blockChi d n - E n ≤ blockChi d n - r * Real.log (c * Real.sqrt r) := by linarith
    exact this.trans hcnt

  have hF : (fun n => hsDefect D (blockChi d) t n - E n) =o[atTop] pw D :=
    hchi.sub (ArithmeticVolumeResolution.error_isLittleO D _ _)

  intro ε hε
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hF.def (div_pos hε hfac), eventually_ge_atTop 1] with n hFn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by positivity
  have habs : -(ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1)) ≤ hsDefect D (blockChi d) t n - E n := by
    have := neg_abs_le (hsDefect D (blockChi d) t n - E n)
    rw [Real.norm_eq_abs, pw, Real.norm_eq_abs, abs_of_pos hnpos] at hFn
    linarith
  have hl := hlow n hn
  have htr := htrans n
  have key : (t - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      t * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  simp only [hsDefect] at habs
  simp only [hh0] at hl
  linarith

end

end GroundTheory.Heights₂.Heights.Targets
end

