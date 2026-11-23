module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPsh
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackThird
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorization
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv

theorem lastCol_mem {N j : ℕ} {a ca : Fin N} (hj : j ≤ N) (hca : (ca : ℕ) = lastCol N j a) :
    ca ∈ stepCols N j a ∧ ∀ r ∈ stepCols N j a, r ≤ ca := by
  unfold lastCol at hca
  refine ⟨?_, ?_⟩
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · intro r hr
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fin.le_iff_val_le_val]
    split_ifs at hca hr <;> omega

theorem transv_mul_transv {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s : ℂ) :
    (1 + Matrix.single cb ca s) * (1 + Matrix.single cb ca (-s)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne s cb ca cb hne (-s), add_zero,
    add_assoc, ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

theorem main : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  intro N j a ca cb L U t' hj hca hcb hblk hL hLu hU hUt hUd hmin
  have hne : ca ≠ cb := by
    intro h
    have h1 := congrArg Fin.val h
    omega
  obtain ⟨hcaS, hmax⟩ := lastCol_mem hj hca
  have hLM : L * U * (1 + Matrix.single cb ca t') = L * (U * (1 + Matrix.single cb ca t')) :=
    Matrix.mul_assoc _ _ _
  set M := U * (1 + Matrix.single cb ca t') with hMdef
  have hMe : ∀ x y, M x y = U x y + if y = ca then U x cb * t' else 0 := by
    intro x y
    rw [hMdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    split_ifs with hy
    · rw [hy, Matrix.mul_single_apply_same]
    · rw [Matrix.mul_single_apply_of_ne t' cb ca x y hy U]
  have hUz : ∀ x y : Fin N, y < x → U x y = 0 := fun x y h => hUt (show id y < id x from h)
  have hMut : ∀ x y : Fin N, y < x → x ≠ cb → M x y = 0 := by
    intro x y hxy hx
    rw [hMe, hUz x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      have h1 : cb < x := by
        rw [Fin.lt_iff_val_lt_val] at hxy ⊢
        have h2 : (x : ℕ) ≠ cb := fun h => hx (Fin.ext h)
        omega
      rw [hUz x cb h1]
      simp
    · simp
  have hMca : M ca ca ≠ 0 := by
    intro h0
    apply hmin
    rw [hLM]
    unfold minorIJ
    rw [dite_eq_left rfl]
    set f := (stepCols N j a).orderEmbOfFin (rfl : (stepCols N j a).card = (stepCols N j a).card) with hf
    have hfmem : ∀ r, f r ∈ stepCols N j a := fun r => Finset.orderEmbOfFin_mem _ _ r
    have hSmap : Finset.univ.map f.toEmbedding = stepCols N j a := Finset.map_orderEmbOfFin_univ _ _
    have hrange : Set.range f = ↑(stepCols N j a) := Finset.range_orderEmbOfFin _ _
    have hprod : (L * M).submatrix f f = L.submatrix f f * M.submatrix f f := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      have hfpS := hfmem p
      have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ stepCols N j a → L (f p) i * M i (f q) = 0 := by
        intro i _ hi
        by_cases hic : (ca : ℕ) < i
        · have hfp := hmax (f p) hfpS
          have hlt : f p < i := by
            rw [Fin.le_iff_val_le_val] at hfp
            rw [Fin.lt_iff_val_lt_val]
            omega
          rw [hLu.2 (f p) i hlt, zero_mul]
        · have hLz : L (f p) i = 0 := by
            apply hL
            intro hiff
            simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hfpS
            unfold lastCol at hca
            split_ifs at hi hfpS hca
            · have h3 := hiff.mpr (by omega)
              omega
            · omega
          rw [hLz, zero_mul]
      have hm := Finset.sum_map Finset.univ f.toEmbedding (fun x => L (f p) x * M x (f q))
      rw [hSmap] at hm
      rw [← Finset.sum_subset (Finset.subset_univ (stepCols N j a)) hz]
      exact hm
    have hUT : (M.submatrix f f).IsUpperTriangular := by
      intro p q hpq
      rw [Matrix.submatrix_apply]
      have hfpcb : f p ≠ cb := by
        intro hfp
        have h4 := hmax (f p) (hfmem p)
        rw [hfp, Fin.le_iff_val_le_val] at h4
        omega
      exact hMut (f p) (f q) (f.strictMono hpq) hfpcb
    have hdetM : (M.submatrix f f).det = 0 := by
      rw [Matrix.det_of_upperTriangular hUT]
      obtain ⟨p0, hp0⟩ : ∃ p0, f p0 = ca := by
        have h1 : ca ∈ Set.range f := by
          rw [hrange]
          exact hcaS
        exact h1
      exact Finset.prod_eq_zero (Finset.mem_univ p0) (by rw [Matrix.submatrix_apply, hp0]; exact h0)
    rw [hprod, Matrix.det_mul, hdetM, mul_zero]
  have hMb : ∀ x y : Fin N, ¬((x : ℕ) < N - j ↔ (y : ℕ) < N - j) → M x y = 0 := by
    intro x y hxy
    rw [hMe, hU x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      rw [hU x cb (fun h => hxy (h.trans hblk.symm))]
      simp
    · simp
  set t := M cb ca / M ca ca with ht
  have hVe : ∀ x y, ((1 + Matrix.single cb ca (-t)) * M) x y = M x y + if x = cb then -t * M ca y else 0 := by
    intro x y
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    split_ifs with hx
    · rw [hx, Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (-t) cb ca x y hx M]
  refine ⟨t, (1 + Matrix.single cb ca (-t)) * M, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hVe, hMb x y hxy]
    split_ifs with hx
    · rw [hx] at hxy
      rw [hMb ca y (fun h => hxy (hblk.symm.trans h))]
      simp
    · simp
  · intro x y hxy
    change y < x at hxy
    rw [hVe]
    by_cases hx : x = cb
    · rw [if_pos hx, hx]
      rw [hx] at hxy
      by_cases hy : y = ca
      · rw [hy, ht, neg_mul, div_mul_cancel₀ _ hMca, add_neg_cancel]
      · have hylt : y < ca := by
          rw [Fin.lt_iff_val_lt_val] at hxy ⊢
          have h2 : (y : ℕ) ≠ ca := fun h => hy (Fin.ext h)
          omega
        rw [hMe cb y, if_neg hy, hUz cb y hxy, hMe ca y, if_neg hy, hUz ca y hylt]
        simp
    · rw [if_neg hx, add_zero]
      exact hMut x y hxy hx
  · intro c hc
    rw [hVe]
    have hcle := hmax c hc
    have hccb : c ≠ cb := by
      intro h
      rw [h, Fin.le_iff_val_le_val] at hcle
      omega
    rw [if_neg hccb, add_zero]
    by_cases hcc : c = ca
    · rw [hcc]
      exact hMca
    · rw [hMe, if_neg hcc, add_zero]
      exact hUd c
  · rw [← Matrix.mul_assoc, transv_mul_transv hne t, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_injective_linear {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (h : Module.finrank ℂ W ≤ n) : ∃ j : W →ₗ[ℂ] (Fin n → ℂ), Function.Injective j := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp)
  let s : Fin (Module.finrank ℂ W) → Fin n := Fin.castLE h
  have hs : Function.Injective s := Fin.castLE_injective h
  refine ⟨(Function.ExtendByZero.linearMap ℂ ℂ s).comp e.toLinearMap, fun a b hab => e.injective ?_⟩
  funext i
  have := congrFun hab (s i)
  change Function.extend s (e a) 0 (s i) = Function.extend s (e b) 0 (s i) at this
  rwa [hs.extend_apply, hs.extend_apply] at this

theorem exists_injOn_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Φ : E → F} {L : E →L[ℂ] F} {w : E}
    (hΦ : HasStrictFDerivAt Φ L w) (hL : Function.Injective L) :
    ∃ B : Set E, IsOpen B ∧ w ∈ B ∧ Set.InjOn Φ B := by
  obtain ⟨N, hN, hanti⟩ := (L : E →ₗ[ℂ] F).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hL)
  have hc : (0 : NNReal) < (2 * N)⁻¹ := by positivity
  obtain ⟨s, hs, hap⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * N)⁻¹) (Or.inr hc)
  obtain ⟨B, hBs, hB, hwB⟩ := mem_nhds_iff.1 hs
  refine ⟨B, hB, hwB, fun u hu v hv huv => ?_⟩
  have h1 := hap u (hBs hu) v (hBs hv)
  rw [huv, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖u - v‖ ≤ N * ‖L (u - v)‖ := by
    have := hanti.le_mul_dist (u - v) 0
    simpa [dist_eq_norm] using this
  by_contra hne
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ‖u - v‖ ≤ N * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hN'.le)
  have h4 : (N : ℝ) * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) = ‖u - v‖ / 2 := by
    push_cast
    field_simp
  rw [h4] at h3
  linarith

theorem exists_linear_separation {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (n : ℕ)
    (hcard : Fintype.card σ ≤ Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) + n) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin n → ℂ)) (B : Set (σ → ℂ)), IsOpen B ∧ w ∈ B ∧
      ∀ u ∈ B, ∀ v ∈ B, (∀ h ∈ I, eval u h = 0) → (∀ h ∈ I, eval v h = 0) → π u = π v → u = v := by
  classical
  set S : Set (σ → ℂ) := (fun h : MvPolynomial σ ℂ => fun j => eval w (pderiv j h)) '' (I : Set _) with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hex : ∀ t : b, ∃ f ∈ I, (fun j => eval w (pderiv j f)) = (t : σ → ℂ) := fun t => by
    obtain ⟨f, hf, h⟩ := hbS t.2
    exact ⟨f, hf, h⟩
  choose F hFI hFg using hex
  let M : Matrix b σ ℂ := fun t q => (t : σ → ℂ) q
  have hrank : M.rank = Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Set.range M.row = b := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact t.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [this, hspan]
    rfl
  let W : Submodule ℂ (σ → ℂ) := LinearMap.ker M.mulVecLin
  have hW : Module.finrank ℂ W ≤ n := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h' : Module.finrank ℂ (LinearMap.range M.mulVecLin) = M.rank := rfl
    simp only [Module.finrank_fintype_fun_eq_card] at h
    show Module.finrank ℂ (LinearMap.ker M.mulVecLin) ≤ n
    omega
  obtain ⟨j, hj⟩ := exists_injective_linear hW
  obtain ⟨l, hl⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  let π : (σ → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (j.comp l)
  let Φ : (σ → ℂ) → (b → ℂ) × (Fin n → ℂ) := fun x => (fun t => eval x (F t), π x)
  let L0 : (σ → ℂ) →L[ℂ] (b → ℂ) := ContinuousLinearMap.pi fun t => polyDiff (F t) w
  have hd : HasStrictFDerivAt Φ (L0.prod π) w :=
    (hasStrictFDerivAt_pi.2 fun t => hasStrictFDerivAt_eval_poly (F t) w).prodMk π.hasStrictFDerivAt
  have hinj : Function.Injective (L0.prod π) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : L0 v = 0 := congrArg Prod.fst hv
    have h2 : π v = 0 := congrArg Prod.snd hv
    have hvW : v ∈ W := by
      show M.mulVecLin v = 0
      funext t
      have h3 := congrFun h1 t
      have h4 : polyDiff (F t) w v = 0 := h3
      rw [polyDiff_apply] at h4
      have h5 : ∀ q, eval w (pderiv q (F t)) = (t : σ → ℂ) q := fun q => congrFun (hFg t) q
      simp only [h5] at h4
      show ∑ q, (t : σ → ℂ) q * v q = 0
      exact h4
    have h6 : j (l v) = 0 := h2
    have h7 : l v = 0 := hj (by rw [h6, map_zero])
    have h8 : l (W.subtype ⟨v, hvW⟩) = ⟨v, hvW⟩ := LinearMap.congr_fun hl _
    have h9 : (⟨v, hvW⟩ : W) = 0 := by rw [← h8]; exact h7
    exact congrArg Subtype.val h9
  obtain ⟨B, hB, hwB, hBinj⟩ := exists_injOn_of_strict hd hinj
  refine ⟨π, B, hB, hwB, fun u hu v hv hIu hIv huv => hBinj hu hv ?_⟩
  refine Prod.ext (funext fun t => ?_) huv
  show eval u (F t) = eval v (F t)
  rw [hIu _ (hFI t), hIv _ (hFI t)]

theorem localOrbitChart : LocalOrbitChart.Statement := by
  intro K _ ι _ Ω _ inst y n hP hsm z₀ hz₀
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z₀ hz₀.1
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz₀.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  have hzero : ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, p k⟩ ≠ 0) →
      ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p,
        eval (ReciprocityTheory.AnForm.R.affCoord p z) h = 0 := fun z hz hzp =>
    (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hzp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)
  have hrank := GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy
    (ReciprocityTheory.AnForm.R.affCoord p z₀) (hzero z₀ hz₀ hp)
  obtain ⟨π, B, hB, hwB, hsep⟩ := exists_linear_separation _ _ n hrank
  let D : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, z ⟨k, p k⟩ ≠ 0}
  have hDopen : IsOpen D := by
    have : D = ⋂ k, {z | z ⟨k, p k⟩ ≠ 0} := by ext z; simp [D]
    rw [this]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have han : ∀ z ∈ D, AnalyticAt ℂ (ReciprocityTheory.AnForm.R.affCoord p) z := by
    intro z hz
    refine analyticAt_pi_iff.2 fun q => ?_
    have hc : ∀ r : Σ k, ι k, AnalyticAt ℂ (fun v : (Σ k, ι k) → ℂ => v r) z := fun r =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) r).analyticAt z
    exact (hc q).div (hc ⟨q.1, p q.1⟩) (hz q.1)
  have hcont : ContinuousOn (ReciprocityTheory.AnForm.R.affCoord p) D := fun z hz =>
    (han z hz).continuousAt.continuousWithinAt
  refine ⟨D ∩ ReciprocityTheory.AnForm.R.affCoord p ⁻¹' B, hcont.isOpen_inter_preimage hDopen hB, ⟨hp, hwB⟩,
    fun z => π (ReciprocityTheory.AnForm.R.affCoord p z), ?_, ?_, ?_⟩
  · intro z hz
    exact (π.analyticAt _).comp (han z hz.1)
  · intro z hz c hc
    have hA : ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) = ReciprocityTheory.AnForm.R.affCoord p z :=
      ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit p ⟨c, hc, rfl⟩
    refine ⟨⟨fun k => mul_ne_zero (hc k) (hz.1 k), ?_⟩, ?_⟩
    · show ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) ∈ B
      rw [hA]
      exact hz.2
    · show π _ = π _
      rw [hA]
  · rintro z ⟨hzN, hzX⟩ z' ⟨hzN', hzX'⟩ hκ
    have hA := hsep _ hzN.2 _ hzN'.2 (hzero z hzX hzN.1) (hzero z' hzX' hzN'.1) hκ
    refine ⟨fun k => z' ⟨k, p k⟩ / z ⟨k, p k⟩, fun k => div_ne_zero (hzN'.1 k) (hzN.1 k), ?_⟩
    funext q
    have h1 : z q / z ⟨q.1, p q.1⟩ = z' q / z' ⟨q.1, p q.1⟩ := congrFun hA q
    have h2 := hzN.1 q.1
    have h3 := hzN'.1 q.1
    show z' q = z' ⟨q.1, p q.1⟩ / z ⟨q.1, p q.1⟩ * z q
    rw [div_mul_eq_mul_div, eq_div_iff h2]
    rw [div_eq_div_iff h2 h3] at h1
    linear_combination -h1

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem stepWeight_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) → ∀ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (B : FinHolAtlas e R.X), (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))) → IsPotential R.A (BM.L.pullback pr hp.1) → IsSection R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m (fun k => pr ⁻¹' BM.W k) → IsAdaptedAtlas R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) → ∃ (ph : R.X → ℝ) (C₅ : ℝ), (∀ x, pr x ∉ bdry BM.s → ∀ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x → Real.log ((BM.hom p).h z) = Real.log ((fsHerm ι (M.dy p)).h z) + ph x) ∧ (∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → ph x = ph x') ∧ IsSingWeight R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) (potOf R (fsHerm ιk fun k => M.dy p (κ k))) ph C₅ ∧ IsGradBound B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) ph C₅ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM p Kk _ ιk _ κ v hb hr e R pr hp B h1 hpot hsec hsnc had
  have hyp : IsStepHyp M BM p κ v R pr := ⟨hb, hr, hp, h1⟩
  have hc := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.ChartEx.hasStepCharts K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp
  have hfs : IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential Kk ιk _ e R).1 _ (_root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm Kk ιk _)
  have hnorm : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  have hsm := _root_.GlobalTheory.CompanionTheory.Ar.PB.CWeight.smoothOn_stepPh K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hps := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc
  obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  have hgr := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hp hc hfs
  obtain ⟨C₂, hC₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.isSingWeight_of_logGrowth e R.X R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm _ (stepPh M BM p v R pr) C₁ hfs hsm hps hC₁
  obtain ⟨C₃, hC₃⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.gradBound_of_local_bounds e R.X R.A B (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.nb BM.m
    (fun k => pr ⁻¹' BM.W k) hpot hsec hsnc hnorm had (stepPh M BM p v R pr) hsm hgr
  refine ⟨stepPh M BM p v R pr, max C₂ C₃, ?_, ?_, ?_, hC₃ _ (le_max_right _ _)⟩
  · intro x hx z hz hzv
    have := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.Wgt.main K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x z (R.mem_U x) hx hz hzv
    rw [this, stepGap]
    ring
  · intro x x' hxx hk
    exact _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main K ι Φ y Ψ N j M n BM p Kk ιk κ v e R pr hyp x x' hxx hk
  · obtain ⟨h1', h2', h3', h4'⟩ := hC₂
    refine ⟨h1', h2', h3', fun x hx => ?_⟩
    have hlog : 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
      apply Real.log_nonneg
      have := hnorm x
      have h2 := Real.add_one_le_exp (1 : ℝ)
      unfold rW
      linarith
    obtain ⟨ha, hb'⟩ := h4' x hx
    refine ⟨?_, hb'.trans (le_max_left _ _)⟩
    have : -max C₂ C₃ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) ≤
        -C₂ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left _ _)) hlog
    exact this.trans ha

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpen
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PshAdd

open ReciprocityTheory.AnForm.M.LocPot

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  intro x j y hy w
  obtain ⟨hyt, ⟨⟨hyP, -⟩, hyΘ⟩, hyU⟩ := hy
  have hP2 : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hyt, hyP⟩
    exact ((hP.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hf2 : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, hyU⟩
    exact ((hf j).contDiffAt hmem).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)).mem_nhds ⟨hyt, hyΘ⟩
    exact ((hΘ.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hPf2 : ContDiffAt ℝ 2 (fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) y :=
    hP2.add hf2
  have h1 := hPf x j y ⟨hyt, ⟨hyP, Set.mem_univ _⟩, hyU⟩ w
  have h2 := hΘp x j y ⟨hyt, hyΘ⟩ w
  have hsum := ReciprocityTheory.AnForm.levi_add_smul (f := fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z))
    (g := Θ.φ x ∘ (A.chart j).symm) 1 hPf2 hΘ2 w
  have heq : ((P + LocPot.ofFun f + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) +
        1 * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z; simp [Function.comp, HAdd.hAdd, Add.add, LocPot.ofFun]
  rw [heq, hsum, one_mul]
  exact add_nonneg h1 h2

end GlobalTheory.CompanionTheory.Ar.PshAdd
end

