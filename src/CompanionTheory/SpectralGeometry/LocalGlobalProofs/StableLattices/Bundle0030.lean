module

public import Mathlib
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHom
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckMatHom

theorem mAct_coord {ι ι' V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ)
    (x : ι → V) (c : ι') : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct, LinearMap.sum_apply]

theorem mAct_mAct {ι ι' ι'' V : Type} [Fintype ι] [Fintype ι'] [AddCommGroup V] [Module ℂ V]
    (A : Matrix ι'' ι' ℂ) (B : Matrix ι' ι ℂ) (x : ι → V) :
    mAct A (mAct B x) = mAct (A * B) x := by
  funext c
  simp only [mAct_coord, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem dOp_mAct {ι ι' V V' : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (A : Matrix ι' ι ℂ) (T : V →ₗ[ℂ] V') (x : ι → V) :
    dOp ι' T (mAct A x) = mAct A (dOp ι T x) := by
  funext c
  have h : ∀ (κ : Type) (y : κ → V) (e : κ), dOp κ T y e = T (y e) := fun _ _ _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, mAct_coord, map_sum, map_smul]

theorem dsigW_eq_prod {k r : ℕ} (U : URep k r) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)), LieWd k r W → ∀ v : U.R.smSub,
      PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W (v : U.R.H) = ((W.map U.dsig).prod v : U.R.H)
  | [], _, _ => rfl
  | X :: W, hW, v => by
    have ih := dsigW_eq_prod U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      URep.dsig_coe U (hW X List.mem_cons_self), ← ih]
    rfl

theorem matHom : MatHom := by
  intro k r F F' U A hA
  refine ⟨fun W hW => ⟨∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖, [W], ?_, fun x => ?_⟩, fun g hg => ?_⟩
  · intro W' hW'
    rw [List.mem_singleton.1 hW']
    exact hW
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change ∑ c : F'.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((mAct A x c : U.R.smSub) : U.R.H)‖ ≤
      (∑ c : F'.ι, ∑ d : F.ι, ‖A c d‖) *
        ∑ e : F.ι, ‖PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W ((x e : U.R.smSub) : U.R.H)‖
    simp only [dsigW_eq_prod U W hW]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mAct_coord, map_sum, Submodule.coe_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [map_smul, Submodule.coe_smul, norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Finset.single_le_sum
      (f := fun e => ‖(((W.map U.dsig).prod (x e) : U.R.smSub) : U.R.H)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ d)
  · refine LinearMap.ext fun x => ?_
    change mAct A (mAct (F.ρ g) (dOp F.ι (U.sig g) x)) = mAct (F'.ρ g) (dOp F'.ι (U.sig g) (mAct A x))
    rw [dOp_mAct, mAct_mAct, mAct_mAct, hA g hg]

end GlobalTheory.CompanionTheory.ZuckMatHom

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuotientBoundOfFactorReduceChart
section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuQBound

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem factor_prod {n : ℕ} {H V ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
    (h : RepOn G σ) (B : H → V) (g : ι → Mat n) (c : ι → (V →L[ℂ] V)) (hg : ∀ j, g j ∈ G)
    (hc : ∀ j v, IsSm G σ v → B (σ (g j) v) = c j (B v)) (v : H) (hv : IsSm G σ v) :
    ∀ l : List ι, (l.map g).prod ∈ G ∧ B (σ (l.map g).prod v) = (l.map c).prod (B v) := by
  intro l
  induction l with
  | nil =>
    refine ⟨h.one_mem, ?_⟩
    simp [h.map_one]
  | cons a l ih =>
    obtain ⟨hP, hBP⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    refine ⟨h.mul_mem _ (hg a) _ hP, ?_⟩
    rw [h.apply_mul (hg a) hP, hc a _ (IsSm.apply h hv hP), hBP, ContinuousLinearMap.mul_apply]

theorem norm_le_avg {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : ∀ t, 0 ≤ φ t)
    (h1 : ∫ t, φ t = 1) (f : (Fin d → ℝ) → V) (hf : Continuous f) (b : V)
    (hb : ∀ t, φ t ≠ 0 → ‖f t - b‖ ≤ ‖b‖ / 2) : ‖b‖ ≤ 2 * ‖∫ t, (φ t : ℂ) • f t‖ := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hcC : HasCompactSupport (fun t => (φ t : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hφf : Integrable (fun t => (φ t : ℂ) • f t) :=
    ((Complex.continuous_ofReal.comp hφ).smul hf).integrable_of_hasCompactSupport hcC.smul_right
  have h2 : Integrable (fun t => (φ t : ℂ) • b) := hφi.ofReal.smul_const b
  have hbi : ∫ t, (φ t : ℂ) • b = b := by
    rw [integral_smul_const, integral_complex_ofReal, h1, Complex.ofReal_one, one_smul]
  have key : ∫ t, (φ t : ℂ) • f t = b + ∫ t, (φ t : ℂ) • (f t - b) := by
    simp_rw [smul_sub]
    rw [integral_sub hφf h2, hbi]
    abel
  have hbound : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ‖b‖ / 2 := by
    have hle : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ∫ t, φ t * (‖b‖ / 2) :=
      norm_integral_le_of_norm_le (hφi.mul_const (‖b‖ / 2)) (ae_of_all _ fun t => ?_)
    · rwa [integral_mul_const, h1, one_mul] at hle
    · by_cases ht : φ t = 0
      · simp [ht]
      · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h0 t)]
        exact mul_le_mul_of_nonneg_left (hb t ht) (h0 t)
  rw [key]
  have h3 : ‖b‖ ≤ ‖b + ∫ t, (φ t : ℂ) • (f t - b)‖ + ‖∫ t, (φ t : ℂ) • (f t - b)‖ := by
    simpa using norm_sub_le (b + ∫ t, (φ t : ℂ) • (f t - b)) (∫ t, (φ t : ℂ) • (f t - b))
  linarith

theorem qBound (hF : Factor) (hR : Reduce) (hC : ChartExists) : QBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB d e X Q hX hQ hS χ hχc hχ0 hχB
  obtain ⟨N, W, β, hW, hBW⟩ := hF n Hm H σ hU V B hB
  obtain ⟨U, hCh⟩ := hC n Hm hU.sq d e X Q hX hQ hS
  have hrep := hU.rep
  have hmem : ∀ t, prodEx X t ∈ UH Hm := hCh.mem
  have hsc : Continuous (prodEx X) := hCh.smooth.continuous
  set Φ : (Fin d → ℝ) → (V →L[ℂ] V) := fun t => ((List.finRange d).map fun j => χ j (t j)).prod with hΦdef
  have hΦc : Continuous Φ := continuous_list_prod _ fun j _ => (hχc j).comp (continuous_apply j)
  have hΦ0 : Φ 0 = 1 := by simp [hΦdef, hχ0]
  have hfac : ∀ v, IsSm (UH Hm) σ v → ∀ t, B (σ (prodEx X t) v) = Φ t (B v) := by
    intro v hv t
    show B (σ ((List.ofFn fun j => ex (X j) (t j)).prod) v) = _
    rw [List.ofFn_eq_map]
    exact (factor_prod hrep B (fun j => ex (X j) (t j)) (fun j => χ j (t j))
      (fun j => ex_mem_of_lie (hX j) (t j)) (fun j w hw => hχB j (t j) w hw) v hv (List.finRange d)).2
  obtain ⟨r, hr, hrΦ⟩ : ∃ r > 0, ∀ t : Fin d → ℝ, dist t 0 < r → dist (Φ t) (Φ 0) < 1 / 2 :=
    Metric.continuous_iff.1 hΦc 0 (1 / 2) (by norm_num)
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hCh.isOpen 0 hCh.zero
  have hmin : 0 < min r r' := lt_min hr hr'
  set ρ := min r r' / 2 with hρ
  have hρpos : 0 < ρ := half_pos hmin
  have hρr : ρ < r := by rw [hρ]; linarith [min_le_left r r']
  have hρr' : ρ < r' := by rw [hρ]; linarith [min_le_right r r']
  let bump : ContDiffBump (0 : Fin d → ℝ) := ⟨ρ / 2, ρ, half_pos hρpos, half_lt_self hρpos⟩
  set φ := bump.normed volume with hφdef
  have hφs : ContDiff ℝ ∞ φ := bump.contDiff_normed
  have hφcs : HasCompactSupport φ := bump.hasCompactSupport_normed
  have hts : tsupport φ = Metric.closedBall 0 ρ := bump.tsupport_normed_eq
  have hφU : tsupport φ ⊆ U := by
    rw [hts]
    intro t ht
    apply hr'U
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at ht
    linarith
  have hφ0 : ∀ t, 0 ≤ φ t := bump.nonneg_normed
  have hφ1 : ∫ t, φ t = 1 := bump.integral_normed
  have hnear : ∀ t, φ t ≠ 0 → ‖Φ t - 1‖ ≤ 1 / 2 := by
    intro t ht
    have htm : t ∈ tsupport φ := subset_tsupport _ ht
    rw [hts, Metric.mem_closedBall] at htm
    have hd := hrΦ t (by linarith)
    rw [dist_eq_norm, hΦ0] at hd
    exact hd.le
  have hRi := fun i => hR n Hm H σ hU d e Q (prodEx X) U hCh (W i) (hW i) φ hφs hφcs hφU
  choose Cr hCr0 hCr using hRi
  refine ⟨2 * ∑ i, ‖β i‖ * Cr i, Finset.univ.sup fun i => (W i).length, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hCr0 i))
  intro v hv R hRb
  have hlie : ∀ i, LieW (UH Hm) (W i) := fun i X' hX' t => ex_mem_of_lie (hW i X' hX') t
  have hgc : ∀ i, Continuous fun t => dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    (continuousOn_dsW_orbit hrep hv (hlie i)).comp_continuous hsc hmem
  have hint : ∀ i, Integrable fun t => (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    ((Complex.continuous_ofReal.comp hφs.continuous).smul (hgc i)).integrable_of_hasCompactSupport
      (hφcs.comp_left Complex.ofReal_zero).smul_right
  have hsum : ∫ t, (φ t : ℂ) • Φ t (B v) =
      ∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
    have e1 : ∀ t, (φ t : ℂ) • Φ t (B v) =
        ∑ i, β i ((φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
      intro t
      rw [← hfac v hv t, hBW _ (IsSm.apply hrep hv (hmem t)), Finset.smul_sum]
      simp only [ContinuousLinearMap.map_smul]
    simp_rw [e1]
    rw [integral_finsetSum _ fun i _ => (β i).integrable_comp (hint i)]
    exact Finset.sum_congr rfl fun i _ => (β i).integral_comp_comm (hint i)
  have havg := norm_le_avg φ hφs.continuous hφcs hφ0 hφ1 (fun t => Φ t (B v))
    (hΦc.clm_apply continuous_const) (B v) (fun t ht => ?_)
  · rw [hsum] at havg
    have hb2 : ‖∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))‖ ≤
        ∑ i, ‖β i‖ * Cr i * R := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine ((β i).le_opNorm _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hCr i v hv R fun P hP => hRb P
        (hP.trans (Finset.le_sup (f := fun i => (W i).length) (Finset.mem_univ i)))) (norm_nonneg _)
    rw [← Finset.sum_mul] at hb2
    nlinarith
  · have hsub : Φ t (B v) - B v = (Φ t - 1) (B v) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [hsub]
    calc ‖(Φ t - 1) (B v)‖ ≤ ‖Φ t - 1‖ * ‖B v‖ := (Φ t - 1).le_opNorm _
      _ ≤ 1 / 2 * ‖B v‖ := mul_le_mul_of_nonneg_right (hnear t ht) (norm_nonneg _)
      _ = ‖B v‖ / 2 := by ring

end GlobalTheory.CompanionTheory.BmuQBound

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuReduce

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_of_smOn_univ {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : E → V} (hf : SmOn Set.univ f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro a
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a (Set.mem_univ a)
  refine (hF.contDiffAt (hU.mem_nhds haU)).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds haU] with g hg
  exact hfF g hg (Set.mem_univ g)

theorem cut_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U) {φ a : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiff ℝ ∞ (fun t => φ t * a t) ∧ HasCompactSupport (fun t => φ t * a t) ∧
      tsupport (fun t => φ t * a t) ⊆ U := by
  have h1 : tsupport (fun t => φ t * a t) ⊆ U := (tsupport_mul_subset_left (f := φ) (g := a)).trans hs
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hc.mul_right, h1⟩
  by_cases hx : x ∈ tsupport (fun t => φ t * a t)
  · exact hφ.contDiffAt.mul (ha.contDiffAt (hU.mem_nhds (h1 hx)))
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

theorem cut_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (v : E) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ φ t v) ∧ HasCompactSupport (fun t => fderiv ℝ φ t v) ∧
      tsupport (fun t => fderiv ℝ φ t v) ⊆ U :=
  ⟨(hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, hc.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans hs⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem contDiff_orbit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : RepOn G σ) {w : H}
    (hw : IsSm G σ w) {W : List (Mat n)} (hW : LieW G W) {s : E → Mat n} (hs : ContDiff ℝ ∞ s)
    (hm : ∀ t, s t ∈ G) : ContDiff ℝ ∞ (fun t => dsW σ W (σ (s t) w)) := by
  have h1 := SmOn.comp (smOn_dsW h (u := fun x => σ x w) (hw.smOn_mul h) hW)
    (φ := fun t : E => ((1 : Mat n), s t)) (B := Set.univ) (contDiff_const.prodMk hs)
    fun t _ => ⟨h.one_mem, hm t⟩
  refine contDiff_of_smOn_univ (h1.congr fun x _ => ?_)
  simp [h.map_one]

theorem dsW_sum (h : RepOn G σ) {W : List (Mat n)} (hW : LieW G W) {ι : Type*} (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSm G σ (v i)) (S : Finset ι) :
    IsSm G σ (∑ i ∈ S, c i • v i) ∧ dsW σ W (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • dsW σ W (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using IsSm.zero, ?_⟩
    have := dsW_smul h (IsSm.zero (G := G) (σ := σ)) (0 : ℂ) hW
    simpa using this
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨((hv i).smul _).add ih.1, by rw [dsW_add h ((hv i).smul _) ih.1 hW, dsW_smul h (hv i) _ hW, ih.2]⟩

theorem lieW_of {Hm : Mat n} {W : List (Mat n)} (hW : LieWd Hm W) : LieW (UH Hm) W :=
  fun X hX t => ex_mem_of_lie (hW X hX) t

theorem isSm_ds {Hm : Mat n} (h : RepOn (UH Hm) σ) {X : Mat n} (hX : Lie Hm X) {u : H} (hu : IsSm (UH Hm) σ u) :
    IsSm (UH Hm) σ (ds σ X u) :=
  hu.dsW h (W := [X]) (lieW_of fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX)

theorem dsW_append (W W' : List (Mat n)) (v : H) : dsW σ (W ++ W') v = dsW σ W (dsW σ W' v) :=
  List.foldr_append

theorem last_letter [CompleteSpace H] (hlin : DsLin) (had : DsAd) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {Y y : Mat n} (hY : Lie Hm Y) (hy : y ∈ UH Hm) {d e : ℕ}
    {Z : Fin d → Mat n} {Q : Fin e → Mat n} (hZ : ∀ j, Lie Hm (Z j)) (hQ : ∀ i, Lie Hm (Q i))
    {a : Fin d → ℝ} {b : Fin e → ℝ} (hab : y⁻¹ * Y * y = ∑ j, (a j : ℂ) • Z j + ∑ i, (b i : ℂ) • Q i)
    {u : H} (hu : IsSm (UH Hm) σ u) :
    dsW σ (W ++ [Y]) (σ y u) =
      ∑ j, a j • dsW σ W (σ y (ds σ (Z j) u)) + ∑ i, b i • dsW σ W (σ y (ds σ (Q i) u)) := by
  obtain ⟨h1, h2⟩ := had n Hm H σ hσ y hy [Y] (fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
  obtain ⟨Λ, hΛ⟩ := hlin n Hm H σ hσ u hu
  have h3 : Lie Hm (y⁻¹ * Y * y) := h1 _ (by simp)
  have h4 : ds σ (y⁻¹ * Y * y) u = ∑ j, (a j : ℂ) • ds σ (Z j) u + ∑ i, (b i : ℂ) • ds σ (Q i) u := by
    rw [hΛ _ h3, hab]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Complex.coe_smul, map_add (f := _), map_sum, map_smul, hΛ _ (hZ _), hΛ _ (hQ _)]
  have h5 : dsW σ [Y] (σ y u) =
      ∑ j, (a j : ℂ) • σ y (ds σ (Z j) u) + ∑ i, (b i : ℂ) • σ y (ds σ (Q i) u) := by
    rw [h2 u hu]
    change σ y (ds σ (y⁻¹ * Y * y) u) = _
    rw [h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul]
  have hA := dsW_sum hσ.rep (lieW_of hW) (fun j => (a j : ℂ)) (fun j => σ y (ds σ (Z j) u))
    (fun j => (isSm_ds hσ.rep (hZ j) hu).apply hσ.rep hy) Finset.univ
  have hB := dsW_sum hσ.rep (lieW_of hW) (fun j => (b j : ℂ)) (fun j => σ y (ds σ (Q j) u))
    (fun j => (isSm_ds hσ.rep (hQ j) hu).apply hσ.rep hy) Finset.univ
  rw [dsW_append, h5, dsW_add hσ.rep hA.1 hB.1 (lieW_of hW), hA.2, hB.2]
  simp only [Complex.coe_smul]

theorem fderiv_orbit [CompleteSpace H] (hder : DsDer) {Hm : Mat n} (hσ : URep Hm σ)
    {W : List (Mat n)} (hW : LieWd Hm W) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : E → Mat n}
    (hs : ContDiff ℝ ∞ s) (hm : ∀ t, s t ∈ UH Hm) {t v : E} {Z : Mat n} (hZ : Lie Hm Z)
    (hfl : ∀ τ : ℝ, s (t + τ • v) = s t * ex Z τ) {u : H} (hu : IsSm (UH Hm) σ u) :
    fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v = dsW σ W (σ (s t) (ds σ Z u)) := by
  have h1 := contDiff_orbit hσ.rep hu (lieW_of hW) hs hm
  have h2 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t v) t v :=
    (h1.differentiable (by simp) t).hasFDerivAt.hasLineDerivAt v
  have h3 : HasLineDerivAt ℝ (fun t => dsW σ W (σ (s t) u)) (dsW σ W (σ (s t) (ds σ Z u))) t v := by
    unfold HasLineDerivAt
    simp only [hfl]
    exact hder n Hm H σ hσ W hW (s t) (hm t) Z hZ u hu
  exact h2.unique h3

theorem integrable_cut {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : Continuous f) : Integrable (fun t => ψ t • f t) :=
  (hψ.smul hf).integrable_of_hasCompactSupport hc.smul_right

theorem parts {d : ℕ} {ψ : (Fin d → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    {f : (Fin d → ℝ) → H} (hf : ContDiff ℝ ∞ f) (v : Fin d → ℝ) :
    ∫ t, ψ t • fderiv ℝ f t v = - ∫ t, fderiv ℝ ψ t v • f t := by
  obtain ⟨h1, h2, -⟩ := cut_fderiv hψ hc (Set.subset_univ _) v
  refine integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (integrable_cut h1.continuous h2 hf.continuous)
    (integrable_cut hψ.continuous hc ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
    (integrable_cut hψ.continuous hc hf.continuous) (fun x _ => hψ.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)

theorem reduce : DsLin → DsAd → DsDer → Reduce := by
  intro hlin had hder n Hm H _ _ _ σ hσ d e Q s U hch W
  simp only [Complex.coe_smul]
  induction W using List.reverseRecOn with
  | nil =>
    intro _ φ hφ hc _
    refine ⟨∫ t, ‖φ t‖, integral_nonneg fun t => norm_nonneg _, fun u _ R hR => ?_⟩
    have hu : ‖u‖ ≤ R := hR [] le_rfl
    refine (norm_integral_le_integral_norm _).trans ?_
    have : ∀ t, ‖φ t • dsW σ [] (σ (s t) u)‖ = ‖φ t‖ * ‖u‖ := fun t => by
      rw [norm_smul]
      exact congrArg _ (hσ.iso _ (hch.mem t) u)
    simp only [this]
    rw [integral_mul_const]
    exact mul_le_mul_of_nonneg_left hu (integral_nonneg fun t => norm_nonneg _)
  | append_singleton W Y ih =>
    intro hWY φ hφ hc hs
    have hW : LieWd Hm W := fun X hX => hWY X (List.mem_append_left _ hX)
    have hY : Lie Hm Y := hWY Y (by simp)
    obtain ⟨Z, hZ, hfl, hsp⟩ := hch.flow
    obtain ⟨a, b, ha, hb, hab⟩ := hsp Y hY
    have hA := fun j => cut_mul hch.isOpen hφ hc hs (ha j)
    have hB := fun i => cut_mul hch.isOpen hφ hc hs (hb i)
    have hA' := fun j => cut_fderiv (hA j).1 (hA j).2.1 (hA j).2.2 (Pi.single j 1)
    choose C hC0 hC using fun j => ih hW _ (hA' j).1 (hA' j).2.1 (hA' j).2.2
    choose D hD0 hD using fun i => ih hW _ (hB i).1 (hB i).2.1 (hB i).2.2
    refine ⟨∑ j, C j + ∑ i, D i, add_nonneg (Finset.sum_nonneg fun j _ => hC0 j)
      (Finset.sum_nonneg fun j _ => hD0 j), fun u hu R hR => ?_⟩
    have hf := contDiff_orbit hσ.rep hu (lieW_of hW) hch.smooth hch.mem
    have hg := fun i => contDiff_orbit hσ.rep (isSm_ds hσ.rep (hch.lieQ i) hu) (lieW_of hW) hch.smooth hch.mem
    have hpt : ∀ t, φ t • dsW σ (W ++ [Y]) (σ (s t) u) =
        ∑ j, (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) +
          ∑ i, (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun t => by
      by_cases ht : t ∈ tsupport φ
      · rw [last_letter hlin had hσ hW hY (hch.mem t) (fun j => hZ j t) hch.lieQ (hab t (hs ht)) hu]
        simp only [fun j => fderiv_orbit hder hσ hW hch.smooth hch.mem (hZ j t) (hfl j t) hu,
          smul_add, Finset.smul_sum, smul_smul]
      · simp [image_eq_zero_of_notMem_tsupport ht]
    have iA : ∀ j, Integrable fun t =>
        (φ t * a j t) • fderiv ℝ (fun t => dsW σ W (σ (s t) u)) t (Pi.single j 1) := fun j =>
      integrable_cut (hA j).1.continuous (hA j).2.1
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
    have iB : ∀ i, Integrable fun t => (φ t * b i t) • dsW σ W (σ (s t) (ds σ (Q i) u)) := fun i =>
      integrable_cut (hB i).1.continuous (hB i).2.1 (hg i).continuous
    simp only [hpt]
    rw [integral_add (MeasureTheory.integrable_finsetSum _ fun j _ => iA j) (MeasureTheory.integrable_finsetSum _ fun j _ => iB j),
      MeasureTheory.integral_finsetSum _ fun j _ => iA j, MeasureTheory.integral_finsetSum _ fun j _ => iB j, add_mul, Finset.sum_mul,
      Finset.sum_mul]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)))
    · rw [parts (hA j).1 (hA j).2.1 hf, norm_neg]
      exact hC j u hu R fun P hP => hR P (by simp; omega)
    · refine hD i _ (isSm_ds hσ.rep (hch.lieQ i) hu) R fun P hP => ?_
      have := hR (P ++ [i]) (by simp; omega)
      rwa [List.map_append, dsW_append] at this

end GlobalTheory.CompanionTheory.BmuReduce

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckStdD

theorem dR_std (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r false).dR X = X := by
  ext c d
  exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv

theorem dR_dual (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r true).dR X = -Xᵀ := by
  ext c d
  have h := (PI.ComplexConjugateDerivative.exp_entry (-X) d c).deriv
  have e : (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) =
      fun t : ℝ => (NormedSpace.exp ((t : ℂ) • (-X))) d c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
    simp [dualM]
  show deriv (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0 = _
  rw [e, h]
  rfl

theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    reH k r Y + Complex.I • imH k r Y = Y := by
  unfold reH imH
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
  rw [smul_smul, hI, ← smul_add]
  have : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y := by
    intro Z; rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

theorem stdD : StdD := by
  intro k r Y
  constructor
  · unfold FRep.dC
    rw [dR_std, dR_std]
    exact reH_add_imH k r Y
  · unfold FRep.dC
    rw [dR_dual, dR_dual]
    conv_rhs => rw [← reH_add_imH k r Y]
    rw [Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]

end GlobalTheory.CompanionTheory.ZuckStdD
end

