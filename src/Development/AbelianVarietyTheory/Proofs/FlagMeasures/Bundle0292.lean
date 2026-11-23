module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTruncatedGaussiansWithDensities
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormPosOnOrthLiftedFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze
section
open Filter Topology Set

namespace GlobalTheory.IwConst

theorem tendsto_scale_div_pow (b : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (s : ℝ) (hs : 0 < s)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (hv : v ≠ ⊤) :
    Tendsto (fun r : ℝ => ENNReal.ofReal c * b (s * r) / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (c * s ^ d) * v)) := by
  have hs' : Tendsto (fun r : ℝ => s * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h0 : Tendsto (fun r : ℝ => s * r) (𝓝 (0 : ℝ)) (𝓝 (s * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hs hr
  have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (s ^ d)) (hb.comp hs')
    (Or.inr ENNReal.ofReal_ne_top)
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) h1 (Or.inr ENNReal.ofReal_ne_top)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hc] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsd : ENNReal.ofReal (s ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hs d
  simp only [Function.comp]
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hs.le d), ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ hsd ENNReal.ofReal_ne_top, mul_div_assoc]

theorem tendsto_ofReal_mul_of_one (g : ℝ → ℝ) (v : ENNReal) (hv : v ≠ ⊤)
    (hg : ContinuousAt g 0) (h0 : g 0 = 1) :
    Tendsto (fun η : ℝ => ENNReal.ofReal (g η) * v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (g η)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (ENNReal.continuous_ofReal.tendsto (g 0)).comp hg.tendsto
    rw [h0, ENNReal.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := ENNReal.Tendsto.mul_const (b := v) h1 (Or.inr hv)
  rw [one_mul] at h2
  exact h2

theorem tendsto_div_pow_of_squeeze (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal) (hv : v ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal,
      Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧
        f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) :
    Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hg : ContinuousAt (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 := by
      fun_prop (disch := norm_num)
    have hg0 : (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).1 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    have h1η : (0 : ℝ) < 1 + η := by linarith
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hL := tendsto_scale_div_pow b d v ((1 + η)⁻¹) (inv_pos.2 h1η) ((1 + η)⁻¹)
      (inv_nonneg.2 h1η.le) hb hv
    filter_upwards [(tendsto_order.1 hL).1 a hη, hev] with r hr1 hr2
    refine lt_of_lt_of_le hr1 (ENNReal.div_le_div_right ?_ _)
    calc ENNReal.ofReal ((1 + η)⁻¹) * b ((1 + η)⁻¹ * r)
        ≤ ENNReal.ofReal ((1 + η)⁻¹) * (ENNReal.ofReal (1 + η) * f r) := by
          gcongr
          rw [← div_eq_inv_mul]
          exact hr2.1
      _ = f r := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 h1η.le), inv_mul_cancel₀ h1η.ne',
            ENNReal.ofReal_one, one_mul]
  · have hg : ContinuousAt (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 := by fun_prop
    have hg0 : (fun η : ℝ => (1 + η) * (1 + η) ^ d) 0 = 1 := by simp
    have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
    obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).2 a ha |>.and self_mem_nhdsWithin).exists
    have hη0 : (0 : ℝ) < η := hηpos
    obtain ⟨b, hb, hev⟩ := h η hη0
    have hU := tendsto_scale_div_pow b d v (1 + η) (by linarith) (1 + η) (by linarith) hb hv
    filter_upwards [(tendsto_order.1 hU).2 a hη, hev] with r hr1 hr2
    exact lt_of_le_of_lt (ENNReal.div_le_div_right hr2.2 _) hr1

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoTsumOfMonotone
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Filter Topology

namespace GlobalTheory.GaussMean.Limit

theorem tendsto_tsum_of_monotone {ι : Type*} (f : ℕ → ι → ENNReal) (g : ι → ENNReal)
    (hm : ∀ y, Monotone fun k => f k y) (ht : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∑' y, f k y) atTop (𝓝 (∑' y, g y)) := by
  letI : MeasurableSpace ι := ⊤
  have h := lintegral_tendsto_of_tendsto_of_monotone (μ := (Measure.count : Measure ι)) (f := f) (F := g)
    (fun k => (measurable_from_top).aemeasurable) (ae_of_all _ hm) (ae_of_all _ ht)
  simpa only [lintegral_count] using h

theorem tendsto_lintegral_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (p : ι → α → Prop) (hp : ∀ y, MeasurableSet {x | p y x}) (f : ℕ → ι → α → ENNReal) (g : ι → α → ENNReal)
    (hf : ∀ k y, Measurable (f k y)) (hm : ∀ y x, Monotone fun k => f k y x)
    (ht : ∀ y x, Tendsto (fun k => f k y x) atTop (𝓝 (g y x))) :
    Tendsto (fun k => ∫⁻ x, (∑' y : {y // p y x}, f k y.1 x) ∂μ) atTop
      (𝓝 (∫⁻ x, (∑' y : {y // p y x}, g y.1 x) ∂μ)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun k => Measurable.aemeasurable ?_)
    (ae_of_all _ fun x a b hab => ENNReal.tsum_le_tsum fun y => hm y.1 x hab)
    (ae_of_all _ fun x => tendsto_tsum_of_monotone (fun k (y : {y // p y x}) => f k y.1 x) _
      (fun y => hm y.1 x) fun y => ht y.1 x)
  have e : (fun x => ∑' y : {y // p y x}, f k y.1 x) = fun x => ∑' y, {x | p y x}.indicator (f k y) x := by
    funext x
    exact (tsum_subtype {y | p y x} fun y => f k y x).trans (tsum_congr fun y => rfl)
  rw [e]
  exact Measurable.tsum fun y => (hf k y).indicator (hp y)

theorem measurable_coord (I : AutInst) (v : InfinitePlace I.F) (w : Fin I.n → ℂ) :
    Measurable fun x : I.GA => ((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ w := by
  have h0 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
    have e : (fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹) = fun g => uMat g⁻¹ := by
      funext g
      exact (Matrix.coe_units_inv g.1).symm
    rw [e]
    exact h0.comp continuous_inv
  have h2 : Continuous fun g : Formalism.REAL.UJ (I.ε v) => ((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ w :=
    (h1.matrix_mul continuous_const).matrix_mulVec continuous_const
  exact h2.measurable.comp ((measurable_pi_apply v).comp measurable_fst)

theorem siegelMean_of_cc : SiegelMeanCc → SiegelMean := by
  intro H I hn s μf _ _ fund hfund
  obtain ⟨hfin, hH⟩ := H I hn s μf fund hfund
  refine ⟨hfin, ?_⟩
  choose φ D h1 h2 h3 using fun v => _root_.GlobalTheory.GaussMean.Trunc.exists_truncated I.n (I.ε v)
  haveI := countable_V I
  have hs : sgn ℝ s ≠ 0 := by cases s <;> simp [sgn]
  have hL := tendsto_lintegral_tsum ((I.muA μf).restrict fund)
    (fun (y : Fin I.n → I.E) (x : I.GA) => y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s)
    (fun y => mand (measurableSet_mem_lam I y) (MeasurableSet.const _))
    (fun k y x => ENNReal.ofReal (∏ v, φ v k (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun y x => ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
    (fun k y => ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun v _ =>
      (h1 v k).1.continuous.measurable.comp (measurable_coord I v _)))
    (fun y x a b hab => ENNReal.ofReal_le_ofReal
      (Finset.prod_le_prod₀ (fun v _ => (h1 v a).2.2.1 _) fun v _ => (h2 v _).1 hab))
    (fun y x => ENNReal.tendsto_ofReal (tendsto_finsetProd _ fun v _ => (h2 v _).2))
  have hR : Tendsto (fun k => I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v k (sgn ℝ s))) atTop
      (𝓝 (I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s)))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal ((tendsto_finsetProd _ fun v _ => h3 v _ hs).const_mul _)) (Or.inr hfin.ne)
  exact tendsto_nhds_unique hL (hR.congr fun k => (hH (fun v => φ v k) (fun v => D v k) fun v => h1 v k).symm)

end GlobalTheory.GaussMean.Limit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpaces
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ComplPos

theorem mem_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_left hy)

theorem mem_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {U U' : Submodule E S.V}
    {x : S.V} (hx : x ∈ orth S (U ⊔ U')) : x ∈ orth S U' := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  exact fun y hy => hx y (Submodule.mem_sup_right hy)

theorem fvec_mem_Xplus {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F : FlagG S r T) (b : Fin (r + 1)) : F.fvec b ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun a => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)

theorem eq_zero_of_mem_X {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (hdet : (ZhatOM (Zhat F F')).det ≠ 0) {x : S.V}
    (hxX : x ∈ F.X) (hx : x ∈ orth S F'.Xplus) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxX
  have hx' : ∀ y ∈ F'.Xplus, S.hT y (∑ i, c i • F.e i) = 0 := by
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx
  have hrow : ∀ b, ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b = 0 := by
    intro b
    have h1 := hx' _ (fvec_mem_Xplus F' b)
    have h2 : S.hT (∑ i, c i • F.e i) (F'.fvec b) = 0 := by
      rw [← S.herm.eq, h1, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply]
  set v : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0 with hv
  have hvZ : Matrix.vecMul v (ZhatOM (Zhat F F')) = 0 := by
    funext b
    simp only [Matrix.vecMul, dotProduct, ZhatOM, Pi.zero_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [hv, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
    have := hrow b
    calc ∑ a : Fin r, star (c a) * ((-1) ^ (r - b.val) * Zhat F F' a.castSucc b)
        = (-1) ^ (r - b.val) * ∑ a : Fin r, star (c a) * Zhat F F' a.castSucc b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
      _ = 0 := by rw [this, mul_zero]
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvZ
  have hc : ∀ a, c a = 0 := by
    intro a
    have := congrFun hv0 a.castSucc
    simp only [hv, Fin.snoc_castSucc, Pi.zero_apply, star_eq_zero] at this
    exact this
  simp [hc]

end GlobalTheory.ComplPos

theorem GlobalTheory.ComplPos.complement_totPos : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ x ∈ orth (VS D) (Xplus F ⊔ Xplus F'), x ≠ 0 → 0 < Algebra.trace ℚ D.host.E ((VS D).hT x x) := by
  intro D X Y u u' F F' w hZ _ x hx hx0
  have hdet : (ZhatOM (Zhat F.fl F'.fl)).det ≠ 0 := by
    have e : ZhatOM (Zhat F.fl F'.fl) = ptMat w := hZ
    rw [e]
    exact Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w
  by_cases hxX : x ∈ Xsp F
  · exact absurd (GlobalTheory.ComplPos.eq_zero_of_mem_X F.fl F'.fl hdet hxX (GlobalTheory.ComplPos.mem_orth_right hx)) hx0
  · have hT : 0 < Tu D u := (D.mem u).A.T_prime.pos
    exact GlobalTheory.LoopC.PerpPos.trace_pos_perp D (Tu D u) F hT x (GlobalTheory.ComplPos.mem_orth_left hx) hxX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceCmbMulCmbStar
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Adapted

variable {n a b c e : ℕ}

theorem trace_cmb_mul_cmb {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * F k).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * cmb F y).trace = 0 := by
  simp [cmb, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_cmb_mul_cmb_star {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {F : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i k, (E i * (F k)ᴴ).trace = 0) (x : Fin a → ℝ) (y : Fin b → ℝ) : (cmb E x * (cmb F y)ᴴ).trace = 0 := by
  simp [cmb, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, h]

theorem trace_star_star (X Y : Matrix (Fin n) (Fin n) ℂ) (h : (X * Y).trace = 0) : (Xᴴ * Yᴴ).trace = 0 := by
  rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose, Matrix.trace_mul_comm, h, star_zero]

theorem hs_neg_star (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (-Xᴴ) = Formalism.REAL.hs X := by
  rw [← nrm_sq, ← nrm_sq, nrm_neg, nrm_conjTranspose]

theorem hs_three {EN : Fin a → Matrix (Fin n) (Fin n) ℂ} {EM : Fin b → Matrix (Fin n) (Fin n) ℂ}
    (hN : IsON EN) (hM : IsON EM) (h1 : ∀ i k, (EN i * (EM k)ᴴ).trace = 0) (h2 : ∀ i k, (EN i * EM k).trace = 0)
    (h3 : ∀ i k, (EN i * EN k).trace = 0) (x u : Fin a → ℝ) (y : Fin b → ℝ) :
    Formalism.REAL.hs (cmb EN x + cmb EM y + -(cmb EN u)ᴴ) = ∑ i, x i ^ 2 + ∑ i, y i ^ 2 + ∑ i, u i ^ 2 := by
  have e2 : (cmb EM y * cmb EN u).trace = 0 := by
    rw [Matrix.trace_mul_comm]; exact trace_cmb_mul_cmb h2 u y
  rw [hs_add, hs_add, hs_neg_star, hs_cmb hN, hs_cmb hM, hs_cmb hN, trace_cmb_mul_cmb_star h1]
  simp [Matrix.add_mul, trace_cmb_mul_cmb h3, e2]

def cmbL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : (Fin a → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := cmb E
  map_add' := cmb_add E
  map_smul' := cmb_smul E

def crdL (E : Fin a → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin a → ℝ) where
  toFun := crd E
  map_add' := crd_add E
  map_smul' := crd_smul E

def adp (EN : Fin a → Matrix (Fin n) (Fin n) ℂ) (EL : Fin e → Matrix (Fin n) (Fin n) ℂ) :
    ((Fin a → ℝ) × (Fin e → ℝ)) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := cmb EN ((Real.sqrt 2)⁻¹ • v.1) - (cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ + cmb EL v.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, smul_add, cmb_add, Matrix.conjTranspose_add]; abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_comm (Real.sqrt 2)⁻¹ r, cmb_smul EN r, cmb_smul EL r,
      Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply, smul_add, smul_sub]

theorem cmb_mem_of {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i ∈ S) (x : Fin a → ℝ) : cmb E x ∈ S :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h i)

theorem cmb_sub_star_mem {E : Fin a → Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ i, E i - (E i)ᴴ ∈ S) (x : Fin a → ℝ) : cmb E x - (cmb E x)ᴴ ∈ S := by
  have : cmb E x - (cmb E x)ᴴ = cmb (fun i => E i - (E i)ᴴ) x := by
    simp [cmb, Matrix.conjTranspose_sum, smul_sub, Finset.sum_sub_distrib]
  rw [this]; exact cmb_mem_of h x

theorem sum_sq_half (w : Fin a → ℝ) : ∑ i, ((Real.sqrt 2)⁻¹ • w) i ^ 2 = ∑ i, w i ^ 2 / 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem exists_adapted (n : ℕ) (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ)
    (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ)
    (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ) (hN : IsON EN) (hM : IsON EM) (hK : IsON EK) (hL : IsON EL)
    (hR : LieRel EN EM EK EL) (hd : dK = dN + dL) :
    ∃ (Q : (Fin dK → ℝ) →ₗ[ℝ] (Fin dN → ℝ) × (Fin dL → ℝ)) (ι : (Fin dL → ℝ) →ₗ[ℝ] (Fin dM → ℝ)),
      (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) ∧
      ∀ x y z, Formalism.REAL.hs (cmb EN x + cmb EM y + cmb EK z) =
        ∑ i, (x i + (Q z).1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + ι (Q z).2 i) ^ 2 + ∑ i, (Q z).1 i ^ 2 / 2 ∧
        crd EL (cmb EK z) = (Q z).2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hR
  have hι : ∀ t, cmb EM (crd EM (cmb EL t)) = cmb EL t := fun t => cmb_crd hM (cmb_mem_of h4 t)
  have hmem : ∀ v, adp EN EL v ∈ Submodule.span ℝ (Set.range EK) := fun v =>
    Submodule.add_mem _ (cmb_sub_star_mem h7 _) (cmb_mem_of h5 _)
  have hsum : ∀ x y v, Formalism.REAL.hs (cmb EN x + cmb EM y + adp EN EL v) =
      ∑ i, (x i + v.1 i / Real.sqrt 2) ^ 2 + ∑ i, (y i + crd EM (cmb EL v.2) i) ^ 2 + ∑ i, v.1 i ^ 2 / 2 := by
    intro x y v
    have e : cmb EN x + cmb EM y + adp EN EL v = cmb EN (x + (Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (y + crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [cmb_add, cmb_add, hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hhs : ∀ v, Formalism.REAL.hs (adp EN EL v) = ∑ i, v.1 i ^ 2 + ∑ i, v.2 i ^ 2 := by
    intro v
    have e : adp EN EL v = cmb EN ((Real.sqrt 2)⁻¹ • v.1) +
        cmb EM (crd EM (cmb EL v.2)) + -(cmb EN ((Real.sqrt 2)⁻¹ • v.1))ᴴ := by
      rw [hι]
      simp only [adp, LinearMap.coe_mk, AddHom.coe_mk]
      abel
    rw [e, hs_three hN hM h1 h2 h3, sum_sq_half, ← hs_cmb hM, hι, hs_cmb hL, ← Finset.sum_div]
    ring
  let T : ((Fin dN → ℝ) × (Fin dL → ℝ)) →ₗ[ℝ] (Fin dK → ℝ) := (crdL EK).comp (adp EN EL)
  have hT : ∀ v, cmb EK (T v) = adp EN EL v := fun v => cmb_crd hK (hmem v)
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h := hhs v
    rw [← hT, hv, hs_cmb hK] at h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h
    have p1 : 0 ≤ ∑ i, v.1 i ^ 2 := by positivity
    have p2 : 0 ≤ ∑ i, v.2 i ^ 2 := by positivity
    have q1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.1 i)).1
      (show ∑ i, v.1 i ^ 2 = 0 by linarith)
    have q2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v.2 i)).1
      (show ∑ i, v.2 i ^ 2 = 0 by linarith)
    ext i
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q1 i (Finset.mem_univ i))
    · exact pow_eq_zero_iff two_ne_zero |>.1 (q2 i (Finset.mem_univ i))
  have hdim : Module.finrank ℝ ((Fin dN → ℝ) × (Fin dL → ℝ)) = Module.finrank ℝ (Fin dK → ℝ) := by
    simp [hd]
  let U := LinearMap.linearEquivOfInjective T hinj hdim
  have hU : ∀ z, cmb EK z = adp EN EL (U.symm z) := by
    intro z
    rw [← hT]
    congr 1
    exact (U.apply_symm_apply z).symm
  refine ⟨U.symm.toLinearMap, (crdL EM).comp (cmbL EL), fun z => ?_, fun x y z => ⟨?_, ?_⟩⟩
  · rw [← hs_cmb hK z, hU, hhs]; rfl
  · rw [hU, hsum]; rfl
  · rw [hU]
    change crd EL (_ - _ + _) = (U.symm z).2
    rw [crd_add, crd_cmb hL, add_eq_right]
    funext i
    simp only [crd, Pi.zero_apply]
    rw [← cmb_crd hM (h4 i), Matrix.sub_mul, Matrix.trace_sub, trace_cmb_mul_cmb_star h1,
      trace_star_star _ _ (trace_cmb_mul_cmb h2 _ _)]
    simp

end GlobalTheory.IwConst.Adapted
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceLoweringMulKeepingIsotropicFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagTrace

variable {n a : ℕ} {ε : Fin n → Bool} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem mem_lowers {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lowers ε W ↔
    ((∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y ∈ perp ε (W (Fin.last a)), X *ᵥ y ∈ W (Fin.last a)) ∧
      ∀ i : Fin a, ∀ y ∈ perp ε (W i.castSucc), X *ᵥ y ∈ perp ε (W i.succ) := by
  simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem mem_keeps {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ keeps ε W ↔
    (∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i) ∧ ∀ i, ∀ y ∈ perp ε (W i), X *ᵥ y ∈ perp ε (W i) := by
  simp only [keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp ε V' ≤ perp ε V :=
  fun _ hy x hx => hy x (h hx)

theorem mul_mem_lowers {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) (hY : Y ∈ keeps ε W) :
    X * Y ∈ lowers ε W := by
  rw [mem_lowers] at hX ⊢
  rw [mem_keeps] at hY
  simp only [← Matrix.mulVec_mulVec]
  exact ⟨⟨fun i y hy => hX.1.1 i _ (hY.1 _ y hy), fun y hy => hX.1.2 _ (hY.2 _ y hy)⟩,
    fun i y hy => hX.2 i _ (hY.2 _ y hy)⟩

theorem isNilpotent_of_mem_lowers (h0 : W 0 = ⊥) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) :
    IsNilpotent X := by
  rw [mem_lowers] at hX
  have h1 : ∀ i : Fin (a + 1), ∀ y, X ^ (i : ℕ) *ᵥ y ∈ perp ε (W i) := by
    intro i
    induction i using Fin.induction with
    | zero => intro y x hx; rw [h0, Submodule.mem_bot] at hx; simp [hx]
    | succ i ih =>
      intro y
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
      exact hX.2 i _ (ih y)
  have h2 : ∀ i : Fin (a + 1), ∀ y ∈ W i, X ^ (i : ℕ) *ᵥ y = 0 := by
    intro i
    induction i using Fin.induction with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i ih =>
      intro y hy
      rw [Fin.val_succ, pow_succ, ← Matrix.mulVec_mulVec]
      exact ih _ (hX.1.1 i y hy)
  refine ⟨a + 1 + a, ?_⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, pow_add, pow_succ, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact h2 (Fin.last a) _ (hX.1.2 _ (h1 (Fin.last a) y))

theorem lowers_le_keeps {j : Fin a → ℕ} (h : IsIsoFlag ε j W) : lowers ε W ≤ keeps ε W := by
  obtain ⟨h0, hm, -, hi⟩ := h
  intro X hX
  rw [mem_lowers] at hX
  rw [mem_keeps]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i => exact fun y hy => hm (Fin.castSucc_le_succ i) (hX.1.1 i y hy)
  · induction i using Fin.lastCases with
    | last => exact fun y hy x hx => hi x hx _ (hX.1.2 y hy)
    | cast i => exact fun y hy => perp_anti (hm (Fin.castSucc_le_succ i)) (hX.2 i y hy)

theorem trace_lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧
      (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  intro n ε a j W h
  refine ⟨fun X hX Y hY => ?_, lowers_le_keeps h, ?_, fun X hX Y hY => ?_⟩
  · exact (Matrix.isNilpotent_trace_of_isNilpotent
      (isNilpotent_of_mem_lowers h.1 (mul_mem_lowers hX hY))).eq_zero
  · rw [mem_keeps]; simp
  · rw [mem_keeps] at hX hY ⊢
    simp only [← Matrix.mulVec_mulVec]
    exact ⟨fun i y hy => hX.1 i _ (hY.1 i y hy), fun i y hy => hX.2 i _ (hY.2 i y hy)⟩

end GlobalTheory.IwConst.FlagTrace
end

