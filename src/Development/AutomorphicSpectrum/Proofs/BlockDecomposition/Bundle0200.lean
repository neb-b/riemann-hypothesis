module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinear
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_eq_sum_of_kernels : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  intro hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val) := Units.continuous_val.comp continuous_inv
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := hval _
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  have hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ := by
    intro i j
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      have h1 : Continuous (fun y : G n => ks i y.val) := hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x)) :=
        (hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem
      exact h1.mul h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x))
      = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
    funext y
    rw [hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable
      (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ => (hint i j).smul (c i * c' j)
  unfold conv
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable
      (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun j _ => (hint i j).smul (c i * c' j)
  rw [MeasureTheory.integral_finsetSum _ hj]
  exact Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _

end GlobalTheory.CompanionTheory.WaveMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevel
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL

def lgArg {n : ℕ} (p : Mat n × Mat n) : ℝ :=
  1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)

theorem lgArg_continuous {n : ℕ} : Continuous (lgArg (n := n)) := by
  unfold lgArg
  refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
  have h1 : Continuous fun p : Mat n × Mat n => p.1 a b :=
    (continuous_id.matrix_elem a b).comp continuous_fst
  have h2 : Continuous fun p : Mat n × Mat n => p.2 a b :=
    (continuous_id.matrix_elem a b).comp continuous_snd
  exact (h1.norm.pow 2).add (h2.norm.pow 2)

theorem one_le_lgArg {n : ℕ} (p : Mat n × Mat n) : 1 ≤ lgArg p := by
  unfold lgArg
  have : 0 ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  linarith

theorem entry_sq_le_lgArg {n : ℕ} (p : Mat n × Mat n) (a b : Fin n) :
    ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ lgArg p := by
  unfold lgArg
  have h1 : ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun b => ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ b)
  have h2 : ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) :=
    Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
      (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
  linarith

theorem lg_eq_log_lgArg {n : ℕ} (y : Mat n) : lg y = Real.log (lgArg (y, y⁻¹)) := rfl

theorem continuousOn_matInv {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have hdet : ContinuousOn (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy
  have hadj : Continuous fun y : Mat n => y.adjugate := continuous_id.matrix_adjugate
  have : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact hdet.smul hadj.continuousOn

theorem continuousOn_lg {n : ℕ} : ContinuousOn (lg (n := n)) (GLs n) := by
  have hp : ContinuousOn (fun y : Mat n => (y, y⁻¹)) (GLs n) :=
    continuousOn_id.prodMk continuousOn_matInv
  have h := lgArg_continuous.comp_continuousOn hp
  exact ContinuousOn.log h fun y _ => (lt_of_lt_of_le one_pos (one_le_lgArg (y, y⁻¹))).ne'

def pairOf {n : ℕ} (y : G n) : Mat n × Mat n := (y.val, (y⁻¹ : G n).val)

theorem pairOf_isInducing {n : ℕ} : Topology.IsInducing (pairOf (n := n)) := by
  have h := (Units.isEmbedding_embedProduct (M := Mat n)).isInducing
  have h2 : Topology.IsInducing (fun p : Mat n × (Mat n)ᵐᵒᵖ => (p.1, p.2.unop)) :=
    ((Homeomorph.refl (Mat n)).prodCongr MulOpposite.opHomeomorph.symm).isInducing
  exact h2.comp h

theorem isCompact_entryBox {n : ℕ} (r : ℝ) : IsCompact {m : Mat n | ∀ a b, ‖m a b‖ ≤ r} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} = Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) r := by
    ext m
    simp [Set.mem_pi]
  have h' : IsCompact {m : Fin n → Fin n → ℂ | ∀ a b, ‖m a b‖ ≤ r} := e ▸ h
  exact h'

theorem isCompact_lg_le {n : ℕ} (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  rw [pairOf_isInducing.isCompact_iff]
  have hset : pairOf '' {y : G n | lg y.val ≤ R} =
      {p : Mat n × Mat n | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 ∧ lgArg p ≤ Real.exp R} := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨by simp [pairOf], by simp [pairOf], ?_⟩
      have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
      have hy' : Real.log (lgArg (pairOf y)) ≤ R := by
        have : lg y.val = Real.log (lgArg (pairOf y)) := by
          rw [lg_eq_log_lgArg, pairOf, hinv]
        rw [← this]; exact hy
      have hpos : 0 < lgArg (pairOf y) := lt_of_lt_of_le one_pos (one_le_lgArg _)
      exact (Real.log_le_iff_le_exp hpos).1 hy'
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨p.1, p.2, h1, h2⟩, ?_, ?_⟩
      · set y : G n := ⟨p.1, p.2, h1, h2⟩ with hy
        have hinv : (y⁻¹ : G n).val = y.val⁻¹ := Matrix.coe_units_inv y
        have hpy : pairOf y = p := rfl
        have : lg y.val = Real.log (lgArg p) := by
          rw [lg_eq_log_lgArg, ← hinv, ← hpy]; rfl
        have hpos : 0 < lgArg p := lt_of_lt_of_le one_pos (one_le_lgArg _)
        show lg y.val ≤ R
        rw [this]
        exact (Real.log_le_iff_le_exp hpos).2 h3
      · rfl
  rw [hset]
  have hbox : IsCompact ({m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)} ×ˢ
      {m : Mat n | ∀ a b, ‖m a b‖ ≤ Real.sqrt (Real.exp R)}) :=
    (isCompact_entryBox _).prod (isCompact_entryBox _)
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : IsClosed {p : Mat n × Mat n | p.1 * p.2 = 1} :=
      isClosed_eq (continuous_fst.matrix_mul continuous_snd) continuous_const
    have c2 : IsClosed {p : Mat n × Mat n | p.2 * p.1 = 1} :=
      isClosed_eq (continuous_snd.matrix_mul continuous_fst) continuous_const
    have c3 : IsClosed {p : Mat n × Mat n | lgArg p ≤ Real.exp R} :=
      isClosed_le lgArg_continuous continuous_const
    exact c1.inter (c2.inter c3)
  · rintro p ⟨-, -, h3⟩
    have hb : ∀ a b, ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ Real.exp R := fun a b =>
      (entry_sq_le_lgArg p a b).trans h3
    refine ⟨fun a b => Real.le_sqrt_of_sq_le ?_, fun a b => Real.le_sqrt_of_sq_le ?_⟩
    · have := hb a b; nlinarith [sq_nonneg ‖p.2 a b‖]
    · have := hb a b; nlinarith [sq_nonneg ‖p.1 a b‖]

theorem lg_continuousOn_and_isCompact :
    ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} :=
  fun _ => ⟨continuousOn_lg, isCompact_lg_le⟩

end GlobalTheory.CompanionTheory.SobGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
section
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.LgBound

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lgCpt : PositivityTheory.RgBcC.VC.LgCpt := by
  intro n R
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℂ _
  let f : G n → ℝ := fun y => 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
  have hinv : ∀ y : G n, (y.val)⁻¹ = (y⁻¹).val := fun y => (Matrix.coe_units_inv y).symm
  have hc1 : Continuous fun y : G n => y.val := Units.continuous_val
  have hc2 : Continuous fun y : G n => (y⁻¹).val := Units.continuous_val.comp continuous_inv
  have hfc : Continuous f := by
    refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
    exact ((hc1.matrix_elem a b).norm.pow 2).add ((hc2.matrix_elem a b).norm.pow 2)
  have hsum : ∀ y : G n, 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hfpos : ∀ y, 0 < f y := fun y => by
    have := hsum y
    show 0 < 1 + _
    linarith
  have hS : {y : G n | lg y.val ≤ R} = f ⁻¹' Set.Iic (Real.exp R) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, lg, hinv]
    exact Real.log_le_iff_le_exp (hfpos y)
  rw [hS]
  have hclosed : IsClosed (f ⁻¹' Set.Iic (Real.exp R)) := isClosed_Iic.preimage hfc

  set r : ℝ := Real.exp R with hr
  have hr0 : 0 ≤ r + 1 := by positivity
  have hterm : ∀ y : G n, f y ≤ r → ∀ a b, ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ r := by
    intro y hy a b
    have h1 : ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ b)
    have h2 : ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2))
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
    have h3 : 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ r := hy
    linarith
  have hle : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ r → t ≤ r + 1 := by
    intro t ht h
    nlinarith [sq_nonneg (t - 1)]
  have hb1 : ∀ y : G n, f y ≤ r → ‖y.val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖(y⁻¹).val a b‖ ^ 2 := by positivity
    linarith
  have hb2 : ∀ y : G n, f y ≤ r → ‖(y⁻¹).val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖y.val a b‖ ^ 2 := by positivity
    linarith
  have hball : IsCompact (Metric.closedBall (0 : Mat n) (r + 1)) := isCompact_closedBall _ _
  have hK : IsCompact ((fun p : Mat n × Mat n => (p.1, MulOpposite.op p.2)) ''
      (Metric.closedBall (0 : Mat n) (r + 1) ×ˢ Metric.closedBall (0 : Mat n) (r + 1))) :=
    (hball.prod hball).image (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  have hpre := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hK
  refine hpre.of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨(y.val, (y⁻¹).val), ⟨?_, ?_⟩, rfl⟩
  · simpa using hb1 y hy
  · simpa using hb2 y hy

end GlobalTheory.CompanionTheory.LgBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeIsOpen
section
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar.OpenCone

variable {n : ℕ}

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian := by
  show (hOf v)ᴴ = hOf v
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem im_form {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    conv_rhs => rw [Matrix.star_dotProduct]
    rw [Matrix.star_mulVec, hM.eq, ← Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem continuous_form :
    Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => (star z.2 ⬝ᵥ hOf z.1 *ᵥ z.2).re := by
  have hent : ∀ i j : Fin n, Continuous fun v : Fin n × Fin n → ℝ => hOf v i j := by
    intro i j
    have : (fun v : Fin n × Fin n → ℝ => hOf v i j) = fun v => ∑ p, (v p : ℂ) * hb p i j := by
      funext v
      simp [hOf, Matrix.sum_apply]
    rw [this]
    fun_prop
  have hent' : ∀ i j : Fin n,
      Continuous fun z : (Fin n × Fin n → ℝ) × (Fin n → ℂ) => hOf z.1 i j :=
    fun i j => (hent i j).comp continuous_fst
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact (hent' i j).mul ((continuous_apply j).comp continuous_snd)

theorem posDef_of_sphere {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian)
    (h : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ M *ᵥ x).re) : M.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hM, fun x hx => ?_⟩
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn]
  have h1 := h _ hy
  have h2 : star (((‖x‖⁻¹ : ℝ) : ℂ) • x) ⬝ᵥ M *ᵥ (((‖x‖⁻¹ : ℝ) : ℂ) • x) =
      (((‖x‖⁻¹ ^ 2 : ℝ)) : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [smul_eq_mul, pow_two]
    ring
  rw [h2, Complex.re_ofReal_mul] at h1
  have h3 : 0 < (star x ⬝ᵥ M *ᵥ x).re := by
    have : 0 < ‖x‖⁻¹ ^ 2 := by positivity
    exact (pos_iff_pos_of_mul_pos h1).1 this
  exact Complex.pos_iff.2 ⟨h3, (im_form hM x).symm⟩

end GlobalTheory.CompanionTheory.ConeHaar.OpenCone

namespace GlobalTheory.CompanionTheory.ConeHaar

open OpenCone

theorem isOpen_cone : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  intro n
  rw [isOpen_iff_eventually]
  intro v hv
  have hpos : ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star x ⬝ᵥ hOf v *ᵥ x).re := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 hv).2 hx0
    exact (Complex.pos_iff.1 this).1
  have hev : ∀ᶠ w in 𝓝 v, ∀ x ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star x ⬝ᵥ hOf w *ᵥ x).re :=
    (isCompact_sphere (0 : Fin n → ℂ) 1).eventually_forall_of_forall_eventually fun x hx =>
      (continuous_form.continuousAt (x := (v, x))).eventually (lt_mem_nhds (hpos x hx))
  exact hev.mono fun w hw => posDef_of_sphere (hOf_herm w) hw

end GlobalTheory.CompanionTheory.ConeHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeReversal
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem isWave_time_refl : ∀ {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → IsWave E fun s => u (-s) := by
  intro n E u hu
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, fun t => h2 (-t), ?_, ?_⟩
  · have hm : Set.MapsTo (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) (Set.univ ×ˢ GLs n) :=
      fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hc : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => (-p.1, p.2)) (Set.univ ×ˢ GLs n) :=
      (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
    exact h1.comp hc hm
  · intro t g hg
    have := iteratedDeriv_comp_neg (𝕜 := ℝ) 2 (fun s => u s g) t
    rw [this, h3 (-t) g hg]
    simp
  · intro g hg
    have := deriv_comp_neg (𝕜 := ℝ) (fun s => u s g) 0
    rw [this]
    simpa using h4 g hg

end GlobalTheory.CompanionTheory.WaveSpd
end
end

