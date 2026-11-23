module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace Topology
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ZOpAvg

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_invertible_matrices (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_id)

def Sm (U : ℝ → Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n)

section Gen

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_slice {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {t : ℝ} {x : E} (hx : x ∈ S) :
    HasFDerivAt (U t) ((fderiv ℝ (Function.uncurry U) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  have hd : DifferentiableAt ℝ (Function.uncurry U) (t, x) :=
    (hU.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    hasFDerivAt_prodMk_right t x
  exact hd.hasFDerivAt.comp x hi

theorem gen_sm {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {c : E → E} (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t x => fderiv ℝ (U t) x (c x)) (Set.univ ×ˢ S) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), c p.2)) :=
    contDiff_const.prodMk (hc.comp contDiff_snd)
  have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
    ContDiffOn.fderiv_of_isOpen hU (isOpen_univ.prod hS) (by simp)
  have h2 := h0.clm_apply h1.contDiffOn
  refine h2.congr ?_
  rintro ⟨t, x⟩ ⟨-, hx⟩
  simp [Function.uncurry, (fderiv_slice hS hU hx).fderiv]

theorem int_real {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {φ : ℝ → W} (hφ : Continuous φ) : Integrable (fun t => g t • φ t) := by
  refine Continuous.integrable_of_hasCompactSupport (hg.smul hφ) ?_
  exact hgc.smul_right

theorem gen_avg [ProperSpace E] [CompleteSpace W] {S : Set E} (hS : IsOpen S) {U : ℝ → E → W}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ S)) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {x : E} (hx : x ∈ S) (v : E) :
    fderiv ℝ (fun x' => ∫ t, g t • U t x') x v = ∫ t, g t • fderiv ℝ (U t) x v := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hx)
  have hSo : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hcU : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ S) := hU.continuousOn
  have hsl : ∀ y ∈ S, Continuous (fun t => U t y) := fun y hy =>
    hcU.comp_continuous (f := fun t : ℝ => (t, y)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hy⟩)
  have hDc : ContinuousOn (fun p : ℝ × E => fderiv ℝ (U p.1) p.2) (Set.univ ×ˢ S) := by
    have h0 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry U)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen hU hSo (by simp)
    have h1 : ContinuousOn (fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry U) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Set.univ ×ˢ S) :=
      h0.continuousOn.clm_comp continuousOn_const
    refine h1.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (fderiv_slice hS hU hy).fderiv
  obtain ⟨T, hT⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hK : IsCompact (Metric.closedBall (0 : ℝ) T ×ˢ Metric.closedBall x r) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hDc.mono (Set.prod_mono (Set.subset_univ _) hball))
  have hdiff : ∀ (t : ℝ) (y : E), y ∈ S → HasFDerivAt (U t) (fderiv ℝ (U t) y) y := fun t y hy =>
    (fderiv_slice hS hU hy).differentiableAt.hasFDerivAt
  have hcD : Continuous (fun t => fderiv ℝ (U t) x) :=
    hDc.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)
  have hIntD := int_real hg hgc hcD
  have key : HasFDerivAt (fun x' => ∫ t, g t • U t x') (∫ t, g t • fderiv ℝ (U t) x) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.closedBall x r)
      (F := fun x' t => g t • U t x') (F' := fun x' t => g t • fderiv ℝ (U t) x')
      (bound := fun t => |g t| * C) (Metric.closedBall_mem_nhds x hr) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hS.mem_nhds hx] with y hy
      exact (int_real hg hgc (hsl y hy)).aestronglyMeasurable
    · exact int_real hg hgc (hsl x hx)
    · exact hIntD.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      by_cases ht : t ∈ tsupport g
      · have := hC (t, y) ⟨hT ht, hy⟩
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
      · have hz : g t = 0 := image_eq_zero_of_notMem_tsupport ht
        simp [hz]
    · have : Continuous (fun t => |g t| * C) := (continuous_abs.comp hg).mul continuous_const
      refine Continuous.integrable_of_hasCompactSupport this ?_
      exact (hgc.comp_left (g := fun a : ℝ => |a|) (by simp)).mul_right
    · refine Filter.Eventually.of_forall fun t y hy => ?_
      exact (hdiff t y (hball hy)).const_smul (g t)
  rw [key.fderiv, ContinuousLinearMap.integral_apply hIntD]
  rfl

end Gen

theorem contDiff_mulRight (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  have : (fun y : Mat n => y * X) = ((LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n).toContinuousLinearMap : Mat n → Mat n) := by
    funext y; simp
  rw [this]
  exact ContinuousLinearMap.contDiff _

theorem sm_Rd (X : Mat n) {U : ℝ → Mat n → V} (hU : Sm U) : Sm (fun t => Rd X (U t)) :=
  gen_sm (isOpen_invertible_matrices n) hU (contDiff_mulRight X)

theorem cont_slice {U : ℝ → Mat n → V} (hU : Sm U) {x : Mat n} (hx : x ∈ GLs n) :
    Continuous (fun t => U t x) := by
  have h : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hU.continuousOn
  exact h.comp_continuous (f := fun t : ℝ => (t, x)) (by fun_prop) (fun t => ⟨Set.mem_univ _, hx⟩)

theorem bump_support {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |T|) ?_
  intro t ht
  refine hg.2.2 t (lt_of_le_of_lt (le_abs_self T) ?_)
  simpa [Metric.mem_closedBall, Real.dist_eq] using ht

theorem int_sm {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun t => (g t : ℂ) • U t x) := by
  simpa only [Complex.coe_smul] using int_real hg.1.continuous (bump_support hg) (cont_slice hU hx)

theorem rd_avg [CompleteSpace V] (X : Mat n) {U : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ} (hU : Sm U) (hg : IsBump g T)
    {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • Rd X (U t) x := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  simp only [Complex.coe_smul]
  exact gen_avg (isOpen_invertible_matrices n) hU hg.1.continuous (bump_support hg) hx (x * X)

def Good (L : (Mat n → V) → (Mat n → V)) : Prop :=
  (∀ U : ℝ → Mat n → V, Sm U → Sm (fun t => L (U t))) ∧
  (∀ F F' : Mat n → V, (∀ y ∈ GLs n, F y = F' y) → ∀ x ∈ GLs n, L F x = L F' x) ∧
  ∀ (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ), Sm U → IsBump g T → ∀ x ∈ GLs n,
    L (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • L (U t) x

theorem good_id : Good (n := n) (V := V) (fun f => f) :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ _ => rfl⟩

theorem good_zero : Good (n := n) (V := V) (fun _ => 0) := by
  refine ⟨fun U _ => ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => by simp⟩
  exact (contDiffOn_const (c := (0 : V))).congr (fun _ _ => rfl)

theorem good_comp {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ (L₂ f)) := by
  refine ⟨fun U hU => h₁.1 _ (h₂.1 U hU), fun F F' h => h₁.2.1 _ _ (h₂.2.1 F F' h), ?_⟩
  intro U g T hU hg x hx
  show L₁ (L₂ _) x = ∫ t, (g t : ℂ) • L₁ (L₂ (U t)) x
  rw [h₁.2.1 _ (fun x' => ∫ t, (g t : ℂ) • L₂ (U t) x') (h₂.2.2 U g T hU hg) x hx]
  exact h₁.2.2 _ g T (h₂.1 U hU) hg x hx

theorem good_add {L₁ L₂ : (Mat n → V) → (Mat n → V)} (h₁ : Good L₁) (h₂ : Good L₂) :
    Good (fun f => L₁ f + L₂ f) := by
  refine ⟨fun U hU => ?_, fun F F' h x hx => ?_, ?_⟩
  · exact ((h₁.1 U hU).add (h₂.1 U hU)).congr (fun _ _ => rfl)
  · simp only [Pi.add_apply, h₁.2.1 F F' h x hx, h₂.2.1 F F' h x hx]
  · intro U g T hU hg x hx
    simp only [Pi.add_apply, smul_add]
    rw [integral_add (int_sm (h₁.1 U hU) hg hx) (int_sm (h₂.1 U hU) hg hx),
      h₁.2.2 U g T hU hg x hx, h₂.2.2 U g T hU hg x hx]

theorem good_smul (c : ℂ) {L : (Mat n → V) → (Mat n → V)} (h : Good L) : Good (fun f => c • L f) := by
  refine ⟨fun U hU => ?_, fun F F' e x hx => ?_, ?_⟩
  · exact ((h.1 U hU).const_smul c).congr (fun _ _ => rfl)
  · simp only [Pi.smul_apply, h.2.1 F F' e x hx]
  · intro U g T hU hg x hx
    simp only [Pi.smul_apply]
    rw [h.2.2 U g T hU hg x hx, ← integral_smul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => smul_comm _ _ _)

theorem good_sum {ι : Type} (s : Finset ι) {L : ι → (Mat n → V) → (Mat n → V)} (h : ∀ i, Good (L i)) :
    Good (fun f => ∑ i ∈ s, L i f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact good_add (h a) ih

theorem good_Rd [CompleteSpace V] (X : Mat n) : Good (n := n) (V := V) (Rd X) := by
  refine ⟨fun U hU => sm_Rd X hU, fun F F' h x hx => ?_, fun U g T hU hg x hx => rd_avg X hU hg hx⟩
  have he : F =ᶠ[𝓝 x] F' := Filter.eventuallyEq_of_mem ((isOpen_invertible_matrices n).mem_nhds hx) h
  show fderiv ℝ F x (x * X) = fderiv ℝ F' x (x * X)
  rw [he.fderiv_eq]

theorem good_Eu [CompleteSpace V] (s : Bool) (a b : Fin n) : Good (n := n) (V := V) (Eu s a b) :=
  good_smul _ (good_add (good_Rd _) (good_smul _ (good_Rd _)))

theorem good_Epow [CompleteSpace V] (s : Bool) (m : ℕ) (a b : Fin n) : Good (n := n) (V := V) (Epow s m a b) := by
  induction m generalizing a b with
  | zero =>
    by_cases h : a = b
    · simpa [Epow, h] using good_id
    · simpa [Epow, h] using good_zero
  | succ m ih =>
    exact good_sum Finset.univ fun c => good_comp (good_Eu s a c) (ih c b)

theorem good_gel [CompleteSpace V] (s : Bool) (m : ℕ) : Good (n := n) (V := V) (gel s m) :=
  good_sum Finset.univ fun a => good_Epow s m a a

theorem good_zOp [CompleteSpace V] (w : List (Bool × ℕ)) : Good (n := n) (V := V) (zOp w) := by
  induction w with
  | nil => exact good_id
  | cons p w ih =>
    show Good (fun f => gel p.1 p.2 (zOp w f))
    exact good_comp (good_gel p.1 p.2) ih

theorem zOp_avg : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V)
    (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T →
    ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x :=
  fun _ _ _ _ _ U g T w hU hg x hx => (good_zOp w).2.2 U g T hU hg x hx

end GlobalTheory.CompanionTheory.WaveMult.ZOpAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPartialEqRightWord
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Chart

def cmL (n : ℕ) : (Idx n → ℝ) →L[ℝ] Mat n :=
  ∑ p, (ContinuousLinearMap.proj p : (Idx n → ℝ) →L[ℝ] ℝ).smulRight (bs p)

theorem cmL_apply {n : ℕ} (t : Idx n → ℝ) : cmL n t = cm t := by
  simp [cmL, cm]

theorem cm_single {n : ℕ} (p : Idx n) : cmL n (Pi.single p 1) = bs p := by
  rw [cmL_apply]
  simp [cm, Pi.single_apply, ite_smul]

theorem hasFDerivAt_chart {n : ℕ} (t : Idx n → ℝ) :
    HasFDerivAt (fun t : Idx n → ℝ => (1 : Mat n) + cm t) (cmL n) t := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact (cmL n).hasFDerivAt.const_add 1

theorem contDiff_chart {n : ℕ} : ContDiff ℝ ∞ (fun t : Idx n → ℝ => (1 : Mat n) + cm t) := by
  have h : (fun t : Idx n → ℝ => (1 : Mat n) + cm t) = fun t => 1 + cmL n t := by
    funext s; rw [cmL_apply]
  rw [h]
  exact contDiff_const.add (cmL n).contDiff

theorem isOpen_GLs' {n : ℕ} : IsOpen (GLs n) := by
  have : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne_fun this continuous_const

theorem contDiffOn_fderiv_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) : ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    rw [Dw_cons]
    exact contDiffOn_fderiv_const isOpen_GLs' ih (bs p)

theorem pd_chart {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ∀ t : Idx n → ℝ, 1 + cm t ∈ GLs n →
      pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  induction L with
  | nil => intro t _; rfl
  | cons p L ih =>
    intro t ht
    have hopen : IsOpen {s : Idx n → ℝ | (1 : Mat n) + cm s ∈ GLs n} :=
      isOpen_GLs'.preimage contDiff_chart.continuous
    have hev : pd L (fun t : Idx n → ℝ => f (1 + cm t)) =ᶠ[nhds t]
        fun s => Dw L f (1 + cm s) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ht) (fun s hs => ih s hs)
    have hD : DifferentiableAt ℝ (Dw L f) (1 + cm t) :=
      ((contDiffOn_Dw f hf L).contDiffAt (isOpen_GLs'.mem_nhds ht)).differentiableAt (by simp)
    have hc : HasFDerivAt (fun s : Idx n → ℝ => Dw L f (1 + cm s))
        ((fderiv ℝ (Dw L f) (1 + cm t)).comp (cmL n)) t :=
      hD.hasFDerivAt.comp t (hasFDerivAt_chart t)
    rw [pd_cons, Dw_cons]
    show fderiv ℝ (pd L fun t : Idx n → ℝ => f (1 + cm t)) t (Pi.single p 1) = _
    rw [hev.fderiv_eq, hc.fderiv]
    simp [cm_single]

theorem chart_main : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  intro n V _ _ f hf
  refine ⟨?_, fun L t ht => pd_chart f hf L t ht⟩
  exact hf.comp contDiff_chart.contDiffOn (fun t ht => ht)

end GlobalTheory.CompanionTheory.SobGL.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCls

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} [MeasurableSpace (G n)]

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem cls_eq_toLp (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = hf.toLp _ := by
  rw [cls, dite_eq_left hf]

theorem continuous_lift {V : Type} [TopologicalSpace V] {f : Mat n → V}
    (hf : ContinuousOn f (GLs n)) : Continuous (fun y : G n => f y.val) := by
  exact hf.comp_continuous Units.continuous_val (fun y => val_mem_GLs y)

theorem cls_congr (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) : cls μ f = cls μ f' := by
  have hff : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => h _ (val_mem_GLs y)
  unfold cls
  rw [hff]

theorem cls_unique [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {f f' : Mat n → V}
    (hc : ContinuousOn f (GLs n)) (hc' : ContinuousOn f' (GLs n))
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => f' y.val) 2 μ)
    (h : cls μ f = cls μ f') : ∀ g ∈ GLs n, f g = f' g := by
  intro g hg
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf'] at h
  have h1 := (MemLp.toLp_eq_toLp_iff hf hf').1 h
  have h2 := (Continuous.ae_eq_iff_eq μ (continuous_lift hc) (continuous_lift hc')).1 h1
  have hu : IsUnit (Matrix.det g) := isUnit_iff_ne_zero.2 hg
  exact congrFun h2 (Matrix.nonsingInvUnit g hu)

theorem cls_add_smul (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a : ℂ) {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) : cls μ (a • f + f') = a • cls μ f + cls μ f' := by
  have hs : MemLp (fun y : G n => (a • f + f') y.val) 2 μ := (hf.const_smul a).add hf'
  rw [cls_eq_toLp (f := a • f + f') μ hs, cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf',
    ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  rfl

theorem rR_cls [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (hU : Unimod) (h : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val)) := by
  have hmp : MeasurePreserving (fun y : G n => y * h) μ μ := by
    have := (hU n μ).1
    exact measurePreserving_mul_right μ h
  rw [cls_eq_toLp (f := f) μ hf,
    cls_eq_toLp (f := fun y => f (y * h.val)) μ (hf.comp_measurePreserving hmp)]
  unfold rR
  rw [dite_eq_left hmp]
  exact Lp.toLp_compMeasurePreserving hf hmp

theorem compLpL_cls (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →L[ℂ] V) {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    A.compLpL 2 μ (cls μ f) = cls μ (fun y => A (f y)) := by
  have hA : MemLp (fun y : G n => A (f y.val)) 2 μ := A.comp_memLp' hf
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := fun y => A (f y)) μ hA]
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (p := 2) (μ := μ) (hf.toLp _), MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hA]
    with y h1 h2 h3
  rw [h1, h2, h3]

theorem clsFacts : ClsFacts := by
  intro n _ _ μ _ V _ _ hU
  exact ⟨fun f f' hc hc' hf hf' h => cls_unique μ hc hc' hf hf' h,
    fun a f f' hf hf' => cls_add_smul μ a hf hf',
    fun f f' h => cls_congr μ h,
    fun h f hf => rR_cls μ hU h hf,
    fun A f hf => compLpL_cls μ A hf⟩

end GlobalTheory.CompanionTheory.FcCls
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeasureCongruenceInvariant
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeHaar

variable {n : ℕ}

theorem posDef_congr_iff (g H : Mat n) (hg : g.det ≠ 0) : (g * H * gᴴ).PosDef ↔ H.PosDef := by
  have hU : IsUnit (star g) := ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)).star
  have h := Matrix.IsUnit.posDef_star_left_conjugate_iff (x := H) hU
  rwa [star_star, Matrix.star_eq_conjTranspose] at h

theorem det_congr_re (g H : Mat n) : (g * H * gᴴ).det.re = ‖g.det‖ ^ 2 * H.det.re := by
  have h1 : (g * H * gᴴ).det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) * H.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  rw [h1, Complex.re_ofReal_mul]

theorem coneW_congr (g : Mat n) (v w : Fin n × Fin n → ℝ) (h : hOf w = g * hOf v * gᴴ) :
    coneW n w = ENNReal.ofReal ((‖g.det‖ ^ (2 * n))⁻¹) * coneW n v := by
  unfold coneW
  rw [h, det_congr_re, ← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (norm_nonneg g.det) (2 * n))),
    mul_pow, ← pow_mul, mul_inv]

theorem map_coneMeas_eq (n : ℕ) (g : Mat n) (hg : g.det ≠ 0)
    (T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ)) (hT : ∀ v, hOf (T v) = g * hOf v * gᴴ)
    (hdet : LinearMap.det T = ‖g.det‖ ^ (2 * n)) : Measure.map T (coneMeas n) = coneMeas n := by
  have hd : 0 < LinearMap.det T := by
    rw [hdet]
    exact pow_pos (norm_pos_iff.2 hg) _
  have hdT : LinearMap.det T ≠ 0 := hd.ne'
  let e : (Fin n × Fin n → ℝ) ≃ᵐ (Fin n × Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero T hdT).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n × Fin n → ℝ) → (Fin n × Fin n → ℝ)) = T := rfl
  have hC : e ⁻¹' cone n = cone n := by
    ext v
    show (hOf (T v)).PosDef ↔ (hOf v).PosDef
    rw [hT v]
    exact posDef_congr_iff g (hOf v) hg
  have hW : ∀ v, coneW n (e v) = ENNReal.ofReal (LinearMap.det T)⁻¹ * coneW n v := by
    intro v
    rw [hdet]
    exact coneW_congr g v (T v) (hT v)
  have hvol : Measure.map e volume
      = ENNReal.ofReal (LinearMap.det T)⁻¹ • (volume : Measure (Fin n × Fin n → ℝ)) := by
    rw [he, Real.map_linearMap_volume_pi_eq_smul_volume_pi hdT, abs_of_pos (inv_pos.2 hd)]
  have hmap : Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n))
      = ENNReal.ofReal (LinearMap.det T)⁻¹ •
        (volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
    conv_lhs => rw [← hC]
    rw [← MeasurableEquiv.restrict_map, hvol, Measure.restrict_smul]
  have ha0 : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hd)).ne'
  have hatop : ENNReal.ofReal (LinearMap.det T)⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← he]
  ext s hs
  rw [MeasurableEquiv.map_apply]
  unfold coneMeas
  rw [withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← ENNReal.mul_right_inj ha0 hatop]
  calc ENNReal.ofReal (LinearMap.det T)⁻¹ *
        ∫⁻ v in e ⁻¹' s, coneW n v ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)
      = ∫⁻ v in e ⁻¹' s, coneW n (e v) ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        simp_rw [hW]
        rw [lintegral_const_mul' _ _ hatop]
    _ = ∫⁻ w in s, coneW n w
          ∂Measure.map e ((volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n)) := by
        rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    _ = ENNReal.ofReal (LinearMap.det T)⁻¹ *
          ∫⁻ w in s, coneW n w ∂(volume : Measure (Fin n × Fin n → ℝ)).restrict (cone n) := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.ConeHaar
end
end

