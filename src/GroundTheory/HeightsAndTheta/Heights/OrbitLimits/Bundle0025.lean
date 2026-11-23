module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PVarIntGraph
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Matrix Filter Topology
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartInt chartDens chartAbsDens sheetSum IsSheetAt)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet fibre IsFiniteProjection projHom pullback linPoly)

namespace VarIntGraph

variable {n e : ℕ}

def graphProj (A : Matrix (Fin e) (Fin n) ℂ) : Matrix (Fin e) (Fin (n + 1)) ℂ :=
  Matrix.of fun i => Fin.snoc (α := fun _ => ℂ) (A i) 0

theorem graphProj_mulVec (A : Matrix (Fin e) (Fin n) ℂ) (z : Fin (n + 1) → ℂ) :
    graphProj A *ᵥ z = A *ᵥ Fin.init z := by
  funext i
  simp [graphProj, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem graphProj_mulVec_graphPt (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    graphProj A *ᵥ graphPt p x = A *ᵥ x := by
  rw [graphProj_mulVec, graphPt_init]

theorem graphPt_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (graphPt p) := fun x x' h => by
  rw [← graphPt_init p x, ← graphPt_init p x', h]

theorem differentiable_eval (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ fun x : Fin n → ℂ => eval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (differentiable_apply i)

theorem differentiable_graphPt (p : MvPolynomial (Fin n) ℂ) : Differentiable ℂ (graphPt p) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [graphPt] using differentiable_eval p
  · simpa [graphPt] using differentiable_apply (𝕜 := ℂ) j

theorem differentiable_init : Differentiable ℂ fun z : Fin (n + 1) → ℂ => Fin.init z :=
  differentiable_pi.2 fun i => differentiable_apply (Fin.castSucc i)

theorem graphHom_comp_pullback (A : Matrix (Fin e) (Fin n) ℂ) (p : MvPolynomial (Fin n) ℂ) :
    (graphHom p).comp (pullback (graphProj A)) = pullback A := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [pullback, linPoly, graphProj, Fin.sum_univ_castSucc, graphHom_X_castSucc, MvPolynomial.algebraMap_eq]

theorem exists_quotEquiv (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ∃ φ : (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) ≃+* (MvPolynomial (Fin n) ℂ ⧸ J),
      ∀ q, φ (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk J (graphHom p q) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg), fun q => rfl⟩

theorem isFiniteProjection_graphProj {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    (p : MvPolynomial (Fin n) ℂ) (hA : IsFiniteProjection J A) :
    IsFiniteProjection (graphIdeal J p) (graphProj A) := by
  obtain ⟨φ, hφ⟩ := exists_quotEquiv J p
  have hcomp : ∀ q, φ (projHom (graphIdeal J p) (graphProj A) q) = projHom J A q := by
    intro q
    simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hφ]
    rw [← AlgHom.comp_apply, graphHom_comp_pullback]
  have heq : (projHom (graphIdeal J p) (graphProj A)).toRingHom =
      (φ.symm : (MvPolynomial (Fin n) ℂ ⧸ J) →+* _).comp (projHom J A).toRingHom :=
    RingHom.ext fun q => by simp [← hcomp]
  refine ⟨fun a b h => hA.injective (by rw [← hcomp, ← hcomp, h]), ?_⟩
  rw [heq]
  exact (RingHom.Finite.of_surjective _ φ.symm.surjective).comp hA.finite

theorem fibre_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (y : Fin e → ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.fibre (graphIdeal J p) (graphProj A) y = graphPt p '' GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y := by
  ext z
  constructor
  · rintro ⟨hz, hzy⟩
    refine ⟨Fin.init z, ⟨init_mem_zeroSet p hz, ?_⟩, graphPt_init_of_mem_zeroSet p hz⟩
    rwa [graphProj_mulVec] at hzy
  · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
    exact ⟨graphPt_mem_zeroSet p hx, by rw [graphProj_mulVec_graphPt]; exact hxy⟩

theorem isSheetAt_graph {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) :
    IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) (graphPt p ∘ s) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  refine ⟨U, hU, by rwa [graphProj_mulVec_graphPt], (differentiable_graphPt p).comp_differentiableOn hsd,
    by rw [graphProj_mulVec_graphPt, Function.comp_apply, hsx], fun y hy => ⟨?_, graphPt_mem_zeroSet p (hsZ y hy).2⟩,
    (fun z => Fin.init z) ⁻¹' V, ?_, ?_⟩
  · rw [Function.comp_apply, graphProj_mulVec_graphPt, (hsZ y hy).1]
  · exact differentiable_init.continuous.continuousAt.preimage_mem_nhds (by rwa [graphPt_init])
  · rintro z ⟨hz, hzV⟩ hzU
    rw [graphProj_mulVec] at hzU ⊢
    have h := hsV (Fin.init z) ⟨init_mem_zeroSet p hz, hzV⟩ hzU
    rw [Function.comp_apply, ← h, graphPt_init_of_mem_zeroSet p hz]

theorem isSheetAt_init {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin e) (Fin n) ℂ}
    {p : MvPolynomial (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin e → ℂ) → Fin (n + 1) → ℂ}
    (hs : IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) :
    IsSheetAt J A x (fun y => Fin.init (s y)) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsZ, V, hV, hsV⟩ := hs
  rw [graphProj_mulVec_graphPt] at hxU hsx
  refine ⟨U, hU, hxU, differentiable_init.comp_differentiableOn hsd,
    by show Fin.init (s (A *ᵥ x)) = x; rw [hsx, graphPt_init],
    fun y hy => ⟨?_, init_mem_zeroSet p (hsZ y hy).2⟩, graphPt p ⁻¹' V,
    (differentiable_graphPt p).continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
  · have h := (hsZ y hy).1
    rwa [graphProj_mulVec] at h
  · rintro x' ⟨hx', hx'V⟩ hx'U
    have h := hsV (graphPt p x') ⟨graphPt_mem_zeroSet p hx', hx'V⟩ (by rwa [graphProj_mulVec_graphPt])
    rw [graphProj_mulVec_graphPt] at h
    show x' = Fin.init (s (A *ᵥ x'))
    rw [← h, graphPt_init]

theorem sheet_eventuallyEq {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {z : Fin m → ℂ} {s t : (Fin e → ℂ) → Fin m → ℂ} (hs : IsSheetAt K B z s) (ht : IsSheetAt K B z t) :
    s =ᶠ[𝓝 (B *ᵥ z)] t := by
  obtain ⟨U, hU, hzU, hsd, hsz, hsZ, -⟩ := hs
  obtain ⟨U', hU', hzU', -, -, -, V, hV, htV⟩ := ht
  have hc : ContinuousAt s (B *ᵥ z) := (hsd.differentiableAt (hU.mem_nhds hzU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (B *ᵥ z), s y ∈ V := hc.preimage_mem_nhds (by rwa [hsz])
  filter_upwards [hU.mem_nhds hzU, hU'.mem_nhds hzU', hV'] with y hy hy' hyV
  obtain ⟨hBy, hZy⟩ := hsZ y hy
  have h := htV (s y) ⟨hZy, hyV⟩ (by rwa [hBy])
  rwa [hBy] at h

theorem maDens_congr_sheet {m : ℕ} (φ : Fin e → (Fin m → ℂ) → ℝ) {s t : (Fin e → ℂ) → Fin m → ℂ}
    {y : Fin e → ℂ} (h : s =ᶠ[𝓝 y] t) :
    ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y = ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ t) y := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ s) y) = fun k => ReciprocityTheory.AnForm.hessC (φ k ∘ t) y :=
    funext fun k => ReciprocityTheory.AnForm.A.hessC_congr' (h.fun_comp (φ k))
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem sheetSum_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (G : ℝ → ℝ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ)
    (y : Fin e → ℂ) :
    sheetSum (graphIdeal J p) (graphProj A)
        (fun z s => G (F z * ReciprocityTheory.AnForm.maDens (fun k => Φ k ∘ s) y)) y =
      sheetSum J A (fun x s => G (F (graphPt p x) *
        ReciprocityTheory.AnForm.maDens (fun k => (fun x => Φ k (graphPt p x)) ∘ s) y)) y := by
  unfold sheetSum
  rw [fibre_graphProj, finsum_mem_image (graphPt_injective p).injOn]
  refine finsum_mem_congr rfl fun x hx => ?_
  have hiff : (∃ s, IsSheetAt (graphIdeal J p) (graphProj A) (graphPt p x) s) ↔ ∃ s, IsSheetAt J A x s :=
    ⟨fun ⟨_, h⟩ => ⟨_, isSheetAt_init h⟩, fun ⟨_, h⟩ => ⟨_, isSheetAt_graph h⟩⟩
  by_cases h : ∃ s, IsSheetAt J A x s
  · rw [dite_eq_left (hiff.2 h), dite_eq_left h]
    have hE := sheet_eventuallyEq (hiff.2 h).choose_spec (isSheetAt_graph (p := p) h.choose_spec)
    rw [graphProj_mulVec_graphPt, hx.2] at hE
    dsimp only
    rw [maDens_congr_sheet Φ hE]
    rfl
  · rw [dite_eq_right (mt hiff.1 h), dite_eq_right h]

theorem chartDens_graphProj (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin e) (Fin n) ℂ)
    (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ) (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ) :
    chartDens (graphIdeal J p) (graphProj A) F Φ =
      chartDens J A (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x)) :=
  funext fun y => sheetSum_graphProj J A p id F Φ y

theorem chartAbsDens_congr_zeroSet {m : ℕ} {K : Ideal (MvPolynomial (Fin m) ℂ)} {B : Matrix (Fin e) (Fin m) ℂ}
    {f g : (Fin m → ℂ) → ℝ} (h : ∀ x ∈ zeroSet K, f x = g x) (φ : Fin e → (Fin m → ℂ) → ℝ) :
    chartAbsDens K B f φ = chartAbsDens K B g φ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]

end VarIntGraph


open VarIntGraph in
theorem VarIntGraphInt.proof (hI : IntegralIndep.Statement) : VarIntGraphInt.Statement := by
  classical
  intro n e J p F Φ hJ hF hΦ hint
  have hG := graphIdeal_isPrime hJ p
  have hex : (∃ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B) ↔
      ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A := by
    refine ⟨fun ⟨B, hB⟩ => ?_, fun ⟨A, hA⟩ => ⟨_, isFiniteProjection_graphProj p hA⟩⟩
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
    rw [ringKrullDim_graphIdeal] at hd
    exact ComplexSets.LinearNoetherNormalization.proof n e J hd
  unfold varInt
  by_cases hJA : ∃ A : Matrix (Fin e) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · rw [dite_eq_right (mt hex.1 hJA), dite_eq_right hJA]
  rw [dite_eq_left (hex.2 hJA), dite_eq_left hJA, chartInt, chartInt, ← chartDens_graphProj]
  have hA := isFiniteProjection_graphProj p hJA.choose_spec
  have hB := (hex.2 hJA).choose_spec
  obtain ⟨U, hU, hZU, hFU⟩ := hF
  have hFF : ∀ z ∈ zeroSet (graphIdeal J p), U.indicator F z = F z := fun z hz => Set.indicator_of_mem (hZU hz) F
  have hFm : Measurable (U.indicator F) := by
    rw [← Set.piecewise_eq_indicator]
    exact hFU.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hB
  have hi : Integrable (chartAbsDens (graphIdeal J p) (graphProj hJA.choose) (U.indicator F) Φ) := by
    rw [chartAbsDens_congr_zeroSet hFF]
    exact hint _ hA
  have h := (hI (n + 1) e (graphIdeal J p) _ _ (U.indicator F) Φ hG hd hA hB hFm hΦ hi).2
  rw [chartInt, chartInt, CutOffDominated.chartDens_congr_zeroSet hFF Φ,
    CutOffDominated.chartDens_congr_zeroSet hFF Φ] at h
  exact h.symm

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

namespace PtsPosDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logNorm_ofWeight_one {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    logNorm (HermLine.ofWeight g hg.2) 1 = g := by
  funext z
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

theorem isSmoothHerm_ofWeight {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSmoothHerm (HermLine.ofWeight g hg.2) :=
  show ContDiffOn ℝ _ (fun z => Real.exp (-g z)) _ from Real.contDiff_exp.comp_contDiffOn hg.1.neg

theorem isSectionOn_ofWeight_one {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    IsSectionOn P (HermLine.ofWeight g hg.2) 1 := by
  refine ⟨0, fun k => by simp [HermLine.ofWeight], fun m hm k => ?_,
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem exists_bound {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = 1} with hTdef
  have hTc : IsClosed T := by
    rw [hTdef, Set.ofPred_forall]
    exact isClosed_iInter fun k =>
      isClosed_eq (continuous_norm.comp (continuous_pi fun i => continuous_apply _)) continuous_const
  have hTb : T ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 := norm_le_pi_norm (fun i : ι p.1 => z ⟨p.1, i⟩) p.2
    rw [hz p.1] at h1
    exact h1
  have hTK : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  have hTU : T ⊆ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    push Not at h
    have h0 : (fun i : ι k => z ⟨k, i⟩) = 0 := funext h
    have := hz k
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨M, hM⟩ := hTK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hTU)
  refine ⟨M, fun z hz => ?_⟩
  have hb : ∀ k, (fun i : ι k => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  set c : K → ℂ := fun k => ((‖fun i : ι k => z ⟨k, i⟩‖ : ℝ) : ℂ)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hb k)))
  have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    intro k
    have : (fun i : ι k => c k * z ⟨k, i⟩) = c k • fun i : ι k => z ⟨k, i⟩ := rfl
    rw [this, norm_smul, hcdef]
    simp only [norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hb k))
  rw [← hg.2 c z hc]
  exact hM _ hmem

theorem isSemiPosHerm_tensor {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hAp : Inter.IsSemiPosHerm A) (hBp : Inter.IsSemiPosHerm B) : Inter.IsSemiPosHerm (A.tensor B) := by
  intro z hz v
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := isOpen_blockNonzero
  have hline : Continuous fun t : ℂ => z + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    simpa using hU.mem_nhds hz
  have hsm : ∀ C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm C →
      ContDiffAt ℝ 2 (fun t : ℂ => Real.log (C.h (z + t • v))) 0 := by
    intro C hC
    have h1 : ContDiffAt ℝ 2 C.h (z + (0 : ℂ) • v) := by
      rw [zero_smul, add_zero]
      exact (hC.contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
    have h2 : ContDiffAt ℝ 2 (fun t : ℂ => z + t • v) 0 := by fun_prop
    have h3 := h1.comp (0 : ℂ) h2
    refine h3.log ?_
    simp only [Function.comp, zero_smul, add_zero]
    exact (C.pos z hz).ne'
  have heq : (fun t : ℂ => Real.log ((A.tensor B).h (z + t • v))) =ᶠ[𝓝 0]
      (fun t : ℂ => Real.log (A.h (z + t • v))) + fun t : ℂ => Real.log (B.h (z + t • v)) := by
    filter_upwards [hev] with t ht
    simp only [Pi.add_apply, HermLine.tensor]
    exact Real.log_mul (A.pos _ ht).ne' (B.pos _ ht).ne'
  rw [(laplacian_congr_nhds heq).eq_of_nhds, (hsm A hA).laplacian_add (hsm B hB)]
  exact add_nonneg (hAp z hz v) (hBp z hz v)

theorem aestronglyMeasurable {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by
  classical
  have hfin := fibreFinite K ι P e Ψ hP hΨ
  obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
  have hind := sheetIndep K ι P e Ψ L _ 1 hP hΨ hL (isSmoothHerm_ofWeight hg) (isSectionOn_ofWeight_one hP hg)
  rw [logNorm_ofWeight_one hg] at hind
  have hsheet : ∀ m, ∀ y ∈ B m, IsSheet P Ψ y (segre (γ m y)) (γ m) := fun m y hy =>
    ⟨rfl, Filter.eventually_of_mem ((hBo m).mem_nhds hy) fun y' hy' => hlift m y' hy'⟩
  have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
    (hlift m y hy).1.continuousAt.continuousWithinAt
  have hO : ∀ m, Set.MapsTo (γ m) (B m) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun m y hy =>
    (hlift m y hy).2.1.1
  have hseg : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd _ fun k _ => continuous_apply _
  set σ : ℕ → (Fin e → ℂ) → ((k : K) → ι k) → ℂ := fun m =>
    (B m).piecewise (fun y => segre (γ m y)) 0 with hσdef
  have hσB : ∀ m, ∀ y ∈ B m, σ m y = segre (γ m y) := fun m y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have hσm : ∀ m, Measurable (σ m) := fun m =>
    (hseg.comp_continuousOn (hγc m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set a : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m).piecewise (fun y => g (γ m y)) 0 with hadef
  have ham : ∀ m, Measurable (a m) := fun m =>
    (hg.1.continuousOn.comp (hγc m) (hO m)).measurable_piecewise continuousOn_const (hBo m).measurableSet
  set dens : ℕ → (Fin e → ℂ) → ℝ := fun m y =>
    max (a m y * maDensity (fun j y' => pot L j (γ m y')) y) 0 with hddef
  have hdm : ∀ m, Measurable (dens m) := fun m =>
    ((ham m).mul (PtsSumMeasurable.measurable_maDensity _)).max measurable_const
  have hdens : ∀ m, ∀ y ∈ B m,
      dens m y = max (g (γ m y) * maDensity (fun j y' => pot L j (γ m y')) y) 0 := by
    intro m y hy
    simp only [hddef, hadef, Set.piecewise_eq_of_mem _ _ _ hy]
  set S : ℕ → Set (Fin e → ℂ) := fun m =>
    {y | y ∈ B m ∧ ∀ m' < m, ¬ (y ∈ B m' ∧ σ m' y = σ m y)} with hSdef
  have hSm : ∀ m, MeasurableSet (S m) := by
    intro m
    have : S m = B m ∩ ⋂ m' ∈ Finset.range m, (B m' ∩ {y | σ m' y = σ m y})ᶜ := by
      ext y
      simp [hSdef, imp_iff_not_or]
    rw [this]
    exact (hBo m).measurableSet.inter (Finset.measurableSet_biInter _ fun m' _ =>
      ((hBo m').measurableSet.inter (measurableSet_eq_fun (hσm m') (hσm m))).compl)
  set f : ℕ → (Fin e → ℂ) → ℝ := fun m => (S m).indicator (dens m) with hfdef
  have hfm : ∀ m, Measurable (f m) := fun m => (hdm m).indicator (hSm m)
  have hpp : ptsPosDens P Ψ (pot L) g =
      fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 := rfl
  rw [hpp]
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N y => ∑ m ∈ Finset.range N, f m y)
    (fun N => (Finset.measurable_sum _ fun m _ => hfm m).aestronglyMeasurable) ?_
  filter_upwards [hind] with y hy
  have hterm : ∀ m, y ∈ S m → f m y = max (sheetDensity P Ψ (pot L) g y (σ m y)) 0 := by
    intro m hm
    have hsh := hsheet m y hm.1
    rw [← hσB m y hm.1] at hsh
    have hex : ∃ γ', IsSheet P Ψ y (σ m y) γ' := ⟨_, hsh⟩
    rw [hfdef]
    simp only
    rw [Set.indicator_of_mem hm, hdens m y hm.1]
    unfold sheetDensity
    rw [dite_eq_left hex]
    rw [hy _ _ _ hex.choose_spec hsh]
  have hmemF : ∀ m, y ∈ S m → σ m y ∈ (hfin y).toFinset := by
    intro m hm
    rw [Set.Finite.mem_toFinset, hσB m y hm.1]
    exact ⟨γ m y, (hlift m y hm.1).2.1, rfl, (hlift m y hm.1).2.2⟩
  have hfy : ∀ m, (∑ w ∈ (hfin y).toFinset, if σ m y = w then f m y else 0) = f m y := by
    intro m
    rw [Finset.sum_ite_eq]
    by_cases hm : y ∈ S m
    · rw [if_pos (hmemF m hm)]
    · split_ifs
      · rfl
      · rw [hfdef]
        simp only
        rw [Set.indicator_of_notMem hm]
  have hev : ∀ w ∈ (hfin y).toFinset, ∀ᶠ N in atTop,
      max (sheetDensity P Ψ (pot L) g y w) 0 =
        ∑ m ∈ Finset.range N, if σ m y = w then f m y else 0 := by
    intro w _
    by_cases hex : ∃ γ', IsSheet P Ψ y w γ'
    · obtain ⟨γ', hγ'⟩ := hex
      have hP' : ∃ m, y ∈ B m ∧ σ m y = w := by
        obtain ⟨m, hm, hmw⟩ := hcov y w γ' hγ'
        exact ⟨m, hm, (hσB m y hm).trans hmw⟩
      obtain ⟨hm1B, hm1w⟩ := Nat.find_spec hP'
      have hm1S : y ∈ S (Nat.find hP') :=
        ⟨hm1B, fun m' hm' h => Nat.find_min hP' hm' ⟨h.1, h.2.trans hm1w⟩⟩
      filter_upwards [eventually_gt_atTop (Nat.find hP')] with N hN
      rw [Finset.sum_eq_single_of_mem (Nat.find hP') (Finset.mem_range.2 hN), if_pos hm1w,
        hterm _ hm1S, hm1w]
      intro m _ hne
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · exfalso
          have hle : Nat.find hP' ≤ m := Nat.find_min' hP' ⟨hmS.1, hmw⟩
          exact hmS.2 _ (lt_of_le_of_ne hle (Ne.symm hne)) ⟨hm1B, hm1w.trans hmw.symm⟩
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
    · have h0 : sheetDensity P Ψ (pot L) g y w = 0 := by
        unfold sheetDensity
        rw [dite_eq_right hex]
      refine Eventually.of_forall fun N => ?_
      rw [h0, max_self]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hmw
      · by_cases hmS : y ∈ S m
        · have hsh := hsheet m y hmS.1
          rw [← hσB m y hmS.1, hmw] at hsh
          exact absurd ⟨_, hsh⟩ hex
        · rw [hfdef]
          simp only
          rw [Set.indicator_of_notMem hmS]
      · rfl
  have hsum : ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, max (sheetDensity P Ψ (pot L) g y w) 0 =
      ∑ w ∈ (hfin y).toFinset, max (sheetDensity P Ψ (pot L) g y w) 0 :=
    finsum_mem_eq_finite_toFinset_sum _ (hfin y)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(eventually_all_finset _).2 hev] with N hN
  rw [hsum, Finset.sum_congr rfl hN, Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => hfy m

end PtsPosDens

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (a r : ℕ) (v : Fin r → Ω),
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) N → IsConjInvariantH N →
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r), A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg (none : Option K) ∧ IsConjInvariantH A ∧
      IsSemipositiveRel (mCoordIdeal (addBlock y v)) (mCoordIdeal (addBlock y v)) A ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * A.h z = ‖z ⟨none, j⟩‖

end

end GroundTheory.Heights₂.Heights.Targets
end

