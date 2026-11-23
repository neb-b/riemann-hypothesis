module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollB
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureB

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassStep.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1) (ε t : ℝ), 0 < ε → 0 < t → S.ell₀ ≤ ell t →
      S.J (a + 1) ε t ≤ S.J a ε t + S.plTerm a ha ε t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

namespace ArgumentConvergenceLemmas

open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)

noncomputable section

theorem molli_contDiffAt {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_fderiv_eq (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_sub_eq {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]

theorem norm_iteratedFDeriv_comp_le_of_isOpen {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)

theorem exists_bound_iteratedFDeriv {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))

end Calculus

theorem tendstoUniformlyOn_of_norm_le {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt

end

end ArgumentConvergenceLemmas

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi levi_zero levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_rsmul_chart (A : FinHolAtlas D X) (P : LocPot X) (hP : IsPotential A P) (a : ℝ)
    (x : X) (k : Fin A.n) (y : Fin D → ℂ)
    (hy : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x) (w : Fin D → ℂ) :
    levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w = a * levi (P.φ x ∘ (A.chart k).symm) y w := by
  have hs : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y :=
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hs w
  have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
      fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
    funext z
    simp [LocPot.rsmul]
  rw [he, h, levi_const, zero_add]

theorem BoundingKaehler.proof : BoundingKaehler.Statement := by
  intro X _ _ _ D A om m th hth
  have hX : IsCompact (Set.univ : Set X) := isCompact_univ
  choose M hM0 hM using fun i => levi_abs_le_global A hX (th i) om.pot (hth i) om.isPot om.pos
  set K : ℝ := 1 + ∑ i, M i with hKdef
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => hM0 i
  have hK : 0 < K := by linarith
  have hMK : ∀ i, M i ≤ K := fun i => by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hM0 j) (Finset.mem_univ i)
    linarith
  have hnn : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x, ∀ w : Fin D → ℂ,
      0 ≤ levi (om.pot.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, levi_zero]
    · exact (om.pos x k y hy w h0).le
  refine ⟨⟨om.pot.rsmul K, ReciprocityTheory.AnForm.M.isPotentialRsmul A K om.pot om.isPot,
    fun x k y hy w hw => ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [levi_rsmul_chart A om.pot om.isPot K x k y hy w]
    exact mul_pos hK (om.pos x k y hy w hw)
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.1.2, hy.2.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith
  · intro x k y hy w
    have hyo : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' om.pot.U x := ⟨hy.1, hy.2.1.2⟩
    have hyb : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((th i).U x ∩ om.pot.U x) :=
      ⟨hy.1, hy.2.2, hy.2.1.2⟩
    rw [levi_rsmul_chart A om.pot om.isPot K x k y hyo w]
    have h1 := abs_le.mp (hM i x k y hyb w)
    have h2 := hnn x k y hyo w
    have h3 := hMK i
    nlinarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem ListMono.proof (hRaise : ListMonoRaise.Statement) (hDens : ListMonoDens.Statement)
    (hCont : LocDensContOnOpen.Statement) (hInt : MIntegrableOfDensLe.Statement)
    (hMono : MIntMonoOfDensLe.Statement) : ListMono.Statement := by
  intro X _ _ _ D A Yo r Om C₁ th u hYo hT
  have hdens := hDens A Yo th Om.pot u hYo (fun i => (hT i).th_pot) Om.isPot
    (fun i => (hT i).u_smooth) (fun i => (hT i).th_le) (fun i => (hT i).nonneg)
  refine ⟨fun i => hRaise A Yo (th i) Om.pot (u i) hYo (hT i).th_pot Om.isPot (hT i).u_smooth
    (hT i).th_le (hT i).nonneg, fun j y hy hY => (hdens j y hy hY).1, fun g hg0 hgV hgA => ?_⟩
  have hcT := hCont A Yo th u hYo (fun i => (hT i).th_pot) (fun i => (hT i).u_smooth)
  have hcA := hCont A Yo (fun _ => Om.pot) u hYo (fun _ => Om.isPot) (fun i => (hT i).u_smooth)
  exact ⟨hInt A Yo _ _ hYo hcT hcA hdens g hgV hgA, hMono A Yo _ _ hdens g hg0 hgV hgA⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoDens
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Topology
open scoped ComplexOrder Matrix
open ReciprocityTheory.AnForm (levi hessC maDens)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

theorem ListMonoDens.proof : ListMonoDens.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn j y hy hyY
  set p := (A.chart j).symm y with hp

  set f : Fin D → (Fin D → ℂ) → ℝ := fun i y' => (th i).φ p ((A.chart j).symm y') with hf
  set v : Fin D → (Fin D → ℂ) → ℝ := fun i y' => u i ((A.chart j).symm y') with hv
  set o : (Fin D → ℂ) → ℝ := fun y' => Om.φ p ((A.chart j).symm y') with ho
  have hfC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two (hth i) p j hy ((th i).mem_U p)
  have hoC : ContDiffAt ℝ 2 o y :=
    ReciprocityTheory.AnForm.M.pot_contDiffAt_two hOm p j hy (Om.mem_U p)
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo) :=
    (A.chart j).isOpen_inter_preimage_symm hYo
  have hvC : ∀ i, ContDiffAt ℝ 2 (v i) y := fun i =>
    ((hu i j).contDiffAt (hopen.mem_nhds ⟨hy, hyY⟩)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  have hgC : ∀ i, ContDiffAt ℝ 2 (fun y' => o y' + (-1) * f i y') y := fun i =>
    hoC.add (contDiffAt_const.mul (hfC i))

  have hA : ∀ i, (hessC (fun y' => f i y' + v i y') y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y ((hfC i).add (hvC i)) fun w =>
      hnn i p j y ⟨hy, hyY, (th i).mem_U p, Set.mem_univ _⟩ w

  have hB : ∀ i, (hessC (fun y' => o y' + (-1) * f i y') y).PosSemidef := fun i => by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef_of_levi _ y (hgC i)
      fun w => ?_
    rw [ReciprocityTheory.AnForm.levi_add_smul (-1) hoC (hfC i) w]
    have h := hle i p j y ⟨hy, ⟨⟨Set.mem_univ _, (th i).mem_U p⟩, Om.mem_U p⟩⟩ w
    have h' : 1 * levi (f i) y w ≤ 1 * levi o y w := h
    linarith

  have hsum : ∀ i, hessC (fun y' => o y' + v i y') y =
      hessC (fun y' => f i y' + v i y') y + hessC (fun y' => o y' + (-1) * f i y') y := fun i => by
    rw [← ReciprocityTheory.AnForm.A.hessC_add _ _ y ((hfC i).add (hvC i))
      (hgC i)]
    congr 1
    funext y'
    ring
  have e1 : locDens A (fun i => potForm (th i) (u i)) j y =
      maDens (fun i y' => f i y' + v i y') y := rfl
  have e2 : locDens A (fun i => potForm Om (u i)) j y = maDens (fun i y' => o y' + v i y') y := rfl
  rw [e1, e2]
  refine ⟨ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y hA, ?_⟩
  unfold maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _ hA fun i => ?_) (by positivity)
  simpa [hsum i] using hB i

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListMonoRaise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul levi_re_analytic)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential potSmoothAt)

theorem ListMonoRaise.proof : ListMonoRaise.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn x k y hy w
  set s := (A.chart k).symm with hs
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyYo : s y ∈ Yo := hy.2.1
  have hyOx : s y ∈ Om.U x := hy.2.2.1

  have hadd : ∀ {f g : (Fin D → ℂ) → ℝ}, ContDiffAt ℝ 2 f y → ContDiffAt ℝ 2 g y →
      levi (fun v => f v + g v) y w = levi f y w + levi g y w := by
    intro f g hf hg
    simpa using levi_add_smul 1 hf hg w

  have hus : ContDiffAt ℝ 2 (u ∘ s) y :=
    ((hu k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hYo).mem_nhds ⟨hyt, hyYo⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hths : ContDiffAt ℝ 2 (th.φ (s y) ∘ s) y := potSmoothAt A th hth (s y) k ⟨hyt, th.mem_U _⟩
  have hOms : ContDiffAt ℝ 2 (Om.φ (s y) ∘ s) y := potSmoothAt A Om hOm (s y) k ⟨hyt, Om.mem_U _⟩

  obtain ⟨W, hWo, hpW, G, hG, hGeq⟩ := hOm.2 (s y) x (s y) ⟨Om.mem_U _, hyOx⟩
  have hGa : AnalyticAt ℂ (G ∘ s) y := hG k y ⟨hyt, hpW⟩
  have hGre : ContDiffAt ℝ 2 (fun v => ((G ∘ s) v).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars.contDiffAt (n := 2)))
  have hVo : IsOpen ((A.chart k).target ∩ s ⁻¹' (W ∩ Om.U (s y) ∩ Om.U x)) :=
    (A.chart k).isOpen_inter_preimage_symm ((hWo.inter (Om.isOpen_U _)).inter (Om.isOpen_U x))
  have hgerm : (potForm Om u).φ x ∘ s =ᶠ[𝓝 y]
      fun v => ((Om.φ (s y) ∘ s) v + (u ∘ s) v) + (-1) * ((G ∘ s) v).re := by
    filter_upwards [hVo.mem_nhds ⟨hyt, ⟨hpW, Om.mem_U _⟩, hyOx⟩] with v hv
    have := hGeq (s v) hv.2
    show Om.φ x (s v) + u (s v) = (Om.φ (s y) (s v) + u (s v)) + (-1) * (G (s v)).re
    linarith
  have hΩ : levi ((potForm Om u).φ x ∘ s) y w = levi (Om.φ (s y) ∘ s) y w + levi (u ∘ s) y w := by
    rw [levi_congr hgerm, levi_add_smul (-1) (hOms.add hus) hGre, levi_re_analytic hGa,
      hadd hOms hus]
    ring

  have h1 := hle (s y) k y ⟨hyt, ⟨trivial, th.mem_U _⟩, Om.mem_U _⟩ w
  have h2 := hnn (s y) k y ⟨hyt, hyYo, th.mem_U _, trivial⟩ w
  have hT : levi ((potForm th u).φ (s y) ∘ s) y w = levi (th.φ (s y) ∘ s) y w + levi (u ∘ s) y w :=
    hadd hths hus
  rw [hT] at h2
  rw [hΩ]
  linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PMIntMonoOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable ChartPartition integralWith)

theorem MIntMonoOfDensLe.proof : MIntMonoOfDensLe.Statement := by
  intro D X _ _ A V Φ Ψ hd g hg0 hgV hgi
  unfold mInt
  split_ifs with h
  · unfold integralWith
    refine Finset.sum_le_sum fun j _ => ?_
    have hTm := (A.chart j).open_target.measurableSet
    obtain ⟨hKc, hKs⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
      (isClosed_tsupport (h.some.χ j)) (h.some.tsupport_subset j)
    have hcc := ReciprocityTheory.AnForm.M.chi_comp_continuousOn h.some j
    have hint : IntegrableOn (fun y => h.some.χ j ((A.chart j).symm y) *
        g ((A.chart j).symm y) * locDens A Ψ j y) (A.chart j).target := by
      refine ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j)
        (Z := tsupport (h.some.χ j)) (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
      have h1 := (hgi j _ hKs hKc).mul_continuousOn (hcc.mono hKs) hKc
      exact h1.congr_fun (fun y _ => by ring) hKc.measurableSet
    refine integral_mono_of_nonneg (ae_restrict_of_forall_mem hTm fun y hy => ?_) hint
      (ae_restrict_of_forall_mem hTm fun y hy => ?_)
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg0 _)) (hd j y hy hyV).1
      · simp [hgV _ hyV]
    · by_cases hyV : (A.chart j).symm y ∈ V
      · exact mul_le_mul_of_nonneg_left (hd j y hy hyV).2 (mul_nonneg (h.some.nonneg j _) (hg0 _))
      · simp [hgV _ hyV]
  · exact le_rfl

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

