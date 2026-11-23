module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeSheets
section
namespace ReciprocityTheory.AnForm.M

open FinHolAtlas Topology

noncomputable section

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isClosed_of_isAnalyticSubset' (A : FinHolAtlas e X) {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  unfold FinHolAtlas.IsAnalyticSubset at hS
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have hxSW : x ∈ S ∩ W := by
      rw [hSW]
      exact ⟨hxW, hcon⟩
    exact hxSW.1
  obtain ⟨i, hi⟩ := hne
  have hca : ContinuousAt (f i) x := by
    obtain ⟨j, hxj⟩ := A.cover x
    have h : ∀ k, AnalyticOnNhd ℂ ((f i) ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf i
    have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
      refine ⟨(A.chart j).map_source hxj, ?_⟩
      show (A.chart j).symm ((A.chart j) x) ∈ W
      rw [(A.chart j).left_inv hxj]
      exact hxW
    have h1 : ContinuousAt ((f i ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
      ((h j _ hmem).continuousAt).comp ((A.chart j).continuousAt hxj)
    refine h1.congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hxj] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy]
  filter_upwards [hW.mem_nhds hxW, hca.eventually_ne hi] with y hyW hyi hyS
  have hy : y ∈ S ∩ W := ⟨hyS, hyW⟩
  rw [hSW] at hy
  exact hyi (hy.2 i)

theorem exists_localHomeomorph_of_isDegreeOff {A : FinHolAtlas e X} {B : FinHolAtlas e Y}
    {h : Y → X} (hh : HoloMap B A h) {d : ℕ} {S : Set X} (hd : IsDegreeOff A B h d S) (y : Y)
    (hy : h y ∉ S) :
    ∃ E : OpenPartialHomeomorph Y X, y ∈ E.source ∧ Set.EqOn h E E.source ∧
      ∃ j : Fin B.n, E.source ⊆ (B.chart j).source := by
  obtain ⟨j, hyj⟩ := B.cover y
  obtain ⟨k, hk⟩ := A.cover (h y)
  have hb : (B.chart j) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source) := by
    refine ⟨(B.chart j).map_source hyj, ?_⟩
    show h ((B.chart j).symm ((B.chart j) y)) ∈ (A.chart k).source
    rw [(B.chart j).left_inv hyj]
    exact hk
  have han := hh.2 j k ((B.chart j) y) hb
  have hdet := hd.2.2.2.2.2 j k ((B.chart j) y) ((B.chart j).map_source hyj)
    (by rw [(B.chart j).left_inv hyj]; exact hy) (by rw [(B.chart j).left_inv hyj]; exact hk)
  set L := (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv with hL
  have hstrict : HasStrictFDerivAt ((A.chart k) ∘ h ∘ (B.chart j).symm)
      (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) ((B.chart j) y) :=
    han.hasStrictFDerivAt.congr_fderiv (by ext v; rfl)
  set Φ := hstrict.toOpenPartialHomeomorph ((A.chart k) ∘ h ∘ (B.chart j).symm) with hΦ
  have hcoe : (Φ : (Fin e → ℂ) → (Fin e → ℂ)) = (A.chart k) ∘ h ∘ (B.chart j).symm :=
    hstrict.toOpenPartialHomeomorph_coe
  have hsrc : (B.chart j) y ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hU : IsOpen (h ⁻¹' (A.chart k).source) := (A.chart k).open_source.preimage hh.1
  refine ⟨(((B.chart j).trans Φ).trans (A.chart k).symm).restrOpen _ hU, ?_, ?_, j, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨⟨hyj, hsrc⟩, ?_⟩, hk⟩
    show Φ ((B.chart j) y) ∈ (A.chart k).target
    rw [hcoe]
    show (A.chart k) (h ((B.chart j).symm ((B.chart j) y))) ∈ (A.chart k).target
    rw [(B.chart j).left_inv hyj]
    exact (A.chart k).map_source hk
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    obtain ⟨⟨⟨hy1, -⟩, -⟩, hy4⟩ := hy'
    show h y' = (A.chart k).symm (Φ ((B.chart j) y'))
    rw [hcoe]
    show h y' = (A.chart k).symm ((A.chart k) (h ((B.chart j).symm ((B.chart j) y'))))
    rw [(B.chart j).left_inv hy1, (A.chart k).left_inv hy4]
  · intro y' hy'
    rw [OpenPartialHomeomorph.restrOpen_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source] at hy'
    exact hy'.1.1.1

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

def LogNormSecLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (x : X) (y : X), IsSection A L s → y ∈ L.U x → s x y ≠ 0 →
      logNormSec L s y = Real.log ‖s x y‖ - L.φ x y

theorem logNormSecLocal : LogNormSecLocalStatement := by
  intro e X _ A L s x y hS hy hs
  unfold logNormSec
  rw [hS.2 y x y ⟨L.mem_U y, hy⟩, Real.log_mul (norm_ne_zero_iff.mpr hs) (Real.exp_pos _).ne',
    Real.log_exp]
  ring

theorem logNormSec_eq_indicator {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hS : IsSection A L s) {x p : X} (hp : p ∈ L.U x) :
    logNormSec L s p = Real.log ‖s x p‖ - L.φ x p + {q | s x q = 0}.indicator (L.φ x) p := by
  by_cases h0 : s x p = 0
  · unfold logNormSec
    rw [hS.2 p x p ⟨L.mem_U p, hp⟩, Set.indicator_apply,
      if_pos (show p ∈ {q | s x q = 0} from h0), h0]
    simp
  · rw [Set.indicator_apply, if_neg (show p ∉ {q | s x q = 0} from h0),
      logNormSecLocal A L s x p hS hp h0]
    ring

theorem prod_option_eq_prod_zpow {e r : ℕ} (σ : Fin r → Option (Fin e)) (m : Fin r → ℕ)
    (w : Fin e → ℂ) (g : Fin r → ℂ) (hg : ∀ k, g k = ∏ i, if σ k = some i then w i ^ m k else 1) :
    ∏ k, g k = ∏ i, w i ^ (((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ)) : ℤ) := by
  simp_rw [hg]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, zpow_natCast]

theorem logNormIntegrable_of (hLU : ReciprocityTheory.AnForm.A.LogUnitMonoLocIntStatement)
    (hD : LocDensContStatement) : LogNormIntegrableStatement := by
  intro e X _ _ _ A L s r m W hL hS hSNC Φ hΦ j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y0 hy0 => ?_) hK
  set c := A.chart j with hc
  have hy0t : y0 ∈ c.target := hKt hy0
  obtain ⟨ψ, hψc, hx0ψ, hψU, σ, -, -, u, hu, hu0, hsu⟩ := hSNC (c.symm y0)
  set x0 := c.symm y0 with hx0
  have hNo : IsOpen (c.target ∩ c.symm ⁻¹' ψ.source) := c.isOpen_inter_preimage_symm ψ.open_source
  have hy0N : y0 ∈ c.target ∩ c.symm ⁻¹' ψ.source := ⟨hy0t, hx0ψ⟩
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.mp hNo y0 hy0N
  set B := Metric.closedBall y0 (ε / 2) with hB
  have hBN : B ⊆ c.target ∩ c.symm ⁻¹' ψ.source :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεN
  have hBc : IsCompact B := isCompact_closedBall y0 (ε / 2)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩

  set V := ψ.target ∩ ψ.symm ⁻¹' c.source with hV
  have hVo : IsOpen V := ψ.isOpen_inter_preimage_symm c.open_source
  have hTinvA : AnalyticOnNhd ℂ (c ∘ ψ.symm) V := (hψc j).2
  have hTV : ∀ y ∈ c.target ∩ c.symm ⁻¹' ψ.source,
      ψ (c.symm y) ∈ V ∧ c (ψ.symm (ψ (c.symm y))) = y := by
    intro y hy
    refine ⟨⟨ψ.map_source hy.2, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, ψ.left_inv hy.2]
      exact c.map_target hy.1
    · rw [ψ.left_inv hy.2, c.right_inv hy.1]

  set m' : Fin e → ℤ :=
    fun i => ((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ) : ℤ) with hm'
  set G : (Fin e → ℂ) → ℝ := fun z => Real.log ‖u (ψ.symm z) * ∏ i, z i ^ m' i‖ with hG
  have hGloc : LocallyIntegrableOn G V := by
    refine hLU e m' V (fun z => u (ψ.symm z)) hVo ?_ (fun z hz => hu0 _ (ψ.map_target hz.1))
    intro z hz
    have hw : c (ψ.symm z) ∈ c.target ∩ c.symm ⁻¹' ψ.source := by
      refine ⟨c.map_source hz.2, ?_⟩
      simp only [Set.mem_preimage, c.left_inv hz.2]
      exact ψ.map_target hz.1
    have h1 : AnalyticAt ℂ ((u ∘ c.symm) ∘ (c ∘ ψ.symm)) z :=
      AnalyticAt.comp (g := u ∘ c.symm) (f := c ∘ ψ.symm) (hu j _ hw) (hTinvA z hz)
    refine (h1.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVo.mem_nhds hz] with w hw
    simp [Function.comp, c.left_inv hw.2]

  have hTc : ContinuousOn (fun y => ψ (c.symm y)) (c.target ∩ c.symm ⁻¹' ψ.source) :=
    ψ.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left) (fun y hy => hy.2)
  set C := (fun y => ψ (c.symm y)) '' B with hC
  have hCc : IsCompact C := hBc.image_of_continuousOn (hTc.mono hBN)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hCV : C ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hTV y (hBN hy)).1
  have hCB : (c ∘ ψ.symm) '' C = B := by
    rw [hC, Set.image_image]
    conv_rhs => rw [← Set.image_id B]
    exact Set.image_congr fun y hy => (hTV y (hBN hy)).2
  have hinj : Set.InjOn (c ∘ ψ.symm) C := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    simp only [Function.comp_apply] at h
    rw [(hTV y (hBN hy)).2, (hTV y' (hBN hy')).2] at h
    rw [h]
  have hderR : ∀ z ∈ V, DifferentiableAt ℝ (c ∘ ψ.symm) z := fun z hz =>
    (hTinvA z hz).differentiableAt.restrictScalars ℝ
  have hdetc : ContinuousOn (fun z => |(fderiv ℝ (c ∘ ψ.symm) z).det|) C := by
    have h1 : ContDiffOn ℝ 1 (c ∘ ψ.symm) V :=
      (hTinvA.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ
    exact ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (h1.continuousOn_fderiv_of_isOpen hVo le_rfl)).abs).mono hCV
  have hGT : IntegrableOn (fun y => G (ψ (c.symm y))) B := by
    have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      hCm (f := c ∘ ψ.symm) (f' := fun z => fderiv ℝ (c ∘ ψ.symm) z)
      (fun z hz => (hderR z (hCV hz)).hasFDerivAt.hasFDerivWithinAt) hinj
      (fun y => G (ψ (c.symm y)))
    rw [hCB] at hiff
    refine hiff.mpr ?_
    refine IntegrableOn.congr_fun
      ((hGloc.integrableOn_compact_subset hCV hCc).continuousOn_smul hdetc hCc) ?_ hCm
    rintro _ ⟨y, hy, rfl⟩
    have h := (hTV y (hBN hy)).2
    simp only [Function.comp_apply, h]

  have hdB : ContinuousOn (locDens A Φ j) B :=
    (hD A Φ hΦ j).mono (hBN.trans Set.inter_subset_left)
  have hsub : c.target ∩ c.symm ⁻¹' ψ.source ⊆ c.target ∩ c.symm ⁻¹' L.U x0 :=
    fun y hy => ⟨hy.1, hψU hy.2⟩
  have hφB : ContinuousOn (fun y => L.φ x0 (c.symm y)) B :=
    ((hL.1 x0 j).continuousOn.mono hsub).mono hBN
  have hsB : ContinuousOn (fun y => s x0 (c.symm y)) B :=
    ((hS.1 x0 j).continuousOn.mono hsub).mono hBN
  set Z := B ∩ (fun y => s x0 (c.symm y)) ⁻¹' {0} with hZ
  have hZm : MeasurableSet Z :=
    (hsB.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton).measurableSet
  have h1 : IntegrableOn (fun y => G (ψ (c.symm y)) * locDens A Φ j y) B :=
    hGT.mul_continuousOn hdB hBc
  have h2 : IntegrableOn (fun y => L.φ x0 (c.symm y) * locDens A Φ j y) B :=
    (hφB.mul hdB).integrableOn_compact hBc
  have h3 := h2.indicator hZm
  refine IntegrableOn.congr_fun (Integrable.add (Integrable.sub h1 h2) h3) ?_ hBm
  intro y hy
  have hyN := hBN hy
  have hp : c.symm y ∈ L.U x0 := hψU hyN.2
  have hprod : ∀ w : Fin e → ℂ, (∏ k, (match σ k with
      | some i => w i ^ m k
      | none => 1)) = ∏ i, w i ^ m' i := by
    intro w
    apply prod_option_eq_prod_zpow
    intro k
    split <;> simp_all
  have hlog : Real.log ‖s x0 (c.symm y)‖ = G (ψ (c.symm y)) := by
    show _ = Real.log ‖u (ψ.symm (ψ (c.symm y))) * ∏ i, (ψ (c.symm y)) i ^ m' i‖
    rw [ψ.left_inv hyN.2, hsu _ hyN.2]
    exact congrArg (fun t => Real.log ‖u (c.symm y) * t‖) (hprod _)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [logNormSec_eq_indicator hS hp, hlog]
  by_cases h0 : s x0 (c.symm y) = 0
  · rw [Set.indicator_of_mem (show y ∈ Z from ⟨hy, h0⟩),
      Set.indicator_of_mem (show c.symm y ∈ {q | s x0 q = 0} from h0)]
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Z from fun h => h0 h.2),
      Set.indicator_of_notMem (show c.symm y ∉ {q | s x0 q = 0} from h0)]
    ring

theorem logNormIntegrable : LogNormIntegrableStatement :=
  logNormIntegrable_of ReciprocityTheory.AnForm.A.logUnitMonoLocInt_thm locDensCont

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    ContDiffAt ℝ 2 (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  have h := hP.1 ((A.chart j).symm y) j
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)).mem_nhds ⟨hy, P.mem_U _⟩
  exact (h.contDiffAt hmem).of_le (by norm_cast)

theorem locDens_cons (A : FinHolAtlas (e + 1) X) (P : LocPot X) (Φ : Fin e → LocPot X)
    (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) j y = ((e + 1).factorial : ℝ) * (2 / Real.pi) ^ (e + 1) *
      (mdisc (Fin.cons (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
        (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) :
          Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)).re := by
  unfold locDens maDens
  congr 3
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

theorem locDens_cons_rsmul (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by
  rw [locDens_cons, locDens_cons]
  have : (fun y' => (P.rsmul c).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => c * P.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_const_mul', mdisc_cons_smul, Complex.re_ofReal_mul]
  ring

theorem locDens_cons_add (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by
  rw [locDens_cons, locDens_cons, locDens_cons]
  have : (fun y' => (P + Q).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y') +
        Q.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_add' _ _ _ (potential_contDiffAt A P hP j hy) (potential_contDiffAt A Q hQ j hy),
    mdisc_cons_add, Complex.add_re]
  ring

theorem locDens_nonneg (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hψ : ∀ i, IsPsh A (Φ i)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  unfold locDens
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  exact hessC_posSemidef _ _ (potential_contDiffAt A (Φ k) (hΦ k) j hy)
    fun w => hψ k ((A.chart j).symm y) j y ⟨hy, (Φ k).mem_U _⟩ w

theorem integrableOn_weight [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  set K := (A.chart j) '' tsupport (P.χ j)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : K ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    (hg j K hKt hKc).continuousOn_mul (hχc.mono hKt) hKc
  have h2 := h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet (by
    rintro y ⟨hy, hyK⟩
    have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
      hyK ⟨_, h, (A.chart j).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this])
  simpa only [mul_assoc] using h2

end Chart

private theorem mdisc_comp_perm_potential {D : ℕ} (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    ReciprocityTheory.AnForm.mdisc (B ∘ σ) = ReciprocityTheory.AnForm.mdisc B := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]

theorem mIntSymm : MIntSymmStatement := by
  intro e X _ A Φ σ g
  have hloc : ∀ j y, locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
    intro j y
    unfold locDens maDens
    congr 2
    exact mdisc_comp_perm_potential (fun k => ReciprocityTheory.AnForm.hessC
      (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
  unfold mInt integralWith
  simp only [hloc]

theorem mIntAdd : MIntAddStatement := by
  intro e X _ _ _ A P Q Φ hP hQ hΦ g hgP hgQ
  unfold mInt integralWith
  split_ifs with h
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some (Fin.cons P Φ) g hgP j
    have i2 := integrableOn_weight A h.some (Fin.cons Q Φ) g hgQ j
    rw [← integral_add i1 i2]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    show _ = _ + _
    rw [locDens_cons_add A P Q Φ hP hQ j hy]
    ring
  · simp

theorem mIntRsmul : MIntRsmulStatement := by
  intro e X _ A c P Φ hP hΦ g
  unfold mInt integralWith
  split_ifs with h
  · simp only [locDens_cons_rsmul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · simp

theorem mIntZsmul : MIntZsmulStatement := by
  intro e X _ A m P Φ hP hΦ g
  exact mIntRsmul A (m : ℝ) P Φ hP hΦ g

theorem mIntLinear : MIntLinearStatement := by
  intro e X _ _ _ A Φ hΦ c g g' hg hg'
  unfold mInt integralWith
  split_ifs with h
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some Φ g hg j
    have i2 := integrableOn_weight A h.some Φ g' hg' j
    rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
    congr 1
    funext y
    ring
  · simp

theorem mIntNonneg : MIntNonnegStatement := by
  intro e X _ A Φ hΦ hψ g hg
  unfold mInt integralWith
  split_ifs with h
  · exact Finset.sum_nonneg fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet
      fun y hy => mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg _)) (locDens_nonneg A Φ hΦ hψ j hy)
  · exact le_rfl

end

end ReciprocityTheory.AnForm.M
end

