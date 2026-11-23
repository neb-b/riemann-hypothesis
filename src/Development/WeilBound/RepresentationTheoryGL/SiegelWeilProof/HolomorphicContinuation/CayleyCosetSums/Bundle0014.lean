module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmCore
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ExpLie : Prop := ∀ (n : ℕ) (x Z : M2 n) (t : ℝ), InG x →
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))

theorem lift_mR' (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  unfold lift
  rw [dite_eq_left h]
  congr 1
  ext : 2
  rfl

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x :=
  (Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

theorem rC_const_mul (Z : M2 n) (a : ℂ) (F : M2 n → ℂ) (x : M2 n) :
    rC Z (fun x => a * F x) x = a * rC Z F x := by
  unfold rC
  rw [deriv_const_mul_field', deriv_const_mul_field']
  ring

theorem rC_zero (Z : M2 n) (x : M2 n) : rC Z (fun _ => (0 : ℂ)) x = 0 := by
  unfold rC
  simp

def Van (j : ℕ) (h : ℂ → ℂ) (s : ℂ) : Prop := ∀ k ≤ j, iteratedDeriv k h s = 0

theorem van_mul {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : Van j h s) : Van j (fun z => q z * h z) s := by
  intro k hk
  rw [leib hU k q h hq hh s hs]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hv (k - i) (by omega)]
  simp

theorem van_sum {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {ι : Type} (S : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ l, DifferentiableOn ℂ (h l) U) {j : ℕ} (hv : ∀ l, Van j (h l) s) : Van j (fun z => ∑ l ∈ S, h l z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => intro k _; simp
  | insert a S ha ih =>
    intro k hk
    have e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z) := by
      funext z; simp [Finset.sum_insert ha]
    have hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U := by
      exact DifferentiableOn.fun_sum (fun l _ => hd l)
    rw [e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top)
      ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]

theorem iter_mul_low {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : ∀ i < j, iteratedDeriv i h s = 0) :
    iteratedDeriv j (fun z => q z * h z) s = q s * iteratedDeriv j h s ∧
      ∀ i < j, iteratedDeriv i (fun z => q z * h z) s = 0 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [leib hU j q h hq hh s hs, Finset.sum_eq_single 0]
    · simp
    · intro b hbm hb
      have := Finset.mem_range.1 hbm
      rw [hv (j - b) (by omega)]
      simp
    · intro h0; exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
  · rw [leib hU i q h hq hh s hs]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b < i + 1 := Finset.mem_range.1 hb
    rw [hv (i - b) (by omega)]
    simp

theorem asmH_of (hF : FarId) (hS : SmoothX) (hT : TopHol) (hR : RcCongr) (hE : ExpLie) : AsmH := by
  intro hLT hSec hCR
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g
  have hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t := ⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩
  haveI : CompactSpace (KR n) := kRCpt n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩

  obtain ⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩ := hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g
  set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ
  set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ

  have hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0 := by
    intro y
    have hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y) := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hΦG z hz y
    have hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0 := fun i hi => hlow i hi (g * ι y)
    obtain ⟨h1, h2⟩ := iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev j, h1]
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]
  have hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0 := by
    intro i hi x' hx'
    have := (hΨG (toGR x' hx')).2 i hi
    rwa [mR_toGR] at this

  have hιKc : Continuous (ιK n) := by
    unfold ιK
    exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨toGR x hx.1, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2

  obtain ⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0
  obtain ⟨-, hK⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀
  refine hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_
  · intro y
    simp only [(hΨG y).1]
    field_simp
  · intro y k hk
    have hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hK z hz g y k hk
    simp only [hφ]
    rw [iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]
  · intro y Q
    rw [rC_const_mul]
    suffices h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]
    obtain ⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q
    obtain ⟨⟨t', hfarId⟩, -⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid
    set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL
    set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef
    set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef
    have hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ =
        tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y) := fun l =>
      hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y
    have hDs : Differentiable ℂ fun z => D (z - s₀) := hDd.comp (differentiable_id.sub_const s₀)
    have hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀) := fun l => (hMd l).comp (differentiable_id.sub_const s₀)
    have hLd : DifferentiableOn ℂ L U := (hΦrC Q y).1
    have hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U :=
      DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1
    have hRd : DifferentiableOn ℂ R U := hcd.mul hsumd

    have hEq : EqOn (fun z => D (z - s₀) * L z) R U := by
      obtain ⟨σ, hσ⟩ := hRU.1
      set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁
      have hz₁U : z₁ ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))
      refine (hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq
        (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_
      have hopen : IsOpen {z : ℂ | max t' σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz
      have hzt : t' < z.re := lt_of_le_of_lt (le_max_left _ _) hz
      have hzU : z ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))
      have hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y) := by
        refine hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1)
          (fun s => (hE n (mR y) (lowQ Q) s y.2).2)
        have e1 := hΦG z hzU (toGR x' hx')
        rw [mR_toGR] at e1
        have e2 := lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')
        rw [mR_toGR] at e2
        simp only [resG]
        rw [e1, e2]
      show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z
      rw [hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]
    have hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hEq hz
    have hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0 := by
      intro i hi
      rw [(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx')
        (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]
    obtain ⟨hL1, -⟩ := iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow
    have hnb : ∀ t, InG (nU (herm t) : M2 n) := fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq
    have hRv : Van j R s₀ := by
      apply van_mul hU hs0 hcd hsumd
      apply van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z)
        (fun l => (hMs l).differentiableOn.mul (hTH l).1)
      intro l
      apply van_mul hU hs0 (hMs l).differentiableOn (hTH l).1
      intro k hk
      rw [(hTH l).2 k]
      rcases lt_or_eq_of_le hk with hk' | hkj
      · have hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0 := by
          funext x
          unfold resG lift
          split_ifs <;> simp [hlow k hk']
        rw [hz0]
        simp [tOp]
      · subst hkj
        have hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
            (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0 := by
          intro k'
          let nb : (Fin n → Fin n → ℝ) → GR n := fun t => toGR (nU (herm t)) (hnb t)
          have key := hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1)
            (toGR (b l) (hab l).2)
          refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key
          show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
              (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _
          simp only [resG]
          rw [lift_mR']
        unfold tOp
        simp_rw [hin, mul_zero, integral_zero]
    have hRj := hRv j le_rfl
    have h0 : D 0 * iteratedDeriv j L s₀ = 0 := by
      have h1 := iteratedDeriv_eq_of_eventuallyEq hev j
      rw [hL1, hRj, sub_self] at h1
      exact h1
    have hLj : iteratedDeriv j L s₀ = 0 := (mul_eq_zero.1 h0).resolve_left hD0
    rw [(hΦrC Q y).2 j] at hLj
    exact hLj

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CRSecA
section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CRSec

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mn (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cT {ι : Type} [Fintype ι] : Matrix ι ι ℂ →L[ℝ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Mᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r M => by
        ext i j
        simp [conjTranspose_apply, Complex.conj_ofReal] }

theorem contDiffAt_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {x : E} {k : WithTop ℕ∞} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ContDiffAt ℝ k (fun y => f y * g y) x := by
  have hf' : ∀ i j, ContDiffAt ℝ k (fun y => f y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hf i) j
  have hg' : ∀ i j, ContDiffAt ℝ k (fun y => g y i j) x := fun i j =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hg i) j
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hf' i l).mul (hg' l j)

theorem contDiff_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]
    {f g : E → Matrix ι ι ℂ} {k : WithTop ℕ∞} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun y => f y * g y) :=
  contDiff_iff_contDiffAt.2 fun x => contDiffAt_mul' hf.contDiffAt hg.contDiffAt

private theorem hasDerivAt_exp_smul_apply_zero {ι : Type} [Fintype ι] (M0 : Matrix ι ι ℂ) (a b : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M a b) M0 := by
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) b).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ι → ℂ) a)).analyticAt M0

private theorem analyticAt_det_of_analyticAt_entries {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) (hF : ∀ a b, AnalyticAt ℂ (fun M => F M a b) M0) :
    AnalyticAt ℂ (fun M => (F M).det) M0 := by
  have e : (fun M => (F M).det) =
      ∑ σ : Equiv.Perm ι, fun M => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ l, F M (σ l) l := by
    ext M
    simp [Matrix.det_apply, Finset.sum_apply, Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine Finset.analyticAt_sum _ fun σ _ => analyticAt_const.mul ?_
  have h := Finset.analyticAt_prod (𝕜 := ℂ) Finset.univ (f := fun l M => F M (σ l) l) (c := M0)
    fun l _ => hF _ _
  have e2 : (∏ l : ι, fun M : Matrix ι ι ℂ => F M (σ l) l) = fun M => ∏ l, F M (σ l) l := by
    ext M
    simp [Finset.prod_apply]
  rwa [e2] at h

theorem analyticAt_adj {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (i j : ι) :
    AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.adjugate i j) M0 := by
  simp only [Matrix.adjugate_apply]
  refine analyticAt_det_of_analyticAt_entries M0 (fun M => M.updateRow j (Pi.single i 1)) fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne h]
    exact hasDerivAt_exp_smul_apply_zero M0 a b

theorem contDiffAt_inv {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) (h : M0.det ≠ 0)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => M⁻¹) M0 := by
  have hd : AnalyticAt ℂ (fun M : Matrix ι ι ℂ => M.det) M0 :=
    analyticAt_det_of_analyticAt_entries M0 (fun M => M) fun a b => hasDerivAt_exp_smul_apply_zero M0 a b
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  have key : ContDiffAt ℝ k (fun M : Matrix ι ι ℂ => (M.det)⁻¹ * M.adjugate i j) M0 :=
    ((hd.inv h).mul (analyticAt_adj M0 i j)).contDiffAt.restrict_scalars ℝ
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun M => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

theorem contDiffAt_fromBlocks {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C D : E → Mn n} {x : E} {k : WithTop ℕ∞} (hA : ContDiffAt ℝ k A x) (hB : ContDiffAt ℝ k B x)
    (hC : ContDiffAt ℝ k C x) (hD : ContDiffAt ℝ k D x) :
    ContDiffAt ℝ k (fun y => (fromBlocks (A y) (B y) (C y) (D y) : M2 n)) x := by
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  rcases i with i | i <;> rcases j with j | j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hA i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hB i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hC i) j
  · exact contDiffAt_pi.1 (contDiffAt_pi.1 hD i) j

def reP (V : Mn n) : Mn n := (1 / 2 : ℂ) • (V + Vᴴ)

def imaginary (V : Mn n) : Mn n := (-(Complex.I / 2)) • (V - Vᴴ)

theorem reP_herm (V : Mn n) : (reP V)ᴴ = reP V := by
  ext i j
  simp [reP]
  ring

theorem imaginaryPart_isHermitian (V : Mn n) : (imaginary V)ᴴ = imaginary V := by
  ext i j
  simp [imaginary]
  ring

theorem reP_add_imP (V : Mn n) : reP V + Complex.I • imaginary V = V := by
  ext i j
  simp only [reP, imaginary, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem imaginaryPart_of_isHermitian {V : Mn n} (h : Vᴴ = V) : imaginary V = 0 := by simp [imaginary, h]

theorem reP_of_herm {V : Mn n} (h : Vᴴ = V) : reP V = V := by
  rw [reP, h, ← two_smul ℂ V, smul_smul]
  norm_num

def fM (a0 : Mn n) (V : Mn n) : Mn n := reP V + Complex.I • (a0 * (1 + imaginary V) * (1 + imaginary V) * a0ᴴ)

end PositivityTheory.Rg.Sw.HSt.CRSec
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ConjImaginaryPartFixed
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, JJ_mul_JJ, neg_neg]

theorem JJ_conjT : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp [sig, JJ_inv]

theorem sig_sig (X : M2 n) : sig (sig X) = X := by
  have h1 : ∀ B : M2 n, JJ n * (JJ n * B) = -B := by
    intro B
    rw [← Matrix.mul_assoc, JJ_mul_JJ, Matrix.neg_mul, Matrix.one_mul]
  rw [sig_eq, sig_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, JJ_conjT, Matrix.mul_assoc,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, h1, JJ_mul_JJ, Matrix.mul_one]

theorem sig_add (X Y : M2 n) : sig (X + Y) = sig X + sig Y := by
  simp [sig_eq, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sig_smul (c : ℂ) (X : M2 n) : sig (c • X) = (starRingEnd ℂ c) • sig X := by
  simp only [sig_eq, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.star_def]

theorem sig_sub (X Y : M2 n) : sig (X - Y) = sig X - sig Y := by
  simp [sig_eq, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem conj_real_part_fixed (Z : M2 n) : sig (Z1 Z) = Z1 Z := by
  have hc : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [Z1, sig_smul, sig_add, sig_sig, hc, add_comm]

theorem conj_imaginary_part_fixed (Z : M2 n) : sig (Z2 Z) = Z2 Z := by
  have hc : starRingEnd ℂ (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    field_simp
  rw [Z2, sig_smul, sig_sub, sig_sig, hc, neg_smul, ← smul_neg, neg_sub]

theorem real_add_imaginary_part (Z : M2 n) : Z1 Z + Complex.I • Z2 Z = Z := by
  have hc : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  simp only [Z1, Z2, smul_smul, hc]
  module

theorem inG_cE {A : M2 n} (hA : sig A = A) (s : ℝ) : InG (II.cE A s) := by
  have hJJ := JJ_mul_JJ (n := n)
  let U : (M2 n)ˣ := ⟨JJ n, -JJ n, by rw [Matrix.mul_neg, hJJ, neg_neg],
    by rw [Matrix.neg_mul, hJJ, neg_neg]⟩
  have hAh : Aᴴ = JJ n * A * JJ n := by
    have h := hA
    rw [sig_eq] at h
    calc Aᴴ = (JJ n * JJ n) * Aᴴ * (JJ n * JJ n) := by
          rw [hJJ, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
      _ = JJ n * (JJ n * Aᴴ * JJ n) * JJ n := by simp only [Matrix.mul_assoc]
      _ = JJ n * A * JJ n := by rw [h]
  have hB : (s • A)ᴴ = (U : M2 n) * (-(s • A)) * ((U⁻¹ : (M2 n)ˣ) : M2 n) := by
    show (s • A)ᴴ = JJ n * (-(s • A)) * (-JJ n)
    rw [conjTranspose_smul, star_trivial, hAh]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul]
  unfold InG II.cE
  rw [← Matrix.exp_conjTranspose, hB, Matrix.exp_units_conj]
  show JJ n * NormedSpace.exp (-(s • A)) * (-JJ n) * JJ n * NormedSpace.exp (s • A) = JJ n
  rw [Matrix.mul_assoc (JJ n * _) (-JJ n) (JJ n), Matrix.neg_mul, hJJ, neg_neg, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute (-(s • A)) (s • A) ((Commute.refl (s • A)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveGR
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def dir1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def dir2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

def CurveGR : Prop :=
  ∀ (n : ℕ) (Z : M2 n) (b : Bool), ∃ γ : ℝ → GR n, Continuous γ ∧ γ 0 = 1 ∧
    (∀ s t, γ (s + t) = γ s * γ t) ∧
    ∀ t, mR (γ t) = NormedSpace.exp ((t : ℂ) • (if b then dir1 Z else dir2 Z))

def FzDer : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (w : ℂ) (Z : M2 n) (b : Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GR n,
    ∃ R : ℂ, HasDerivAt (fun s : ℝ => fz m e w (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) R 0 ∧
      ‖R‖ ≤ C * ‖fz m e w (mR y)‖

end PositivityTheory.Rg.Sw.HSt
end
end

