module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceLevi

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M

noncomputable section

structure EnergyStep.Data {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (n + 1) X)
    (Om : KaehlerForm A) where

  w : X → ℝ

  v : X → ℝ

  f : Fin n → X → ℝ

  M : ℝ
  w_smooth : A.Smooth w
  w_psh : IsPsh A (Om.pot + LocPot.ofFun w)
  v_smooth : A.Smooth v
  v_nonpos : ∀ x, v x ≤ 0
  le_v : ∀ x, -M ≤ v x
  f_smooth : ∀ i, A.Smooth (f i)
  f_psh : ∀ i, IsPsh A (Om.pot + LocPot.ofFun (f i))

def EnergyStep.Data.T {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas (n + 1) X}
    {Om : KaehlerForm A} (d : EnergyStep.Data A Om) : Fin n → LocPot X :=
  fun i => Om.pot + LocPot.ofFun (d.f i)

def EnergyStep.Statement : Prop :=
  ∀ {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (d : EnergyStep.Data A Om),
    mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -d.w x) ≤
      mInt A (Fin.cons Om.pot d.T) (fun x => -d.w x) + d.M * Om.vol

theorem KaehlerForm.isPsh {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    (Om : KaehlerForm A) : IsPsh A Om.pot := by
  intro x j y hy z
  by_cases hz : z = 0
  · subst hz
    simp [levi]
  · exact (Om.pos x j y hy z hz).le

theorem levi_add_const {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (c : ℝ) (y z : ι → ℂ) :
    levi (fun y' => g y' + c) y z = levi g y z := by
  have h : fderiv ℝ (fun y' => g y' + c) = fderiv ℝ g := funext fun y' => fderiv_add_const c
  unfold levi
  rw [h]

theorem isPsh_add_const {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {P : LocPot X} (hP : IsPsh A P) (c : ℝ) : IsPsh A (P + LocPot.ofFun fun _ => c) := by
  intro x j y hy z
  have h : (P + LocPot.ofFun fun _ => c).φ x ∘ (A.chart j).symm =
      fun y' => (P.φ x ∘ (A.chart j).symm) y' + c := rfl
  rw [h, levi_add_const]
  exact hP x j y ⟨hy.1, hy.2.1⟩ z

theorem mInt_neg {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas n X) (Φ : Fin n → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ)
    (hg : MIntegrable A Φ g) : mInt A Φ (fun x => -g x) = -mInt A Φ g := by
  have h := mIntLinear A Φ hΦ (-1) g (fun _ => 0) hg (mIntegrableCont A Φ hΦ _ continuous_const)
  simp only [neg_one_mul, add_zero, st_mInt_zero] at h
  exact h

theorem EnergyStep.proof : EnergyStep.Statement := by
  intro n X _ _ _ A Om d
  have hT : ∀ i, IsPotential A (d.T i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (d.f_smooth i))
  have hcons : ∀ P, IsPotential A P → ∀ i, IsPotential A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · simpa using hT i
  have hw := isPotential_ofFun A _ d.w_smooth
  have hv := isPotential_ofFun A _ d.v_smooth
  have hOw := isPotentialAdd A _ _ Om.isPot hw
  have cw := st_smooth_continuous A d.w_smooth
  have cv := st_smooth_continuous A d.v_smooth
  have int : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g →
      MIntegrable A (Fin.cons P d.T) g := fun P hP g hg => mIntegrableCont A _ (hcons P hP) g hg

  have h1 := mIntAdd A Om.pot (LocPot.ofFun d.v) d.T Om.isPot hv hT (fun x => -d.w x)
    (int _ Om.isPot _ cw.neg) (int _ hv _ cw.neg)
  have h2 := mInt_neg A _ (hcons _ hv) d.w (int _ hv _ cw)
  have h3 := (byPartsSymm A d.v d.w d.v_smooth d.w_smooth d.T hT).symm
  have h4 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT d.v
    (int _ Om.isPot _ cv) (int _ hw _ cv)
  have hpsh : ∀ P, IsPsh A P → ∀ i, IsPsh A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · exact d.f_psh i

  have h5 := mIntNonneg A _ (hcons _ Om.isPot) (hpsh _ Om.isPsh) (fun x => -d.v x)
    fun x => by have := d.v_nonpos x; linarith
  rw [mInt_neg A _ (hcons _ Om.isPot) d.v (int _ Om.isPot _ cv)] at h5

  have h6 := mIntLinear A _ (hcons _ hOw) d.M (fun _ => 1) d.v (int _ hOw _ continuous_const)
    (int _ hOw _ cv)
  beta_reduce at h6
  have h7 := mIntNonneg A _ (hcons _ hOw) (hpsh _ d.w_psh) (fun x => d.M * 1 + d.v x)
    fun x => by have := d.le_v x; linarith
  rw [h6] at h7

  have h8 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT (fun _ => 1)
    (int _ Om.isPot _ continuous_const) (int _ hw _ continuous_const)
  have h9 := stokes A d.w d.w_smooth d.T hT
  have h10 := massIndep A (fun _ => Om.pot) (Fin.cons (fun _ => 0) d.f) (fun _ => Om.isPot)
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using st_smooth_const A 0
      · simpa using d.f_smooth i)
  have h11 : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun ((Fin.cons (fun _ => 0) d.f : Fin (n + 1) → X → ℝ) i))
        (fun _ => 1) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      show Om.pot.φ x y = Om.pot.φ x y + 0
      ring
    · rfl
  have hV : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = Om.vol := by
    rw [h11, h10]
    rfl
  rw [h8, h9, add_zero, hV] at h7
  rw [h1, h2, h3]
  linarith [h4, h5, h7]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplaceKappa
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC logNormSec)

noncomputable section

namespace GreenMassReplace

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem secNorm_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) :
    secNorm L s y = ‖s x y‖ * Real.exp (-L.φ x y) :=
  hS.2 y x y ⟨L.mem_U y, hy⟩

def logNormSqAdd (L : LocPot X) (s : X → X → ℂ) (ε : ℝ) (y : X) : ℝ :=
  Real.log (secNorm L s y ^ 2 + ε)

theorem logNormSqAdd_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    logNormSqAdd L s ε y =
      Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) - 2 * L.φ x y := by
  unfold logNormSqAdd
  rw [secNorm_eq_local hS hy]
  have hP : 0 < ‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y) := by positivity
  have h1 : Real.exp (-L.φ x y) ^ 2 = Real.exp (-(2 * L.φ x y)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h2 : Real.exp (2 * L.φ x y) * Real.exp (-(2 * L.φ x y)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : (‖s x y‖ * Real.exp (-L.φ x y)) ^ 2 + ε =
      (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) * Real.exp (-(2 * L.φ x y)) := by
    rw [mul_pow, h1, add_mul, mul_assoc ε, h2, mul_one]
  rw [h3, Real.log_mul hP.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem kappaEp_φ_eq_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) {ε : ℝ} (hε : 0 < ε) :
    (kappaEp L s ε).φ x y = Real.log (‖s x y‖ ^ 2 + ε * Real.exp (2 * L.φ x y)) := by
  have h := logNormSqAdd_eq_local hS hy hε
  unfold logNormSqAdd at h
  show 2 * L.φ x y + Real.log (secNorm L s y ^ 2 + ε) = _
  rw [h]
  ring

theorem smooth_logNormSqAdd {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    A.Smooth (logNormSqAdd L s ε) := by
  intro j y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hyt : y ∈ (A.chart j).target := hy.1
  set q := (A.chart j).symm y with hq
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q) :=
    (A.chart j).isOpen_inter_preimage_symm (L.isOpen_U q)
  have hyO : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U q := ⟨hyt, L.mem_U q⟩
  have heq : (logNormSqAdd L s ε ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun z =>
      Real.log (‖(s q ∘ (A.chart j).symm) z‖ ^ 2 +
        ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) z)) - 2 * (L.φ q ∘ (A.chart j).symm) z := by
    filter_upwards [hO.mem_nhds hyO] with z hz
    exact logNormSqAdd_eq_local hS hz.2 hε
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hSc : ContDiffAt ℝ ∞ (s q ∘ (A.chart j).symm) y :=
    ((hS.1 q j y hyO).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hΦ : ContDiffAt ℝ ∞ (L.φ q ∘ (A.chart j).symm) y :=
    ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A L hL q j hyO
  refine ((((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
    (contDiffAt_const.mul (contDiffAt_const.mul hΦ).exp)).log ?_).sub (contDiffAt_const.mul hΦ)
  exact (by positivity : (0 : ℝ) < ‖(s q ∘ (A.chart j).symm) y‖ ^ 2 +
    ε * Real.exp (2 * (L.φ q ∘ (A.chart j).symm) y)).ne'

theorem isPotential_kappaEp {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hL : IsPotential A L) (hS : IsSection A L s) {ε : ℝ} (hε : 0 < ε) :
    IsPotential A (kappaEp L s ε) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ (ReciprocityTheory.AnForm.M.isPotentialRsmul A 2 L hL)
    (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (smooth_logNormSqAdd hL hS hε))

theorem kappaEp_formNonneg [CompactSpace X] {A : FinHolAtlas e X} (Om : KaehlerForm A)
    {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L) (hS : IsSection A L s) :
    ∃ Cκ : ℝ, 0 ≤ Cκ ∧ ∀ ε, 0 < ε → FormNonneg A Set.univ (kappaEp L s ε + Om.pot.rsmul Cκ) := by
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A isCompact_univ L Om.pot hL Om.isPot Om.pos
  refine ⟨2 * M, by positivity, fun ε hε x k y hy w => ?_⟩
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyL : (A.chart k).symm y ∈ L.U x := hy.2.2.1.1
  have hyΩ : (A.chart k).symm y ∈ Om.pot.U x := hy.2.2.2
  set S := s x ∘ (A.chart k).symm with hSdef
  set Φ := L.φ x ∘ (A.chart k).symm with hΦdef
  set Ψ := Om.pot.φ x ∘ (A.chart k).symm with hΨdef
  have hO : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' L.U x) :=
    (A.chart k).isOpen_inter_preimage_symm (L.isOpen_U x)
  have hSa : AnalyticAt ℂ S y := hS.1 x k y ⟨hyt, hyL⟩
  have hΦ2 : ContDiffAt ℝ 2 Φ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two hL x k hyt hyL
  have hΨ2 : ContDiffAt ℝ 2 Ψ y := ReciprocityTheory.AnForm.M.pot_contDiffAt_two Om.isPot x k hyt hyΩ
  have heq : (kappaEp L s ε).φ x ∘ (A.chart k).symm =ᶠ[𝓝 y]
      fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z)) := by
    filter_upwards [hO.mem_nhds ⟨hyt, hyL⟩] with z hz
    exact kappaEp_φ_eq_local hS hz.2 hε
  have hK2 : ContDiffAt ℝ 2 (fun z => Real.log (‖S z‖ ^ 2 + ε * Real.exp (2 * Φ z))) y := by
    have hSc : ContDiffAt ℝ 2 S y := (hSa.restrictScalars (𝕜 := ℝ)).contDiffAt
    refine (((contDiff_norm_sq ℝ).contDiffAt.comp y hSc).add
      (contDiffAt_const.mul (contDiffAt_const.mul hΦ2).exp)).log ?_
    exact (by positivity : (0 : ℝ) < ‖S y‖ ^ 2 + ε * Real.exp (2 * Φ y)).ne'
  have hκ2 := hK2.congr_of_eventuallyEq heq
  have hsum : (kappaEp L s ε + Om.pot.rsmul (2 * M)).φ x ∘ (A.chart k).symm =
      fun z => ((kappaEp L s ε).φ x ∘ (A.chart k).symm) z + (2 * M) * Ψ z := rfl
  rw [hsum, levi_add_smul (2 * M) hκ2 hΨ2 w, levi_congr heq w]
  have hA := levi_log_normSq_add_exp hSa hΦ2 hε w
  have hB := hM x k y ⟨hyt, hyL, hyΩ⟩ w
  have hΨnn : 0 ≤ levi Ψ y w := by
    rcases eq_or_ne w 0 with h0 | h0
    · rw [h0, ReciprocityTheory.AnForm.levi_zero]
    · exact (Om.pos x k y ⟨hyt, hyΩ⟩ w h0).le
  set E := ε * Real.exp (2 * Φ y) with hE
  have hE0 : 0 < E := mul_pos hε (Real.exp_pos _)
  have hh : 0 < ‖S y‖ ^ 2 + E := by positivity
  set c := 2 * E / (‖S y‖ ^ 2 + E) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ≤ 2 := by
    rw [hc, div_le_iff₀ hh]
    nlinarith [sq_nonneg ‖S y‖]
  have hl := (abs_le.mp hB).1
  have hMΨ : 0 ≤ M * levi Ψ y w := mul_nonneg hM0 hΨnn
  nlinarith

def zeroSet (s : X → X → ℂ) : Set X := {y | s y y = 0}

theorem zero_iff_local {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s y y = 0 ↔ s x y = 0 := by
  have h := hS.2 y x y ⟨L.mem_U y, hy⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (Real.exp_pos _).ne')

theorem zeroSet_analytic {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) : A.IsAnalyticSubset (zeroSet s) := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext y
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_const]
  constructor
  · rintro ⟨h0, hy⟩
    exact ⟨hy, (zero_iff_local hS hy).1 h0⟩
  · rintro ⟨hy, h0⟩
    exact ⟨(zero_iff_local hS hy).2 h0, hy⟩

theorem interior_zeroSet {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ}
    (hS : IsSection A L s) {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (hsnc : IsSNC A L s m W) : interior (zeroSet s) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ψ, -, hxψ, hψL, σ, -, -, u, -, hu0, hprod⟩ := hsnc x
  have hOimg : IsOpen (ψ '' (ψ.source ∩ interior (zeroSet s))) :=
    ψ.isOpen_image_source_inter isOpen_interior
  have hne : (ψ '' (ψ.source ∩ interior (zeroSet s))).Nonempty := ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩
  have hsub : ψ '' (ψ.source ∩ interior (zeroSet s)) ⊆ ⋃ i, {z : Fin e → ℂ | z i = 0} := by
    rintro _ ⟨y, ⟨hyψ, hyZ⟩, rfl⟩
    have hz : y ∈ zeroSet s := interior_subset hyZ
    have h0 : s x y = 0 := (zero_iff_local hS (hψL hyψ)).1 hz
    rw [hprod y hyψ] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (hu0 y hyψ)
    · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
      revert hk
      cases hσ : σ k with
      | none => intro hk; exact absurd hk one_ne_zero
      | some i => intro hk; exact Set.mem_iUnion.2 ⟨i, eq_zero_of_pow_eq_zero hk⟩
  have hpos := hOimg.measure_pos volume hne
  have hnull : volume (⋃ i, {z : Fin e → ℂ | z i = 0}) = 0 :=
    measure_iUnion_null fun i => ReciprocityTheory.AnForm.M.PLAux.volume_coord_eq_zero i
  exact hpos.ne' (measure_mono_null hsub hnull)

theorem greenEp_eq_off (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) {y : X}
    (hy : y ∉ zeroSet s) :
    greenEp L s ε y = -2 * logNormSec L s y + logNormSqAdd L s ε y := by
  have hn : 0 < secNorm L s y := mul_pos (norm_pos_iff.2 hy) (Real.exp_pos _)
  have h1 : 1 + ε / secNorm L s y ^ 2 = (secNorm L s y ^ 2 + ε) / secNorm L s y ^ 2 := by
    field_simp
  unfold greenEp logNormSqAdd
  rw [h1, Real.log_div (by positivity) (by positivity), Real.log_pow]
  show _ = -2 * Real.log (secNorm L s y) + _
  push_cast
  ring

theorem greenEp_nonneg (L : LocPot X) (s : X → X → ℂ) {ε : ℝ} (hε : 0 < ε) (y : X) :
    0 ≤ greenEp L s ε y :=
  Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hε.le (sq_nonneg _)))

end GreenMassReplace

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

