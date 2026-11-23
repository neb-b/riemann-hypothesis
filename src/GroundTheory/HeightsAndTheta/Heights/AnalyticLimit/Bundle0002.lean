module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoDens
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def ListMonoDens.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (Om : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) →
    IsPotential A Om → (∀ i, A.SmoothOn Yo (u i)) → (∀ i, LeviLe A Set.univ 1 (th i) 1 Om) →
    (∀ i, FormNonneg A Yo (potForm (th i) (u i))) →
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y ∧
        locDens A (fun i => potForm (th i) (u i)) j y ≤ locDens A (fun i => potForm Om (u i)) j y

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoRaise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def ListMonoRaise.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th Om : LocPot X)
    (u : X → ℝ), IsOpen Yo → IsPotential A th → IsPotential A Om → A.SmoothOn Yo u →
    LeviLe A Set.univ 1 th 1 Om → FormNonneg A Yo (potForm th u) → FormNonneg A Yo (potForm Om u)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) → ∀ (Om : KaehlerForm A) (C₁ : ℝ),
    ∃ CE : ℝ, ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ j, IsBoundedPotForm A R.Yo R.r Om C₁ (th j) (u j)) →
      TailLogBound A R.Yo R.r (fun j => potForm (th j) (u j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLogSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLogSmooth.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ), ∃ CE : ℝ,
    ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
        TailLogBound A R.Yo R.r (fun i => potForm (th i) (u i)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLocDensContOnOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def LocDensContOnOpen.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn Yo (u i)) →
    ∀ j, ContinuousOn (locDens A (fun i => potForm (th i) (u i)) j)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yo)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntMonoOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens mInt MIntegrable)

def MIntMonoOfDensLe.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] (A : FinHolAtlas D X) (V : Set X)
    (Φ Ψ : Fin D → LocPot X),
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V →
      0 ≤ locDens A Φ j y ∧ locDens A Φ j y ≤ locDens A Ψ j y) →
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ V → g x = 0) → MIntegrable A Ψ g →
      mInt A Φ g ≤ mInt A Ψ g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic locDensCont locDens_nonneg_of_psh)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StMIntegrableOfDensLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot locDens MIntegrable)

def MIntegrableOfDensLe.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (V : Set X) (Φ Ψ : Fin D → LocPot X),
    IsOpen V → (∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ContinuousOn (locDens A Ψ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V)) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V →
      0 ≤ locDens A Φ j y ∧ locDens A Φ j y ≤ locDens A Ψ j y) →
    ∀ g : X → ℝ, (∀ x, x ∉ V → g x = 0) → MIntegrable A Ψ g → MIntegrable A Φ g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic locDensCont locDens_nonneg_of_psh)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt integralWith locDens)

theorem tailLogBound_dim_zero {X : Type} [TopologicalSpace X] (A : FinHolAtlas 0 X) (Yo : Set X)
    (r : X → ℝ) (T : Fin 0 → LocPot X) : ∃ CE : ℝ, TailLogBound A Yo r T CE := by
  classical
  have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have : IsFiniteMeasure (volume : Measure (Fin 0 → ℂ)) := ⟨by rw [hv]; exact ENNReal.one_lt_top⟩
  have hd : ∀ j y, locDens A T j y = 1 := fun j y => by
    simp [locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  have hint : ∀ (f : (Fin 0 → ℂ) → ℝ) (K : Set (Fin 0 → ℂ)),
      ∫ y in K, f y = (volume K).toReal * f default := by
    intro f K
    have : f = fun _ => f default := funext fun y => congrArg f (Subsingleton.elim y default)
    rw [this, integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol : ∀ K : Set (Fin 0 → ℂ), 0 ≤ (volume K).toReal ∧ (volume K).toReal ≤ 1 := fun K =>
    ⟨ENNReal.toReal_nonneg, by
      have := ENNReal.toReal_mono (by rw [hv]; exact ENNReal.one_ne_top)
        (measure_mono (μ := volume) (Set.subset_univ K))
      rwa [hv, ENNReal.toReal_one] at this⟩
  set p : Fin A.n → X := fun j => (A.chart j).symm default
  set B := ∑ j, |Real.log (r (p j))|
  set M := ∑ j, |r (p j)| + Real.exp 1
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hM : 0 < M := by positivity
  refine ⟨B * M, fun R₀ hR₀ => ⟨fun j K _ _ => Integrable.of_finite.integrableOn, ?_⟩⟩
  set g := (tail Yo r R₀).indicator fun x => Real.log (r x)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hlog : 1 ≤ Real.log R₀ := by
    have := Real.log_le_log (Real.exp_pos 1) hR₀
    rwa [Real.log_exp] at this
  have hg : ∀ x, |g x| ≤ |Real.log (r x)| := fun x => by
    simp only [g, Set.indicator]
    split_ifs <;> simp
  have hterm : ∀ (P : ChartPartition A) j,
      |∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A T j y| ≤ |Real.log (r (p j))| ∧
        (M < R₀ → ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
          g ((A.chart j).symm y) * locDens A T j y = 0) := by
    intro P j
    rw [hint, hd, mul_one]
    have hχ0 := P.nonneg j (p j)
    have hχ1 : P.χ j (p j) ≤ 1 := P.sum_eq_one (p j) ▸
      Finset.single_le_sum (fun i _ => P.nonneg i (p j)) (Finset.mem_univ j)
    obtain ⟨hv0, hv1⟩ := hvol (A.chart j).target
    refine ⟨?_, fun hMR => ?_⟩
    · rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hχ0]
      have := hg (p j)
      have h2 : P.χ j (p j) * |g (p j)| ≤ |Real.log (r (p j))| := by nlinarith [abs_nonneg (g (p j))]
      nlinarith [abs_nonneg (g (p j))]
    · have hr : |r (p j)| ≤ ∑ i, |r (p i)| :=
        Finset.single_le_sum (f := fun i => |r (p i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hn : p j ∉ tail Yo r R₀ := fun h => by
        have := h.2
        have := le_abs_self (r (p j))
        have := Real.exp_pos 1
        linarith
      show (volume (A.chart j).target).toReal * (P.χ j (p j) * g (p j)) = 0
      rw [show g (p j) = 0 from Set.indicator_of_notMem hn _]
      simp
  have hRHS : 0 ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
    have : 0 ≤ Real.log R₀ := by linarith
    positivity
  show mInt A T g ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀
  unfold mInt
  split_ifs with h
  · unfold integralWith
    by_cases hMR : M < R₀
    · rw [Finset.sum_eq_zero fun j _ => (hterm h.some j).2 hMR]
      exact hRHS
    · replace hMR := not_lt.mp hMR
      calc _ ≤ ∑ j, |Real.log (r (p j))| :=
            Finset.sum_le_sum fun j _ => (le_abs_self _).trans (hterm h.some j).1
        _ ≤ B * M * Real.log R₀ ^ (0 + 1) / R₀ := by
          rw [le_div_iff₀ hR₀pos, pow_one]
          have h1 : B * R₀ ≤ B * M := mul_le_mul_of_nonneg_left hMR hB
          have h2 : B * M ≤ B * M * Real.log R₀ := by
            have := mul_nonneg hB hM.le
            nlinarith
          linarith
  · exact hRHS

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

theorem ell_anti {t t' : ℝ} (ht' : 0 < t') (htt : t' ≤ t) : ell t ≤ ell t' :=
  Real.log_le_log (inv_pos.2 (lt_of_lt_of_le ht' htt)) (inv_anti₀ ht' htt)

namespace System

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
  (S : System R)

end System

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  integralWith)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

section Defs

variable {W : Type} [TopologicalSpace W]

def secNorm (L : LocPot W) (s : W → W → ℂ) (x : W) : ℝ := ‖s x x‖ * Real.exp (-L.φ x x)

def greenEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  Real.log (1 + ε / secNorm L s x ^ 2)

def kappaEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) : LocPot W :=
  LocPot.rsmul 2 L + LocPot.ofFun fun x => Real.log (secNorm L s x ^ 2 + ε)

def curForms {D : ℕ} (th : Fin (D + 1) → LocPot W) (u : Fin (D + 1) → ℝ → W → ℝ) (t : ℝ) :
    Fin (D + 1) → LocPot W :=
  fun i => potForm (th i) (u i t)

def mixedForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) :
    Fin (D + 1) → LocPot W :=
  fun i => if (i : ℕ) < b then T i else Om

def restForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) : Fin D → LocPot W :=
  fun i => if (i : ℕ) < b then T i.castSucc else Om

def restrictForms {D : ℕ} (S : Set W) (Φ : Fin D → LocPot W) : Fin D → LocPot S :=
  fun i => (Φ i).pullback Subtype.val continuous_subtype_val

end Defs

structure UIData (D : ℕ) (W : Type) [TopologicalSpace W] where

  A : FinHolAtlas (D + 1) W

  Om : KaehlerForm A

  L : LocPot W

  s : W → W → ℂ

  nc : ℕ

  mult : Fin nc → ℕ

  comp : Fin nc → Set W

  B : ∀ k, FinHolAtlas D (comp k)
  L_pot : IsPotential A L
  s_sec : IsSection A L s
  s_snc : IsSNC A L s mult comp
  B_holo : ∀ k, HoloMap (B k) A Subtype.val

  Yo : Set W
  Yo_open : IsOpen Yo
  bd_analytic : A.IsAnalyticSubset Yoᶜ
  bd_interior : interior Yoᶜ = ∅
  bdComp_analytic : ∀ k, (B k).IsAnalyticSubset (Subtype.val ⁻¹' Yo)ᶜ
  bdComp_interior : ∀ k, interior ((Subtype.val ⁻¹' Yo : Set (comp k))ᶜ) = ∅

  r : W → ℝ

  th : Fin (D + 1) → LocPot W

  u : Fin (D + 1) → ℝ → W → ℝ

  lim : Fin (D + 1) → W → ℝ

  C : ℝ

  C₁ : ℝ

  ell₀ : ℝ

  CE : ℝ
  form : ∀ a t, 0 < t → ell₀ ≤ ell t → IsSmoothPotForm A Yo r Om C₁ (th a) (u a t)
  lim_le : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, lim a x ≤ u a t x
  near : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, r x ≤ ell t →
    u a t x ≤ lim a x + t ^ (1 / 3 : ℝ) + errE C t
  mono : ∀ a t t₀, 0 < t → t ≤ t₀ → ell₀ ≤ ell t₀ → ∀ x, u a t x ≤ u a t₀ x + C * errE C t₀
  tail : ∀ b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound A Yo r (mixedForms Om.pot (curForms th u t) b) CE
  tailComp : ∀ k b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound (B k) (Subtype.val ⁻¹' Yo) (r ∘ Subtype.val)
      (restrictForms (comp k) (restForms Om.pot (curForms th u t) b)) CE

namespace UIData

variable {D : ℕ} {W : Type} [TopologicalSpace W] (S : UIData D W)

def T (t : ℝ) : Fin (D + 1) → LocPot W := curForms S.th S.u t

def green (ε : ℝ) : W → ℝ := greenEp S.L S.s ε

def J (a : ℕ) (ε t : ℝ) : ℝ := mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.green ε)

def rest (a : ℕ) (t : ℝ) : Fin D → LocPot W := restForms S.Om.pot (S.T t) a

def divInt (Φ : Fin D → LocPot W) (g : W → ℝ) : ℝ :=
  ∑ k, (S.mult k : ℝ) * mInt (S.B k) (restrictForms (S.comp k) Φ) (g ∘ Subtype.val)

def plTerm (a : ℕ) (ha : a < D + 1) (ε t : ℝ) : ℝ :=
  mInt S.A (Fin.cons (kappaEp S.L S.s ε) (S.rest a t)) (S.u ⟨a, ha⟩ t) -
    2 * S.divInt (S.rest a t) (S.u ⟨a, ha⟩ t)

def gap (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : W → ℝ :=
  fun x => S.u ⟨a, ha⟩ t₀ x + S.C * errE S.C t₀ - S.u ⟨a, ha⟩ t x

def errW (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.gap a ha t₀ t)

def errDiv (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  S.divInt (S.rest a t) (S.gap a ha t₀ t)

end UIData

def UniformIntegrability.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ →
      S.ell₀ ≤ ell t → mInt S.A (S.T t) (S.green ε) ≤ η

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection projLine_isSimpleNormalCrossing ptAtlas)
open OnePoint

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

