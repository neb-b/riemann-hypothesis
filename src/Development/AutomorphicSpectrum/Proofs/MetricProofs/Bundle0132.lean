module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegral
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def ratioWt (A B : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (A.h z) - Real.log (B.h z) else 0

theorem ratioWt_of_mem {A B : HermLine ι} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ratioWt A B z = Real.log (A.h z) - Real.log (B.h z) := if_pos hz

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem smul_mem_iff (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  simp [hc]

theorem ratioWt_smul {A B : HermLine ι} (hab : A.a = B.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : ratioWt A B (fun p => c p.1 * z p) = ratioWt A B z := by
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [ratioWt_of_mem hz, ratioWt_of_mem ((smul_mem_iff c z hc).2 hz), A.smul c z hc, B.smul c z hc, hab]
    have h0 : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    rw [Real.log_mul h0 (A.pos z hz).ne', Real.log_mul h0 (B.pos z hz).ne']
    ring
  · have hz' := fun h => hz ((smul_mem_iff c z hc).1 h)
    simp only [ratioWt, if_neg hz, if_neg hz']

theorem ratioWt_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    SmoothFn (ratioWt A B) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (A.h z) - Real.log (B.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (ContDiffOn.log hA fun z hz => (A.pos z hz).ne').sub (ContDiffOn.log hB fun z hz => (B.pos z hz).ne')
  exact h.congr fun z hz => ratioWt_of_mem hz

def wtLine {A B : HermLine ι} (hab : A.a = B.a) : HermLine ι :=
  HermLine.ofWeight (ratioWt A B) fun c z hc => ratioWt_smul hab c z hc

theorem wtLine_h {A B : HermLine ι} (hab : A.a = B.a) (z : (Σ k, ι k) → ℂ) :
    (wtLine hab).h z = Real.exp (-ratioWt A B z) := rfl

theorem wtLine_smooth {A B : HermLine ι} (hab : A.a = B.a) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (wtLine hab) :=
  Real.contDiff_exp.comp_contDiffOn (ratioWt_smooth hA hB).neg

theorem logNormRat_wtLine {A B : HermLine ι} (hab : A.a = B.a) :
    logNormRat (wtLine hab) 1 1 = ratioWt A B := by
  funext z
  simp [logNormRat, wtLine_h]

theorem tensor_wtLine_h {A B : HermLine ι} (hab : A.a = B.a) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (A.tensor (wtLine hab)).h z = B.h z := by
  change A.h z * Real.exp (-ratioWt A B z) = B.h z
  rw [ratioWt_of_mem hz, neg_sub, Real.exp_sub, Real.exp_log (B.pos z hz), Real.exp_log (A.pos z hz)]
  field_simp [(A.pos z hz).ne']

theorem snoc_smooth {n : ℕ} {L : Fin n → HermLine ι} {B : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hB : IsSmoothHerm B) (j : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hB
  · rw [Fin.snoc_castSucc]
    exact hL i

theorem position_metric (hML : MetricLocalStatement) (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) (L : Fin D → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (A B : HermLine ι) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hab : A.a = B.a) :
    II K ι P (D + 1) (Fin.snoc L B) = II K ι P (D + 1) (Fin.snoc L A) - ptsIntegral P (pot L) (ratioWt A B) := by
  have hT : IsSmoothHerm (A.tensor (wtLine hab)) := ContDiffOn.mul hA (wtLine_smooth hab hA hB)
  have mc : II K ι P (D + 1) (Fin.snoc L (A.tensor (wtLine hab))) =
      II K ι P (D + 1) (Fin.snoc L A) - ptsIntegral P (pot L) (ratioWt A B) :=
    Known.metricChange K ι (II K ι) (hII K ι) P D L A (ratioWt A B) (fun c z hc => ratioWt_smul hab c z hc)
      hP hL hA (ratioWt_smooth hA hB)
  rw [← mc]
  refine hML K ι (II K ι) (hII K ι) P (D + 1) _ _ hP (snoc_smooth hL hB) (snoc_smooth hL hT) ?_ ?_
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      change B.a = A.a + 0
      rw [add_zero, hab]
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  · intro j z hz
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact (tensor_wtLine_h hab hz.1).symm
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem position_integral (hE : ResExistsStatement) {P J : Ideal (MRing ι)} {D : ℕ} (R : AnLogRes P J D) {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X)
    (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X) (hP : IsArithVar P (D + 1))
    (hdeg : IsDegreeOff A R.A π dg br) (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X)
    (hL : ∀ j, IsSmoothHerm (L j)) (hΦ : ∀ j, IsPotential A (Φ j))
    (hS : ∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1))
    (B₁ B₂ : HermLine ι) (h₁ : IsSmoothHerm B₁) (h₂ : IsSmoothHerm B₂) (hab : B₁.a = B₂.a)
    (v : X → ℝ) (hv : Continuous v)
    (hlog : ∀ x, Real.log (B₁.h (R.lift x x)) - Real.log (B₂.h (R.lift x x)) = v (π x)) :
    ptsIntegral P (pot L) (ratioWt B₁ B₂) = dg * mInt A Φ v := by
  have h1P : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : IsMultiHomog (1 : MRing ι) (fun _ => 0) := ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one
  have hrat : IsRatSectionOn P (wtLine hab) 1 1 := by
    refine ⟨fun _ => 0, fun _ => 0, hm, hm, h1P, h1P, fun k => ?_⟩
    change ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 0
    simp
  have hnull : IsNull R.A (∅ : Set R.X) := fun j => by simp
  have hlift : ∀ x ∉ (∅ : Set R.X), logNormRat (wtLine hab) 1 1 (R.lift x x) = v (π x) := by
    intro x _
    rw [logNormRat_wtLine, ratioWt_of_mem (R.mem x x (R.mem_U x)).1, hlog x]
  have hb := _root_.GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base hE K ι P J D R X A π hπ dg br hP hdeg L Φ hL hΦ hS (wtLine hab) 1 1 v ∅
    (wtLine_smooth hab h₁ h₂) hrat hnull hlift (mIntegrableCont A Φ hΦ v hv)
  rwa [logNormRat_wtLine] at hb

def toEnd {D : ℕ} (r : Fin (D + 1)) : Equiv.Perm (Fin (D + 1)) :=
  (finSuccEquiv' r).trans finSuccEquivLast.symm

theorem toEnd_self {D : ℕ} (r : Fin (D + 1)) : toEnd r r = Fin.last D := by
  simp [toEnd]

theorem toEnd_succAbove {D : ℕ} (r : Fin (D + 1)) (i : Fin D) : toEnd r (r.succAbove i) = i.castSucc := by
  simp [toEnd]

end GlobalTheory.CompanionTheory.Ar.PB.Tele

namespace GlobalTheory.CompanionTheory.Ar.PB


open Tele in
theorem num_sub_num : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (t t' : ℝ) (w : Fin (D + 1) → σ), 0 < t → t ≤ S.t₀ → 0 < t' → t' ≤ S.t₀ → Re.num II t w - Re.num II t' w = ∑ r : Fin (D + 1), mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t')) (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
  intro hIn II hII K _ ι _ D σ _ S P Re t t' w ht ht0 ht' ht'0
  have hF := hII.1
  have hP := Re.arith
  have hpot : ∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ
      (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1) := by
    intro a s hs hs0 x _
    obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot a x (Set.mem_univ x)
    refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
    · intro j
      exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
    · rintro y ⟨hyV, hyU⟩
      have hm := Re.R.mem x y hyU
      obtain ⟨c, hc, e⟩ := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
      have h := Re.line_eq a s hs hs0 y
      rw [e, (Re.line a s).smul c _ hc, (Re.ref a).smul c _ hc, Re.line_deg] at h
      have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
      rw [Real.log_mul hp ((Re.line a s).pos _ hm.1).ne',
        Real.log_mul hp ((Re.ref a).pos _ hm.1).ne'] at h
      have hvg : Real.log ((Re.ref a).h (Re.R.lift x y)) -
          (S.th a).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
      show Real.log ((Re.line a s).h (Re.R.lift x y)) -
        ((S.th a).φ (Re.π x) (Re.π y) + S.phT a s (Re.π y)) = (G y).re
      linarith
  have hbasic := (anSys_open_basics D σ S).2.2.2.1
  have hsc : ∀ (b : Prop) [Decidable b], 0 < (if b then t else t') ∧ (if b then t else t') ≤ S.t₀ := by
    intro b _
    split_ifs
    exacts [⟨ht, ht0⟩, ⟨ht', ht'0⟩]
  let Wd : ℕ → Fin (D + 1) → HermLine ι := fun m j => Re.line (w j) (if (j : ℕ) < m then t else t')
  have hdeg : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have step : ∀ r : Fin (D + 1), II K ι P (D + 1) (Wd (r + 1)) - II K ι P (D + 1) (Wd r) =
      Re.deg * mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
        (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
    intro r
    let L : Fin D → HermLine ι := fun i => Re.line (w (r.succAbove i)) (if r.succAbove i < r then t else t')
    have hL : ∀ i, IsSmoothHerm (L i) := fun i => Re.line_smooth _ _ (hsc _).1 (hsc _).2
    have hsm : ∀ B : HermLine ι, IsSmoothHerm B → ∀ j : Fin (D + 1),
        IsSmoothHerm ((Fin.snoc L B : Fin (D + 1) → HermLine ι) j) := fun B hB j => snoc_smooth hL hB j
    have e1 : Wd (r + 1) = (Fin.snoc L (Re.line (w r) t) : Fin (D + 1) → HermLine ι) ∘ toEnd r := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove r j with rfl | ⟨i, rfl⟩
      · rw [Function.comp_apply, toEnd_self, Fin.snoc_last]
        exact congrArg (Re.line (w _)) (if_pos (Nat.lt_succ_self _))
      · have hne : ((r.succAbove i : Fin (D + 1)) : ℕ) ≠ r := fun h => Fin.succAbove_ne r i (Fin.ext h)
        have hiff : ((r.succAbove i : Fin (D + 1)) : ℕ) < r + 1 ↔ r.succAbove i < r := by
          rw [Fin.lt_def]
          omega
        rw [Function.comp_apply, toEnd_succAbove, Fin.snoc_castSucc]
        exact congrArg (Re.line (w (r.succAbove i))) (if_congr hiff rfl rfl)
    have e0 : Wd r = (Fin.snoc L (Re.line (w r) t') : Fin (D + 1) → HermLine ι) ∘ toEnd r := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove r j with rfl | ⟨i, rfl⟩
      · rw [Function.comp_apply, toEnd_self, Fin.snoc_last]
        exact congrArg (Re.line (w _)) (if_neg (lt_irrefl _))
      · rw [Function.comp_apply, toEnd_succAbove, Fin.snoc_castSucc]
        exact congrArg (Re.line (w (r.succAbove i))) (if_congr Fin.lt_def.symm rfl rfl)
    rw [e1, e0, (hF K ι).1 P (D + 1) _ (toEnd r) hP fun j => hsm _ (Re.line_smooth _ _ ht ht0) _,
      (hF K ι).1 P (D + 1) _ (toEnd r) hP fun j => hsm _ (Re.line_smooth _ _ ht' ht'0) _]
    have hab : (Re.line (w r) t).a = (Re.line (w r) t').a := (Re.line_deg _ _).trans (Re.line_deg _ _).symm
    have hsl := position_metric hIn.metricLocal II hF hP L hL _ _ (Re.line_smooth (w r) t ht ht0)
      (Re.line_smooth (w r) t' ht' ht'0) hab
    rw [hsl, sub_sub_cancel]
    refine position_integral hIn.resExists Re.R S.A Re.π Re.holo Re.deg Re.br hP Re.degree L _ hL
      (fun i => hbasic _ _ (hsc _).1 (hsc _).2) (fun i => hpot _ _ (hsc _).1 (hsc _).2) _ _
      (Re.line_smooth _ _ ht ht0) (Re.line_smooth _ _ ht' ht'0) hab _ ?_ ?_
    · exact (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A ((S.reg (w r)).2.2 t ht ht0).1).sub
        (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A ((S.reg (w r)).2.2 t' ht' ht'0).1)
    · intro x
      rw [Re.line_eq _ _ ht ht0, Re.line_eq _ _ ht' ht'0]
      ring
  have tel : II K ι P (D + 1) (Wd (D + 1)) - II K ι P (D + 1) (Wd 0) =
      ∑ r : Fin (D + 1), (II K ι P (D + 1) (Wd (r + 1)) - II K ι P (D + 1) (Wd r)) := by
    rw [Fin.sum_univ_eq_sum_range (fun m => II K ι P (D + 1) (Wd (m + 1)) - II K ι P (D + 1) (Wd m)) (D + 1)]
    exact (Finset.sum_range_sub (fun m => II K ι P (D + 1) (Wd m)) (D + 1)).symm
  have hWt : Wd (D + 1) = fun j => Re.line (w j) t := by
    funext j
    simp [Wd, j.is_lt]
  have hWt' : Wd 0 = fun j => Re.line (w j) t' := by
    funext j
    simp [Wd]
  simp only [Realis.num]
  rw [← sub_div, ← hWt, ← hWt', tel, Finset.sum_congr rfl fun r _ => step r, ← Finset.mul_sum,
    mul_div_cancel_left₀ _ hdeg]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentity
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SqFubini

def eY (d : ℕ) : ((Fin d → ℂ) × ℂ) ≃ᵐ (Fin (d + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm

theorem eY_apply {d : ℕ} (x : (Fin d → ℂ) × ℂ) : eY d x = Fin.cons x.2 x.1 := by
  first | rfl | (simp [eY, MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eY, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eY_measurePreserving (d : ℕ) : MeasurePreserving (eY d) volume volume :=
  (Measure.measurePreserving_swap).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm

def eW (d : ℕ) : ((Fin d → ℂ) × (ℂ × ℂ)) ≃ᵐ (Fin (d + 2) → ℂ) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ)
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem eW_apply {d : ℕ} (x : (Fin d → ℂ) × (ℂ × ℂ)) :
    eW d x = Fin.cons x.2.1 (Fin.cons x.2.2 x.1) := by
  first | rfl | (simp [eW, MeasurableEquiv.prodComm, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eW, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eW_measurePreserving (d : ℕ) : MeasurePreserving (eW d) volume volume :=
  ((Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc volume volume volume)).trans
    (((MeasurePreserving.id volume).prod
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem fubini_piece {Y P Z : Type*} [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure P) (ρ : Measure Z) [SFinite μ] [SFinite ν]
    (e : (Y × P) ≃ᵐ Z) (he : MeasurePreserving e (μ.prod ν) ρ) (B : Set Y) (S : Set Z)
    (hS : e ⁻¹' S = B ×ˢ Set.univ) (F : Z → ℝ) (hF : IntegrableOn F S ρ) :
    IntegrableOn (fun y => ∫ p, F (e (y, p)) ∂ν) B μ ∧
      ∫ z in S, F z ∂ρ = ∫ y in B, ∫ p, F (e (y, p)) ∂ν ∂μ := by
  have h1 : IntegrableOn (F ∘ e) (B ×ˢ Set.univ) (μ.prod ν) := by
    rw [← hS]
    exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hF
  have h2 : ∫ z in S, F z ∂ρ = ∫ x in B ×ˢ Set.univ, F (e x) ∂(μ.prod ν) := by
    rw [← hS]
    exact (he.setIntegral_preimage_emb e.measurableEmbedding F S).symm
  constructor
  · have h3 : Integrable (F ∘ e) ((μ.restrict B).prod (ν.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact h1
    simpa [IntegrableOn, Function.comp_def] using h3.integral_prod_left
  · rw [h2]
    simpa [Function.comp_def] using setIntegral_prod (F ∘ e) h1

theorem fibre_sum {d k : ℕ} (B : Set (Fin d → ℂ)) (F : ℕ → (Fin (d + 2) → ℂ) → ℝ)
    (H : (Fin (d + 1) → ℂ) → ℝ) (κ : ℝ)
    (hF : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B})
    (hH : IntegrableOn H {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B})
    (hpt : ∀ y ∈ B, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
      κ * ∫ a : ℂ, H (Fin.cons a y))
    (hB : MeasurableSet B) :
    ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B}, F i z =
      κ * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B}, H z := by
  have hSW : (eW d) ⁻¹' {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eW_apply]
  have hSY : (eY d) ⁻¹' {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eY_apply]
  have hW := fun i (hi : i < k) => fubini_piece volume volume volume (eW d) (eW_measurePreserving d) B _ hSW
    (F i) (hF i hi)
  have hY := fubini_piece volume volume volume (eY d) (eY_measurePreserving d) B _ hSY H hH
  simp only [eW_apply, eY_apply] at hW hY
  rw [hY.2, Finset.sum_congr rfl fun i hi => (hW i (Finset.mem_range.1 hi)).2,
    ← integral_finsetSum _ fun i hi => (hW i (Finset.mem_range.1 hi)).1, ← integral_const_mul]
  exact setIntegral_congr_fun hB fun y hy => hpt y hy

theorem ae_ne (d : ℕ) : ∀ᵐ z : Fin (d + 2) → ℂ, z 0 ≠ z 1 := by
  let L : (Fin (d + 2) → ℂ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 0) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 1)
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (d + 2) → ℂ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L, LinearMap.mem_ker, Pi.single_apply] at h1
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin (d + 2) → ℂ)) (LinearMap.ker L) hs
  refine measure_mono_null ?_ h0
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
  simp [L, LinearMap.mem_ker, hz]

theorem isC2At_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {σ : Type} [Fintype σ]
    (c : σ → ℝ) (P : σ → LocPot X) (x : X) (h : ∀ a, IsTwiceDifferentiableAt A (P a) x) : IsTwiceDifferentiableAt A (sumPot c P) x := by
  intro j hj
  have : (sumPot c P).φ x ∘ (A.chart j).symm =
      fun y => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) y := rfl
  rw [this]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (h a j hj)

end SqFubini

namespace SqFubini

def EW {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k i : ℕ) :
    Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
  let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i
  fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))

def EY {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k : ℕ) :
    Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
  fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)

end SqFubini


open SqFubini in
theorem AnSq.sum_polar_gH_eq : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  intro hI hF d σ _ SY a₀ ε Q c hc k hk1 hk2
  have hlim := _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence hI d σ SY a₀ ε Q
  obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) Q.SW
  obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
  have hhom := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned (d + 1) σ SY

  have hexW := fun i => mInt_sumPot_expand (d + 2) Q.SW.X Q.SW.A (Option σ) Q.SW.open' Q.SW.potH
    (Q.wcoef c k i) Q.gH hnW hC2W fun w => (hlim w).1
  have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
    (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
  have hpolW : ∀ i, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) =
      mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH := fun i => (hexW i).2.symm
  have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) =
      mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) := by
    rw [hexY.2]
    exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

  have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ Q.U n → Q.ΦW n z ∈ Q.SW.open' := by
    intro n z hz
    rw [Q.bdry_eq 0, Set.mem_preimage, Q.first_projection_chart_compat n z hz]
    exact Q.ΦY_open n _ (by simpa using hz)

  have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) Q.SW.X Q.SW.A _ _ Q.ΦW
    (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH Q.coverW
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (Q.B_meas n |>.2 hz)))
    (hexW i).1
  have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ Q.ΦY
    (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) Q.coverY
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (Q.ΦY_open n z (Q.B_meas n |>.2 hz)))
    hexY.1

  have key : ∀ n, ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
      2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z := by
    intro n
    let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, c a * Q.α n a y
    have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε Q c hc n k hk1 hk2
    have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} := (Q.coverW.2.1 n).1
    have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} := (Q.coverY.2.1 n).1
    let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
      logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (EW (Q.G n) α k i) z
    have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n}),
        Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = F i z := by
      intro i hi
      filter_upwards [ae_restrict_of_ae (ae_ne d), ae_restrict_mem hmW] with z hne hz
      have hU : Fin.tail (Fin.tail z) ∈ Q.U n := (Q.B_meas n).2 hz
      have h1 : Q.gH (Q.ΦW n z) = logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
        Q.norm_hom n z hU hne
      have h2 : paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
          maDens (EW (Q.G n) α k i) z := hd.2 i hi z hU
      rw [h1, h2]
    have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
        maDens (EY (Q.G n) α k) z := by
      intro z hz
      have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
          maDens (EY (Q.G n) α k) z := hd.1 z ((Q.B_meas n).2 hz)
      rw [h2, one_mul]
    have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} :=
      fun i hi => ((hcW i).1 n).congr (hae i hi)
    have hHint : IntegrableOn (maDens (EY (Q.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} :=
      (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
    have hpt : ∀ y ∈ Q.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 * kappa k) * ∫ a : ℂ, maDens (EY (Q.G n) α k) (Fin.cons a y) := by
      intro y hy
      have hyU : y ∈ Q.U n := (Q.B_meas n).2 hy
      have hnh : Q.U n ∈ 𝓝 y := (Q.U_open n).mem_nhds hyU
      have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
      exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk1 hk2 (Q.G n) α y
        (by filter_upwards [hnh] with y' hy' using Q.G_pos n y' hy')
        (fun p q => ((Q.G_smooth n p q).contDiffAt hnh).of_le h2)
        (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((Q.α_smooth n a).contDiffAt hnh).of_le h2))
    rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
      setIntegral_congr_fun hmY hH]
    exact fibre_sum (Q.B n) F _ _ hFint hHint hpt (Q.B_meas n).1
  have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z)
      (∑ i ∈ Finset.range k, mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH) :=
    hasSum_sum fun i _ => (hcW i).2
  rw [funext key] at hsW
  rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
  exact hsW.unique (hcY.2.mul_left _)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

