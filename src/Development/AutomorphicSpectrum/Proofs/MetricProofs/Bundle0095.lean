module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntries
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacChange
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_prod_zpow (hz : z ∈ mcPts (mCoordIdeal x)) {κ : Type} [Fintype κ] (t : κ → Ω) (e : κ → ℤ)
    (h0 : ∀ k, t k ≠ 0) (ht : ∀ k, RegAt x (mCoordIdeal z) (t k)) (ht' : ∀ k, RegAt x (mCoordIdeal z) (t k)⁻¹) :
    RegAt x (mCoordIdeal z) (∏ k, t k ^ e k) ∧
      valAt x (∏ k, t k ^ e k) z = ∏ k, valAt x (t k) z ^ e k := by
  let u : κ → (regRing x z)ˣ := fun k =>
    ⟨⟨t k, ht k⟩, ⟨(t k)⁻¹, ht' k⟩, Subtype.ext (mul_inv_cancel₀ (h0 k)), Subtype.ext (inv_mul_cancel₀ (h0 k))⟩
  let f : (regRing x z)ˣ →* Ωˣ := Units.map (regRing x z).subtype.toMonoidHom
  let g : (regRing x z)ˣ →* ℂˣ := Units.map (regVal x hz).toMonoidHom
  let U : (regRing x z)ˣ := ∏ k, u k ^ e k
  have h1 : ((U : regRing x z) : Ω) = ∏ k, t k ^ e k := by
    have e1 : ((U : regRing x z) : Ω) = ((f U : Ωˣ) : Ω) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have h2 : valAt x ((U : regRing x z) : Ω) z = ∏ k, valAt x (t k) z ^ e k := by
    have e1 : valAt x ((U : regRing x z) : Ω) z = ((g U : ℂˣ) : ℂ) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  rw [← h1]
  exact ⟨(U : regRing x z).2, h2⟩

theorem reg_detFac (hz : z ∈ mcPts (mCoordIdeal x)) {N : ℕ} (j : ℕ) (i : Fin N) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) :
    RegAt x (mCoordIdeal z) (detFac j i A) ∧ valAt x (detFac j i A) z = detFac j i (valMat x z A) := by
  have h₁ := reg_minor hz hA (wIdx N j) (wIdx N j)
  have h₂ := reg_minor hz hA (omIdx N j) (omIdx N j)
  unfold detFac
  split_ifs
  · exact ⟨ValRing.regAt_mul h₁.1 h₂.1, (reg_mul hz h₁.1 h₂.1).2.trans (by rw [h₁.2, h₂.2])⟩
  · rw [mul_one, mul_one]; exact h₁
  · rw [one_mul, one_mul]; exact h₂
  · rw [mul_one, mul_one]; exact ⟨ValRing.regAt_one x z, CovMap.LocImg.FV.valAt_one' hz⟩

theorem ratio_reg (hz : z ∈ mcPts (mCoordIdeal x)) {k : K} {c₁ c₂ : ι k}
    (h₁ : (X ⟨k, c₁⟩ : MRing ι) ∉ mCoordIdeal z) (h₂ : (X ⟨k, c₂⟩ : MRing ι) ∉ mCoordIdeal z) :
    x ⟨k, c₂⟩ / x ⟨k, c₁⟩ ≠ 0 ∧ RegAt x (mCoordIdeal z) (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) ∧
      valAt x (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) z = z ⟨k, c₂⟩ / z ⟨k, c₁⟩ := by
  have hne : ∀ {c : ι k}, (X ⟨k, c⟩ : MRing ι) ∉ mCoordIdeal z → z ⟨k, c⟩ ≠ 0 := fun {c} hc h0 => hc (by
    show mConeMap z (X ⟨k, c⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  obtain ⟨hx₁, hv⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₁ hz (hne h₁)
  obtain ⟨hx₂, -⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₂ hz (hne h₂)
  refine ⟨div_ne_zero hx₂ hx₁, ⟨fun l => if l = k then 1 else 0, X ⟨k, c₂⟩, X ⟨k, c₁⟩,
    isMultiHomog_X_single ⟨k, c₂⟩, isMultiHomog_X_single ⟨k, c₁⟩, h₁, ?_⟩, ?_⟩
  · simp only [aeval_X]
    field_simp
  · rw [valAt_eq hz (hv c₂), inv_mul_eq_div]

end Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}


include M in
theorem detFac_change (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (p : Ψ × Fin N) :
    detFac j p.2 (F₂.T p.1) = detFac j p.2 (F₁.T p.1) * detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := by
  have hT₁ := h₁.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have h := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main M.Ω N j p.2 M.j_le).2.2.2 _ _ hT₁.1 ((hT₁.1.inv hu₁).mul (h₂.1 p.1).1)).2
  rwa [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at h

theorem prod_ratio (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) :
    (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k' =
      ∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k' := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [← mul_zpow, div_mul_cancel₀ _ (c₁ k')]


open CovMap.LocImg.FrameChange in
theorem frame_rel (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) (m : ι k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * F₂.u ⟨k, m⟩ I' := by
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (-detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 + e2 -
    (∑ I, M.coef ⟨k, m⟩ I * minorIJ (F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2)) * hd -
    F₂.u ⟨k, m⟩ I' * hA

theorem frame_none (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N)
    (hp : M.blk p = none) :
    F₂.υ p * ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' =
      detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.υ p := by
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have e1 := h₁.2.2.2 p hp
  have e2 := h₂.2.2.2 p hp
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 - e2 + M.lam p * hd + F₂.υ p * hA

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → (∀ τ, IsBlockDiag j (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)) ∧ (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)).det ≠ 0) ∧ ∀ p : Ψ × Fin N, (∀ k, M.blk p = some k → ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * plk M F₁ zb p.2 ⟨k, m⟩ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) = (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') * plk M F₂ zb p.2 ⟨k, m⟩ h) ∧ (M.blk p = none → valAt M.x (F₂.υ p) zb * (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') = detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x (F₁.υ p) zb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have hj := M.j_le
  have r₁₂ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular K ι Φ y Ψ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have r₂₁ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular K ι Φ y Ψ N j M zb F₂ F₁ hz hF₂ hF₁ hG₂ hG₁
  have hprod : ∀ τ, ((F₁.T τ)⁻¹ * F₂.T τ) * ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hF₂.1 τ).2.isUnit,
      Matrix.nonsing_inv_mul _ (hF₁.1 τ).2.isUnit]
  have hSS : ∀ τ, valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ) * valMat M.x zb ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [← (regMat_mul hz (r₁₂ τ) (r₂₁ τ)).2, hprod]
    exact CovMap.LocImg.FV.valMat_one hz
  have hbd : ∀ τ, IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := fun τ =>
    ((hF₁.1 τ).1.inv (hF₁.1 τ).2.isUnit).mul (hF₂.1 τ).1
  have hbd' : ∀ τ, IsBlockDiag j ((F₂.T τ)⁻¹ * F₁.T τ) := fun τ =>
    ((hF₂.1 τ).1.inv (hF₂.1 τ).2.isUnit).mul (hF₁.1 τ).1
  refine ⟨fun τ => ⟨CovMap.LocImg.FV.valMat_blockDiag hz (hbd τ), fun h0 => ?_⟩, fun p => ?_⟩
  · have h := congrArg Matrix.det (hSS τ)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have ht := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₁.1 k) (hG₂.1 k)
  have ht' := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₂.1 k) (hG₁.1 k)
  have c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0 := fun k h => (ht' k).1 (by rw [h, zero_div])
  obtain ⟨hrR, hrV⟩ := reg_prod_zpow hz (fun k : NonPluckerBlocks M.blk => M.x ⟨k, F₂.c k⟩ / M.x ⟨k, F₁.c k⟩) (M.b p)
    (fun k => (ht k).1) (fun k => (ht k).2.1) (fun k => by rw [inv_div]; exact (ht' k).2.1)
  simp only [fun k : NonPluckerBlocks M.blk => (ht k).2.2] at hrV
  obtain ⟨hdR, hdV⟩ := reg_detFac hz j p.2 (r₁₂ p.1)
  refine ⟨fun k hk h hh m => ?_, fun hp => ?_⟩
  · have hdet : ((F₁.T p.1)⁻¹ * F₂.T p.1).det ≠ 0 := fun h0 => by
      have h := congrArg Matrix.det (hprod p.1)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hdne := CovMap.LocImg.FrameChange.detFac_ne_zero hj p.2 (hbd p.1) hdet
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') /
        detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := ⟨_, rfl⟩
    have hρ' : detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ρ =
        ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [hρ, mul_comm]; exact div_mul_cancel₀ _ hdne
    have hrel : ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' →
        ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := fun m I' hI' => by
      apply mul_left_cancel₀ hdne
      rw [← mul_assoc, hρ']
      exact frame_rel M hF₁ hF₂ c₁ p k hk m I' hI'
    have hstep : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
    have hinv : ∑ m : ι k, F₂.u' (stepCols N j p.2) ⟨k, m⟩ * F₂.u ⟨k, m⟩ (stepCols N j p.2) = 1 := by
      rw [hF₂.2.2.1 p k hk _ _ hstep hstep, if_pos rfl]
    obtain ⟨hρR, hval⟩ := CovMap.LocImg.FV.reg_values hz p.2 (fun (m : ι k) I => F₁.u ⟨k, m⟩ I)
      (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) (fun m : ι k => F₂.u' (stepCols N j p.2) ⟨k, m⟩) _ ρ _ hstep
      (fun m I => (hG₁.2.1 _ _).1) (fun m I => (hG₂.2.1 _ _).1) (fun m => (hG₂.2.1 _ _).2) (r₁₂ p.1) hrel hinv
    have hmove : ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) zb *
          minorIJ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) I (stepCols N j p.2) =
        valAt M.x ρ zb * ∑ I, valAt M.x (F₂.u ⟨k, m⟩ I) zb * minorIJ h I (stepCols N j p.2) :=
      CovMap.LocImg.FV.sum_minor_mul hj p.2 (fun (m : ι k) I => valAt M.x (F₁.u ⟨k, m⟩ I) zb)
        (fun (m : ι k) I => valAt M.x (F₂.u ⟨k, m⟩ I) zb) _ _ hval h hh m
    have hv : detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x ρ zb =
        ∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [← hdV, ← (reg_mul hz hdR hρR).2, hρ', hrV]
    rw [plk, plk, hmove, ← mul_assoc, hv]
  · have e := congrArg (fun s => valAt M.x s zb) (frame_none M hF₁ hF₂ c₁ p hp)
    rw [(reg_mul hz (hG₂.2.2 p hp).2.1 hrR).2, (reg_mul hz hdR (hG₁.2.2 p hp).2.1).2, hrV, hdV] at e
    exact e

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentAppendIndependentSpan
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep

theorem eq_zero_of_sum_mem_span : ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : 𝓞 E →+* Module.End ℂ V) (s₀ : 𝓞 E →+* ℂ) (I₀ : AddSubgroup V) (r k : ℕ) (v : Fin r → V) (q : Fin k → V),
    IsOFamily ρ I₀ v → (∀ (c : 𝓞 E), ∀ x ∈ I₀, ρ c x ∈ I₀) → (∀ c, q c ∈ eigSp ρ s₀) →
    LinearIndependent ℂ (Fin.append (fun a => eigComp ρ s₀ (v a)) q) →
    ∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ Submodule.span ℂ (I₀ : Set V) → l = 0 := by
  intro E _ _ V _ _ ρ s₀ I₀ r k v q hF _ hq hli l hl
  obtain ⟨c, hc⟩ := EigCoef.eigComp_eq_combination E s₀
  obtain ⟨h1, h2, h3⟩ := hc V ρ
  let π : V →ₗ[ℂ] V := ∑ a ∈ c.support, c a • ρ a
  have hπ : ∀ x, π x = eigComp ρ s₀ x := by
    intro x
    rw [h1 x]
    simp [π, LinearMap.sum_apply]
  have hact : ∀ (b : 𝓞 E) x, π (ρ b x) = s₀ b • π x := by
    intro b x
    have e : π (ρ b x) = ρ b (π x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [π, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      have : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      exact LinearMap.congr_fun this x
    rw [e, EigCoef.mem_eigSp_iff.1 (hπ x ▸ h2 x) b]
  let W : Submodule ℂ V := Submodule.span ℂ (Set.range fun a => eigComp ρ s₀ (v a))
  have hO : ∀ y ∈ oSpan ρ v, π y ∈ W := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, i, rfl⟩ := hy
      rw [hact, hπ]
      exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact W.neg_mem hx
  have hI : ∀ x ∈ I₀, π x ∈ W := by
    intro x hx
    obtain ⟨_, _, hN⟩ := hF
    have hm := hO _ (AddSubgroup.nsmul_relIndex_mem (oSpan ρ v) hx)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at hm
    have hN' : (((oSpan ρ v).relIndex I₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    exact (W.smul_mem_iff hN').1 hm
  have hS : Submodule.span ℂ (I₀ : Set V) ≤ W.comap π := Submodule.span_le.2 hI
  have hxe : ∑ c, l c • q c ∈ eigSp ρ s₀ := Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hq c)
  have hW : ∑ c, l c • q c ∈ W := by
    have h := hS hl
    rw [Submodule.mem_comap, hπ, h3 _ hxe] at h
    exact h
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hW
  have hz := Fintype.linearIndependent_iff.1 hli (Fin.append (-m) l) (by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hm]
    simp)
  funext j
  have := hz (Fin.natAdd r j)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Cusp.EigIndep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgHomAdjoinInv
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Kext

theorem exists_algHom_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G :=
  _root_.UpperTheory.Reformulated.B.Yde9.main

end GlobalTheory.CompanionTheory.Ar.Cmp.Kext
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBasicOpenOfIsSncModel
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  intro K _ ι _ Ω _ _ y e J h p hp t ht
  obtain ⟨m, f, a, hf, ha, hsum, hcl⟩ := h p hp
  rw [Algebra.adjoin_range_eq_range_aeval] at hf ha
  choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)
  choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)
  obtain rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=
    funext fun l => (hF l).symm
  have hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_one, hA]
    exact sub_eq_zero.2 hsum
  have h1 := ht _ hker
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_one] at h1
  obtain ⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h1
  have hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0 := fun h0 => hl (ht _ h0)
  obtain ⟨-, z, n, -, -, hspan, hq⟩ := hcl l hfl _ rfl
  exact ⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousChangeOfFrameStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_change_of_frame : ∀ (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ) (T₀ : Matrix (Fin m) (Fin m) ℂ), (∀ i, ContinuousAt (fun z => M z i) 0) → (∀ i, ContinuousAt (fun z => f z i) 0) → LinearIndependent ℂ (M 0) → (∀ i, f 0 i = ∑ j, T₀ j i • M 0 j) → (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) → ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | exact GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernelStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), Sᵀ = S → ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) → ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | exact GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | (intros; apply GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMulPowEqAevalOfMemAdjoinInv
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_mul_pow_eq_aeval_of_mem_adjoin_inv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω), aeval τ F ≠ 0 →
      S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      ∀ s : S, ∃ (N : ℕ) (G : MvPolynomial σ ℚ), (s : Ω) * aeval τ F ^ N = aeval τ G := by
  intro Ω _ _ σ τ F S hf hS s
  obtain ⟨x, hx⟩ := s
  subst hS
  change ∃ (N : ℕ) (G : MvPolynomial σ ℚ), x * aeval τ F ^ N = aeval τ G
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨q, rfl⟩
    · exact ⟨1, 1, by simp [hf]⟩
    · exact ⟨0, X q, by simp⟩
  | algebraMap r =>
    exact ⟨0, C r, by simp [MvPolynomial.algebraMap_eq]⟩
  | add a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * F ^ M + H * F ^ N, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, ← h, ← h']
    ring
  | mul a b _ _ iha ihb =>
    obtain ⟨N, G, h⟩ := iha
    obtain ⟨M, H, h'⟩ := ihb
    refine ⟨N + M, G * H, ?_⟩
    simp only [map_mul, ← h, ← h']
    ring

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothConjInvariantMetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (a : K → ℤ), ∃ A : HermLine J, A.a = a ∧ IsSmoothHerm A ∧ IsConjInvariantH A := by
  intro K _ J _ a
  let S : K → ((k : K) × J k → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖ ^ 2
  have hS0 : ∀ k z, 0 ≤ S k z := fun k z => Finset.sum_nonneg fun i _ => by positivity
  have hSpos : ∀ k (z : (k : K) × J k → ℂ), (∃ i, z ⟨k, i⟩ ≠ 0) → 0 < S k z := by
    rintro k z ⟨i, hi⟩
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))
  have hSmul : ∀ (c : K → ℂ) k (z : (k : K) × J k → ℂ), S k (fun p => c p.1 * z p) = ‖c k‖ ^ 2 * S k z := by
    intro c k z
    simp only [S, norm_mul, mul_pow, Finset.mul_sum]
  refine ⟨⟨a, fun z => ∏ k, S k z ^ ((a k : ℝ) / 2), ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro z hz
    exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hSpos k z (hz k)) _
  · intro c z hc
    show ∏ k, S k (fun p => c p.1 * z p) ^ ((a k : ℝ) / 2) = _
    simp only [hSmul]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Real.mul_rpow (by positivity) (hS0 k z)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · show ContDiffOn ℝ _ (fun z => ∏ k, S k z ^ ((a k : ℝ) / 2)) _
    apply contDiffOn_prod
    intro k _ z hz
    exact ((ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) _)).contDiffAt.rpow_const_of_ne
      (hSpos k z (hz k)).ne').contDiffWithinAt
  · intro z
    simp [S]
end

