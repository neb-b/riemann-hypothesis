module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0002
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KFiniteDerivativesFiniteSpan
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0003

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFormalDegreeIdentity
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPhi

theorem hsInner_smul_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (a b : ℂ) (A A' : Wq →L[ℂ] Wp) :
    B.hsInner (a • A) (b • A') = a * star b * B.hsInner A A' := by
  have h : ∀ (c : ℂ) (Y : Wq →L[ℂ] Wp), B.hsVec (c • Y) = c • B.hsVec Y := fun c Y => rfl
  unfold B.hsInner
  rw [h, h, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem isUnit_det_of_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  have h : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : (Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r)) * g = 1 := by
    rw [Matrix.mul_assoc, h]; exact PI.HwUniqW.Hpk_mul_self
  exact Matrix.isUnit_det_of_left_inverse h1

theorem haar_left {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem Ph_coeff : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (dd : ℝ), R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ (x y x' y' : R.H) (X X' : Wq →L[ℂ] Wp) (p : B.SS k r), D.inSS p → Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g)) (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) D.μG ∧ B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p = ⟪y', R.σ (JF.sR p) y⟫_ℂ * ⟪R.σ (JF.sL p) x, x'⟫_ℂ / (dd : ℂ) * B.hsInner ((D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹))) X' := by
  intro hH k r ε mu R Wp _ _ _ _ Wq _ _ _ _ D dd hR hdd x y x' y' X X' p hp
  obtain ⟨hmul, hone, hinner, -, -, -, -, ⟨w, hw, -⟩, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hR
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r ε D.μG (haar_left D.haarG)
  obtain ⟨hdeg, hS⟩ := hc mu R hR
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hd : c * Formalism.QuantumDeterminants.fdegHC mu = dd := (hdeg w hw0).symm.trans (hdd w hw0)
  obtain ⟨hI, hE⟩ := hS (R.σ (JF.sR p) y) (R.σ (JF.sL p) x) y' x'
  rw [hd] at hE
  have ha : (Matrix.of p.1.1 : Mx k r) ∈ GG k r := hp.1.1
  have hb : (Matrix.of p.1.2 : Mx k r) ∈ GG k r := hp.2.1.1
  have hc' : (Matrix.of p.2.1 : Mx k r) ∈ GG k r := hp.2.2.1.1
  have hd' : (Matrix.of p.2.2 : Mx k r) ∈ GG k r := hp.2.2.2.1
  have hL : JF.sL p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hb ha
  have hRR : JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd' hc'
  have hLi : (JF.sL p)⁻¹ ∈ GG k r := PI.HwUniqW.inv_mem_UH hL
  set Y := (D.π (Matrix.of p.1.1)).comp (X.comp (D.π' (Matrix.of p.2.1)⁻¹)) with hY
  have key : ∀ g ∈ GG k r, B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g) (⟪x', R.σ g y'⟫_ℂ • X') =
      ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ * star ⟪x', R.σ g y'⟫_ℂ * B.hsInner Y X' := by
    intro g hg
    have e1 : B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) g = ⟪x, R.σ (B.sgs p g) y⟫_ℂ • Y := by
      unfold B.rho
      rw [hY, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    have e2 : B.sgs p g = (JF.sL p)⁻¹ * (g * JF.sR p) := by
      unfold B.sgs JF.sL JF.sR
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hgR : g * JF.sR p ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg hRR
    have e3 : ⟪x, R.σ (B.sgs p g) y⟫_ℂ = ⟪R.σ (JF.sL p) x, R.σ g (R.σ (JF.sR p) y)⟫_ℂ := by
      rw [← hinner _ hL, e2, ← hmul _ hL _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hLi hgR), ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hL), Matrix.one_mul, hmul _ hg _ hRR]
    rw [e1, e3, hsInner_smul_smul]
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mx k r) ∈ GG k r := by
    rw [ae_iff]; exact D.haarG.conc
  have hae2 : (fun g : Formalism.QuantumDeterminants.Mt k r => B.hsInner (B.rho D p (fun g => ⟪x, R.σ g y⟫_ℂ • X) (Matrix.of g))
      (⟪x', R.σ (Matrix.of g) y'⟫_ℂ • X')) =ᵐ[D.μG] fun g => ⟪R.σ (JF.sL p) x, R.σ (Matrix.of g) (R.σ (JF.sR p) y)⟫_ℂ *
        star ⟪x', R.σ (Matrix.of g) y'⟫_ℂ * B.hsInner Y X' := hae.mono fun g hg => key _ hg
  refine ⟨(hI.mul_const _).congr hae2.symm, ?_⟩
  unfold B.Ph
  rw [integral_congr_ae hae2, integral_mul_const, hE]

end GlobalTheory.BesselPhi
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishingStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  first | exact @GlobalTheory.BesselConv.be_conv | exact GlobalTheory.BesselConv.be_conv | (intros; apply GlobalTheory.BesselConv.be_conv <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.KFiniteDerivativesFiniteSpanStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.k_finite_derivatives_finite_span : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  first | exact @GlobalTheory.UnitBoxWords.box_words | exact GlobalTheory.UnitBoxWords.box_words | (intros; apply GlobalTheory.UnitBoxWords.box_words <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.MatrixCoefficientSmoothDerivativesStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.matrix_coefficient_smooth_derivatives : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDG ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  first | exact @GlobalTheory.CoeffDeriv.coeff_dLR | exact GlobalTheory.CoeffDeriv.coeff_dLR | (intros; apply GlobalTheory.CoeffDeriv.coeff_dLR <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothMapsClosure
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

theorem smMap_comp {R R' R'' : Rep k r} {T : R.H → R'.H} {T' : R'.H → R''.H}
    (hT : SmMap R R' T) (hT' : SmMap R' R'' T') : SmMap R R'' (fun v => T' (T v)) := by
  refine ⟨fun v hv => hT'.mem _ (hT.mem v hv), ?_, ?_, ?_⟩
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add _ (hT.mem v hv) _ (hT.mem w hw)]
  · intro a v hv
    rw [hT.smul a v hv, hT'.smul a _ (hT.mem v hv)]
  · intro W hW
    exact cw_comp (Bm := fun v => dsigW (k := k) (r := r) R''.σ W (T' v)) hT (hT'.cont W hW)

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem dsigW_mem (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W v ∈ R.sm := by
  induction W with
  | nil => exact hv
  | cons X W ih =>
    exact ((GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X (hW X List.mem_cons_self)).1 _
      (ih (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)))).1

theorem dsig_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ)
    {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (a • v + w) =
      a • dsig (k := k) (r := r) R.σ X v + dsig (k := k) (r := r) R.σ X w := by
  have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR X hX).1
  have h1 := ((h v hv).2.const_smul a).add (h w hw).2
  refine HasDerivAt.deriv ?_
  convert h1 using 1
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]

theorem dsigW_lin (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) (a : ℂ) {v w : R.H} (hv : v ∈ R.sm) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v + w) =
      a • dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    show dsig R.σ X (dsigW R.σ W (a • v + w)) = _
    rw [ih hW']
    exact dsig_lin hK hR (hW X List.mem_cons_self) a (dsigW_mem hK hR W hW' hv) (dsigW_mem hK hR W hW' hw)

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := by
  obtain ⟨hu, hi, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
      = gᴴ * Xᴴ * ((g⁻¹)ᴴ * Hpk k r) + (Hpk k r * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem norm_sigma (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (v : R.H) : ‖R.σ g v‖ = ‖v‖ := by
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, _⟩, hds⟩ := hR.2
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hPQ : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hQP : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  have hx' : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := Formalism.QuantumDeterminants.ioh_inUJ ε _ P₀ P₀⁻¹ g hPQ hH hg
  have hm := hds.2.2.1.2.1 (P₀ * g * P₀⁻¹) hx' v
  have e2 : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
  simp only [e2] at hm
  exact hm

theorem dsigW_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) (W : List (Mx k r))
    (hW : ∀ X ∈ W, InLieHpk k r X) {v : R.H} (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (R.σ g v) =
      R.σ g (dsigW (k := k) (r := r) R.σ (W.map fun X => g⁻¹ * X * g) v) := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hW'' : ∀ Y ∈ W.map (fun X => g⁻¹ * X * g), InLieHpk k r Y := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW' Z hZ)
    have hdet : IsUnit g.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
    have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    have h := (GlobalTheory.T.derivedAction_discreteSeries_properties hK k r ε mu R hR _ (inLie_conj hg (hW X List.mem_cons_self))).2.1 _
      (dsigW_mem hK hR _ hW'' hv) g hg
    rw [e] at h
    show dsig R.σ X (dsigW R.σ W (R.σ g v)) = R.σ g (dsig R.σ (g⁻¹ * X * g) _)
    rw [ih hW', h]

theorem smMap_sigma (hK : PI.KFinSmooth) (hR : R.IsDG ε mu) {g : Mx k r} (hg : g ∈ GG k r) :
    SmMap R R (fun v => R.σ g v) := by
  refine ⟨?_, fun v _ w _ => map_add (R.σ g) v w, fun a v _ => map_smul (R.σ g) a v, ?_⟩
  · intro v hv
    exact PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 v hv g hg
  · intro W hW
    refine ⟨1, [W.map fun X => g⁻¹ * X * g], ?_, fun v hv => ?_⟩
    · intro w hw Y hY
      rw [List.mem_singleton.mp hw] at hY
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hY
      exact inLie_conj hg (hW Z hZ)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      rw [dsigW_sigma hK hR hg W hW hv, norm_sigma hR hg]

theorem smMap_lin (hK : PI.KFinSmooth) {R₀ : Rep k r} (hR : R.IsDG ε mu) {T T' : R₀.H → R.H} (a : ℂ)
    (hT : SmMap R₀ R T) (hT' : SmMap R₀ R T') : SmMap R₀ R (fun v => a • T v + T' v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add
      (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a (hT.mem v hv)) (hT'.mem v hv)
  · intro v hv w hw
    rw [hT.add v hv w hw, hT'.add v hv w hw, smul_add]
    abel
  · intro b v hv
    rw [hT.smul b v hv, hT'.smul b v hv, smul_add, smul_comm]
  · intro W hW
    refine cw_of_semiBd R₀ (((semiBd_of_cw R₀ (hT.cont W hW)).mul (norm_nonneg a)).add
      (semiBd_of_cw R₀ (hT'.cont W hW))) (fun v hv => ?_)
    rw [dsigW_lin hK hR W hW a (hT.mem v hv) (hT'.mem v hv)]
    exact (norm_add_le _ _).trans (by rw [norm_smul])

end DS

theorem smMap_act : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → R''.IsDG ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  intro hK k r ε mu mu' mu'' R R' R'' hR hR' _
  exact ⟨fun g hg => smMap_sigma hK hR hg, fun T T' hT hT' => smMap_comp hT hT',
    fun T T' a hT hT' => smMap_lin hK hR' a hT hT', fun Wp _ T Bm hT hB => cw_comp hT hB⟩

end GlobalTheory.SmMapAct
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorBesselTransferStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_bessel_transfer : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  first | exact @GlobalTheory.herm_smul_eq_sum_of_tensRaw | exact GlobalTheory.herm_smul_eq_sum_of_tensRaw | (intros; apply GlobalTheory.herm_smul_eq_sum_of_tensRaw <;> assumption)
end Gp91
end

