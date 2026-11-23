module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0100
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0105
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

def cW (k r : ℕ) (θ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def PhaseSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ θ : ℝ, ∃ h h' : Q.Mx k r, h ∈ UWset k r z ∧ h' ∈ UWset k r z' ∧
      (∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        h *ᵥ (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = Complex.exp (-((θ : ℂ) * Complex.I)) • (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) ∧
        (∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = 0 → h *ᵥ v = v) ∧
        CP.mu0 k r z z' (rot θ ζ) = h * cW k r θ * CP.mu0 k r z z' ζ * h') ∧
      ∀ v, inWb k r v → herm (Hpk k r) v z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v

def LowerUnipotentRotation : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (θ : ℝ) (Y : ℂ) (f : Q.Mx k r → E), ∀ g ∈ Q.Glev k r (Fin.last r),
      Q.tL k r z z' (Fin.last r) Y 1 0 f (cW k r θ * g) =
        Complex.exp (-((θ : ℂ) * Complex.I)) • Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => f (cW k r θ * x)) g

def RotRadSp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ (θ : ℝ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)), Φ ∈ Q.RadSp k r z z' π π' →
      (fun c g => Φ c (cW k r θ * g)) ∈ Q.RadSp k r z z' π π'

def ThtRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ (θ : ℝ) (h h' : Q.Mx P.k P.r), h ∈ UWset P.k P.r Bs.z → h' ∈ UWset P.k P.r Bs.z' →
    ∀ ζ ∈ Gauge.GC.Ann P,
      h *ᵥ SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = Complex.exp (-((θ : ℂ) * Complex.I)) • SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z = 0 → herm (Hpk P.k P.r) v (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 →
        h *ᵥ v = v) →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v) →
      ∀ Xf : Wq →L[ℂ] Wp,
        (Bs.π h).comp (((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) Xf).comp (Bs.π' h')) =
          Complex.exp ((θ : ℂ) * Complex.I) • (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) ((Bs.π h).comp (Xf.comp (Bs.π' h')))

def PhaseInvOfCut : Prop :=
  PhaseSec → LowerUnipotentRotation → RotRadSp → ThtRot → KapLine → AlgSS → DatumConst → FibStable → PhaseInv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetCornerMatrixLevelZero
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section lev

variable {k : ℕ}

theorem det_corner_matrix_level_zero {r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    (Zhat k r' z z' g).det = Q.zetaL k r' z z' (Fin.last r') g := by
  subst hr
  exact (Matrix.det_fin_one _).trans rfl

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grpInt_at_dframe (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    GrpInt (p.T.bs P.r) ν'r m₀r ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) := by
  have hG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hT := mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos
  have hdet : (Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀).det ≠ 0 := by
    rw [det_corner_matrix_level_zero (Nat.sub_self P.r), hζ]
    intro h0
    rw [h0, map_zero] at hG
    linarith
  have hdom : ((x.1, γ₀) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r) ∈
      Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a _ => ?_⟩, ?_⟩
    · exfalso
      have ha := a.isLt
      revert ha
      show ¬ (a.val < P.r - P.r)
      omega
    · show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
        Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
      rw [hζ]
      exact hG
  obtain ⟨-, -, he⟩ := Ψ.2
  intro hB hhB hBν
  have e := he (x.1, γ₀) hdom _ (Formalism.FourierDecayAlt.P.Topx1.vecw_conj_mem _ hLev.2.2 hhB) _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB)
  try dsimp only at e
  have hc := Formalism.FourierDecayAlt.P.PBI.dframe_commute _ (Nat.sub_self P.r) hLev.2.2 hγG hγF hdet hhB hBν
  exact e.symm.trans (congrArg (fun g => (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 g) hc)

end place

end Formalism.FourierDecayAlt.P.PBI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_enorm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) {x : H} (hx : x ∈ DDsp σ w0)
    {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ g x)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN) := by
  rw [l_of_be (hbe _ (dd_stable hds hg x hx) v hv) hlv]
  have hbe' := be_enorm_le (c := c) hds hT hπ hW hN (x := x) (v := v) hg
  calc ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹ • (be z c π σ μW μN (σ g x) v) (l v)‖ₑ
      = ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖(be z c π σ μW μN (σ g x) v) (l v)‖ₑ := enorm_smul _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * (‖be z c π σ μW μN (σ g x) v‖ₑ * ‖l v‖ₑ) := by
        gcongr
        exact ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ((∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) *
          ‖l v‖ₑ) := by gcongr
    _ = _ := by ring

theorem lint_left {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    {a : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM a x) ∂μG = ∫⁻ x, F x ∂μG := by
  have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    exact this.measurable
  rw [← lintegral_map hF hm, hG.left a ha]

theorem gN_mul_rpow (hNI : NormInv) {x Y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ} (hb : 0 ≤ b) :
    B.gN (Y * x) ^ (-b) ≤ B.gN x ^ b * B.gN Y ^ (-b) := by
  obtain ⟨hsub, hinv⟩ := hNI k r
  have hxi := MatrixMultiplicationContinuity.uh_inv hx
  have hYx : Y * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hY hx
  have h1 : 1 ≤ B.gN x := (hinv x hx).2
  have h2 : 1 ≤ B.gN Y := (hinv Y hY).2
  have h3 : 1 ≤ B.gN (Y * x) := (hinv _ hYx).2
  have hle : B.gN Y ≤ B.gN (Y * x) * B.gN x := by
    have e : Y = Y * x * x⁻¹ := by rw [Matrix.mul_assoc, hxi.2.1, Matrix.mul_one]
    calc B.gN Y = B.gN (Y * x * x⁻¹) := by rw [← e]
      _ ≤ B.gN (Y * x) * B.gN x⁻¹ := hsub _ _
      _ = B.gN (Y * x) * B.gN x := by rw [(hinv x hx).1]
  have hpos : 0 < B.gN x := lt_of_lt_of_le one_pos h1
  have hq : B.gN Y / B.gN x ≤ B.gN (Y * x) := (div_le_iff₀ hpos).mpr hle
  have hqpos : 0 < B.gN Y / B.gN x := div_pos (lt_of_lt_of_le one_pos h2) hpos
  calc B.gN (Y * x) ^ (-b) ≤ (B.gN Y / B.gN x) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hqpos hq (by linarith)
    _ = B.gN x ^ b * B.gN Y ^ (-b) := by
        rw [Real.div_rpow (lt_of_lt_of_le one_pos h2).le hpos.le, Real.rpow_neg hpos.le,
          div_eq_mul_inv, inv_inv, mul_comm]

theorem meas_matmul {α : Type*} [MeasurableSpace α] {f g : α → Formalism.QuantumDeterminants.Mt k r}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => (fun i j => (Matrix.of (f p) * Matrix.of (g p)) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hf)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp hg))

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem perm_id_of_mono {m : ℕ} (τ : Equiv.Perm (Fin m)) (h : StrictMono (fun l => (τ l).val)) : τ = 1 := by
  have hm : StrictMono τ := fun a b hab => Fin.lt_def.mpr (h hab)
  have hinv : StrictMono τ.symm := by
    intro a b hab
    by_contra hc
    have h' := hm.monotone (not_lt.mp hc)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h'
    exact absurd hab (not_lt.mpr h')
  refine Equiv.ext fun l => ?_
  have h1 : l ≤ τ l := hm.le_apply
  have h2 : l ≤ τ.symm l := hinv.le_apply
  have h3 := hm.monotone h2
  rw [Equiv.apply_symm_apply] at h3
  rw [Equiv.Perm.one_apply]
  exact le_antisymm h3 h1

theorem top_self {m N : ℕ} (a : Fin m → Fin N) (ha : Function.Injective a) :
    (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if a (σ k) = a k then (1 : ℂ) else 0)) = 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra H
      exact hσ (Equiv.ext fun l => by simpa using not_not.mp (fun h => H ⟨l, h⟩))
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (ha.ne hk)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem prod_ne_zero_imp {m N : ℕ} (a b : Fin m → Fin N) (σ : Equiv.Perm (Fin m))
    (h : ∏ k, (if a (σ k) = b k then (1 : ℂ) else 0) ≠ 0) : ∀ k, a (σ k) = b k := by
  intro k
  by_contra hk
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk))

private theorem leading_term_identity_lemma {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (P : (Fin m → Fin n) → Prop) [DecidablePred P] (d : (Fin m → Fin n) → ℂ)
    (fa fb : (Fin m → Fin n) → Fin m → Fin n) (s0 : ℂ) (c0 : Fin m → Fin n) (h0 : P c0)
    (h1 : ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c0 (σ k) = fb c0 k then (1 : ℂ) else 0) = 1)
    (hz : ∀ c, P c → c ≠ c0 → ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0) = 0) :
    ∃ C : Fin m → A, ∀ u : ℂ, (∑ c, if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) =
      algebraMap ℂ A (u ^ m * d c0) + ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * C l := by
  have hP : PolyLe m (fun u => ∑ c, if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    refine pl_sum Finset.univ (fun c u => if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0)
      fun c _ => ?_
    by_cases hc : P c
    · simp only [hc, if_true]
      exact pl_lmul _ (qminor_poly E (fa c) (fb c) s0)
    · simp only [hc, if_false]
      exact pl_zero m
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun u => ?_⟩
  rw [← hC u]
  beta_reduce
  have hsplit : ∀ c, (if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      (if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) -
        (if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    intro c
    split_ifs
    · rw [mul_sub, Algebra.smul_def, ← map_mul]
      congr 2
      ring
    · simp
  have hsecond : (∑ c, if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      algebraMap ℂ A (u ^ m * d c0) := by
    rw [Finset.sum_eq_single c0]
    · rw [if_pos h0, h1, mul_one]
    · intro c _ hc
      split_ifs with hPc
      · rw [hz c hPc hc, mul_zero, mul_zero, map_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib, hsecond]
  abel

theorem leading_term_identity : LeadAA := by
  intro A _ _ k r E xi m hm
  classical
  have hxv : ∀ l, (xR k r m hm l).val = l.val := fun l => rfl
  have hxinj : Function.Injective (xR k r m hm) := fun a b h => Fin.ext (by rw [← hxv a, ← hxv b, h])
  have hxm : StrictMono (xR k r m hm) := fun a b hab => Fin.lt_def.mpr (by rw [hxv, hxv]; exact hab)
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun c => StrictMono c)
    (fun c => (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det)
    (fun _ => xR k r m hm) id 0 (xR k r m hm) hxm (top_self _ hxinj) (by
      intro c hc hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp (xR k r m hm) c σ (right_ne_zero_of_mul hσ)
      have hσm : StrictMono (fun l => (σ l).val) := by
        intro a b hab
        have h1 : c a < c b := hc hab
        rw [← heq a, ← heq b, Fin.lt_def, hxv, hxv] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ hσm
      apply hne
      funext l
      rw [← heq l, hσ1]
      rfl)
  refine ⟨C, fun u => ?_⟩
  have h := hC u
  simp only [id, add_zero] at h
  unfold AAx
  exact h

theorem leading_term_vector_identity : LeadAAv := by
  intro A _ _ k r E y m hm
  classical
  have hkey : ∀ l, keyS k r (sR k r m hm l) = l.val := by
    intro l
    have hl := l.isLt
    have hv : (sR k r m hm l).val = 2 * r + k - l.val := rfl
    unfold keyS
    rw [hv]
    split_ifs with h
    · omega
    · omega
  have hsinj : Function.Injective (sR k r m hm) := fun a b h =>
    Fin.ext (by rw [← hkey a, ← hkey b, h])
  have hsm : StrictMono (fun l => keyS k r (sR k r m hm l)) := fun a b hab => by
    simp only [hkey]
    exact hab
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun B => StrictMono (fun l => keyS k r (B l)))
    (fun B => (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) (B l)).det)
    id (fun _ => sR k r m hm) ((m : ℂ) - 1) (sR k r m hm) hsm (top_self _ hsinj) (by
      intro B hB hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp B (sR k r m hm) σ (right_ne_zero_of_mul hσ)
      have hB' : ∀ l, B l = sR k r m hm (σ.symm l) := by
        intro l
        have := heq (σ.symm l)
        rwa [Equiv.apply_symm_apply] at this
      have hσm : StrictMono (fun l => (σ.symm l).val) := by
        intro a b hab
        have h1 := hB hab
        simp only [hB', hkey] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ.symm hσm
      apply hne
      funext l
      rw [hB' l, hσ1]
      rfl)
  refine ⟨C, fun ell => ?_⟩
  have h := hC ell
  simp only [id] at h
  unfold AAv
  rw [show ell + (m : ℂ) - 1 = ell + ((m : ℂ) - 1) by ring]
  exact h

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurePreservingProdRearrange
section
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measurePreserving_prod_rearrange {L M P N : Type*} [MeasurableSpace L] [MeasurableSpace M] [MeasurableSpace P] [MeasurableSpace N]
    (μL : Measure L) (μM : Measure M) (μP : Measure P) (μN : Measure N) [SigmaFinite μL] [SigmaFinite μM]
    [SigmaFinite μP] [SigmaFinite μN] :
    MeasurePreserving (fun p : L × (M × (P × N)) => (p.2.1, ((p.1, p.2.2.1), p.2.2.2)))
      (μL.prod (μM.prod (μP.prod μN))) (μM.prod ((μL.prod μP).prod μN)) := by
  have h1 := (measurePreserving_prodAssoc μL μM (μP.prod μN)).symm
  have h2 := (Measure.measurePreserving_swap (μ := μL) (ν := μM)).prod (MeasurePreserving.id (μP.prod μN))
  have h3 := measurePreserving_prodAssoc μM μL (μP.prod μN)
  have h4 := (MeasurePreserving.id μM).prod (measurePreserving_prodAssoc μL μP μN).symm
  have := h4.comp (h3.comp (h2.comp h1))
  convert this using 1
  funext ⟨l, m, p, n⟩
  rfl

theorem muSS_eq (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
    (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (he : MeasurePreserving e volume volume)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (c1 c2 : NNReal)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) :
    S.μSS = (c1 * c2) • ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0')).map
      (fun p => OD.Xi S w e p.1 p.2) := by
  have sf : ∀ {V : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn V μ → SigmaFinite μ := by
    intro V μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI := sf hμ0
  haveI := sf hμ0'
  have m1 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z).measurable
  have m2 : Measurable (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
      Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)) := (HC.cont_Phi S.z').measurable

  have hA : MeasurePreserving
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (OD.nuR S w μ0 μ0'))
      ((S.μW.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0)).prod
        (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))) := by
    have h1 := (measurePreserving_prodAssoc (volume : Measure (C2.Lstidx w → ℂ))
      (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0))
      (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))).symm
    have h2 := (measurePreserving_prod_rearrange (volume : Measure (C2.Lstidx w → ℂ)) S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have h3 := ((MeasurePreserving.id S.μW).prod (he.prod (MeasurePreserving.id μ0))).prod
      (MeasurePreserving.id (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')))
    have := h3.comp (h2.comp h1)
    simp only [OD.nuR]
    convert this using 1
    all_goals first | rfl | (funext p; rfl)
  have hB : Measurable (Prod.map
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
      (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) :=
    (measurable_id.prodMap m1).prodMap (measurable_id.prodMap m2)
  have hXi : (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => OD.Xi S w e p.1 p.2) =
      (Prod.map
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
        (Prod.map (id : Mt k r → Mt k r) (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
          Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))) ∘
      (fun p : (C2.Lstidx w → ℂ) × OD.RR k r w => ((p.2.1.1, (e (p.1, p.2.1.2.1), p.2.1.2.2)), p.2.2)) := by
    funext p; rfl
  rw [hXi, ← Measure.map_map hB hA.measurable, hA.map_eq,
    ← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    Measure.map_id, Measure.map_id]
  show (S.μW.prod S.μN).prod (S.μW'.prod S.μN) = _
  have e2 : S.μW'.prod S.μN = S.μW'.prod (c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2))) := by rw [← hN2]
  rw [e2, hN1]
  rw [ENNReal.smul_def c1, ENNReal.smul_def c2, ENNReal.smul_def (c1 * c2), Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.ME
end

