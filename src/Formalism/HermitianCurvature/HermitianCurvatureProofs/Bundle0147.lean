module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0143

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfLoc
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hmat_zb (h : C.LPt) (s : ℕ) (τ : ℂ) (hl : D.IsLocPt (h ++ [(s, τ)]) (D.ptSize (h ++ [(s, τ)])))
    (a' q : ℕ) (ha' : a' < D.ptSize (h ++ [(s, τ)])) (hq : q < D.ptSize (h ++ [(s, τ)])) :
    U.hMat (D.ptPerm (h ++ [(s, τ)])) (D.ptDiag (h ++ [(s, τ)])) ⟨a', ha'⟩ ⟨q, hq⟩ =
      C3.Zb (D.ptSize h) s (U.hMat (D.ptPerm h) (D.ptDiag h)) τ a' q := by
  have hP := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h s τ
  have hlh := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hl
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hl).1
  have hspech := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlh).1
  have entry : ∀ {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (x y : Fin p),
      U.hMat σ d x y = if σ x = y then d y else 0 := by
    intro p σ d x y
    simp only [U.hMat, Matrix.mul_diagonal, U.wP, Matrix.of_apply]
    split_ifs <;> simp
  rw [entry]
  have hpa : ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) =
      if a' < D.ptSize h then D.ptPartner h a' else D.ptSize h + (s - 1 - (a' - D.ptSize h)) := by
    rw [hspec ⟨a', ha'⟩]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.partner_append s τ h a' (by omega)
  have hdq : D.ptDiag (h ++ [(s, τ)]) ⟨q, hq⟩ = if q < D.ptSize h then D.ptScal h q else τ := by
    simp only [D.ptDiag]
    exact Formalism.FourierDecayAlt.P.Dx2.SL.scal_append s τ h q (by omega)
  have heq : (D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ = ⟨q, hq⟩) ↔
      ((D.ptPerm (h ++ [(s, τ)]) ⟨a', ha'⟩ : Fin _) : ℕ) = q := by
    constructor
    · intro e; rw [e]
    · intro e; exact Fin.ext e
  unfold C3.Zb
  by_cases h1 : a' < D.ptSize h
  · rw [dite_eq_left h1]
    have hpart : D.ptPartner h a' < D.ptSize h := by
      rw [← hspech ⟨a', h1⟩]; exact (D.ptPerm h ⟨a', h1⟩).isLt
    by_cases h2 : q < D.ptSize h
    · rw [dite_eq_left h2, entry]
      have heqh : (D.ptPerm h ⟨a', h1⟩ = ⟨q, h2⟩) ↔ D.ptPartner h a' = q := by
        rw [← hspech ⟨a', h1⟩]
        constructor
        · intro e; rw [e]
        · intro e; exact Fin.ext e
      by_cases h3 : D.ptPartner h a' = q
      · rw [if_pos (heq.2 (by rw [hpa, if_pos h1]; exact h3)), if_pos (heqh.2 h3), hdq, if_pos h2]
        rfl
      · rw [if_neg (fun e => h3 (by rw [heq] at e; rw [hpa, if_pos h1] at e; exact e)),
          if_neg (fun e => h3 (heqh.1 e))]
    · rw [dite_eq_right h2, if_neg]
      intro e
      rw [heq, hpa, if_pos h1] at e
      omega
  · rw [dite_eq_right h1]
    by_cases h3 : D.ptSize h ≤ q ∧ a' < D.ptSize h + s ∧ q < D.ptSize h + s ∧
        (a' - D.ptSize h) + (q - D.ptSize h) + 1 = s
    · rw [if_pos h3, if_pos (heq.2 (by rw [hpa, if_neg h1]; omega)), hdq, if_neg (by omega)]
    · rw [if_neg h3, if_neg]
      intro e
      rw [heq, hpa, if_neg h1] at e
      apply h3
      omega

theorem one_mem_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨1, ?_, 1, ?_, (Matrix.mul_one 1).symm⟩
  · simp [Formalism.QuantumDeterminants.UWset, Formalism.QuantumDeterminants.UH]
  · simp [Formalism.QuantumDeterminants.Nset, Formalism.QuantumDeterminants.UH, Matrix.one_apply]

theorem vLet_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) (K : B.Mat k r → E)
    (s g : B.Mat k r) (hs : s ∈ Sset k r z) (hg : g ∈ B.GV k r) :
    D.vLet k r z z' j hj l e K (s * g) = D.vLet k r z z' j hj l e (fun x => K (s * x)) g := by
  have hD : Dmin k r z z' (s * g) ⟨j, by omega⟩ = Dmin k r z z' g ⟨j, by omega⟩ := by
    have := Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz hz' s hs 1 (one_mem_Sset k r z') g ⟨j, by omega⟩
    rwa [Matrix.mul_one] at this
  have hA := AAInvW.left_aa E k r z (j - e) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)
    ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) K s g hs hg
  unfold D.vLet
  rw [hD, hA.1.symm, hA.2.symm]

theorem loc_left {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {s x : B.Mat k r} (hs : s ∈ B.GV k r) (h : CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K (s * x)) :
    CapelliWordSumExpansion.Loc (⊤ : ℕ∞) (fun y => K (s * y)) x := by
  obtain ⟨U, f', hU, hsxU, hf', he⟩ := h
  have hc : Continuous (fun y : B.Mat k r => s * y) := continuous_const.mul continuous_id
  refine ⟨(fun y => s * y) ⁻¹' U, fun y => f' (s * y), hU.preimage hc, hsxU, ?_, fun y hy hyG => ?_⟩
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun y => s * y, map_add' := fun a b => Matrix.mul_add s a b,
        map_smul' := fun c y => Matrix.mul_smul s c y }
    have hl : ContDiff ℝ (⊤ : ℕ∞) (fun y : B.Mat k r => s * y) := (LinearMap.toContinuousLinearMap L).contDiff
    exact hf'.comp hl.contDiffOn (fun y hy => hy)
  · exact he _ hy (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hyG)

theorem smoothLev_of_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {K : B.Mat k r → E}
    {D : Set (Q.Mx k r)} (h : ∀ x ∈ Q.Glev k r 0 ∩ D, CapelliWordSumExpansion.Loc (⊤ : ℕ∞) K x) : Q.SmoothLev k r 0 D K := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  exact ⟨U, f', hU, hgU, by exact_mod_cast hf', fun g hg hgl => he g hg hgl.1⟩

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnfoldIint
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_le_I {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
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
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) (hw0DD : w0 ∈ DDsp σ w0)
    {e1 : Mx k r → ℂ} (hee1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e1 g = ⟪v, σ g w0⟫_ℂ)
    {zz : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, (fun m : Formalism.QuantumDeterminants.Mt k r => ‖e1 (Matrix.of m)‖ₑ)
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) i j) ∂(μW.prod μN) := by
  have b1 := l_enorm_le (c := c) hds hT hπ hW hN hbe hv hlv hw0DD hz
  refine b1.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr_ae
  filter_upwards [prod_ae hW hN] with p hp
  show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) w0⟫_ℂ‖ₑ =
    ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz)‖ₑ
  rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hz)]

theorem e_weight {e : Mx k r → ℂ} {C a b : ℝ}
    (hb : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e y‖ ≤ C * B.gN y ^ (-a))
    {x : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hpos : 0 < B.gN x) :
    ‖e x‖ₑ * ENNReal.ofReal (B.gN x ^ b) ≤ ENNReal.ofReal |C| * ‖B.gN x ^ (-(a - b))‖ₑ := by
  have h1 := hb x hx
  have h2 : ‖e x‖ * B.gN x ^ b ≤ |C| * B.gN x ^ (-(a - b)) := by
    have e2 : B.gN x ^ (-(a - b)) = B.gN x ^ (-a) * B.gN x ^ b := by
      rw [← Real.rpow_add hpos]
      ring_nf
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpos.le _)))
      (Real.rpow_nonneg hpos.le _)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

def Iint (A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (z : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) ∂μ

def Aext (e : Mx k r → ℂ) (m : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ := ‖e (Matrix.of m)‖ₑ

theorem Aext_meas {e : Mx k r → ℂ} (he : Continuous e) : Measurable (Aext e) := by
  unfold Aext
  exact (Continuous.enorm (he.comp (show Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Matrix.of m) from continuous_id))).measurable

theorem Iint_meas {A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μ] : Measurable (Iint A μ) := by
  unfold Iint
  refine Measurable.lintegral_prod_right' (f := fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
    A (fun i j => (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) i j)) ?_
  refine hA.comp (Continuous.measurable ?_)
  exact ((continuous_snd.fst.matrix_mul continuous_snd.snd).matrix_mul continuous_fst)

theorem unfold_Iint {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {A Ψ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A) (hΨ : Measurable Ψ)
    (hinv : ∀ᵐ z ∂νq, ∀ᵐ p ∂(μW.prod μN),
      Ψ (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) = Ψ z) :
    ∫⁻ z, Iint A (μW.prod μN) z * Ψ z ∂νq = ∫⁻ x, A x * Ψ x ∂μG := by
  have hcont : ∀ z : Formalism.QuantumDeterminants.Mt k r,
      Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    fun z => Continuous.matrix_mul continuous_id continuous_const
  have hg : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul continuous_fst continuous_snd).measurable
  rw [hq (fun x => A x * Ψ x) (hA.mul hΨ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with z hz
  unfold Iint Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [lintegral_map (f := fun s : Formalism.QuantumDeterminants.Mt k r => A (fun i j => (Matrix.of s * Matrix.of z) i j) *
      Ψ (fun i j => (Matrix.of s * Matrix.of z) i j))
    (by exact (hA.comp (hcont z).measurable).mul (hΨ.comp (hcont z).measurable)) hg]
  have hmA : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j)) :=
    hA.comp ((show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul (Continuous.matrix_mul continuous_fst continuous_snd) continuous_const).measurable)
  rw [← lintegral_mul_const _ hmA]
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with p hp
  exact congrArg _ hp.symm

theorem pull2 {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} (F G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (M : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hm : ∀ z, Measurable fun z' => G z' * M z z') :
    ∫⁻ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' ∂νq = K * ∫⁻ z, F z * ∫⁻ z', G z' * M z z' ∂νq' ∂νq := by
  have h1 : ∀ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' = K * (F z * ∫⁻ z', G z' * M z z' ∂νq') := by
    intro z
    have e1 : (fun z' => K * (F z * (G z' * M z z'))) = fun z' => (K * F z) * (G z' * M z z') := by
      funext z'
      ring
    rw [e1, lintegral_const_mul _ (hm z), mul_assoc]
  simp_rw [h1]
  exact lintegral_const_mul' K _ hK

theorem final2 {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hF : Measurable Fx)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG ∂μG = c * ((∫⁻ x, Fx x ∂μG) * ∫⁻ y, Fx y ∂μG) := by
  have h1 : ∀ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG = (c * Fx x) * ∫⁻ y, Fx y ∂μG := by
    intro x
    simp_rw [← mul_assoc]
    exact lintegral_const_mul _ hF
  simp_rw [h1]
  rw [lintegral_mul_const _ (hF.const_mul c), lintegral_const_mul _ hF, mul_assoc]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

