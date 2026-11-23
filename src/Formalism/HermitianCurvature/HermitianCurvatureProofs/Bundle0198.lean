module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpModelAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCovarianceHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def bq (H : B.Mat k r) : B.Mat k r →ₗ[ℝ] B.Mat k r →ₗ[ℝ] B.Mat k r :=
  LinearMap.mk₂ ℝ (fun M N => Mᴴ * H * N)
    (fun M M' N => by simp [Matrix.conjTranspose_add, Matrix.add_mul])
    (fun c M N => by simp [Matrix.conjTranspose_smul])
    (fun M N N' => by simp [Matrix.mul_add])
    (fun c M N => by simp)

def bqL (H : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (B.Mat k r →ₗ[ℝ] B.Mat k r) ≃ₗ[ℝ] (B.Mat k r →L[ℝ] B.Mat k r)).toLinearMap ∘ₗ
      bq H)

theorem bqL_apply (H M N : B.Mat k r) : bqL H M N = Mᴴ * H * N := rfl

theorem tangent_eq {d : ℕ} {O : Set (Fin d → ℝ)} {κ : (Fin d → ℝ) → B.Mat k r} (hO : IsOpen O)
    (hκ : ContDiffOn ℝ ∞ κ O) (hG : ∀ y ∈ O, κ y ∈ B.GV k r) {x : Fin d → ℝ} (hx : x ∈ O)
    (v : Fin d → ℝ) :
    (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x + (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v = 0 := by
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hB := (bqL (Hpk k r)).hasDerivAt_of_bilinear (fun _ => hc) (fun _ => hc)
  have hmem : ∀ᶠ t in nhds (0 : ℝ), x + t • v ∈ O := by
    have hcont : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hx)
  have hev : (fun _ : ℝ => Hpk k r) =ᶠ[nhds 0]
      fun t : ℝ => bqL (Hpk k r) ((κ ∘ fun t : ℝ => x + t • v) t) ((κ ∘ fun t : ℝ => x + t • v) t) := by
    filter_upwards [hmem] with t ht
    rw [bqL_apply]
    exact (hG _ ht).symm
  have h2 := hB.congr_of_eventuallyEq hev
  have e := h2.deriv
  rw [deriv_const] at e
  simp only [Function.comp_apply, zero_smul, add_zero] at e
  have e' : (κ x)ᴴ * Hpk k r * fderiv ℝ κ x v + (fderiv ℝ κ x v)ᴴ * Hpk k r * κ x = 0 := e.symm
  exact (add_comm _ _).trans e'

theorem chart_id {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    fderiv ℝ Φ (κ x) (fderiv ℝ κ x v) = v := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, _⟩ := hC
  have hd : DifferentiableAt ℝ κ x := (hκ.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hdΦ : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.contDiffAt (hU.mem_nhds (hκO x hx).2.1)).differentiableAt (by simp)
  have h1 := hdΦ.hasFDerivAt.comp x hd.hasFDerivAt
  have hev : (Φ ∘ κ) =ᶠ[nhds x] id := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact (hκO y hy).2.2
  have h2 : HasFDerivAt (Φ ∘ κ) (ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq hev
  have := h1.unique h2
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => L v) this

theorem vr_onto {d : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) {x : Fin d → ℝ} (hx : x ∈ O) (v : Fin d → ℝ) :
    ∃ Y : B.Mat k r, B.inLie k r Y ∧ VR κ Φ Y x = v := by
  have hG : ∀ y ∈ O, κ y ∈ B.GV k r := fun y hy => (hC.2.2.2.2.1 y hy).1
  have hg : (κ x)ᴴ * Hpk k r * κ x = Hpk k r := hG x hx
  have hdet : IsUnit (κ x).det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH (hG x hx)
  have hT := tangent_eq hC.1 hC.2.2.1 hG hx v
  set g := κ x with hgdef
  set A := fderiv ℝ κ x v with hAdef
  refine ⟨g⁻¹ * A, ?_, ?_⟩
  · have e1 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
      calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg]
        _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * g := by rw [Matrix.mul_nonsing_inv g hdet]; simp
    have e2 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
      calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg]
        _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.mul_one]
    show (g⁻¹ * A)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * A) = 0
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2, ← Matrix.mul_assoc]
    exact hT
  · show fderiv ℝ Φ g (g * (g⁻¹ * A)) = v
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hdet, Matrix.one_mul]
    exact chart_id hC hx v

def ellL {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ) :
    B.Mat k r →ₗ[ℝ] ℝ where
  toFun X := ξ ⬝ᵥ VR κ Φ X x
  map_add' X Y := by simp only [VR, Matrix.mul_add, map_add (f := _), dotProduct_add]
  map_smul' c X := by simp only [VR, Matrix.mul_smul, map_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul]

theorem ellL_apply {d : ℕ} (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (x ξ : Fin d → ℝ)
    (X : B.Mat k r) : ellL κ Φ x ξ X = ξ ⬝ᵥ VR κ Φ X x := rfl

def cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) : B.Mat k r :=
  Matrix.of fun j i => ((ℓ (Matrix.single i j 1) : ℝ) : ℂ) - Complex.I * ((ℓ (Complex.I • Matrix.single i j 1) : ℝ) : ℂ)

theorem ell_single (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (i j : Fin (2 * r + k + 1)) (c : ℂ) :
    ℓ (Matrix.single i j c) = c.re * ℓ (Matrix.single i j 1) + c.im * ℓ (Complex.I • Matrix.single i j 1) := by
  have : (Matrix.single i j c : B.Mat k r) =
      c.re • (Matrix.single i j (1 : ℂ) : B.Mat k r) + c.im • (Complex.I • (Matrix.single i j (1 : ℂ) : B.Mat k r)) := by
    ext p q
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp
  rw [this, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem re_trace_cMat (ℓ : B.Mat k r →ₗ[ℝ] ℝ) (X : B.Mat k r) : (Matrix.trace (cMat ℓ * X)).re = ℓ X := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, cMat, Matrix.of_apply, Complex.re_sum, Complex.mul_re,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ell_single ℓ i j (X i j)]
  norm_num
  ring

theorem inLie_half (C : B.Mat k r) : B.inLie k r ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hH' : ∀ M : B.Mat k r, Hpk k r * (Hpk k r * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hH, Matrix.one_mul]
  have hHc : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  show ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r))ᴴ * Hpk k r +
    Hpk k r * ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHc,
    Matrix.conjTranspose_conjTranspose, hs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hH, hH',
    Matrix.mul_one]
  rw [← smul_add]
  have : Cᴴ * Hpk k r - Hpk k r * C + (Hpk k r * C - Cᴴ * Hpk k r) = 0 := by abel
  rw [this, smul_zero]

theorem re_trace_half (C X : B.Mat k r) (hX : B.inLie k r X) :
    (Matrix.trace ((1 / 2 : ℂ) • (C - Hpk k r * Cᴴ * Hpk k r) * X)).re = (Matrix.trace (C * X)).re := by
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hX' : Hpk k r * (X * Hpk k r) = -Xᴴ := by
    have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
    have h2 := congrArg (· * Hpk k r) h
    simp only [Matrix.add_mul, Matrix.mul_assoc, hH, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_right h2
  have e1 : Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = -star (Matrix.trace (C * X)) := by
    calc Matrix.trace (Hpk k r * Cᴴ * Hpk k r * X) = Matrix.trace (Hpk k r * (Cᴴ * Hpk k r * X)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Cᴴ * (Hpk k r * (X * Hpk k r))) := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = -Matrix.trace ((X * C)ᴴ) := by
          rw [hX', Matrix.mul_neg, Matrix.trace_neg, Matrix.conjTranspose_mul]
      _ = -star (Matrix.trace (C * X)) := by rw [Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub, e1, smul_eq_mul]
  simp [Complex.mul_re]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.ChartCovPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity


open ChartCovPf in
theorem chart_covariance_holds : ChartCov := by
  intro k r d O U κ Φ hC x hx ξ
  refine ⟨(1 / 2 : ℂ) • (cMat (ellL κ Φ x ξ) - Hpk k r * (cMat (ellL κ Φ x ξ))ᴴ * Hpk k r),
    inLie_half _, ?_, ?_⟩
  · intro hξ h0
    obtain ⟨Y, hY, hYv⟩ := vr_onto hC hx ξ
    have e := re_trace_half (cMat (ellL κ Φ x ξ)) Y hY
    rw [h0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, re_trace_cMat, ellL_apply, hYv] at e
    exact hξ (dotProduct_self_eq_zero.1 e.symm)
  · intro X hX
    rw [re_trace_half _ X hX, re_trace_cMat, ellL_apply]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FamOK {d : ℕ} (O : Set (Fin d → ℝ)) (P : WOp d) (m : ℕ) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O

def OpCV : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ 2 * r + k + 1 → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * Ξ₀.charpoly.coeff (2 * r + k + 1 - j)

def OpCapR : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z'] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ₀ Bs).charpoly.coeff (k - j)

def OpCapL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ : B.Mat k r), B.inLie k r Ξ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace (Ξ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def OpCVOf : Prop := RwChart → CapWords → OpCV

def OpCapROf : Prop := RwChart → CapRWords → OpCapR

def OpCapLOf : Prop := RwChart → CapLWords → OpCapL

def NilOfCharpoly : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ j, 1 ≤ j → j ≤ n → M.charpoly.coeff (n - j) = 0) → IsNilpotent M

def ConjAlg : Prop :=
  ∀ (k r : ℕ) (g : B.Mat k r), g ∈ B.GV k r →
    (∀ A : B.Mat k r, B.inLie k r A → B.inLie k r (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, IsNilpotent A → IsNilpotent (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, A ≠ 0 → g * A * g⁻¹ ≠ 0) ∧
    ∀ A X : B.Mat k r, Matrix.trace ((g * A * g⁻¹) * (g * X * g⁻¹)) = Matrix.trace (A * X)

def CovL : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
      (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * X)).re

def opOne {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d := [(1, [V]), (-c, [])]

theorem opOne_app {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    WOp.app (opOne V c) v x = vfD V v x - c * v x := by
  simp [opOne, WOp.app, vfW]
  ring

theorem opOne_symb {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (x ξ : Fin d → ℝ) :
    WOp.symb (opOne V c) 1 x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) := by
  simp [opOne, WOp.symb]

theorem opOne_ok {d : ℕ} {O : Set (Fin d → ℝ)} {V : (Fin d → ℝ) → (Fin d → ℝ)} (c : ℂ) (hV : ContDiffOn ℝ ∞ V O) :
    FamOK O (opOne V c) 1 := by
  intro t ht
  simp only [opOne, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨by simp, ?_⟩
    intro W hW
    simp only [List.mem_singleton] at hW
    rw [hW]; exact hV
  · exact ⟨by simp, by simp⟩

theorem re_trace_span {k r q : ℕ} (A : B.Mat k r) (Xs : Fin q → B.Mat k r) (a : Fin q → ℝ)
    (h : ∀ i, (Matrix.trace (A * Xs i)).re = 0) :
    (Matrix.trace (A * ∑ i, ((a i : ℝ) : ℂ) • Xs i)).re = 0 := by
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h i, mul_zero]

theorem fin_shift {n : ℕ} {p : ℕ → Prop} (h : ∀ j : Fin n, p ((j : ℕ) + 1)) : ∀ j, 1 ≤ j → j ≤ n → p j := by
  intro j h1 h2
  have := h ⟨j - 1, by omega⟩
  simpa [Nat.sub_add_cancel h1] using this

theorem chartSysWOfParts_of (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly)
    (hConj : ConjAlg) (hCovL : CovL) : ChartSysWOfParts := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 k r z z' d O U κ Φ u hk hz hz' hT hT' hC hOm hG
  obtain ⟨hCk, hNR, hNL, hCLe, hCRe, hCVe⟩ := hG
  obtain ⟨huc, hfld, hw⟩ := h2 k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨q, Xs, hXs, hspan⟩ := h3 k r
  obtain ⟨Bs, hBs⟩ := h8 k r z hz hT
  obtain ⟨Bs', hBs'⟩ := h8 k r z' hz' hT'
  have oCV := hCV h2 h4 k r z z' d O U κ Φ u hC hOm hCk hCVe
  have oCR := hCR h2 h5 k r z z' d O U κ Φ u Bs' hC hOm hCk hBs' (hCRe Bs' hBs')
  have oCL := hCL h2 h6 k r z z' d O U κ Φ u Bs hC hOm hCk hBs (hCLe Bs hBs)
  have hXin : ∀ i, B.inLie k r (Xs i) := fun i => (hspan (Xs i) (hXs i)).1
  choose cR hcR using fun i => hNR (Xs i) (hXs i)
  choose cL hcL using fun i => hNL (Xs i) (hXs i)
  choose PV cV hcV0 hPVok hPVapp hPVsym using
    fun j : Fin (2 * r + k + 1) => oCV ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PR cRR hcR0 hPRok hPRapp hPRsym using
    fun j : Fin k => oCR ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PL cLL hcL0 hPLok hPLapp hPLsym using
    fun j : Fin k => oCL ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  have hOmx : ∀ x ∈ O, κ x ∈ JF.Om k r z z' := fun x hx => ⟨(hC.2.2.2.2.1 x hx).1, hOm x hx⟩
  refine ⟨Fin q ⊕ Fin q ⊕ Fin (2 * r + k + 1) ⊕ Fin k ⊕ Fin k, inferInstance,
    Sum.elim (fun i => opOne (VR κ Φ (Xs i)) (cR i)) (Sum.elim (fun i => opOne (VL κ Φ (Xs i)) (cL i))
      (Sum.elim PV (Sum.elim PR PL))),
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (Sum.elim (fun j => (j : ℕ) + 1)
      (Sum.elim (fun j => (j : ℕ) + 1) (fun j => (j : ℕ) + 1)))),
    ?_, ?_, huc, ?_, ?_⟩
  · rintro (i | i | j | j | j)
    · show 1 ≤ 2 * r + k + 1; omega
    · show 1 ≤ 2 * r + k + 1; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; exact Nat.succ_le_of_lt j.isLt
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
  · rintro (i | i | j | j | j)
    · exact opOne_ok _ (hfld _).1
    · exact opOne_ok _ (hfld _).2
    · exact hPVok j
    · exact hPRok j
    · exact hPLok j
  · rintro (i | i | j | j | j) x hx
    · show WOp.app (opOne (VR κ Φ (Xs i)) (cR i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).1
      simp only [B.Rw, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcR i _ (hOmx x hx), smul_eq_mul, sub_self]
    · show WOp.app (opOne (VL κ Φ (Xs i)) (cL i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).2
      simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcL i _ (hOmx x hx), smul_eq_mul, sub_self]
    · exact hPVapp j x hx
    · exact hPRapp j x hx
    · exact hPLapp j x hx
  · intro x hx ξ hξ hall
    obtain ⟨Ξ₀, hΞ₀, hΞ₀0, hcov⟩ := h1 k r d O U κ Φ hC x hx ξ
    have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    obtain ⟨cLie, cNil, cNe, cTr⟩ := hConj k r (κ x) hg
    have hcovL := hCovL k r d O U κ Φ hC x hx ξ Ξ₀ hΞ₀ hcov
    have hΞ : B.inLie k r (κ x * Ξ₀ * (κ x)⁻¹) := cLie Ξ₀ hΞ₀
    have hNRz : ∀ i, (Matrix.trace (Ξ₀ * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inl i)
      change WOp.symb (opOne (VR κ Φ (Xs i)) (cR i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcov _ (hXin i)]
      exact_mod_cast h0
    have hNLz : ∀ i, (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inr (Sum.inl i))
      change WOp.symb (opOne (VL κ Φ (Xs i)) (cL i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcovL _ (hXin i)]
      exact_mod_cast h0
    have hVF : ∀ j : Fin (2 * r + k + 1), Ξ₀.charpoly.coeff (2 * r + k + 1 - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inl j)))
      change WOp.symb (PV j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPVsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcV0 j)
    have hRF : ∀ j : Fin k, (cmp Ξ₀ Bs').charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      change WOp.symb (PR j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPRsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcR0 j)
    have hLF : ∀ j : Fin k, (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))
      change WOp.symb (PL j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPLsym j x hx ξ _ hΞ hcovL] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcL0 j)
    have hnil0 : IsNilpotent Ξ₀ :=
      hNil _ Ξ₀ (fin_shift (p := fun j => Ξ₀.charpoly.coeff (2 * r + k + 1 - j) = 0) hVF)
    have hUW' := h7 k r z' Bs' hz' hT' hBs' Ξ₀ hΞ₀ (fin_shift (p := fun j => (cmp Ξ₀ Bs').charpoly.coeff (k - j) = 0) hRF)
    have hUW := h7 k r z Bs hz hT hBs _ hΞ
      (fin_shift (p := fun j => (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - j) = 0) hLF)
    refine ⟨κ x * Ξ₀ * (κ x)⁻¹, hΞ, cNe Ξ₀ (hΞ₀0 hξ), cNil Ξ₀ hnil0, ?_, ?_⟩
    · intro X hX
      rcases hX with hX | hX
      · exact hUW X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span _ Xs a hNLz
    · intro X hX
      rw [cTr Ξ₀ X]
      rcases hX with hX | hX
      · exact hUW' X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span Ξ₀ Xs a hNRz

theorem chartEqs_of_J (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly) (hConj : ConjAlg)
    (hCovL : CovL) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords) (h5 : CapRWords) (h6 : CapLWords)
    (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField) (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_all (chartSysWOfParts_of hCV hCR hCL hNil hConj hCovL) h1 h2 h3 h4 h5 h6 h7 h8 hS s1 s2 s3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInt
section
open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem aCInt_of_proper (hP : ACProper) : ACInt := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc g hg
  obtain ⟨P, hPc, hPm⟩ := hP k r Wp Wq D (tsupport φ₀) {g} hφc isCompact_singleton
    (Set.singleton_subset_iff.2 hg)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have hfin : D.μSS P < ⊤ := by
    show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) P < ⊤
    exact hPc.measure_lt_top
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hφ' : Continuous (fun x : Mt k r => φ₀ (Matrix.of x)) :=
    hφ.comp (continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i))
  have hmeasφ : Measurable (fun x : Mt k r => φ₀ (Matrix.of x)) := hφ'.measurable
  have hmeas : Measurable (fun p : B.SS k r => φ₀ (B.sgs p g)) := by
    have h1 : Measurable (fun p : B.SS k r => Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF (p, (g : Mt k r))) :=
      Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.sgF_meas.comp (measurable_id.prodMk measurable_const)
    exact hmeasφ.comp h1
  have hind : Integrable (P.indicator fun _ : B.SS k r => M) D.μSS :=
    (integrable_indicator_iff hPc.isClosed.measurableSet).2 (integrableOn_const hfin.ne)
  refine hind.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · rw [Set.indicator_of_mem hpP]; exact hM _
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPm p hp g rfl (subset_tsupport _ hne))
    rw [h0, norm_zero, Set.indicator_of_notMem hpP]

theorem averaging_integrability_holds : ACInt := aCInt_of_proper averaging_properness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpOfPair
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAStarOp_of_pairL (h : SA.SAPairL) : JAStarOp :=
  SA.jAStarOp_of_parts SA.model_adjoint_identity_holds self_adjoint_section_holds h SA.fundamental_quadratic_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
end

