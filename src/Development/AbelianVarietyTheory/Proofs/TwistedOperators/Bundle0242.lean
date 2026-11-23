module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0229
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivConjFrameToRealLieLoweringOperatorEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

open GlobalTheory.HolRead GlobalTheory.HolRead.AdExt GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem conj_frame_eq {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ} (hd : IsUnit G.det) (hx : IsUnit x.det)
    (h : xᴴ * G * x = S) (hS : S * S = 1) (A : Matrix (Fin n) (Fin n) ℂ) :
    G⁻¹ * (x * A * x⁻¹)ᴴ * G = x * (S * Aᴴ * S) * x⁻¹ := by
  have hxi : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hx
  have hix : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hx
  have hxh : ∀ M : Matrix (Fin n) (Fin n) ℂ, xᴴ * (x⁻¹ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hix, conjTranspose_one, Matrix.one_mul]
  have hGi : G⁻¹ = x * S * xᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    calc x * S * xᴴ * G = x * S * (xᴴ * G * x) * x⁻¹ := by
          simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
      _ = 1 := by rw [h, Matrix.mul_assoc x S S, hS, Matrix.mul_one, hxi]
  have hG : G = x⁻¹ᴴ * S * x⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, hxi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hxi, conjTranspose_one, Matrix.one_mul]
  rw [hGi, hG]
  simp only [conjTranspose_mul, Matrix.mul_assoc, hxh]

theorem sgn_mul_self (p a : ℕ) : (sgn p a : ℝ) * sgn p a = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem diag_single_diag {n : ℕ} (s : Fin n → ℝ) (c d : Fin n) :
    (diagonal fun a => ((s a : ℝ) : ℂ)) * (Matrix.single c d (1 : ℂ))ᴴ * (diagonal fun a => ((s a : ℝ) : ℂ)) =
      (s c * s d) • Matrix.single d c (1 : ℂ) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.smul_apply]
  by_cases hi : d = i <;> by_cases hj : c = j <;> subst_vars <;> simp [*]
  ring

variable {D : D7} {S T : HSp D}

theorem conjAt_single (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau)
    (c d : Fin T.rank) : conjAt T ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) =
      (-(sgn C.X.p0 c * sgn C.X.p0 d) : ℝ) • (B ρ * Matrix.single d c 1 * (B ρ)⁻¹) := by
  unfold Ctx.IsB sgnM at hB
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have hsd := diag_single_diag (fun a : Fin T.rank => sgn C.X.p0 (a : ℕ)) c d
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hsd, Matrix.mul_smul, Matrix.smul_mul, neg_smul]

theorem conjL_I_smul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) :
    conjL (I • Z) = -(I • conjL Z) := by
  funext τ a b
  change conj (I * Z τ a b) = -(I * conj (Z τ a b))
  rw [map_mul, Complex.conj_I]
  ring

theorem conjL_unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) :
    conjL (unitFr τ c d) = unitFr τ c d := by
  funext τ' a b
  change conj (unitFr τ c d τ' a b) = unitFr τ c d τ' a b
  simp only [unitFr]
  split_ifs <;> simp

theorem toLie_I_conjL (C : Ctx S T) (R : RealPoints C.θ T) {B : C.Bas} (hB : C.IsB B) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ unitLie C.X) : toLie R B (fun ρ => C.m.e ρ) (I • conjL Z) = 0 := by
  unfold Ctx.IsB sgnM at hB
  funext ρ
  apply Subtype.ext
  rw [toLie_I]
  have hx : IsUnit (B ρ).det := isUnit_det_B C hB ρ
  have hS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [← Complex.ofReal_mul, sgn_mul_self, Complex.ofReal_one]
  have key : (mat (conjL Z) (C.m.e ρ))ᴴ * (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) +
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * mat (conjL Z) (C.m.e ρ) = 0 := by
    have hZe := hZ (C.m.e ρ)
    rw [mat_conjL]
    ext i j
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin T.rank) ℂ => (starRingEnd ℂ) (M i j)) hZe
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.map_apply, Matrix.zero_apply, ← starRingEnd_apply, map_add, map_mul, map_zero,
      Complex.conj_conj, Complex.conj_ofReal] at h1 ⊢
    linear_combination h1
  have hMS : (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) * (mat (conjL Z) (C.m.e ρ))ᴴ *
      (diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ)) = -mat (conjL Z) (C.m.e ρ) := by
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left key, Matrix.mul_neg, ← Matrix.mul_assoc, hS,
      Matrix.one_mul]
  simp only [conjAt]
  rw [conj_frame_eq (R.1 ρ).2 hx (hB ρ) hS, hMS, Matrix.mul_neg, Matrix.neg_mul, neg_neg, sub_self, smul_zero]
  rfl

theorem fderiv_toLieC_eq_zero : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (φ : GA D T → ℂ), LowKilled C.θ T B φ → ∀ (g : GA D T) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB φ hφ g ρ c d hcd Z Z' hZ hZ' hsum
  obtain ⟨-, hk⟩ := hφ
  by_cases hf : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  swap
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp

  have hZ1 : toLieC C R B Z = toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d - I • Z' := by rw [← hsum, add_sub_cancel_right]
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_unitFr, conjL_I_smul, map_neg,
      toLie_I_conjL C R hB hZ', neg_zero, sub_zero]
  have hZ2 : toLieC C R B Z' = toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) := by
    have e : Z' = I • Z - I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d := by
      rw [← hsum, smul_add, smul_smul, I_mul_I, neg_one_smul]
      abel
    rw [e]
    simp only [toLieC, LinearMap.comp_apply, map_sub, conjL_I_smul, conjL_unitFr, map_neg,
      toLie_I_conjL C R hB hZ, neg_zero, zero_sub, neg_neg]
  rw [hZ1, hZ2]

  have hs : ∀ a : ℕ, sgn C.X.p0 a = 1 ∨ sgn C.X.p0 a = -1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  have hε : (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) * (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) =
      (1 : ℝ) := by
    have h1 := sgn_mul_self C.X.p0 c
    have h2 := sgn_mul_self C.X.p0 d
    linear_combination (sgn C.X.p0 (d : ℕ) * sgn C.X.p0 (d : ℕ)) * h1 + h2
  have hI : (1 / (2 * I) : ℂ) = -(I / 2) := by
    rw [one_div, mul_inv, Complex.inv_I]
    ring

  have hA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_val]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have hBm : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ).1 := by
    rw [toLie_I]
    simp only [mat_unitFr, if_true]
    rw [conjAt_single C R hB ρ c d, conjAt_single C R hB ρ d c, hI]
    rcases hs c with h1 | h1 <;> rcases hs d with h2 | h2 <;> rw [h1, h2] <;> module
  have memA : (1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hA]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2
  have memB : (1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹)) ∈
      lieU (gramAt D T ρ) := by
    rw [hBm]
    exact (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
      toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) ρ).2

  have hN1 : toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memA⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memA⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hA, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_val]
      simp [mat_unitFr, hρ, conjAt]
  have hN2 : toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) =
      HSMul.hSMul (α := ℝ) (β := GlobalTheory.SmoothForms.LieN T) (γ := GlobalTheory.SmoothForms.LieN T)
        (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ))) (atPlace T ρ ⟨_, memB⟩) := by
    funext ρ'
    apply Subtype.ext
    change (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) ρ').1 =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • ((atPlace T ρ ⟨_, memB⟩ : GlobalTheory.SmoothForms.LieN T) ρ').1
    by_cases hρ : ρ' = ρ
    · subst hρ
      simp only [atPlace, Pi.single_eq_same]
      rw [hBm, smul_smul, hε, one_smul]
    · simp only [atPlace, Pi.single_eq_of_ne hρ]
      rw [toLie_I]
      simp [mat_unitFr, hρ, conjAt]
  have hk1 := congrFun (hk ρ d c hcd) g
  simp only [RderC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk1
  have e1 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / 2 : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ + conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN1]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memA⟩))
  have e2 : (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0)
      (toLie R B (fun ρ => C.m.e ρ) (I • GlobalTheory.HolRead.unitFr (C.m.e ρ) c d)) =
      (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) •
        Rder C.θ T ρ ((1 / (2 * I) : ℂ) • (B ρ * single d c 1 * (B ρ)⁻¹ - conjAt T ρ (B ρ * single d c 1 * (B ρ)⁻¹))) φ g := by
    rw [hN2]
    exact (map_smul _ _ _).trans (congrArg (fun z : ℂ => (-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) • z)
      (fderiv_atPlace R g hf ρ ⟨_, memB⟩))
  rw [e1, e2]
  simp only [Complex.real_smul]
  linear_combination (((-(sgn C.X.p0 (c : ℕ) * sgn C.X.p0 (d : ℕ)) : ℝ) : ℂ)) * hk1

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoords

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem trace_tmul_base {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem repr_eq_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (x : E) (l : ι) :
    Algebra.trace F E
        ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l * x) = b.repr x l := by
  have h := congrArg (Algebra.traceForm F E
      ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l)) (b.sum_repr x)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Algebra.traceForm_apply] at h
  exact h.symm

theorem coords_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (d : ℕ) (c e : Fin d → E), ∀ w : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w =
        ∑ l, sndA F (Algebra.trace (AF F) (AF F ⊗[F] E) (((1 : AF F) ⊗ₜ[F] c l) * w)) ⊗ₜ[F] e l := by
  classical
  let b := Module.finBasis F E
  refine ⟨_, fun l => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l, b, ?_⟩
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul_base, map_mul,
      AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    simp only [repr_eq_trace]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, ← Finset.sum_add_distrib, TensorProduct.add_tmul]

end GlobalTheory.TwistCoords

namespace GlobalTheory.TwistCoords

theorem finPart_eq_sum_trace :
    ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w =
      ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  intro D
  obtain ⟨d, c, e, h⟩ := coords_gen D.host.F D.host.E
  exact ⟨d, c, e, fun w => h w⟩

end GlobalTheory.TwistCoords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupportOfAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem adjZ_eq_neg_of_mem_upq {p q : ℕ} {Z : Mat p q} (h : Z ∈ upq p q) : adjZ Z = -Z := by
  have h0 : Zᴴ * Jm p q + Jm p q * Z = 0 := h
  have h1 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left h0
  rw [adjZ, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc,
    GlobalTheory.InvPairingTensor.Jm_mul_self, Matrix.one_mul]

theorem finiteSupport_of_admissible :
    ∀ (p q r s : ℕ) (T : GrpData r s) (R : DSRep T), Formalism.MainNotions.SchurIrreducible.AdmGK R.HK → FiniteSupport p q R := by
  intro p q r s T R hA A _ _ B hB P
  refine GlobalTheory.InvPairingTensor.exists_finiteDimensional_kill R hA B (fun Z hZ Q y => ?_) P
  rw [hB Z Q y, adjZ_eq_neg_of_mem_upq hZ, map_neg, LinearMap.neg_apply, map_neg, neg_add_cancel]

end GlobalTheory.Chain.IoLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

theorem jacGrp_besGrp_haar : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  intro D S S₀ A L ρ d o ν 𝓝 hν
  have hNc : IsClosed (flagN d : Set (GA D S)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag S (isIsoSub_e d)
  have hνH : ν.IsHaarMeasure := hν.1
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn (o.emb (h, 1))
  have hmA : ∀ h, ν.map (fun n : flagN d => embA d o h * n.1 * (embA d o h)⁻¹) = ν.map Subtype.val := fun h =>
    GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH (o.emb (h, 1))
  refine ⟨⟨GlobalTheory.jacGrp_isClosed D S S₀ ρ d, fun μ hμ => ?_⟩, GlobalTheory.BesClosed.besGrp_isClosed D S S₀ A L ρ d o, fun μ hμ => ?_⟩
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }

end GlobalTheory.MixPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorLevelMultiplicitySpaceMemGoodRows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct Pointwise

namespace GlobalTheory.ProjLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_isConjPl_of_div {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : Pl D.host.E}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ IsConjPl w w' := by
  intro hc
  have hov : ∀ {j : Fin 2} {u : Pl D.host.E}, P.Div j u → ((D.host.g j : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
    intro j u hu
    have h1 := P.pb_over j
    rw [← hu] at h1
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g j : ℕ) : 𝓞 D.host.K) ∈ u.asIdeal := h1
    rwa [map_natCast] at this
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext (hzv.trans ((bridge_star_holds D.R D.host _).trans
      (D.host.conj.apply_symm_apply (y : D.host.E))))
    exact e ▸ hz
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • w.asIdeal = w'.asIdeal := hmax.eq_of_le w'.isPrime.ne_top hle
  have hm := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w (hov hw)).2.2.2
    (P.pb k) (P.pb_over k) w' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w w').2 heq)
  have hg : D.host.g k = D.host.g k' :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w' hm.1).1.symm.trans
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k') (D.host.g_prime k') (D.nd.g_split k') w' (hov hw')).1
  obtain rfl : k = k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
  exact hm.2.1 hw hw'

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end

end GlobalTheory.ProjLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stable_orbital_integrals_well_defined : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  first | exact @GlobalTheory.TrPhiOK.phiOK_local | exact GlobalTheory.TrPhiOK.phiOK_local | (intros; apply GlobalTheory.TrPhiOK.phiOK_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.NoLowPairing

theorem no_pairing_of_noLow : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK → NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ b : Formalism.BasicNotions.TH.Pol (p - i) (q - i) r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq r s, ∀ P y, b (fockAct2 (p - i) (q - i) r s Z P) y + b P ((X.ds r s lam').HK.act Z y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq b hb
  exact GlobalTheory.NoInvPairing.eq_zero_of_noIntw' (X.ds r s lam') (X.fock (p - i) (q - i) r s) hadm
    (fun M f hf => hlow i hi hip hiq M f hf) b hb

end GlobalTheory.NoLowPairing
end

