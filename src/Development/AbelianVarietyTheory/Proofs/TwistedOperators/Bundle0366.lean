module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockRealPointTransportContinuousIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransport

variable {D : D7}

def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

def cf (b b' : Bool) (c : ℂ) : ℂ := (c.re : ℂ) + ((sg b * sg b' * c.im : ℝ) : ℂ) * Complex.I

theorem cf_cf (b b' : Bool) (c : ℂ) : cf b b' (cf b b' c) = c := by
  have h : sg b * sg b' * (sg b * sg b') = 1 := by
    rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]
  apply Complex.ext <;> simp [cf, h, ← mul_assoc]

theorem continuous_cf (b b' : Bool) : Continuous (cf b b') := by
  unfold cf; fun_prop

theorem jm_mul_single_mul_jm {m n : ℕ} (εB : Fin m → Bool) (εA : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm εB * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm εA =
      Matrix.single i j (((sg (εB i) * sg (εA j) : ℝ)) : ℂ) := by
  ext a b
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, sg]
  by_cases ha : i = a <;> by_cases hb : j = b <;> subst_vars <;> simp_all <;> split_ifs <;> simp

variable {S T : HSp D}

theorem det_fr_unit {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) : IsUnit (A.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)

theorem unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    unitMap (A.onb τ) (B.onb τ) i j = (B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ := by
  simp only [unitMap, GlobalTheory.ChainFr.Fr.onb, Matrix.nonsing_inv_nonsing_inv _ (det_fr_unit A τ)]

theorem cplxO_unitMap_fr (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (i : Fin T.rank)
    (j : Fin S.rank) :
    cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j) =
      (B.fr τ)⁻¹ * Matrix.single i j ((((sg (B.ε τ i) * sg (A.ε τ j) : ℝ)) : ℂ) * Complex.I) * A.fr τ := by
  rw [unitMap_fr]
  have e : B.cart τ * ((B.fr τ)⁻¹ * Matrix.single i j (1 : ℂ) * A.fr τ) * A.cart τ =
      (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
    simp only [GlobalTheory.ChainFr.Fr.cart, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
      Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit A τ)]
  rw [cplxO, e, jm_mul_single_mul_jm, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_comm]

theorem fockMat_eq (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) (z : Fin T.rank → Fin S.rank → ℂ) :
    fockMat A B τ z = (B.fr τ)⁻¹ * Matrix.of (fun i j => cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
  have ht : ∀ i j, (((z i j).re : ℂ) • unitMap (A.onb τ) (B.onb τ) i j +
      ((z i j).im : ℂ) • cplxO (A.cart τ) (B.cart τ) (unitMap (A.onb τ) (B.onb τ) i j)) =
      (B.fr τ)⁻¹ * Matrix.single i j (cf (B.ε τ i) (A.ε τ j) (z i j)) * A.fr τ := by
    intro i j
    rw [cplxO_unitMap_fr, unitMap_fr, ← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_smul,
      ← Matrix.add_mul, ← Matrix.mul_add, Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 3
    simp only [cf, smul_eq_mul, mul_one, Complex.ofReal_mul]
    ring
  rw [fockMat]
  simp only [ht]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
  congr 2
  conv_rhs => rw [Matrix.matrix_eq_sum_single (Matrix.of _)]
  simp only [Matrix.of_apply]

def fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : Fin T.rank → Fin S.rank → ℂ :=
  fun i j => cf (B.ε τ i) (A.ε τ j) ((B.fr τ * X * (A.fr τ)⁻¹) i j)

theorem fockInvMat_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (z : Fin T.rank → Fin S.rank → ℂ) : fockInvMat A B τ (fockMat A B τ z) = z := by
  funext i j
  rw [fockInvMat, fockMat_eq]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (det_fr_unit B τ),
    Matrix.mul_nonsing_inv _ (det_fr_unit A τ), Matrix.mul_one, Matrix.of_apply, cf_cf]

theorem fockMat_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau)
    (X : Matrix (Fin T.rank) (Fin S.rank) ℂ) : fockMat A B τ (fockInvMat A B τ X) = X := by
  rw [fockMat_eq]
  have e : (Matrix.of fun i j => cf (B.ε τ i) (A.ε τ j) (fockInvMat A B τ X i j)) = B.fr τ * X * (A.fr τ)⁻¹ := by
    ext i j; simp only [Matrix.of_apply, fockInvMat, cf_cf]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (det_fr_unit A τ), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (det_fr_unit B τ)]

theorem continuous_fockMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockMat A B τ) := by
  unfold fockMat; fun_prop

theorem continuous_fockInvMat (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (τ : D.what₂.Tau) :
    Continuous (fockInvMat A B τ) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_cf _ _).comp
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)

def fockInv (θ : InfFam D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (w : WO S T) :
    VCx D.what₂.Tau S.rank T.rank :=
  fun τ => fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S w τ)

theorem fockInv_fockPt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fockInv θ A B (fockPt σ A B z) = z := by
  funext τ
  have e : GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ = fockMat A B τ (z τ) := congrFun (h.pi_iota T S _) τ
  show fockInvMat A B τ (GlobalTheory.FockCompare.piW θ T S (fockPt σ A B z) τ) = z τ
  rw [e, fockInvMat_fockMat]

theorem fockPt_fockInv {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) {w : WO S T} (hw : w.map (finPart D) = 0) :
    fockPt σ A B (fockInv θ A B w) = w := by
  have e : (fun τ => fockMat A B τ (fockInv θ A B w τ)) = GlobalTheory.FockCompare.piW θ T S w :=
    funext fun τ => fockMat_fockInvMat A B τ _
  rw [fockPt, e]
  exact h.iota_pi hw

theorem fockPt_transport : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), Continuous (fockPt σ A B) ∧
      (∀ w : WO S T, w.map (finPart D) = 0 → ∃ z, fockPt σ A B z = w) ∧
      ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g → ∃ (m : Measure (WO S T)) (α : WO S T → ℂ),
        SFinite m ∧ Integrable α m ∧ ∀ H : WO S T → ℂ, ∫ w, α w * H w ∂m = ∫ z, g z * H (fockPt σ A B z) := by
  intro D θ σ h S T A B
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : T2Space (WO S T) := (GlobalTheory.MixModel.lattice_Mx D T.rank S.rank).2.2.2.1
  have hc : Continuous (fockPt σ A B) :=
    (h.continuous_iota T S).comp (continuous_pi fun τ => (continuous_fockMat A B τ).comp (continuous_apply τ))
  have hic : Continuous (fockInv θ A B) := continuous_pi fun τ =>
    (continuous_fockInvMat A B τ).comp ((continuous_apply τ).comp (GlobalTheory.FockCompare.continuous_pi' h.inf T S))
  have hl : Function.LeftInverse (fockInv θ A B) (fockPt σ A B) := fun z => fockInv_fockPt h A B z
  have hr : Set.range (fockPt σ A B) = {w | fockPt σ A B (fockInv θ A B w) = w} := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg (fockPt σ A B) (hl z)
    · intro hw
      exact ⟨_, hw⟩
  have hme : MeasurableEmbedding (fockPt σ A B) :=
    MeasurableEmbedding.of_measurable_inverse hc.measurable
      (by rw [hr]; exact (isClosed_eq (hc.comp hic) continuous_id).measurableSet) hic.measurable hl
  refine ⟨hc, fun w hw => ⟨_, fockPt_fockInv h A B hw⟩, fun g hg => ?_⟩
  haveI : SigmaFinite (volume : Measure (Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin T.rank → Fin S.rank → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (VCx D.what₂.Tau S.rank T.rank)) := inferInstance
  refine ⟨Measure.map (fockPt σ A B) volume, g ∘ fockInv θ A B, MeasureTheory.Measure.instSFiniteMap _ _, ?_, fun H => ?_⟩
  · rw [hme.integrable_map_iff]
    have e : (g ∘ fockInv θ A B) ∘ fockPt σ A B = g := funext fun z => congrArg g (hl z)
    rw [e]; exact hg
  · rw [hme.integral_map]
    simp only [Function.comp_apply, hl _]

end GlobalTheory.FockTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.FrameChange

variable {D : D7}

theorem sign_eq_of_ne_zero {n : ℕ} {ε ε' : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * x = x * Formalism.REAL.Jm ε') {a i : Fin n} (hx : x a i ≠ 0) : ε a = ε' i := by
  have hc := congrFun (congrFun h a) i
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_contra hne
  apply hx
  cases h1 : ε a <;> cases h2 : ε' i <;> simp only [h1, h2] at hc hne
  · exact (hne trivial).elim
  · simp at hc; linear_combination -hc / 2
  · simp at hc; linear_combination hc / 2
  · exact (hne trivial).elim

theorem Jm_mul_fr {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) (h : Y.cart τ = X.cart τ) :
    Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) := by
  unfold Fr.cart at h
  calc Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹)
      = (X.fr τ * (X.fr τ)⁻¹) * Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) := by
        rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.one_mul]
    _ = X.fr τ * ((X.fr τ)⁻¹ * Formalism.REAL.Jm (X.ε τ) * X.fr τ) * (Y.fr τ)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X.fr τ * ((Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * Y.fr τ) * (Y.fr τ)⁻¹ := by rw [h]
    _ = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * (Y.fr τ * (Y.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.mul_one]

theorem fr_mul_inv_mul {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) :
    X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = 1 := by
  calc X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = X.fr τ * ((Y.fr τ)⁻¹ * Y.fr τ) * (X.fr τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.mul_one, GlobalTheory.CompactFockAction.fr_mul_inv]

section Coef

variable {V W : HSp D}

def coef (A A' : Fr V) (B B' : Fr W) (v : FVar D W.rank V.rank) (p : Fin W.rank × Fin V.rank) : ℂ :=
  if B'.ε v.1 v.2.1 = A'.ε v.1 v.2.2 then
    (B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2
  else starRingEnd ℂ ((B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2)

def sub (A A' : Fr V) (B B' : Fr W) : PolF D W.rank V.rank →ₐ[ℂ] PolF D W.rank V.rank :=
  MvPolynomial.aeval fun v => ∑ p, coef A A' B B' v p • (MvPolynomial.X (v.1, p.1, p.2) : PolF D W.rank V.rank)

end Coef

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem onb_eq (X Y : Fr V) (τ : D.what₂.Tau) : Y.onb τ = X.onb τ * (X.fr τ * (Y.fr τ)⁻¹) := by
  unfold Fr.onb
  rw [← Matrix.mul_assoc, GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.one_mul]

theorem inv_fr_mul (X Y : Fr V) (τ : D.what₂.Tau) : (X.fr τ * (Y.fr τ)⁻¹)⁻¹ = Y.fr τ * (X.fr τ)⁻¹ :=
  Matrix.inv_eq_left_inv (fr_mul_inv_mul Y X τ)

theorem aPlusAll_change (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) (v : FVar D W.rank V.rank)
    (g : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) :
    aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A'.onb B'.onb v g =
      ∑ p, coef A A' B B' v p •
        aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A.onb B.onb (v.1, p.1, p.2) g := by
  obtain ⟨ρ, i, j⟩ := v
  simp only [aPlusAll]
  rw [onb_eq A A' ρ, onb_eq B B' ρ, GlobalTheory.FockBasis.unitMap_mul, inv_fr_mul,
    GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.CompactFockAction.Jm_single A B ρ a b)]
  congr 1
  simp only [coef]
  by_cases hx : (B.fr ρ * (B'.fr ρ)⁻¹) a i * (A'.fr ρ * (A.fr ρ)⁻¹) j b = 0
  · simp [hx]
  · have h1 := sign_eq_of_ne_zero (Jm_mul_fr B B' ρ (hB ρ)) (left_ne_zero_of_mul hx)
    have h2 := sign_eq_of_ne_zero (Jm_mul_fr A' A ρ (hA ρ).symm) (right_ne_zero_of_mul hx)
    rw [h1, ← h2]
    simp only [decide_eq_true_eq]

theorem ptF_sub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (Q : PolF D W.rank V.rank) :
    ptF ψ θ A' B' f Q = ptF ψ θ A B f (sub A A' B B' Q) := by
  have e1 : A'.cart = A.cart := funext hA
  have e2 : B'.cart = B.cart := funext hB
  have hS := GlobalTheory.CompactFockAction.cart_isCartanInv A
  have hT := GlobalTheory.CompactFockAction.cart_isCartanInv B
  unfold ptF pureTensorO sub
  rw [e1, e2]
  have hAt : ∀ X Y i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ X Y i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (f + f') =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f +
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f' :=
    fun _ _ _ _ _ h h' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ X Y i (a : ℂ) f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (a • f) =
      a • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f :=
    fun _ _ _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ X Y i j f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j f) =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ i j _ h => GlobalTheory.FockSubst.aPlus_comm (sS := A.cart) (sT := B.cart) hψ hθ i.1 _ hS hT j.1 _ h
  exact GlobalTheory.FockSubst.pure_subst (P := IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (hAt _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hAt _ _) (Ac _ _)
    (Aadd _ _) (Asm _ _) (coef A A' B B') (fun v p => (v.1, p.1, p.2))
    (aPlusAll_change hψ hθ A A' B B' hA hB) hf Q

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D}

theorem coef_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ)
    (v : FVar D W.rank V.rank) (q : Fin W.rank × Fin V.rank) :
    ∑ p, coef X' X Y' Y v p * coef X X' Y Y' (v.1, p.1, p.2) q = if q = (v.2.1, v.2.2) then 1 else 0 := by
  obtain ⟨ρ, i, j⟩ := v

  have hK : ∀ c d, (∑ a, (Y'.fr ρ * (Y.fr ρ)⁻¹) a d * (Y.fr ρ * (Y'.fr ρ)⁻¹) c a) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul Y Y' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hU : ∀ c d, (∑ b, (X.fr ρ * (X'.fr ρ)⁻¹) c b * (X'.fr ρ * (X.fr ρ)⁻¹) b d) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul X X' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hprod : (∑ p : Fin W.rank × Fin V.rank, ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
      ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) = if q = (i, j) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (X.fr ρ * (X'.fr ρ)⁻¹) j b) *
        ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) =
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a) *
        ((X.fr ρ * (X'.fr ρ)⁻¹) j b * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) := fun a b => by ring
    simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, hU, hK]
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : q1 = i <;> by_cases h2 : j = q2 <;> (try simp [h1, h2]) <;> (try exact fun h => h1 h.symm) <;>
      (try exact fun h => h2 h.symm)

  have hterm : ∀ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q =
      if Y.ε ρ i = X.ε ρ j then
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)
      else starRingEnd ℂ (((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) := by
    intro p
    simp only [coef]
    by_cases hx : (Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2 = 0
    · simp [hx]
    · have h1 := sign_eq_of_ne_zero (Jm_mul_fr Y' Y ρ (hY ρ).symm) (left_ne_zero_of_mul hx)
      have h2 := sign_eq_of_ne_zero (Jm_mul_fr X X' ρ (hX ρ)) (right_ne_zero_of_mul hx)
      rw [h1, ← h2]
      split_ifs <;> simp [map_mul]
  by_cases hs : Y.ε ρ i = X.ε ρ j
  · simp only [hterm, hs, if_true]
    exact hprod
  · simp only [hterm, hs, if_false]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hprod]
    split_ifs <;> simp

theorem sub_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ) :
    (sub X X' Y Y').comp (sub X' X Y' Y) = AlgHom.id ℂ (PolF D W.rank V.rank) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  obtain ⟨ρ, i, j⟩ := v
  calc sub X X' Y Y' (sub X' X Y' Y (MvPolynomial.X (ρ, i, j)))
      = ∑ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p •
          ∑ q : Fin W.rank × Fin V.rank, coef X X' Y Y' (ρ, p.1, p.2) q •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [sub, MvPolynomial.aeval_X, map_sum, map_smul]
    _ = ∑ q : Fin W.rank × Fin V.rank, (∑ p : Fin W.rank × Fin V.rank,
          coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
    _ = ∑ q : Fin W.rank × Fin V.rank, (if q = (i, j) then (1 : ℂ) else 0) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [coef_comp X X' Y Y' hX hY (ρ, i, j)]
    _ = MvPolynomial.X (ρ, i, j) := by
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [hq]
        · simp

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

theorem ptF_frame_change : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  intro D ψ θ hψ hθ V W A A' B B' hA hB
  let e : PolF D W.rank V.rank ≃ₐ[ℂ] PolF D W.rank V.rank :=
    AlgEquiv.ofAlgHom (sub A' A B' B) (sub A A' B B') (sub_comp A' A B' B (fun τ => (hA τ).symm) fun τ => (hB τ).symm)
      (sub_comp A A' B B' hA hB)
  refine ⟨e.toLinearEquiv, fun f hf P => ?_⟩
  exact (ptF_sub hψ hθ A' A B' B (fun τ => (hA τ).symm) (fun τ => (hB τ).symm) hf P).symm

end GlobalTheory.FrameChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  first | exact @GlobalTheory.TwistBlockK.atK_sub_one | exact GlobalTheory.TwistBlockK.atK_sub_one | (intros; apply GlobalTheory.TwistBlockK.atK_sub_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory

theorem hasSum_pow_div_factorial_exp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem hasSum_fin_prod_pow_div_factorial_exp : ∀ (n : ℕ) (x : Fin n → ℂ),
    HasSum (fun f : Fin n → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro n
  induction n with
  | zero =>
    intro x
    have := hasSum_unique (fun f : Fin 0 → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
    simpa using this
  | succ n ih =>
    intro x
    have h := hasSum_pow_div_factorial_exp (x 0)
    have ht := ih (Fin.tail x)
    have h1 : Summable (fun i => ‖x 0 ^ i / (i.factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 h.summable
    have h2 : Summable (fun f : Fin n → ℕ => ‖∏ k, Fin.tail x k ^ f k / ((f k).factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 ht.summable
    have h0 := summable_mul_of_summable_norm h1 h2
    have h3 := HasSum.mul h ht h0
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff, Fin.sum_univ_succ,
      Complex.exp_add]
    convert h3 using 1
    all_goals first
      | rfl
      | (funext p; simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail] <;> ring)

theorem hasSum_finsupp_prod_pow_div_factorial_exp : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ),
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro κ _ x
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hA := hasSum_fin_prod_pow_div_factorial_exp (Fintype.card κ) (fun i => x (e.symm i))
  have hsum : (∑ i, x (e.symm i)) = ∑ k, x k := Equiv.sum_comp e.symm x
  rw [hsum] at hA
  have hB : HasSum (fun f : κ → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
    rw [← ((Equiv.arrowCongr e (Equiv.refl ℕ)).symm).hasSum_iff]
    convert hA using 1
    funext g
    simp only [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def, id]
    exact (Equiv.prod_comp e.symm (fun k => x k ^ g (e k) / ((g (e k)).factorial : ℂ))).symm.trans
      (by simp)
  rw [← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).symm.hasSum_iff]
  convert hB using 1
  funext f
  simp only [Function.comp_apply]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

end GlobalTheory
end

