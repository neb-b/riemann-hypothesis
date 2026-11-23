module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.Refock

variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem gram_reS : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem hO_trace (S T : HSp D) (x y : WO S T) : hO S T x y =
    trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem inv_eq_of_gram_conjTranspose_change {n : ℕ} {G' G P Pinv : Matrix (Fin n) (Fin n) D.host.E} (h : G' = Pᴴ * G * P)
    (hP : P * Pinv = 1) : G'⁻¹ = Pinv * G⁻¹ * Pinvᴴ := by
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_eq_right_inv hP, Matrix.mul_assoc]

theorem gram_reS_inv : (reS S b).gram⁻¹ = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ :=
  inv_eq_of_gram_conjTranspose_change (gram_reS b) (frameMatrix_mul_frameMatrixInv b)

theorem map_conjTranspose_incA {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Mᴴ.map (incA D) = ((M.map (incA D)).map (cA D))ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, conjTranspose_apply, Matrix.transpose_apply]
  rfl

theorem adelicMap_inv_conjTranspose_congruence {n : ℕ} {G' G Pinv : Matrix (Fin n) (Fin n) D.host.E} (h : G'⁻¹ = Pinv * G⁻¹ * Pinvᴴ) :
    G'⁻¹.map (incA D) = Pinv.map (incA D) * G⁻¹.map (incA D) * ((Pinv.map (incA D)).map (cA D))ᵀ := by
  rw [h, Matrix.map_mul, Matrix.map_mul, map_conjTranspose_incA]

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (A Q : Matrix (Fin n) (Fin n) R)
    (Y X : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin m) (Fin m) R) :
    trace (Q * A * (Q.map c)ᵀ * (Y.map c)ᵀ * C * X) = trace (A * ((Y * Q).map c)ᵀ * C * (X * Q)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

theorem hO_reW (x y : WO (reS S b) T) : hO (reS S b) T x y = hO S T (reW S T b x) (reW S T b y) := by
  rw [hO_trace, hO_trace, adelicMap_inv_conjTranspose_congruence (gram_reS_inv b)]
  exact trace_inverseGram_conj_smul_eq (R := AE D) (cA D) (n := S.rank) (m := T.rank) _ _ _ _ _
end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T where
  toFun := reW S T b
  map_zero' := Matrix.zero_mul _
  map_add' := reW_add b

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ) (w₀ : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T w₀ (reF S T b f) = reF S T b (heisO ψ S T (reW S T b w₀) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, symplO, hO_reW, reW_add]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e := by
  show θ τ ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ e)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 e

theorem compAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : Mx D T.rank S.rank) :
    compAt θ τ (reW S T b x) = compAt θ τ x * (frPinv S b).map (tauE D τ) := by
  have e1 : ∀ {m n : ℕ} (w : Mx D m n), compAt θ τ w = w.map ((θ τ).comp (infPart D)) := fun _ => rfl
  show compAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))) = _
  rw [e1, e1, Matrix.map_mul, Matrix.map_map]
  congr 2
  funext e
  exact theta_incA hθ τ e

theorem finPart_reW (x : Mx D T.rank S.rank) (hx : x.map (finPart D) = 0) :
    (reW S T b x).map (finPart D) = 0 := by
  show (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))).map (finPart D) = 0
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem tauFrame_mul_tauFrameInv (τ : D.what₂.Tau) :
    (frP S b).map (tauE D τ) * (frPinv S b).map (tauE D τ) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cplxO_mul {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) : cplxO 1 s (z * M) = cplxO 1 s z * M := by
  simp only [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]

theorem continuous_reW : Continuous (reW S T b) :=
  continuous_id.matrix_mul continuous_const

theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) = lineAt θ τ z t := by
  have hL := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z * (frP S b).map (tauE D τ))
  have key := GlobalTheory.RealLineAt.lineAt_unique D θ hθ T.rank S.rank τ z
    ((reWHom (T := T) b).comp (lineAt θ τ (z * (frP S b).map (tauE D τ)))) (lineAt θ τ z)
    ⟨(continuous_reW b).comp hL.1, fun s => finPart_reW b _ (hL.2.1 s), fun s τ' => ?_⟩
    (GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z)
  · exact DFunLike.congr_fun key t
  · refine (compAt_reW b hθ τ' (lineAt θ τ (z * (frP S b).map (tauE D τ)) s)).trans ?_
    rw [hL.2.2 s τ']
    split_ifs
    · subst τ'
      rw [Matrix.smul_mul, Matrix.mul_assoc, tauFrame_mul_tauFrameInv, Matrix.mul_one]
    · exact Matrix.zero_mul _

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)
variable (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
include hθ

theorem dRho_reF (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ (reS S b) T) θ τ (z * (frP S b).map (tauE D τ)) (reF S T b f) =
      reF S T b (dRho (heisO ψ S T) θ τ z f) := by
  funext x
  have h : ∀ t : ℝ, heisO ψ (reS S b) T (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) (reF S T b f) x =
      heisO ψ S T (lineAt θ τ z t) f (reW S T b x) := fun t => by
    exact (congrFun (heisO_reF b ψ _ f) x).trans
      (congrArg (fun w => heisO ψ S T w f (reW S T b x)) (lineAt_reW b hθ τ z t))
  show deriv (fun t : ℝ => heisO ψ (reS S b) T (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) (reF S T b f) x) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f (reW S T b x)) 0
  simp only [h]

theorem aPlus_reF (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (f : WO S T → ℂ) :
    aPlus (heisO ψ (reS S b) T) θ τ (cplxO 1 s) (z * (frP S b).map (tauE D τ)) (reF S T b f) =
      reF S T b (aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f) := by
  have h1 := dRho_reF b ψ hθ τ z f
  have h2 : dRho (heisO ψ (reS S b) T) θ τ (cplxO 1 s (z * (frP S b).map (tauE D τ))) (reF S T b f) =
      reF S T b (dRho (heisO ψ S T) θ τ (cplxO 1 s z) f) :=
    (congrArg (fun w => dRho (heisO ψ (reS S b) T) θ τ w (reF S T b f)) (cplxO_mul s z _)).trans
      (dRho_reF b ψ hθ τ (cplxO 1 s z) f)
  simp only [aPlus, crea]
  rw [h1, h2, LinearMap.map_smul, LinearMap.map_sub, LinearMap.map_smul]

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem unitMap_re {m : ℕ} (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin m) (j : Fin S.rank) :
    unitMap ((frPinv S b).map (tauE D τ) * B) B' i j = unitMap B B' i j * (frP S b).map (tauE D τ) := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (tauFrame_mul_tauFrameInv b τ)]
  simp only [Matrix.mul_assoc]

theorem gramAt_reS (τ : D.what₂.Tau) :
    gramAt D (reS S b) τ = ((frP S b).map (tauE D τ))ᴴ * gramAt D S τ * (frP S b).map (tauE D τ) := by
  have e : ((frP S b).map (tauE D τ))ᴴ = (frP S b)ᴴ.map (tauE D τ) :=
    Matrix.ext fun i j => by simp [conjTranspose_apply, Formalism.IndefR.Eqv.tauE_star]
  refine (congrArg (fun M : Matrix (Fin S.rank) (Fin S.rank) D.host.E => M.map (tauE D τ)) (gram_reS b)).trans ?_
  show _ = _ * (S.gram).map (tauE D τ) * _
  rw [Matrix.map_mul, Matrix.map_mul, e]

theorem conjTranspose_gram_congruence_cancel {n : ℕ} (B P Pinv G : Matrix (Fin n) (Fin n) ℂ) (h : P * Pinv = 1) :
    (Pinv * B)ᴴ * (Pᴴ * G * P) * (Pinv * B) = Bᴴ * G * B := by
  have h' : Pinvᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h, conjTranspose_one]
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Pinv, h, Matrix.one_mul, ← Matrix.mul_assoc Pinvᴴ, h', Matrix.one_mul]

theorem opPow_comm {ι X Y : Type} (A : ι → (X → ℂ) → (X → ℂ)) (A' : ι → (Y → ℂ) → (Y → ℂ))
    (H : (X → ℂ) → (Y → ℂ)) (hA : ∀ i g, A' i (H g) = H (A i g)) (k : ι →₀ ℕ) (f : X → ℂ) :
    opPow A' k (H f) = H (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_comm' {ι X Y : Type} (A : ι → (X → ℂ) → (X → ℂ)) (A' : ι → (Y → ℂ) → (Y → ℂ))
    (H : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (hA : ∀ i g, A' i (H g) = H (A i g)) (f : X → ℂ) (P : MvPolynomial ι ℂ) :
    pureTensorL A' (H f) P = H (pureTensorL A f P) := by
  have e : pureTensorL A' (H f) = H ∘ₗ pureTensorL A f := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    rw [LinearMap.comp_apply, pureTensorL, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact opPow_comm A A' H hA k f
  rw [e, LinearMap.comp_apply]

theorem aPlusAll_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (k : FVar D T.rank S.rank) (g : WO S T → ℂ) :
    aPlusAll (heisO ψ (reS S b) T) θ (fun τ => cplxO 1 (sT τ)) (fun τ => (frPinv S b).map (tauE D τ) * BS τ) BT k
        (reF S T b g) = reF S T b (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) BS BT k g) :=
  (congrArg (fun w => aPlus (heisO ψ (reS S b) T) θ k.1 (cplxO 1 (sT k.1)) w (reF S T b g))
    (unitMap_re b k.1 (BS k.1) (BT k.1) k.2.1 k.2.2)).trans
    (aPlus_reF b ψ hθ k.1 (sT k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g)

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan


open Refock in
theorem pureTensorO_reF : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∃ BS' : D.what₂.Tau → Matrix (Fin (reS S b).rank) (Fin (reS S b).rank) ℂ, (∀ τ, (BS' τ)ᴴ * gramAt D (reS S b) τ * BS' τ = (BS τ)ᴴ * gramAt D S τ * BS τ) ∧ ∀ (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ (reS S b) T (fun _ => 1) sT BS' BT (reF S T b f) P = reF S T b (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P) := by
  intro D S T b ψ θ hθ BS
  refine ⟨fun τ => (frPinv S b).map (tauE D τ) * BS τ, fun τ => ?_, fun sT BT f P => ?_⟩
  · rw [gramAt_reS b τ]
    exact conjTranspose_gram_congruence_cancel _ _ _ _ (tauFrame_mul_tauFrameInv b τ)
  · exact pureTensorL_comm' _ _ (reF S T b) (fun k g => aPlusAll_reF b ψ hθ sT BT BS k g) f P

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaising
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.FockTDec

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

section General

variable {σ : Type}

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  zero_mem' := fun P => by simp
  add_mem' := fun {L L'} h h' P => by
    rw [LinearMap.add_apply]
    exact (totalDegree_add _ _).trans (max_le (h P) (h' P))
  smul_mem' := fun c L h P => by
    rw [LinearMap.smul_apply]
    exact (totalDegree_smul_le _ _).trans (h P)

theorem one_mem : (1 : Module.End ℂ (MvPolynomial σ ℂ)) ∈ nonRaising σ := fun _ => le_rfl

theorem mul_mem {L L' : Module.End ℂ (MvPolynomial σ ℂ)} (h : L ∈ nonRaising σ) (h' : L' ∈ nonRaising σ) :
    L * L' ∈ nonRaising σ := fun P => (h _).trans (h' P)

theorem totalDegree_X_mul_pderiv (x y : σ) (P : MvPolynomial σ ℂ) :
    (X x * pderiv y P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s y = 0
  · simp [h0]
  · have hs' : (Finsupp.single y 1) + (s - Finsupp.single y 1) = s := by
      rw [add_tsub_cancel_of_le]
      rw [Finsupp.single_le_iff]; omega
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    refine le_trans ?_ (le_totalDegree hs)
    have h1 := totalDegree_monomial_le (s - Finsupp.single y 1) (AddMonoidAlgebra.coeff P s * (s y : ℂ))
    have h2 : (s.sum fun _ e => e) = 1 + (s - Finsupp.single y 1).sum fun _ e => e := by
      conv_lhs => rw [← hs']
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [h2]
    exact Nat.add_le_add_left h1 1

theorem pderiv_mem (y : σ) : (pderiv y).toLinearMap ∈ nonRaising σ := by
  intro P
  change (pderiv y P).totalDegree ≤ _
  by_cases h : pderiv y P = 0
  · simp [h]
  · refine le_trans ?_ (totalDegree_X_mul_pderiv y y P)
    rw [totalDegree_mul_of_isDomain (X_ne_zero y) h]
    omega

theorem mul_pderiv_mem (x y : σ) :
    LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) * (pderiv y).toLinearMap ∈ nonRaising σ :=
  fun P => totalDegree_X_mul_pderiv x y P

theorem pderiv_mul_mem (x y : σ) :
    (pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) ∈ nonRaising σ := by
  classical
  intro P
  have e : ((pderiv y).toLinearMap * LinearMap.mulLeft ℂ (X x : MvPolynomial σ ℂ) :
      Module.End ℂ (MvPolynomial σ ℂ)) P = pderiv y (X x * P) := rfl
  rw [e]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_X_mul_pderiv x y P) ?_)
  by_cases h : x = y
  · subst h; rw [pderiv_X_self, mul_one]
  · rw [pderiv_X_of_ne h, mul_zero, totalDegree_zero]; exact Nat.zero_le _

end General

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i l : Fin b) (j : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' l ≠ ε j then X (τ, i, j) * X (τ, l, j) else 0

theorem sgn_mul_self (e : Bool) : sgn e * sgn e = 1 := by
  cases e <;> simp [sgn]

theorem term_mem (i l : Fin b) (j : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  rw [smul_mul_smul_comm, sgn_mul_self, one_smul]
  by_cases hi : ε' i = ε j <;> by_cases hl : ε' l = ε j
  · simp only [hi, hl, if_true, ne_eq, not_true, and_false, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero]
    exact mul_pderiv_mem _ _
  · simp only [hi, hl, if_true, ne_eq, not_false_iff, and_self, if_false]
    rw [LinearMap.mulLeft_mul, Module.End.mul_eq_comp, sub_self]
    exact Submodule.zero_mem _
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (mul_mem (pderiv_mem _) (pderiv_mem _))
  · simp only [hi, hl, if_true, false_and, if_false, LinearMap.mulLeft_zero_eq_zero, sub_zero, neg_mul]
    exact Submodule.neg_mem _ (pderiv_mul_mem _ _)

def quadAll (Y : Matrix (Fin b) (Fin b) ℂ) : PolF D b a :=
  ∑ i, ∑ l, Y i l • ∑ j, quad τ ε ε' i l j

theorem quadAll_hom (Y : Matrix (Fin b) (Fin b) ℂ) : (quadAll τ ε ε' Y).IsHomogeneous 2 := by
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => ?_)
  unfold quad
  split_ifs
  · exact (isHomogeneous_X ℂ _).mul (isHomogeneous_X ℂ _)
  · exact Submodule.zero_mem _

theorem fockQuadraticPart_ne_zero_of_offBlock_entry (Y : Matrix (Fin b) (Fin b) ℂ) (i₀ l₀ : Fin b) (j₀ : Fin a) (hi : ε' i₀ = ε j₀)
    (hl : ε' l₀ ≠ ε j₀) (hY : Y i₀ l₀ ≠ 0) : quadAll τ ε ε' Y ≠ 0 := by
  classical
  intro h0
  let pt : FVar D b a → ℂ := fun v => if v = (τ, i₀, j₀) ∨ v = (τ, l₀, j₀) then 1 else 0
  have hq : ∀ i l j, eval pt (quad τ ε ε' i l j) = if j = j₀ ∧ l = l₀ ∧ i = i₀ then 1 else 0 := by
    intro i l j
    unfold quad
    by_cases hc : ε' i = ε j ∧ ε' l ≠ ε j
    · rw [if_pos hc, map_mul, eval_X, eval_X]
      by_cases hj : j = j₀
      · subst hj
        have h1 : i ≠ l₀ := fun h => hl (h ▸ hc.1)
        have h2 : l ≠ i₀ := fun h => hc.2 (h ▸ hi)
        by_cases h3 : i = i₀ <;> by_cases h4 : l = l₀ <;> simp [pt, h1, h2, h3, h4]
      · simp [pt, hj]
    · rw [if_neg hc, map_zero, if_neg]
      rintro ⟨rfl, rfl, rfl⟩
      exact hc ⟨hi, hl⟩
  have := congrArg (eval pt) h0
  unfold quadAll at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, smul_eval, hq, map_zero, ite_and] at this
  apply hY
  simpa using this

theorem sub_mem (Y : Matrix (Fin b) (Fin b) ℂ) :
    fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) ∈ nonRaising (FVar D b a) := by
  have : fockT τ ε ε' Y - LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
      ∑ i, ∑ l, Y i l • ∑ j, ((raiO τ ε ε' i j * lowO τ ε ε' l j - LinearMap.mulLeft ℂ (quad τ ε ε' i l j)) +
        if i = l then (1 / 2 : ℂ) • 1 else 0) := by
    have hm : LinearMap.mulLeft ℂ (quadAll τ ε ε' Y) =
        ∑ i, ∑ l, Y i l • ∑ j, LinearMap.mulLeft ℂ (quad τ ε ε' i l j) := by
      refine LinearMap.ext fun P => ?_
      simp [quadAll, Finset.sum_mul, LinearMap.sum_apply]
    rw [hm]
    unfold fockT
    simp only [← Finset.sum_sub_distrib, ← smul_sub]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    abel
  rw [this]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ (term_mem τ ε ε' i l j) ?_)
  split_ifs
  · exact Submodule.smul_mem _ _ one_mem
  · exact Submodule.zero_mem _

theorem fockT_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin b) (Fin b) ℂ), 0 < a → (∃ i l, ε' i ≠ ε' l ∧ Y i l ≠ 0 ∧ Y l i ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' Y ha ⟨i, l, hil, h1, h2⟩
  refine ⟨quadAll τ ε ε' Y, _, ?_, quadAll_hom τ ε ε' Y, sub_mem τ ε ε' Y, by abel⟩
  by_cases h : ε' i = ε ⟨0, ha⟩
  · exact fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y i l ⟨0, ha⟩ h (fun h' => hil (h.trans h'.symm)) h1
  · refine fockQuadraticPart_ne_zero_of_offBlock_entry τ ε ε' Y l i ⟨0, ha⟩ ?_ h h2
    revert h hil
    cases ε' i <;> cases ε' l <;> cases ε ⟨0, ha⟩ <;> simp

end GlobalTheory.Chain.FockTDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible IsIrredSubrep)
open scoped InnerProductSpace
open scoped Pointwise

namespace GlobalTheory.CompactRight

theorem map_mul_right_eq_of_mem_compact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) : Measure.map (· * k) μ = μ := by
  set c := Measure.haarScalarFactor (Measure.map (· * k) μ) μ with hc
  have hmapEq : Measure.map (· * k) μ = c • μ := Measure.isMulLeftInvariant_eq_smul _ μ
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set S : Set G := V * (K : Set G) with hS
  have hScpt : IsCompact S := hVc.mul hK
  have hVsubS : V ⊆ S := by
    intro v hv
    exact Set.mem_mul.2 ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hSpre : (· * k) ⁻¹' S = S := by
    ext x
    simp only [Set.mem_preimage, hS, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, a, ha, hva⟩
      refine ⟨v, hv, a * k⁻¹, K.mul_mem ha (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hva, mul_inv_cancel_right]
    · rintro ⟨v, hv, a, ha, hva⟩
      exact ⟨v, hv, a * k, K.mul_mem ha hk, by rw [← mul_assoc, hva]⟩
  have hSpos : μ S ≠ 0 := (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds (μ := μ) hV1) (measure_mono hVsubS)).ne'
  have hSfin : μ S ≠ ⊤ := hScpt.measure_lt_top.ne
  have hmapS : Measure.map (· * k) μ S = μ S := by
    rw [show (· * k) = (MeasurableEquiv.mulRight k : G → G) from rfl, MeasurableEquiv.map_apply]
    exact congrArg μ hSpre
  have hcOne : c = 1 := by
    have hcEq : (c : ENNReal) * μ S = 1 * μ S := by
      have hcS := hmapS
      rw [hmapEq, smul_apply, ENNReal.smul_def, smul_eq_mul] at hcS
      rw [one_mul]
      exact hcS
    exact_mod_cast (ENNReal.mul_left_inj hSpos hSfin).1 hcEq
  rw [hmapEq, hcOne, one_smul]

end GlobalTheory.CompactRight
end

