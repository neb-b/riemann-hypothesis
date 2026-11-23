module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {κ : Type} [Fintype κ] (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (hA' : ∀ i f, P f → P (A' i f)) (hc' : ∀ i j f, P f → A' i (A' j f) = A' j (A' i f))
    (Aadd' : ∀ i f f', P f → P f' → A' i (f + f') = A' i f + A' i f')
    (Asm' : ∀ i (a : ℂ) f, P f → A' i (a • f) = a • A' i f)
    (c : ι → κ → ℂ) (r : ι → κ → ι) (h : ∀ i f, P f → A' i f = ∑ b, c i b • A (r i b) f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' f Q = pureTensorL A f
      (MvPolynomial.aeval (fun v : ι => ∑ b, c v b • (MvPolynomial.X (r v b) : MvPolynomial ι ℂ)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), MvPolynomial.C_mul',
      map_smul, map_smul, pure_one, pure_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hp, h _ _ (pure_mem hadd hsm hA hf _), map_mul,
      MvPolynomial.aeval_X, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, map_smul, pure_X_mul hadd hsm hA hc Aadd Asm hf]

end Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (t : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)

include hψ hθ hf

theorem dRho_csmul (w : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (w • u) f =
      (w.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ u f + (w.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (I • u) f := by
  have e : w • u = (w.re : ℂ) • u + (w.im : ℂ) • (I • u) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (dRho_laws hψ hθ hf τ _).2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_dir_add (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO s t) z f + aPlus (heisO ψ S T) θ τ (cplxO s t) z' f := by
  simp only [aPlus_eq, GlobalTheory.OrientedRealForm.cplxO_add, fun z => (dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem aPlus_dir_zero : aPlus (heisO ψ S T) θ τ (cplxO s t) 0 f = 0 := by
  have := aPlus_dir_add hψ hθ τ s t hf 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aPlus_dir_sum {κ : Type} (F : Finset κ) (z : κ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (∑ b ∈ F, z b) f = ∑ b ∈ F, aPlus (heisO ψ S T) θ τ (cplxO s t) (z b) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using aPlus_dir_zero hψ hθ τ s t hf
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aPlus_dir_add hψ hθ τ s t hf, ih]

theorem aPlus_dir_smul (e : Bool) (w : ℂ) {u : Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hu : cplxO s t u = ((if e then 1 else -1 : ℂ) * I) • u) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (w • u) f =
      (if e then w else starRingEnd ℂ w) • aPlus (heisO ψ S T) θ τ (cplxO s t) u f := by
  have h1 : cplxO s t (w • u) = (w * ((if e then 1 else -1 : ℂ) * I)) • u := by
    rw [← smul_smul, ← hu]
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rw [aPlus_eq, aPlus_eq, h1, hu, dRho_csmul hψ hθ τ hf w, dRho_csmul hψ hθ τ hf (w * _),
    dRho_csmul hψ hθ τ hf (_ * I)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, w = x + y * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  cases e
  · simp only [Bool.false_eq_true, if_false, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> simp <;> ring_nf <;> simp
  · simp only [if_true]
    match_scalars <;> simp <;> ring_nf <;> simp

omit hψ hθ hf

theorem unitMap_mul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (j : Fin n) : unitMap B (B' * k) a j = ∑ b, k b a • unitMap B B' b j := by
  have e : k * single a j (1 : ℂ) = ∑ b, k b a • single b j (1 : ℂ) := by
    ext p q
    by_cases h : j = q
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, h]
  unfold unitMap
  rw [Matrix.mul_assoc B', e, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxO_unitMap {S' : D.what₂.Tau → SPar} (M : DSModel T S') {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin T.rank) (j : Fin n) : cplxO 1 (cart M τ) (unitMap B (onb M τ) b j) =
      ((if M.ε τ b then 1 else -1 : ℂ) * I) • unitMap B (onb M τ) b j := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have e : Formalism.REAL.Jm (M.ε τ) * single b j (1 : ℂ) = (if M.ε τ b then 1 else -1 : ℂ) • single b j (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : b = p
    · rw [h]
    · simp [h]
  unfold cplxO unitMap cart onb
  rw [Matrix.mul_one, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * single b j (1 : ℂ)) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem kset_zero {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n}
    (h : ε b ≠ ε a) : k b a = 0 := by
  have e := congrFun (congrFun hk.2 b) a
  rw [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at h e <;> simp at e <;>
    first | linear_combination (1 / 2 : ℂ) * e | linear_combination (-1 / 2 : ℂ) * e

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  intro D ψ θ S T S' M BS f k c hψ hθ hS hf hk hc P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f' :=
    fun _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f :=
    fun _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ i j _ h => aPlus_comm (sS := fun _ => 1) (sT := cart M) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (fun τ => onb M τ * k τ) i g =
      ∑ b, c i.1 b i.2.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (i.1, b, i.2.2) g := by
    rintro ⟨τ, a, j⟩ g hg
    simp only [aPlusAll]
    rw [unitMap_mul, aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ τ _ _ hg _ _ (cplxO_unitMap τ M _ b j), hc]
    by_cases h : M.ε τ b = M.ε τ a
    · rw [h]
    · rw [kset_zero (hk τ) h]
      simp
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _) (Ac _) (Aadd _) (Asm _) (hA _) (Ac _) (Aadd _) (Asm _)
    (fun v b => c v.1 b v.2.1) (fun v b => (v.1, b, v.2.2)) key hf P

end GlobalTheory.FockSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIndep

section Mat

variable {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {H t B' : Matrix (Fin m) (Fin m) ℂ} {δ : Fin m → ℂ}

theorem trace_unitMap (hB : Bᴴ * G * B = 1) (hB' : B'ᴴ * H * B' = diagonal δ) (a c : Fin m) (b d : Fin n) :
    (G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b).trace = if (a, b) = (c, d) then δ a else 0 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hG : G⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]
  have e : G⁻¹ * (unitMap B B' c d)ᴴ * H * unitMap B B' a b =
      B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * B') * Matrix.single a b (1 : ℂ) * B⁻¹) := by
    simp only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, hB', Matrix.one_mul,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, Matrix.diagonal_apply]
  by_cases h : c = a
  · subst h
    by_cases h' : d = b
    · subst h'; simp
    · simp [Matrix.trace_single_eq_of_ne _ _ _ h', Ne.symm h']
  · simp [h, Ne.symm h]

theorem cplxO_unitMap (ht : t * B' = B' * diagonal δ) (a : Fin m) (b : Fin n) :
    cplxO 1 t (unitMap B B' a b) = (Complex.I * δ a) • unitMap B B' a b := by
  have e : diagonal δ * Matrix.single a b (1 : ℂ) = δ a • Matrix.single a b (1 : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    split_ifs with h
    · rw [h.1, smul_eq_mul]
    · simp
  rw [cplxO, unitMap, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ht, Matrix.mul_assoc B', e,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]

end Mat

theorem pureTensorO_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  intro D ψ θ S T S' M BS f hψ hθ hS hBS hf f0 hv
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hB' : ∀ τ, (onb M τ)ᴴ * gramAt D T τ * onb M τ = diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [← M.fr_gram τ, onb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hu τ), conjTranspose_one, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hu τ)]
    rfl
  unfold pureTensorO aPlusAll
  refine pure_injective (P := IsThetaFunO ψ S T)
    (B := fun k => annih (heisO ψ S T) θ k.1 (cplxO 1 (cart M k.1)) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2))
    (c := fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * π * Complex.I) *
      (Complex.I * (-2 * (tauE D k.1 D.host.xi0).im : ℝ))))
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf f0 ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun _ _ h => annih_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · exact fun _ _ _ h h' => annih_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => annih_smul hψ hθ _ _ _ a h
  · rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩ g hg
    refine (annih_aPlus (sS := fun _ => 1) hψ hθ τ _ hS hT τ' _ hg).trans ?_
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    unfold omDir
    by_cases h : τ = τ'
    · subst h
      simp only [if_true, cplxO_unitMap (ht τ), Matrix.mul_smul, Matrix.trace_smul, trace_unitMap (hB τ) (hB' τ),
        Prod.mk.injEq, true_and]
      have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
      split_ifs <;> simp [Complex.mul_re, hre]
    · simp [h]
  · intro i
    have him := xi_zero_im_pos D i.1
    have hn : 0 < ‖tauE D i.1 D.host.xi0‖ := norm_pos_iff.2 fun h => by simp [h] at him
    have hfs : 0 < fockScale D i.1 := by
      unfold fockScale
      have := Real.pi_pos
      positivity
    simp [hfs.ne', him.ne', Real.pi_ne_zero]
  · exact fun i => hv i.1 _

end GlobalTheory.FockIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7}

def word (θ : InfF D) (V : HSp D) (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (φ : GA D V → ℂ) :
    GA D V → ℂ := l.foldr (fun p f => Rder θ V p.1 p.2 f) φ

def IsMod (θ : InfF D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ ∃ (N : ℕ) (C : ℝ), ∀ g, ‖word θ V l φ g‖ ≤ C * (height θ V g : ℝ) ^ N

private theorem word_mem_smFun {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : word θ V l φ ∈ SmFun θ V := by
  induction l with
  | nil => exact hφ
  | cons p l ih =>
    exact Rder_mem (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hl p (by simp))

theorem word_add {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) :
    word θ V l (φ + ψ) = word θ V l φ + word θ V l ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    show Rder θ V p.1 p.2 (word θ V l (φ + ψ)) =
      Rder θ V p.1 p.2 (word θ V l φ) + Rder θ V p.1 p.2 (word θ V l ψ)
    rw [ih hl', Rder_add (word_mem_smFun hl' hφ) (word_mem_smFun hl' hψ) (hl p (by simp))]

theorem word_smul {θ : InfF D} {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (c : ℂ) (φ : GA D V → ℂ) : word θ V l (c • φ) = c • word θ V l φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    show Rder θ V p.1 p.2 (word θ V l (c • φ)) = c • Rder θ V p.1 p.2 (word θ V l φ)
    rw [ih fun q hq => hl q (List.mem_cons_of_mem _ hq), Rder_smul]

theorem word_Rder {θ : InfF D} {V : HSp D} (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    word θ V l (Rder θ V τ X φ) = word θ V (l ++ [(τ, X)]) φ := by
  unfold word
  rw [List.foldr_append]
  rfl

def Decay (θ : InfF D) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ SmFun θ V ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
    Continuous (word θ V l φ) ∧ IsRapidDecay θ V (word θ V l φ)}
  add_mem' := by
    rintro φ ψ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨add_mem a1 b1, fun γ hγ g => by simp only [Pi.add_apply, a2 γ hγ, b2 γ hγ], fun l hl => ?_⟩
    rw [word_add hl a1 b1]
    refine ⟨(a3 l hl).1.add (b3 l hl).1, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    obtain ⟨C', hC'⟩ := (b3 l hl).2 N
    refine ⟨C + C', fun g => le_trans ?_ (add_le_add (hC g) (hC' g))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  zero_mem' := by
    refine ⟨zero_mem _, fun _ _ _ => rfl, fun l hl => ?_⟩
    have := word_smul (θ := θ) hl 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact ⟨continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  smul_mem' := by
    rintro c φ ⟨a1, a2, a3⟩
    refine ⟨Submodule.smul_mem _ c a1, fun γ hγ g => by simp only [Pi.smul_apply, a2 γ hγ], fun l hl => ?_⟩
    rw [word_smul hl]
    refine ⟨(a3 l hl).1.const_smul c, fun N => ?_⟩
    obtain ⟨C, hC⟩ := (a3 l hl).2 N
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

theorem Rder_left {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) :
    Rder θ V τ X φ (γ * g) = Rder θ V τ X φ g := by
  show deriv (fun t : ℝ => φ (γ * g * oneP θ V τ X t)) 0 = deriv (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simp only [mul_assoc, h]

theorem append_mem_lie {V : HSp D} {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)}
    (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    ∀ p ∈ l ++ [(τ, X)], p.2 ∈ lieAt V p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hl p hp
  · rw [List.mem_singleton] at hp
    subst hp
    exact hX

theorem Rder_mem_Decay {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : φ ∈ Decay θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ Decay θ V := by
  obtain ⟨h1, h2, h3⟩ := h
  refine (show _ ∧ _ ∧ _ from ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩)
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

theorem IsMod.rder {θ : InfF D} {V : HSp D} {φ : GA D V → ℂ} (h : IsMod θ V φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : IsMod θ V (Rder θ V τ X φ) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold IsMod
  refine ⟨Rder_mem h1 hX, fun γ hγ g => Rder_left (h2 γ hγ) τ X g, fun l hl => ?_⟩
  rw [word_Rder]
  exact h3 _ (append_mem_lie hl hX)

private theorem word_const_eq_const_norm_le {θ : InfF D} {V : HSp D} (c : ℂ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    ∃ d : ℂ, word θ V l (fun _ => c) = (fun _ => d) ∧ ‖d‖ ≤ ‖c‖ := by
  induction l with
  | nil => exact ⟨c, rfl, le_rfl⟩
  | cons p l ih =>
    obtain ⟨d, hd, -⟩ := ih
    refine ⟨0, ?_, by simp⟩
    show Rder θ V p.1 p.2 (word θ V l fun _ => c) = _
    rw [hd]
    funext g
    simp [Rder]

theorem isMod_const (θ : InfF D) (V : HSp D) (c : ℂ) : IsMod θ V fun _ => c := by
  unfold IsMod
  refine ⟨?_, fun _ _ _ => rfl, fun l _ => ?_⟩
  · intro k τs Xs _ g
    exact contDiff_const
  · obtain ⟨d, hd, hdc⟩ := word_const_eq_const_norm_le (θ := θ) (V := V) c l
    rw [hd]
    exact ⟨continuous_const, 0, ‖c‖, fun _ => by rw [pow_zero, mul_one]; exact hdc⟩

structure IsKerSys (θ : InfF D) (V W : HSp D) {M : Type} [AddCommGroup M] [Module ℂ M]
    (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) : Prop where
  cont : ∀ f, Continuous fun p : GA D V × GA D W => κ f p.1 p.2
  left : ∀ f, ∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, κ f (γ * g) (δ * h) = κ f g h
  level : ∀ f, ∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧
    IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, κ f (g * k) (h * k') = κ f g h
  growth : ∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ g h, ‖κ f g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N
  derV : ∀ τ, ∀ X ∈ lieAt V τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f (g * oneP θ V τ X t) h) (κ f' g h) 0
  derW : ∀ τ, ∀ X ∈ lieAt W τ, ∀ f, ∃ f', ∀ g h,
    HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0
  cap : ∀ τ, ∃ a b : ℕ → Module.End ℂ M, (∀ k f h, gelf θ V τ k (fun g => κ f g h) = fun g => κ (a k f) g h) ∧
    (∀ k f g, gelf θ W τ k (κ f g) = κ (b k f) g) ∧ Algebra.adjoin ℂ (Set.range a) = Algebra.adjoin ℂ (Set.range b)

def swapKer {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)) :
    M →ₗ[ℂ] (GA D W → GA D V → ℂ) where
  toFun f h g := κ f g h
  map_add' f f' := by rw [map_add (f := _)]; rfl
  map_smul' c f := by rw [map_smul]; rfl

theorem IsKerSys.swap {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (h : IsKerSys θ V W κ) : IsKerSys θ W V (swapKer κ) := by
  refine ⟨fun f => (h.cont f).comp continuous_swap, fun f γ hγ δ hδ g g' =>
    h.left f δ hδ γ hγ g' g, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨U, U', hU, hU', hk⟩ := h.level f
    exact ⟨U', U, hU', hU, fun k hk1 hk2 k' hk1' hk2' g g' => hk k' hk1' hk2' k hk1 hk2 g' g⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun f => ?_⟩
    obtain ⟨C, hC⟩ := hN f
    refine ⟨C, fun g g' => ?_⟩
    have hb := hC g' g
    rw [mul_comm (height θ V g' : ℝ)] at hb
    exact hb
  · intro τ X hX f
    obtain ⟨f', hf'⟩ := h.derW τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  · intro τ X hX f
    obtain ⟨f', hf'⟩ := h.derV τ X hX f
    exact ⟨f', fun g g' => hf' g' g⟩
  · intro τ
    obtain ⟨a, b, ha, hb, hab⟩ := h.cap τ
    exact ⟨b, a, fun k f g' => hb k f g', fun k f g => ha k f g, hab.symm⟩

def OmCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w

def thKer (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GlobalTheory.RealWeil.thetaSub ψ S T →ₗ[ℂ] (GA D S → GA D T → ℂ) where
  toFun f g h := om (g, h) f.1 0
  map_add' f f' := by funext g h; simp
  map_smul' c f := by funext g h; simp

end GlobalTheory.Mem.Lift

end
end

