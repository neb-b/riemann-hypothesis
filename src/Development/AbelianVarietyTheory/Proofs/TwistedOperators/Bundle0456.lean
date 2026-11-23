module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRelOfLocalMatching
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareRel

section Rel

variable {P Q Pr : Type*} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pr] [Module ℂ Pr]

def relOf (q : P →ₗ[ℂ] Pr) (q' : Q →ₗ[ℂ] Pr) : Submodule ℂ (P × Q) :=
  LinearMap.eqLocus (q ∘ₗ LinearMap.fst ℂ P Q) (q' ∘ₗ LinearMap.snd ℂ P Q)

theorem mem_relOf {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} {x : P × Q} : x ∈ relOf q q' ↔ q x.1 = q' x.2 := Iff.rfl

theorem relOf_fst {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq' : Function.Surjective q') (a : P) : ∃ b, (a, b) ∈ relOf q q' := by
  obtain ⟨b, hb⟩ := hq' (q a)
  exact ⟨b, hb.symm⟩

theorem relOf_snd {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) (b : Q) : ∃ a, (a, b) ∈ relOf q q' := by
  obtain ⟨a, ha⟩ := hq (q' b)
  exact ⟨a, ha⟩

theorem relOf_ne_top [Nontrivial Pr] {q : P →ₗ[ℂ] Pr} {q' : Q →ₗ[ℂ] Pr} (hq : Function.Surjective q) : relOf q q' ≠ ⊤ := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne (0 : Pr)
  obtain ⟨a, rfl⟩ := hq y
  have h1 : (a, (0 : Q)) ∈ relOf q q' := h ▸ Submodule.mem_top
  rw [mem_relOf, map_zero] at h1
  exact hy h1

end Rel

section Pol

variable {σ₁ σ₂ ν : Type} (e : σ₁ ⊕ σ₂ ≃ ν)

def polTens : MvPolynomial σ₁ ℂ ⊗[ℂ] MvPolynomial σ₂ ℂ ≃ₗ[ℂ] MvPolynomial ν ℂ :=
  ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)).equiv
    (MvPolynomial.basisMonomials ν ℂ) (Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr e).toEquiv)

theorem finsupp_sum_eq (m : σ₁ →₀ ℕ) (n : σ₂ →₀ ℕ) :
    Finsupp.domCongr e (Finsupp.sumElim m n) = m.mapDomain (e ∘ Sum.inl) + n.mapDomain (e ∘ Sum.inr) := by
  ext x
  obtain ⟨s, rfl⟩ := e.surjective x
  have h1 : Function.Injective (e ∘ Sum.inl) := e.injective.comp Sum.inl_injective
  have h2 : Function.Injective (e ∘ Sum.inr) := e.injective.comp Sum.inr_injective
  rcases s with s | s
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inl]
    rw [show e (Sum.inl s) = (e ∘ Sum.inl) s from rfl, Finsupp.mapDomain_apply_of_injective h1, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu).symm
  · rw [Finsupp.add_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.sumElim_inr]
    rw [show e (Sum.inr s) = (e ∘ Sum.inr) s from rfl, Finsupp.mapDomain_apply_of_injective h2, Finsupp.mapDomain_notin_range]
    · simp
    · rintro ⟨u, hu⟩
      exact Sum.inl_ne_inr (e.injective hu)

theorem polTens_tmul (p₁ : MvPolynomial σ₁ ℂ) (p₂ : MvPolynomial σ₂ ℂ) :
    polTens e (p₁ ⊗ₜ p₂) = MvPolynomial.rename (e ∘ Sum.inl) p₁ * MvPolynomial.rename (e ∘ Sum.inr) p₂ := by
  have key : (TensorProduct.mk ℂ _ _).compr₂ (polTens e).toLinearMap =
      (LinearMap.mul ℂ (MvPolynomial ν ℂ)).compl₁₂ (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inl)).toLinearMap
        (MvPolynomial.rename (R := ℂ) (e ∘ Sum.inr)).toLinearMap := by
    refine (MvPolynomial.basisMonomials σ₁ ℂ).ext fun m => (MvPolynomial.basisMonomials σ₂ ℂ).ext fun n => ?_
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials]
    have h : (MvPolynomial.monomial m (1 : ℂ)) ⊗ₜ[ℂ] (MvPolynomial.monomial n (1 : ℂ)) =
        ((MvPolynomial.basisMonomials σ₁ ℂ).tensorProduct (MvPolynomial.basisMonomials σ₂ ℂ)) (m, n) := by
      rw [Module.Basis.tensorProduct_apply, MvPolynomial.coe_basisMonomials, MvPolynomial.coe_basisMonomials]
    rw [h, polTens]
    erw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, mul_one,
      Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    rw [finsupp_sum_eq]
  exact LinearMap.congr_fun₂ key p₁ p₂

end Pol

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

section Route

variable {D : D7} {a b c d b' : ℕ}

end Route

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : ℕ) {d b' b₁ : ℕ}

theorem hasInfExp_alpha {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (τ : D.what₂.Tau) {a : ℚ}
    (h : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ a) : HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j) τ a := by
  obtain ⟨-, -, ⟨θ, hθ⟩, -⟩ := id h
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨n', hn', ho'⟩ := hL.xi_fin t'
  have h0 := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  have h0' := GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t') hn' ho' τ
  have hK : ∀ s, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G s i j = (L.mu0 (j + 1) * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j) * L.xi s := fun s => by
    show L.mu0 (j + 1) * L.xi s * L.eta ^ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = _
    exact mul_right_comm _ _ _
  have e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t' i j = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j * (L.xi t)⁻¹ * L.xi t' := by
    rw [hK t', hK t, mul_inv_cancel_right]
  have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.Chain.StepVac.hasInfExp_mul h (GlobalTheory.Chain.StepVac.hasInfExp_inv h0)) h0'
  rw [e]
  simpa using this

end Grid

theorem nontrivial_of_tensor {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
    [AddCommGroup Pi] [Module ℂ Pi] [Nontrivial Pi] (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi) : Nontrivial Pr := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨u, hu⟩ := exists_ne (0 : Pi)
  apply hu
  rw [← e.apply_symm_apply u, hz (e.symm u), map_zero]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7} {Pr Pf Pi : Type*} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf]
  [AddCommGroup Pi] [Module ℂ Pi]

end GlobalTheory.SquareRel

namespace GlobalTheory.SquareRel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta)

variable {D : D7}

end GlobalTheory.SquareRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignatureMatrixExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackFrame

open GlobalTheory.PackLoc

section Lin

variable {m N : ℕ} (e : Option (Fin m) ≃ Fin N)

theorem embOpt_mul (h k : Matrix (Fin m) (Fin m) ℂ) : embOpt e (h * k) = embOpt e h * embOpt e k := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embOpt, Matrix.mul_apply]

theorem embOpt_ct (h : Matrix (Fin m) (Fin m) ℂ) : embOpt e hᴴ = (embOpt e h)ᴴ := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt]

theorem embOpt_Jm {εA : Fin m → Bool} {ε : Fin N → Bool} (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = εA i) :
    Formalism.REAL.Jm ε = embOpt e (Formalism.REAL.Jm εA) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

theorem embOpt_unit {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : IsUnit (embOpt e h) := by
  obtain ⟨k, hk⟩ := hh.exists_right_inv
  exact IsUnit.of_mul_eq_one (embOpt e k) (by rw [← embOpt_mul, hk, embOpt_one])

theorem embOpt_inv {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : (embOpt e h)⁻¹ = embOpt e h⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← embOpt_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hh), embOpt_one])

theorem Jm_unit (ε : Fin m → Bool) : IsUnit (Formalism.REAL.Jm ε) := by
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm ε) ?_
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

def vecOpt (y : Fin m → ℂ) (a : ℂ) : Fin N → ℂ := fun b => (e.symm b).elim a y

theorem embOpt_vec (h : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (a : ℂ) :
    embOpt e h *ᵥ vecOpt e y a = vecOpt e (h *ᵥ y) a := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [embOpt, vecOpt, Matrix.mulVec, dotProduct]

theorem eu_vecOpt (y : Fin m → ℂ) (a : ℂ) : eu (vecOpt e y a) ^ 2 = eu y ^ 2 + ‖a‖ ^ 2 := by
  unfold eu
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp, Fintype.sum_option, add_comm]
  simp [vecOpt]

theorem vecOpt_zero_one : vecOpt e 0 1 = Pi.single (e none) 1 := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [vecOpt, Pi.single_apply]

def colM (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i b => (e.symm b).elim (z i 0) (F i)

variable (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ)

theorem colM_vec (y : Fin m → ℂ) (a : ℂ) : colM e F z *ᵥ vecOpt e y a = F *ᵥ y + a • fun i => z i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  simp [colM, vecOpt, Matrix.mulVec, dotProduct, add_comm, mul_comm]

theorem mul_colM (g : Matrix (Fin N) (Fin N) ℂ) : g * colM e F z = colM e (g * F) (g * z) := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [colM, Matrix.mul_apply]

theorem colM_mul (h : Matrix (Fin m) (Fin m) ℂ) : colM e F z * embOpt e h = colM e (F * h) z := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [colM, embOpt, Matrix.mul_apply]

theorem colM_gram (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1) :
    (colM e F z)ᴴ * J * colM e F z = embOpt e (Fᴴ * J * F) := by
  rw [Matrix.mul_assoc] at h1 h2 h3 ⊢
  rw [Matrix.mul_assoc, mul_colM]
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | none => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h3 0) 0
    | some b => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h2 0) b
  | some a => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h1 a) 0
    | some b => simp [colM, embOpt, Matrix.mul_apply (M := _ᴴ)]

theorem exists_frame (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1)
    (εA : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (ε : Fin N → Bool) (hA : IsUnit A)
    (hG : Aᴴ * Formalism.REAL.Jm εA * A = Fᴴ * J * F) (h0 : ε (e none) = true) (hε : ∀ i, ε (e (some i)) = εA i) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = J ∧
      (∀ (y : Fin m → ℂ) (a : ℂ), eu (B *ᵥ (F *ᵥ y + a • fun i => z i 0)) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
      B *ᵥ (fun i => z i 0) = Pi.single (e none) 1 ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (h : Matrix (Fin m) (Fin m) ℂ), g * F = F * h → g * z = z →
        B * g * B⁻¹ = embOpt e (A * h * A⁻¹) := by
  set M := colM e F z with hM
  set C := embOpt e A with hC
  have hCu : IsUnit C := embOpt_unit e hA
  have hg : Mᴴ * J * M = Cᴴ * Formalism.REAL.Jm ε * C := by
    rw [hM, colM_gram e F z J h1 h2 h3, ← hG, embOpt_mul, embOpt_mul, embOpt_ct, embOpt_Jm e h0 hε]
  have hMu : IsUnit M := by
    have : IsUnit (Mᴴ * J * M) := by
      rw [hg]; exact (((Matrix.isUnit_conjTranspose _).2 hCu).mul (Jm_unit ε)).mul hCu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hMu
  have key : ∀ y a, (C * M⁻¹) *ᵥ (F *ᵥ y + a • fun i => z i 0) = vecOpt e (A *ᵥ y) a := by
    intro y a
    rw [← colM_vec e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, embOpt_vec]
  refine ⟨C * M⁻¹, hCu.mul hMi, ?_, fun y a => ?_, ?_, fun g h e1 e2 => ?_⟩
  · calc (C * M⁻¹)ᴴ * Formalism.REAL.Jm ε * (C * M⁻¹) = (M⁻¹)ᴴ * (Cᴴ * Formalism.REAL.Jm ε * C) * M⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (M * M⁻¹)ᴴ * J * (M * M⁻¹) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  · rw [key, eu_vecOpt]
  · have := key 0 1
    simpa [vecOpt_zero_one] using this
  · have e3 : g * M = M * embOpt e h := by rw [hM, mul_colM, colM_mul, e1, e2]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd, embOpt_mul, embOpt_mul, ← embOpt_inv e hA, ← hC]
    calc C * M⁻¹ * g * (M * C⁻¹) = C * (M⁻¹ * (g * M)) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e3, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

end Lin

variable {D : D7}

theorem map_cT_tau (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X).map (tauE D τ) = (X.map (tauE D τ))ᴴ := by
  ext a b
  exact GlobalTheory.FockCompare.tauE_star τ _

theorem map_incA_tau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (X.map (incA D)).map ((θ τ).comp (infPart D)) = X.map (tauE D τ) := by
  ext a b
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem exists_adapted_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  intro D θ hθ Y V d τ εA A ε e hA hG h0 hε
  have h1 := congrArg (fun X => X.map (tauE D τ)) d.perp
  have h2 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.UnitaryEmbeddingGroup.perp' d)
  have h3 := congrArg (fun X => X.map (tauE D τ)) d.gram
  have h4 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.AutFunCounterexample.gram_pull V Y d.ι d.isom)
  simp only [Matrix.map_mul, map_cT_tau, Matrix.map_zero _ (map_zero _)] at h1 h2 h3 h4
  have h5 : (antiDiagonalSignGramMatrix 1 (1 : D.host.E)).map (tauE D τ) = 1 := by
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [antiDiagonalSignGramMatrix]
  rw [h5] at h3
  obtain ⟨B, b1, b2, b3, b4, b5⟩ := exists_frame e _ _ _ h1 h2 h3 εA A ε hA (hG.trans h4.symm) h0 hε
  refine ⟨B, b1, b2, b3, b4, fun h _ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _ τ, fun h hh => b5 _ h ?_ ?_⟩
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) ((embRel_iff d (atTau θ Y τ h) _).2 rfl).1
    have k2 := (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hh).2.1
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at k2
    exact k1.trans (congrArg _ k2)
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) (GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d (atTau θ Y τ h))
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    exact k1

end GlobalTheory.PackFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinCoefMultT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

def FinCoef (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (n : ℕ) (L : Fin n → (M.H τ →L[ℂ] ℂ)) (v : Fin n → M.H τ),
    (∀ i, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (v i)) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), φ (x * atTau θ V τ g) = ∑ i, L i (M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (v i))

theorem FinCoef.zero (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    FinCoef θ M τ 0 := fun _ => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp⟩

theorem FinCoef.add {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ ψ : GA D V → ℂ} (h₁ : FinCoef θ M τ φ) (h₂ : FinCoef θ M τ ψ) : FinCoef θ M τ (φ + ψ) := fun x => by
  obtain ⟨n₁, L₁, v₁, hv₁, e₁⟩ := h₁ x
  obtain ⟨n₂, L₂, v₂, hv₂, e₂⟩ := h₂ x
  refine ⟨n₁ + n₂, Fin.append L₁ L₂, Fin.append v₁ v₂, fun i => ?_, fun g hg => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hv₁ i
    · simpa using hv₂ i
  · rw [Fin.sum_univ_add, Pi.add_apply, e₁ g hg, e₂ g hg]
    simp

theorem FinCoef.smul {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {φ : GA D V → ℂ} (c : ℂ) (h : FinCoef θ M τ φ) : FinCoef θ M τ (c • φ) := fun x => by
  obtain ⟨n, L, v, hv, e⟩ := h x
  refine ⟨n, fun i => c • L i, v, hv, fun g hg => ?_⟩
  rw [Pi.smul_apply, e g hg, Finset.smul_sum]
  simp

theorem FinCoef.sum {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau}
    {n : ℕ} {φ : Fin n → GA D V → ℂ} (h : ∀ i, FinCoef θ M τ (φ i)) : FinCoef θ M τ (∑ i, φ i) := by
  classical
  have : ∀ s : Finset (Fin n), FinCoef θ M τ (∑ i ∈ s, φ i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using FinCoef.zero θ M τ
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih
  exact this Finset.univ

theorem finCoef_lift {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T)
    (z : SmT M) : FinCoef θ M τ (PiTensorProduct.lift T z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    intro x
    obtain ⟨ℓ, -, hℓ⟩ := GlobalTheory.DefiniteEnd.exists_sobCont M τ T f x
    have hsv : SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) (f τ : M.H τ) := by
      have hw : ∀ w ∈ M.sm τ, SmoothVec (lieAt V τ) (fun g => M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)) w := by
        intro w hw
        rw [GlobalTheory.SmVec.sm_eq M τ] at hw
        exact hw
      exact hw _ (f τ).2
    refine ⟨1, fun _ => r • LinearMap.toContinuousLinearMap ℓ, fun _ => (f τ : M.H τ), fun _ => hsv, fun g hg => ?_⟩
    have e1 := congrFun (hT.equiv τ g hg f ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩ rfl) x
    have e3 : T f (x * atTau θ V τ g) = ℓ (M.rep τ g (f τ)) := by
      rw [hℓ ⟨M.rep τ g (f τ), GlobalTheory.ConjMult.rep_mem_sm M τ hg (f τ).2⟩]
      exact e1.symm
    rw [Fin.sum_univ_one, map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, e3, LinearMap.coe_toContinuousLinearMap']
    rfl
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ha.add hb

end GlobalTheory.ColTypeLift

namespace GlobalTheory.ColTypeLift

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem finCoef_multT {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    [FiniteDimensional ℂ (M.H τ)] (F : MultT θ M ∅ 1) (z : SmT M) : FinCoef θ M τ (F.1 z) := by
  have hm : PiTensorProduct.lift.symm F.1 ∈ Mult θ M ∅ 1 := (mem_multT θ M ∅ 1 F.1).1 F.2
  have key : ∀ T ∈ Mult θ M ∅ 1, FinCoef θ M τ (PiTensorProduct.lift T z) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx => exact finCoef_lift M τ hx z
    | zero => simpa using FinCoef.zero θ M τ
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact hx.add hy
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply]; exact hx.smul c
  have := key _ hm
  rwa [LinearEquiv.apply_symm_apply] at this

theorem isTypeAt_sum (θ : InfFam D) (N : Node D) (hs : N.V.SigOK) (hd : N.V.IsDefinite) (τ : D.what₂.Tau) {n : ℕ}
    (F : Fin n → N.Cusp θ) (z : Fin n → SmT N.M) : IsTypeAt θ N.V τ (N.S τ) (∑ i, (F i).1 (z i)) := by
  haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  exact GlobalTheory.EndCusp.isTypeAt_of_finSum θ N.V τ (N.M.enum τ) (N.M.ds τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _
    (FinCoef.sum fun i => finCoef_multT N.M τ (F i) (z i))

theorem xp_definite {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R} (hG : G.Is)
    (k : ℕ) (hk : k ≤ D.R.m) : (G.Xp k).V.SigOK ∧ (G.Xp k).V.IsDefinite := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp
  | succ k =>
    have h := hG.spaces.X k hk
    refine ⟨h.sigOK, fun τ => Or.inl ?_⟩
    rw [h.sig, h.rank]
    simp

end GlobalTheory.ColTypeLift
end
end

