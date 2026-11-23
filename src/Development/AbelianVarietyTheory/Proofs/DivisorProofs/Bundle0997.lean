module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignatures
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev MD (P Q R S : ι → ℕ) (w : ι) : Type := Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ

theorem sumPl_singleD (w : ι) (M : MD P Q R S w) :
    sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w))
      (fun w' => heisOp ((Pi.single w M : ∀ w', MD P Q R S w') w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

def eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) : ∀ w', MD P Q R S w' :=
  Pi.single w (Matrix.single a b x)

theorem eS_ne (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) {w' : ι} (h : w' ≠ w) :
    eS w a b x w' = 0 := by
  simp [eS, Pi.single_eq_of_ne h]

theorem eS_same (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) :
    eS w a b x w = Matrix.single a b x := by
  simp [eS]

theorem sum_eS (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (x : ℂ) (c : ∀ w', MD P Q R S w') :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w]
  · rw [eS_same, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp [Matrix.single_apply]
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    simp [eS_ne w a b x hy]
  · simp

theorem decomp (c : ∀ w, MD P Q R S w) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w]
  · simp only [eS_same]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp only [Matrix.single_apply, and_self, if_true, Complex.real_smul, mul_one]
      exact (Complex.re_add_im _).symm
    · intro y _ hy; simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun b' _ => ?_
      simp [Matrix.single_apply, hy, Ne.symm hy]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => ?_
    simp [eS_ne _ _ _ _ (Ne.symm hy)]
  · simp

abbrev Idx (P Q R S : ι → ℕ) : Type := Σ w : ι, Ix (P w) (Q w) × Ix (R w) (S w) × Bool

def cu (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : Idx P Q R S) : ∀ w, MD P Q R S w :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem sum_idx {M : Type} [AddCommMonoid M] (f : Idx P Q R S → M) :
    ∑ i, f i = ∑ w, ∑ a, ∑ b, (f ⟨w, a, b, true⟩ + f ⟨w, a, b, false⟩) := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem dual {l : Type} [Fintype l] (φ : (∀ w, MD P Q R S w) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  rw [sum_idx]
  simp only [cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD.QuadFockD

open GlobalTheory.RealLift.QuadFock

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

theorem cu_true_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, true⟩ w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ∀ w, Mat (R w) (S w)) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (w' : ι) :
    cu (P := P) (Q := Q) ⟨w, a, b, false⟩ w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ∀ w', MD P Q R S w') w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, true⟩ =
      (Pi.single w (Matrix.single a b Complex.I) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cv (P := P) (Q := Q) (R := R) (S := S) ⟨w, a, b, false⟩ =
      (Pi.single w (Matrix.single a b (1 : ℂ)) : ∀ w', MD P Q R S w') := by
  simp [cv, eS]

end GlobalTheory.HoweD.QuadFockD

namespace GlobalTheory.HoweD

open GlobalTheory.RealLift.QuadFock GlobalTheory.HoweD.QuadFockD

theorem quad_fockD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) T) := by
  intro ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual l (Idx P Q R S) Z (fun i => φ (QuadFockD.cu i)) (fun i => φ (QuadFockD.cv i))
    (QuadFockD.dual φ hφ)
  have hop : sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i : Idx P Q R S, (1 / 2 : ℂ) •
        (sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) +
          sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cv i w)) *
            sumPl (V := fun w => Pol (P w) (Q w) (R w) (S w)) (fun w => heisOp (QuadFockD.cu i w * (Y w)ᵀ))) := by
    rw [sum_idx]
    simp only [QuadFockD.cu_true_mul, QuadFockD.cu_false_mul, QuadFockD.cv_true, QuadFockD.cv_false, sumPl_singleD,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [_root_.GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad (P w) (Q w) (R w) (S w) (Y w) (hY w)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add (f := _), atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear hq hop hφ hY
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsSupCoinvariantsEqTop
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftUnitTimesCoord
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenReadsOfUnfBC
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem genReads_of_unfBC {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r g : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] ((U (σ'.comp (incF c c' hle))).X k).Λ)
    (idx : Fin g ≃ ((U (σ'.comp (incF c c' hle))).X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (x : ((U (σ'.comp (incF c c' hle))).X k).dom) (ϑ : (Fin g → ℂ) → ℂ)
    (h : GenReads (unfBC hle U σ') k bas idx e x ϑ) : GenReads (U (σ'.comp (incF c c' hle))) k bas idx e x ϑ := by
  obtain ⟨B, hB⟩ := h
  letI : Algebra c.F ℂ := (σ'.comp (incF c c' hle)).toAlgebra
  letI : Algebra c'.F ℂ := σ'.toAlgebra
  exact ⟨⟨B.ex, B.ex_add, B.ex_onto, B.ex_ker, B.ex_lin, B.hol, B.der, B.fr, B.fr_hol, B.fr_ne, B.fr_g, B.fr_0, B.χ,
    B.χ_norm, B.fr_per⟩, hB⟩

theorem CcIs.unfBC {D : D7} (θ : InfFam D) (V W : HSp D) {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ)
    (dict : GA D W → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D W → ℂ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f₀ : WO V W → ℂ) (cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ)
    (h : CcIs θ V W hr (U (σ'.comp (incF c c' hle))) dict mu x₀ om f₀ cc) :
    CcIs θ V W hr (Formalism.L2.Pj.unfBC hle U σ') dict mu x₀ om f₀ cc := by
  refine ⟨h.1, fun a γ hA hx' g bas idx e hs hi ϑ hϑ w hw => ?_⟩
  have hrel : relab c' σ' = relab c (σ'.comp (incF c c' hle)) := funext fun τ => RingHom.ext fun x => rfl
  have hi' : IdxIs c (σ'.comp (incF c c' hle)) ((U (σ'.comp (incF c c' hle))).X (dict a).1) idx e := by
    unfold IdxIs at hi ⊢
    rw [hrel] at hi
    exact hi
  exact h.2 a γ hA hx' g bas idx e hs hi' ϑ (genReads_of_unfBC hle U σ' _ bas idx e ⟨_, hx'⟩ ϑ hϑ) w hw

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruentStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTriple_trivial_over_reals_of_gram_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) → ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  first | (exact @GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (exact GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (intros; apply GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr  <;> assumption)
end

