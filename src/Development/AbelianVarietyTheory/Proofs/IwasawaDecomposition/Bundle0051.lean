module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameInteger
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCarryDual

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameIntegerStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acts_by_same_integer_statement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  first | exact @GlobalTheory.PrimeOrderScalar.acts_by_same_integer | exact GlobalTheory.PrimeOrderScalar.acts_by_same_integer | (intros; apply GlobalTheory.PrimeOrderScalar.acts_by_same_integer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasis
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem evM_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  intro L _ _ _ n a ι _ _ b P ι' _ _ b' P' hP hP' τ B

  have key : ∀ x, evM P' x - b'.toMatrix b * evM P x * b.toMatrix b' =
      Matrix.of fun i j => MvPolynomial.eval x (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) := by
    intro x
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evM, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) =
        b'.toMatrix b * evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * b.toMatrix b' := by
    intro γ₀ h
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h
    have e1 := hP γ γ₀ hγ
    have e2 := hP' γ γ₀ hγ
    have e3 := (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b') (c := b') (b' := b) (c' := b) (f := a.ρ γ)).symm
    have f1 : evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
      rw [e1]; rfl
    have f2 : evM P' (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b' b' (a.ρ γ) := by
      rw [e2]; rfl
    rw [f1, f2, e3]
  have hz : ∀ i j, MvPolynomial.eval (evPt τ B) (P' i j - ∑ k, ∑ l,
        MvPolynomial.C (b'.toMatrix b i k) * P k l * MvPolynomial.C (b.toMatrix b' l j)) = 0 := by
    intro i j
    rw [evPt_eq_upt]
    refine _root_.GlobalTheory.UDense.eval_eq_zero_of_rat L n _ ?_ (tauPt τ B) (isUPt_tauPt τ B)
    intro γ₀ h
    have := congrArg (fun M => M i j) (key (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))))
    simp only [hrat γ₀ h, sub_self] at this
    simpa using this.symm
  rw [← sub_eq_zero, key]
  ext i j
  simpa using hz i j

end GlobalTheory.AlgWtHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicative
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtMul

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def substL (A : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.C (A v.1 v.2.1 m) * MvPolynomial.X (v.1, m, v.2.2)

def substR (B : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.X (v.1, v.2.1, m) * MvPolynomial.C (B v.1 m v.2.2)

theorem eval_bind_substL (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by
  calc MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt Y) (substL A v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt Y) (substL A v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt Y) (substL A v)) = upt (fun σ => A σ * Y σ) := by
        funext v
        simp [substL, upt, Matrix.mul_apply]
      rw [hf]

theorem eval_bind_substR (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q) =
      MvPolynomial.eval (upt (fun σ => X σ * B σ)) Q := by
  calc MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) Q)
      = MvPolynomial.aeval (fun v => MvPolynomial.aeval (upt X) (substR B v)) Q :=
        MvPolynomial.aeval_bind₁ _ _ _
    _ = _ := by
      change MvPolynomial.eval (fun v => MvPolynomial.eval (upt X) (substR B v)) Q = _
      have hf : (fun v => MvPolynomial.eval (upt X) (substR B v)) = upt (fun σ => X σ * B σ) := by
        funext v
        simp [substR, upt, Matrix.mul_apply]
      rw [hf]

theorem defectL_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by
  rw [map_sub, eval_bind_substL]
  simp [evM, Matrix.mul_apply]

theorem defectR_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by
  rw [map_sub, eval_bind_substR]
  simp [evM, Matrix.mul_apply]

theorem evM_ratPt (a : AlgWt L n) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hA : Agrees a b P)
    (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) = LinearMap.toMatrix b b (a.ρ γ) := by
  rw [hA γ γ₀ h]
  ext i j
  rfl

theorem ratPt_one :
    ratPt ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
  funext σ
  simp [ratPt]

theorem ratPt_mul (γ₀ γ₁ : GL (Fin n) L) :
    ratPt ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ := by
  funext σ
  simp [ratPt, Matrix.map_mul]

theorem evM_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧
      ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y →
        evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  intro L _ _ _ n a ι _ _ b P hA
  have h1 : evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 := by
    have hm : ((((1 : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [OneMemClass.coe_one, Units.val_one]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    rw [← ratPt_one, evM_ratPt a b P hA 1 1 hm, map_one, LinearMap.toMatrix_one]
  have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ γ₁ : GL (Fin n) L, γ₁ ∈ GQ0 L n →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * ratPt (γ₁ : Matrix (Fin n) (Fin n) L) σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt (ratPt (γ₁ : Matrix (Fin n) (Fin n) L))) := by
    intro γ₀ h₀ γ₁ h₁
    obtain ⟨γ, hγ⟩ := exists_gq γ₀ h₀
    obtain ⟨γ', hγ'⟩ := exists_gq γ₁ h₁
    have hm : ((((γ * γ' : GQ L n) : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((γ₀ * γ₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) := by
      simp only [Subgroup.coe_mul, Units.val_mul, hγ, hγ', Matrix.map_mul]
    rw [← ratPt_mul, evM_ratPt a b P hA _ _ hm, evM_ratPt a b P hA _ _ hγ, evM_ratPt a b P hA _ _ hγ', map_mul,
      LinearMap.toMatrix_mul]
  have hL : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt Y →
      evM P (upt (fun σ => ratPt (γ₀ : Matrix (Fin n) (Fin n) L) σ * Y σ)) =
        evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) * evM P (upt Y) := by
    intro γ₀ h₀ Y hY
    ext i j
    have e := _root_.GlobalTheory.UDense.eval_eq_zero_of_rat L n (MvPolynomial.bind₁ (substL (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) i m) * P m j)
      (fun γ₁ h₁ => by rw [defectL_eval, hrat γ₀ h₀ γ₁ h₁, sub_self]) Y hY
    rw [defectL_eval, sub_eq_zero] at e
    exact e
  refine ⟨h1, fun X Y hX hY => ?_⟩
  ext i j
  have e := _root_.GlobalTheory.UDense.eval_eq_zero_of_rat L n (MvPolynomial.bind₁ (substR Y) (P i j) -
      ∑ m, P i m * MvPolynomial.C (evM P (upt Y) m j))
    (fun γ₀ h₀ => by rw [defectR_eval, hL γ₀ h₀ Y hY, sub_self]) X hX
  rw [defectR_eval, sub_eq_zero] at e
  exact e

end GlobalTheory.AlgWtMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalDualEqAddSpanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latS_eq_of_lattice_last_coord_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  first | exact @GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | exact GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span | (intros; apply GlobalTheory.Mem.LocalDualBase.localDual_eq_add_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCarryDualStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_maps_latS_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → ∀ (L' : Submodule (𝓞 E) (Fin n → E)) (Y : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))), Y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ x : Fin n → TensorProduct F E (FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((Y⁻¹ : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin n) (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L) → ∀ z ∈ dualSet (σ : E →+* E) J L', ((bc (prV (E := E) w) Y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)) := by
  first | exact @GlobalTheory.Mem.LevDual.unitary_carry_dual | exact GlobalTheory.Mem.LevDual.unitary_carry_dual | (intros; apply GlobalTheory.Mem.LevDual.unitary_carry_dual <;> assumption)
end

