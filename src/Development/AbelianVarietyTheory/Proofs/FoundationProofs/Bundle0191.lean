module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLower
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattner
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.HarmonicParam

variable {p q : ℕ}

theorem card_filter_sum (P : Ix p q → Prop) [DecidablePred P] (A : Finset (Fin p)) (B : Finset (Fin q))
    (hA : ∀ i, P (Sum.inl i) ↔ i ∈ A) (hB : ∀ j, P (Sum.inr j) ↔ j ∈ B) :
    (Finset.univ.filter P).card = A.card + B.card := by
  rw [← Finset.card_disjSum]
  congr 1
  ext x
  cases x <;> simp [hA, hB]

theorem rhoNC_of_strictAnti (lam : Ix p q → ℚ) (h1 : StrictAnti fun i => lam (Sum.inl i))
    (h2 : StrictAnti fun j => lam (Sum.inr j)) (h3 : ∀ i j, lam (Sum.inr j) < lam (Sum.inl i)) :
    (∀ i : Fin p, rhoNC lam (Sum.inl i) = (q : ℚ) / 2 - ((p : ℚ) - 1 - 2 * (i.1 : ℚ)) / 2) ∧
    (∀ j : Fin q, rhoNC lam (Sum.inr j) = -(p : ℚ) / 2 - ((q : ℚ) - 1 - 2 * (j.1 : ℚ)) / 2) := by
  have h1' : ∀ i i', lam (Sum.inl i) < lam (Sum.inl i') ↔ i' < i := fun i i' => h1.lt_iff_gt
  have h2' : ∀ i i', lam (Sum.inr i) < lam (Sum.inr i') ↔ i' < i := fun i i' => h2.lt_iff_gt
  have h4 : ∀ i j, ¬ lam (Sum.inl i) < lam (Sum.inr j) := fun i j => (h3 i j).not_gt
  constructor
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ Finset.univ (by simp [sameBlock]) (by simp [sameBlock, h3]),
      card_filter_sum _ ∅ ∅ (by simp [sameBlock]) (by simp [sameBlock, h4]),
      card_filter_sum _ (Finset.Ioi i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock]),
      card_filter_sum _ (Finset.Iio i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock])]
    have hi : i.1 + 1 ≤ p := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ ∅ (by simp [sameBlock, h4]) (by simp [sameBlock]),
      card_filter_sum _ Finset.univ ∅ (by simp [sameBlock, h3]) (by simp [sameBlock]),
      card_filter_sum _ ∅ (Finset.Ioi i) (by simp [sameBlock]) (by simp [sameBlock, h2']),
      card_filter_sum _ ∅ (Finset.Iio i) (by simp [sameBlock]) (by simp [sameBlock, h2'])]
    have hi : i.1 + 1 ≤ q := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

theorem hcParam_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) →
    IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧
    ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  intro p q n hn ap am hap ham _ _
  have hn' : (p : ℚ) + q + 1 ≤ n := by exact_mod_cast hn
  have h1 : StrictAnti fun i => hcParam n ap am (Sum.inl i) := by
    intro i j hij
    have a : (ap j : ℚ) ≤ ap i := by exact_mod_cast hap hij.le
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h2 : StrictAnti fun i => hcParam n ap am (Sum.inr i) := by
    intro i j hij
    have a : (am i.rev : ℚ) ≤ am j.rev := by exact_mod_cast ham (Fin.rev_le_rev.2 hij.le)
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h3 : ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
    intro i j
    have a : (0 : ℚ) ≤ ap i := Nat.cast_nonneg _
    have b : (0 : ℚ) ≤ am j.rev := Nat.cast_nonneg _
    have c : (0 : ℚ) ≤ j.1 := Nat.cast_nonneg _
    have d : (i.1 : ℚ) + 1 ≤ p := by exact_mod_cast i.2
    simp only [hcParam]
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h3⟩
  · rintro (a | a) (b | b) h
    · rw [h1.injective h]
    · exact absurd h (h3 a b).ne'
    · exact absurd h (h3 b a).ne
    · rw [h2.injective h]
  · rintro (a | a) (b | b) h
    · exact h1 h
    · exact h.elim
    · exact h.elim
    · exact h2 h
  · rintro (a | a)
    · exact ⟨2 * (ap a) + 2 * (p - (a.1 + 1)) + (n - p - q + 1), by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-2 * (am a.rev) - 2 * (a.1 + 1) - (n - p - q - 1), by simp only [hcParam]; push_cast; ring⟩
  · rintro (a | a) (b | b)
    · exact ⟨ap a - ap b - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨ap a + (p - (a.1 + 1)) + am b.rev + (b.1 + 1) + (n - p - q),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-(ap b + (p - (b.1 + 1)) + am a.rev + (a.1 + 1) + (n - p - q)),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨am b.rev - am a.rev - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
  · obtain ⟨r1, r2⟩ := rhoNC_of_strictAnti _ h1 h2 h3
    funext a
    rcases a with a | a
    · simp only [blattner, r1, hcParam, wtK]
      ring
    · simp only [blattner, r2, hcParam, wtK]
      ring

end GlobalTheory.HarmonicParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DilMonomial
section
noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix

def rectDiag (p q : ℕ) (f : ℕ → ℝ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then ((f i : ℝ) : ℂ) else 0

def diagP (p q : ℕ) (σ : ℕ → ℝ) : Mat p q :=
  Matrix.fromBlocks 0 (rectDiag p q σ) (rectDiag p q σ)ᴴ 0

def tanhDiag (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.diagonal fun a => (if a.isLeft then 1 else -1) *
    ((σ (posIx a) * Real.tanh (t * σ (posIx a)) : ℝ) : ℂ)

def hypMat (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin p => ((Real.cosh (t * σ i) : ℝ) : ℂ))
    (rectDiag p q fun i => Real.sinh (t * σ i)) (rectDiag p q fun i => Real.sinh (t * σ i))ᴴ
    (Matrix.diagonal fun j : Fin q => ((Real.cosh (t * σ j) : ℝ) : ℂ))

def dil {p q : ℕ} (n : ℕ) (u : Ix p q → ℝ) : Pol p q n 0 →ₗ[ℂ] Pol p q n 0 :=
  ((Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) : ℝ) : ℂ) •
    (MvPolynomial.aeval fun l : Ln p q n 0 =>
      (MvPolynomial.C ((Real.exp (u l.1) : ℝ) : ℂ) * MvPolynomial.X l : Pol p q n 0)).toLinearMap

theorem diagonalElement_mem (p q : ℕ) (σ : ℕ → ℝ) : diagP p q σ ∈ pR p q := pY_mem (rectDiag p q σ)

theorem dil_monomial {p q n : ℕ} (u : Ix p q → ℝ) (α : Ln p q n 0 →₀ ℕ) (c : ℂ) :
    dil n u (MvPolynomial.monomial α c) =
      ((Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) : ℝ) : ℂ) • MvPolynomial.monomial α c := by
  have h : Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) =
      Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) * ∏ l : Ln p q n 0, Real.exp (u l.1) ^ α l := by
    simp only [← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add, Finset.sum_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h, Complex.ofReal_mul, mul_smul, dil, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.algebraMap_eq, Complex.ofReal_prod, Complex.ofReal_pow]
  ring

theorem dil_dil_neg {p q n : ℕ} (u : Ix p q → ℝ) (Φ : Pol p q n 0) : dil n u (dil n (-u) Φ) = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), hP, hQ]
  | monomial α c =>
    rw [dil_monomial, map_smul, dil_monomial, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      ← Finset.sum_add_distrib]
    simp

theorem dil_zero {p q n : ℕ} (Φ : Pol p q n 0) : dil n 0 Φ = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add (f := _), hP, hQ]
  | monomial α c => rw [dil_monomial]; simp

end GlobalTheory.FockDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEquivariantTensorMapOfCyclicCommuting
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockBilin

theorem gen_ind {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : V) (h : genSub act {x₀} = ⊤)
    (N : Submodule ℂ V) (h0 : x₀ ∈ N) (hs : ∀ Z, ∀ y ∈ N, act Z y ∈ N) (x : V) : x ∈ N := by
  have hle : genSub act {x₀} ≤ N := sInf_le ⟨by simpa using h0, hs⟩
  rw [h] at hle
  exact hle Submodule.mem_top

theorem uniq {p q : ℕ} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ U) (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : U)
    (h : genSub act {x₀} = ⊤) (f g : U →ₗ[ℂ] V)
    (hf : ∀ Z x, f (act Z x) = a Z (f x)) (hg : ∀ Z x, g (act Z x) = a Z (g x))
    (h0 : f x₀ = g x₀) : f = g := by
  ext x
  have := gen_ind act x₀ h (LinearMap.eqLocus f g) h0 (fun Z y hy => by
    rw [LinearMap.mem_eqLocus] at hy ⊢
    rw [hf, hg, hy]) x
  exact this

theorem exists_bilin : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  intro p q r s V _ _ a₁ a₂ hc M₁ M₂ i₁ i₂ h₁ h₂ x₀ y₀ g₁ g₂ h0
  have hc' : ∀ Y Z v, a₁ Y (a₂ Z v) = a₂ Z (a₁ Y v) := fun Y Z v =>
    LinearMap.congr_fun (hc Y Z) v
  let N : Submodule ℂ M₂.V :=
    { carrier := {y | ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y}
      add_mem' := by
        rintro y y' ⟨f, hf, e⟩ ⟨g, hg, e'⟩
        exact ⟨f + g, fun Z x => by simp [hf, hg], by simp [e, e']⟩
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro c y ⟨f, hf, e⟩
        exact ⟨c • f, fun Z x => by simp [hf], by simp [e]⟩ }
  have hN : ∀ y, ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y := by
    intro y
    refine gen_ind M₂.act y₀ g₂ N ⟨i₁, h₁, h0⟩ ?_ y
    rintro Z y ⟨f, hf, e⟩
    exact ⟨a₂ Z ∘ₗ f, fun Y x => by simp [hf, hc'], by simp [e, h₂]⟩
  choose F hF hF0 using hN
  have u := uniq M₁.act a₁ x₀ g₁
  have hadd : ∀ y y', F (y + y') = F y + F y' := fun y y' =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hsmul : ∀ (c : ℂ) y, F (c • y) = c • F y := fun c y =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hact : ∀ Z y, F (M₂.act Z y) = a₂ Z ∘ₗ F y := fun Z y =>
    u _ _ (hF _) (fun Y x => by simp [hF, hc']) (by simp [hF0, h₂])
  have hy0 : F y₀ = i₁ := u _ _ (hF _) h₁ (by rw [hF0, h0])
  let G : M₂.V →ₗ[ℂ] M₁.V →ₗ[ℂ] V := { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hG : ∀ x y, TensorProduct.lift G.flip (x ⊗ₜ y) = F y x := fun x y => by
    simp [G]
  refine ⟨TensorProduct.lift G.flip, ?_, ?_, ?_, ?_⟩
  · intro Z x y; rw [hG, hG, hF]
  · intro Z x y; rw [hG, hG, hact]; rfl
  · intro x; rw [hG, hy0]
  · intro y; rw [hG, hF0]

end GlobalTheory.FockBilin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompact
section
open Formalism.BasicNotions.TH

namespace GlobalTheory

theorem mat_compact_eq_sum_units {n : ℕ} (Z : Mat n 0) :
    Z = ∑ a : Fin n, ∑ b : Fin n,
      Z (Sum.inl a) (Sum.inl b) • Eab (Sum.inl a : Ix n 0) (Sum.inl b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Eab,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem gkMod_compact_glRel {n : ℕ} (M : GKMod n 0) :
    Formalism.REAL.GlRel (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b))) := by
  intro a b c d
  show M.act _ * M.act _ - M.act _ * M.act _ = _
  rw [← M.lie, map_sub]
  congr 1
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')
  · split_ifs with h
    · subst h; simp [Eab]
    · rw [Eab, Eab, Matrix.single_mul_single_of_ne, map_zero]
      intro h'; exact h (Sum.inl_injective h')

theorem gkMod_compact_irr_units {n : ℕ} (M : GKMod n 0) (h : Formalism.MainNotions.SchurIrreducible.IrrGK M)
    (S : Submodule ℂ M.V)
    (hS : ∀ a b : Fin n, ∀ x ∈ S, M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)) x ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine h.2 S fun Z y hy => ?_
  rw [mat_compact_eq_sum_units Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b y hy)

theorem gkMod_compact_isHW_units {n : ℕ} (M : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V)
    (h : IsHW M.act Λ v) :
    Formalism.REAL.IsHW (fun a b : Fin n => M.act (Eab (Sum.inl a : Ix n 0) (Sum.inl b)))
      (fun a => ((Λ (Sum.inl a) : ℚ) : ℂ)) v := by
  obtain ⟨-, h1, h2⟩ := h
  simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1 h2
  exact ⟨fun a => h1 _, fun a b hab => h2 (Sum.inl a) (Sum.inl b) hab⟩

theorem exists_intertwiner_map_highestVector :
    ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V),
      Formalism.MainNotions.SchurIrreducible.IrrGK M → Formalism.MainNotions.SchurIrreducible.IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' →
      ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  intro n M M' Λ v v' hM hM' hv hv'
  have w := gkMod_compact_isHW_units M Λ v hv
  have w' := gkMod_compact_isHW_units M' Λ v' hv'
  obtain ⟨T, hT⟩ := exists_linearEquiv_of_irreducible_isHW M.V M'.V n _ _ _ v v'
    (gkMod_compact_glRel M) (gkMod_compact_glRel M') (gkMod_compact_irr_units M hM)
    (gkMod_compact_irr_units M' hM') w w' hv.1 hv'.1
  obtain ⟨S, hS, hvS, htop⟩ :=
    exists_stable_submodule_topWeight_line M'.V n _ _ v' (gkMod_compact_glRel M') w'
  have hStop : S = ⊤ := by
    rcases gkMod_compact_irr_units M' hM' S hS with h | h
    · rw [h, Submodule.mem_bot] at hvS
      exact absurd hvS hv'.1
    · exact h
  obtain ⟨c, hc⟩ := htop (T v) (by rw [hStop]; trivial) (fun a => by
    rw [← hT a a v, w.1 a, map_smul])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, map_eq_zero_iff T T.injective] at hc
    exact hv.1 hc
  refine ⟨c⁻¹ • T.toLinearMap, ?_, fun Z x => ?_⟩
  · simp [hc, smul_smul, hc0]
  · have key : T (M.act Z x) = M'.act Z (T x) := by
      rw [mat_compact_eq_sum_units Z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hT a b x]
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, key, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfIsPlaceOver
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory

theorem exists_tameGenAt_of_isPlaceOver :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)),
      IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  fun E Ω _ _ _ _ _ A v h => GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω v A h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
section
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.GaussInt

theorem gaussSum_mul_gaussSum_inv_of_isPrimitive {K : Type} [Field K] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter K N} {ψ : AddChar (ZMod N) K} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : K) := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  rw [Finset.sum_eq_single (1 : ZMod N)]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

end GlobalTheory.GaussInt
end

