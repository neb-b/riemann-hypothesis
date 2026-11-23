module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ChiK
section
noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def chiK (l : ℕ) [Fact l.Prime] (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def htv (j : Ω →+* Qbar l) (ζ : Ω) {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) (b : ℕ) : Qbar l :=
  ∑ i, o i * j (ζ ^ b * (Polynomial.derivative (P i)).eval (ζ ^ b) / (P i).eval (ζ ^ b))

def HTPres (A : ValuationSubring Ω) (c : Coef l) (m : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω) {ι : Type}
    [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    GlobalTheory.Col.KumPres A m m ζ (Z m) (fun i => (P i).eval ζ) o

def tval (L : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : Qbar l := ∑ n ∈ Finset.range N, L.coeff n * (z - 1) ^ n

def mass (L : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) (x : ℕ) : Qbar l :=
  ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval L (l ^ (3 * r)) (ξ ^ k)

def HTLawAt (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∀ m, m₀ ≤ m → ∃ (ζ : Ω) (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPres A c m Z ζ P o ∧
    ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
      Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j ζ P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j ζ))

def Pin (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω →* (Qbar l)ˣ)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (a a' κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l)
    (L : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l) (m₀ c₀ n₀ : ℕ),
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ (ν σ : Qbar l) = a) ∧
    ‖a‖ = 1 ∧ ‖a'‖ = 1 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ κ ≠ 0 ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧
    (∀ n, L.coeff n ∈ c.O) ∧ HTLawAt A c Z j m₀ c₀ Rhs ∧
    (∀ m, m₀ ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (m - c₀) (Rhs m ψ z) (v m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) ∧
    ∀ r, 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def FixIc (c : Coef l) (a : Qbar l) : Prop :=
  ∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ x : Qbar l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ a = a

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
section
noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eval_liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (liftK X l n a) = a :=
  Classical.epsilon_spec (AdicCompletion.eval_surjective (idl l) (X.Kl l) n a)

theorem eval_clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {w : X.K} (h : w ≠ 0) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n w) = X.cls l n (Units.mk0 w h) := by
  unfold clsK
  rw [dite_eq_left h]
  exact eval_liftK X l n _

theorem clsK_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : clsK X l n 0 = 0 := by
  unfold clsK
  exact dif_neg fun h => h rfl

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f g : X.Kˣ) :
    X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  unfold Tower.cls
  rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

theorem map_liftSL (M : ℕ) (g : SL(2, ZMod M)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M g) = g :=
  Classical.epsilon_spec (GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M g)

theorem liftSL_map_mul_inv_mem (M : ℕ) (γ : SL(2, ℤ)) :
    liftSL M (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, map_liftSL, mul_inv_cancel]

theorem exists_place_over (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] :
    ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 := by

  let R : Subring Ω := (Int.castRingHom Ω).range
  let x : R := ⟨(l : Ω), RingHom.mem_range.2 ⟨(l : ℤ), by simp⟩⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
    obtain ⟨n, hn⟩ := RingHom.mem_range.1 y.2
    have h1 : ((l * n : ℤ) : Ω) = 1 := by
      have hv := congrArg Subtype.val hy
      rw [Subring.coe_mul, Subring.coe_one, ← hn] at hv
      rw [Int.cast_mul, Int.cast_natCast]
      exact hv
    have h2 : (l : ℤ) * n = 1 := by
      have h5 : algebraMap ℚ Ω (((l * n : ℤ)) : ℚ) = algebraMap ℚ Ω 1 := by
        rw [map_intCast, map_one]
        exact h1
      exact_mod_cast (algebraMap ℚ Ω).injective h5
    have h3 := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have h4 := (Fact.out : l.Prime).two_le
    omega
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (Ideal.span {x}) hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).1 (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

theorem cycMod_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) :
    Function.Surjective (cycMod ℚ Ω l r) := by
  intro x
  obtain ⟨A, hA⟩ := exists_place_over Ω l
  obtain ⟨s, hs⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA r x
  exact ⟨_, hs⟩

theorem cycMod_repC [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    cycMod ℚ Ω l r (repC (Ω := Ω) l r x) = x :=
  Classical.epsilon_spec (cycMod_surjective Ω l r x)

theorem galB_section_zero (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (w : ℕ) (a : X.Khat l) :
    X.galB l s (fun u => (u 0) ^ w • a) = fun u => (u 0) ^ w • X.kmap l (X.gal s) a := by
  funext u
  show X.kmap l (X.gal s)
      (((![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1] : Fin 2 → ℤ_[l]) 0) ^ w • a) = _
  rw [map_smul, Matrix.cons_val_zero]

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ZetaElementsUnramifiedOrdinaryOfEulerSystemInert
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

def ZetaSysUr2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), Sys W c y S' ∧ NzAt W A y

theorem zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (h : ZetaSysUr2) : ZetaUr := fun l _ Ω _ _ _ ι e S A W g hN hS => es_of_sys (h l Ω ι e S A W g hN hS)

def ExistsZetaEulerSystemIwasawaData (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' ∧ IwSys2 c A ν Z ∧ SpLink A e χ Z y ∧ Pin e A W c ν χ Z

def ZetaEulerSystemNonvanishing (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∀ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω → (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' → IwSys2 c A ν Z → SpLink A e χ Z y → Pin e A W c ν χ Z → NzAt W A y

theorem zetaSysU_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaSysUr2 := by
  intro l _ Ω _ _ _ ι e S A W g hN hS
  obtain ⟨c, y, S', ν, χ, Z, h1, h2, h3, h4⟩ := hG l Ω ι e S A W g hN hS
  exact ⟨c, y, S', h1, hL l Ω ι e S A W g hN hS c y S' ν χ Z h1 h2 h3 h4⟩

theorem zetaUr_of_halves2 (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω → (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : ExistsZetaEulerSystemIwasawaData Pin) (hL : ZetaEulerSystemNonvanishing Pin) : ZetaUr :=
  zetaElementsUnramifiedOrdinary_of_eulerSystem_inertia (zetaSysU_of_halves2 Pin hG hL)

end GlobalTheory.KZ

end
end

