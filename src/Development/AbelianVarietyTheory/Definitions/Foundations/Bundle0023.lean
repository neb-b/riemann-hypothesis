module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleTwistIffAdmissibleUntwisted
section
noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def admitted {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = mat W s *ᵥ pr b) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def psiCyc {l : ℕ} [Fact l.Prime] (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) : Qbar l :=
  ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def AdmT {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (_gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) : Prop :=
  1 ≤ e ∧ 1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (ψ 1 = 1 ∧ ∀ a b : (ZMod l)ˣ, ψ ((a * b : (ZMod l)ˣ) : ZMod l) = ψ a * ψ b) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) →
      pr (X.galB l s b) = ((cycBar ℚ Ω l s : Qbar l) ^ e * (psiCyc ψ s)⁻¹) • (mat W s *ᵥ pr b)) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def unTw {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l :=
  tw W (cycBar ℚ Ω l ^ e * χ⁻¹)

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTPresNuOfPolys (A : ValuationSubring Ω) (c : Coef l) (m c₀ : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω)
    {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    (∀ i, (P i).eval ζ ≠ 0) ∧ GlobalTheory.Col.KumPres A (m - c₀) m (ζ ^ l ^ c₀) (Z m) (fun i => (P i).eval ζ) o

def HTLawCsOfCoef (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∃ ζ : ℕ → Ω, (∀ m, IsPrimitiveRoot (ζ m) (l ^ m) ∧ ζ (m + 1) ^ l = ζ m) ∧
    ∀ m, m₀ ≤ m → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m c₀ Z (ζ m) P o ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
        Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j (ζ m) P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j (ζ m)))

def Pin7 (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω → (Qbar l)ˣ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (a a' κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l)
    (L : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l) (m₀ c₀ n₀ : ℕ),
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ (ν σ : Qbar l) = a) ∧
    ‖a‖ = 1 ∧ ‖a'‖ = 1 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ κ ≠ 0 ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧
    (∀ n, L.coeff n ∈ c.O) ∧ HTLawCsOfCoef A c Z j m₀ c₀ Rhs ∧
    (∀ m, m₀ ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (m - c₀) (Rhs m ψ z) (v m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) ∧
    (∀ r, 1 ≤ r → ∀ x : (ZMod (l ^ r))ˣ, χ r x = (φ ((x : ZMod (l ^ r)).val : ZMod l))⁻¹) ∧
    ∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTCoL (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m ((l : Qbar l) ^ c₀ * Z m s y) ((l : Qbar l) ^ c₀ * h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

theorem htCoL_of_eq (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) (hZ : ∀ s, Z m s y = h * lamv l m s) : HTCoL A c j Z m c₀ y h :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun s _ _ => by simp [Cg, hZ, mul_assoc]⟩

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.MapEvalOfFixCoeff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tval_coe (Q : Polynomial (Qbar l)) {N : ℕ} (hN : Q.natDegree < N) (z : Qbar l) :
    tval (Q : PowerSeries (Qbar l)) N z = Q.eval (z - 1) := by
  rw [Polynomial.eval_eq_sum_range' hN]
  simp only [tval, Polynomial.coeff_coe]

theorem tval_dirac {y N : ℕ} (hN : y < N) (z : Qbar l) : tval ((1 + PowerSeries.X) ^ y) N z = z ^ y := by
  have h : (((1 + Polynomial.X) ^ y : Polynomial (Qbar l)) : PowerSeries (Qbar l)) = (1 + PowerSeries.X) ^ y := by simp
  rw [← h, tval_coe _ (lt_of_le_of_lt _ hN)]
  · simp
  · refine Polynomial.natDegree_pow_le.trans ?_
    rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C, mul_one]

theorem mass_dirac {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x y : ℕ} (hx : x < l ^ r) (hy : y < l ^ r) :
    mass ((1 + PowerSeries.X) ^ y) r ξ x = if x = y then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have h0 : ξ ≠ 0 := hξ.ne_zero (by omega)
  have hy' : y < l ^ (3 * r) := hy.trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have e : ∀ k, ξ ^ (l ^ r - (k * x) % l ^ r) * tval ((1 + PowerSeries.X) ^ y) (l ^ (3 * r)) (ξ ^ k) = (ξ ^ y / ξ ^ x) ^ k := by
    intro k
    rw [tval_dirac hy', pow_sub₀ _ h0 (Nat.mod_lt _ (by omega)).le, hξ.pow_eq_one,
      ← pow_eq_pow_mod _ hξ.pow_eq_one, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm x k, mul_comm y k]
    field_simp
  simp only [mass, e]
  split_ifs with h1
  · subst h1; simp [h0]
  · have hne : ξ ^ y / ξ ^ x ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ h0)] at h
      exact h1 (hξ.pow_inj hx hy h.symm)
    have := mul_geom_sum (ξ ^ y / ξ ^ x) (l ^ r)
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm x, mul_comm y, pow_mul, pow_mul, hξ.pow_eq_one, one_pow, one_pow, div_one,
      sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

end GlobalTheory.KZ
end
end

