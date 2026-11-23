module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet

abbrev Idx (I : Type) [Fintype I] (n : ℕ) : Type := {ν : I → ℕ // ∑ i, ν i ≤ n + 1}

structure JetRing (R : Type) [CommRing R] (I : Type) [Fintype I] (n : ℕ) where

  B : Type
  [cr : CommRing B]
  [alg : Algebra R B]

  b : Module.Basis (Idx I n) R B

  one : b ⟨0, by simp⟩ = 1

  mul : ∀ ν ν' : Idx I n, b ν * b ν' =
    if h : ∑ i, (ν.1 + ν'.1) i ≤ n + 1 then (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) • b ⟨ν.1 + ν'.1, h⟩ else 0

  π : B →+* R

  π_eq : ∀ x, π x = b.repr x ⟨0, by simp⟩

  κ : DividedPowers (RingHom.ker π)

  nil : IsNilDP κ

attribute [instance] JetRing.cr JetRing.alg

section Alg

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

def admitted (X : Obj F 𝔠 (Sp R)) (N : I → Module.End R (HdR X.A)) : Prop :=
  (∀ i (a : 𝓞 F), Commute (N i) (act (dp0 R) (𝟙 _) X.rm a)) ∧ (∀ i j, N i * N j = 0) ∧
    ∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ →
      (∀ i x y, ψ (N i x) y + ψ x (N i y) = 0) ∧ ∀ i j x y, ψ (N i x) (N j y) = 0

end Alg

abbrev FR (E : Type) [Field E] : Type := maximalRealSubfield E

section Cx

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)}

structure Unif (φ : I → E →+* ℂ) (L : Set E) (z : I → ℂ) (X : Obj (FR E) 𝔠 (Sp ℂ)) where

  e : Fin (Module.finrank ℚ (FR E)) ≃ I

  c : 𝔠.elt

  pos : IsTotPos (c : FR E)

  u : HolUnif X.A (X.diag c) (Module.finrank ℚ (FR E))

  lat : ∀ w, w ∈ u.Λ ↔ ∃ x ∈ L, w = fun j ↦ defCoord φ z x (e j)

  act : ∀ (a : 𝓞 (FR E)) w, u.ex (fun j ↦ φ (e j) ((a : FR E) : E) * w j) = u.ex w ≫ X.rm.act a

  h : I → ℝ

  ah : ∃ χ, u.IsAH (Matrix.diagonal fun j ↦ (h (e j) : ℂ)) χ

variable {φ : I → E →+* ℂ} {L : Set E} {z : I → ℂ} {X : Obj (FR E) 𝔠 (Sp ℂ)}

def Unif.IsDet (U : Unif φ L z X) (δ : X.DetOmega) (C : ℂ) : Prop :=
  ∀ (v : Fin (Module.finrank ℚ (FR E)) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ),
    (∀ j, U.u.IsDiff (W j) (v j).hom) → δ v = C * W.det

def Unif.IsCMVec (U : Unif φ L z X) (i : I) (y : HdR X.A) (w : ℂ) : Prop :=
  (∀ (a : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) a * w' j) = U.u.ex w' ≫ α) →
    push (dp0 ℂ) (𝟙 _) α y = φ i a • y) ∧
  ∃ v, IsLieImage y v ∧ U.u.IsDiff (Pi.single (U.e.symm i) w) v

structure CxPt (𝔠 : FracId (FR E)) (φ : I → E →+* ℂ) (L : Set E) where

  X : Obj (FR E) 𝔠 (Sp ℂ)

  U : Unif φ L 0 X

  δ : X.DetGen

  C : ℂ

  det : U.IsDet δ.1 C

  ψ : LinearMap.BilinForm ℂ (HdR X.A)

  pol : IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ

  y : I → HdR X.A

  w : I → ℂ

  s : I → ℂ

  cm : ∀ i, U.IsCMVec i (y i) (w i)

def CxPt.low (T : CxPt 𝔠 φ L) (i : I) : Module.End ℂ (HdR T.X.A) :=
  T.s i • (T.ψ.flip (T.y i)).smulRight (T.y i)

def CxPt.A (T : CxPt 𝔠 φ L) (i : I) : ℂ := Real.pi * T.U.h i * T.s i * T.w i ^ 2

def CxPt.IsOver (T : CxPt 𝔠 φ L) {R : Type} [CommRing R] (σ : R →+* ℂ)
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen) (N : I → Module.End R (HdR X₀.A)) : Prop :=
  ∃ (p : T.X.A.left ⟶ X₀.A.left) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) T.X.A σ (spMap σ) p),
    T.X.IsPullBy X₀ (spMap σ) p ∧ Obj.DetCorr σ p δ₀.1 T.δ.1 ∧
      ∀ i x₀ x, m.Corr x₀ x → m.Corr (N i x₀) (T.low i x)

end Cx

def IsEis {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) (k : ℕ) (G : ((F →+* ℝ) → ℂ) → ℂ) : Prop :=
  (k ≠ 2 → ∀ z ∈ halfSpace F, HasSum (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k 0 z) (G z)) ∧
    (k = 2 → ∃ H, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsContinuation 𝔞 𝔟 H ∧ G = H 0)

def EisExp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : FracId F) (s : ℕ), 1 ≤ s →
    ∃ G, IsEis 𝔞 𝔟 (2 * s) G ∧ DifferentiableOn ℂ G (halfSpace F) ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 (2 * s) G

def EisFourier : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : FracId F) (k : ℕ), 1 ≤ k → ∀ G,
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : (𝔞 * 𝔟).elt → ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
      HasFourier 𝔞 𝔟 (fun z ↦ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) * G z / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k) a ∧
      a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ ∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n

def ModelInt : Prop := AllLat fun E _ _ I _ d φ _ _ 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ L) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i)

def JetInt : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L =>
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l + ((∑ i, κ i : ℕ) : ℝ) * c_vp 𝔣 l)
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s)))

end GlobalTheory.LatJet
