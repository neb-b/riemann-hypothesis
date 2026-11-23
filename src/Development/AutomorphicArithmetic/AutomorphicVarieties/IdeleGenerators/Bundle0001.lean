module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

def mirab (R : Type) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | ![0, 1] ᵥ* (g : Matrix (Fin 2) (Fin 2) R) = ![0, 1]}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [← Matrix.vecMul_vecMul, ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : GL (Fin 2) R where
  val := !![(y : R), x; 0, 1]
  inv := !![((y⁻¹ : Rˣ) : R), -(((y⁻¹ : Rˣ) : R) * x); 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

section Loc

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

def K1 (c : ℕ) : Subgroup (GL (Fin 2) (w.adicCompletion F)) :=
  ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)))).map
    (Matrix.GeneralLinearGroup.map (w.adicCompletionIntegers F).subtype)

def Uop {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) :
    Module.End ℂ V := Hi.dc ρ (K1 w c) (K1 w c) (aff (atFin w (unif w)) 0)

def HasU {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V) (c : ℕ) (lam : ℂ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ v ∈ Hi.fixd ρ (K1 w c) ∧ Uop w ρ c v = lam • v

def IsCondAt (ω : HChar F) (c : ℕ) : Prop :=
  IsLeast {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
    Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} c

def EmbAt {l : ℕ} [Fact l.Prime] (τ : F →+* Qbar l) : Prop := ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖τ (x : F)‖ < 1

def ordI (I : Ideal (𝓞 F)) : ℕ := (Associates.mk w.asIdeal).count (Associates.mk I).factors

end Loc

section Forms

variable {F : Type} [Field F] [NumberField F]

def chiI (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (I : Ideal (𝓞 F)) : ℂ :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 F), (if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0) ^ ordI w I

def GenD (y : Af F) (𝔪 : Ideal (𝓞 F)) : Prop :=
  𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 F),
    Valued.v (pLoc F w y) = WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ))


open Classical in
def coefAt (c : Ideal (𝓞 F) → ℂ) (y : Af F) : ℂ := if h : ∃ 𝔪, GenD y 𝔪 then c h.choose else 0


open Classical in
def coefDiv (c : Ideal (𝓞 F) → ℂ) (𝔮 𝔪 : Ideal (𝓞 F)) : ℂ := if h : ∃ 𝔫, 𝔪 = 𝔮 * 𝔫 then c h.choose else 0

def absF (y : (Af F)ˣ) : ℝ := ∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖pLoc F w (y : Af F)‖

variable [IsTotallyReal F]

def reAt (v : InfinitePlace F) (x : F) : ℝ := (v.embedding x).re

def HasExp (φ : GA F 2 → ℂ) (k : ℕ) (c₀ : (Af F)ˣ → ℂ) (c : Ideal (𝓞 F) → ℂ) : Prop :=
  ∀ (x : TR.Rinf F) (y : (TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ yf : (Af F)ˣ,
    HasSum (fun ξ : {ξ : F // ∀ v, 0 < reAt v ξ} => coefAt c (algebraMap F (Af F) ξ.1 * (yf : Af F)) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ))))
      (φ (TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)) / ((((∏ v, y.val v) * absF yf) ^ ((k : ℝ) / 2) : ℝ) : ℂ) - c₀ yf)


variable (F) in
def locSm (w : HeightOneSpectrum (𝓞 F)) : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) (TR.Sm F 2) :=
  (TR.finRep F 2).comp (locGL F 2 w)

structure IsHol (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (φ : TR.Sm F 2) : Prop where
  aut : TR.IsAutForm φ
  level : ∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))
  cent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g
  wt : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ
  low : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)

def hk (k : ℕ) (w : HeightOneSpectrum (𝓞 F)) (c : ℕ) : Module.End ℂ (TR.Sm F 2) :=
  (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) c

def hkCoef (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (a : Ideal (𝓞 F) → ℂ)
    (𝔪 : Ideal (𝓞 F)) : ℂ :=
  a (w.asIdeal * 𝔪) + chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1) * coefDiv a w.asIdeal 𝔪

structure IsEigHol (k : ℕ) (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (φ : TR.Sm F 2)
    (lam : HeightOneSpectrum (𝓞 F) → ℂ) : Prop where
  hol : IsHol k c ω φ
  ne : φ ≠ 0
  eig : ∀ w, hk k w (c w) φ = lam w • φ

variable {Ω : Type} [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]

structure OrdForm (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) (s : ℤ) (c : HeightOneSpectrum (𝓞 F) → ℕ)
    (m : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ) (a : HeightOneSpectrum (𝓞 F) → Qbar l) (π : TR.CuspSub F 2)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) : Prop where
  reg : π.IsRegAlg
  pol : ∃ χ : HChar F, π.Polarized χ
  cont : Continuous r
  att : AttR ι r π
  det : Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ s * ξ
  ξ_open : IsOpen (ξ.ker : Set (G F Ω))
  fin : {w | c w ≠ 0}.Finite
  ram : ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    (Ine (F := F) A ≤ ξ.ker ↔ c w = 0 ∨ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
  sph : ∀ w, c w = 0 → HasFixed (π.locRep w) (K1 w 0)
  away : ∀ w, c w ≠ 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ lam, HasU w (π.locRep w) (c w) lam ∧ ‖ι.symm lam‖ = 1
  above : ∀ w, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 1 ∧ m w 1 + 2 ≤ m w 0 ∧ m w 0 + m w 1 = s ∧ ‖a w‖ = 1 ∧
    (∃ lam, HasU w (π.locRep w) 1 lam ∧ ‖ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w‖ < 1) ∧
    ∀ τ : F →+* Qbar l, EmbAt w τ → π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf (m w))

end Forms

end UpperTheory.V.Sd
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

def EigAut : Prop :=
  ∀ (k N : ℕ) [NeZero N], 2 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), Continuous ρ → IsIrr ρ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV w) σ →
        (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom =
          X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))) → IsAutR ι ρ

def DirOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (N : ℕ), 0 < N →
    ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu N φ → ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M), M ∣ N ∧ χ.IsPrimitive ∧
      φ = Chr.dirG ℚ Ω (χ.ringHomComp ι.symm.toRingHom)

def PropEG : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ

def SIabs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)) (Φ : Γ →* (Qbar l)ˣ),
    (∀ s, ‖(Φ s : Qbar l)‖ = 1) → IsIrr ρ → ResSum ρ ![1, Φ] → ∀ H : Subgroup Γ, H.Normal →
    (∃ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.Separable) → ¬ IsIrr (ρ.comp H.subtype) →
      (∀ s ∈ H, Cong (Φ s) 1) ∧ ∀ s, Cong (Φ s ^ 2) 1

def EisReg : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (φ θ : G ℚ Ω →* (Qbar l)ˣ)
    (k : ℕ), 2 ≤ k → ∀ ρ, EisRep ι φ θ k ρ → ∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) →
    ∃ s ∈ H, ∃ a : (Qbar l)ˣ, ¬ IsOfFinOrder a ∧
      (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C 1)

def SI : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (φ θ : G ℚ Ω →* (Qbar l)ˣ) (k : ℕ), 2 ≤ k → IsOfFinOrder φ → ∀ ρ, EisRep ι φ θ k ρ →
    (∀ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) → H.Normal →
      (∃ s ∈ H, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s) 1) → IsIrr (ρ.comp H.subtype)) ∧
    ((∃ s, ¬ Cong ((cycBar ℚ Ω l ^ (k - 1) * φ) s ^ 2) 1) → IrrOpen ρ)

def Ad0Irr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IrrOpen ρ → IrrOpen (ad0 ρ)

def IrrAb : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)),
    Continuous r → IrrOpen r → ∀ H H' : Subgroup Γ, IsOpen (H : Set Γ) → H' ≤ H → (∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ H') →
      IsIrr (r.comp H'.subtype)

def Ad0Facts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin 2) (Qbar l)),
    (Continuous ρ → Continuous (ad0 ρ)) ∧
    (∃ P : GL (Fin 3) (Qbar l), (P : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ = P ∧ ∀ s,
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ * (P : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)) = P) ∧
    (∀ (H : Subgroup Γ) (a b : Γ →* (Qbar l)ˣ), IsDiagOn ρ H ![a, b] → IsDiagOn (ad0 ρ) H ![b / a, 1, a / b]) ∧
    (∀ (H : Subgroup Γ) (κ : Fin 2 → ↥H →* (Qbar l)ˣ), IsFlagOn ρ H κ → IsFlagOn (ad0 ρ) H ![κ 0 / κ 1, 1, κ 1 / κ 0]) ∧
    (∀ s (a b : (Qbar l)ˣ), (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) →
      (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly =
        (X - C ((a / b : (Qbar l)ˣ) : Qbar l)) * (X - C 1) * (X - C ((b / a : (Qbar l)ˣ) : Qbar l))) ∧
    ∀ a b : Γ →* (Qbar l)ˣ, (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) → ResSum ρ ![a, b] → ResSum (ad0 ρ) ![b / a, 1, a / b]

def ShapeFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (n : ℕ) (r : Γ →* GL (Fin n) (Qbar l)) (δ : Γ →* (Qbar l)ˣ),
    (∀ (H : Subgroup Γ) (χ : Fin n → Γ →* (Qbar l)ˣ), IsDiagOn r H χ → IsDiagOn (tw r δ) H fun i => χ i * δ) ∧
    (∀ (H : Subgroup Γ) (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), IsDiagOn r H χ → (∀ i, ∀ s ∈ H, χ' i s = χ (e i) s) →
      IsDiagOn r H χ') ∧
    (∀ (H : Subgroup Γ) (κ : Fin n → ↥H →* (Qbar l)ˣ), IsFlagOn r H κ → IsFlagOn (tw r δ) H fun i => κ i * δ.comp H.subtype) ∧
    (∀ χ : Fin n → Γ →* (Qbar l)ˣ, (∀ s, ‖(δ s : Qbar l)‖ = 1) → ResSum r χ → ResSum (tw r δ) fun i => χ i * δ) ∧
    (∀ (χ χ' : Fin n → Γ →* (Qbar l)ˣ) (e : Equiv.Perm (Fin n)), (∀ i s, ‖(χ i s : Qbar l)‖ = 1) → ResSum r χ →
      (∀ i s, Cong (χ' i s) (χ (e i) s)) → ResSum r χ') ∧
    (IsIrr r → IsIrr (tw r δ))

def ResFacts : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
    Continuous (galEmb F E Ω) ∧ IsOpen (galOf F E Ω : Set (G F Ω)) ∧ (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l ∧
    (IsIrr (r.comp (galOf F E Ω).subtype) ↔ IsIrr (r.comp (galEmb F E Ω))) ∧
    (IrrOpen r → IrrOpen (r.comp (galEmb F E Ω))) ∧
    (∀ τ, TypeAway r τ → TypeAway (r.comp (galEmb F E Ω)) fun i => (τ i).comp (galEmb F E Ω)) ∧
    ∀ m ψ A, OrdAt r m ψ A → OrdAt (r.comp (galEmb F E Ω)) m (fun i => (ψ i).comp (galEmb F E Ω)) A

def SelfTwGal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop), (∀ v B B', sat v B → sat v B' → B = B') →
    Continuous r → AttachedSys ι r sat → ∀ (η : HChar F) (m : ℕ), 0 < m → η ^ m = 1 → η ≠ 1 → SelfTw sat η →
    ∃ δ : G F Ω →* (Qbar l)ˣ, δ ≠ 1 ∧ IsOpen (δ.ker : Set (G F Ω)) ∧ RepIso r (tw r δ) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω], IsNormChar E η →
        δ.comp (galEmb F E Ω) = 1

def UpQuad : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutR ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpCyc : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (Module.finrank F E).Prime → ∀ (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def UpSol : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

def TwC : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutC ι r → IsAutC ι (tw r κ)

def TwR : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (κ : G F Ω →* (Qbar l)ˣ), IsAlgChar ι κ → IsAutR ι r → IsAutR ι (tw r κ)

def AlgCyc : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    (∀ (j : ℤ) (χ : G F Ω →* (Qbar l)ˣ), IsOpen (χ.ker : Set (G F Ω)) → IsAlgChar ι (cycBar F Ω l ^ j * χ)) ∧
    (∀ κ κ' : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ' → IsAlgChar ι (κ * κ')) ∧
    ∀ κ : G F Ω →* (Qbar l)ˣ, IsAlgChar ι κ → IsAlgChar ι κ⁻¹

def AlgRes : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (κ : G F Ω →* (Qbar l)ˣ),
    IsAlgChar ι κ → IsAlgChar ι (κ.comp (galEmb F E Ω))

def Twist : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ discr K → ∀ (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), IsCC c →
    ∃ κ : G K Ω →* (Qbar l)ˣ, IsTwist ι c κ

def RibetLat : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    (ρ : Γ →* GL (Fin 2) (Qbar l)) (a b : Γ →* (Qbar l)ˣ), Continuous ρ → IsIrr ρ → (∀ s, ‖(a s : Qbar l)‖ = 1 ∧ ‖(b s : Qbar l)‖ = 1) →
    ResSum ρ ![a, b] → ∀ g₀ : Γ, ¬ Cong (a g₀) (b g₀) → ∃ ρ' : Γ →* GL (Fin 2) (Qbar l), RepIso ρ ρ' ∧
      ρ' g₀ 0 1 = 0 ∧ ρ' g₀ 1 0 = 0 ∧ (∀ s, ‖ρ' s 0 0 - a s‖ < 1 ∧ ‖ρ' s 1 1 - b s‖ < 1 ∧ ‖ρ' s 1 0‖ < 1 ∧ ‖ρ' s 0 1‖ ≤ 1) ∧
      ∃ s, ‖ρ' s 0 1‖ = 1

end UpperTheory.V.Sd
end
end

