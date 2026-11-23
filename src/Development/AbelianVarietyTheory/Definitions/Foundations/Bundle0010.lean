module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def zt (ε : Ω →+* ℂ) (l n : ℕ) : Ω := eOm ε (1 / (l : ℚ) ^ n)

def Stab (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) : Prop := ∀ x, s x ∈ A ↔ x ∈ A

def InZl (ε : Ω →+* ℂ) (l n : ℕ) (F : Ω) : Prop := ∃ D : ℕ, ¬ l ∣ D ∧ (D : Ω) * F ∈ Subring.closure {zt ε l n}


open Classical in
def IsNT (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  ∃ τ : (ZMod (l ^ n))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, τ a (zt ε l n) = zt ε l n ^ (a : ZMod (l ^ n)).val) ∧
    (l : Ω) ^ (n - m) * F' = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m]), τ a F

def KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) : Subfield X.K :=
  RingHom.eqLocusField (X.sl (ofSL (ModularGroup.T ^ L))).toRingEquiv.toRingHom (RingHom.id X.K)

variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

structure IsCusp (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) : Prop where
  int : ∀ x, x ∈ A ↔ IsInt (p := p) (j x)
  alg : ∀ x, IsAlgZp (p := p) (j x)
  root : ∀ n, j (zt ε p n) = T.ζ n
  dense : ∀ (k : ℕ) (e : Ωl), IsInt (p := p) e → IsAlgZp (p := p) e → ∃ a ∈ A, Cong (p := p) k e (j a)
  down : ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x)
  up : ∀ (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x)

structure IsIo (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl) (n : ℕ)
    (ψ : O0 p →+* Ωl) (io : KT X (p ^ n) →+* Ωl) : Prop where
  ev : ∀ (y : KT X (p ^ n)) (S : Finset Ω),
    (∀ r, (X.exp y).coeff r ∈ A ∧ (X.exp y).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω)) →
    ∃ x', GlobalTheory.Glue.Ev ψ (fun r : ℤ => j ((X.exp y).coeff ((r : ℚ) / (p : ℚ) ^ n))) (io y) x'
  gal : ∀ (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω), g (T.qq n) = T.qq n → (∀ x, g (j x) = j (s x)) →
    ∀ y y' : KT X (p ^ n), (y' : X.K) = X.gal s y → g (io y) = io y'

def IsNTr (ε : Ω →+* ℂ) (l n m : ℕ) [NeZero l] (F F' : Ω) : Prop :=
  1 ≤ m ∧ m ≤ n ∧ F ∈ IntermediateField.adjoin ℚ {zt ε l n} ∧ IsNT ε l n m F F'

theorem InZl.mem_adjoin {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨D, hD, hF⟩ := h
  have hD0 : (D : Ω) ≠ 0 := by
    rintro h0
    exact hD (by rw [Nat.cast_eq_zero.1 h0]; exact dvd_zero _)
  have h1 : (D : Ω) * F ∈ IntermediateField.adjoin ℚ {zt ε l n} :=
    (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l n}).toSubring)).2
      (IntermediateField.subset_adjoin ℚ _) hF
  have h2 := mul_mem (inv_mem (natCast_mem (IntermediateField.adjoin ℚ {zt ε l n}) D)) h1
  rwa [inv_mul_cancel_left₀ hD0] at h2

theorem IsNTr.apply_eq_of_mem_adjoin {z F : Ω} (hF : F ∈ IntermediateField.adjoin ℚ {z}) {s t : Ω ≃ₐ[ℚ] Ω} (h : s z = t z) :
    s F = t F := by
  induction hF using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx, h]
  | algebraMap r => rw [AlgEquiv.commutes, AlgEquiv.commutes]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

theorem IsNTr.add {l n m : ℕ} [NeZero l] {F F' G G' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m G G') :
    IsNTr ε l n m (F + G) (F' + G') := by
  obtain ⟨h1, h2, hF, τ, hτ, e⟩ := h
  obtain ⟨-, -, hG, τ', hτ', e'⟩ := h'
  refine ⟨h1, h2, add_mem hF hG, τ, hτ, ?_⟩
  rw [mul_add, e, e', ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by
    rw [map_add (f := _), IsNTr.apply_eq_of_mem_adjoin hG ((hτ a).trans (hτ' a).symm)]

theorem KT.mem_def (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := Iff.rfl

section

variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

end

end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ChiProj
section
noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def chiProj (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, χ (δ : ZMod N).val * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime]

def IsActC (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) : Prop :=
  (∀ (g : GQ l) (x : Om l), act g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)) ∧
    ∀ (g : GQ l) (y : PadicComplex l), ‖act g y‖ = ‖y‖

def IsCyc (χ : GQ l →* ℚ_[l]ˣ) : Prop :=
  ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a

def chiC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l) : PadicComplex l :=
  algebraMap ℚ_[l] (PadicComplex l) ((χ g ^ i : ℚ_[l]ˣ) : ℚ_[l])

def Kinf (K : FinExt l) : IntermediateField ℚ_[l] (Om l) :=
  K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x | ∃ j : ℕ, x ^ (l ^ j) = 1}

def Hinf (K : FinExt l) : Subgroup (GQ l) := (Kinf K).fixingSubgroup

def Gj (K : FinExt l) (j : ℕ) : Subgroup (GQ l) := (Ks K j).fixingSubgroup

def Lev (l j : ℕ) : Prop := 1 ≤ j ∧ (l = 2 → 2 ≤ j)

def IsGen (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (j : ℕ) (g : GQ l) : Prop :=
  g ∈ Gj K j ∧ ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ))

def inC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) :=
  (fun x : Om l => (x : PadicComplex l)) '' (F : Set (Om l))

def intC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) := {y | y ∈ inC F ∧ ‖y‖ ≤ 1}

def Ohat (K : FinExt l) : Set (PadicComplex l) := closure (intC (Kinf K))

def Xlev (K : FinExt l) (i : ℕ) : AddSubgroup (PadicComplex l) :=
  AddSubgroup.closure {z | ∃ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) ∧
    y ∈ intC (Ks K (i - 1)) ∧ z = ζ * y}

def Xj (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) :=
  (⨆ (i : ℕ) (_ : j < i), Xlev K i).topologicalClosure

def rho1 (l : ℕ) : ℝ := (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1))

def twAct (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (y : Fin r → PadicComplex l) :
    Fin r → PadicComplex l :=
  chiC χ i g • (U g).mulVec (fun a => act g (y a))

def CocOn {X : Type} [AddCommGroup X] [TopologicalSpace X] (G : Subgroup (GQ l)) (A : GQ l → X → X)
    (M : Set X) (c : GQ l → X) : Prop :=
  ContinuousOn c G ∧ (∀ g ∈ G, c g ∈ M) ∧ ∀ g ∈ G, ∀ h ∈ G, c (g * h) = c g + A g (c h)

def CobOn {X : Type} [AddCommGroup X] (G : Subgroup (GQ l)) (A : GQ l → X → X) (M : Set X)
    (c : GQ l → X) : Prop :=
  ∃ x ∈ M, ∀ g ∈ G, c g = A g x - x

def ball (l : ℕ) [Fact l.Prime] (r : ℕ) : Set (Fin r → PadicComplex l) := {y | ∀ a, ‖y a‖ ≤ 1}

def Frame (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m : ℕ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) : Prop :=
  IsGen χ K m g ∧ (∀ a b, ContinuousOn (fun σ => U σ a b) (Gj K m)) ∧
    (∀ σ ∈ Gj K m, ∀ a b, U σ a b ∈ intC (Ks K m)) ∧
    (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, U (σ * τ) = U σ * U τ) ∧ (∀ σ ∈ Hinf K, U σ = 1) ∧
    ∀ a b, ‖(U g - 1) a b‖ < rho1 l

def HTBasis (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (J : Set ℤ) : Prop :=
  ∃ (e : Fin r → Fin r → PadicComplex l) (u : Fin r → ℤ), LinearIndependent (PadicComplex l) e ∧
    (∀ k, u k ∈ J) ∧ ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def admissibleLettersSubalgebra (R : Type) [CommRing R] (N l : ℕ) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | admitted N l T})

def SSPotB (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ admissibleLettersSubalgebra ℂ N l, FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.SSBB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) :
    Prop :=
  ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

theorem iota_mem_admissibleSubalgebra (R : Type) [CommRing R] {N l : ℕ} {T : Letter} (hT : admitted N l T) :
    FreeAlgebra.ι R T ∈ admissibleLettersSubalgebra R N l :=
  Algebra.subset_adjoin ⟨T, hT, rfl⟩

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NormOneSevenOneTwo
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.Model

theorem mem_rayI_of_coprime {K : Type} [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)) (J : Ideal (𝓞 K)) :
    J ≠ 0 → J ⊔ 𝔮 = ⊤ → ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) → I ∈ rayI 𝔮 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ u hu =>
    intro _ _ I hI
    rw [Ideal.isUnit_iff] at hu
    subst hu
    have hI1 : I = 1 := Units.ext (by rw [hI, FractionalIdeal.coeIdeal_top, Units.val_one])
    rw [hI1]
    exact one_mem _
  | h₃ a P ha hP ih =>
    intro _ hcop I hI
    have hP0 : P ≠ 0 := hP.ne_zero
    have hPq : ¬ P ∣ 𝔮 := by
      intro hd
      apply hP.not_isUnit
      rw [Ideal.isUnit_iff, eq_top_iff, ← hcop]
      exact sup_le Ideal.mul_le_left (Ideal.le_of_dvd hd)
    have hacop : a ⊔ 𝔮 = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le_sup_right Ideal.mul_le_right _
    have hPf : (P : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hP0
    have haf : (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha
    have hI' : I = Units.mk0 _ hPf * Units.mk0 _ haf := Units.ext (by
      rw [hI, Units.val_mul, Units.val_mk0, Units.val_mk0, FractionalIdeal.coeIdeal_mul])
    have hu : Units.mk0 _ hPf ∈ rayI 𝔮 :=
      Subgroup.subset_closure ⟨⟨P, Ideal.isPrime_of_prime hP, hP0⟩, hPq, rfl⟩
    rw [hI']
    exact Subgroup.mul_mem _ hu (ih ha hacop _ rfl)

end GlobalTheory.Mem.An.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.CyclotomicQExpansion

open GlobalTheory.KZ GlobalTheory.Glue

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open scoped Classical in
open Classical in
def thN (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l) : HahnSeries ℚ Ω :=
  if h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ then
    h.choose else 0

theorem thN_spec (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n d : ℕ) (b : X.Fn l)
    (h : ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ ∧ IsLat 1 φ) :
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧ IsLat 1 (thN X A N l n d b) := by
  rw [thN, dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.CyclotomicQExpansion
end
end

