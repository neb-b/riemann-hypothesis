module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.EigProjRegNeZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Norms

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp

end Eigen

section Further

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Further

section FurtherEigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]


end FurtherEigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

def NormalCharts (x : (Σ k, ι k) → Ω) : Prop :=
  ∀ c, mseg x c ≠ 0 → IsIntegrallyClosedIn (chartRing O (mseg x) c) Ω

structure IsLatticeFamily (x : (Σ k, ι k) → Ω) (p : ℕ) (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg)
    (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
    ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → (D c).TestFacts (chartRing O (mseg x) c) p (algebraMap O Ω w)
    (fun τ a => algebraMap O Ω (χ τ a)) φ

def pullFamily {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s) :
    (∀ k : K ⊕ K', Sum.elim ι ι' k) → LieLatticeData Ω F n Sg r s :=
  fun c => (D (restrictChart c)).bc (chartRing O (mseg (joinCoord x z)) c)

def HasBundles (x : (Σ k, ι k) → Ω) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s)
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)) : Prop :=
  ∀ τ c, mseg x c ≠ 0 → (Lie τ).lat c = (D c).lie τ ∧ (W τ).lat c = (D c).W τ ∧
    (Om τ).lat c = (D c).om τ ∧ (OmHT τ).lat c = (D c).omHT τ

def CkRelations (x : (Σ k, ι k) → Ω) (d p : ℕ) (φ : Equiv.Perm Sg) {VL VO : Sg → Type}
    [∀ τ, AddCommGroup (VL τ)] [∀ τ, Module Ω (VL τ)] [∀ τ, AddCommGroup (VO τ)] [∀ τ, Module Ω (VO τ)]
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (VL τ))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (VO τ)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
    Q.IsHomogeneous (d + 1 - k) → ∃ h : Sg → ℝ,
      (∀ τ, ((ck O x d (r τ) (Lie τ) (W τ) k L Q : ℤ) : ℝ) + ((ck O x d (s τ) (Om τ) (OmHT τ) k L Q : ℤ) : ℝ) =
        h τ - (k : ℝ) * ((rootNum O x d (r τ) (Lie τ) (psum (Fin (r τ)) ℤ (k - 1)) L Q (p : O) : ℤ) : ℝ) /
          ((p : ℝ) - 1)) ∧
      ∀ τ, (p : ℝ) ^ k * h τ = h (φ τ) +
        (k : ℝ) * ((rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O) : ℤ) : ℝ)

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace HTChart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

def IsFrame (σ : E →+* K) (m : ℕ)
    (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) {j k : ℕ}
    (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom))))
    (bM : Basis (Fin k) A (D.omHT σ)) (g : Matrix (Fin N) (Fin j ⊕ Fin k) A) : Prop :=
  (∀ a, ∃ x' : Fin N → A, (fun l => g l (Sum.inl a)) = i (bW a) + ((p : A) ^ m) • x') ∧
  ∀ a, ∃ y ∈ D.omHT σ, D.q σ (fun l => g l (Sum.inr a)) = (bM a : Ω) + ((p : A) ^ m) • y

end HTChart

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module GlobalTheory.CompanionTheory.Ar.BT

abbrev LevGrp (La : Type) [AddCommGroup La] (p n : ℕ) : Type :=
  Multiplicative (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La)))

def lev {La : Type} [AddCommGroup La] (p n : ℕ) (a : La) : LevGrp La p n :=
  Multiplicative.ofAdd (Submodule.Quotient.mk a)

structure OrdTower (p : ℕ) (O : Type) [CommRing O] (La : Type) [AddCommGroup La]
    (L : Type) [AddCommGroup L] [Module O L] where

  A : ∀ n, Subalgebra O (LevGrp La p n → O)
  hopf : ∀ n, IsHopfOrder (A n)
  res_iff : ∀ n (g : LevGrp La p n → O),
    g ∈ A n ↔ ∃ f ∈ A (n + 1), ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))
  ker_res : ∀ n (f : A (n + 1)), (∀ a : La, f.1 (lev p (n + 1) (p • a)) = 0) →
    f ∈ Ideal.span {g : A (n + 1) | ∃ h ∈ A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1}

  der : ∀ n, (LevGrp La p n → O) → Module.Dual O L → Prop
  der_ex : ∀ n, ∀ f ∈ A n, ∃ w, der n f w
  der_unique : ∀ n f w w', der n f w → (der n f w' ↔ ∃ u : Module.Dual O L, w' = w + (p ^ n) • u)
  der_onto : ∀ n w, ∃ f ∈ A n, der n f w
  der_add : ∀ n f g w w', der n f w → der n g w' → der n (f + g) (w + w')
  der_mul : ∀ n f g w w', der n f w → der n g w' → der n (f * g) (f 1 • w' + g 1 • w)
  der_const : ∀ n (r : O), der n (fun _ => r) 0
  der_zero : ∀ n (f : augIdeal (A n)), der n f.1.1 0 → (f : A n) ∈ augIdeal (A n) ^ 2
  der_res : ∀ n f g w, der (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → der n g w

namespace OrdTower

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def Acts (φ : La →+ La) (dφ : L →ₗ[O] L) : Prop :=
  ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) →
    (f ∈ X.A n → g ∈ X.A n) ∧ ∀ w, X.der n f w → X.der n g (w ∘ₗ dφ)

def PairingExtends (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ) : Prop :=
  ∀ n, ∃ s ∈ prodSpan (X.A n), ∀ a b, s (lev p n a, lev p n b) = ((ζ n ^ B a b : Oˣ) : O)

structure Realises [Fact p.Prime] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) : Prop where
  res : ∀ n (f : G.A (n + 1)) (a : La), (e n (G.res n f)).1 (lev p n a) = (e (n + 1) f).1 (lev p (n + 1) (p • a))
  pt : ∀ (a : La) n (f : G.A n), (τ a).pt n f = (e n f).1 (lev p n a)

end OrdTower

end GlobalTheory.CompanionTheory.Ar.HT
end
end

