module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

open Formalism.BasicNotions.TH

def lowerOp {p q : ℕ} (n : ℕ) (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) : Pol p q n 0 :=
  ∑ c : Fin n, MvPolynomial.pderiv ((Sum.inl a, Sum.inl c) : Ln p q n 0)
    (MvPolynomial.pderiv ((Sum.inr b, Sum.inl c) : Ln p q n 0) Φ)

def KilledByPMinus {p q n : ℕ} (Φ : Pol p q n 0) : Prop :=
  ∀ (a : Fin p) (b : Fin q), lowerOp n a b Φ = 0

def singVal {p q : ℕ} (X : Mat p q) (i : Fin (min p q)) : ℝ :=
  (Matrix.toEuclideanLin X.toBlocks₁₂ :
    EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues i.val

def coef {p q n : ℕ} {T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)} {T₁ : GrpData p q}
    {T₂ : GrpData n 0} (F : FockData T₀ T₁ T₂) (X : Mat p q) (Φ₁ Φ₂ : Pol p q n 0) : ℂ :=
  inner ℂ (F.ι Φ₂) (F.π (T₁.expt X, 1) (F.ι Φ₁))

def HarmonicDecay : Prop :=
  ∀ (p q n : ℕ) (T₀ : GrpData (p * n + q * 0) (p * 0 + q * n)) (T₁ : GrpData p q) (T₂ : GrpData n 0)
    (F : FockData T₀ T₁ T₂) (X : Mat p q), X ∈ pR p q →
    ∀ Φ₁ Φ₂ : Pol p q n 0, KilledByPMinus Φ₁ → KilledByPMinus Φ₂ →
      ‖coef F X Φ₁ Φ₂‖ ≤
        (∏ i : Fin (min p q), Real.cosh (singVal X i) ^ (-(n : ℤ))) * ‖F.ι Φ₁‖ * ‖F.ι Φ₂‖

theorem fockAct1_lower {p q n : ℕ} (a : Fin p) (b : Fin q) (Φ : Pol p q n 0) :
    fockAct1 p q n 0 (Eab (Sum.inr b) (Sum.inl a)) Φ = -lowerOp n a b Φ := by
  rw [fockAct1_Eab, lowerOp, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_neg_distrib]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : ((Sum.inr b, Sum.inl c) : Ln p q n 0) ≠ (Sum.inl a, Sum.inl c) := by simp
  have hc : ∀ (i j : Ln p q n 0) (P : Pol p q n 0),
      MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
    intro i j P
    classical
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P k hP =>
      simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hP, MvPolynomial.pderiv_X]
      by_cases h1 : k = i <;> by_cases h2 : k = j <;> simp [Pi.single_apply, h1, h2] <;>
        (try split_ifs) <;> (try simp) <;> (try ring)
  simp [omE, raiB, lowB, linePos, hne, hc (Sum.inr b, Sum.inl c) (Sum.inl a, Sum.inl c)]

end GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

def len_vp (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℝ≥0∞ :=
  (Module.length O M : ℝ≥0∞) / (Module.length O (O ⧸ Ideal.span {(l : O)}) : ℝ≥0∞)

def val_vp {O : Type} [CommRing O] (l : ℕ) (x : O) : ℝ≥0∞ :=
  len_vp O l (O ⧸ Ideal.span {x})

section Rep

variable {Γ A : Type} [Group Γ] [CommRing A] {m : ℕ}

end Rep

section Div

variable {Γ O' : Type} [Group Γ] [CommRing O'] [IsDomain O'] {m : ℕ}

end Div

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

abbrev ineAt (v : PlE D.host) : Subgroup (GE D) := Ine (F := D.host.E) (D.nd.plOm.1 v)

def InertiaBound (ε' : ℝ) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : GE D →* (D.ntw.Ok i k)ˣ) : Prop :=
  ∀ γ : PlE D.host → GE D, (∀ P ∈ Q, TameGenAt (D.nd.plOm.1 P) (γ P)) →
    (D.R.t : ℝ≥0∞) * ∑ P ∈ Q, val_vp (D.ntw.l i) (((ψ (γ P) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) - 1) ≤
      ENNReal.ofReal ε'

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SplitColumnClasses
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  p.Prime ∧ (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E

theorem splitsCompletely_g (D : D7) (i : Fin 2) : SplitsCompletely D.host.E (D.host.g i) :=
  ⟨D.host.g_prime i, D.nd.g_split i⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

end
end

