module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

end GlobalTheory.AdeleEv

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.AbCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) [IsAffineHom φ]

def preU (U : X.affineOpens) : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, U.2.preimage φ⟩

theorem preU_mono : Monotone (preU φ) := fun _ _ h _ hx ↦ h hx

def prePair (U : X.affineOpens) : Pair φ := ⟨(preU φ U, U), le_rfl⟩

def preAff : AffOp X ⥤ AffOp X' := (preU_mono φ).functor.op

abbrev OPre (s' : X' ⟶ Sp R') : AffOp X ⥤ CommAlgCat.{0} R' := preAff φ ⋙ OAff s'

def preRes (s' : X' ⟶ Sp R') : CoefMap (RingHom.id R') (OAff s') (OPre φ s') := CoefMap.restrict _ _

def preα (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (U : AffOp X) : (OAff s).obj U →+* (OPre φ s').obj U :=
  secPull s s' (prePair φ U.unop)

variable {φ} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'}

def preCoef (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (OAff s) (OPre φ s') where
  G := 𝟭 _
  α U := preα φ s s' U
  naturality {p q} a b := (pairPull h).naturality
    (homOfLE (show prePair φ q.unop ≤ prePair φ p.unop from
      ⟨preU_mono φ (leOfHom a.unop), leOfHom a.unop⟩)).op b
  smul U := semiHom_secPull h (prePair φ U.unop)

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp IsFieldData IsIntLattice IsClassZetaVals betaBound_vp c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal

def Sz (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (r : ℝ) (x : ℂ) : Prop :=
  ∃ h : x ∈ algebraicClosure ℚ ℂ, ‖lam ⟨x, h⟩‖ ≤ (l : ℝ) ^ r

def OneOver {E : Type} [Field E] [NumberField E] (l : ℕ) (y : (Af E)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1

abbrev LP := ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (_ : ℕ) (_ : I → E →+* ℂ) (_ : ℕ)
  (_ : ClassGroup (OF E) → ℚ) (_ : Ideal (OF E)) (_ : PeriodPair) (_ : ℕ) (_ : Set E), Prop

def AllLat (P : LP) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s → ∀ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z →
    ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → IsIntLattice d Λ → ∀ l : ℕ, l.Prime →
    ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → P E I d φ s z 𝔣 Λ l (lattice (condQ 𝔣 Q) y)

def LatIntRam : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))

def LatIntUnr : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l = 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))


open Classical in
def Expansion : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 →
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l +
          ((∑ i, κ i : ℕ) : ℝ) * (c_vp 𝔣 l + 1 + if l = 2 then 1 else 0))
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))

section Transport

variable {K : Type} [Field K] [NumberField K]

def TorsTransport (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) : Prop :=
  Ω₀ ≠ 0 ∧ Ω₁ ≠ 0 ∧ (∀ x, g (ι x) = ι x) ∧ IsLatOf ι 1 Λ₀ ∧ (∃ 𝔞, IsInvIdealOf t 𝔞 ∧ IsLatOf ι 𝔞 Λ₁) ∧
    g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 ∧ g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 ∧
    ∀ x x' : K, ι x ∉ Λ₀.lattice →
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) →
      g (Λ₀.weierstrassP (ι x) / Ω₀ ^ 2) = Λ₁.weierstrassP (ι x') / Ω₁ ^ 2 ∧
        g (Λ₀.derivWeierstrassP (ι x) / Ω₀ ^ 3) = Λ₁.derivWeierstrassP (ι x') / Ω₁ ^ 3

def IsLatDatum {E : Type} [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q

end Transport

def PeriodEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ)
      (art : Ideles K →* Gab K Ω), j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
      ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ →
      ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁

def LatAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ : I → ℕ) (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsAlgebraic ℚ (coordIn E d s κ Ω₀ (S 0))

def LatConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ κ' : I → ℕ), IsConjWt φ g κ κ' → ∀ (y : (Af E)ˣ) (S S' : ℂ → ℂ),
        IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹)) S' →
        g (coordIn E d s κ Ω₀ (S 0)) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' 0)

end GlobalTheory.LatVal
end
end

