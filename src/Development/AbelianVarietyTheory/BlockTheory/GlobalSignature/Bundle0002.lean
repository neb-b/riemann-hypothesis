module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

abbrev Wsp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ

def sgn {P Q : ℕ} : Fin P ⊕ Fin Q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

def herm {P Q : ℕ} (x y : Wsp P Q) : ℂ := ∑ j, sgn j * x j * (starRingEnd ℂ) (y j)

def qf {P Q : ℕ} (x : Wsp P Q) : ℝ := (herm x x).re

def bil {P Q : ℕ} (x y : Wsp P Q) : ℝ := Algebra.trace ℝ ℂ (herm x y)

theorem herm_self {P Q : ℕ} (x : Wsp P Q) : herm x x = (qf x : ℂ) := by
  have term : ∀ j, sgn j * x j * (starRingEnd ℂ) (x j) =
      (((sgn j).re * Complex.normSq (x j) : ℝ) : ℂ) := by
    intro j
    rw [mul_assoc, Complex.mul_conj]
    rcases j with j | j <;> simp [sgn]
  unfold qf herm
  simp_rw [term]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

def fourierT {V : Type} [MeasurableSpace V] (e : ℝ) (β : V → V → ℝ) (μ : Measure V)
    (Φ : V → ℂ) (y : V) : ℂ :=
  ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((e * β x y : ℝ) : ℂ)) ∂μ

def IsSelfDualFor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (e : ℝ) (β : V → V → ℝ) (μ : Measure V) : Prop :=
  ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fourierT e β μ Φ) μ ∧
    ∀ x, fourierT e β μ (fourierT e β μ Φ) x = Φ (-x)

def dx (P Q : ℕ) : Measure (Wsp P Q) := (2 : ℝ≥0∞) ^ (P + Q) • volume

def cM (M : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ M / (Nat.factorial (M - 1) : ℝ))

def IsDxDq {P Q : ℕ} (β : ℝ) (fib : ℝ → Measure (Wsp P Q)) : Prop :=
  ∃ (U : Set (Wsp P Q)) (B : Set ℝ), {x | x ≠ 0} ⊆ U ∧ IsOpen B ∧ β ∈ B ∧
    IsFibreFamily (dx P Q) qf id U (volume : Measure ℝ) B fib

def act {P Q : ℕ} (g : UpqT P Q) (x : Wsp P Q) : Wsp P Q := (UpqT.mat g).mulVec x

def IsPerpFrame {P Q P' Q' : ℕ} (x₀ : Wsp P Q) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q)
    (ι : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ v w, herm (j v) (j w) = herm v w) ∧
  (∀ y, herm y x₀ = 0 ↔ ∃ v, j v = y) ∧
  (∀ g', act (ι g') x₀ = x₀ ∧ ∀ v, act (ι g') (j v) = j (act g' v))

def SelfDualMeasures : Prop :=
  ∀ e : ℝ, (e = 1 ∨ e = -1) →
    (∀ (P Q : ℕ) (μ : Measure (Wsp P Q)), μ.IsAddHaarMeasure →
      (IsSelfDualFor e bil μ ↔ μ = dx P Q)) ∧
    (∀ ν : Measure ℝ, ν.IsAddHaarMeasure →
      (IsSelfDualFor e (fun t s : ℝ => t * s) ν ↔ ν = volume))

def SphereVolume : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ fib : ℝ → Measure (Wsp M 0), IsDxDq 1 fib →
    fib 1 {x | qf x = 1} = cM M

def QuotientMeasure : Prop :=
  ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : Wsp P Q, qf x₀ = β →
    (∀ y : Wsp P Q, qf y = β → ∃ g : UpqT P Q, act g⁻¹ x₀ = y) ∧
    (∃ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      (β = 1 → P' + 1 = P ∧ Q' = Q) ∧ (β = -1 → P' = P ∧ Q' + 1 = Q) ∧ IsPerpFrame x₀ j ι) ∧
    ∀ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      IsPerpFrame x₀ j ι →
        Set.range ι = {g | act g x₀ = x₀} ∧
        ∀ (c : CDHaar) (fib : ℝ → Measure (Wsp P Q)), IsDxDq β fib →
          ∀ s : Wsp P Q → UpqT P Q, (∀ y, qf y = β → act (s y)⁻¹ x₀ = y) →
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (cM (P + Q))⁻¹ *
                  ∫⁻ y in {y | qf y = β}, (∫⁻ g', f (ι g' * s y) ∂(c.cd P' Q')) ∂(fib β)

def RealPlaceMeasures : Prop := SelfDualMeasures ∧ SphereVolume ∧ QuotientMeasure

end GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsUnimodularLC (G : Type) [Group G] [TopologicalSpace G] [MeasurableSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G ∧ SecondCountableTopology G ∧
    BorelSpace G ∧ (∃ μ : Measure G, μ.IsHaarMeasure) ∧
    ∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsDiscreteWithDomains {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  Countable Γ ∧ DiscreteTopology Γ ∧
    ∀ μ : Measure G, μ.IsHaarMeasure →
      ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ IsFundamentalDomain Γ 𝓕 μ

section Points

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratPts (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ J) := HFinIn R σ J

def UnimodularOver (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E)
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  IsUnimodularLC (HA R σ J) ∧
    ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsUnimodularLC (Hstab R σ J x)

end Points

def AdelicUnitaryHaar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (AF F) σ J ∧ UnimodularOver (Ainf F) σ J ∧ UnimodularOver (Af F) σ J ∧
      (∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J) ∧
      IsDiscreteWithDomains (ratPts (AF F) σ J) ∧
      ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 →
        IsDiscreteWithDomains (HstabFin (AF F) σ J x)

theorem isUnimodularLC_of_commGroup (G : Type) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] : IsUnimodularLC G :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun _ _ => inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Places

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsInertAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime

def IsSplitAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (v.asIdeal.primesOver (𝓞 E)).ncard = 2

def IsEtaAt (v : HeightOneSpectrum (𝓞 F)) (η : ℤ) : Prop :=
  (IsInertAt F E v ∧ η = -1) ∨ (IsSplitAt F E v ∧ η = 1)

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

abbrev maxOrder (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)

def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1

def IsDualExp (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (c : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp c

def dualIndex (v : HeightOneSpectrum (𝓞 F)) (c : ℤ) : ℝ := (resCard F v : ℝ) ^ c

end Places

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

def IsSelfDualLattice (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v

def latTup (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Fv F v ⊗[F] E) := {X | X 0 ∈ L}

def qTup (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : Fv F v := qR (Fv F v) σ J (X 0)

end Lattice

def densityValue (N : ℝ) (q : ℕ) (η : ℤ) (M : ℕ) : ℝ :=
  N ^ ((1 / 2 : ℝ) - M) * (1 - (η : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ)))

def SelfDualLatticeDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 1 ≤ M → IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (η : ℤ), IsEtaAt F E v η →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar F v ψ →
  AllSome (IsDualExp F v ψ) fun c =>
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ (latTup v L) = ENNReal.ofReal (dualIndex F v c ^ (-(M : ℤ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal (dualIndex F v c ^ (-(1 / 2 : ℝ))) ∧
    ∀ β : Fv F v, Valued.v β = 1 →
      (∀ (U : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (B : Set (Fv F v))
          (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
          {X | qTup σ J v X ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B →
          IsFibreFamily μ (qTup σ J v) id U ν B fib →
          fib β (latTup v L) =
            ENNReal.ofReal (densityValue (dualIndex F v c) (resCard F v) η M) ∧
          ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t (latTup v L) = fib β (latTup v L)) ∧
      (∀ g : Fv F v → ℂ,
          IsContDensityOn μ (qTup σ J v) id ν {t | t ≠ 0} ((latTup v L).indicator 1) g →
          ∀ t : Fv F v, Valued.v (t - β) < 1 →
            g t = (densityValue (dualIndex F v c) (resCard F v) η M : ℂ))

end GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

abbrev Sp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ

def herm {P Q : ℕ} (x y : Sp P Q) : ℂ :=
  ∑ i : Fin P, x (Sum.inl i) * star (y (Sum.inl i)) -
    ∑ j : Fin Q, x (Sum.inr j) * star (y (Sum.inr j))

def qf {P Q : ℕ} (x : Sp P Q) : ℝ :=
  ∑ i : Fin P, Complex.normSq (x (Sum.inl i)) - ∑ j : Fin Q, Complex.normSq (x (Sum.inr j))

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_self {P Q : ℕ} (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x x = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x : ℂ) := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf, Complex.star_def,
    Complex.mul_conj]

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform {P Q : ℕ} (x y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x y = _root_.Formalism.UG.hform (starRingEnd ℂ) (_root_.Formalism.UG.Jpq P Q) y x := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.Formalism.UG.hform, _root_.Formalism.UG.Jpq, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply, Complex.star_def]
  simp [mul_comm, sub_eq_add_neg, Finset.sum_neg_distrib]

def dx (P Q : ℕ) : Measure (Sp P Q) := ((2 : ℝ≥0∞) ^ (P + Q)) • (volume : Measure (Sp P Q))

def cM (M : ℕ) : ℝ := (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)

open MeasureTheory Matrix in
open scoped ENNReal in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM_pos (M : ℕ) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM M := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.cM
  positivity

def IsDxDq {P Q : ℕ} (fib : ℝ → Measure (Sp P Q)) : Prop :=
  IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {x | x ≠ 0} (volume : Measure ℝ) Set.univ fib

def act {P Q : ℕ} (g : UpqT P Q) (x : Sp P Q) : Sp P Q := UpqT.mat g *ᵥ x

def IsPerpEmb {P Q P' Q' : ℕ} (x₀ : Sp P Q)
    (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ) (j : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ u v : Sp P' Q', herm (A *ᵥ u) (A *ᵥ v) = herm u v) ∧
  (∀ y : Sp P Q, herm y x₀ = 0 ↔ ∃ u : Sp P' Q', A *ᵥ u = y) ∧
  (∀ g : UpqT P' Q', act (j g) x₀ = x₀ ∧ ∀ u : Sp P' Q', act (j g) (A *ᵥ u) = A *ᵥ act g u)

def IsSection {P Q : ℕ} (β : ℝ) (x₀ : Sp P Q) (s : Sp P Q → UpqT P Q) : Prop :=
  Measurable s ∧ ∀ y : Sp P Q, qf y = β → act (s y) x₀ = y

def QuotFormula (c : CDHaar) (P Q P' Q' : ℕ) (β : ℝ) : Prop :=
  ∀ x₀ : Sp P Q, qf x₀ = β →
    AllSome
      (fun Aj : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ × (UpqT P' Q' → UpqT P Q) =>
        IsPerpEmb x₀ Aj.1 Aj.2)
      (fun Aj =>
        Set.range Aj.2 = {g | act g x₀ = x₀} ∧
        AllSome (fun fib : ℝ → Measure (Sp P Q) => IsDxDq fib) (fun fib =>
          AllSome (fun s : Sp P Q → UpqT P Q => IsSection β x₀ s) (fun s =>
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (ENNReal.ofReal (cM (P + Q)))⁻¹ *
                  ∫⁻ y, (∫⁻ g', f (s y * Aj.2 g') ∂(c.cd P' Q')) ∂(fib β))))

def CompactDualQuotient : Prop :=
  ∀ (c : CDHaar) (P Q : ℕ),
    QuotFormula c (P + 1) Q P Q 1 ∧ QuotFormula c P (Q + 1) P Q (-1)

def SelfDualReal : Prop :=
  ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    (∀ P Q : ℕ, SelfDual (dx P Q) (fun x y : Sp P Q =>
      Complex.exp (2 * Real.pi * Complex.I * ((ε * (2 * (herm x y).re) : ℝ) : ℂ)))) ∧
    SelfDual (volume : Measure ℝ)
      (fun t s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (t * s) : ℝ) : ℂ)))

def SphereMass : Prop :=
  ∀ M : ℕ, 1 ≤ M → AllSome (fun fib : ℝ → Measure (Sp M 0) => IsDxDq fib)
    (fun fib => fib 1 Set.univ = ENNReal.ofReal (cM M))

end GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Defs

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UnramifiedPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal →
    Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal


open Classical in
def eta (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsField (Fv F v ⊗[F] E) then -1 else 1

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

def intToEv (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
  (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype

def maxOrder (v : HeightOneSpectrum (𝓞 F)) : Subring (Fv F v ⊗[F] E) :=
  letI := (intToEv F E v).toAlgebra
  (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.mem_maxOrder (v : HeightOneSpectrum (𝓞 F))
    (z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v ↔
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.intToEv F E v).IsIntegralElem z :=
  Iff.rfl

variable {F E}

def IsSelfDualLattice (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F))
    (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (Fv F v ⊗[F] E) (L : Set (Fin M → Fv F v ⊗[F] E)) = ⊤ ∧
    ∀ y : Fin M → Fv F v ⊗[F] E, y ∈ L ↔ ∀ x ∈ L, hR (Fv F v) σ J x y ∈ maxOrder F E v

def IsLocalChar (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) : Prop :=
  Continuous ψ ∧ (∀ t, ‖ψ t‖ = 1) ∧ ∃ t, ψ t ≠ 1

def DualExponent (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (Fv F v) ℂ) (n : ℤ) : Prop :=
  ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔
    Valued.v t ≤ WithZero.exp n

end Defs

def LocalDensity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ (v : HeightOneSpectrum (𝓞 F)), UnramifiedPlace F E v →
  ∀ (ψ : AddChar (Fv F v) ℂ), IsLocalChar v ψ → ∀ n : ℤ, DualExponent v ψ n →
  ∀ (L : Submodule (maxOrder F E v) (Fin M → Fv F v ⊗[F] E)), IsSelfDualLattice σ J v L →
  ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), SdW F E σ M J (Fv F v) ψ 1 μ →
  ∀ (ν : Measure (Fv F v)), SdR (Fv F v) ψ ν →
    μ {X | X 0 ∈ L} = ENNReal.ofReal ((resCard F v ^ n) ^ (-(M : ℝ))) ∧
    ν (v.adicCompletionIntegers F : Set (Fv F v)) =
      ENNReal.ofReal ((resCard F v ^ n) ^ (-(1 / 2 : ℝ))) ∧
    ∀ (fib : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id Set.univ ν {c | c ≠ 0} fib →
    ∀ β : Fv F v, Valued.v β = 1 →
      fib β {X | qR (Fv F v) σ J (X 0) = β ∧ X 0 ∈ L} =
        ENNReal.ofReal ((resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) *
          (1 - eta F E v ^ M * (resCard F v ^ M)⁻¹)) ∧
      ∀ t : Fv F v, Valued.v (t - β) < 1 → fib t {X | X 0 ∈ L} = fib β {X | X 0 ∈ L}


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    1 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)


open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.density_factor_pos (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (M : ℕ) (hM : 1 ≤ M) :
    0 < 1 - _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ := by
  have hq := _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard F v
  have hqM : 1 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := one_lt_pow₀ hq (by omega)
  have hpos : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M := by linarith
  have hsign : |_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v| = 1 := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta
    split_ifs <;> norm_num
  have hle := le_abs_self (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M *
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹)
  rw [abs_mul, abs_pow, hsign, one_pow, one_mul, abs_inv, abs_of_pos hpos] at hle
  have hinv : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqM
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces
end
end

