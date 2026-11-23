module

public import Mathlib
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

@[expose] public section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Loc GroundTheory.Automorphic Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

def Uni {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  μ.IsHaarMeasure ∧ μ.IsInvInvariant

section

variable {G T : Type} [Group G] [MeasurableSpace G] [Group T] [MeasurableSpace T]

def Pair [TopologicalSpace G] [TopologicalSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T) : Prop :=
  Uni μ ∧ IsClosedEmbedding j ∧ Uni ν

def IsNrm (j : T →* G) (ν : Measure T) (ρ : G → ℝ≥0∞) : Prop := Measurable ρ ∧ ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1


open scoped Classical in
open Classical in
def qI (μ : Measure G) (j : T →* G) (ν : Measure T) (F : G → ℂ) : ℂ :=
  if h : ∃ ρ, IsNrm j ν ρ then ∫ x, F x * ((h.choose x).toReal : ℂ) ∂μ else 0

def QInt (μ : Measure G) (j : T →* G) (ν : Measure T) (F : G → ℂ) : Prop :=
  Measurable F ∧ (∀ t g, F (j t * g) = F g) ∧ ∀ ρ, IsNrm j ν ρ → Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ

end

def NormEx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∃ ρ : G → NNReal, Continuous ρ ∧ IsNrm j ν (fun g => ρ g) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ g ∈ Set.range j * C, ρ g ≠ 0 → g ∈ D

def QuotEq : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) → ∀ ρ, IsNrm j ν ρ →
      (QInt μ j ν F ↔ Integrable (fun x => F x * ((ρ x).toReal : ℂ)) μ) ∧ (QInt μ j ν F ↔ ∫⁻ x, ‖F x‖ₑ * ρ x ∂μ ≠ ⊤) ∧
      qI μ j ν F = ∫ x, F x * ((ρ x).toReal : ℂ) ∂μ

def QuotLin : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    (∀ (ι : Type) (s : Finset ι) (c : ι → ℂ) (F : ι → G → ℂ), (∀ i ∈ s, QInt μ j ν (F i)) →
      QInt μ j ν (fun g => ∑ i ∈ s, c i * F i g) ∧ qI μ j ν (fun g => ∑ i ∈ s, c i * F i g) = ∑ i ∈ s, c i * qI μ j ν (F i)) ∧
    ∀ (a b : NNReal), a ≠ 0 → b ≠ 0 → Pair (a • μ) j (b • ν) ∧ ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) →
      (QInt (a • μ) j (b • ν) F ↔ QInt μ j ν F) ∧ qI (a • μ) j (b • ν) F = ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * qI μ j ν F

def QuotMap : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
    [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T'] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (μ' : Measure G') (j' : T' →* G') (ν' : Measure T'), Pair μ' j' ν' → ∀ (e : G ≃ₜ* G') (y : G'), μ.map e = μ' → ν.map (fun t => e (j t)) = ν'.map j' →
      ∀ F : G' → ℂ, Measurable F → (∀ t g, F (j' t * g) = F g) →
        (QInt μ j ν (fun g => F (e g * y)) ↔ QInt μ' j' ν' F) ∧ qI μ j ν (fun g => F (e g * y)) = qI μ' j' ν' F

def QuotProd : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (G' : Type) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G'] [T2Space G']
    [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (T' : Type) [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [LocallyCompactSpace T'] [T2Space T']
    [SecondCountableTopology T'] [MeasurableSpace T'] [BorelSpace T'] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (μ' : Measure G') (j' : T' →* G') (ν' : Measure T'), Pair μ' j' ν' → Pair (μ.prod μ') (j.prodMap j') (ν.prod ν') ∧
      ∀ (F : G → ℂ) (F' : G' → ℂ), Measurable F → (∀ t g, F (j t * g) = F g) → Measurable F' → (∀ t g, F' (j' t * g) = F' g) →
        (QInt μ j ν F → QInt μ' j' ν' F' → QInt (μ.prod μ') (j.prodMap j') (ν.prod ν') (fun g => F g.1 * F' g.2)) ∧
        qI (μ.prod μ') (j.prodMap j') (ν.prod ν') (fun g => F g.1 * F' g.2) = qI μ j ν F * qI μ' j' ν' F'

def QuotPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)]
    [∀ i, BorelSpace (G i)] (T : ι → Type) [∀ i, Group (T i)] [∀ i, TopologicalSpace (T i)] [∀ i, IsTopologicalGroup (T i)]
    [∀ i, LocallyCompactSpace (T i)] [∀ i, T2Space (T i)] [∀ i, SecondCountableTopology (T i)] [∀ i, MeasurableSpace (T i)]
    [∀ i, BorelSpace (T i)]
    (μ : ∀ i, Measure (G i)) (j : ∀ i, T i →* G i) (ν : ∀ i, Measure (T i)), (∀ i, Pair (μ i) (j i) (ν i)) →
    ∀ J : (∀ i, T i) →* ∀ i, G i, (∀ t i, J t i = j i (t i)) → Pair (Measure.pi μ) J (Measure.pi ν) ∧
      ∀ F : ∀ i, G i → ℂ, (∀ i, Measurable (F i) ∧ ∀ t g, F i (j i t * g) = F i g) →
        ((∀ i, QInt (μ i) (j i) (ν i) (F i)) → QInt (Measure.pi μ) J (Measure.pi ν) (fun g => ∏ i, F i (g i))) ∧
        qI (Measure.pi μ) J (Measure.pi ν) (fun g => ∏ i, F i (g i)) = ∏ i, qI (μ i) (j i) (ν i) (F i)

def QuotOpen : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ U : Subgroup G, IsOpen (U : Set G) → ∀ i : U.comap j →* U, (∀ t, (i t : G) = j t) →
      Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) ∧
      ∀ F : G → ℂ, Measurable F → (∀ t g, F (j t * g) = F g) → (∀ g, F g ≠ 0 → g ∈ Set.range j * (U : Set G)) →
        (QInt μ j ν F ↔ QInt (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) fun u => F u) ∧
        qI μ j ν F = qI (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) fun u => F u

def QuotFub : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [T2Space T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (μ : Measure G) (j : T →* G) (ν : Measure T), Pair μ j ν →
    ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [SFinite m] (F : X → G → ℂ), Measurable (Function.uncurry F) →
      (∀ a t g, F a (j t * g) = F a g) → ∀ ρ, IsNrm j ν ρ → ∫⁻ a, ∫⁻ x, ‖F a x‖ₑ * ρ x ∂μ ∂m ≠ ⊤ →
      QInt μ j ν (fun g => ∫ a, F a g ∂m) ∧ qI μ j ν (fun g => ∫ a, F a g ∂m) = ∫ a, qI μ j ν (F a) ∂m

end UpperTheory.ConvolutionTheory.G
