module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem GraphClosed.full : GraphClosed.Statement.{u, w} := GraphClosed.proof
theorem VeryAmplePow.full : VeryAmplePow.Statement.{u, w} := VeryAmplePow.proof

theorem SectionExists.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : SectionExists.Statement.{u, w} :=
  SectionExists.proof (SectionCount.assembled hTop hF hT hH hR) VeryAmplePow.full
    (LeadingCoeffPos.proof_of_cut hR hPos)

theorem VeryAmpleNefPlusAmple.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} :=
  VeryAmpleNefPlusAmple.proof Generated.full (SectionExists.assembled hTop hF hT hH hR hPos)
    (StepThree.assembled hL hG) GraphClosed.full hPt

theorem NefProductNonneg.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    NefProductNonneg.Statement.{u, w} :=
  NefProductNonneg.proof (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) hR

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

def omegaRes (x : Fin (N + 1) → Ω) :
    ∀ I J : Kleiman.Chart x, I.1 ⊆ J.1 → (Ω →ₗ[S] Ω) :=
  fun _ _ _ => LinearMap.id

def CechAugExact {x : Fin (N + 1) → Ω} (G : Kleiman.Chart x → Submodule S Ω) (B : Submodule S Ω) : Prop :=
  (∀ J, B ≤ G J) ∧
  (∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G 0,
      Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) 0 s = 0 → ∃ b ∈ B, ∀ J, s J = b) ∧
  ∀ p : ℕ, ∀ s ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G (p + 1),
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) (p + 1) s = 0 →
      ∃ t ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) G p,
        Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t = s

end CechSide

section CellSide

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def cellCOf (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => G I.1

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

def cellZOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellCOf S G n ⊓ LinearMap.ker (cellD S y n)

def cellBOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellCOf S G n).map (cellD S y n)

abbrev cellHOf (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) : Type :=
  ↥(cellZOf S y G n) ⧸ (cellBOf S y G n).comap (cellZOf S y G n).subtype

def CellAugExact (y : (Σ k, ι k) → Ω) (G : (∀ k, Finset (ι k)) → Submodule S Ω) (A : Submodule S Ω) : Prop :=
  (∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → A ≤ G I) ∧
  (∀ s ∈ cellCOf S G 0, cellD S y 0 s = 0 →
    ∃ a ∈ A, ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → s c = a) ∧
  ∀ q : ℕ, ∀ s ∈ cellCOf S G (q + 1), cellD S y (q + 1) s = 0 →
    ∃ t ∈ cellCOf S G q, cellD S y q t = s

variable [DecidableEq K]

def baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1))) (I : ∀ k, Finset (ι k)) :
    ∀ k, Finset (ι k) :=
  Function.update I k₀ (I k₀ ∪ J.map e.symm.toEmbedding)

end CellSide

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def BaseRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ b : ℤ, BundleRealises y k₀ (Kleiman.twistBundle F x b) (b • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def NumModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n →
          Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun i => (L i).toSubSystem) =
            NumbersDVR.intNum F (mIdealOver F y) δ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def MultiSerre.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∀ᶠ m : K → ℤ in Filter.atTop,
        (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        (Module.finrank F (cechHc ι (quotPart F V) m 0) : ℤ) = NumbersDVR.hilbFn V m

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def VeryAmpleModel.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
        (Kleiman.IsVeryAmple Q.toSubSystem ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def TensorRealise.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (n : ℕ) (L : Fin n → Kleiman.LineBundle F x) (δ : Fin n → K → ℤ),
        (∀ i, BundleRealises y k₀ (L i) (δ i)) → ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in Filter.atTop,
          ((Kleiman.tensorSub (fun i => (L i).toSubSystem) T).twist (Kleiman.twistSys F x (c : ℤ))).secs =
            secOver F y (∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def ModelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ n : ℕ, (Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) n ↔
        relDim (mIdealOver F y) = ((n : ℕ) : WithBot (WithTop ℤ)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def EulerPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∃ (B : ℕ) (χ : MvPolynomial K ℚ),
        (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) ∧
        (∀ (m : K → ℤ) (i : ℕ), B < i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        ∀ m : K → ℤ, ∑ i ∈ Finset.range (B + 1),
          (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ) =
            eval (fun k => (m k : ℚ)) χ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver)

def ModelCechRefine.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ)
    (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ (γ : K → ℤ)
      (T : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω),
      (∀ J, (T.sub J : Set Ω) = chartSecOver F y k₀ e γ J) →
      ∀ n : ℕ, Nonempty (T.H n ≃ₗ[F] cellH F y γ n)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GraphRestrict.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω)
    (K' : Type) [Field K'] [Algebra k K'] (x' : Fin (N + 1) → K') (s' : Fin m → K')
    (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0),
    IsGraphGen Q n s → mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') →
    (∃ i, x' i ≠ 0) → (∃ j, s' j ≠ 0) →
    ∃ (Q' : Kleiman.LineBundle k x') (r : Ω → K'),
      Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ IsGraphGen Q' n s'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def RayVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop, ∀ i : ℕ, 1 ≤ i →
      Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

