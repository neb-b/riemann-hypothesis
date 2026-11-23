module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec

@[expose] public section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} (R : Fr l O)

def diag (n : ℕ) (a : O⟦X⟧) : LetA O n := fun _ => a

def KillsN {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (i : ZMod n) (a : O⟦X⟧) : Prop :=
  ∀ y ∈ W.Nl T' i, ∃ x ∈ W.Nl T i, W.map f x = diag n a • y

variable [NeZero n] {R} (jE : R.EE →ₐ[O] W.EE)

def vec {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) (x : DD R n r) : W.DD T :=
  ∑ i, ∑ k, jE (x i k) • b i k



end Generic

variable {l : ℕ} [Fact l.Prime]

instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
