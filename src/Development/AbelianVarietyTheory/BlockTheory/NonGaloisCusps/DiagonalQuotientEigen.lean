module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct

def cc (l : ℕ) (a : ℤ) : ℚ := ((1 + (l : ℚ)) ^ a - 1) / (-(l : ℚ))

def eigMs (LL : Type) [Field LL] (l : ℕ) (U : Multiset ℤ) (w j j' : ℤ) : Multiset LL :=
  U.bind fun u => (Finset.Ico j j').val.map fun j'' => ((cc l (j'' - (u - w)) : ℚ) : LL)

def DiagWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) F M) (e : Fin m → F),
    (∀ s, f (b s) = e s • b s) ∧ Finset.univ.val.map e = S

def EigWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] (f : M →ₗ[F] M) (S : Multiset F) : Prop :=
  ∃ _ : Module.Finite F M, f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def qΔ : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def mulD (a : LetA O n) : W.DD T →ₗ[O] W.DD T := Algebra.lsmul O O (W.DD T) a

def NΔl (i : ZMod n) : Submodule O (W.DD T) := W.NΔ T ⊓ (W.Nl T i).restrictScalars O

def qN (i : ZMod n) (j : ℤ) : Submodule O (W.DD T) :=
  ((NΔl W T i).map (mulD W T (qΔ W ^ j.toNat))).comap (mulD W T (qΔ W ^ (-j).toNat))

abbrev qQuot (i : ZMod n) (j j' : ℤ) : Type :=
  ↥(qN W T i j) ⧸ (qN W T i j').submoduleOf (qN W T i j)

def IsNab (g : W.Gam) (a : LetA O n) (i : ZMod n) (j : ℤ) (nb : ↥(qN W T i j) →ₗ[O] ↥(qN W T i j)) : Prop :=
  ∀ x : ↥(qN W T i j),
    (a * W.π₀) • ((nb x : ↥(qN W T i j)) : W.DD T) = W.γD T g (x : W.DD T) - a • (x : W.DD T)

def DiagQuot (g : W.Gam) (a : LetA O n) (i : ZMod n) (j j' : ℤ) (S : Multiset LL) : Prop :=
  qN W T i j' ≤ qN W T i j ∧
    Module.Free O (qQuot W T i j j') ∧ Module.Finite O (qQuot W T i j j') ∧
    Module.finrank O (qQuot W T i j j') = (j' - j).toNat * Module.finrank LL T.V ∧
    (∃ nb, IsNab W T g a i j nb) ∧
    ∀ nb, IsNab W T g a i j nb →
      ∃ hs : (qN W T i j').submoduleOf (qN W T i j) ≤ ((qN W T i j').submoduleOf (qN W T i j)).comap nb,
        DiagWith ((Submodule.mapQ _ _ nb hs).baseChange LL) S

def SenIs (k : Type) [Field k] [Algebra O k] (g : W.Gam) (a : LetA O n) (i : ZMod n) (S : Multiset k) :
    Prop :=
  (∃ nb, IsNab W T g a i 0 nb) ∧
    ∀ nb, IsNab W T g a i 0 nb →
      ∃ hs : (qN W T i 1).submoduleOf (qN W T i 0) ≤ ((qN W T i 1).submoduleOf (qN W T i 0)).comap nb,
        EigWith ((Submodule.mapQ _ _ nb hs).baseChange k) S

def SenPair (g : W.Gam) (a : LetA O n) (i : ZMod n) (U : Multiset ℤ) (w : ℤ) : Prop :=
  (∀ j j' : ℤ, j < j' → DiagQuot W T g a i j j' (eigMs LL PD.p U w j j')) ∧
    ∀ (k : Type) [Field k] [Algebra O k], Function.Surjective (algebraMap O k) →
      SenIs W T k g a i (U.map fun u => ((u - w : ℤ) : k))


open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN_zero (i : ZMod n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN W T i 0 = _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.NΔl W T i := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.qN, _root_.GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen.mulD, Module.End.one_eq_id, Submodule.map_id,
    Submodule.comap_id]

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen
