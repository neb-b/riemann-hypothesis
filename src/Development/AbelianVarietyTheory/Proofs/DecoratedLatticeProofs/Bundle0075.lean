module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.CollCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Core.Deg

theorem splits_level (D : D7) (w : D.what₂.Word) : SplitsE D (D.mem w).A.T :=
  S.splitsCompl_of_ncard _ _ (D.mem w).A.T_prime
    (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem w).A.T_prime (S.level_norm_one_mod_conductor _ w)).2

end GlobalTheory.CollCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCoordinatesHomeomorph
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC GlobalTheory.HermSD

noncomputable section

namespace GlobalTheory.HermCoordEquiv

open GlobalTheory.GaussMean.OneVec

theorem sum_sum_split {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin n → Fin n → M) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (f p.1.1 p.1.2 + f p.1.2 p.1.1) := by
  classical
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0) +
      (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  have hsub : ∀ g : Fin n → Fin n → M, ∑ p : {p : Fin n × Fin n // p.1 < p.2}, g p.1.1 p.1.2 =
      ∑ a, ∑ b, if a < b then g a b else 0 := by
    intro g
    rw [← Fintype.sum_prod_type' (f := fun a b => if a < b then g a b else 0), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) (fun a : Fin n × Fin n => g a.1 a.2)).symm
  rw [Finset.sum_add_distrib, hsub (fun a b => f a b), hsub (fun a b => f b a)]
  conv_lhs => enter [2, a, 2, b]; rw [h1 a b]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if b < a then f a b else 0)]
  abel

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem pair_eq (h : IsCMExt F E σ) {n : ℕ} (S T : HermR R σ n) :
    pairHerm R σ n S T = coordPair R σ n (hermCoord R σ S) (hermCoord R σ T) := by
  unfold pairHerm coordPair
  rw [sum_sum_split (fun a b => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)]
  beta_reduce
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have := half_trace R h (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 a a) *
      (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (T.1 a a)))
    rw [map_mul, fixed_eq R h (S.2 a a), fixed_eq R h (T.2 a a)] at this
    simpa [hermCoord] using this
  · refine Finset.sum_congr rfl fun p _ => ?_
    have hT : T.1 p.1.2 p.1.1 = sigR R σ (T.1 p.1.1 p.1.2) := (T.2 p.1.2 p.1.1).symm
    have hS : S.1 p.1.2 p.1.1 = sigR R σ (S.1 p.1.1 p.1.2) := (S.2 p.1.2 p.1.1).symm
    simp only [hermCoord]
    rw [hT, hS]
    have hw : S.1 p.1.1 p.1.2 * sigR R σ (T.1 p.1.1 p.1.2) + sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2 =
        algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) (sigR R σ (S.1 p.1.1 p.1.2) * T.1 p.1.1 p.1.2)) := by
      rw [← add_sigR R h, add_comm, map_mul, sigR_sigR R h]
    rw [hw, half_trace R h]

variable [TopologicalSpace R] [IsTopologicalRing R]

end Main

end GlobalTheory.HermCoordEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedDatum_small_typePrime_any_level : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 1 < N.R.m → ∀ (P : rowSG Pr sel mu) (h : AutY X N.R i) (h' : AutY X N.R (i + 1)), h ∈ stabL X.E _ (lamYat (Pr := Pr) i P.1) → h' ∈ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1) → LocSmall (Formalism.L2.Col.qOf P.1) (lamYat (Pr := Pr) (R := N.R) i P.1) (lamYat (Pr := Pr) (R := N.R) (i + 1) P.1) (omPhi Ch sel mu cst i P h h') 1 := by
  first | exact @GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp | exact GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp | (intros; apply GlobalTheory.Core.Ht2.MovedDatumS.omPhi_locSmall_sharp <;> assumption)
end

