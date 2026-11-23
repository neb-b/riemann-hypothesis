module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0015

@[expose] public section

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

theorem le_of_sigmaEquiv {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin s) : d a ≤ n := by
  have h1 := Fintype.card_le_of_injective _ (sigma_mk_injective (β := fun a => Fin (d a)) (i := a))
  simpa [Fintype.card_congr e] using h1

section Loc

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory GlobalTheory.RegType

variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {w : HeightOneSpectrum (𝓞 E)}
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : IsRec h rc) (hDZ : DiscreteGroups.sglob.DzType.DepthZeroInertiaBig)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ

end Loc

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField



end DiscreteGroups.sglob.DzType.Rt

end
