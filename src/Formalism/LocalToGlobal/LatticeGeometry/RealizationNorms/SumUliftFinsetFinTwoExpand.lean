module

public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.GelfandTransference.Bundle0001
public import Mathlib

@[expose] public section

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

variable [StarRing K]

variable [_root_.NumberField.IsTotallyComplex K]

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem nPl_mul_two [_root_.NumberField.IsTotallyComplex K] : Fintype.card (InfinitePlace K) * 2 = finrank ℚ K := by
  rw [NumberField.IsTotallyComplex.finrank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  ring

variable [StarRing K]

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings

open NumberField NumberField.InfinitePlace Module Matrix

noncomputable section

namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [_root_.NumberField.IsTotallyComplex K]

end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
