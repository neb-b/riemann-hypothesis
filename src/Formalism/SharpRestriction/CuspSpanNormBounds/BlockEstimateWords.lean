module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonSummationDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables

@[expose] public section

section PartDefs

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Defs

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

end Defs

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs

section PartDefs2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Iface

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

end Iface

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs2

section PartE0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Append

variable {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ)

end Append

section E0

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {ha : ∀ i s v, a i s v ≠ 0} {Ks : ℕ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

end E0

end Formalism.MainNotions.BlockEstimateWords

end

end PartE0

section PartP72

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Small

variable {D : D7} {k0 : ℕ}

end Small

section P72

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

end P72

end Formalism.MainNotions.BlockEstimateWords

end

end PartP72

section PartP74

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section P74

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

end P74

end Formalism.MainNotions.BlockEstimateWords

end

end PartP74

section PartP73

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Psd

end Psd

section Lift

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

end Lift

end Formalism.MainNotions.BlockEstimateWords

end

end PartP73

section PartPPo0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Pos

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0} {χ : ℝ → ℝ} {Ks : ℕ} {E₀ Eg : ℝ}

end Pos

end Formalism.MainNotions.BlockEstimateWords

end

end PartPPo0

section PartPPo

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Main

variable {D : D7} {k0 : ℕ} {G : GramWordSpace.GramMap k0 D.R.rS} {X : GramWordSpace.Dat D k0}
  {a : ℕ → ℕ → D.what₂.Tau → ℂ} {cb : ℕ → ℕ → ℝ} {c0 : ℝ} {χ : ℝ → ℝ} {Ks : ℕ}
  {E₀ Eg E₁ E₂ E₃ C C4 T T' : ℝ} {δ : D.host.E} {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {κL : ℕ → ℕ → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Φ : ℝ → GramWordSpace.GWord D → TA.Pt D.host.E → H}

end Main

end Formalism.MainNotions.BlockEstimateWords

end

end PartPPo

section PartVec

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Vec

variable {D : D7} {k0 : ℕ} (G : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0)
  (a : ℕ → ℕ → D.what₂.Tau → ℂ) (cb : ℕ → ℕ → ℝ) (c0 : ℝ) (χ : ℝ → ℝ)

end Vec

end Formalism.MainNotions.BlockEstimateWords

end

end PartVec

section PartClosed

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartClosed

section PartR0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Sums

variable {W : Type}

end Sums

section Words

variable {D : D7}

end Words

end Formalism.MainNotions.BlockEstimateWords

end

end PartR0

section PartR0b

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Prob

variable {D : D7}

end Prob

section WordSet

variable {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (Ks : ℕ)

end WordSet

end Formalism.MainNotions.BlockEstimateWords

end

end PartR0b

section PartR1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartR1

section PartU

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartU

section PartPoPi

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Span

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

end Span

section Maps

open scoped FourierTransform

variable {ι : Type} [Fintype ι]

end Maps

section Main

open scoped FourierTransform

variable {ι : Type} [Fintype ι]

end Main

end Formalism.MainNotions.BlockEstimateWords

end

end PartPoPi

section PartLat1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

open NumberField

theorem trace_places {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

theorem trace_tau (D : D7) (x : D.host.E) :
    ((Algebra.trace ℚ D.host.E x : ℚ) : ℝ) = ∑ v, 2 * (plEmb D v x).re := by
  have := host_totallyComplex D
  rw [trace_places x]
  refine (Fintype.sum_bijective (plOf D) (plOf_bijective D) _ _ fun v => ?_).symm
  rcases InfinitePlace.embedding_mk_eq (plEmb D v) with h | h
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h]
  · show _ = 2 * ((InfinitePlace.mk (plEmb D v)).embedding x).re
    rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

section Scl

variable {ι : Type} [Fintype ι]

end Scl

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat1

section PartLat2a

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Alg

variable {K : Type} [Field K] [NumberField K]

end Alg

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2a

section PartLat2b

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Geo

open NumberField

variable (D : D7)

instance hostFieldTotallyComplex : NumberField.IsTotallyComplex D.host.E := host_totallyComplex D

theorem place_is_complex (v : D.what₂.Tau) : (plOf D v).IsComplex := NumberField.IsTotallyComplex.isComplex _

def l2Pl : D.what₂.Tau ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  Equiv.ofBijective (fun v => ⟨plOf D v, place_is_complex D v⟩) (by
    constructor
    · intro v w h
      exact (plOf_bijective D).1 (congrArg Subtype.val h)
    · intro w
      obtain ⟨v, hv⟩ := (plOf_bijective D).2 w.1
      exact ⟨v, Subtype.ext hv⟩)

instance no_real_places : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (NumberField.IsTotallyComplex.isComplex w.1)) w.2⟩

end Geo

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2b

section PartLat2c

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Main

open NumberField
open scoped Pointwise

variable (D : D7)

end Main

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2c

section PartLat2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Dens

open NumberField

end Dens

end Formalism.MainNotions.BlockEstimateWords

end

end PartLat2

section PartDefs3

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

def sclL (av : ℕ → ℕ → ℂ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | o, (t, s) :: bs => (av (o + 1) s * t, s) :: sclL av (o + s) bs

def okL (r : ℕ) (T T' : ℝ) (o s : ℕ) (t : ℂ) : Prop := t ≠ 0 ∧ (s = 1 → o = r → T * T' < Complex.normSq t)

def wLoc (k r : ℕ) (T T' : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (t, s) :: bs =>
    (if okL r T T' o s t then Real.sqrt (ptWeightFrom k r T T' o [(t, s)]) else 0) * wLoc k r T T' (o + s) bs

def cblk (κ : ℝ) (i s : ℕ) : ℝ := (κ ^ (s * (s - 1)))⁻¹ * ∏ l ∈ Finset.Ico i (i + s), κ ^ (4 * (l - 1))

def ccL (κ : ℝ) : ℕ → List (ℂ × ℕ) → ℝ
  | _, [] => 1
  | o, (_, s) :: bs => Real.sqrt (cblk κ (o + 1) s) * ccL κ (o + s) bs

structure LocFrame (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) (B : LocBessel D.R.k D.R.rS)
    (f : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (B.Wq →L[ℂ] B.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) where
  B' : LocBessel (k0 + 1) D.R.rS
  f' : GramWordSpace.GFn B'
  μ' : GramWordSpace.Sec k0
  av : ℕ → ℕ → ℂ
  A : ℝ
  hc : B'.c = cStd
  hε : ∀ i, B'.ε i = B.ε (Fin.cast (by omega) i)
  hlam : ∀ i, B'.lam i = B.lam (Fin.cast (by omega) i)
  hu : ∀ i, B'.u i = B.u (Fin.cast hk i)
  hu' : ∀ i, B'.u' i = B.u' (Fin.cast hk i)
  hT : Tz (k0 + 1) D.R.rS B'.z = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z
  hT' : Tz (k0 + 1) D.R.rS B'.z' = (‖B.c‖ / 2) ^ (2 * D.R.rS) * Tz D.R.k D.R.rS B.z'
  hsec : IsSection (k0 + 1) D.R.rS B'.z B'.z' μ'
  hf : UnitaryLevelOperators.IsKFinCoefT B'.σ f'
  hav : ∀ i s, ‖av i s‖ = (‖B.c‖ / 2) ^ (2 * i + s - 3)
  hA : 0 < A
  val : ∀ γ γ' : Point ℂ (D.R.rS + 1),
    ((Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ.1) *
        Real.sqrt (ptWeightFrom D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') 0 γ'.1) : ℝ) : ℂ) *
      hsInner ((BlockEstimateTheorem.vmOf D hk G).V B f γ.1) ((BlockEstimateTheorem.vmOf D hk G).V B f γ'.1) =
    ((A * (ccL (‖B.c‖ / 2) 0 γ.1 * ccL (‖B.c‖ / 2) 0 γ'.1) *
        (wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ.1) *
          wLoc (k0 + 1) D.R.rS (Tz (k0 + 1) D.R.rS B'.z) (Tz (k0 + 1) D.R.rS B'.z') 0 (sclL av 0 γ'.1)) : ℝ) : ℂ) *
      hsInner (G.V B' f' (sclL av 0 γ.1)) (G.V B' f' (sclL av 0 γ'.1))
  energy : ENNReal.ofReal (A * (B'.beta μ' f' f').re) ≤
    ∫⁻ p : (Fin D.R.rS → ℂ) × ℂ, ENNReal.ofReal (bcWeight D.R.k D.R.rS (Tz D.R.k D.R.rS B.z) (Tz D.R.k D.R.rS B.z') p *
      hsNormSq (B.J f (bigCell D.R.k D.R.rS p.1 (μsec p.2))))

section Glob

variable {D : D7} (L : LatticeDataWithDual D) (kap : D.what₂.Tau → ℝ) (av : D.what₂.Tau → ℕ → ℕ → ℂ) (Aa : D.what₂.Tau → ℝ)

end Glob

structure XTie {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (x : D.what₂.Tau → LocalDataRealPlace D) (T T' : ℝ) (kap : D.what₂.Tau → ℝ) : Prop where
  hT : ∀ v, X.T v = kap v ^ (2 * D.R.rS) * T
  hT' : ∀ v, X.T' v = kap v ^ (2 * D.R.rS) * T'
  lam : ∀ v, (X.loc v).lam = (x v).lam
  u : ∀ v, (X.loc v).u = (x v).u
  u' : ∀ v, (X.loc v).u' = (x v).u'
  a : ∀ v, X.a v = (x v).a
  b : ∀ v, X.b v = (x v).b
  a1 : ∀ v, X.a1 v = (x v).a1
  b1 : ∀ v, X.b1 v = (x v).b1

end Formalism.MainNotions.BlockEstimateWords

end

end PartDefs3

section PartN1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Fr

variable {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) (x : D.what₂.Tau → LocalDataRealPlace D) (l : D.what₂.Tau → Fin (k0 + 1))
    (R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (GramWordSpace.lev (Fr v).B' (Fr v).μ' j hj).POp)
    (Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : TopsChoicePartA.Word), TopsChoicePartA.AuxiliarySlotStates w.length → GramWordSpace.GFn (Fr v).B' → GramWordSpace.GFn (Fr v).B')

end Fr

end Formalism.MainNotions.BlockEstimateWords

end

end PartN1

section PartN2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartN2

section PartNum0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable


section Num

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}

variable (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

end Num

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum0

section PartNum1

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Num1

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}
    (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

end Num1

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum1

section PartNum2

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Num2

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}
    (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

end Num2

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum2

section PartNum3

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Num3

variable {D : D7} {k0 : ℕ} {X : GramWordSpace.Dat D k0} {Ks : ℕ} {E₀ Eg E₁ E₂ C T T' ϱ : ℝ} {δ : D.host.E}
    {x : D.what₂.Tau → LocalDataRealPlace D} {L : LatticeDataWithDual D} {Kd : KernelData D} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    {kap : D.what₂.Tau → ℝ} {av : D.what₂.Tau → ℕ → ℕ → ℂ}

variable (hH : ThmAHyp D C Ks δ T T' x L Kd B f μsec) (hX : XTie X x T T' kap)
    (hϱ : IsFrameScale D L ϱ) (hkap : ∀ v, kap v = kaV D δ v / ϱ)
    (hav : ∀ v i s, ‖av v i s‖ = kap v ^ (2 * i + s - 3))
    (hE₁ : 0 < E₁) (hE₁C : E₁ ≤ C) (hE₂ : 0 < E₂) (hE₂C : E₂ ≤ C)

include hH hX hϱ hkap hav hE₁ hE₁C hE₂ hE₂C

end Num3

end Formalism.MainNotions.BlockEstimateWords

end

end PartNum3

section PartVal0

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section Val

variable {D : D7} {L : LatticeDataWithDual D}

end Val

end Formalism.MainNotions.BlockEstimateWords

end

end PartVal0

section PartVal

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

section ValM

variable {D : D7} {k0 : ℕ} (hk : k0 + 1 = D.R.k) {G : GramWordSpace.GramMap k0 D.R.rS} {B : D.what₂.Tau → LocBessel D.R.k D.R.rS}
    {f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp)}
    {μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (Fr : ∀ v, LocFrame D hk G (B v) (f v) (μsec v)) (x : D.what₂.Tau → LocalDataRealPlace D) (l : D.what₂.Tau → Fin (k0 + 1))
    (R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (GramWordSpace.lev (Fr v).B' (Fr v).μ' j hj).POp)
    (Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : TopsChoicePartA.Word), TopsChoicePartA.AuxiliarySlotStates w.length → GramWordSpace.GFn (Fr v).B' → GramWordSpace.GFn (Fr v).B')

end ValM

end Formalism.MainNotions.BlockEstimateWords

end

end PartVal

section PartOuter

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartOuter

section PartPack

open Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace nonZeroDivisors NumberField

noncomputable section

namespace Formalism.MainNotions.BlockEstimateWords

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt Formalism.MainNotions.InterlacingSignCuts Formalism.MainNotions.BridgeLemma₅

attribute [local instance] Classical.propDecidable

end Formalism.MainNotions.BlockEstimateWords

end

end PartPack
