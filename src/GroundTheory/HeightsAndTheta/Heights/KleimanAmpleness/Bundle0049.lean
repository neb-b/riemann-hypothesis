module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockVecSegreJoin
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def PowRealises.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
        ∀ (p : ℕ) (c : ℤ), (Kleiman.twistMul Q.toSubSystem p c).secs =
          secOver F y (p • β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem ModelDimEq.full : ModelDimEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d
  obtain ⟨hnz, hsame⟩ := hmod
  choose c hc using hnz
  obtain ⟨c', hc', htr⟩ := exists_trdeg_chartRing_eq y _ hsame c hc
  have hy := trdeg_quotient_mIdealOver (F := F) y c hc
  have hx := trdeg_quotient_mIdealOver (F := F) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c' hc'
  rw [← htr, Fintype.card_unit] at hx

  have _ : (mIdealOver F y).IsPrime := RingHom.ker_isPrime _
  have _ : (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))).IsPrime :=
    RingHom.ker_isPrime _
  have hfin := trdeg_lt_aleph0_of_finiteType (R := F) (S := MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y)
  rw [hy] at hfin
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt le_self_add hfin)
  have dimy : ringKrullDim (MvPolynomial (Σ k, ι k) F ⧸ mIdealOver F y) = ((t + Fintype.card K : ℕ) : ℕ∞) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hy, ht]
    simp
  have dimx : ringKrullDim (Kleiman.Poly F N ⧸ Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      ((t + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ReindexDim.proof F (ι k₀) Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) N e,
      GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hx, ht]
    simp
  have hrel : relDim (mIdealOver F y) = ((t : ℕ) : WithBot (WithTop ℤ)) := by
    unfold relDim
    rw [dimy]
    have e₁ : WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
        ((((t + Fintype.card K : ℕ) : ℕ∞)) : WithBot ℕ∞) =
        (((((t + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
    rw [e₁, Nat.cast_add, add_sub_cancel_right]
    rfl
  rw [hrel]
  constructor
  · intro h
    have h' := h.dim
    rw [dimx] at h'
    have htd : t + 1 = d + 1 := by exact_mod_cast h'
    rw [show t = d by omega]
  · intro h
    have htd : t = d := by exact_mod_cast h
    refine ⟨inferInstance, fun p hp n => Kleiman.homogeneousComponent_mem_primeOf _ hp n, le_rfl,
      ⟨e (c k₀), ?_⟩, by rw [dimx, htd]⟩
    rw [Kleiman.mem_primeOf_of_isHomogeneous _ (isHomogeneous_X F _), aeval_X]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hc k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftComap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W' : Ideal (MRing (segreIdx ι) F)), IsMultiProjPrime W' →
      segreRels ι F ⊆ W' →
      IsMultiProjPrime (W'.comap (segreIncl ι F)) ∧ W' = segreLift ι F (W'.comap (segreIncl ι F))

theorem SegreLiftComap.hyps :
    IsMultiProjPrime (⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) ∧
      segreRels (fun _ : Unit => Fin 1) ℚ ⊆
        ((⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) : Set _) := by
  have : ∀ k, Nonempty (segreIdx (fun _ : Unit => Fin 1) k) := fun k => by
    rcases k with _ | _
    · exact ⟨fun _ => (0 : Fin 1)⟩
    · exact ⟨(0 : Fin 1)⟩
  refine ⟨NumbersDVR.isMultiProjPrime_bot, ?_⟩
  rintro g ⟨c, d, rfl⟩
  obtain rfl : c = d := Subsingleton.elim _ _
  simp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      FieldNumbers.relDim (mIdealOver F (segreJoin y)) = FieldNumbers.relDim (mIdealOver F y)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibreIdeal.Statement : Prop :=
  ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (F : Type) [Field F] (φ : O →+* F)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω),
    segreRels ι F ⊆ ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) : Set _) ∧
    (mIdealOver O y).map (MvPolynomial.map φ) ≤
      ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ)).comap (segreIncl ι F) ∧
    ∀ W : Ideal (MRing ι F), (mIdealOver O y).map (MvPolynomial.map φ) ≤ W →
      (mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) ≤ segreLift ι F W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftIntNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W → ∀ β : K → ℤ,
      intNum F (segreLift ι F W) ![IndefiniteRowSideFullHecke.Kleiman2.pullDeg β] = intNum F W ![β]

theorem SegreLiftIntNum.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      IsMultiProjPrime (segreLift ι F W)

theorem SegreLiftPrime.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (n : ℕ) (μs : Fin n → K → ℤ),
      NumbersDVR.intNum F (mIdealOver F (segreJoin y)) (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) =
        NumbersDVR.intNum F (mIdealOver F y) μs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreNef.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ β : K → ℤ,
      (IndefiniteRowSideFullHecke.Kleiman2.IsNef F (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔ IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SegreTwist.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∀ (β : K → ℤ) (c : ℤ),
      secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg (Sum.inl ())) =
        secOver S y (β + fun _ => c)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftRelDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
      relDim (segreLift ι F W) = relDim W

theorem SegreLiftRelDim.hyps : IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) :=
  NumbersDVR.isMultiProjPrime_bot

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ChartSecGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
      (∀ j, η j ∈ secOver S y β) →
      (GeneratesOver S y β η ↔
        ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
          (Submodule.span (Kleiman.chartRing S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (Set.range η) : Set Ω) =
            chartSecOver S y k₀ e β I)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

