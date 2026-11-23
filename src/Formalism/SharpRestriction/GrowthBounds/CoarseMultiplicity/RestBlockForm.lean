module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0010
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev GlobalTheory (X : Loc) := ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m

abbrev Vecs (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) :=
  ∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t

abbrev Syms (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) :=
  ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)

def KeptAll (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) : Prop :=
  ∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)

def InSSZ (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mm : ℝ) (X : Loc) [NeZero X.m] (β : GlobalTheory X)
    (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)).SSZ O
    (r := X.m)

def kapZ (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  ∑ x : TT × Bool, (m + 1) * Nat.log p (hhDegs TT aT bT x)

def zTen (K : Type) [Field K] (p : ℕ) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : K :=
  (p : K) ^ kapZ p m TT aT bT / ∏ x : TT × Bool, ((hhDegs TT aT bT x).factorial : K)


open Classical in
def FormAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∃ (κ : GlobalTheory X → O) (s s' : GlobalTheory X → Vecs O C0 CE1 CE2 X → Syms O C0 CE1 CE2 X),
      (∀ β, κ β ≠ 0 ∧ vLEO X.p (κ β) (4 * X.kap0)) ∧
      (∀ β u, KeptAll C0 CE1 CE2 X β → FamOK O C0 CE1 CE2 Cm X β u →
        InSSZ O C0 CE1 CE2 (X.m0 13) X β (s β u) ∧ InSSZ O C0 CE1 CE2 (X.m0 13) X β (s' β u)) ∧
      ∀ β u β' u', KeptAll C0 CE1 CE2 X β → KeptAll C0 CE1 CE2 X β' →
        FamOK O C0 CE1 CE2 Cm X β u → FamOK O C0 CE1 CE2 Cm X β' u' →
        ∀ a : Fin (numSeg X.TT) → O,
          (∀ j, segForm O X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) = algebraMap O (KK O) (a j)) →
        ∀ P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        ∀ Q ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
          InWj w (P - symFam (KK O) X.p C0 CE1 CE2 X β (s β u)) X.c →
          InWj w (Q - symFam (KK O) X.p C0 CE1 CE2 X β' (s' β' u')) X.c →
          ∃ ν : O, zTen (KK O) X.p X.m X.TT X.aT X.bT * fock P Q =
            algebraMap O (KK O) ((if β = β' then κ β * ∏ j, a j else 0) + w ^ X.c * ν)

def lgSeg (X : Loc) (j : Fin (numSeg X.TT)) : ℕ :=
  (∑ i : Fin (segS X.TT j), (Nat.log X.p (X.bT (segPos X.TT j i)) + Nat.log X.p (X.aT (segPos X.TT j i)))) +
    Nat.log X.p (X.aT (segNext X.TT j)) + Nat.log X.p (X.bT (segNext X.TT j))

def facSeg (X : Loc) (j : Fin (numSeg X.TT)) : ℕ :=
  (∏ i : Fin (segS X.TT j), (X.bT (segPos X.TT j i)).factorial * (X.aT (segPos X.TT j i)).factorial) *
    (X.aT (segNext X.TT j)).factorial * (X.bT (segNext X.TT j)).factorial

def zSeg (K : Type) [Field K] (X : Loc) (j : Fin (numSeg X.TT)) : K :=
  (X.p : K) ^ ((X.m + 1) * lgSeg X j) / (facSeg X j : K)

def BlockFormAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ (κ : O) (s s' : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O) →
          MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
          s u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m) ∧
          s' u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m)) ∧
        ∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ u' ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ a : O, ((specConst X.p (X.seg C0 CE1 CE2 j) b : ℕ) : KK O) * fock u u' = algebraMap O (KK O) a →
          ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s u))
              (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s' u')) = algebraMap O (KK O) (κ * (a + w ^ X.c * x))

def RestBlockForm : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => BlockFormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

def RestForm : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => FormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

end Formalism.MainNotions.ColumnSystems.Pf
