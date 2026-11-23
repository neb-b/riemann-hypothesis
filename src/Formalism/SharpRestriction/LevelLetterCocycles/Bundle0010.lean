module

public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.LocalRingCardinality.DataParams₂
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0010
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ImageMemOfGens
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
section
noncomputable section

namespace Formalism.MainNotions.AdmissibleParameterJ

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain

variable {D : D7}

section Sets

variable (D)

def c0 : ℚ := ((D.R.t : ℚ) - 1) / 2

def sz (j : ℕ) (ρ : D.what₂.Tau) : ℚ :=
  if h : j - 1 < D.R.m then (D.hc ρ).e ⟨j - 1, h⟩ else 0

def cloudJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin (D.R.k - 1), q = sz D j ρ + (D.hc ρ).v a + c0 D}

def lowJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin D.R.m, q = sz D j ρ - (D.hc ρ).b a + c0 D}

def blockJ : Set ℚ := {q | ∃ c : ℕ, c < D.R.t ∧ q = c}

def Jp (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudJ D j ρ ∪ lowJ D j ρ ∪ blockJ D

def refl (q : ℚ) : ℚ := ((D.R.t : ℚ) - 1) - q

def reflS (S : Set ℚ) : Set ℚ := {q | refl D q ∈ S}

def Jm (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := reflS D (Jp D j ρ)

def JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := if up then Jp D j ρ else Jm D j ρ

def cloudT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then cloudJ D j ρ else reflS D (cloudJ D j ρ)

def lowT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then lowJ D j ρ else reflS D (lowJ D j ρ)

def JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudT D up j ρ ∪ lowT D up j ρ

def dualS (S : Set ℚ) : Set ℚ := {q | -q - 1 ∈ S}

def PPm (j : ℕ) (ρ : D.what₂.Tau) : Multiset ℚ :=
  (Finset.univ.val.map fun a : Fin (D.R.k - 1) => (D.hc ρ).v a) +
  (Finset.univ.val.map fun a : Fin D.R.m => -(D.hc ρ).b a) +
  ((Finset.range D.R.t).val.map fun c : ℕ => -sz D j ρ + ((D.R.t : ℚ) + 1) / 2 - ((c : ℚ) + 1))

end Sets

section Emb

variable (D)

def PlaceOf (ρ : D.what₂.Tau) (g : D.R.GG) : Prop :=
  ((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨
    ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g

def TypeU (ep : Bool) (g : D.R.GG) : Prop := (g ∈ D.R.Psi ↔ ep = true)

def ReadAt (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG)
    (ρ : D.what₂.Tau) : Prop :=
  (D.naut.iotaQC i).toRingHom.comp τ₀ = D.host.emb g ∧ PlaceOf D ρ g

variable {D}

def gEmb {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    D.host.E →+* Qbar (D.nd.l i) :=
  (C.LL.1.val.toRingHom).comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw))

end Emb

section Stmt

variable (D)

def rQ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)) :=
  mapRep (iotaOQ D.nd D.naut i) (r x)

def rankOneCharacterQbar (i : D.nd.Loc) : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)) :=
  mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL i)


open Classical in
def hodgeTateJumpsAtModulesForSign (ep : Bool) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (g : D.R.GG) (ρ : D.what₂.Tau), ReadAt D i (gEmb C τ) g ρ ∧
        (∀ (x : D.nd.X i) (a : ℤ),
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)) ∧
        ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), π ∈ D.nd.Z i →
          TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ π → ∀ a : ℤ,
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)

def ConclusionJa : Prop := ∃ ep : Bool, hodgeTateJumpsAtModulesForSign D ep

variable {D} (L : SizeData₂ D)

def CloudCentreDistance : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ q ∈ cloudJ D j ρ, ((sz D j ρ : ℚ) : ℝ) ≤ ((q - c0 D : ℚ) : ℝ) ∧
      ((q - c0 D : ℚ) : ℝ) ≤ (sz D j ρ : ℝ) + L.Sc) ∧
    (∀ q ∈ lowJ D j ρ, ((D.R.t : ℚ) + 3) / 2 ≤ |q - c0 D| ∧ ((|q - c0 D| : ℚ) : ℝ) ≤ L.etaSz) ∧
    (∀ q ∈ blockJ D, |q - c0 D| ≤ c0 D) ∧
    (cloudJ D j ρ).ncard = D.R.k - 1 ∧ (lowJ D j ρ).ncard = D.R.m ∧ (Jp D j ρ).ncard = D.R.nV

def jcCondition : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ q ∈ lowJ D j ρ, (-L.etaSz + (c0 D : ℝ) ≤ (q : ℝ) ∧ q ≤ -2) ∨
      ((D.R.t : ℚ) + 1 ≤ q ∧ (q : ℝ) ≤ L.etaSz + (c0 D : ℝ))) ∧
    (∀ up, (-1 : ℚ) ∉ JJ D up j ρ ∧ (D.R.t : ℚ) ∉ JJ D up j ρ) ∧
    (∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q) ∧
    (0 : ℚ) ∉ cloudJ D j ρ ∪ lowJ D j ρ


variable (D) in
def JumpLowsSignCount : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    {q ∈ lowJ D j ρ | q < 0}.ncard = D.R.m - j ∧ {q ∈ lowJ D j ρ | 0 < q}.ncard = j ∧
    {q ∈ lowT D false j ρ | q < 0}.ncard = j ∧ {q ∈ lowT D false j ρ | 0 < q}.ncard = D.R.m - j ∧
    {q ∈ JW D true j ρ | q < 0}.ncard = D.R.m - j ∧ {q ∈ JW D false j ρ | q < 0}.ncard = D.R.k - 1 + j

def hJ : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t

def JumpAbsoluteBound : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau, ∀ up, ∀ q ∈ JJ D up j ρ,
    |(q : ℝ)| ≤ L.sc.b + L.Sc + L.etaSz + 1 + (c0 D : ℝ)) ∧
  L.sc.b + L.Sc + L.etaSz + 1 + (c0 D : ℝ) ≤ hJ L ∧ L.sc.b ≤ hJ L ∧ hJ L ≤ 2 * L.sc.b

def DualCloudSizes : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ up, ∀ u ∈ dualS (cloudT D up j ρ),
      ((sz D j ρ - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) ≤ ((|u| : ℚ) : ℝ) ∧
      ((|u| : ℚ) : ℝ) ≤ ((sz D j ρ + ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) + L.Sc) ∧
    (∀ up, ∀ u ∈ dualS (lowT D up j ρ),
      -L.etaSz - ((D.R.t : ℝ) + 1) / 2 ≤ (u : ℝ) ∧ (u : ℝ) ≤ L.etaSz - ((D.R.t : ℝ) + 1) / 2) ∧
    (∀ up, (0 : ℚ) ∉ dualS (JW D up j ρ)) ∧
    {u ∈ dualS (JW D false j ρ) | u < 0}.ncard = D.R.m - j ∧
    {u ∈ dualS (JW D true j ρ) | u < 0}.ncard = D.R.k - 1 + j

def ThickPlaceCloudSizes : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    ((D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces →
      ∀ up, ∀ u ∈ dualS (cloudT D up j ρ),
        L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ ((|u| : ℚ) : ℝ) ∧
        ((|u| : ℚ) : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + (L.etaSz + D.R.t + 2) + L.Sc) ∧
    ∀ up, ∀ u ∈ dualS (lowT D up j ρ ∪ blockJ D), ((|u| : ℚ) : ℝ) ≤ L.etaSz + D.R.t + 2

def JumpConditions : Prop := ConclusionJa D ∧ CloudCentreDistance L ∧ jcCondition L ∧ JumpLowsSignCount D ∧ JumpAbsoluteBound L ∧ DualCloudSizes L ∧ ThickPlaceCloudSizes L

end Stmt

section admitted

variable (D)

def AdmDict : Prop :=
  ∃ ep : Bool, ∀ (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) g ρ, ReadAt D i τ₀ g ρ →
    ∃ (sg : ℚ) (cτ : ℤ), (TypeU D ep g → sg = 1) ∧ (¬ TypeU D ep g → sg = -1) ∧
      (D.naut.locAutHodgeTateWeightsLevelZero i τ₀).map (fun n : ℤ => (n : ℚ)) =
        (PPm D (D.nd.j i) ρ).map (fun p => sg * p + cτ) ∧
      ∀ w, InducesW D.nd i τ₀ w → D.naut.IsdRW i (rankOneCharacterQbar D i) w ∧
        (D.naut.jumpsW i (rankOneCharacterQbar D i) τ₀).map (fun n : ℤ => (n : ℚ)) =
          {sg * (-sz D (D.nd.j i) ρ) - c0 D + cτ}

def AdmRead : Prop :=
  ∀ i r, GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      InducesW D.nd i (gEmb C τ) w ∧
      (∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp (gEmb C τ) = D.host.emb g) ∧
      ∀ x, D.naut.IsdRW i (rQ D i r x) w → D.naut.IsdRW i (rankOneCharacterQbar D i) w →
        ∀ c : ℤ, D.naut.jumpsW i (rankOneCharacterQbar D i) (gEmb C τ) = {c} →
          (∀ a : ℤ,
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
              ((D.naut.jumpsW i (rQ D i r x) (gEmb C τ)).count (a + c) : ℤ) ∧
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
              ((D.naut.jumpsW i (rQ D i r x) (gEmb C τ)).count (c - 1 - a) : ℤ)) ∧
          (∀ M : GE D.nd →* Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i),
            (M = rTwO D.nd i r x ∨ M = rDuO D.nd i r x) → ∀ a : ℤ,
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ≠ 0)) ∧
          ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), x ∈ D.nd.Z i →
            TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ x → ∀ a : ℤ,
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a =
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a -
                (if 0 ≤ a ∧ a < (D.R.t : ℤ) then 1 else 0) ∧
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a =
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ (-a - 1) ∧
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a ≠ 0) ∧
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a ≠ 0)

variable {D} (L : SizeData₂ D)

def AdmPar : Prop :=
  L.etaSz + D.R.t + L.Sc < L.sc.w'' D.R.n ∧ 3 * L.sc.w'' D.R.n ≤ L.sc.b ∧
    (∀ tt, (L.bT tt : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b) ∧ (D.R.t : ℝ) ≤ L.etaSz


end admitted

end Formalism.MainNotions.AdmissibleParameterJ

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExtensionClauses
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot35

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def CocycleClassImage (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F

def AdmExtC (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F

def ExtensionClassTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtC D HW F → CocycleClassImage D HW F

def InvariantCocycleClassImage (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm18 D HW F

def AdmExtCΔ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P8 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.Pr2a D HW F ∧ Formalism.MainNotions.HerrComplexNaturality.HerrExtensionUpToUnit D HW F

def InvariantCocycleClassTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtCΔ D HW F → InvariantCocycleClassImage D HW F

def AdmDss (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.P2 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm ∧ Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleQuotientGlobal D HW F

end Formalism.MainNotions.UnusedSlot35
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinrankMaxUnramifiedSubfieldPadicFinExtPos
section
noncomputable section

namespace Formalism.MainNotions.N.PreambleDegrees

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.PreambleDegrees.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem finrank_sup_adjoin (F : IntermediateField ℚ_[l] (Om l)) (y : Om l) :
    finrank ℚ_[l] ↥(F ⊔ IntermediateField.adjoin ℚ_[l] {y}) = finrank ℚ_[l] ↥F * (minpoly F y).natDegree := by
  have hint : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) y).tower_top
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup, ← IntermediateField.adjoin.finrank hint]
  set_option synthInstance.maxHeartbeats 200000 in
    exact (Module.finrank_mul_finrank ℚ_[l] ↥F ↥(IntermediateField.adjoin F {y})).symm

theorem Ks_eq (K : FinExt l) (s : ℕ) {z : Om l} (hz : IsPrimitiveRoot z (l ^ s)) :
    Ks K s = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {z} := by
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos _).ne'⟩
  unfold Ks
  congr 1
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one (show x ^ (l ^ s) = 1 from hx)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro x rfl; exact hz.pow_eq_one)

theorem finrank_Ks (K : FinExt l) {s : ℕ} (hs : 0 < s) :
    finrank ℚ_[l] ↥(Ks K s) = finrank ℚ_[l] ↥(K0 K) * (l ^ (s - 1) * (l - 1)) := by
  have hz := ζQ_primitive l s
  rw [Ks_eq K s hz, finrank_sup_adjoin, natDegree_minpoly_eq (F := K0 K) inf_le_right hs hz,
    Nat.totient_prime_pow Fact.out hs]

theorem finrank_maxUnramifiedSubfield_padicFinExt_pos (K : FinExt l) : 0 < finrank ℚ_[l] ↥(K0 K) := by
  have := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).injective
  exact finrank_pos

end Formalism.MainNotions.N.PreambleDegrees
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN eY IsRem fMX pullJ IsSer IsTrunc TCase)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSerZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : W.DD T)
    (c : ℕ → W.DD T) : Prop :=
  c 0 = 0 ∧ (∀ y, DL W T i (c y) ∧ c y ∈ W.N T) ∧
    ∀ K : ℕ, ∃ j : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ j •
      (((PD.p : ℕ) : O) ^ eY PD.p K • ζ -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y)))

def IsTrZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (ζ t : W.DD T) : Prop :=
  ∃ (c : ℕ → W.DD T) (r s : ℕ → LetA O n), IsSerZ W T i ζ c ∧
    (∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) ∧
    t = ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)

theorem isTrunc_iff (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (w z : W.DD T) :
    IsTrunc W T i j M X σ w z ↔ ∃ t, IsTrZ W T i j M X σ (W.γ T w - w) t ∧
      z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w - t := by
  constructor
  · rintro ⟨c, r, s, hc, hr, rfl⟩
    exact ⟨_, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
    exact ⟨c, r, s, hc, hr, rfl⟩

def TTool2Z [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n),
    (∀ ζ, DL W T i ζ → InPN W T 1 ζ → ∃ t, IsTrZ W T i j M X σ ζ t) ∧
    (∀ ζ t, DL W T i ζ → InPN W T 1 ζ → IsTrZ W T i j M X σ ζ t →
      DL W T (i + (j : ZMod n)) t ∧ t ∈ pullJ W T i j ∧
      ∃ p ∈ pullJ W T i j,
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T t - t) = fMX W M X • p) ∧
    (∀ (a a' : O) (ζ ζ' t t' t'' : W.DD T), DL W T i ζ → InPN W T 1 ζ → DL W T i ζ' →
      InPN W T 1 ζ' → IsTrZ W T i j M X σ ζ t → IsTrZ W T i j M X σ ζ' t' →
      IsTrZ W T i j M X σ (a • ζ + a' • ζ') t'' →
      ∃ p ∈ pullJ W T i j, t'' - (a • t + a' • t') = fMX W M X • p) ∧
    (∀ ζ t, DL W T i ζ → InPN W T M ζ → j = 1 → X ≤ (PD.p - 1) * M →
      IsTrZ W T i j M X σ ζ t → ∃ p ∈ pullJ W T i j, t = fMX W M X • p)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
section
noncomputable section

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N

namespace SumRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def StrongMultiplicityOneCuspidalSums : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

def IsobaricMultiplicityOne : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

end SumRepresentations

end Formalism.MainNotions.N.T2

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations in
theorem litGoodO : Formalism.MainNotions.N.LitGoodO := by
  intro l _ LL
  haveI : FiniteDimensional ℚ_[l] LL.1 := LL.2
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, ?_⟩
  have hr : Set.range (algebraMap (OL LL) LL.1) = ((OL LL).toSubring.toAddSubgroup : Set LL.1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr]
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_)
  intro x hx
  show x ∈ OL LL
  rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
  have : ‖x‖ < 1 := by simpa using hx
  exact le_of_lt this
end Formalism.MainNotions.N.T2
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalCongruenceBound
section
noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module

variable {D : D7}

def LocalCongruenceBound (CT eta : ℕ) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (c : ℚ) : Prop :=
  ∃ N r' : ℕ, 2 ≤ N ∧ N ≤ D.R.nV + 1 ∧ 1 ≤ r' ∧ 4 * r' ≤ N ^ 2 ∧
    (c : ℝ) ≤ ((D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) *
        (CT * (N * r' + (eta + D.R.t + 1) * (N + r'))))) : ℕ) : ℝ) +
      (Br.sPi D.loc D.nbr i ρ π : ℝ) +
      (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℝ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℝ) + 4 * D.R.nV * (D.nd.vdel i : ℝ) +
      D.R.t * (∑ q ∈ D.nd.Q i, (vZeta i q : ℝ))

end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
section
noncomputable section

namespace Formalism.MainNotions.TypePrimeCongruences

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def TypePrimeChoiceConclusions (D : D7) : Prop := @PairedCharacterCondition.TypePrimeChoiceLemmas D

def TypePrimeWildIdempotentChoice (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → HG D.nd D.naut i →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → PairedCharacterCondition.WildIdempotentChoice i r ρ π

end Formalism.MainNotions.TypePrimeCongruences
end
end

