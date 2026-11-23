module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0024
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmaDN0OfAdmits
public import Formalism.SharpRestriction.LevelLetterCocycles.WachQuotientCyclicDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsOfGrading
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

def KillLevFacts (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => LevGrad ((HW l).W K 1 LL hG)

theorem annihilator_levels_of_grading (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hK : KillLevFacts D HW) : KillerLevelsTheorem D HW F Cm := by
  rintro ⟨-, h9⟩
  intro l _ K LL hG hC h5
  have hfd : FiniteDimensional (Padic l) ↥(K0 K) := by
    first
    | exact inferInstance
    | exact ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank (Padic l) ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hC
  have hT := tool_algebra_of_ring_condition D HW F h9 l K LL hC h5
  exact KL.killerLevCore_of _ (KF.psUnitE_of _ hR hT) (KF.psCoprime_of _ hR) (hK l K LL hG hC h5)
    (KF.psStable_of _ hR) hR.1

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DualLemmaOfDeterminant
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem evaluation_add (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f + g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f + Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_mul (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  funext i
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hz) f g

theorem evalZero_X_eq_pi0 (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  show PowerSeries.subst W.π₀₁ PowerSeries.X = W.π₀ i
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hz)]
  rfl

theorem evalZero_C (c : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C c) = algebraMap O (LetA O n) c := by
  funext i
  show PowerSeries.subst W.π₀₁ (PowerSeries.C c) = _
  rw [PowerSeries.subst_C]
  rfl

def AdaptData (T : LocLat G Qp LL O) (i : ZMod n) (h η m : ℕ) (e' : Fin (finrank LL T.V) → W.DD T)
    (m' : ℕ) (u : Fin m' → ℤ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T (i - 1) e' ∧ m' ≤ m ∧ ∃ hmr : m' ≤ finrank LL T.V,
    (∀ j, -(η : ℤ) ≤ u j ∧ u j ≤ η) ∧
    (∀ j (hj : e' (Fin.castLE hmr j) ∈ W.N T),
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨_, hj⟩)) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (u j)) ∧
    ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum (PD := PD) T τ h η ≤ ∑ j, ((h : ℤ) + u j)

def AdaptBas : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ),
        AdaptData W T₂ i (b i + S) η m e' m' u

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def ExpansionFormLetter (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  ∀ (c : ZMod n) (y : W.DD T), y ∈ DelS W T → y ∈ letS W T c → (∃ k : ℕ, W.Q ^ k • y ∈ W.N T) →
    (∀ ζ τ, Pt c ζ τ → ∀ (k : ℕ) (hk : W.Q ^ k • y ∈ W.N T) (i : ℤ),
      W.levN T c ζ ⟨W.Q ^ k • y, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) →
    y ∈ W.N T

end Local

def ExpansionFormAll (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ExpansionFormLetter ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG)

def ExpansionFormHypothesis : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → DdRFull D → DiRank D HW F Cm → ExpansionFormAll D HW

def ModelFLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → ExpansionFormAll D HW → modelFR D HW

theorem modelFStep_of (hL : ModelFLinkStep) (hP : ExpansionFormHypothesis) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
      DdRFull D → DiRank D HW F Cm → Adm1 D HW F Cm CA CB CK → modelFR D HW :=
  fun D HW F Cm CA CB CK hd hr hA => hL D HW F Cm CA CB CK hA (hP D HW F Cm CA CB CK hA hd hr)

def ModelQLinkStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CA CB CK : ℝ),
    Adm1 D HW F Cm CA CB CK → modelLR D HW → modelQR D HW

theorem modelQStep_of (hL : ModelQLinkStep) (hM : ModelLStep) : ModelQStep :=
  fun D HW F Cm CA CB CK hA => hL D HW F Cm CA CB CK hA (hM D HW F Cm CA CB CK hA)

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

structure LevSteps {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {Λ κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (e : Fin r → C.V) : Prop where

  k1b : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).K1b

  k1c : ∀ s < ell, ((lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).lev s).FiniteOrderFixed (baseIdOf hR).Bs.ℓ s

  k1d : ∀ s < ell, ((lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).lev s).PhiGammaCommute

  unitsAt : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).UnitsAt

  compl : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Compl ϖ

  filt : ∀ s < ell, IsFilt (FilD W T c s)

  jumps : ∀ s < ell, Formalism.ExponentWindows.G.Jumps (kind s) G₀ Sz η (b s) (FilD W T c s)

  mem : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Mem

  locReg : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocReg

  pa1b : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocalizesConst M e

  equiv : (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Equiv

  span : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N (c - (ell : ZMod n))

  ind : LinearIndependent (PowerSeries O) e

  locLIs : (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η).LocLIs lam

  lamInd : LinearIndependent LL lam

  lamSpan : Submodule.span LL (Set.range lam) = ⊤

theorem finalLevels_of {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {H : ℕ → ℕ} {κ : PowerSeries O} {r : ℕ} {lam : Fin r → Dc W T c}
    (Hy : LvHyp Lb hR uZ ιZ C c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ lam) (ϖ : O)
    (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) (e : Fin r → C.V)
    (hs : LevSteps Hy ϖ j M g G₀ Sz η kind b e) :
    E.FinalLevels (latOf C) c ell H (lvData Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η)
      (lvModel Hy ((baseIdOf hR).Bs.ff' ell j M g) kind b η) ϖ (W.χΓ W.gam) j M g G₀ Sz η kind b e lam
      (UL lam kind b η) :=
  { kind_eq := fun _ _ => rfl
    b_eq := fun _ _ => rfl
    η_eq := rfl
    k1b := hs.k1b
    hasU := fun _ _ => rfl
    k1c := hs.k1c
    k1d := hs.k1d
    unitsAt := hs.unitsAt
    compl := hs.compl
    filt := hs.filt
    jumps := hs.jumps
    mem := hs.mem
    locReg := hs.locReg
    pa1b := hs.pa1b
    equiv := hs.equiv
    span := hs.span
    ind := hs.ind
    flDef := fun _ _ _ => Iff.rfl
    locLIs := hs.locLIs
    lamInd := hs.lamInd
    lamSpan := hs.lamSpan
    uIs := fun _ _ _ => Iff.rfl }

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

structure MapSteps (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O)) : Prop where

  locComm : ∀ s < ell, ∀ (w : C₁.V)
    (hw : w ∈ (latOf C₁).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))
    (hw' : (latHomOf hC).f w ∈ (latOf C₂).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)),
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨w, hw⟩) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨(latHomOf hC).f w, hw'⟩

  loclComm : ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s y) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (E.extL P y)

  mapFl : ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s

  cMap : ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P

  prLIs : ∀ k, (latHomOf hC).f (e₁ k) -
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
    E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n)))

def levelMapOf (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (ms : MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P) :
    E.LevelMap (latHomOf hC) (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η)
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η) where
  prE := prEOf Mh ell
  prL := P
  loc_comm := ms.locComm
  locL_comm := ms.loclComm

theorem arc_of_steps (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (ϖ : O) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (ls₁ : LevSteps Hy₁ ϖ j M g G₀ Sz η kind b e₁) (ls₂ : LevSteps Hy₂ ϖ j M g G₀ Sz η kind b e₂)
    (ms : MapSteps hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P) :
    E.FinalArc (latHomOf hC) c ell H LL (KsW W) (DeltaT PD.p) ϖ (W.χΓ W.gam) j M g G₀ Sz η kind b :=
  ⟨{ r₁ := r₁
     r₂ := r₂
     S₁ := lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     S₂ := lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     m := levelMapOf hC Hy₁ Hy₂ Mh j M g η kind b e₁ e₂ P ms
     D₁ := Dc W T₁ c
     D₂ := Dc W T₂ c
     R₁ := lvModel Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     R₂ := lvModel Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η
     e₁ := e₁
     e₂ := e₂
     lam₁ := lam₁
     lam₂ := lam₂
     U₁ := UL lam₁ kind b η
     U₂ := UL lam₂ kind b η },
   { lev₁ := finalLevels_of Hy₁ ϖ j M g G₀ Sz η kind b e₁ ls₁
     lev₂ := finalLevels_of Hy₂ ϖ j M g G₀ Sz η kind b e₂ ls₂
     mapFl := ms.mapFl
     cMap := ms.cMap
     prLIs := ms.prLIs }⟩

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalCorollaryOfDeRham
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module

variable {l : ℕ} [Fact l.Prime]

theorem fd_mu (m : ℕ) :
    FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}) := by
  classical
  have hl : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have hfin : Set.Finite {x : Om l | x ^ (l ^ m) = 1} := by
    have : {x : Om l | x ^ (l ^ m) = 1} ⊆
        ((Polynomial.nthRoots (l ^ m) (1 : Om l)).toFinset : Set (Om l)) := by
      intro x hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hl).2 hx
    exact (Finset.finite_toSet _).subset this
  have := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

def richLL (K LL : FinExt l) (m : ℕ) : FinExt l :=
  ⟨(bigLL K LL).1 ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ m) = 1}, by
    have := (bigLL K LL).2
    have := fd_mu (l := l) m
    exact IntermediateField.finiteDimensional_sup _ _⟩

theorem le_richLL (K LL : FinExt l) (m : ℕ) : LL.1 ≤ (richLL K LL m).1 := (le_bigLL K LL).trans le_sup_left

theorem caseA_richLL (K LL : FinExt l) (m : ℕ) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) :
    CaseA K (richLL K LL m) :=
  ⟨hK, h2, le_rfl, fun h => absurd h h2, (le_inf le_rfl hK).trans le_sup_left, fun τ x =>
    (le_sup_left : (bigLL K LL).1 ≤ (richLL K LL m).1)
      ((le_sup_right : _ ≤ (bigLL K LL).1) (τ.fieldRange_le_normalClosure ⟨x, rfl⟩))⟩

theorem exists_prim_Om (m : ℕ) : ∃ x : Om l, IsPrimitiveRoot x (l ^ m) := by
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast hpos.ne'⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ m) (Om l))
    (Polynomial.degree_cyclotomic_pos (l ^ m) (Om l) hpos).ne'
  exact ⟨x, (Polynomial.isRoot_cyclotomic_iff).mp hx⟩

theorem prim_richLL (K LL : FinExt l) (m : ℕ) :
    ∃ ζ : ↥(richLL K LL m).1, IsPrimitiveRoot ζ (l ^ m) := by
  obtain ⟨x, hx⟩ := exists_prim_Om (l := l) m
  have hmem : x ∈ (richLL K LL m).1 :=
    (le_sup_right : _ ≤ (richLL K LL m).1) (IntermediateField.subset_adjoin _ _ hx.pow_eq_one)
  exact ⟨⟨x, hmem⟩, IsPrimitiveRoot.coe_submonoidClass_iff.mp hx⟩

theorem lift_of_caseA_rich (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) :
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
      (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)),
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) n emb ((Th l).v LL) := by
  intro l _ K LL n _ emb
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  intro hL h5
  have hn := hL.2.2.1
  subst hn
  have h5' : 5 ≤ l := by rwa [(Th l).PD_p K] at h5
  have hK : K.1 ≤ MaximalUnramifiedExtension l := by
    intro x hx
    obtain ⟨y, hy⟩ := hL.1.2 ⟨x, hx⟩
    have : (y : Om l) = x := congrArg Subtype.val hy
    rw [← this]
    exact y.2.2
  set m := N (finrank ℚ_[l] ↥(K0 K))
  have hA := caseA_richLL K LL m hK (by omega)
  let _ : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥(richLL K LL m).1) := Fintype.ofFinite _
  have H' : ThmELiftAt ((Th l).PD K) (O := ↥(OL (richLL K LL m))) (finrank ℚ_[l] ↥(K0 K))
      (fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      ((Th l).v (richLL K LL m)) := by
    intro hL'
    obtain ⟨a, ha⟩ := exists_rot (PD := (Th l).PD K)
      (emb := fun i => (IntermediateField.inclusion (le_richLL K LL m)).comp (emb i))
      (Wf l K (richLL K LL m) hA).emb_bij.2
      hL'.2.2.2.2.1 (Wf l K (richLL K LL m) hA).emb_σ
    have := thmELiftAt_rot (Wf l K (richLL K LL m) hA).emb a
      (hLift l K (richLL K LL m) hA h5' (prim_richLL K LL m))
    rw [← ha] at this
    exact this hL'
  exact thmELiftAt_bc (IntermediateField.inclusion (le_richLL K LL m)) ((Th l).v (richLL K LL m))
    emb (richLL K LL m).2 (by rw [(Th l).PD_p K]; exact (Th l).v_l _)
    ⟨inferInstance, Formalism.BasicNotions.Examples₂.LB.OL_dvr _, Formalism.BasicNotions.Examples₂.LB.OL_frac _⟩
    (hBC l K LL (richLL K LL m) (le_richLL K LL m)) H' hL h5

theorem local_theorem_of_cyclotomic_lift (Th : LocTheory) (N : ℕ → ℕ)
    (Wf : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
      LocWach ((Th l).PD K) ↥LL.1 ↥(OL LL) ((Th l).v LL) (finrank ℚ_[l] ↥(K0 K)))
    (hLift : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL)
      [NeZero (finrank ℚ_[l] ↥(K0 K))], 5 ≤ l →
      (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ (l ^ N (finrank ℚ_[l] ↥(K0 K)))) →
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) (finrank ℚ_[l] ↥(K0 K)) (Wf l K LL h).emb
        ((Th l).v LL))
    (hBC : admBC Th) : LiftingTheoremLocalTheory Th 800 :=
  ⟨lift_of_caseA_rich Th N Wf hLift hBC, thmEBound_holds⟩

end Formalism.MainNotions.N.Ln03
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.PrecompConst
section
namespace Formalism.MainNotions.UnusedSlot80.InvCut

open Formalism.MainNotions.N.Ln03

def PrecompConst : Prop :=
  ∀ (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ) (S : Set (ZMod (l ^ (s + 1)))ˣ),
    Subgroup.closure S = ⊤ → ∀ f : Rs LL l s → LL, (∀ a ∈ S, precomp LL l s a f = f) →
      ∃ c : LL, ∀ ζ : Rs LL l s, f ζ = c

def GenUnits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

end Formalism.MainNotions.UnusedSlot80.InvCut
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TwAllF
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ TwGoodAll D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

end Formalism.MainNotions
end
end

