module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSfI
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlP
public import Formalism.LocalToGlobal.CharacterGerms.ValueEquationOfProjectors
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
variable {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C}

theorem upCharS_chartL (hL : UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : LabS E C Orb d} (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g) :
    UPCharSelfSt Y (selfOfLab ha hg o) Hc :=
  upCharS_at_chartL Pl.place_doubling_condition hL hie hd hY ha hg hr o Hc

variable (Xo c)

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValBr
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def EndoLogSt (Y : FBChart C V O dd) : Prop :=
  ∀ ε : Pt C 1 dd, (∀ i, MvPowerSeries.constantCoeff (ε i) = 0) →
    comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)) →
    ∀ (τ : Type) [Finite τ] (a : Fin dd → MvPowerSeries τ C), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
    ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => VP.exAt Y a q.2) (ε i) =
      VP.exAt Y (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • a j) i

end Formalism.L2.FormalSeriesBounds
end
end

