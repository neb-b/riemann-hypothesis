module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up.SerCp
open GlobalTheory.Mem.R3.Tr Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.ExportSeries hiding Base

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

section L1
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

private def weight {n : ℕ} (x : ExportSeries.Weight a.D n) : ExportSeries.Weight b.D n where
  p := (by with_unfolding_all exact (x.p :))
  q := (by with_unfolding_all exact (x.q :))
  ap := (by with_unfolding_all exact (x.ap :))
  am := (by with_unfolding_all exact (x.am :))
  c := (by with_unfolding_all exact (x.c :))
  lam := (by with_unfolding_all exact (x.lam :))

private def twist {A : Type} [CommGroup A] (x : Twist a.D A) : Twist b.D A where
  Q := (by with_unfolding_all exact (x.Q :))
  chi := (by with_unfolding_all exact (x.chi :))
  res := (by with_unfolding_all exact (x.res :))

private def typeDat {r : ℕ} (x : TypeDat a.D r) : TypeDat b.D r where
  Pg := (by with_unfolding_all exact (x.Pg :))
  P := (by with_unfolding_all exact (x.P :))
  mu := (by with_unfolding_all exact (x.mu :))

private def frame {S T : HSp a.D} (x : Frame S T) : @Frame b.D ((S)) ((T)) where
  ψ := (by with_unfolding_all exact (x.ψ :))
  θ := (by with_unfolding_all exact (x.θ :))
  sT := (by with_unfolding_all exact (x.sT :))
  BS := (by with_unfolding_all exact (x.BS :))
  BT := (by with_unfolding_all exact (x.BT :))
  ΛS := (by with_unfolding_all exact (x.ΛS :))
  ΛT := (by with_unfolding_all exact (x.ΛT :))
  βS := (by with_unfolding_all exact (x.βS :))
  βT := (by with_unfolding_all exact (x.βT :))
  f₀ := (by with_unfolding_all exact (x.f₀ :))

private def base {S T : HSp a.D} (x : ExportSeries.Base S T) : @ExportSeries.Base b.D ((S)) ((T)) where
  hr := (by with_unfolding_all exact (x.hr :))
  F := frame b x.F
  G := (by with_unfolding_all exact ((typeDat b x.G) :))
  de := twist b x.de
  w := (by with_unfolding_all exact ((weight b x.w) :))
  mu0 := (by with_unfolding_all exact (x.mu0 :))
  eta := (by with_unfolding_all exact (x.eta :))













end L1

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C)

end L2

private abbrev lt {B : Base} {C : Cols B} (c : Late B C) (n : NStage B C c.W) : Late B C := ⟨c.W, c.V, c.S, n, c.G⟩

section L2
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)

section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N}

end





section
variable {N : NData (lt c a).D.R (lt c a).D.host (lt c a).D.what₂} {X : NTw (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N} {ρ : Setup X}
  {Y : NExp (lt c a).D.R (lt c a).D.host (lt c a).D.what₂ (lt c a).D.LL0 N X} {i : X.Tw} {j : Fin (lt c a).D.R.m} {s : Bool} {rd : Rd ρ Y i j s}

end

end L2

section L3
open GlobalTheory.SeriesTie
variable {B : Base} {C : Cols B} {c : Late B C} {a : NStage B C c.W} (b : NStage B C c.W)
  {Γ : Type} [i1 : Group Γ] [i2 : Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 (lt c a).D.what₂.LL Γ Pl0 I0 (List ℕ) T (lt c a).D.R.m} {Ks : Type} [i3 : Field Ks] [i4 : NumberField Ks]
  [iK : Algebra Ks (lt c a).D.what₂.LL] {Rl : RealDat3 (lt c a).D A3 Ks}
  {v₀ : ∀ (j : Fin (lt c a).D.R.m) (σ : (lt c a).D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec} {j : Fin (lt c a).D.R.m}
  {X : ExportSeries.Base (Vc (lt c a).D j) (Wc (lt c a).D j)} {ν : ℂ}

end L3

section L4
open GlobalTheory.SeriesTie
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp)

end L4

end GlobalTheory.HeightCounting.Up.SerCp
end
