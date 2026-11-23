module

public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RT.PeriodPointConditions

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions

attribute [local instance] MemberForms.clsPFin

def resC {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (z : (D.mem u).P.Wrow) :
    (D.mem u).P.Wrow :=
  open Classical in T.valP.eW.symm (fun c' => if c' = c then T.valP.eW z c' else 0)

def pcL {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (z : (D.mem u).P.Wrow)
    (F : (D.mem u).P.Mt) : ℂ :=
  ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ) * (D.fm u).ipP (resC T c (T.jM F)) (resC T c z)

def PerDec0At {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
    ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, ∀ c,
      ∃ y : D.what₂.LL, D.what₂.embLL y = pcL T c ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
        ∀ w : D.what₂.places.Pl, y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

def PerDec0 (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), PerDec0At T

theorem perDec0_of_cols {D : D7} (C : Formalism.L2.Forms.ColsTiedSym D) (h : ∀ u, PerDec0At (C.forms u)) (u : D.what₂.Word) :
    PerDec0 D u := ⟨_, _, C.forms u, h u⟩

def PerDecTw (D : D7) (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ pc : (T.fm u μ).clsP → (D.PTw u μ).Wrow → (D.PTw u μ).Mt → ℂ,
    (∀ z F, (D.PTw u μ).period z F = ∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * pc c z F) ∧
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ c,
      ∃ y : D.what₂.LL, D.what₂.embLL y = pc c ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ → y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.RT.PeriodPointConditions
