module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam GlobalTheory.TotalFrame GlobalTheory.FlagPts Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}


open Classical in
def FlagFam.lat {Z : Mdl Y i₀} (s : FlagFam P Z) : Lat Z := if h : ∃ L : Lat Z, s.1 = allSteps L then h.choose else Lat.top Z


def Mdl.inclV (Z : Mdl Y i₀) : i₀.c.V W →+* Z.i.c.V W :=
  ((IntermediateField.inclusion Z.le).toRingHom.comp (i₀.c.V W).subtype).codRestrict _ fun a => a.2

end Family

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

section Reduction

abbrev V₀ : Type := κ.c.V ct.W

abbrev kbar : Type := AlgebraicClosure (ResidueField ct.V₀)

def ρ₀ : ct.V₀ →+* ct.kbar := (algebraMap (ResidueField ct.V₀) ct.kbar).comp (residue ct.V₀)

abbrev LaBar : Type := ct.kbar ⊗[ℤ] S.Dw.La

def eigLat (σ : D.host.E →+* ℂ) : Submodule ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) :=
  eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* _)) (embV κ.c ct.W σ)

def redLa : ct.V₀ ⊗[ℤ] S.Dw.La →ₗ[ℤ] ct.LaBar := ct.ρ₀.toIntAlgHom.toLinearMap.rTensor S.Dw.La

def eigBar (τ : PsiT D) : Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar (ct.redLa '' ct.eigLat (embOf D τ))

instance : FiniteDimensional ct.kbar ct.LaBar :=
  have := S.Dw.fin
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  Module.Finite.base_change ℤ _ _

abbrev FlP : Type := Flags ct.kbar fun τ : PsiT D => ↥(ct.eigBar τ)

def FlP.sub {ct : At S κ p} (F : ct.FlP) (τ : PsiT D) (i : ℕ) : Submodule ct.kbar ct.LaBar :=
  (F.step τ i).map (ct.eigBar τ).subtype

abbrev LaP (_ct : At S κ p) : Type :=
  S.Dw.La ⧸ (Ideal.span {(p : 𝓞 D.host.E)} • ⊤ : Submodule (𝓞 D.host.E) S.Dw.La)

def Sum1 : Type := {l : Submodule (𝓞 D.host.E) ct.LaP // (∃ l', IsCompl l l') ∧
  Nonempty (l ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)}))}

def Sum1.bar {ct : At S κ p} (l : ct.Sum1) : Submodule ct.kbar ct.LaBar :=
  Submodule.span ct.kbar {s | ∃ a : S.Dw.La, Submodule.Quotient.mk a ∈ l.1 ∧ s = 1 ⊗ₜ a}

def psiBar : LinearMap.BilinForm ct.kbar ct.LaBar := S.Dw.EF.baseChange ct.kbar

def locus (l : ct.Sum1) : Closeds ct.FlP :=
  between j (fun τ => l.bar.submoduleOf (ct.eigBar τ)) fun τ => (ct.psiBar.orthogonal l.bar).submoduleOf (ct.eigBar τ)

end Reduction

section Point

variable {Z : ct.Mdl} (y : ct.Pt Z)

def lieStep (σ : D.host.E →+* ℂ) (r : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  Submodule.span ↥y.C.S {w | ∃ (x : LieG (ct.htPt y).Gt) (u : Vecs S.Dw (ct.Y Z.i).t ↥y.C.S) (i : Fin (S.Dw.mult σ)),
    Z.FlagAt y.gen u ∧ (i : ℕ) < r ∧
    u σ i = spMap (dualMap (intO ↥y.C.S).subtype) ≫ ((ct.htPt y).lieCmp x).1.left ≫ htToModel (ct.dat y) ∧
    w = (ct.htPt y).bLie x}

def htStep (τ : PsiT D) (i : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  if i ≤ j then ct.lieStep y (embOf D τ) i
  else (ct.htPt y).eigV (embInt y.P (embOf D τ)) ⊓
    (ct.htPt y).pairV.orthogonal (ct.lieStep y (conjEmb (embOf D τ)) (N - i))

def LevelMatch (t : (htpTrue ct).Tp y) (a : S.Dw.La) : Prop :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  (Tate.lev t 1).left ≫ abVarι y.P = y.P.y ≫ ((ct.Y Z.i).oF.etaA a ^ (Z.i.l.A / p)).left

def redGraph (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) : AddSubgroup ((htpTrue ct).TC y × ct.LaBar) :=
  AddSubgroup.closure {q | ∃ (c : ↥(intO ↥y.C.S)) (t : (htpTrue ct).Tp y) (a : S.Dw.La), ct.LevelMatch y t a ∧
    q = ((show (ct.fld y).C from c.1) • (htpTrue ct).iT y t, ρ c ⊗ₜ a)}

def redSub (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) (F : Submodule (ct.fld y).C ((htpTrue ct).TC y)) :
    Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar {s | ∃ w ∈ F, (w, s) ∈ ct.redGraph y ρ}

end Point

def SpPt (Z : ct.Mdl) : Type :=
  {x : Sp ct.kbar ⟶ Z.X // x ≫ Z.s ≫ spMap Z.inclV = spMap ct.ρ₀}

def IsRedFlag {Z : ct.Mdl} (x : ct.SpPt Z) (F : ct.FlP) : Prop :=
  p ∣ Z.i.l.A ∧ ∃ (y : ct.Pt Z) (ρ : ↥(intO ↥y.C.S) →+* ct.kbar), spMap ρ ≫ y.z = x.1 ∧
    ∀ τ i, F.sub τ i = ct.redSub y ρ (ct.htStep y τ i)


open Classical in
def redFlag {Z : ct.Mdl} (x : ct.SpPt Z) : ct.FlP :=
  if h : ∃ F, ct.IsRedFlag x F then h.choose else Classical.arbitrary _


open Classical in
def diffExpo (_ct : At S κ p) (l : PsiT D → ℕ → ℤ) (σ : D.host.E →+* ℂ) : ℤ :=
  ∑ t : D.what₂.Tau, if σ = DV.tauEmb D t then ∑ i ∈ Finset.Icc (j + 1) N, l (D.eTau t) i else 0

def degLatPiece {Z B : ct.Mdl} (L : Lat B) {k : Type} [Field k] (c : Curve k Z.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degLat L (-ct.expo (indWt τ i))

end At

def crhOf (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (hf : ∀ Z, FlagFam P Z) : CrHSt ct (flgOf ct P) where
  nefHT Z l := ∀ c : Curve ct.Fbar (ct.flagCl Z (hf Z).1).X,
    0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degLatPiece (hf Z).lat c τ i : ℝ)
  descK Z l := Descends (ct.flagCl Z (hf Z).1) (hf Z).lat κ.l (ct.expo l) (ct.diffExpo l)
  bdryLoci Z := ∃ s : Set ct.Sum1, s.Finite ∧
    (∀ x : ct.SpPt (ct.flagCl Z (hf Z).1), (∃ z, ¬ Mdl.abP _ (x.1 z)) → ∃ l ∈ s, ct.redFlag x ∈ ct.locus l) ∧
    ∀ l ∈ s, dim (ct.locus l) + D.R.f * (N - 1) = D.R.f * (N * (N - 1) / 2)
  htFlags := hf
  YsP Z := ct.SpPt (ct.flagCl Z (hf Z).1)
  ysBd x := ∃ z, ¬ Mdl.abP _ (x.1 z)
  FlP := ct.FlP
  hFl x := ct.redFlag x
  FlCl := Closeds ct.FlP
  flMem F s := F ∈ s
  flDim := dim
  Sum1 := ct.Sum1
  locus := ct.locus
  bdryLoci_def _ := Iff.rfl
  CrvS Z := Curve ct.Fbar (ct.flagCl Z (hf Z).1).X
  degGr c := ct.degLatPiece (hf _).lat c
  nefHT_def _ _ := Iff.rfl

end GlobalTheory.LocM
