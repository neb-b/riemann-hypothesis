module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtensionPropertyPi
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleStageOfPackage
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad.Test

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Scheme.{0}}

end Lat

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Pts

section Stages

variable {D : D7} {N j : ℕ} {Comp : Type} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg}
  (P : PadPkg D N j Comp jC ng)


end Stages

section Sign

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

end Sign

section Phi

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

end Phi

end GlobalTheory.ShFam.Pad.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.LieMet GlobalTheory.Points GlobalTheory.GradedPieces
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Frm

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {C M : Type} [NormedField C] [IsUltrametricDist C] [AddCommGroup M] [Module C M] {m : ℕ}






end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {x' : Sp T ⟶ X}

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} (y : Z.Pt)

variable {y}




end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

variable {ct}


end GlobalTheory.LocM.Frm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ}

structure StFam (S : Sig A N j) (κ : Lv A) : Type 1 where
  st : ∀ {p : ℕ} (ct : At S κ p), Stages ct
  α : ℕ → ℕ → 𝓞 D.host.E
  hα : ∀ {p : ℕ} (ct : At S κ p), (st ct).locB.alp = α p

abbrev Ats (S : Sig A N j) (κ : Lv A) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → At S κ p

variable {S : Sig A N j} {κ : Lv A}

def Ats.Over (cts : Ats S κ) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (v : PlL D p), (cts p v).W = placeW D p v (jC p v)

def Stages.fix {p : ℕ} {ct : At S κ p} (st : Stages ct) : Stages ct := { st with mo := motTrue ct, ky := keyTrue ct }

structure LocAt (S : Sig A N j) (κ : Lv A) (p : ℕ) : Type 1 where
  loc : ModuliIntegralCharts.Loc D N j p
  ex : ModuliIntegralCharts.ExtA D loc
  locB : p.Prime → BoundaryLocalData.LocB D loc
  pbKF : ∀ {c : ℕ}, ngTrue.KF (D.R.f * N) c → loc.Sec (loc.keySh c)
  bc : CodeAt S κ → loc.Mdl


open Classical in
def bcAt {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) : ct.Mdl :=
  if h : ∃ Z', IsBCAt ct Z Z' then h.choose else ct.Xm

def primeAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) [Fact p.Prime] : LocAt S κ p :=
  haveI : Fintype (PlL D p) := finPl D p
  haveI : Nonempty (PlL D p) := plL_ne D p
  { loc := Loc.pi fun v => (F.st (cts p v)).fix.loc
    ex := ExtA.pi fun v => (F.st (cts p v)).fix.ex
    locB := fun _ => LocB.pi (fun v => (F.st (cts p v)).fix.locB) (F.α p) fun v => F.hα (cts p v)
    pbKF := fun kf v => (cts p v).pbKF kf
    bc := fun Z v => bcAt (cts p v) Z }

def fillAt (S : Sig A N j) (κ : Lv A) (p : ℕ) (hp : ¬ p.Prime) : LocAt S κ p where
  loc := (exists_loc_extA_nat D N j p).choose
  ex := (exists_loc_extA_nat D N j p).choose_spec.some
  locB h := absurd h hp
  pbKF _ := @Zero.zero _ (((exists_loc_extA_nat D N j p).choose.secAdd _).toZero)
  bc _ := (exists_loc_extA_nat D N j p).choose.Xm

def locAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) : LocAt S κ p :=
  if hp : p.Prime then @primeAt _ _ _ _ _ _ F cts p ⟨hp⟩ else fillAt S κ p hp

def locStOf (F : StFam S κ) (cts : Ats S κ) : LocSt D N j ngTrue where
  loc p := (locAt F cts p).loc
  ex p := (locAt F cts p).ex
  locB p := (locAt F cts p).locB
  pbKF p := (locAt F cts p).pbKF

def globStOf (F : StFam S κ) (cts : Ats S κ) : GlobSt fun p => ((locStOf F cts).loc p).Mdl where
  Xg := CodeAt S κ
  bc p := (locAt F cts p).bc
  DivG Z := CDiv Z.X
  effD B := B.Eff
  noVertD {Z} B := Z.NoVert B
  posBdD {Z} B := Z.PosBd B
  ampleOnAbelianBase Z m B := Z.AmpleHodge m B
  Met := QLB S.sys.Y κ.c κ.good
  nefFibM := QLB.NefFib
  ampleGen := QLB.AmpleGen
  limRA := QLB.LimRA

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.Pad

def inclQb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) : c.F →+* Qb :=
  c.F.val.toRingHom.codRestrict (algebraicClosure ℚ ℂ) fun a =>
    haveI := c.fin
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom c.F.val)


open Classical in
def carry {F : Type} [Field F] (f g : F →+* Qb) : Qb →+* Qb :=
  haveI : Nonempty (Qb →+* Qb) := ⟨RingHom.id Qb⟩
  if f = g then RingHom.id Qb else Classical.epsilon fun σ => σ.comp f = g

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

def ioAt (p : ℕ) [Fact p.Prime] (y : Pt s) : Qb →+* ℂ_[p] := (iotaP p).comp (carry y.fK (inclQb κ.c))

def normDetIo (p : ℕ) [Fact p.Prime] (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (io : Qb →+* ℂ_[p]) (a : Qb) : ℝ :=
  ‖io a‖ * Real.exp (∑ i : Fin N, y.lnRoot io p b (DV.tauEmb D τ) i)


open Classical in
def normDetAt (p : ℕ) (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (a : Qb) : ℝ :=
  if h : p.Prime then (haveI := Fact.mk h; normDetIo s p b τ y (ioAt s p y) a) else 1

def padAt {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
    (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s)
    (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp) : PadPkg D N j s.Comp jC ng :=
  { padOf s L G M F I with
    normDetT := fun p τ (y : Pt s) => normDetAt s p true τ y (F.sv τ y)
    normDetH := fun p τ (y : Pt s) => normDetAt s p false τ y (F.sv τ y) }

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
end
end

