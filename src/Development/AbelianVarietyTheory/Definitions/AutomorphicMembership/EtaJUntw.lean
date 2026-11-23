module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.DataRRMetric

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.Mem NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sub

@[reducible] def subFam {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn K G Pl0 T m) (p : T → Prop) (h0 : p A.μ0) : FamIn K G Pl0 {t // p t} m where
  v0 := A.v0
  μ0 := ⟨A.μ0, h0⟩
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal i t := A.muVal i t.1
  etaVal := A.etaVal
  ok t := A.ok t.1
  MtildeCSD t := A.MtildeCSD t.1
  leftGroupActionRight t := A.leftGroupActionRight t.1
  heckeR t := A.heckeR t.1
  MtCSD i t := A.MtCSD i t.1
  leftGroupActionLift i t := A.leftGroupActionLift i t.1
  heckeL i t := A.heckeL i t.1

@[reducible] def subLev {D : D7} {T : Type} (L : Links.LevCh D T) (p : T → Prop) : Links.LevCh D {t // p t} where
  C := L.C
  xiH t := L.xiH t.1
  mu0 := L.mu0
  eta := L.eta
  xi t := L.xi t.1
  Pg := L.Pg
  Q t := L.Q t.1
  chi := L.chi
  xiR t := L.xiR t.1
  ΛY := L.ΛY
  ΛX := L.ΛX
  ΛV := L.ΛV
  ΛW := L.ΛW
  βY := L.βY
  βX := L.βX
  βV := L.βV
  βW := L.βW

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def InUse (R : RealDat D A Ks) (t : T) : Prop := t = A.μ0 ∨ ∃ w, R.mu w = t

abbrev useFam (R : RealDat D A Ks) : FamIn D.what₂.LL G Pl0 {t // InUse R t} D.R.m := subFam A (InUse R) (Or.inl rfl)


set_option maxHeartbeats 2000000 in
def useReal (R : RealDat D A Ks) : RealDat D (useFam R) Ks where
  toLevCh := subLev R.toLevCh (InUse R)
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := ⟨fun t => R.B.R t.1, fun i t => R.B.L i t.1, R.B.rankR, R.B.rankL⟩
  prX := R.prX
  HX t := R.HX t.1
  HV i t := R.HV i t.1
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX t := R.jX t.1
  jV i t := R.jV i t.1
  νY t := R.νY t.1
  fdY t := R.fdY t.1
  ν0 := R.ν0
  fd0 := R.fd0
  νX t := R.νX t.1
  fdX t := R.fdX t.1
  νV i t := R.νV i t.1
  fdV i t := R.fdV i t.1
  νW := R.νW
  fdW := R.fdW
  ωY t := R.ωY t.1
  ωX t := R.ωX t.1
  ωP i t := R.ωP i t.1
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY t := R.vY t.1
  vX t := R.vX t.1
  vP i t := R.vP i t.1
  ItY := R.ItY
  ItX := R.ItX
  ioY t := R.ioY t.1
  ioX t := R.ioX t.1
  Th t := R.Th t.1
  BV := R.BV
  ioP := R.ioP
  thF i t := R.thF i t.1
  thG i t := R.thG i t.1
  nW := R.nW
  FW := R.FW
  mu w := ⟨R.mu w, Or.inr ⟨w, rfl⟩⟩
  twPl := R.twPl
  kap := R.kap
  lam i t := R.lam i t.1
  err0 := R.err0


open Classical in
def extSub (R : RealDat D A Ks) (F : Face D A) (Zs : DefSub (useFam R).fam.amb) : DefSub A.fam.amb where
  Z t := if h : InUse R t then Zs.Z ⟨t, h⟩ else (R.toCx F).zs.Z t
  Zl i t := if h : InUse R t then Zs.Zl i ⟨t, h⟩ else (R.toCx F).zs.Zl i t

def useFace (R : RealDat D A Ks) (F : Face D A) : Face D (useFam R) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc Zs := ⟨(F.Dc (extSub R F Zs)).Mem, (F.Dc (extSub R F Zs)).a, (F.Dc (extSub R F Zs)).Xc,
    fun u t => (F.Dc (extSub R F Zs)).Pt u t.1⟩
  Sp Zs := ⟨(F.Sp (extSub R F Zs)).HH, (F.Sp (extSub R F Zs)).nHH, (F.Sp (extSub R F Zs)).iHH, (F.Sp (extSub R F Zs)).Pu,
    (F.Sp (extSub R F Zs)).Rw⟩
  Zsc Zs :=
    let Z := F.Zsc (extSub R F Zs)
    ⟨Z.F0, fun t => Z.J0 t.1, Z.E1u, Z.l3m, Z.l3u, Z.l6m, Z.l6u, Z.x, Z.b, Z.la, Z.de⟩

structure IsTupAll (R : RealDat D A Ks) (F : Face D A) : Prop where
  tw : R.tup_tw F
  mu_off : R.tup_mu_off
  mu_ne : R.tup_mu_ne
  mu_conj : R.tup_mu_conj
  mu_on : R.tup_mu_on

structure CharAll (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  kap_use : (useReal R).scal_kap
  tup : IsTupAll R F

variable {R : RealDat D A Ks} {F : Face D A}





set_option maxHeartbeats 2000000 in
def useSide {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] {S : RowSide D EE} (Y : SideTie R F tup b S) :
    SideTie (useReal R) (useFace R F) (fun t => tup t.1) b S where
  eE := Y.eE
  eE_range := Y.eE_range
  eE_norm := Y.eE_norm
  eA t := Y.eA t.1
  eA_range t := Y.eA_range t.1
  eA_norm t := Y.eA_norm t.1
  eOp_tie t := Y.eOp_tie t.1
  iota_tie t := Y.iota_tie t.1
  lat_tie t := Y.lat_tie t.1


set_option maxHeartbeats 2000000 in
def useTie {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) : RowsTie (useReal R) (useFace R F) X0 where
  tup t := Y.tup t.1
  tup_inj _ _ e := Subtype.ext (Y.tup_inj e)
  tup_zero := Y.tup_zero
  muAt_tie := Y.muAt_tie
  sharp := useSide Y.sharp
  base := useSide Y.base
  ty := Y.ty
  ty_inj := Y.ty_inj
  ft_tie := Y.ft_tie
  framedRowBaseTie := Y.framedRowBaseTie
  eV i t := Y.eV i t.1
  eV_range i t := Y.eV_range i t.1
  eV_norm i t := Y.eV_norm i t.1
  eV_rat i t := Y.eV_rat i t.1
  eV_lat i t := Y.eV_lat i t.1
  eMt_tie i t := Y.eMt_tie i t.1
  eW := Y.eW
  eW_range := Y.eW_range
  eW_norm := Y.eW_norm
  eW_lat := Y.eW_lat
  theta_tie i t := Y.theta_tie i t.1
  isot_tie := Y.isot_tie
  lam_tie i t := Y.lam_tie i t.1
  etaJ_tie := Y.etaJ_tie


end Sub

section Metric

open scoped InnerProductSpace

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (v : InfinitePlace K) (f g : S.Forms) : ℂ :=
  ∑ i, ∑ j, star (v.embedding (S.basis.repr f i)) * v.embedding (S.H i j) * v.embedding (S.basis.repr g j)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

def AmbMetric {tup : T → D.what₂.Tup} {b : Bool} {S : RowSide D EE} (Y : SideTie R F tup b S) (amb : AmbForm D S) : Prop :=
  ∀ t, DV.Used D (tup t) → ∀ v : InfinitePlace D.what₂.LL, v ≠ InfinitePlace.mk D.what₂.embLL →
    ∀ (x y : (amb.MtH (tup t)).V) (f g : (A.MtildeCSD t).Forms),
      Y.eA t (amb.jAmb (tup t) x) = R.jX t f → Y.eA t (amb.jAmb (tup t) y) = R.jX t g →
        Formalism.HermitianLatticesTheory.majAt (amb.MtH (tup t)).b (amb.MtH (tup t)).X v x y =
          (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * csumAt (A.MtildeCSD t) v f g

def MjMetric {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) (X : DivX D) : Prop :=
  ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ InfinitePlace.mk D.what₂.embLL →
    ∀ (x y : (X.MjH ((i : ℕ) + 1)).V) (f g : Fin (R.nW i) → D.what₂.LL),
      Y.eW i (X.jM _ x) = (R.FW i).j (sg0 D A) f → Y.eW i (X.jM _ y) = (R.FW i).j (sg0 D A) g →
        Formalism.HermitianLatticesTheory.majAt (X.MjH ((i : ℕ) + 1)).b (X.MjH ((i : ℕ) + 1)).X v x y =
          (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) *
            ⟪(R.FW i).j (sgAt D.what₂.embLL v) f, (R.FW i).j (sgAt D.what₂.embLL v) g⟫_ℂ

def RowForm (S : RowSide D EE) : Prop :=
  (∃ b : Module.Basis (Fin (Module.finrank ℂ EE)) ℂ EE, ∀ y ∈ S.RRset D.what₂.mu0, ∀ i, b.repr y i ∈ Set.range D.what₂.embLL) →
    S.RRset D.what₂.mu0 ⊆ Set.range S.jEE

def quotNormAt {S : RowSide D EE} (amb : AmbForm D S) (v : InfinitePlace D.what₂.LL) (x : (amb.MtH D.what₂.mu0).V) : ℝ :=
  ⨅ u : {u : (amb.MtH D.what₂.mu0).V | amb.jAmb D.what₂.mu0 u ∈ S.Usp D.what₂.mu0},
    Formalism.HermitianLatticesTheory.normAt (amb.MtH D.what₂.mu0).b (amb.MtH D.what₂.mu0).X v (x + u)

def RowMetricDef (S : RowSide D EE) (amb : AmbForm D S) {n : ℕ} (onb : Fin n → EE) (ty : Fin n → D.what₂.FT) (X : DivX D)
    (E : EigIdx D X) (κ : (D.what₂.LL →+* ℂ) → ℝ) : Prop :=
  ∀ v : InfinitePlace D.what₂.LL, v ≠ InfinitePlace.mk D.what₂.embLL →
    ∀ (x : E.Pi → S.RR.V) (q : E.Pi → (amb.MtH D.what₂.mu0).V),
      (∀ c, amb.jAmb D.what₂.mu0 (q c) ∈ S.V0 D.what₂.mu0) →
      (∀ c, S.jEE (x c) = S.iota D.what₂.mu0 (amb.jAmb D.what₂.mu0 (q c))) →
      (∀ c, S.jEE (x c) ∈ Submodule.span ℂ (onb '' {σ | E.cOf (ty σ) = c})) →
        Formalism.HermitianLatticesTheory.normAt S.RR.b S.RR.X v (∑ c, x c) ^ 2 =
          ∑ c, κ v.embedding * Real.exp (∑ j ∈ SizeData₂.lifts D, DV.logLamC E j c v.embedding) * quotNormAt amb v (q c) ^ 2

def LogLamTie {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) (X : DivX D) : Prop :=
  ∀ (i : Fin D.R.m) π (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    X.logLam ((i : ℕ) + 1) π e = Real.log (R.lam i A.μ0 (Y.ty π) (InfinitePlace.mk e))

def eigOf {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) (X : DivX D) : EigIdx D X where
  Pi := A.fam.base.Ix
  dec := Classical.decEq _
  cOf := Y.ty
  lam_const _ _ _ _ _ _ _ h := by rw [Y.ty_inj h]

end Metric


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RowT (D : D7) (fr : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) : Type 1 where

  G : Type
  [grp : Group G]
  [fin : Fintype G]

  Pl0 : Type

  T : Type

  A : FamIn D.what₂.LL G Pl0 T D.R.m

  core : CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]

  R : RealDat D A core.Q.c.F

  F : Face D A

  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec

  char : CharAll R F
  guard : QGuard R

  fw : FWTie core R (kapTop D) v₀

  rho : RhoTie R

  bar : BarTie fw
  frame : R.C = fr

  p0 : BaseLevelRowSide D
  tie : RowsTie R F p0

  tup_onto : Function.Surjective tie.tup
  xi_eq : ∀ t, R.xiH t = xi (tie.tup t)

  rowForm : RowForm (RowSide.sharp D)
  rowForm0 : RowForm p0.s
  rrDef : DV.RRDef D
  rationalRoots_def : p0.s.RRDef
  kap_def : DV.KapDef D
  lam_def : DV.LamDef D
  bu_def : Rows.BuDefQ D.what₂
  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m →
    D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0

  amb : AmbForm D (RowSide.sharp D)
  amb0 : AmbForm D p0.s
  amb_metric : AmbMetric tie.sharp amb
  ambientBase_metric : AmbMetric tie.base amb0

  X : DivX D
  idx : IdxDefs D X
  kapR_def : DV.KapRBase X

  kapR_const : ∀ e, X.kapR e = X.kapR D.what₂.embLL
  Qp_eq : ∀ μ (p : ℕ), p ∈ X.Qp μ ↔ p.Prime ∧ ∃ v : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ v.asIdeal ∧ ¬ (xi μ).UnrAt v
  logLam_eq : LogLamTie tie X

  mj_metric : MjMetric tie X

  rr_metric : RRMetricDef D X amb (eigOf tie X)

  baseRow_metric : RowMetricDef p0.s amb0 D.what₂.onb0 D.what₂.ft0 X (eigOf tie X) fun _ => p0.kap0

  eQ : ∀ t, X.QPl (tie.tup t) ≃ R.Q t

  qv_eq : ∀ t v, X.qv (tie.tup t) v = Nat.card (kP (eQ t v).1)

  nu_eq : ∀ t v (i : Fin D.R.m), X.nu (tie.tup t) v ((i : ℕ) + 1) = (((fr.mu0 i * xi (tie.tup t)).val (eQ t v).1 : ℂˣ) : ℂ)

  vdd_eq : ∀ (p : ℕ) τ (P : HeightOneSpectrum (𝓞 D.host.E)), p.Prime → (p : 𝓞 D.host.E) ∈ P.asIdeal →
    X.vdd p τ = (multiplicity P.asIdeal (differentIdeal ℤ (𝓞 D.host.E)) : ℝ) / (eWL D.host.E P : ℝ)

attribute [instance] RowT.grp RowT.fin RowT.alg

namespace RowT

variable {D : D7} {fr : CharFrame D} {xi : D.what₂.Tup → HChar D.host.E} (r : RowT D fr xi)


end RowT

end GlobalTheory.Mem.Top

end
