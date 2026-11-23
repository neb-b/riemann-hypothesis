module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import ReciprocityTheory.Automorphisms.Unitary
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
public import Formalism.LocalToGlobal.Columns.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Dec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def ActStable (P : RowPsi V n) (M : Mult.DSModel V Sp) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, actM P M h T ∈ Minf θ P M

def IpInv (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, ∀ T' ∈ Minf θ P M, Mult.ipM M μ 𝓕 (actM P M h T) (actM P M h T') = Mult.ipM M μ 𝓕 T T'

def HermPosLev (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ N : ℕ, 0 < N → PeterssonHilbertSpace.IsHermPos (Mult.Mult θ M (levN P N) (fun _ => 1)) (Mult.ipM M μ 𝓕)

def IsotDecomp (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  Mult.goodPart θ M J χ e = ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, isotL θ P M J χ e π ∧
    ∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' →
      ∀ x ∈ isotL θ P M J χ e π, ∀ y ∈ isotL θ P M J χ e π', Mult.ipM M μ 𝓕 x y = 0

end Dec

section DecProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {P : RowPsi V n} {M : Mult.DSModel V Sp}

theorem isMultMap_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k)
    {T : Mult.MMap M} (h : Mult.IsMultMap θ M J χ T) : Mult.IsMultMap θ M J' χ' T :=
  ⟨h.aut, h.cusp, fun v k hk g => by rw [h.lev v k (hJ hk) g, hχ k hk], h.equiv, h.cont⟩

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    Mult.Mult θ M J χ ≤ Mult.Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => isMultMap_mono hJ hχ hT

theorem levN_mono (N m : ℕ) : levN P (N * m) ⊆ levN P N := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

abbrev LN (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : RowPsi V n) (M : Mult.DSModel V Sp) (N : ℕ) :
    Submodule ℂ (Mult.MMap M) :=
  Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

theorem LN_directed : Directed (· ≤ ·) (LN θ P M) := by
  intro i j
  have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel hpos
  refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
  · apply mult_mono
    · rw [e]
      exact levN_mono _ _
    · intros
      rfl
  · apply mult_mono
    · rw [e, mul_comm]
      exact levN_mono _ _
    · intros
      rfl

theorem mem_Minf {T : Mult.MMap M} : T ∈ Minf θ P M ↔ ∃ N, T ∈ LN θ P M N :=
  Submodule.mem_iSup_of_directed _ LN_directed

theorem LN_le_Minf (N : ℕ) : LN θ P M N ≤ Minf θ P M := le_iSup (LN θ P M) N

theorem common3 {x y z : Mult.MMap M} (hx : x ∈ Minf θ P M) (hy : y ∈ Minf θ P M) (hz : z ∈ Minf θ P M) :
    ∃ N, x ∈ LN θ P M N ∧ y ∈ LN θ P M N ∧ z ∈ LN θ P M N := by
  obtain ⟨a, ha⟩ := mem_Minf.1 hx
  obtain ⟨b, hb⟩ := mem_Minf.1 hy
  obtain ⟨c, hc⟩ := mem_Minf.1 hz
  obtain ⟨d, had, hbd⟩ := LN_directed (θ := θ) (P := P) (M := M) a b
  obtain ⟨k, hdk, hck⟩ := LN_directed (θ := θ) (P := P) (M := M) d c
  exact ⟨k, hdk (had ha), hdk (hbd hb), hck hc⟩

theorem mult_le_Minf {J : Set (GA D V)} {χ : GA D V → ℂ} (hl : LevOK P J χ) : Mult.Mult θ M J χ ≤ Minf θ P M := by
  obtain ⟨N0, hN0, h0⟩ := hl
  have e : N0 - 1 + 1 = N0 := Nat.sub_add_cancel hN0
  refine le_trans ?_ (LN_le_Minf (N0 - 1))
  apply mult_mono
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).1
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).2.symm

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem hp3 (hHP : HermPosLev θ P M μ 𝓕) (x y z : Minf θ P M) :
    ∃ N, PeterssonHilbertSpace.IsHermPos (LN θ P M N) (Mult.ipM M μ 𝓕) ∧ (x : Mult.MMap M) ∈ LN θ P M N ∧
      (y : Mult.MMap M) ∈ LN θ P M N ∧ (z : Mult.MMap M) ∈ LN θ P M N := by
  obtain ⟨N, hx, hy, hz⟩ := common3 x.2 y.2 z.2
  exact ⟨N, hHP (N + 1) (Nat.succ_pos N), hx, hy, hz⟩

def ipA (hHP : HermPosLev θ P M μ 𝓕) : Minf θ P M →ₗ⋆[ℂ] Minf θ P M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => Mult.ipM M μ 𝓕 x y)
    (fun x x' y => by
      obtain ⟨N, hp, hx, hx', hy⟩ := hp3 μ 𝓕 hHP x x' y
      exact hp.add ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩)
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      exact hp.smul s ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x y y' => by
      obtain ⟨N, hp, hx, hy, hy'⟩ := hp3 μ 𝓕 hHP x y y'
      have h1 := hp.herm ⟨(y : Mult.MMap M) + y', Submodule.add_mem _ hy hy'⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h3 := hp.herm ⟨y', hy'⟩ ⟨x, hx⟩
      have h4 := hp.add ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩
      simp only [Submodule.coe_add] at h1 h2 h3 h4 ⊢
      rw [← h1, ← h2, ← h3, h4, map_add (f := _)])
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      have h1 := hp.herm ⟨s • (y : Mult.MMap M), Submodule.smul_mem _ s hy⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h4 := hp.smul s ⟨y, hy⟩ ⟨x, hx⟩
      simp only [Submodule.coe_smul] at h1 h2 h4 ⊢
      rw [← h1, ← h2, h4, map_mul, Complex.conj_conj]
      rfl)

end DecProofs

end Formalism.IndefR.principalLevelFrame
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Zero

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : Mult.DSModel V S)

end Zero

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def TopMultH (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) =
    Mult.MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

def datXP (R : RealDat D A Ks) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) : Formalism.L2.DIV.LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q t) P R.chi (R.xiR t) Frm.B


open Classical in
def SsetF (R : RealDat D A Ks) (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Sb ∪ R.Q t).image (Formalism.L2.DIV.underPl D.host.F)

def toChainReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) :
    ChainReal D where
  θ := R.θ
  ψ := R.ψ
  η := R.eta
  Ptw := Ptw D
  Y := Yc D
  SY j := Mult.parB (Ptw D) (min j D.R.m)
  MY := R.MY
  X := D.sp.X'
  MX := R.MX
  J _ μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j R.triv) else Set.univ
  χ _ μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j R.triv) else 0
  JX _ μ := levS _ R.βX (R.datXt (tupT μ))
  χX _ μ := levChi _ R.βX (R.datXt (tupT μ))
  meas _ μ j := R.νY (tupT μ) j
  fd μ j := R.fdY (tupT μ) j
  measX _ μ := R.νX (tupT μ)
  fdX μ := R.fdX (tupT μ)
  measE b := ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0
  fdE := R.fd0
  chr μ := R.toLevCh.mu (tupT μ)
  Sinf k := PolF D (Yc D (k + 1)).rank (Yc D k).rank
  pt _ μ k := R.ptY (tupT μ) k
  It := R.ItY
  th μ k := thetaKO (R.ωY (tupT μ) k)
  ioC _ μ k := if h : k + 1 < D.R.m then
      (LinearEquiv.ofEq _ _ (by simp only [if_pos (show k < D.R.m by omega)])).toLinearMap ∘ₗ
        R.ioY (tupT μ) k ∘ₗ (LinearEquiv.ofEq _ _ (by simp only [if_pos h])).toLinearMap
    else 0
  SinfX := PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank
  ptX _ μ := R.ptX (tupT μ)
  ItX := R.ItX
  thX μ := thetaKO (R.ωX (tupT μ))
  ioX _ μ := (LinearEquiv.ofEq _ _ (by simp only [if_pos (show D.R.m - 1 < D.R.m by omega)])).toLinearMap ∘ₗ
    R.ioX (tupT μ) ∘ₗ (LinearEquiv.ofEq _ _ (hTop (tupT μ)).symm).toLinearMap
  JE b := levS _ (R.βY 0) (R.dat0 (R.levR F b))
  χE b := levChi _ (R.βY 0) (R.dat0 (R.levR F b))
  eE _ := R.e0
  Sb := SsetF R (tupT D.what₂.mu0)
  volTop := 1
  JP b μ j := if j < D.R.m then levS _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else Set.univ
  χP b μ j := if j < D.R.m then levChi _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)) else 0
  JXP b μ := levS _ R.βX (datXP R (tupT μ) (R.levR F b))
  χXP b μ := levChi _ R.βX (datXP R (tupT μ) (R.levR F b))
  nrm b := (RealDat.nP F b)⁻¹

def levSubV (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (J : Set (GA D V)) (χ : GA D V → ℂ) :
    Submodule ℂ (GA D V → W) where
  carrier := {F | ∀ k ∈ J, ∀ g, F (g * k) = χ k • F g}
  add_mem' {F F'} hF hF' k hk g := by simp only [Pi.add_apply, hF k hk g, hF' k hk g, smul_add]
  zero_mem' k _ g := by simp
  smul_mem' c F hF k hk g := by simp only [Pi.smul_apply, hF k hk g, smul_comm c (χ k)]

def datVP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ (Vc D i).rank :=
  datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg (R.Q t) P (fun _ => R.chi ((i : ℕ) + 1)) (R.xiR t) Frm.A

def ipVia {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N] (e : H →ₗ[ℂ] N)
    (x y : N) : ℂ := by
  classical
  exact if h : x ∈ LinearMap.range e ∧ y ∈ LinearMap.range e then ⟪h.1.choose, h.2.choose⟫_ℂ else 0

def toLiftReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)
    (hinj : ∀ i t, Function.Injective (R.extV i t)) :
    LiftReal D (toChainReal R F tupT hm hTop) where
  V := Vc D
  W := Wc D
  κ i := kapAt (Wc D i) (sg0 D A)
  SW i := parAt (Wc D i) (sg0 D A)
  MW i := R.MW i (sg0 D A)
  JW i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χW i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  eW i := R.eWf i (sg0 D A)
  JA i := levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  χA i := levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))
  measW i := ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i
  fdW i := R.fdW i
  SbW := SsetF R (tupT D.what₂.mu0)
  TauV i := (R.cV i).W
  Amt μ i := LinearMap.range (R.extV i (tupT μ)) ⊓
    levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
      (levChi _ (R.βV i) (datVP R i (tupT μ) (R.levR F false)))
  ipA μ i := fun x y => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) x y
  measV μ i := R.νV i (tupT μ)
  fdV μ i := R.fdV i (tupT μ)
  TK i := LowT (R.MW i (sg0 D A))
  embK i := PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype
  Sinf' i := PolF D (Wc D i).rank (Vc D i).rank
  ioK i := R.ioP i
  ptW μ i := R.ptP i (tupT μ)
  thW μ i := fun g h f => thetaKO (R.ωP i (tupT μ)) h g f
  thC μ i := LinearMap.lcomp ℂ (GA D (Wc D i) → ℂ) (PiTensorProduct.map fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ R.thF i (tupT μ) ∘ₗ
    (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left

structure RecReal (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t))
    (X0 : BaseLevelRowSide D) (Ish : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true)
    (I0 : RowIds X0.s (toChainReal R F tupT hm hTop) false)
    (IL : LiftIds (toLiftReal R F tupT hm hTop hinj)) (K : ColReal D) {Xd : DivX D} (E : EigIdx D Xd)
    (labPi : E.Pi → A.fam.base.Ix) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (ι : ∀ i, ↥(GfC (Yc D 0)) →* ↥(GfC (Wc D i))) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D R.C nch) : Prop where

  base : R.BaseW F

  tied : RecTied D X0 (toChainReal R F tupT hm hTop) Ish I0 (toLiftReal R F tupT hm hTop hinj) IL K

  prtE : ∀ π, Ish.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtE0 : ∀ π, I0.prt π = (principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F false)))
    (levChi _ (R.βY 0) (R.dat0 (R.levR F false))) R.e0 (principalLevelFrame.rowRepR R.θ (eFT π))).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtWE : ∀ i π, IL.prtW i π = (principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A))
    (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
    (R.eWf i (sg0 D A)) (principalLevelFrame.rowRepR R.θ (eFT π))).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

  xi : ∀ μ, Used0 D μ → K.xi μ = R.toLevCh.xi (tupT μ)

  tupXi : ∀ μ, Used0 D μ → R.toLevCh.xiH (tupT μ) = Tp.xi μ

  tupAt : ∀ w, tupT (D.what₂.muAt w) = R.mu (D.plEq w)

  isomFin : ∀ i, principalLevelFrame.IsIsomFin (ι i)

  frameMatch : ∀ i, principalLevelFrame.FrameMatch PY (PW i) (ι i)

end FromLinks

end Formalism.IndefR.RecTie

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.NearConstantMultiplicities
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure CxPassIn3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : Prop where

  ratMuP : X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false

  isGood : Formalism.IndefR.TransferLatticeStatement.IsGood τ

  chars : Formalism.IndefR.CxPass.CharsX τ A3.A.fam.X

  m1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩

  nbarPos : 0 < nbar

  near_constant_multiplicities : Formalism.IndefR.CxPass.NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de

  laTie : ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G

section Pass3

variable [_root_.NumberField.IsTotallyComplex K] {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {X : CxData A3.fam3.amb3} {s : ℕ} {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}
  {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
  [∀ s, FiniteDimensional K (Ws s)] {τ : ∀ s, Representation K G (Ws s)} {nbar : ℝ}

theorem passage3_of (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true) :=
  Formalism.IndefR.CxPass.cutPassage3S K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar hN.ok hN.sep
    hN.stable hN.inBlock hN.h4pos (hN.pos false) (hN.pos true) (fun b => (hN.what₂ b).1) hN.ratMu hN.h2P hP.ratMuP
    hN.gUnit hN.gEquiv hN.npTie.1 hN.npTie.2 hP.isGood hP.chars hP.m1 hP.nbarPos hP.near_constant_multiplicities hP.laTie

def packageFullHecke (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  basePackageFullHecke { toPrimitiveStatementsBaseLiftsOnly := hN, passage := passage3_of hN hP }

end Pass3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.TensCastR
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

def RowRepTie {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar} (rowRep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E n)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V))
    (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  ∀ σ, (rowRep σ).Iso (rowRepR θ (eFT σ))

def RowLocPin {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V D.R.r)
    (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  Formalism.L2.RowLocTied D lp (Formalism.L2.Col.rowFrameOf D (OccRows θ PY M J χ e) eFT)

end Formalism.IndefR.principalLevelFrame

end
end

