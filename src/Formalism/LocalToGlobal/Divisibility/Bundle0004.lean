module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.HeckeRI

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

namespace FamIn3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 I0 Ty T : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def indef2 {P : Subgroup G} {ψ : P →* Kˣ} {Zs : DefSub A3.fam3.amb3} (S : IndefData (A3.side3 P ψ Zs))
    (Ep : A3.A.fam.base.Ix → Submodule K (Fin S.D → K))
    (Wp : ∀ j : Fin m, A3.A.fam.base.Ix → Submodule K (Fin (S.dW j) → K))
    (lam : Fin m → T → A3.A.fam.base.Ix → InfinitePlace K → ℝ) :
    IndefData (A3.A.side P ψ (A3.fam3.toSub2 Zs)) where
  μ := S.μ
  Tw := S.Tw
  D := S.D
  XE := S.XE
  Ep := Ep
  ι := S.ι
  dW := S.dW
  XW := S.XW
  Wp := Wp
  M := S.M
  θ := S.θ
  κ := S.κ
  lam := lam
  err0 := S.err0

def indefDown {P : Subgroup G} {ψ : P →* Kˣ} {Zs : DefSub A3.fam3.amb3} (S : IndefData (A3.side3 P ψ Zs)) :
    IndefData (A3.A.side P ψ (A3.fam3.toSub2 Zs)) :=
  A3.indef2 S (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)

def cols2 {P : Subgroup G} {ψ : P →* Kˣ} {Zs : DefSub A3.fam3.amb3} (Dc : DefCols (A3.side3 P ψ Zs)) :
    DefCols (A3.A.side P ψ (A3.fam3.toSub2 Zs)) where
  Mem := Dc.Mem
  a := Dc.a
  Xc := Dc.Xc
  Pt := Dc.Pt

def sper2 {P : Subgroup G} {ψ : P →* Kˣ} {Zs : DefSub A3.fam3.amb3} {Dc : DefCols (A3.side3 P ψ Zs)} (Sp : SPer Dc) :
    SPer (A3.cols2 Dc) where
  HH := Sp.HH
  nHH := Sp.nHH
  iHH := Sp.iHH
  Pu := Sp.Pu
  Rw := Sp.Rw

def colData2 {P : Subgroup G} {ψ : P →* Kˣ} {Zs : DefSub A3.fam3.amb3} {Dc : DefCols (A3.side3 P ψ Zs)} {Sp : SPer Dc}
    {S : IndefData (A3.side3 P ψ Zs)} (C : ColData Dc Sp S)
    (Ep : A3.A.fam.base.Ix → Submodule K (Fin S.D → K))
    (Wp : ∀ j : Fin m, A3.A.fam.base.Ix → Submodule K (Fin (S.dW j) → K))
    (lam : Fin m → T → A3.A.fam.base.Ix → InfinitePlace K → ℝ) :
    ColData (A3.cols2 Dc) (A3.sper2 Sp) (A3.indef2 S Ep Wp lam) where
  B := C.B
  ζ := C.ζ
  sE := C.sE

end FamIn3

section Fam3

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m)

abbrev DivisionCompatibilityDataThreeSided (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) : Type :=
  DivisionCompatibilityData D A3.A P0 ψ0 Ps ψs (A3.fam3.toSub2 Zs) (A3.indefDown S0) (A3.indefDown S1) X0 (A3.cols2 Dc)

variable {D A3}

variable (D A3)

structure DivTied3 (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop where

  ranks : m = D.R.m ∧ A3.A.r = D.R.r ∧ A3.A.t = D.R.t

  grp : GrpTie D A3.A P0 ψ0 Ps ψs I.eG

  tup : TupTie D A3.A (A3.indefDown S0) I.tup

  mu1 : S1.μ = S0.μ

  sharp : RowSideTie D A3.A (Formalism.BasicNotions.RowSide.sharp D) Ps ψs (A3.fam3.toSub2 Zs) (A3.indefDown S1) I.tup I.eRR I.jA

  base : RowSideTie D A3.A X0.s P0 ψ0 (A3.fam3.toSub2 Zs) (A3.indefDown S0) I.tup I.eRR0 I.jA0

  mt : MtTie D A3.A P0 ψ0 (A3.fam3.toSub2 Zs) I.tup I.eMt

  th : ThTie D A3.A (A3.indefDown S0) I.tup I.eMt I.jW

  num : NumTie D A3.A (A3.indefDown S0) I.tup

  cols : ColTie D A3.A (A3.colData2 C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)) NuC I.wU I.eNu I.eRR

variable {D A3} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
  {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {S1 : IndefData (A3.side3 Ps ψs Zs)}
  {X0 : Formalism.BasicNotions.BaseLevelRowSide D} {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc}

end Fam3

section SplitParts

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL G Pl0 T m)

structure RowSideDef3 {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : Formalism.BasicNotions.RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb)
    (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup) (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop where

  forms : ∀ t, FormsTie D.what₂.embLL (jA t) (rH D A P ψ t) (rE D A P ψ t) (X.eOp (tup t))

  Mtilde : ∀ t, OLatTie D.what₂.embLL (X.Mtilde (tup t)) (jA t) (rNab D A P ψ t)

  iota : ∀ t (F : Fin ((A.fam.R t).nV (A.fam.lvl P ψ)) → D.what₂.LL),
    X.iota (tup t) (jA t ((rV0 D A P ψ t).mulVec F)) =
      X.jEE (eRR ((S.ι t).mulVec (((A.side P ψ Zs).Pq t).mulVec F)))

structure MtDef3 (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) : Prop where

  forms : ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap)
    (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))

  lat : ∀ (i : Fin m) (t : T), OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1))
    ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t)

structure ThDef3 {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    (S0 : IndefData (A.side P0 ψ0 Zs)) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin m) (t : T),
      (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) : Prop where

  li : ∀ i : Fin m, LinearIndependent ℂ fun k => jW i (Pi.single k 1)

  span : ∀ i : Fin m, Submodule.span ℂ (Set.range fun k => jW i (Pi.single k 1)) = ⊤

  lat : ∀ i : Fin m, OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (jW i) (S0.M i)

structure ColDef3 {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}
    {S1 : IndefData (A.side Ps ψs Zs)} {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (_C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (wU : D.what₂.Word → Dc.Mem)
    (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) : Prop where

  wU_bij : Function.Bijective wU

  Nu : ∀ u, HLatTie (D.div.Nu u) (NuC (wU u)) (Dc.Xc (wU u)) (eNu u)

end SplitParts

section Split

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m)

structure DivDef3 (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop where

  ranks : m = D.R.m ∧ A3.A.r = D.R.r ∧ A3.A.t = D.R.t

  grp : GrpTie D A3.A P0 ψ0 Ps ψs I.eG

  tup : TupTie D A3.A (A3.indefDown S0) I.tup

  mu1 : S1.μ = S0.μ

  sharp : RowSideDef3 D A3.A (Formalism.BasicNotions.RowSide.sharp D) Ps ψs (A3.fam3.toSub2 Zs) (A3.indefDown S1) I.tup I.eRR I.jA

  base : RowSideDef3 D A3.A X0.s P0 ψ0 (A3.fam3.toSub2 Zs) (A3.indefDown S0) I.tup I.eRR0 I.jA0

  mt : MtDef3 D A3.A P0 ψ0 (A3.fam3.toSub2 Zs) I.tup I.eMt

  th : ThDef3 D A3.A (A3.indefDown S0) I.tup I.eMt I.jW

  cols : ColDef3 D A3.A (A3.colData2 C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)) NuC I.wU I.eNu

structure DivRows3 (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs))
    (X0 : Formalism.BasicNotions.BaseLevelRowSide D) {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (_NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) : Prop where

  sharpRR : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown S1).RR (A3.indefDown S1).XE I.eRR

  baseRR : HLatTie X0.s.RR (A3.indefDown S0).RR (A3.indefDown S0).XE I.eRR0

  divisionRows_rationalLift : ∀ (i : Fin m) (t : T), Formalism.BasicNotions.Idx.Z0 D (I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (I.tup t) ((i : ℕ) + 1)) (I.eMt i t ((lZ0 D A3.A P0 ψ0 (A3.fam3.toSub2 Zs) i t).mulVec (Pi.single k 1))))

  thTheta : ∀ (i : Fin m) (t : T) x,
    D.what₂.thetaP (I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (I.tup t) ((i : ℕ) + 1) (I.eMt i t x)) =
      I.jW i (((A3.indefDown S0).θ i t).mulVec ((lPrj D A3.A P0 ψ0 (A3.fam3.toSub2 Zs) i t).mulVec x))

  num : NumTie D A3.A (A3.indefDown S0) I.tup

  colsBk : ∀ u x y, D.div.Bk u (I.eNu u x) (I.eRR y) =
    (A3.colData2 C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)).B (I.wU u) x y

variable {D A3} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
  {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {S1 : IndefData (A3.side3 Ps ψs Zs)}
  {X0 : Formalism.BasicNotions.BaseLevelRowSide D} {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc}

theorem DivTied3.ofSplit (hD : DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I) (hR : DivRows3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I) :
    DivTied3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I :=
  { ranks := hD.ranks
    grp := hD.grp
    tup := hD.tup
    mu1 := hD.mu1
    sharp := ⟨hR.sharpRR, hD.sharp.forms, hD.sharp.Mtilde, hD.sharp.iota⟩
    base := ⟨hR.baseRR, hD.base.forms, hD.base.Mtilde, hD.base.iota⟩
    mt := ⟨hD.mt.forms, hD.mt.lat, hR.divisionRows_rationalLift⟩
    th := ⟨hD.th.li, hD.th.span, hD.th.lat, hR.thTheta⟩
    num := hR.num
    cols := ⟨hD.cols.wU_bij, hD.cols.Nu, hR.colsBk⟩ }

end Split

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.TiedLemmas
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

def PlConjEq (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ w, D.plEq (D.what₂.places.conj w) = conjPl (D.plEq w)

section PlConj

open Formalism.BasicNotions

theorem plConj_vAdd (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx
    simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ _ hx, D.val_eq _ _ (star_ne_zero.mpr hx)] at h1
    exact WithTop.coe_injective h1

theorem mem_iff_vAdd_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hxK : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext (by rw [h]; simp))
  have hv : w.valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxK
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w x]
  unfold vAdd
  rw [neg_pos]
  conv_rhs => rw [← WithZero.exp_lt_exp, WithZero.exp_log hv, WithZero.exp_zero]

theorem plConjEq (D : D7) : PlConjEq D := by
  unfold PlConjEq
  intro w
  have hc : ∀ y : 𝓞 D.what₂.LL, ((cO D.what₂.LL y : 𝓞 D.what₂.LL) : D.what₂.LL) = star (y : D.what₂.LL) :=
    fun y => rfl
  have hcc : ∀ y : 𝓞 D.what₂.LL, cO D.what₂.LL (cO D.what₂.LL y) = y := fun y =>
    RingOfIntegers.ext (by rw [hc, hc, star_star])
  ext x
  show x ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔ x ∈ (D.plEq w).asIdeal.map (cO D.what₂.LL)
  first
    | rw [Ideal.mem_map_of_equiv]
    | rw [Ideal.mem_map_iff_of_surjective _ (cO D.what₂.LL).surjective]
  have hiff : (∃ y ∈ (D.plEq w).asIdeal, cO D.what₂.LL y = x) ↔ cO D.what₂.LL x ∈ (D.plEq w).asIdeal := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hcc]
    · intro h
      exact ⟨_, h, hcc x⟩
  rw [hiff]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hne : cO D.what₂.LL x ≠ 0 := fun h => hx (by rw [← hcc x, h, map_zero])
    rw [mem_iff_vAdd_pos _ x hx, mem_iff_vAdd_pos _ _ hne, plConj_vAdd, hc]

end PlConj

section Cut

open TensorProduct Formalism.BasicNotions.Rows

section CutTensor

variable {O R W : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup W] [Module O W] [Module R W]
  [IsScalarTower O R W]

end CutTensor

section OForm

def OForm {O : Type} [CommRing O] {φ : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : OLat O φ W) : Prop :=
  letI : Algebra O ℂ := φ.toAlgebra
  letI : Module O W := Module.compHom W φ
  haveI : IsScalarTower O ℂ W := ⟨fun a b w => mul_smul (φ a) b w⟩
  Function.Injective ((Submodule.span O (M.gen : Set W)).subtype.liftBaseChange ℂ)

end OForm

section CutRec


theorem restRowsFiniteGroupCard_pos (D : Formalism.BasicNotions.D7) : 0 < D.what₂.restRowsFiniteGroupCard := D.what₂.restRowsFiniteGroupCard_pos

end CutRec

end Cut

section Fam

variable (D : Formalism.BasicNotions.D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL G Pl0 T m)

theorem ranks_r_sym (D : Formalism.BasicNotions.D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  have h1 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega


end Fam

section Inhabit

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Inhabit

end Formalism.L2.DIV
end
end

