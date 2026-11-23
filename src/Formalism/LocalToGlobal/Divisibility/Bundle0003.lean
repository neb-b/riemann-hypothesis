module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.RowLat

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

structure InertDat3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (I0 Ty : Type) where

  PlI : Type

  plI : PlI → I0

  opI : PlI × Ty → Module.End K B.S.Forms

abbrev Typ3 (K Pl0 I0 Ty : Type) [Field K] : Type := (Pl0 → K[X]) × (I0 × Ty → K)

namespace InertDat3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}
  {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) (ℓ : Lvl K G)

abbrev OpIx : Type := (B.Pl × ℕ) ⊕ (D.PlI × Ty)

def opAll : D.OpIx → Module.End K B.S.Forms := Sum.elim B.op D.opI

def HasRes3 (p : Typ3 K Pl0 I0 Ty) (x : D.OpIx → K) : Prop :=
  B.HasRes p.1 (fun i => x (Sum.inl i)) ∧ ∀ k : D.PlI × Ty, x (Sum.inr k) = p.2 (D.plI k.1, k.2)

def inertTypeEigenspaceSum (p : Typ3 K Pl0 I0 Ty) : Submodule K B.S.Forms := Col.eigSum D.opAll (D.HasRes3 p)

def resSet3 (X : Finset (G → K)) : Set (Typ3 K Pl0 I0 Ty) :=
  {p | (∀ P0, P0 ∉ Set.range B.pl → p.1 P0 = 1) ∧ (∀ P0, P0 ∉ Set.range D.plI → ∀ y, p.2 (P0, y) = 0) ∧
    B.inV0 (Lvl.full X) (D.inertTypeEigenspaceSum p) ≠ ⊥}


open Classical in
def ixFin3 (X : Finset (G → K)) : Finset (Typ3 K Pl0 I0 Ty) :=
  if h : (D.resSet3 X).Finite then h.toFinset else ∅

def part3 (Z : Submodule K B.S.Forms) (p : Typ3 K Pl0 I0 Ty) : Submodule K (Fin (B.dZ ℓ Z) → K) :=
  (B.inV0 ℓ (D.inertTypeEigenspaceSum p)).comap (B.zE ℓ Z).mulVecLin

def DiffAt (p p' : Typ3 K Pl0 I0 Ty) : Prop :=
  (∃ P : B.Pl, p.1 (B.pl P) ≠ p'.1 (B.pl P)) ∨ ∃ k : D.PlI × Ty, p.2 (D.plI k.1, k.2) ≠ p'.2 (D.plI k.1, k.2)

structure Ok3 : Prop where

  comm : Col.PairComm D.opAll

  split : Col.SplitOver D.opI

  opG : ∀ k g, Commute (D.opI k) (B.r g)

  plI_inj : Function.Injective D.plI

structure InertRationalAdjoint : Prop where

  rat : ∀ k a b, LinearMap.toMatrix B.S.basis B.S.basis (D.opI k) a b ∈ cmMax K

  adj : ∀ k, ∃ k', ∀ f g : B.S.Forms,
    B.S.csum (D.opI k f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (D.opI k' g : B.S.Cl → B.S.V)

def Stable3 (Z : Submodule K B.S.Forms) : Prop := ∀ i, Z ≤ Z.comap (D.opAll i)

end InertDat3

structure DefFam3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T J : Type) where

  F : DefFam K G Pl0 T J

  RI : ∀ t, InertDat3 (F.R t) I0 Ty

  LI : ∀ j t, InertDat3 (F.L j t) I0 Ty

  trI : J → (I0 × Ty → K) → I0 × Ty → K

namespace DefFam3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 I0 Ty T J : Type} [Fintype J] (F3 : DefFam3 K G Pl0 I0 Ty T J)

def tr3 (j : J) (p : Typ3 K Pl0 I0 Ty) : Typ3 K Pl0 I0 Ty := (F3.F.tr j p.1, F3.trI j p.2)

@[reducible] def base3 : DefBase K where
  K0 := cmMax K
  v0 := F3.F.v0
  Tup := T
  μ0 := F3.F.μ0
  Ix := ↥((F3.RI F3.F.μ0).ixFin3 F3.F.X)
  fIx := inferInstance
  J := J
  fJ := inferInstance

@[reducible] def amb3 : DefAmb F3.base3 where
  FR t := (F3.F.R t).S.Forms
  aR _ := inferInstance
  mR _ := inferInstance
  OpR t := (F3.RI t).OpIx ⊕ G
  opR t := Sum.elim (F3.RI t).opAll fun g => (F3.F.R t).r g
  ZHR t := (F3.F.R t).ZHg F3.F.X
  FL j t := (F3.F.L j t).S.Forms
  aL _ _ := inferInstance
  mL _ _ := inferInstance
  OpL j t := (F3.LI j t).OpIx ⊕ G
  opL j t := Sum.elim (F3.LI j t).opAll fun g => (F3.F.L j t).r g
  ZHL j t := (F3.F.L j t).ZHg F3.F.X

def toSub2 (Zs : DefSub F3.amb3) : DefSub F3.F.amb := ⟨Zs.Z, Zs.Zl⟩

def side3 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F3.amb3) : DefSide F3.base3 where
  nV t := (F3.F.R t).nV (F3.F.lvl P ψ)
  HV t := (F3.F.R t).HV (F3.F.lvl P ψ)
  Mt t := (F3.F.R t).Mt (F3.F.lvl P ψ)
  dQ t := (F3.F.R t).dZ (F3.F.lvl P ψ) (Zs.Z t)
  Pq t := (F3.F.R t).Pq (F3.F.lvl P ψ) (Zs.Z t)
  XQ t := (F3.F.R t).XQ (F3.F.lvl P ψ) (Zs.Z t)
  Qp t p := (F3.RI t).part3 (F3.F.lvl P ψ) (Zs.Z t) p.1
  dZ j t := (F3.F.L j t).dZ (F3.F.lvlA P ψ) (Zs.Zl j t)
  HT j t := (F3.F.L j t).HZ (F3.F.lvlA P ψ) (Zs.Zl j t)
  XT j t := (F3.F.L j t).XQ (F3.F.lvlA P ψ) (Zs.Zl j t)
  Tl j t := (F3.F.L j t).Tl (F3.F.lvlA P ψ) (Zs.Zl j t)
  Zp j t p := (F3.LI j t).part3 (F3.F.lvlA P ψ) (Zs.Zl j t) (F3.tr3 j p.1)

structure Ok3 (s : ℕ) : Prop where

  ok2 : F3.F.Ok s

  what₂ : ∀ t, (F3.RI t).Ok3

  lifts : ∀ j t, (F3.LI j t).Ok3

def IsType3 {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) (f : Typ3 K Pl0 I0 Ty → Typ3 K Pl0 I0 Ty) (x : D.OpIx → K) : Prop :=
  ∃ p ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, D.HasRes3 (f p) x

def TypesSep3 : Prop :=
  ∀ p ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI F3.F.μ0).ixFin3 F3.F.X, p ≠ p' →
    ∀ j, (F3.LI j F3.F.μ0).DiffAt (F3.tr3 j p) (F3.tr3 j p')

end DefFam3

end Formalism.L2.DIV
end
end

-- bundled from Formalism.LocalToGlobal.Divisibility.LiftLat
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Poly

variable {K : Type} [Field K]

def dualPoly (s : K) (R : K[X]) : K[X] := C R.leadingCoeff⁻¹ * R.reverse.comp (C s * X)

variable {Pl : Type}

def trScale (r m t : ℕ) (q : Pl → ℕ) (etaV : Pl → Kˣ) (P : Pl) : K :=
  (etaV P : K) * (q P : K) ^ ((2 * r + (m + 1) * t - 1) / 2)

def trLift (r m t : ℕ) (q : Pl → ℕ) (etaV : Pl → Kˣ) (Sg : Pl → K[X]) (P : Pl) : K[X] :=
  dualPoly (trScale r m t q etaV P) (Sg P)

end Poly

section Dat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

def liftDat (S : CSD K) (ρ : Representation K G S.Forms) (ok : Set Pl0)
    (op : ok × ℕ → Module.End K S.Forms) (r t : ℕ) (q : Pl0 → ℕ) (muV etaV : Pl0 → Kˣ) : BlockDat K G Pl0 where
  S := S
  r := ρ
  Pl := ok
  pl := Subtype.val
  q := fun P => q P
  n := r + t
  t := t
  op := op
  bl := [fun P => Col.firstValA muV etaV q r P]

def rowDat (S : CSD K) (ρ : Representation K G S.Forms) (ok : Set Pl0)
    (op : ok × ℕ → Module.End K S.Forms) (r m t : ℕ) (q : Pl0 → ℕ) (muV : Fin m → Pl0 → Kˣ) :
    BlockDat K G Pl0 where
  S := S
  r := ρ
  Pl := ok
  pl := Subtype.val
  q := fun P => q P
  n := r + m * t
  t := t
  op := op
  bl := List.ofFn fun j : Fin m => fun P : ok => Col.firstValB (muV j) q r m t P

def GoodStable (X : Finset (G → K)) : Prop := ∀ χ ∈ X, (fun g => χ g⁻¹) ∈ X

structure FamIn (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 T : Type) (m : ℕ) where

  v0 : InfinitePlace K

  μ0 : T

  X : Finset (G → K)

  r : ℕ

  t : ℕ

  q : Pl0 → ℕ

  muVal : Fin m → T → Pl0 → Kˣ

  etaVal : Pl0 → Kˣ

  ok : T → Set Pl0

  MtildeCSD : T → CSD K

  leftGroupActionRight : ∀ τ, Representation K G (MtildeCSD τ).Forms

  heckeR : ∀ τ, ok τ × ℕ → Module.End K (MtildeCSD τ).Forms

  MtCSD : Fin m → T → CSD K

  leftGroupActionLift : ∀ j τ, Representation K G (MtCSD j τ).Forms

  heckeL : ∀ j τ, ok τ × ℕ → Module.End K (MtCSD j τ).Forms

namespace FamIn

variable {T : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

def fam : DefFam K G Pl0 T (Fin m) where
  v0 := A.v0
  μ0 := A.μ0
  X := A.X
  R τ := rowDat (A.MtildeCSD τ) (A.leftGroupActionRight τ) (A.ok τ) (A.heckeR τ) A.r m A.t A.q fun j => A.muVal j τ
  L j τ := liftDat (A.MtCSD j τ) (A.leftGroupActionLift j τ) (A.ok τ) (A.heckeL j τ) A.r A.t A.q (A.muVal j τ) A.etaVal
  tr _ := trLift A.r m A.t A.q A.etaVal

def side (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A.fam.amb) : DefSide A.fam.base := A.fam.side P ψ Zs

end FamIn

end Dat

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

def etaW (w : HeightOneSpectrum (𝓞 K)) : ℕ := Formalism.HermitianLatticesTheory.locLen w.asIdeal (B.Tl ℓ Z) (B.cutZ ℓ Z)

def etaU (w : HeightOneSpectrum (𝓞 K)) : ℚ := Col.lenUW w (B.Tl ℓ Z) (B.cutZ ℓ Z)

def jT (w : HeightOneSpectrum (𝓞 K)) : ℤ := jw (B.HZ ℓ Z) w (B.Tl ℓ Z)

def DG : ℕ := Nat.card ℓ.P * B.S.DGam

def heckeSet : Set (Matrix (Fin B.S.dim) (Fin B.S.dim) K) := Set.range B.opMat

def vProj : Matrix (Fin B.S.dim) (Fin B.S.dim) K := B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)

def lE : Matrix (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ)) (Fin (B.dZ ℓ Z)) K := B.S.lvlPr B.r ℓ.P ℓ.ψ * B.fE ℓ Z

structure OkH : Prop where

  rat : ∀ i a b, B.opMat i a b ∈ cmMax K

  adj : ∀ i, ∃ i', ∀ f g : B.S.Forms,
    B.S.csum (B.op i f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (B.op i' g : B.S.Cl → B.S.V)

end BlockDat

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)

def etaJ (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) : ℚ := (F.L j t).etaU (F.lvlA P ψ) (Zs.Zl j t) w

def etaJW (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) : ℕ := (F.L j t).etaW (F.lvlA P ψ) (Zs.Zl j t) w

def JJ (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) : ℚ := (F.L j t).JexpU (F.lvlA P ψ) (Zs.Zl j t) w

def JJW (j : J) (t : T) (w : HeightOneSpectrum (𝓞 K)) : ℕ := (F.L j t).JexpW (F.lvlA P ψ) (Zs.Zl j t) w

end DefFam

section Statements

def EtaUnits : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)),
    B.etaU ℓ Z w * (Col.eW w : ℚ) = (B.etaW ℓ Z w : ℚ)

structure BlockHyp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ) : Prop where

  conj : IsConjAt v0

  irr : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ

  ok : B.Ok s

def LiftLattices : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s →
    Submodule.IsLattice K (B.Tl ℓ Z) ∧ Submodule.IsLattice K (B.cutZ ℓ Z) ∧ Submodule.IsLattice K (B.delZ ℓ Z) ∧
      B.delZ ℓ Z ≤ B.cutZ ℓ Z ∧ B.cutZ ℓ Z ≤ B.Tl ℓ Z

def BoundsIVAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s →
    ∀ w : HeightOneSpectrum (𝓞 K),
      B.jT ℓ Z w ≤ (B.etaW ℓ Z w : ℤ) +
        (B.dZ ℓ Z : ℤ) * ((B.JexpW ℓ Z w : ℤ) + vw w ((B.DG ℓ : ℕ) : K) + vw w (s : K))

end Statements

section Links

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)

def InEta (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (bd : J → ℝ) : Prop :=
  ∀ j : J, ∑ w ∈ Tw, lw w * (F.etaJW P ψ Zs j (μ w) w : ℝ) ≤
    bd j * ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0) : ℝ)

end Links

end Formalism.L2.DIV
end
end

