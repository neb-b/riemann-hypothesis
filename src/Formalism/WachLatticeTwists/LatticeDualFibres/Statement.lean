module

public import Formalism.WachLatticeTwists.Statement
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.StatementRho

@[expose] public section

universe u

open Formalism.NG (KO annih)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

def eO (O : Type u) [CommRing O] (ℓ : ℕ) : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def toKO (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    FractionRing O →ₗ[O] KO O := Submodule.mkQ _

def mulSub {O : Type u} [CommRing O] (a : O) (M : Type u) [AddCommGroup M] [Module O M] :
    Submodule O M := LinearMap.range (LinearMap.lsmul O M a)

structure DirectPush (O A HV : Type u) [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV]
    [Module O HV] (q : HV →ₗ[O] A) where
  HY : Type u
  HVY : Type u
  HL : Type u
  HVL : Type u
  [gY : AddCommGroup HY] [mY : Module O HY]
  [gVY : AddCommGroup HVY] [mVY : Module O HVY]
  [gL : AddCommGroup HL] [mL : Module O HL]
  [gVL : AddCommGroup HVL] [mVL : Module O HVL]

  jY : HY →ₗ[O] HVY

  jL : HL →ₗ[O] HVL

  p1 : HL →ₗ[O] HY

  p2 : HVL →ₗ[O] HV

  φs : HY →ₗ[O] A
  comm : ∀ x : HL, φs (p1 x) = q (p2 (jL x))

  HfVY : Submodule O HVY

  HfVL : Submodule O HVL

attribute [instance] DirectPush.gY DirectPush.mY DirectPush.gVY DirectPush.mVY DirectPush.gL
  DirectPush.mL DirectPush.gVL DirectPush.mVL

namespace DirectPush

variable {O A HV : Type u} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV]
    [Module O HV] {q : HV →ₗ[O] A} (P : DirectPush O A HV q)

def HfY : Submodule O P.HY := P.HfVY.comap P.jY

end DirectPush

structure DualPush (O A HT' : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    (pr : A →ₗ[O] HT' →ₗ[O] KO O) where
  HY : Type u
  HVY : Type u
  HVY' : Type u
  HLb : Type u
  HVLb : Type u
  [gY : AddCommGroup HY] [mY : Module O HY]
  [gVY : AddCommGroup HVY] [mVY : Module O HVY]
  [gVY' : AddCommGroup HVY'] [mVY' : Module O HVY']
  [gLb : AddCommGroup HLb] [mLb : Module O HLb]
  [gVLb : AddCommGroup HVLb] [mVLb : Module O HVLb]

  jY : HY →ₗ[O] HVY

  jLb : HLb →ₗ[O] HVLb

  p1 : HLb →ₗ[O] HT'

  p2 : HVLb →ₗ[O] HVY'

  φs : HY →ₗ[O] A

  prF : HVY →ₗ[O] HVY' →ₗ[O] FractionRing O
  cup : ∀ (y : HY) (x : HLb), pr (φs y) (p1 x) = toKO O (prF (jY y) (p2 (jLb x)))

  HfVY : Submodule O HVY

  HfVY' : Submodule O HVY'

  HfVLb : Submodule O HVLb

attribute [instance] DualPush.gY DualPush.mY DualPush.gVY DualPush.mVY DualPush.gVY' DualPush.mVY'
  DualPush.gLb DualPush.mLb DualPush.gVLb DualPush.mVLb

namespace DualPush

variable {O A HT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    {pr : A →ₗ[O] HT' →ₗ[O] KO O} (Q : DualPush O A HT' pr)

def HfY : Submodule O Q.HY := Q.HfVY.comap Q.jY

end DualPush

def StatLocTorsDual : Prop :=
  ∀ (O A H : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (S : Submodule O A) (a : O),
    (∀ s ∈ S, a • s ∈ annih pr M) →
    Module.length O (S ⧸ (annih pr M).comap S.subtype) ≤
      Module.length O (M ⧸ mulSub a M)

def StatLocQuotLen : Prop :=
  ∀ (O M : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] M), Submodule.torsion O M ≤ LinearMap.range δ →
    ∀ ℓ e : ℕ, Module.length O (M ⧸ mulSub ((ℓ : O) ^ e) M) ≤
      ((Module.finrank O M + d : ℕ) : ℕ∞) * ((e : ℕ∞) * eO O ℓ)

end Formalism.RepresentationBoundsCohomology.LOC
