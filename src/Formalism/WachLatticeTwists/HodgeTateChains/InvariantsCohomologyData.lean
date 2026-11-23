module

public import Formalism.WachLatticeTwists.HodgeTateChains.Statement

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

abbrev Md (ℓ : ℕ) [Fact ℓ.Prime] := ModuleCat.{0} ℤ_[ℓ]

structure Piece (ℓ : ℕ) [Fact ℓ.Prime] (A : Md ℓ) where

  E : Md ℓ

  HH : Md ℓ

  Wm : Md ℓ

  WX : Md ℓ

  gm : Wm →ₗ[ℤ_[ℓ]] Wm

  gX : WX →ₗ[ℤ_[ℓ]] WX

  lam : A →ₗ[ℤ_[ℓ]] E

  io : E →ₗ[ℤ_[ℓ]] A

  infm : Wm →ₗ[ℤ_[ℓ]] E

  infX : WX →ₗ[ℤ_[ℓ]] E

  res : E →ₗ[ℤ_[ℓ]] HH

namespace Piece

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Md ℓ} (P : Piece ℓ A)

def Sandwich : Prop := ∀ x, P.io (P.lam x) = (ℓ : ℤ_[ℓ]) • x

def InfRes : Prop :=
  (∀ y, P.res y = 0 ↔ ∃ w x, y = P.infm w + P.infX x) ∧
  ∀ w x, P.infm w + P.infX x = 0 ↔ (∃ w', w = P.gm w' - w') ∧ ∃ x', x = P.gX x' - x'

def T4 : Prop := ∀ y : P.HH, (ℓ : ℤ_[ℓ]) • y = 0

def T3 : Prop := (∀ x, P.gX x = x → x = 0) ∧ ∀ x, ∃ y, (ℓ : ℤ_[ℓ]) • x = P.gX y - y

def HodgeTate (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Prop :=
  (∀ x : P.Wm, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) ∧ aeval P.gm (HTpoly ℓ w U i) = 0

def Inputs (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Prop :=
  P.Sandwich ∧ P.InfRes ∧ P.T4 ∧ P.T3 ∧ P.HodgeTate w U i

end Piece

def StatPiece : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ) (A : Md ℓ) (P : Piece ℓ A), P.Inputs w U i →
      TorsKilled ℓ A (2 + max 1 (rI ℓ m U i))

structure LLData (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where

  HK : Md ℓ

  Hm : ℕ → Md ℓ

  Gr : ℕ → Md ℓ

  piece : ∀ k, Piece ℓ (Gr k)

  f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] Hm (k + 1)

  p : ∀ k, Hm (k + 1) →ₗ[ℤ_[ℓ]] Hm k

  res : HK →ₗ[ℤ_[ℓ]] Hm n

  cor : Hm n →ₗ[ℤ_[ℓ]] HK

namespace LLData

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (D : LLData ℓ n)

def LES : Prop := (∀ x : D.Hm 0, x = 0) ∧ ∀ k, Function.Exact (D.f k) (D.p k)

end LLData

structure InvariantsCohomologyData (ℓ : ℕ) [Fact ℓ.Prime] where

  M : Md ℓ

  A : Md ℓ

  piece : Piece ℓ A

  H0WeightInvariants : Md ℓ

  jm : H0WeightInvariants →ₗ[ℤ_[ℓ]] piece.Wm

  jX : H0WeightInvariants →ₗ[ℤ_[ℓ]] piece.WX

  invariantsModPower : ℕ → Md ℓ

  red : ∀ r, H0WeightInvariants →ₗ[ℤ_[ℓ]] invariantsModPower r

  dl : ∀ r, invariantsModPower r →ₗ[ℤ_[ℓ]] A

  emb : ∀ r, Submodule.torsionBy ℤ_[ℓ] M ((ℓ : ℤ_[ℓ]) ^ r) →ₗ[ℤ_[ℓ]] invariantsModPower r

namespace InvariantsCohomologyData

variable {ℓ : ℕ} [Fact ℓ.Prime] (D : InvariantsCohomologyData ℓ)

def Union : Prop := ∀ x : D.M, ∃ r : ℕ, ((ℓ : ℤ_[ℓ]) ^ r) • x = 0

def Flat : Prop := ∀ r, Function.Injective (D.emb r)

def LES : Prop := ∀ r, Function.Exact (D.red r) (D.dl r)

def Inv : Prop :=
  (∀ x, D.jm x = 0 → D.jX x = 0 → x = 0) ∧
  ∀ x, D.piece.gm (D.jm x) = D.jm x ∧ D.piece.gX (D.jX x) = D.jX x

end InvariantsCohomologyData

def InvariantsKilledByPower : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ), 0 ∉ U → U.Nonempty → ∀ D : InvariantsCohomologyData ℓ,
    D.piece.Inputs w U 0 → D.Union → D.Flat → D.LES → D.Inv →
      ∀ x : D.M, ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x = 0

structure TBData (ℓ : ℕ) [Fact ℓ.Prime] where

  HY : Md ℓ

  HYL : Md ℓ

  Hr : Md ℓ

  HrL : Md ℓ

  Zr : Md ℓ

  ZrL : Md ℓ

  HW : Md ℓ

  HWL : Md ℓ

  secondCohomologyTwist : Md ℓ

  HV : Md ℓ

  HB : Md ℓ

  HA : Md ℓ

  HGe : Md ℓ

  HWe : Md ℓ

  HAK : Md ℓ
  iY : HY →ₗ[ℤ_[ℓ]] HYL
  f1 : HY →ₗ[ℤ_[ℓ]] Hr
  fL : HYL →ₗ[ℤ_[ℓ]] HrL
  ir : Hr →ₗ[ℤ_[ℓ]] HrL
  q : Zr →ₗ[ℤ_[ℓ]] Hr
  bd : Hr →ₗ[ℤ_[ℓ]] secondCohomologyTwist
  iZ : Zr →ₗ[ℤ_[ℓ]] ZrL
  qL : ZrL →ₗ[ℤ_[ℓ]] HrL
  kL : HWL →ₗ[ℤ_[ℓ]] ZrL
  jZ : Zr →ₗ[ℤ_[ℓ]] HV

  ex : HV →ₗ[ℤ_[ℓ]] HB
  bZ : ZrL →ₗ[ℤ_[ℓ]] HB
  bW : HWL →ₗ[ℤ_[ℓ]] HB
  jW : HW →ₗ[ℤ_[ℓ]] HV
  pr : HV →ₗ[ℤ_[ℓ]] HA
  aR : Hr →ₗ[ℤ_[ℓ]] HA
  gE : HGe →ₗ[ℤ_[ℓ]] HWL
  pE : HWL →ₗ[ℤ_[ℓ]] HWe

  La0 : Submodule ℤ_[ℓ] HB
  res : HAK →ₗ[ℤ_[ℓ]] HA
  cor : HA →ₗ[ℤ_[ℓ]] HAK

  HfK : Submodule ℤ_[ℓ] HAK

  y : HY

  yK : HAK

namespace TBData

variable {ℓ : ℕ} [Fact ℓ.Prime] (D : TBData ℓ)

def LES : Prop :=
  Function.Exact D.q D.bd ∧ Function.Exact D.kL D.qL ∧ Function.Exact D.gE D.pE

end TBData

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
