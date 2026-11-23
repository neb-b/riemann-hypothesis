module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

variable {u : D.what₂.Word}

end GlobalTheory.LocMod.PinModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.StepData GlobalTheory.SymBridge
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod

section Gen
variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Gen

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) {d : Dat (I.rec7 l Z) u}
  {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) (I.rec7 l Z).host.E}

def baseFr (i : ℕ) (hi : i ≤ B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup I.mu0)) :
    Matrix (Fin ((I.rec7 l Z).sp.X i).rank) (Fin (B.R.N i)) (I.rec7 l Z).host.E := fun r a =>
  Formalism.L2.Col.frsF I.sel (I.tup I.mu0) (A.p0 i).1.1 P (Pi.single a 1) (finCongr (rankN (I.rec7 l Z) i hi) r)

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdEx' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ), IsStdChar (I.rec7 l Z) ψ (-1) →
    ∀ L : ∀ j, Lat ((I.rec7 l Z).sp.X j), (∀ j, j ≤ B.R.m → ∀ z, z ∈ L j ↔ z ∈ intVec (I.rec7 l Z) _) →
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
      (p : ι → SplitPt (I.rec7 l Z) k) (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle)
      (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
      (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
      Places p J (fun x => ∃ i, x = (p i).v) ∧ (∀ i, HasConductor (χ i) 1 ∧ (p i).IsChar ψ (χ i)) ∧ resCard k = B.T u ∧
      (∀ i, valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (X.piT u : B.fields.E)))) =
          valuation k ((q.1 : 𝒪[k]) : k) ∧
        valuation k ((p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E)))) = 1) ∧
      (∀ x : Pl (I.rec7 l Z), (∃ i, x = (p i).v) ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal) ∧
      (∀ j i, (β j i).b = 1) ∧ StdT I l Z u p β Q L

def TwLev' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ j, j ≤ B.R.m → ∀ b,
      (∀ i g, g • Q j i = Q j i → ∃ h : (β j i).gl g ∈ A.U j b, A.chi j b ⟨_, h⟩ = 1) ∧
      ∀ κ ∈ A.U j b, ∃ g : ι → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ i, g i • Q j i = Q j i) ∧
        ∃ κ' ∈ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β j i).gl (g i)).prod * κ'

def TwRam' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y)) ∧ (RamT (I := I) (l := l) (u := u) (a := a) j φ ↔ ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y))

def TwTrans' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∃ φ' ∈ (I.fm l u a).Fi j, ∀ b y, A.rd θ j hj b φ' y = trc c (A.rd θ j hj b φ y)

def TwS' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) k) (β : ∀ j i, Frame (p i) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j) (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j).rank)) (L : ∀ j, Lat ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X j)),
    StdT I l Z u p β Q L → ∀ (J : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1),
    ∃ S : ∀ j, (ι → 𝓀[k]ˣ) → ColT I l u a j → ColT I l u a j, ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ →
      (∀ b y, IsContAut _ (A.rd θ j hj b φ y) ∧ ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y)) ∧
      ∀ η, RamT (I := I) (l := l) (u := u) (a := a) j (S j η φ) ∧ ∀ b y, A.rd θ j hj b (S j η φ) y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y)

def TwVec' : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ ψ θ x vac c₀, PinX I l Z ψ θ x vac c₀ →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)),
    StdT I l Z u p β Q (fun j => (x j).L) → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) α γ (cT : WO _ _ →₀ ℂ),
      Reps ψ (β j) (β (j + 1)) (x j).L (x (j + 1)).L (fun i => phiOne (Q j i) (Q (j + 1) i)) J (fun v => ∃ i, v = (p i).v) cT →
      ∀ e : AE (I.rec7 l Z), IsIdemSum e ((B.primes X).vT u) →
        IsRatDatum ψ _ _ e (fun z => B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z))) (vac j)
          (comb ψ _ _ cT (vac j))

end GlobalTheory.AdForm

end
end

