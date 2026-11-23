module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.Top.Model
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Check

variable {D : D7}

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

variable {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
  (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X')

theorem ReadsG.period_eq {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} (h : ReadsG K eW j x G f) (h' : ReadsG K eW j x G' f)
    (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) : Pm.period w G = Pm.period w G' := by
  choose v hv using hw
  have e : w = ∑ c, eW.symm (Pi.single c (j (v c))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, LinearEquiv.eq_symm_apply]
    simp only [hv]
    exact (Finset.univ_sum_single _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := hasMat_exists (K.y c)
  have hc : (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M.stabilizer₂ c)).ne'
  exact mul_left_cancel₀ hc ((h c _ g hg).symm.trans (h' c _ g hg))

end Read

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {P : LevelP R.Pg D.R.r ℂ} {u : D.what₂.Word} {g : Geo D}

theorem colCh_nonempty (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : ∃ k : ColCh u C, ∀ j, Nonempty (k.Ch j) :=
  by
    let k : ColCh u C :=
      { kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => Finsupp.single 1 1, eT := fun _ _ _ => Finsupp.single 1 1,
        Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }
    exact ⟨k, fun _ => ⟨()⟩⟩

end Package

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

end Real

end GlobalTheory.Fam.Check

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealOf
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

def JetS (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (s : ℕ → ℂ) : Prop :=
  ∀ j (hj : j + 1 ≤ B.R.m), s j ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
    pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
      jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) (s j) (ColDat.xiS θ j hj f) P

def lowOf : (FrN (I.rec7 l Z) (B.R.N B.R.m) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :=
  fnOf _ (shiftOf (sgT (D := I.rec7 l Z) u)) 1 ∘ₗ (I.perIn u I.mu0).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    Formalism.L2.Col.polOf _ (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩

variable {I l Z} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))

@[reducible] def realOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : RealD (commOf R u g) where
  N := B.R.N
  hN := rankN (I.rec7 l Z)
  NT := B.R.N B.R.m - 1
  hT := rankP (I.rec7 l Z)
  fr := fun _ => ⟨fun y => ⟨y.1, y.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  lam := Formalism.L2.Forms.lamT (D := I.rec7 l Z) u
  n := fun j τ => (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ + (I.chain l u I.mu0).sSharp j τ).toNat
  sS := (I.chain l u I.mu0).sSharp
  sD := (I.chain l u I.mu0).sDiv
  sc := fun j τ => if s j = 0 then 1 else s j / I.J.cD τ
  BT := fun _ => 1
  sg := sgT (D := I.rec7 l Z) u
  J := J
  low := fun _ h => Eq.rec (motive := fun n _ => (FrN (I.rec7 l Z) (B.R.N n) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ))
    (lowOf I l Z u) h.symm

def JOf (j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ))
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : Prop :=
  ∀ v, ∀ k ∈ GinfC (I.rec7 l Z).sp.X', ∀ z z' : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
    IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' → J v k z' = j v ⟨z.1, z.2⟩

variable (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) {a : I.ι} (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

end GlobalTheory.AdForm
end
end

