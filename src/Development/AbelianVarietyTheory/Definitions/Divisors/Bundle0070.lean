module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotLeafMMZero
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF)

theorem N_eq : d.O.N = GlobalTheory.ChiGrid.bigN D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  have : D.R.r + 6 = D.R.k + D.R.m + 5 := by unfold Ranks.r; omega
  rw [this]

theorem nr_eq : d.O.nr = GlobalTheory.ChiGrid.nRk D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m = D.R.r + 1
  unfold Ranks.r; omega

theorem s_eq : d.O.s = GlobalTheory.ChiGrid.sLen D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m + 5 = D.R.r + 6
  unfold Ranks.r; omega

theorem PPF_eq (C b : ℝ) : d.O.PPF C b = GlobalTheory.ChiGrid.sizeP D C b := by
  unfold FunData.PPF GlobalTheory.ChiGrid.sizeP
  rw [nr_eq]; rfl

theorem Lc_eq : d.O.Lc = GlobalTheory.ChiGrid.cloudLen D := by
  classical
  have h : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  unfold FunData.Lc GlobalTheory.ChiGrid.cloudLen
  refine le_antisymm (Finset.sup_le fun τ hτ => ?_) (Finset.sup_le fun τ _ => ?_)
  · have hτ' : τ < Fintype.card D.what₂.Tau := h ▸ Finset.mem_range.1 hτ
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ =>
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat)
      (Finset.mem_univ ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, hτ'⟩)))
    show (cloud D τ 2 - cloud D τ D.R.k).toNat = _
    simp only [cloud, dif_pos hτ']
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ => (d.O.cl τ 2 - d.O.cl τ d.O.k).toNat)
      (Finset.mem_range.2 (show ((Fintype.equivFin D.what₂.Tau τ : Fin _) : ℕ) < D.R.f from h ▸ (Fintype.equivFin D.what₂.Tau τ).2)))
    show _ = (cloud D _ 2 - cloud D _ D.R.k).toNat
    simp only [cloud, dif_pos (Fintype.equivFin D.what₂.Tau τ).2, Fin.eta, Equiv.symm_apply_apply]

theorem ga_eq (C : ℝ) : d.O.ga C = GlobalTheory.ChiGrid.gap D C := by
  unfold FunData.ga GlobalTheory.ChiGrid.gap
  rw [N_eq, nr_eq, s_eq, Lc_eq d]; rfl

theorem ee_eq (h : Ideal.absNorm d.G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    d.O.ee CF p.Z.b v = d.G.pl.depth ⟨1, CF, p.Z.b⟩ v := by
  unfold FunData.ee GlobalTheory.ChiGrid.Places.depth GlobalTheory.ChiGrid.depth0
  rw [PPF_eq]
  have e : d.O.qq d.O.sv0 = GlobalTheory.ChiGrid.q0 D := h
  rw [e]
  by_cases hv : v = d.G.pl.v0
  · rw [if_pos hv]; exact if_pos hv
  · rw [if_neg hv]; exact if_neg hv

end GlobalTheory.BigTop.Fun.Model

namespace GlobalTheory.BigTop.Fun.FieldProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun.FieldProbe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.TestLat

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Numbers

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
  {K K' : Type} [Field K] [Field K']

def BottomsWith (Q : ℂ → Prop) : Prop :=
  ∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
    IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ Q (P.norm : ℂ) ∧ Q (P'.norm : ℂ)

structure SqIn (σ : K →+* ℂ) : Prop where

  norms : BottomsWith G μ₀ (fun _ => True) → BottomsWith G μ₀ fun z => z ∈ Set.range σ

  toric : ∀ (i j : Fin D.R.m) (s : ℕ) (c : Bool) (x y : ℂ), 1 ≤ s → s ≤ halfRank D i j → IsTor G i j s (nuH G μ₀ i j) x →
    IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y → y / x ∈ Set.range σ

variable {G μ₀}

theorem SqIn.mono {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : SqIn G μ₀ σ) (hσ : Set.range σ ⊆ Set.range σ') : SqIn G μ₀ σ' :=
  ⟨fun a => let ⟨δ, t0, b⟩ := h.norms a
    ⟨δ, t0, fun ij => let ⟨P, P', c⟩ := b ij; ⟨P, P', c.1, hσ c.2.1, hσ c.2.2⟩⟩,
    fun i j s c x y a b d e => hσ (h.toric i j s c x y a b d e)⟩

end Numbers

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure SlopeTestRemainingChoices (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) (W : G.Weil) (n : ℕ) where

  M : Vol G

  ρ : G.RealVec

  ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W

  cv : ChainVec p.R.toRealDat

  rm : RealMatch W

  S : SumChoice W Set.univ

  rp : ClassReps G

  e : Fin n ≃ TestIx G × VVIdx (LaP G)

  c : Fin D.R.m → Fin D.R.m → p.P.T → ℂ

def SlopeTestRemainingChoices.ch {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Choice p.R.toRealDat :=
  ⟨⟨1, CF, p.Z.b⟩, G, W, a.M, a.ρ, a.ξ, a.cv, a.rm, a.S, a.rp, n, a.e, a.c⟩

theorem SlopeTestRemainingChoices.atScale {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) :
    a.ch.AtScale CF p.Z.b := rfl

structure SlopeTestRemainingChoices.OK {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) : Prop where

  is : a.ch.Is

  eser : GlobalTheory.GLq.ESerTie D

  field : a.ch.FieldOK

  sq : SqIn G p.P.A3.A.μ0 D.what₂.embLL

def Fld : FldT := fun p _ G W => ∃ (n : ℕ) (a : SlopeTestRemainingChoices p G W n), a.OK

end GlobalTheory.BigTop.Fun

end
end

