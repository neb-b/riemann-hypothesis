module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FacWithCsNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Deep

variable (T : CoreJ D) (j : ℕ) {l : Level T.Q.H} (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l)
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)



variable {Q T j Xo c U dict}

end Deep

section Restrict

variable {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']


open Classical in
def restrictOr (φ : M →ₗ[K] M') (C : Submodule K M) (C' : Submodule K M') : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, φ x ∈ C' then φ.restrict h else 0

end Restrict

section Keeps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem mul_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspW Xo c U G)
    (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspW Xo c U (G + G') := by
  rw [mem_cuspW] at hf hg ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [show exZ Dw (G + G') = exZ Dw G + exZ Dw G' from funext fun i => exZ_add _ _ _]
    exact mul_mem_secZ hf.1 hg.1
  · rw [AllWt.rdU_mul, show modelWt (U σ) (G + G') = fun k => modelWt (U σ) G k + modelWt (U σ) G' k from
      funext (modelWt_add (U σ) hG hG')]
    exact holSub_mul siegelSpaceAlgebra_holds (hf.2 σ hσ) (hg.2 σ hσ)

theorem levPh_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) (hK : KeepsCusp U (G + G'))
    (hK' : KeepsCusp U G') {S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)} (χ : S →* (c.F)ˣ) {u f : Rul Xo c}
    (hu : u ∈ cuspW Xo c U G') (hf : f ∈ cuspW Xo c U G) (h : S) : levPh Xo c S χ u f h ∈ cuspW Xo c U (G + G') := by
  rw [levPh_apply, levTr_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hK _ _ (mul_mem_cuspW hG hG' hf (hK' _ _ hu)))


end Keeps


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure LiftData (T : CoreJ D) (i : Fin D.R.m) : Type 1 where

  l : Level T.Q.H
  typeLevel : IsTypeLevel l

  Xo : Moduli (T.Q.Dw ((i : ℕ) + 1)) l

  c : Coeff l

  U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r

  dict : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U σ).X k).Ψ D.R.r

  fr : TypeFrame (T.Q.Dw ((i : ℕ) + 1)) l

  ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) c.F

  om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (c.F)ˣ

  u₀ : cuspW Xo c U (gTw T.Q ((i : ℕ) + 1))

theorem inR_succ (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

namespace LiftData

variable {T : CoreJ D} {i : Fin D.R.m} (Y : LiftData T i)

abbrev Hb : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.l) := grpHR Y.fr

abbrev V (G : WTZ D.host.E) : Submodule Y.c.F (Rul Y.Xo Y.c) := cuspW Y.Xo Y.c Y.U G

def NN : Submodule (𝓞 Y.c.F) (Y.V (gKap T.Q ((i : ℕ) + 1))) := latN Y.fr Y.U _ Y.ψ

set_option synthInstance.maxHeartbeats 400000 in
def Ph : Y.V (gKapMinus T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] (Y.Hb → Y.V (gKap T.Q ((i : ℕ) + 1))) :=
  LinearMap.pi fun h => restrictOr (LinearMap.proj h ∘ₗ levPh Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) Y.u₀) _ _

def eGood : Y.V (gKap T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] Y.V (gKap T.Q ((i : ℕ) + 1)) :=
  restrictOr (goodOp Y.Xo Y.c Y.typeLevel Y.fr Y.om i) _ _

variable (h : T.Q.Pins) (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (he : IsIdempotentElem (goodIdemTw Y.om i))
include h hK he

end LiftData

variable {T : CoreJ D} (h : T.Q.Pins) {i : Fin D.R.m} (Y : LiftData T i) [StarRing Y.c.F] (CI C2 : ℝ)

def facOf : SlopeBoundLiftData Y.c.F (pageOf Q) :=
  facWith Q Y.U Y.dict h (inR_succ i) CI C2 (mixVals Y.Xo Y.c (bZero Q ((i : ℕ) + 1))) Y.Hb Y.NN Y.Ph Y.eGood
    (Nat.card (LevelGroup D.host))


open Classical in
def LiftData.ofCore (hT : LawsJ T) (i : Fin D.R.m) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) T.Q.c.F)
    (om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (T.Q.c.F)ˣ)
    (u₀ : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (gTw T.Q ((i : ℕ) + 1))) : LiftData T i where
  l := T.Q.l
  typeLevel := (isTypeLevel_of_pin hT.pins.2.1).1
  Xo := T.Q.Xo _
  c := T.Q.c
  U := T.U _
  dict σ g := if hσ : GoodEmb T.Q.c σ then T.dict _ σ (cast (congrArg (GA D) (hT.spaceW _ (inR_succ i) σ hσ)).symm g)
    else T.dict _ σ 1
  fr := ((isTypeLevel_of_pin hT.pins.2.1).1.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2).some
  ψ := ψ
  om := om
  u₀ := u₀

end GlobalTheory.SlopeRec
