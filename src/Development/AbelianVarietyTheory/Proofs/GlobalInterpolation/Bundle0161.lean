module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPerTw
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuples
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace GlobalTheory.PerRedU

theorem perTwAt_of_perDecTw {D : D7} {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (h : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
          y = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ) := by
  intro x hx F hF _
  obtain ⟨pc, hs, hi⟩ := h
  choose y hy hv using hi x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, fun w hw => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hs, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, map_inv₀, map_natCast, hy c]
  · refine Finset.sum_induction _ (fun t => t = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) t : ℝ))
      (fun a b ha hb => Formalism.MainNotions.WeightDegreeSizes.pair_add_ge D w ha hb) (Or.inl rfl) fun c _ => ?_
    rcases hv c w hw with h0 | h0
    · left; rw [h0, mul_zero]
    by_cases hy0 : y c = 0
    · left; rw [hy0, mul_zero]
    right
    have hn0 : ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Formalism.MainNotions.OrbitPlaces.vAdd_mul w (inv_ne_zero hn0) hy0, Formalism.MainNotions.OrbitPlaces.vAdd_inv w hn0]
    have hb := Formalism.MainNotions.DIV.HookProducts.AdmPerTw.vAdd_dvd_le (D := D) w (D.mem u).C.DGam_pos.ne'
      (Formalism.MainNotions.DIV.HookProducts.AdmPerTw.card_stabilizer_dvd₂ hD T u μ c)
    have h0' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast h0
    unfold Formalism.MainNotions.WeilJacquetShalikaLaw.vDG
    push_cast
    linarith

theorem exists_muAt_of_usedT {D : D7} {μ : D.what₂.Tup} (hU : Formalism.MainNotions.LocalQuadraticParts.UsedT D μ) (hμ : μ ≠ D.what₂.mu0) :
    ∃ w, μ = D.what₂.muAt w :=
  hU.resolve_left hμ

theorem admissiblePeriodTwists_of_periodDecompositions {D : D7} {Dx : DivX D} {T : TwForms D}
    (h : ∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun hD u μ hU hμ => perTwAt_of_perDecTw hD (h u μ hμ (exists_muAt_of_usedT hU hμ))

theorem main : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun _ _ _ h => admissiblePeriodTwists_of_periodDecompositions h

end GlobalTheory.PerRedU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClosingTrueCols
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LvT.Built.TrueCols

theorem closing_true_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ColIn.JetsIn I → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT Y (I.tw l l0 Z) u := by
  intro B X I hOk hJ hS l Z l0 Y u
  exact _root_.GlobalTheory.LvT.Built.TrueCols.row_true B X I hOk hJ hS l l0 Z Y u
end GlobalTheory.LvT.Built.TrueCols
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LowerTwistedCompatibleOfEvaluationBranching
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PerQ

theorem lowerTieTwAt_to_lib : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup),
    GlobalTheory.PerQ.LowerTieTwAt D T u μ → Formalism.MainNotions.DIV.HookProducts.AdmPtTw.LowerTieTwAt D T u μ := by
  rintro D T u μ ⟨a, b, P, hP⟩
  exact ⟨a, b, ⟨P.br, P.coM, P.coP, P.Pt_eq, P.lat_co, P.pt_co⟩, hP⟩

end GlobalTheory.PerQ
end

