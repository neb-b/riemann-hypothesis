module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicReadingLastStepTrivialOffLevel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal


open Classical in
theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := _root_.GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => _root_.GlobalTheory.PhiOneVal.maps_rd_iff_colCond (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelComponentFixesStandardPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.AdForm.CompFix.intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s) ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 :=
          mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.AdForm.comp_fixes_stdPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b κ hκ i g hg

  let e := Classical.choose hS.1
  have he := Classical.choose_spec hS.1
  obtain ⟨hpi, hT⟩ := _root_.GlobalTheory.AdForm.piT_mem_and_T_mem_place I hOk l Z u k (p i) (e i) (he i)
  have key : ∀ κ₀ ∈ A.U j b, ∀ r s : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank,
      ((mt _ κ₀).map (p i).pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank →
        valuation k (((mt _ κ₀).map (p i).pr) r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s) < 1) := by
    intro κ₀ hκ₀ r s
    have hn := rankN (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) j hj
    have h3 := GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice I hOk hPins l Z u a Ch A hA j hj b κ₀ hκ₀ (p i).v hT (Fin.cast hn s)
    let y : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) → AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) := fun r' =>
      mt _ κ₀ (Fin.cast hn.symm r') s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) (Fin.cast hn.symm r') s
    have hy : (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (toEAf (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (y r'))) =
        (fun r' => Formalism.UG.prV (E := (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) (p i).v (GlobalTheory.AdForm.finM _ hn κ₀ r' (Fin.cast hn s)) -
          (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j)) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F] (p i).v.adicCompletion (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.F)) r' (Fin.cast hn s)) := by
      funext r'
      simp only [y]
      rw [RingHom.map_sub, RingHom.map_sub]
      congr 1
      by_cases h : r' = Fin.cast hn s
      · subst h
        have : Fin.cast hn.symm (Fin.cast hn s) = s := Fin.ext rfl
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
      · have h' : Fin.cast hn.symm r' ≠ s := fun h2 => h (Fin.ext (by rw [← h2]; rfl))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
    have hLb : ∀ x, x ∈ (A.K j hj b).lev.Lb ↔ ∀ j' : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j), ∃ r : 𝓞 (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E, x j' = (r : (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).host.E) ∧ (j'.1 + 1 = (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j → X.piT u ∣ r) :=
      fun x => (hA.reads j hj).lb b x
    rw [← hy] at h3
    have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) (e i).1 (he i) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).R.N j) (X.piT u) hpi (A.K j hj b).lev.Lb hLb y h3 (Fin.cast hn r)
    have hyr : y (Fin.cast hn r) = mt _ κ₀ r s - (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s := rfl
    rw [hyr] at h4
    have h1 : (p i).pr ((1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (AE (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G))) r s) =
        (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [map_sub, h1] at h4
    refine ⟨?_, fun hr => ?_⟩
    · have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) (Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank) k) r s ∈ 𝒪[k] by
        simp only [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      rwa [sub_add_cancel] at this
    · exact h4.2 (by rw [Fin.coe_cast, ← hn]; exact hr)

  set M := (mt _ κ).map (p i).pr with hMdef
  set M' := (mt _ κ⁻¹).map (p i).pr with hM'def
  have hmt : ∀ x y : GA (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j), mt _ (x * y) = mt _ x * mt _ y := fun x y => by
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, mul_inv_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, inv_mul_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM := _root_.GlobalTheory.AdForm.OffPlace.map_pr_of_off (_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) k (p i) _ _ (β j i) κ g hg
  rw [← hMdef] at hM
  rcases Nat.eq_zero_or_pos ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank with h0 | hpos
  · have : g = 1 := by
      apply Units.ext
      apply Matrix.ext
      intro a b
      have ha : a.val < ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := a.isLt
      omega
    rw [this, one_smul]
  let r₀ : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := ⟨((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank := by simp only [r₀]; omega
  have hK := GlobalTheory.AdForm.CompFix.intMat_keeps M M' hMM (fun r s => (key κ hκ r s).1) (fun r s => (key κ⁻¹ (inv_mem hκ) r s).1) r₀
    (fun s => (key κ⁻¹ (inv_mem hκ) r₀ s).2 hr₀)

  have hbg : ∀ x : Fin ((_root_.GlobalTheory.Mem.assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G).sp.X j).rank → k, (β j i).b *ᵥ (g⁻¹ • x) = M' *ᵥ ((β j i).b *ᵥ x) := by
    intro x
    have e1 : (β j i).b * g.val = M * (β j i).b := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, (β j i).b'b, Matrix.mul_one]
    have e2 : (β j i).b *ᵥ x = M *ᵥ ((β j i).b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine Pair.ext fun x a' => ?_
  rw [Pair.smul_hasVal, _root_.GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hS j hj i r₀ hr₀, _root_.GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hS j hj i r₀ hr₀, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK ((β j i).b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitIntComp

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

theorem eq_sec_add_csec (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a = q.sec (q.pr a) + cA D (q.sec (q.pr (cA D a))) := by
  have h := (idem_iff q a).1 ha
  rw [q.sec_pr, q.sec_pr, map_mul, cA_cA]
  conv_lhs => rw [← h]
  ring

theorem mem_intAt_iff (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) :
    a ∈ intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨(q.int_iff _).2 ?_, (q.int_iff _).2 ?_⟩
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 h.2
    · rw [q.sec_pr, RingHom.map_mul]; exact mul_mem_intAE (e_mem_intAt q).2 ((cA_int_iff a).2 h.2)
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    rw [eq_sec_add_csec q ha, RingHom.map_add (f := _)]
    exact add_mem ((q.int_iff _).1 h1) ((cA_int_iff _).2 ((q.int_iff _).1 h2))

theorem val_xi (q : SplitPt D k) (h : q.UnitAA) : valuation k ((ofSplit q).xi) = 1 := by
  have he := e_mem_intAt q
  have hpe : q.pr q.e = 1 := by rw [← sec_one q, q.pr_sec]
  have h1 := ((mem_intAt_iff q (h.1 q.e he).1.1).1 (h.1 q.e he).1).1
  have h2 := ((mem_intAt_iff q (h.1 q.e he).2.1).1 (h.1 q.e he).2).1
  rw [map_mul, hpe, mul_one] at h1 h2
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hprod : q.pr (incA D D.host.xi0⁻¹) * q.pr (incA D D.host.xi0) = 1 := by
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one]
  change valuation k (q.pr (incA D D.host.xi0)) = 1
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 := congrArg (valuation k) hprod
  rw [map_mul, map_one] at v3
  refine le_antisymm v1 ?_
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos v2 hlt zero_le' zero_lt_one
  rw [v3, mul_one] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitIntComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicReadingLastStepTrivialOffLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicReading_lastStep_trivial_off_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → Nonempty (Unique (Ch B.R.m)) → ∃ A' : TwDat I l Z u a Ch, A'.Is ∧ (∀ i, i < B.R.m → ∀ β, A'.kb i β = A.kb i β) ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A'.kb B.R.m β) = 1 := by
  first | exact @GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial | exact GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial | (intros; apply GlobalTheory.AdForm.TopMove.exists_twDat_top_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomothetiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_central_glue_localHomotheties : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  first | exact @GlobalTheory.Core.Mi.LatGlue.glue | exact GlobalTheory.Core.Mi.LatGlue.glue | (intros; apply GlobalTheory.Core.Mi.LatGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeMemPl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.AdForm.exists_readsG_of_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K eW hR heW hb hL f

  have hv : ∀ c : (I.stX a).Cl, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
      f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
    intro c
    obtain ⟨h₀, hh₀⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := I.rec7 l Z) (K.y c)
    obtain ⟨w, hw, e⟩ := _root_.GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ I l Z u a R.MX j hj ((LinearMap.proj (h₀ * g.bT)).comp f.1)
    refine ⟨w, hw, fun v h hh => ?_⟩
    rw [GlobalTheory.Core.Rk.Top.Model.hasMat_pt hh hh₀]
    exact e v
  choose w hw hwv using hv
  obtain ⟨G', hG'⟩ := _root_.GlobalTheory.Mem.Col2.PerIn.exists_Mt_of_rep_values (I.perIn u a) B.fields.emb B.embLL (fun _ => rfl) w hw
    (fun c s => GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character I hI hP l Z u R g c₀ hX j hj P t a bad K hR hb hL f c (w c) (hw c) (hwv c) s)
  refine ⟨G', fun c v h hh => ?_⟩
  rw [hwv c v h hh]
  have hz : ∀ c', eW.symm (Pi.single c (j v)) c' = (Pi.single c (j v) : (I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) c' := by
    intro c'
    funext y'
    have := heW (eW.symm (Pi.single c (j v))) c' y' y' rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  generalize eW.symm (Pi.single c (j v)) = z at hz
  have hzc : z c = j v := by rw [hz c, Pi.single_eq_same]
  have hzo : ∀ c', c' ≠ c → z c' = 0 := fun c' h => by
    rw [hz c']
    exact Pi.single_eq_of_ne h _
  haveI := (l.per u a).step.fin_stab c.1 ((I.perIn u a).S'.rep c)
  have hne : ((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := (I.perIn u a).clFin (l.per u a)
  show _ = _ * (∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' • (Formalism.L2.DIV.pairB (K := ℂ) (I.perIn u a).sgT).compl₁₂
      (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ LinearMap.proj c')
      (LinearMap.proj c' ∘ₗ (I.perIn u a).rd B.fields.emb B.embLL)) z G'
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  erw [Fintype.sum_eq_single c (fun c' hc' => by
    change (I.perIn u a).wt c' * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c')) _ = 0
    rw [hzo c' hc']
    simp only [map_zero, LinearMap.zero_apply, mul_zero])]
  change _ = _ * ((((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ)⁻¹) * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c)) (G'.1 c.1 ((I.perIn u a).S'.rep c)))
  rw [hzc, hG' c, ← mul_assoc]
  erw [mul_inv_cancel₀ hne, one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMoves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedLat

theorem movedLat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P := by
  intro D L hT Gi Gl Kc Yd cX ex W _ j hj g
  obtain ⟨c, hc⟩ := W.Q.charW.base.lev.βY j hj
  have hsd : IsSelfDualC (Yc D j) ((pk W).ΛY j) := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩
  exact (_root_.GlobalTheory.FinPl.GlobImage.glob D (Yc D j) _ hsd).1 g

end GlobalTheory.MovedLat
end

