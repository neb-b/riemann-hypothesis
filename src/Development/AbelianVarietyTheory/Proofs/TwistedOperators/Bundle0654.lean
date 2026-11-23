module

public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSmulMemHatLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def exInd {G : GlobalTheory.SplitFlip.Grid k} (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ := fun b =>
  match b with
  | .ex i j => (SetLike.coe (GlobalTheory.SplitFlip.matLat (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).tgt))
      (GlobalTheory.SplitFlip.stdLat k (Fin (G.rank (GlobalTheory.SplitFlip.Edge.ex i j).src))))).indicator 1
  | .theta i j => φ (.theta i j)

theorem isNatDatum_exInd {G : GlobalTheory.SplitFlip.Grid k} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {e : ℕ} {γ : List GlobalTheory.SplitFlip.Edge}
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ b)) : ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (exInd φ b) := by
  intro b hb
  cases b with
  | ex i j => exact GlobalTheory.SplitFlip.hasDepth_indicator hϖ e _
  | theta i j => exact hφ _ hb

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_exOne_eq_exInd {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (keep : Bool) (g : G.VertexGroup) (γ : List GlobalTheory.SplitFlip.Edge)
    (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exOne φ))) x 0 =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ γ (exInd φ))) x 0 := by
  unfold flatTensor
  congr 1
  funext v
  unfold flatIntegrand moved GlobalTheory.SplitFlip.Grid.pathAct GlobalTheory.SplitFlip.Grid.lines₂
  have key : (γ.map fun b => exOne φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod =
      (γ.map fun b => exInd φ b (G.moveArgs .one g (fill hs x 0 v) b)).prod := by
    refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
    cases b with
    | theta i j => rfl
    | ex i j =>
      have h0 : G.moveArgs .one g (fill hs x 0 v) (.ex i j) = 0 := by
        have : fill hs x 0 v (.ex i j) = 0 := by
          unfold fill
          dsimp only
          split_ifs <;> ext <;> simp
        simp [GlobalTheory.SplitFlip.Grid.moveArgs, this]
      rw [h0]
      simp [exOne, exInd, Set.indicator_of_mem (Submodule.zero_mem _)]
  rw [key]

end Local

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ j, AddCommGroup (A j)]


open Classical in
theorem sum_reps_mul_indicator_eq_self (SA BA : ∀ j, A j → Prop) (hSA : ∀ j a b, SA j a → SA j b → SA j (a - b)) (R : ∀ j, Finset (A j))
    (hR2 : ∀ j x, BA j x → ∃ r ∈ R j, SA j (x - r)) (hR3 : ∀ j, ∀ r ∈ R j, ∀ r' ∈ R j, SA j (r - r') → r = r')
    (F : (∀ j, A j) → ℂ) (hper : ∀ x a, (∀ j, SA j (a j)) → F (x + a) = F x) (x : ∀ j, A j)
    (hsupp : F x ≠ 0 → ∀ j, BA j (x j)) :
    ∑ q : (∀ j, R j), F (fun j => (q j).1) * ∏ j, (if SA j (x j - (q j).1) then (1 : ℂ) else 0) = F x := by
  by_cases hex : ∃ q : (∀ j, R j), ∀ j, SA j (x j - (q j).1)
  · obtain ⟨q₀, hx⟩ := hex
    rw [Finset.sum_eq_single q₀]
    · rw [Finset.prod_eq_one fun j _ => if_pos (hx j), mul_one]
      have h := hper (fun j => (q₀ j).1) (x - fun j => (q₀ j).1) hx
      rw [add_sub_cancel] at h
      exact h.symm
    · intro q _ hne
      by_contra hz
      apply hne
      have h1 : ∀ j, SA j (x j - (q j).1) := fun j => by
        by_contra h0
        apply hz
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring
      refine funext fun j => Subtype.ext ?_
      have := hSA j _ _ (hx j) (h1 j)
      rw [sub_sub_sub_cancel_left] at this
      exact hR3 j _ (q j).2 _ (q₀ j).2 this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hne
      apply hex
      have sx := hsupp hne
      choose r hr hrs using fun j => hR2 j (x j) (sx j)
      exact ⟨fun j => ⟨r j, hr j⟩, hrs⟩
    · intro q _
      by_contra hz
      apply hex
      refine ⟨q, fun j => ?_⟩
      by_contra h0
      apply hz
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg h0)]; ring

end Abstract


set_option maxHeartbeats 1000000 in
theorem colFlat_expansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (eL : AE D), IsIdemSum eL {w.1} → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∃ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G), (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = eL ∧ IsCombOf ch.W (d i j) ((c i).1 j)) ∧ ∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf eL (y j)) → ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 y) 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t β w eL heL φ hφ
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w.1 w.2
  have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
  haveI := (isUnitVol_unitVol w.1).1
  have hT := (locGrid ch.G t w.1).isTensor_pureTensor (unifAt w.1) (depthAt ch.G w.1)
    (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ) (isNatDatum_exInd (isUnif_unifAt w.1) φ hφ)
  obtain ⟨N, hF⟩ := exists_isSBArgs_flat (locGrid ch.G t w.1) one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (unifAt w.1)
    (depthAt ch.G w.1) _ (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) hm h00.unif h00.cond hT
  set Fl := flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1)
    ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (exInd φ))) with hFl
  choose Rp hR1 hR2 hR3 using fun j : Fin D.R.m => _root_.GlobalTheory.FunObj.exists_finset_cosetReps (ch.S.βp (j + 1)) (ch.S.βp j) {w.1} eL N heL
  have sdT : ∀ j, j ≤ D.R.m → IsSelfDualC (ch.G.V (.top j)) (ch.G.Λ (.top j)) := fun j hj =>
    (ch.G.isV (X := .top j) hj fun _ h => by cases h).sd
  let d : (∀ j : Fin D.R.m, Rp j) → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j) := fun κ j =>
    { FinDatum.ind ch.G t (.top t j) {w.1} (fun w' hw' => by
        rw [Finset.mem_singleton] at hw'
        subst hw'
        exact (Good.locPl_cases w.2).elim (fun h => .inl h.1) fun h => .inr ⟨_, h.2.2, rfl⟩) eL heL with
      fn := cosLoc {w.1} eL (ch.S.βp (j + 1)) (ch.S.βp j) (N : ℤ) (κ j).1
      sb := GlobalTheory.T.indicator_smallCoset_half_isSchwartzBruhat (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.S.βp j)
        (ch.S.βp (j + 1)) {w.1} eL N (κ j).1 (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT j j.2.le) | exact (sdT j j.2.le).1)
        (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ (sdT (j + 1) j.2) | exact (sdT (j + 1) j.2).1) (ch.S.βp_is j j.2.le)
        (ch.S.βp_is (j + 1) j.2) heL (hR1 j _ (κ j).2).1 }
  choose c₁ hc₁ using fun (κ : ∀ j : Fin D.R.m, Rp j) (j : Fin D.R.m) =>
    GlobalTheory.CombsExist.exists_isCombOf ch.W (p := .top t j) (sdT j j.2.le) (sdT (j + 1) j.2) (d κ j)
  refine ⟨∀ j : Fin D.R.m, Rp j, Finset.univ, fun κ => Fl (ch.S.colAt t w.1 fun j => (κ j).1) 0, d,
    fun κ => (fun j => if h : j < D.R.m then c₁ κ ⟨j, h⟩ else 0, fun _ => 0), ?_, ?_⟩
  · intro κ _ j
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [dite_eq_left j.2]
    exact hc₁ κ j
  · intro y hy
    refine Eq.trans ?_ (flatTensor_exOne_eq_exInd (G := locGrid ch.G t w.1) one_le_sLen _ _ _ _ _ φ _).symm
    have hper : ∀ (x a : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))),
        (∀ j : Fin D.R.m, IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) (a j)) →
        Fl (ch.S.colAt t w.1 (x + a)) 0 = Fl (ch.S.colAt t w.1 x) 0 := fun x a ha => by
      rw [colAt_add]
      have := hF.per (ch.S.colAt t w.1 x) 0 (ch.S.colAt t w.1 a) 0 (fun j hj r s => ?_) (fun i _ r s => by simp)
      · rwa [add_zero] at this
      · rw [colAt_eq _ t w.1 _ hj]
        have := ha ⟨j, hj⟩ w.1 (Finset.mem_singleton_self _) (Fin.cast (topRank_eq ch.G t w.1 hj) r)
          (Fin.cast (topRank_eq ch.G t w.1 hj.le) s)
        rw [zpow_natCast] at this
        exact this
    have hsupp : Fl (ch.S.colAt t w.1 y) 0 ≠ 0 → ∀ j : Fin D.R.m,
        IsHalf eL (y j) ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) (y j) := by
      intro hne j
      refine ⟨hy j, fun w' hw' r s => ?_⟩
      rw [Finset.mem_singleton] at hw'
      subst hw'
      have := (hF.supp _ _ hne).1 j j.2 (Fin.cast (topRank_eq ch.G t w.1 j.2).symm r)
        (Fin.cast (topRank_eq ch.G t w.1 j.2.le).symm s)
      rw [colAt_eq _ t w.1 y j.2] at this
      rw [_root_.zpow_neg, zpow_natCast]
      exact this
    have key := sum_reps_mul_indicator_eq_self (ι := Fin D.R.m) (A := fun j : Fin D.R.m => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
      (fun j a => IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (N : ℤ) a)
      (fun j a => IsHalf eL a ∧ IsSmall {w.1} (ch.S.βp ((j : ℕ) + 1)) (ch.S.βp j) (-(N : ℤ)) a)
      (fun _ _ _ h h' => h.sub h') Rp (fun j x h => hR2 j x h.1 h.2) hR3 (fun x => Fl (ch.S.colAt t w.1 x) 0)
      hper y hsupp
    refine (Finset.sum_congr rfl fun κ _ => ?_).trans key
    exact congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun j _ => cosLoc_eq_ite (hy j))

end GlobalTheory.LocAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)),
    (∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y))) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.CosDual.cosDual | exact GlobalTheory.CosDual.cosDual | (intros; apply GlobalTheory.CosDual.cosDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeFirstRowEqDoubleAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.LatticeBidual

theorem latRow_bidual : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u → (∀ u' : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (fun _ => True) u' → (∀ v ∈ latRow G i, W.ψ (symplO _ _ v u') = 1) → W.ψ (symplO _ _ u u') = 1) → u ∈ latRow G i := by
  intro D hq T L μ0 hL sc G W M hM i hi u hu H
  have sdG : ∀ j, j ≤ D.R.m → IsSelfDualC (G.V (.grid j 0)) (G.Λ (.grid j 0)) := by
    intro j hj
    cases j with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ j => exact (G.sp.V_is (j + 1) 0 (by omega) hj (by omega)).sd
  have sdS := sdG (i + 1) hi
  have sdT := sdG i hi.le
  have sdB : IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    obtain ⟨I', h1, h2⟩ := _root_.GlobalTheory.ConjIdeal.stA_modul_conj_inv G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact _root_.GlobalTheory.idLat_isSelfDualC _ _ _ I' sdT h1 h2
  have hO : ∀ v ∈ latRow G i, v ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := fun v hv => GlobalTheory.RowLoc.mem_latO_negSp.1 hv.1
  have hB : ∀ v ∈ latRow G i, v ∈ latBig G i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · exact fun v hv => _root_.GlobalTheory.RowBig.latRow_zero_le_latBig D hq T L μ0 hL sc G W M hM hi hv
    · exact fun v hv => _root_.GlobalTheory.RowBig.latRow_le_latBig D hq T L μ0 hL sc G W M hM i hi1 hi hv
  have hdep := _root_.GlobalTheory.DepthBig.smul_mem_hatMx_of_mem_latBig D hq T L μ0 hL sc G W M hM i hi
  have finO := (GlobalTheory.AscFinWit.finLat_latO
    (S := G.V (.grid (i + 1) 0)) (T := G.V (.grid i 0))
    (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0))
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS).toIsLattice)
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdT | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdT).toIsLattice)).fin
  have finB := (GlobalTheory.AscFinWit.finLat_latO
    (S := G.V (.grid (i + 1) 0)) (T := G.V (.grid i 0))
    (LS := G.Λ (.grid (i + 1) 0)) (LT := idLat (shiftId G) (G.Λ (.grid i 0)))
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdS).toIsLattice)
    (by first | exact GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdB | exact (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ sdB).toIsLattice)).fin
  have uO : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
      (G.Λ (.grid i 0) : Set _) (fun _ => True) := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finO u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdT (fun _ => True) v (finO v (hO v hv))).1 (hO v hv) u' hu'
  have uB : u ∈ latBig G i := by
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) u hu).2 fun u' hu' => ?_
    refine H u' (finB u' hu') fun v hv => ?_
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdS sdB (fun _ => True) v (finB v (hB v hv))).1 (hB v hv) u' hu'
  exact ⟨GlobalTheory.RowLoc.mem_latO_negSp.2 uO, hdep u uO uB⟩

end GlobalTheory.AscFin.LatticeBidual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionaryPointsLocalMatricesLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul' (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem map_eq_one_of_off {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {g : GA D V}
    (hg : g ∈ GlobalTheory.FinPl.grpOff V (· = w.under (𝓞 D.host.F))) : (Formalism.L2.Theta.mt V g).map p.π = 1 := by
  ext i k
  have h0 := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V _ g).1 hg i k _ rfl
  have h1 : p.π ((Formalism.L2.Theta.mt V g - 1) i k) = 0 := by
    rw [hp.2.1]
    exact (GlobalTheory.LocHat.prV_eq_zero_iff_cpt _ _).1 (GlobalTheory.StabOff.prV_toEAf_eq_zero _ _ h0) w rfl
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1, ← Matrix.map_apply (f := p.π), Matrix.map_one _ (map_zero _) (map_one _)]

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ (e + cA D e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

theorem suppAt_mul' {e : AE D} {V : HSp D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) : SuppAt e V (a * b) := by
  rw [suppAt_iff'] at ha hb ⊢
  have : Formalism.L2.Theta.mt V (a * b) - 1 = (Formalism.L2.Theta.mt V a - 1) * Formalism.L2.Theta.mt V b + (Formalism.L2.Theta.mt V b - 1) := by
    rw [mt_mul', Matrix.sub_mul, Matrix.one_mul]; abel
  rw [this, smul_add, ← smul_mul_assoc, ha, hb]

theorem suppAt_inv' {e : AE D} {V : HSp D} {a : GA D V} (ha : SuppAt e V a) : SuppAt e V a⁻¹ := by
  rw [suppAt_iff'] at ha ⊢
  have : Formalism.L2.Theta.mt V a⁻¹ - 1 = -(Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a - 1)) := by
    rw [Matrix.mul_sub, mt_inv_mul', Matrix.mul_one]; abel
  rw [this, smul_neg, ← mul_smul_comm, ha]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem isLoc_mul' {S : HSp D} {F : Frame k S.rank Y} {a b : GA D S} {x y : GL Y k} (ha : p.IsLoc F a x)
    (hb : p.IsLoc F b y) : p.IsLoc F (a * b) (x * y) := by
  refine ⟨suppAt_mul' ha.1 hb.1, ?_⟩
  rw [mt_mul', Matrix.map_mul, ha.2, hb.2, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem isLoc_inv' {S : HSp D} {F : Frame k S.rank Y} {a : GA D S} {x : GL Y k} (ha : p.IsLoc F a x) :
    p.IsLoc F a⁻¹ x⁻¹ := by
  refine ⟨suppAt_inv' ha.1, ?_⟩
  have h1 : (Formalism.L2.Theta.mt S a⁻¹).map p.π * (F.β * x.val * F.γ) = 1 := by
    rw [← ha.2, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Matrix.mul_assoc x.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  calc (Formalism.L2.Theta.mt S a⁻¹).map p.π = (Formalism.L2.Theta.mt S a⁻¹).map p.π * ((F.β * x.val * F.γ) * (F.β * (x⁻¹).val * F.γ)) := by
        rw [h2, Matrix.mul_one]
    _ = F.β * (x⁻¹).val * F.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit p in
theorem frOf_conj {n N : ℕ} (h : N = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (x : GL (Fin n) (Lev.EAf D)) :
    (frOf h β w).β * (GlobalTheory.FunObj.inBasis h β w x).val * (frOf h β w).γ = (loc w x).val := by
  subst h
  have e1 : (frOf rfl β w).β = (loc w β).val := by ext i j; rfl
  have e2 : (frOf rfl β w).γ = ((loc w β)⁻¹).val := by ext i j; rfl
  have e3 : GlobalTheory.FunObj.inBasis rfl β w x = (loc w β)⁻¹ * loc w x * loc w β := by
    have e4 : GlobalTheory.FunObj.inBasis rfl β w x = GlobalTheory.StepData.reGL (finCongr rfl) (loc w (β⁻¹ * x * β)) := by
      simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e5 : ∀ g : GL (Fin N) (Kw w), GlobalTheory.StepData.reGL (finCongr rfl) g = g := fun g => Units.ext (by ext i j; rfl)
    rw [e4, e5, map_mul, map_mul, map_inv]
  rw [e1, e2, e3, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

end GlobalTheory.FlatPlaceLoc

namespace GlobalTheory.FlatPlaceLoc

open GlobalTheory.FlatPlace GlobalTheory.LocMod

variable {D : D7}

theorem loc_finE {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} (g : GA D V) :
    (loc w (Lev.finE V g)).val = (Formalism.L2.Theta.mt V g).map p.π := by
  ext i j
  rw [Matrix.map_apply, hp.2.1]
  rfl

theorem isLoc_of_inBasis {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {V : HSp D} {N : ℕ} (h : N = V.rank)
    (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) (gk : GL (Fin N) (Kw w)) (hs : SuppAt p.e V g)
    (hb : GlobalTheory.FunObj.inBasis h β w (Lev.finE V g) = gk) : p.IsLoc (frOf h β w) g gk :=
  ⟨hs, by rw [← hb, frOf_conj, loc_finE hp]⟩

theorem elt_zero {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w)) :
    (repsAt G t w).elt β (D.R.m, 0) = stair (locGrid G t w) (unifAt w) (cosExp G w) 0 :=
  (onColumn_apply (G := locGrid G t w) _ 0).trans rfl


open Classical in
theorem localization₂ : Big fun ch => LocP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp β r r₀ h hpts j hj
  obtain ⟨hr, hr₀, hh⟩ := hpts
  have L1 : p.IsLoc (frRow ch.S.B t w j hj) (r j) _ := isLoc_of_inBasis hp _ _ _ _ (hr j hj).1 (hr j hj).2
  have L0 : p.IsLoc (frRow ch.S.B t w j hj) (r₀ j) _ := isLoc_of_inBasis hp _ _ _ _ (hr₀ j hj).1 (hr₀ j hj).2
  refine ⟨?_, fun he => ?_, fun ho => ?_⟩
  · convert isLoc_mul' p (isLoc_inv' p L0) L1 using 1
    beta_reduce
    rw [Pi.mul_apply]
    by_cases h0 : j = 0
    · subst h0
      have hn : (0 : ℕ) ∉ idx D := by rw [mem_idx]; omega
      rw [if_pos rfl, if_neg hn, epsV_apply, if_neg hn, one_mul, elt_zero]
      exact (inv_inv _).symm.trans (mul_one _).symm
    · by_cases hi : j ∈ idx D
      · rw [if_neg h0, if_pos hi, inv_one, one_mul, epsV_apply, if_pos hi]
      · have hm : D.R.m ≤ j + 1 := by rw [mem_idx] at hi; omega
        rw [if_neg h0, if_neg hi, inv_one, mul_one, epsV_eq_one t w hm, elt_eq_one t w β hm, mul_one]
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    rw [hδ.2.1 he, inv_one, one_mul] at hoff
    rw [mt_mul', Matrix.map_mul, map_eq_one_of_off hp hoff, Matrix.one_mul, L0.2, Matrix.mul_assoc,
      (frRow ch.S.B t w j hj).γβ, Matrix.mul_one]
    rfl
  · obtain ⟨δ, hδ, hoff⟩ := hh j hj
    refine ⟨δ, hδ, ?_⟩
    have h0 : j ≠ 0 := by rintro rfl; simp at ho
    have hr0 : (Formalism.L2.Theta.mt _ (r₀ j)).map p.π = 1 := by
      rw [L0.2]
      simp only [if_neg h0, Units.val_one, Matrix.mul_one, (frRow ch.S.B t w j hj).βγ]
    rw [mt_mul', Matrix.map_mul, hr0, Matrix.mul_one, ← mul_inv_cancel_left δ (h j), mt_mul', Matrix.map_mul,
      map_eq_one_of_off hp hoff, Matrix.mul_one]

end GlobalTheory.FlatPlaceLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
section
namespace GlobalTheory.RowReal

open GlobalTheory.RowClaim

theorem realLine : Big fun ch => RealLine ch :=
  big_mono (fun ch h => realLine_of_periodsOnLine ch h) _root_.GlobalTheory.RowReal.periodsOnLine_big

end GlobalTheory.RowReal
end

