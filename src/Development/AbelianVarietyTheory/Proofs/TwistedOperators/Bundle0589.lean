module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
public import Lean
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx.CarryWeil

open GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gram_posDef_def (G : GridData L sc) {Y : Node} (hY : DefNode D.R.m Y) (τ : D.what₂.Tau) :
    (gramAt D (G.V Y) τ).PosDef := by
  rcases Y with ⟨_ | i, j⟩ | i | j
  · obtain ⟨-, rfl⟩ := hY
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact GlobalTheory.Hk3.StepX.gram_posDef_X τ
  · obtain ⟨hi, rfl⟩ := hY
    have hV := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg, Nat.sub_self, Nat.zero_div] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  · exact hY.elim
  · have hV := G.isV (X := .top j) hY (fun j h => by cases h)
    have := hV.sigOK (tauE D τ)
    rw [hV.sig] at this
    simp only [Node.neg] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem cart_def (G : GridData L sc) (W : G.Weil) {Y : Node} (hY : DefNode D.R.m Y) : W.cart Y = fun _ => 1 := by
  funext τ
  have hr : Y.InRange D.R.m := by
    rcases Y with ⟨i, j⟩ | i | j <;> simp only [DefNode, Node.InRange] at hY ⊢ <;> omega
  have hpos := gram_posDef_def G hY τ
  exact GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ (W.cart_is Y hr τ) ⟨Matrix.mul_one 1, by simp, by simpa using hpos⟩
    (by simp)

theorem heq_one {V V' : HSp D} (h : V' = V) :
    HEq (fun _ : D.what₂.Tau => (1 : Matrix (Fin V'.rank) (Fin V'.rank) ℂ))
      (fun _ : D.what₂.Tau => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) := by
  subst h; rfl

theorem attChr_congr {C : Type} [CommGroup C] {a a' b b' : C} {n n' : ℕ} (h1 : a = a') (h2 : b = b') (h3 : n = n') :
    Formalism.IndefR.Lift.attChr a b n = Formalism.IndefR.Lift.attChr a' b' n' := by
  subst h1 h2 h3; rfl

section Transport

open GlobalTheory.Mem

theorem exists_om_tr {X X' : Stages} (h : X'.B.toPre = X.B.toPre) {ψ : AddChar (AF X.toD7.host.F) ℂ} {S T : HSp X.toD7}
    {χS χT : (AE X.toD7)ˣ →* Circle} {ω : GA X.toD7 S × GA X.toD7 T →* Module.End ℂ (WO S T → ℂ)}
    {ψ' : AddChar (AF X'.toD7.host.F) ℂ} {S' T' : HSp X'.toD7} {χS' χT' : (AE X'.toD7)ˣ →* Circle}
    (hψ : HEq ψ' ψ) (hS : HEq S' S) (hT : HEq T' T) (h1 : HEq χS' χS) (h2 : HEq χT' χT)
    (hw : IsWeilDatumO ψ S T χS χT ω) :
    ∃ ω' : GA X'.toD7 S' × GA X'.toD7 T' →* Module.End ℂ (WO S' T' → ℂ), IsWeilDatumO ψ' S' T' χS' χT' ω' ∧ HEq ω' ω := by
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B; cases B'
  dsimp only at h
  subst h
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  refine ⟨ω, ?_, HEq.rfl⟩
  exact
    { std := (by with_unfolding_all exact (hw.std :))
      hecS := (by with_unfolding_all exact (hw.hecS :))
      hecT := (by with_unfolding_all exact (hw.hecT :))
      resS := (by with_unfolding_all exact (hw.resS :))
      resT := (by with_unfolding_all exact (hw.resT :))
      om_pres := fun p f hf =>
        have r := hw.om_pres p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
        ⟨(by with_unfolding_all exact (r.quasi :)), (by with_unfolding_all exact (r.level :)), (by with_unfolding_all exact (r.cont :)), (by with_unfolding_all exact (r.smooth :))⟩
      om_heis := fun g h w₀ f hf => hw.om_heis g h w₀ f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_aut := fun γ hγ γ' hγ' f hf => hw.om_aut γ hγ γ' hγ' f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_cont := fun f hf => hw.om_cont f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_unit := fun μ 𝓕 hμ h𝓕 p f hf => hw.om_unit μ 𝓕 hμ h𝓕 p f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩
      om_split := fun e he g h hg hh x y hx hy => by
        obtain ⟨r, hr, hℓ⟩ := hw.om_split e he g h hg hh x y hx hy
        exact ⟨r, hr, fun ℓ hℓ' f hf => hℓ ℓ (fun u hu f' hf' => hℓ' u hu f' ⟨(by with_unfolding_all exact (hf'.quasi :)), (by with_unfolding_all exact (hf'.level :)), (by with_unfolding_all exact (hf'.cont :)), (by with_unfolding_all exact (hf'.smooth :))⟩) f ⟨(by with_unfolding_all exact (hf.quasi :)), (by with_unfolding_all exact (hf.level :)), (by with_unfolding_all exact (hf.cont :)), (by with_unfolding_all exact (hf.smooth :))⟩⟩ }

end Transport

end GlobalTheory.RowEx.CarryWeil


open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowEx.CarryWeil in
theorem GlobalTheory.RowEx.carryW_of_weil : GlobalTheory.Published.WeilRepresentationUnitaryPair → CarryW := by
  intro hW X X' T T' L Γ _ _ Pl0 A Ks _ _ _ R μ₀ ι hL hch hmod sc G G' hG W
  obtain ⟨W1, hW1⟩ := GlobalTheory.ChiGrid.WeilOver.exists_weil_over_of_clauses hW R hL.is' hch hmod sc G'
  have hm : X'.toD7.R.m = X.toD7.R.m := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    rfl
  have F1 : HEq W1.ψ W.ψ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.StdAdelicChar.existsUnique_isStdChar _ (-1) (Or.inr rfl)).unique W1.ψ_std ((by with_unfolding_all exact (W.ψ_std :))))
  have F2 : HEq W1.θ W.θ := by
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_of_eq ((GlobalTheory.SmoothForms.RealPts.realPoints _).1 _ _ W1.θ_is ((by with_unfolding_all exact (W.θ_is :))))
  have F3 : ∀ Y, DefNode X'.toD7.R.m Y → HEq (W1.cart Y) (W.cart Y) := by
    intro Y hY
    rw [cart_def G' W1 hY, cart_def G W (hm ▸ hY)]
    have hV : HEq (G'.V Y) (G.V Y) := by
      rcases Y with ⟨_ | i, j⟩ | i | j
      · obtain ⟨-, rfl⟩ := hY
        have hpre := hL.pre
        obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
        obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
        cases B; cases B'
        dsimp only at hpre
        subst hpre
        exact heq_of_eq ((congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm)
      · exact (hG.grid i j).1
      · exact hY.elim
      · exact (hG.top j).1
    have hpre := hL.pre
    obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
    obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
    cases B; cases B'
    dsimp only at hpre
    subst hpre
    exact heq_one (eq_of_heq hV)
  have F4 : ∀ p, DefPair X'.toD7.R.m p → ∃ ω, IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω ∧
      HEq ω (W.om (mapPair ι p)) := by
    intro p hp
    have hr : (mapPair ι p).InRange X.toD7.R.m := by
      rw [← hm]
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;>
        simp only [DefPair, mapPair, Pair.InRange, Pair.big, Node.InRange] at hp ⊢ <;> omega
    have key : HEq (G'.pS p) (G.pS (mapPair ι p)) ∧ HEq (G'.pT p) (G.pT (mapPair ι p)) ∧
        HEq (G'.chrS p) (G.chrS (mapPair ι p)) ∧ HEq (G'.chrT p) (G.chrT (mapPair ι p)) := by
      have eta := hL.is.eta
      have eta' := hL.is'.eta
      have mu0 := hL.is.mu0
      have mu0' := hL.is'.mu0
      have xi := hL.is.xi
      have xi' := hL.is'.xi
      have hxi := hL.xi
      obtain ⟨f, f', hff, hC, hC'⟩ := hL.C
      have hpre := hL.pre
      obtain ⟨B, C, Wr, V, S, N, Gj⟩ := X
      obtain ⟨B', C', Wr', V', S', N', Gj'⟩ := X'
      cases B; cases B'
      dsimp only at hpre
      subst hpre
      obtain rfl := eq_of_heq hff
      rw [hC] at eta mu0
      rw [hC'] at eta' mu0'
      have eEta : R.toLevCh.eta = L.eta := (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ eta' ((by with_unfolding_all exact (eta :)))
      rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩
      · obtain ⟨hi, hj⟩ := hp
        have hS1 : G'.V (.grid (i + 1) j) = G.V (.grid (i + 1) j) := eq_of_heq (hG.grid i j).1
        have hT1 : G'.V (.grid i j) = G.V (.grid i j) := by
          cases i with
          | zero =>
            subst hj
            exact (congrArg LSp.sp (colY_m _)).trans (congrArg LSp.sp (colY_m L)).symm
          | succ k => exact eq_of_heq (hG.grid k j).1
        have ech := eq_of_heq hG.chi
        exact ⟨heq_of_eq (congrArg negSp hS1), heq_of_eq hT1,
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => (negSp V).rank) hS1)),
          heq_of_eq (attChr_congr (congrFun ech _) eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
      · exact hp.elim
      · exact hp.elim
      · have hj := Nat.lt_of_succ_le hp
        have emu : R.toLevCh.mu0 (j + 1) = L.mu0 (j + 1) :=
          (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (mu0' ⟨j, hj⟩) ((by with_unfolding_all exact ((mu0 ⟨j, hj⟩) :)))
        have exi : R.toLevCh.xi t = L.xi (ι t) := by
          have h1 := xi (ι t)
          have h2 := xi' t
          rw [eq_of_heq (hxi t)] at h2
          exact (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ h2 ((by with_unfolding_all exact (h1 :)))
        have hS1 : G'.V (.top j) = G.V (.top j) := eq_of_heq (hG.top j).1
        have hT1 : G'.V (.top (j + 1)) = G.V (.top (j + 1)) := eq_of_heq (hG.top (j + 1)).1
        have emu' : R.toLevCh.mu t (j + 1) = L.mu (ι t) (j + 1) := congrArg₂ (· * ·) emu exi
        exact ⟨heq_of_eq hS1, heq_of_eq hT1,
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hS1)),
          heq_of_eq (attChr_congr emu' eEta (congrArg (fun V : HSp _ => V.rank) hT1))⟩
    exact exists_om_tr hL.pre F1 key.1 key.2.1 key.2.2.1 key.2.2.2 (W.om_is (mapPair ι p) hr)
  have key : ∀ p : Pair T', ∃ ω, (p.InRange X'.toD7.R.m →
      IsWeilDatumO W1.ψ (G'.pS p) (G'.pT p) (G'.chrS p) (G'.chrT p) ω) ∧
      (DefPair X'.toD7.R.m p → HEq ω (W.om (mapPair ι p))) ∧ (¬ DefPair X'.toD7.R.m p → ω = W1.om p) := by
    intro p
    by_cases hp : DefPair X'.toD7.R.m p
    · obtain ⟨ω, h1, h2⟩ := F4 p hp
      exact ⟨ω, fun _ => h1, fun _ => h2, fun h => absurd hp h⟩
    · exact ⟨W1.om p, W1.om_is p, fun h => absurd h hp, fun _ => rfl⟩
  choose om hom hdef hnd using key
  refine ⟨{ W1 with om := om, om_is := hom }, ?_, F1, F2, F3, hdef⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hW1
  refine ⟨a1, a2, a3, a4, a5, a6, fun t k hk => ?_, fun t k hk => ?_⟩
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a7 t k hk
  · show HEq (om (.mu t 0 k)) _
    rw [hnd (.mu t 0 k) (fun h => h)]
    exact a8 t k hk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridHighestWeightEqCompactChainParameter
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.ChiGrid GlobalTheory.RowReal
open Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.RowReal.WeightsX

open GlobalTheory.SignedHC

theorem mem_listBlock_iff {c x : ℚ} {n : ℕ} : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n ↔ x ∈ TPar.block c n := by
  rw [GlobalTheory.SignedHC.mem_block]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

theorem pairwise_listBlock (c : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  linarith

theorem psiPar_eq (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar =
    (num D C τ).a 0 :: ((List.finRange D.R.m).flatMap (fun i : Fin D.R.m =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)]) ++
      (List.finRange (D.R.k - 1)).map fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)) := rfl

theorem psiPar_props (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    (rowEntries D C τ).psiPar.Pairwise (· > ·) ∧ ∀ x ∈ (rowEntries D C τ).psiPar, x ∈ (num D C τ).weightX 0 := by
  have hm : (num D C τ).NearMid := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  have hGm : (num D C τ).m = D.R.m := rfl
  have hGk : (num D C τ).k = D.R.k := rfl
  have hga : (0 : ℚ) < (num D C τ).ga := by exact_mod_cast (by omega : 0 < (num D C τ).ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) →
      (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga := fun i x hx =>
    blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)
  have piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++
      [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i := by
    intro i y hy
    rw [(num D C τ).a_eq_succ_add i]
    rcases List.mem_append.1 hy with h | h
    · have := hB i y h; exact ⟨this.1.le, this.2⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨le_rfl, by linarith⟩
  have hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)),
      y ∈ (num D C τ).cloudHalf := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩
  rw [psiPar_eq]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
        have := piece i y h
        linarith [hle (Nat.zero_le (i : ℕ))]
      · have := cloudHalf_lt (hU y h)
        linarith [hle (Nat.zero_le (num D C τ).m)]
    · intro i _
      rw [List.pairwise_append]
      refine ⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hB i x hx).1
    · refine (List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_
      intro x hx y hy
      have h1 := piece i x hx
      have h2 := piece j y hy
      have h3 : (i : ℕ) + 1 ≤ j := hij
      linarith [hle h3]
    · refine (List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_
      have hij' : (i : ℕ) < j := hij
      have := (num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)
      have h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2) := by exact_mod_cast this
      simp only [GridData.vHalf]; linarith
    · intro x hx y hy
      obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hx
      have h1 := piece i x h
      have h2 := cloudHalf_lt (hU y hy)
      have h3 : (i : ℕ) + 1 ≤ (num D C τ).m := by have := i.2; omega
      linarith [hle h3]
  · intro y hy
    rw [GridData.mem_weightX]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))
      · rw [List.mem_singleton] at h; subst h
        exact Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)
    · exact Or.inr (Or.inl (hU y h))

theorem length_psiPar (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar.length = rankP D D.R.m := by
  rw [length_psi, rowSizes_nR]; simp [rankX]

end GlobalTheory.RowReal.WeightsX

namespace GlobalTheory.RowReal

open GlobalTheory.SignedHC GlobalTheory.RowReal.WeightsX

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AAUnit

theorem natCast_notMem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (h : Nat.Coprime n p) (hp : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ w.asIdeal := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hn) (w.asIdeal.mul_mem_left v hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem absNorm_cmIdeal_not_mem_gridPlaces {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  rcases P.mem_S0_of_sum_eq.mp hv with h | h
  ·
    subst h
    have hq := GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (D := D)
    exact natCast_notMem_of_coprime P.v0 ((Nat.Prime.coprime_iff_not_dvd hq.1).mpr hq.2.2).symm P.basePlace_over_qZero
  ·
    have hcop : ∀ p ∈ D.host.levelPrimes, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
        ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal :=
      fun p hp hpv => natCast_notMem_of_coprime v (D.host.ccK_coprime p (by simp [hp])) hpv
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF (D := D)).mp h with h' | h' | h' | h'
    · exact hcop _ (D.host.g_level 0) h'
    · exact hcop _ (D.host.g_level 1) h'
    · exact hcop _ D.host.pde_level.1 h'
    · exact hcop _ D.host.pde_level.2 h'

theorem exists_valuation_one_element_at_grid_places : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.SepRows.OffQ D → L.Is μ₀ → ∀ (G : GridData L sc), ∀ w ∈ G.pl.W0, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1 := by
  intro D T L sc μ₀ _ _ G w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw

  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := by
    intro hin
    apply absNorm_cmIdeal_not_mem_gridPlaces G.pl hv
    have hc : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈ ((G.pl.w v).under (𝓞 D.host.F)).asIdeal := by
      show ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈
        Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (G.pl.w v).asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hin
    rw [G.pl.under_w hv] at hc
    exact hc
  refine ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩
  have key := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) (v := G.pl.w v)).mpr hN
  rw [map_natCast] at key
  first
  | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := G.pl.w v) _).trans key
  | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact key)

end GlobalTheory.AAUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOffPartVacuumCommutantActsByScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_offPart_vacuumCommutant_acts_by_scalar : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∃ c : ℂ, heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) ((1 - e - cA D e) • w) (W.vac i) = c • W.vac i := by
  first | exact @GlobalTheory.CommVac.heisO_offPart_vac | exact GlobalTheory.CommVac.heisO_offPart_vac | (intros; apply GlobalTheory.CommVac.heisO_offPart_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7} (θ : InfFam D) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)

def atP : Subgroup (NI V C) :=
  (GinfC V ⊓ ⨅ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), (GlobalTheory.RowReal.infMatHom V (θ τ')).ker).subgroupOf (NI V C)

def offP : Subgroup (NI V C) := ((GlobalTheory.RowReal.infMatHom V (θ τ)).ker).subgroupOf (NI V C)

variable {θ V C τ}

theorem mem_atP {p : NI V C} :
    p ∈ atP θ V C τ ↔ (p : GA D V) ∈ GinfC V ∧ ∀ τ', τ' ≠ τ → cmp θ τ' (p : GA D V) = 1 := by
  simp only [atP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

theorem mem_offP {q : NI V C} : q ∈ offP θ V C τ ↔ cmp θ τ (q : GA D V) = 1 := by
  simp only [offP, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  rfl

end GlobalTheory.FibreAtTau
end
end

