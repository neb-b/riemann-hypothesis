module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPointMemSumTranslateOfAnnihilator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0619
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColconSplitFamAppend
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.Unf

theorem colcon_splitFam_append {T : Type} {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : p.Fam S) (e : q.Fam S), splitFam q (Path.Fam.append (q := q) d e) = (d, e)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
      show ((splitFam q (Path.Fam.append (q := q) d e.1)).1, ((splitFam q (Path.Fam.append (q := q) d e.1)).2, e.2)) = (d, e)
      rw [colcon_splitFam_append q d e.1]
      rfl

theorem colcon_getD_downFam {T : Type} {S : Arrow T → Type} (t : T) (i : ℕ) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, S (.down t i j)) (j : ℕ) (hj : j < n), getD t i n (downFam t i n f) j hj = f ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, j, hj => by
      unfold getD
      have hs := colcon_splitFam_append (p := Path.one (.down t i n)) (downPath t i n) ((), f (Fin.last n))
        (downFam t i n fun j => f j.castSucc)
      rw [downFam]
      split_ifs with h
      · erw [hs]
        exact colcon_getD_downFam t i n _ j h
      · have hnj : n = j := by omega
        subst j
        change (splitFam (p := Path.one (.down t i n)) (downPath t i n) _).1.2 =
          f (Fin.last n)
        rw [hs]

theorem colcon_nIter_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) {q q' : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), NIter ρ μ q l h z →
      (∀ h' : ∀ i, H i, (∀ i, i ∉ l → h' i = h i) → q h' = q' h') → NIter ρ μ q' l h z
  | [], h, z, hz, hq => (show z = q h from hz).trans (hq h fun _ _ => rfl)
  | i :: l, h, z, ⟨f, hf, hr⟩, hq => ⟨f, hf, fun g => colcon_nIter_congr ρ μ l _ _ (hr g) fun h' hh' => hq h' fun k hk => by
      rw [hh' k fun hl => hk (List.mem_cons_of_mem _ hl), Function.update_of_ne fun e => hk (by simp [e])]⟩

theorem colcon_quot {G : Type} [Group G] [MeasurableSpace G] {R R' : Subgroup G} (e : R = R') {ρ : Measure R} {ρ' : Measure R'}
    (hh : HEq ρ ρ') {μ : Measure G} {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 ρ' μ f z) : IsQuotIntL1 ρ μ f z := by
  subst e
  obtain rfl := eq_of_heq hh
  exact h

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem colcon_rowGrp_jac {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (jacAt G hM j σ hj).d := by
  unfold rowGrp
  rw [dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  rfl

theorem colcon_rowGrp_bes {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m)
    (vN : VolN (besDecAt G j σ hj)) :
    rowGrp G j = besGrp (besAt G hM j σ hj vN).d (besAt G hM j σ hj vN).o := by
  unfold rowGrp
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  rfl

theorem colcon_gen (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t)
    (F : Fn G (.grid D.R.m D.R.m)) (ρ : ∀ j, Measure (rowGrp G j))
    (hJ : ∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR)
    (hB : ∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) (h : Pts G) (g : GA D (G.V (.grid D.R.m j)))
      (φ : GA D (G.V (.top j)) → ℂ) (z : ℂ), g = h j →
      (chainFrom G W t hM σ j hj vN).Iter
        (colPer W hM σ j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) σ j hj vN) F φ g) z →
      NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h' => jPer W M t (conAt W hM Φ h') F σ j hj φ)
        (List.range' (j + 1) (2 * σ)) h z := fun
  | 0, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hc : conAt W hM Φ h j = lastDat W hM j hj vN (h j) (Φ ⟨j, by omega⟩)
          (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := by
        unfold conAt
        rw [dite_eq_left hj]
        rfl
      have hz' : z = colPer W hM 0 j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) 0 j hj vN) F φ (h j) () := hz
      show z = jPer W M t (conAt W hM Φ h) F 0 j hj φ
      rw [hz']
      show _ = ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (conAt W hM Φ h j)
        (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
      rw [hc]
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom]
      rw [colcon_getD_downFam, colcon_getD_downFam]
      rfl
  | σ + 1, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m := by omega
      let vN' := (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ hj')).some
      have hstep : ∃ (f₁ : GA D (G.V (.grid D.R.m (j + 1))) → ℂ)
          (f₂ : GA D (G.V (.grid D.R.m (j + 1))) → GA D (G.V (.grid D.R.m (j + 1 + 1))) → ℂ),
        IsQuotIntL1 (jacAt G hM (j + 1) (σ + 1) (by omega)).μR
          (M.ν (.grid D.R.m (j + 1))) f₁ z ∧
        ∀ a, IsQuotIntL1 (besAt G hM (j + 1 + 1) σ hj' vN').μR
          (M.ν (.grid D.R.m (j + 1 + 1))) (f₂ a) (f₁ a) ∧
          ∀ b, (chainFrom G W t hM σ (j + 1 + 1) hj' vN').Iter
            (fun rest => colPer W hM (σ + 1) j hj vN
              (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) (σ + 1) j hj vN)
              F φ (h j) (a, b, rest)) (f₂ a b) := hz
      rcases hstep with ⟨f₁, f₂, h1, h2⟩
      have hl : List.range' (j + 1) (2 * (σ + 1)) = (j + 1) :: (j + 1 + 1) :: List.range' (j + 1 + 1 + 1) (2 * σ) := by
        rw [show 2 * (σ + 1) = 2 * σ + 1 + 1 by ring, List.range'_succ, List.range'_succ]
      rw [hl]
      have hjJ : j + 1 + 2 * (σ + 1) + 1 = D.R.m := by omega
      refine ⟨f₁, colcon_quot (colcon_rowGrp_jac hM (j + 1) (σ + 1) hjJ)
        (hJ (j + 1) (σ + 1) hjJ) h1, fun a => ?_⟩
      refine ⟨f₂ a, colcon_quot (colcon_rowGrp_bes hM (j + 1 + 1) σ hj' vN')
        (hB (j + 1 + 1) σ hj') (h2 a).1,
        fun b => ?_⟩
      have hi := (h2 a).2 b
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom] at hi
      have ih := colcon_gen G W t hM Φ F ρ hJ hB σ (j + 1 + 1) hj' vN'
        (Function.update (Function.update h (j + 1) a) (j + 1 + 1) b) b _ (f₂ a b) (by simp) hi
      refine colcon_nIter_congr _ _ _ _ _ ih fun h' hh' => ?_
      have e0 : h' j = h j := (hh' j (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _))
      have e1 : h' (j + 1) = a := (hh' (j + 1) (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_self _ _ _))
      have e2 : h' (j + 1 + 1) = b := (hh' (j + 1 + 1) (by simp only [List.mem_range'_1]; omega)).trans (Function.update_self _ _ _)
      change _ = jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj'
        (biL W M t j φ (conAt W hM Φ h' j))
      apply congrArg (jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj')
      have hx : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
      have hlast : ¬ (j + 2 * 0 + 2 = D.R.m) := by omega
      have hC : conAt W hM Φ h' j = _ :=
        (dite_eq_right hlast).trans (dite_eq_left hx)
      rw [hC]
      obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
      simp only [e0, e1, e2, colcon_getD_downFam]
      -- These projections of the Bessel data are independent of the choice of vN.
      dsimp only [biL, GlobalTheory.SeeSaw.biLift, volAt, contr, flatBF, flatFB, Link.κ,
        stepAt, linkAt, besAt, jacAt]
      rfl

theorem nIter_conAt_of_colPer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t) (F : Fn G (.grid D.R.m D.R.m)) (φ : Fn G (.top 0)) (z : ℂ), (chain G W t hM).Iter (colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downFam t D.R.m D.R.m Φ)) F φ 1) z → ∀ (ρ : ∀ j, Measure (rowGrp G j)), (∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR) → (∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) → NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h => jPer W M t (conAt W hM Φ h) F _ 0 top_idx φ) (idx D) 1 z := by
  intro D T L sc G W t M hM Φ F φ z hz ρ hJ hB
  have e : List.range' (0 + 1) (2 * ((D.R.m - 2) / 2)) = idx D := by
    unfold idx
    have := top_idx (D := D)
    congr 1
    omega
  rw [← e]
  exact colcon_gen G W t hM Φ F ρ hJ hB _ 0 top_idx (topVN hM) 1 1 φ z rfl hz

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDual

theorem ann_depLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
    ∀ u ∈ depLat G (.core i), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) u y) = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi e he y hy h u hu
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  have h1 := h (e • u) (hu.2 e he)
  rw [smul_smul, hee, symplO_smul_half _ _ e u y hy] at h1
  exact h1


set_option maxHeartbeats 1000000 in
theorem cosDual : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
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
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hyp x hx
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨X, hXdef⟩ : ∃ X : WO (G.pS (.core i)) (G.pT (.core i)), X = e • x₀.map (incA D) := ⟨_, rfl⟩
  have hXh : IsHalf e X := fun a b => by
    simp only [hXdef, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨Z, hZdef⟩ : ∃ Z : WO (G.pS (.core i)) (G.pT (.core i)), Z = X - actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := ⟨_, rfl⟩
  have hZ : IsHalf e Z := fun a b => by
    simp only [hZdef, Matrix.sub_apply, mul_sub, hXh a b, half_actO _ _ e g X hXh a b]
  have key : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • v) y) = 1) →
      (∀ v ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO _ _ 1 g (e • v)) y) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) = 1 := by
    intro y hy h1 h2
    have hy' : IsHalf (cA D e) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g⁻¹ y) := half_actO _ _ _ _ _ hy
    have hA := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he y hy h1
    have hB := ann_depLat D hq T L μ0 hL sc G W M hM i hi e he _ hy' (fun v hv => by
      have h3 := h2 v hv
      rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g (e • v) (actO _ _ 1 g⁻¹ y), actO_inv]
      exact h3)
    have H := hyp y hy hA hB
    rw [← hXdef] at H
    rw [← GlobalTheory.SymplOInv.symplO_actO D _ _ 1 g X (actO _ _ 1 g⁻¹ y), actO_inv] at H
    have hsum : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by
      rw [hZdef]; abel
    have hs : symplO (G.pS (.core i)) (G.pT (.core i)) X y =
        symplO (G.pS (.core i)) (G.pT (.core i)) Z y +
          symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y := by
      conv_lhs => rw [hsum]
      exact GlobalTheory.LatVac.symplO_add_left _ _ _ _ _
    rw [hs, AddChar.map_add_eq_mul] at H
    generalize hcdef : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c at H
    have hc : c ≠ 0 := by
      intro h0
      have h5 : W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) *
          W.ψ (-(symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y)) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      rw [show W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (actO (G.pS (.core i)) (G.pT (.core i)) 1 g X) y) = c from hcdef,
        h0, zero_mul] at h5
      exact zero_ne_one h5
    have H' : (W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) Z y) - 1) * c = 0 := by
      rw [sub_mul, H, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 H').resolve_right hc)
  obtain ⟨a, ha, b, hb, hZeq⟩ := _root_.GlobalTheory.AnnSum.ann_sum D hq T L μ0 hL sc G W M hM i hi e he g Z hZ key
  have heq : e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - a) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - -b)) := by
    rw [smul_sub, sub_neg_eq_add, smul_add, actO_add, ← hXdef]
    have h6 : X = Z + actO (G.pS (.core i)) (G.pT (.core i)) 1 g X := by rw [hZdef]; abel
    rw [hZeq] at h6
    conv_lhs => rw [h6]
    abel
  obtain ⟨a₁, h1, a₂, h2, heq2⟩ := _root_.GlobalTheory.CosDualStep.coset_equation_mul_right_congruent_one_mod_depthIdeal D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g a ha (-b) (neg_mem hb) heq
  exact GlobalTheory.T.gridCoreNode_unitReading_integral_congruent D hq T L μ0 hL sc G W M hM i hi e he g a₁ h1 a₂ h2 heq2 x hx

end GlobalTheory.CosDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DblHandEqBiLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

theorem dbl_hand_eq_biLift : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : GlobalTheory.FunObj.Vol G}
    (hM : M.Is t) (σ j : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ) (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.top j)) φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))),
      Chain.hand (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
        (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
        (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        Φ₁ Φ₂ φ g h₁ h₂ =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (contr (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (G.V (.top (j + 1)))
          ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
          (flatBF (B := besAt G hM j (σ + 1) hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
            ((stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))).om
              (g, h₁) Φ₁))
          (flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega))
            (B := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
            (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega)))
            ((stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
              (besDecAt G (j + 1 + 1) σ (by omega))).om (h₁, h₂) Φ₂))) := by
  intro D T L sc G Wl t M hM σ j hj vN

  obtain ⟨χz, hz, hzr, -, hEven, hOdd⟩ := _root_.GlobalTheory.RowChars.rowChars G Wl t

  have hjOdd : (D.R.m - 1 - j) % 2 = 1 := by omega
  have hjEven : (D.R.m - 1 - (j + 1)) % 2 = 0 := by omega
  have hS₁ := (hOdd j (by omega) hjOdd).1
  have hT₁ := (hOdd j (by omega) hjOdd).2
  have hS₂ := (hEven (j + 1) (by omega) hjEven).1
  have hT₂ := (hEven (j + 1) (by omega) hjEven).2
  exact dbl_hand_of_chars G Wl t hM σ j hj χz hz hzr hS₁ hT₁ hS₂ hT₂ vN

end GlobalTheory.RowChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowZeroLeSelfDualHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.RowBig

theorem latRow_zero_le_latBig : All fun {D} _ _ _ {G} _ _ => 0 < D.R.m → latRow G 0 ≤ latBig G 0 := by
  intro D hq T L μ0 hL sc G W M hM him u hu
  have hS : IsSelfDualC (G.V (.grid (0 + 1) 0)) (G.Λ (.grid (0 + 1) 0)) :=
    (G.sp.V_is (0 + 1) 0 (by omega) him (by omega)).sd
  have hT : IsSelfDualC (G.V (.grid 0 0)) (G.Λ (.grid 0 0)) := by
    obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
    exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
  have h1 := idLat_one (G.Λ (.grid 0 0))
  have hsh := isSelfDualC_idLat_shiftId G _ hT
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hu' : u ∈ latO (negSp (G.V (.grid (0 + 1) 0))) (G.V (.grid 0 0)) (G.Λ (.grid (0 + 1) 0) : Set _)
      (G.Λ (.grid 0 0) : Set _) (fun _ => True) ∧
      ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (0 + 1) 0)) (G.Λ (.grid 0 0))) := hu
  have key := _root_.GlobalTheory.DepthShift.mem_latO_shift hq μ0 hL G (G.Λ (.grid (0 + 1) 0)) 1 (G.Λ (.grid 0 0)) hS (by rw [h1]; exact hT)
    (by rw [one_mul]; exact hsh) u (by rw [h1]; exact GlobalTheory.RowLoc.mem_latO_negSp.1 hu'.1) ⟨e, he, by rw [h1]; exact hu'.2 e he⟩
  rw [one_mul] at key
  exact key

end GlobalTheory.RowBig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeights
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end GlobalTheory.BottomRealAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PieceA

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (M : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem finLat_comap_extX {V V₀ W : HSp D} {ρ : ℕ} (d : GlobalTheory.MixModel.HypDec V V₀ ρ) {Γ : AddSubgroup (WO V W)}
    (hΓ : FinLat Γ) : FinLat (Γ.comap (d.extX W)) := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have hc : Continuous (d.extX W) := by
    show Continuous fun a : Mx D W.rank ρ => a ⬝ d.pX
    exact continuous_id.matrix_mul continuous_const
  have hinv : ∀ a : Mx D W.rank ρ, d.extX W a ⬝ d.jX = a := fun a => by
    rw [GlobalTheory.MixModel.HypDec.extX_apply, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jX, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hinv a]
    exact mxAt_mul_right (hΓ.fin _ ha) _
  · have hK : IsCompact ((fun w : WO V W => w ⬝ d.jX) '' (Γ : Set (WO V W))) :=
      hΓ.cpt.image (continuous_id.matrix_mul continuous_const)
    refine hK.of_isClosed_subset (hΓ.cpt.isClosed.preimage hc) ?_
    intro a ha
    exact ⟨_, ha, hinv a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hΓ.opn
    refine ⟨d.extX W ⁻¹' U, hU.preimage hc, by simpa using h0, fun a ha haf => ?_⟩
    exact hUA _ ha (by rw [GlobalTheory.MixModel.HypDec.extX_apply]; exact mxAt_mul_right haf _)

end GlobalTheory.AscFin.PieceA

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.PieceA

theorem finLat_pcBF_A₁ : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  have H := _root_.GlobalTheory.AscFin.GridLat.lattices_grid
  unfold OnStd at H ⊢
  delta All at H ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  exact finLat_comap_extX _ ((H D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).1

end GlobalTheory.AscFin
end

