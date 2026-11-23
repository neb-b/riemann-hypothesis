module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0452

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwiner
section
noncomputable section

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem itPair_of_par (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') {θ : InfFam D} (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
        GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (_root_.GlobalTheory.modelsAreCoverSeries_of_hypotheses hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (_root_.GlobalTheory.Chain.RealIt.GlueProof.glueLaw D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => _root_.GlobalTheory.vacChar_of_record D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (_root_.GlobalTheory.vacuumFock_all_records D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.RowThetaIt

end Gen

section Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.PairLift GlobalTheory.SignedHC GlobalTheory.RemoveBlock
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem dataAR_row (D : D7) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (i j : ℕ) (τ : D.what₂.Tau) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      parV D i j τ = dualPar (signed (al ++ be) (ga ++ de) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)))) ∧
      parV D i (j + 1) τ =
        dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j))) := by
  have he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩
  set G := grid D τ with hG
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'
  have hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ := by
    simp only [att, he, hδ]
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_true]; ring
    · have h' : ¬ Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_false]; ring
  have hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ' := by
    simp only [att, he, hδ']
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i j) ↔ False := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) ↔ False := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_false]; ring
    · have h' : Odd (rkV D i j) := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_true]; ring
  rw [hT, hS']
  set P := shift δ (G.parD i j) with hP
  have hpart := partner_parD D τ i j hi hj δ δ'
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold bigN; unfold Ranks.r at h1
    omega
  have hgap : GapOver P (2 * (bigN D : ℚ) ^ 3) := GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i j hi hj.le)
  have hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P)
      (2 * (bigN D : ℚ) ^ 3) := by
    rw [hP, ← hpart]; exact GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)
  have hreg : IsRegular P := isRegular_of_gapOver (by positivity) hgap
  have hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P := farFrom_shift (farFrom_parD D τ i j hi hj)
  have hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P := fun x hx =>
    le_trans (by linarith) (hfar3 x hx)
  have hne : P.Nonempty := by
    have hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud :=
      GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩
    have hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j := GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)
    exact ⟨_, mem_shift' hmem⟩
  have hcard : P.card + D.R.t ≤ bigN D := by
    rw [hP, card_shift]
    have h0 : (G.parD i j).card ≤ rkV D i j := card_parD_le D τ i j hi
    have a : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have b : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    have d : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
    show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    unfold rkV Ranks.r at h0
    omega
  have hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (entries P) := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    have hy := fst_mem_entries (mem_shift.1 hs)
    obtain ⟨z, hz⟩ := int_parD D τ i j _ hy
    simp only at hz
    obtain ⟨q, hq⟩ := D.R.t_odd
    have htq : ((D.R.t : ℚ) + 1) / 2 = q + 1 := by rw [hq]; push_cast; ring
    refine ⟨z + G.e (j + 1) - (q + 1), ?_⟩
    rw [htq]; push_cast; linarith
  obtain ⟨al, be, ga, de, hPe, hP'⟩ :=
    _root_.GlobalTheory.PairLift.FromSigned.thetaPar_partner D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'
  rcases hP' with ⟨hd, hP'⟩ | ⟨-, hP'⟩
  · refine ⟨D.R.t, al, be, ga, de, hd, ?_, ?_⟩
    · rw [← hPe]; rfl
    · rw [← hP', ← hpart]; rfl
  · exfalso
    set c' : ℚ := -(G.e (j + 1) : ℚ) + δ' with hc'
    have hx0 : ((D.R.t : ℚ) - 1) / 2 ∈ Formalism.BasicNotions.TH.block D.R.t :=
      by simp only [Formalism.BasicNotions.TH.block, List.mem_map, List.mem_range]; simp; exact ⟨0, by omega, by simp⟩
    have m1 : (((D.R.t : ℚ) - 1) / 2 + c', false) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      rw [hP']
      simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map]
      exact Or.inr ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx0))), rfl⟩
    have m2 : (((D.R.t : ℚ) - 1) / 2 + c', true) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      simp only [partner, Finset.mem_union, Finset.mem_image]
      refine Or.inr ⟨_, mem_block.2 ⟨0, by omega, by push_cast; ring⟩, rfl⟩
    have := hgap' _ m1 _ m2 (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.RowThetaIt

end Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem rowTheta_it : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hD hH _ hSz F hc _ G' W _ G hSp _ _ _ i j hi hj ω f hω hf
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hc.lev, hc.models.inf, hc.models.νY, hc.models.νY', hc.models.νX⟩
  have hV := hSp.vert i j hi hj.le
  have hV' := hSp.vert i (j + 1) hi hj
  obtain ⟨It, -, hIt⟩ := itPair_of_par hD hH (G.nV i j).M (G.nV i (j + 1)).M hR.inf R.ψ
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) j))
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) (j + 1)))
    (fun τ => by rw [hV.par, hV'.par]; exact dataAR_row D hSz (i + 1) j τ hi hj)
  refine ⟨It, fun t => hIt (ω t) f ⟨_, _, hω t, fun τ =>
    ⟨GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _,
      GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _⟩⟩
    ⟨hf.isFinVec.1, GlobalTheory.PairLift.vac_ne hf, hf.isFinVec.2⟩⟩

end GlobalTheory.RowThetaIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemSumIdeal

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_sub_mem_idS_prod [StarRing E] (P : Finset (Pl E)) (d : Pl E → ℕ) {ε : E ⊗[F] Formalism.L2.Herm.Af F}
    (hε : ε ∈ Formalism.L2.Herm.intAf F E)
    (h : ∀ w ∈ P, ∃ a : E ⊗[F] Formalism.L2.Herm.Af F, GlobalTheory.InertNbr.IdemOf F w a ∧ a * ε = a) :
    ∃ t ∈ Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w), (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - ε := by
  classical
  choose! a ha hae using h
  have hone : (1 : E ⊗[F] Formalism.L2.Herm.Af F) - ε ∈ Formalism.L2.Herm.intAf F E := sub_mem (one_mem _) hε
  set t : Formalism.L2.Herm.intAf F E := ⟨1 - ε, hone⟩ with ht
  set b : Pl E → Formalism.L2.Herm.intAf F E := fun w =>
    if hw : w ∈ P then ⟨1 - a w, (ha w hw).one_sub_mem⟩ else 1 with hb
  have hbm : ∀ w ∈ P, b w ∈ Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := by
    intro w hw
    have := (ha w hw).one_sub_mem_idS (d w)
    simpa [hb, hw] using this
  have hprod : ∏ w ∈ P, b w ∈ ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) := Ideal.prod_mem_prod hbm
  have hmap : ∏ w ∈ P, Formalism.L2.DIV.idS F (w.asIdeal ^ d w) = Formalism.L2.DIV.idS F (∏ w ∈ P, w.asIdeal ^ d w) := by
    unfold Formalism.L2.DIV.idS
    exact (map_prod (Ideal.mapHom (Formalism.L2.DIV.oToS F E)) _ P).symm
  have hfix : t * ∏ w ∈ P, b w = t := by
    refine Finset.prod_induction b (fun x => t * x = t) (fun x y hx hy => by rw [← mul_assoc, hx, hy]) (mul_one t) ?_
    intro w hw
    apply Subtype.ext
    simp only [hb, hw, dif_pos, ht, Subring.coe_mul]
    linear_combination (hae w hw)
  refine ⟨t, ?_, rfl⟩
  rw [← hfix, ← hmap]
  exact Ideal.mul_mem_left _ _ hprod

end Generic

end GlobalTheory.IdemSumIdeal

namespace GlobalTheory.IdemSumIdeal

theorem idemOf_toEAf {D : D7} {a : AE D} {w : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt a w) :
    GlobalTheory.InertNbr.IdemOf D.host.F w (toEAf D a) := by
  refine ⟨by rw [← map_mul, h.1.1], fun x hx => ?_⟩
  rw [h.2 x hx]
  have e : toEAf D (a * incA D ((x : D.host.E)⁻¹)) = toEAf D a * Formalism.L2.Col.iA D.host.F D.host.E ((x : D.host.E)⁻¹) := by
    rw [map_mul]; rfl
  rw [← e]
  exact not_congr ⟨GlobalTheory.IdemIntegral.toEAf_mem_of_finPart_mem, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

theorem isIdemSum_props : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ),
    IsIdemSum e P → infPart D e = 0 ∧ toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      ∃ t ∈ Formalism.L2.DIV.idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w), (t : EAf D) = 1 - toEAf D e := by
  intro D e P d h
  obtain ⟨⟨es, hes, he⟩, -⟩ := id h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact sum_mem fun w hw => (idemOf_toEAf (hes w hw)).mem
  refine ⟨?_, hint, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.ExportSeries.SpecGood.infPart_eq_zero_of_isIdemAt D w (es w) (hes w hw)
  · refine one_sub_mem_idS_prod P d hint fun w hw => ?_
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt h hw
    exact ⟨toEAf D a, idemOf_toEAf ha, by rw [← map_mul, hae]⟩

end GlobalTheory.IdemSumIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InMaxCompactOfModelFrameInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical


open Matrix in
theorem GlobalTheory.CuspGK.inK_inv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S)
    (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GlobalTheory.CuspGK.InK M τ g) :
    GlobalTheory.CuspGK.InK M τ g⁻¹ ∧ g⁻¹⁻¹ = g := by
  obtain ⟨hU, hK1, hK2⟩ := h
  set P := M.fr τ with hPdef
  have hP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set u := P * g * P⁻¹ with hu
  have huu : IsUnit u.det := Matrix.UnitaryGroup.det_isUnit ⟨u, hK1⟩
  have hg : IsUnit g.det := by
    have hdet : u.det = P.det * g.det * P⁻¹.det := by simp [hu, Matrix.det_mul]
    rw [hdet] at huu
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left huu)
  have hinv : P * g⁻¹ * P⁻¹ = u⁻¹ := by
    rw [hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hP, Matrix.mul_assoc]
  have hsu : star u * u = 1 := Unitary.star_mul_self_of_mem hK1
  have hustar : u⁻¹ = star u := Matrix.inv_eq_left_inv hsu
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ huu
  have h2 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ huu
  refine ⟨⟨?_, ?_, ?_⟩, Matrix.nonsing_inv_nonsing_inv _ hg⟩
  · have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
    show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hgg]; simp
  · show P * g⁻¹ * P⁻¹ ∈ _
    rw [hinv, hustar]
    exact Unitary.star_mem hK1
  · show P * g⁻¹ * P⁻¹ * _ = _ * (P * g⁻¹ * P⁻¹)
    rw [hinv]
    clear_value u
    calc u⁻¹ * Formalism.REAL.Jm (M.ε τ) = u⁻¹ * Formalism.REAL.Jm (M.ε τ) * (u * u⁻¹) := by rw [h2, Matrix.mul_one]
      _ = u⁻¹ * (Formalism.REAL.Jm (M.ε τ) * u) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = u⁻¹ * (u * Formalism.REAL.Jm (M.ε τ)) * u⁻¹ := by rw [hK2]
      _ = (u⁻¹ * u) * Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) * u⁻¹ := by rw [h1, Matrix.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeAdm

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def smAut (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f}
  add_mem' := fun ha hb => GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb
  zero_mem' := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V
  smul_mem' := fun c _ ha => GlobalTheory.Mem.AutSpace.isAutFunSm_smul c ha

theorem isAutFunSm_of_mem_gkGen (hθ : IsInfFam θ) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, IsAutFunSm θ V f := by
  have hA : GlobalTheory.CuspGK.IsGKSub θ M (smAut θ V) :=
    ⟨fun τ g hg f hf => GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf τ g hg.1,
      fun τ X hX f hf => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf⟩
  exact fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := smAut θ V) hψ hA hf

theorem level_gkGen {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g := by
  obtain ⟨U, hU, hψU⟩ := hψ.level
  let A : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g}
      add_mem' := fun ha hb u hu hu' g => by simp only [Pi.add_apply, ha u hu hu' g, hb u hu hu' g]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c f hf u hu hu' g => by simp only [Pi.smul_apply, hf u hu hu' g] }
  have hA : GlobalTheory.CuspGK.IsGKSub θ M A := by
    refine ⟨fun τ g _ f hf u hu hu' x => ?_, fun τ X _ f hf u hu hu' x => ?_⟩
    · show f (x * u * atTau θ V τ g) = f (x * atTau θ V τ g)
      rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) hu',
        ← mul_assoc]
      exact hf u hu hu' _
    · have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hu' τ X f) x
      rw [show rTr V u f = f from funext (hf u hu hu')] at this
      exact this.symm
  exact ⟨U, hU, fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := A) (fun u hu hu' g => hψU u hu hu' g) hA hf⟩

theorem gelf_mem_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (τ : D.what₂.Tau) (k : ℕ) :
    ∀ f ∈ A, gelf θ V τ k f ∈ A := by
  intro f hf
  have hC : ∀ Z, ∀ g ∈ A, RderC θ V τ Z g ∈ A := fun Z g hg => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact A.add_mem (hA.lie τ _ h1 g hg) (A.smul_mem _ (hA.lie τ _ h2 g hg))
  have key : ∀ l : List ((GA D V → ℂ) → (GA D V → ℂ)), (∀ F ∈ l, ∀ g ∈ A, F g ∈ A) →
      l.foldr (fun F acc => F acc) f ∈ A := by
    intro l hl
    induction l with
    | nil => exact hf
    | cons F l ih => exact hl F (by simp) _ (ih fun F' hF' => hl F' (by simp [hF']))
  refine Submodule.sum_mem _ fun idx _ => key _ fun F hF => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hF
  exact hC _

end GlobalTheory.KTypeAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFinVecOfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

section Local

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

variable {e I}

end Local

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

end GlobalTheory.FlipPath

end
end

