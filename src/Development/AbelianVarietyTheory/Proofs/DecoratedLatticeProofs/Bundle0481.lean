module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroChar

theorem map_conj_local {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {β : GL (Fin (c.V 0).rank) (Lev.EAf D)} {b : GA D (c.V 0)}
    {π' : Lev.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a) {n : GA D (c.V 0)}
    {q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k}
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q)
    (σ : Fin (c.V 0).rank → XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (hσ : Function.Bijective σ)
    (hM : MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 (G.s + 1) (Nat.zero_add _)).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix id σ)) :
    ((β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β).val).map π' =
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix σ σ := by
  set F := G.FY 0 (G.s + 1) (Nat.zero_add _) with hF
  set B := (G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _) with hB
  set p := ofSplit G.q with hp
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo p F (π' := π') hπ B.val σ hM
  have hfin : ∀ g : GA D (c.V 0), (finE (c.V 0) g).val.map π' = (mt (c.V 0) g).map p.π := by
    intro g
    rw [GlobalTheory.LevSplit.finE_val]
    ext i j
    exact hπ _
  have hBB : (B⁻¹).val * B.val = 1 := Units.inv_mul B
  have hmt : ∀ g h : GA D (c.V 0), (mt (c.V 0) (g * h)).map p.π = (mt (c.V 0) g).map p.π * (mt (c.V 0) h).map p.π :=
    fun g h => Matrix.map_mul
  have ht1 : (mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π = 1 := by
    rw [← hmt, mul_inv_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set W := (mt (c.V 0) b⁻¹).map p.π * F.β * B.val with hW
  set W' := (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π with hW'
  have hWW : W' * W = 1 := by
    rw [hW, hW']
    calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π * ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
        = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht1, Matrix.mul_one, F.γβ, Matrix.mul_one, hBB]
  have hβ' : β.val.map π' = W.submatrix id σ := by
    rw [hβ]; rfl
  have hinv : (β⁻¹).val.map π' = W'.submatrix σ id := by
    refine Matrix.left_inv_eq_left_inv (A := β.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [hβ', ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hWW]
      exact Matrix.submatrix_one_equiv (Equiv.ofBijective σ hσ)
  have hn : (mt (c.V 0) n).map p.π = F.β * q.val * F.γ := hloc.2
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv, hfin, hβ', hmt, hmt, hn]
  have hs : ∀ (X : Matrix (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (Fin (c.V 0).rank) G.k)
      (Mid : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) G.k)
      (Z : Matrix (Fin (c.V 0).rank) (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k),
      X.submatrix σ id * Mid * Z.submatrix id σ = (X * Mid * Z).submatrix σ σ := fun X Mid Z => Matrix.ext fun i j => rfl
  rw [hs]
  congr 1
  rw [hW, hW']
  calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π *
        ((mt (c.V 0) b⁻¹).map p.π * (F.β * q.val * F.γ) * (mt (c.V 0) b).map p.π) *
        ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
      = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * q.val *
        (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
        simp only [Matrix.mul_assoc]
    _ = (B⁻¹).val * q.val * B.val := by simp only [ht1, Matrix.mul_one, F.γβ]


set_option maxHeartbeats 1000000 in
theorem psi_red_at {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Pl D.host.E) (b : GA D (c.V 0))
    (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) (hL : GlobalTheory.LevZero.LocAt G PP b β) (hr : D.R.r ≤ (c.V 0).rank) (n : GA D (c.V 0))
    (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k) (p : ℕ) (hq : q ∈ GlobalTheory.RootEx.N G.k _ (G.s + 1) p)
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q) (hS : finE (c.V 0) (b⁻¹ * n * b) ∈ St β)
    (hblk : redFn β PP (finE (c.V 0) (b⁻¹ * n * b)) ∈ blockTri (blk2 D.R.r)) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * n * b))))) :
    (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) = (G.S.ψ (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  obtain ⟨π', hπ, hred, -, -⟩ := _root_.GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  have hσ : Function.Bijective (fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm i)) :=
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _))).bijective
  have hmat := map_conj_local G hπ hloc _ hσ hM
  obtain ⟨y, hy⟩ := hS
  have hI : β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β = intGL _ _ _ y := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  rw [hI] at hmat
  rw [← hy, redFn_frGL] at hz hblk
  unfold edgeSum at hz
  rw [upper_block_val_submatrix hr hblk] at hz
  have hrk : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hN := (GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq
  have hsum : (∑ i : Fin D.R.r, ∑ j : Fin D.R.r, if GlobalTheory.chainEdge D.R.k i j then
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val)
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q :=
    GlobalTheory.NChainChar.edge_sum_typeFrame D.R.k D.R.t G.s (c.V 0).rank D.R.r p hr hrk e he G.S.ϖ q hN
  set w : Formalism.L2.Herm.intAf D.host.F D.host.E := ∑ i : Fin D.R.r, ∑ j : Fin D.R.r,
    if GlobalTheory.chainEdge D.R.k i j then y.val (Fin.castLE hr i) (Fin.castLE hr j) else 0 with hw
  have hres : resS D.host.F PP w = Ideal.Quotient.mk PP.asIdeal z := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hker := (hred.ker (w - Formalism.L2.DIV.oToS D.host.F D.host.E z)).1 (by
    rw [map_sub, hres, Formalism.L2.DIV.resS_oToS, sub_self])
  have hpw : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) w = (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · have := congrFun (congrFun hmat (Fin.castLE hr i)) (Fin.castLE hr j)
      exact this
    · exact map_zero _
  have hpz : π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have hv : ValuativeRel.valuation G.k ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) < 1 := by
    have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w - Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        -((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) := by
      rw [map_sub, hpw]
      rw [show (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) from rfl, hpz]
      ring
    rw [h1, Valuation.map_neg] at hker
    exact hker
  have hone : G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q)) = 1 := by
    refine (G.S.cond _).2 ?_ _ le_rfl
    have h5 := (G.S.unif _).1 hv
    have h6 : ValuativeRel.valuation G.k (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k)) = ValuativeRel.valuation G.k ((1 : G.kˣ) : G.k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  have e2 : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E) =
      ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) +
        GlobalTheory.RootEx.simpleSum q := by
    have : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k) = 1 := by rw [Units.inv_mul]
    linear_combination (GlobalTheory.RootEx.simpleSum q) * this
  rw [e2, AddChar.map_add_eq_mul, hone, one_mul]

theorem levChi_eq_psiBes : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  intro D c v cm st b G h0 hB PP n q hq hloc hlev
  obtain ⟨hr, ξ, hL⟩ := hB.mem.lev
  have hL' : st.L = Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B := hL
  have hl := hlev.2
  rw [hL'] at hl
  change finE (c.V 0) (b⁻¹ * n * b) ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  have hP : (fun PP : cm.Pg => upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))) ∈ cm.P.H := hl.2
  have hchi : levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = ((cm.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
    rw [hL']
    unfold levChi levFn
    rw [extendOne_of_mem _ hl.2]
    have e1 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).s = 0 := rfl
    have e2 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).Q = ∅ := rfl
    simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    rfl
  rw [hchi]
  choose x hx using (hB.grp _).1 hP
  rw [hB.chr ⟨_, hP⟩ x hx, Units.coe_prod, Finset.prod_eq_single PP]
  · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := PP.1.asIdeal)
      (edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))))
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP) PP.1 (hB.loc PP).idem (x PP) _ (hx PP) z hz]
    rw [psi_red_at (G PP) PP.1 b st.β (hB.loc PP) hr n q _ hq hloc hl.1.2.1 (blockTri_blkOf_le _ _ (hl.1.2.2.1 PP.1 PP.2)) z hz]
    rw [GlobalTheory.LocBesChar.psiBes_isLoc D (G PP).k (ofSplit (G PP).q) c.ψ (G PP).S.ψ (G PP).char D.R.rS
      (c.B 0 D.R.rS h0) ((G PP).sc 0) _ ((G PP).s + 1) ((G PP).FX 0 (by omega)) ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _))
      ((G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)) n q hq hloc]
  · intro PP' _ hne
    obtain ⟨e, he⟩ := hB.com.split
    have h1 := GlobalTheory.NChainChar.redFn_conj_eq_one he PP.2 (hB.loc PP).idem hloc.1 b hl.1.2.1 PP'.2
      (fun h => hne (Subtype.ext h).symm)
    have h2 : Ideal.Quotient.mk PP'.1.asIdeal (0 : 𝓞 D.host.E) = edgeSum (GlobalTheory.chainEdge D.R.k)
        (upperLeftBlock hr (redFn st.β PP'.1 (finE (c.V 0) (b⁻¹ * n * b)))) := by
      rw [h1, map_zero]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [Units.val_one, Matrix.one_apply_ne]
        intro e; rw [e] at hij; exact absurd hij.1 (by omega)
      · rfl
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP') PP'.1 (hB.loc PP').idem (x PP') _ (hx PP') 0 h2]
    simp [GlobalTheory.LocMod.Place.pr]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LevZeroChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacMove
variable {D : D7}

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact GlobalTheory.FinPl.MovedVac.smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem mem_latO_iff_actO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) (u : WO S T) :
    u ∈ latO S T (Λ : Set _) (Λ' : Set _) P ↔ actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  refine ⟨actO_mem_latO hΛ hM hΛ' hM' hg hh, fun hu => ?_⟩
  have := actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

end GlobalTheory.VacMove

namespace GlobalTheory.VacMove

theorem isThetaAt_moveLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Λ M : Lat S) (Λ' M' : Lat T), IsSelfDualC S Λ → IsSelfDualC S M → IsSelfDualC T Λ' → IsSelfDualC T M' → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, Moves S b Λ M (fun _ => True) → Moves T b' Λ' M' (fun _ => True) → ∀ e Φ f₀ f, e * e = e → infPart D e = 0 → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  intro D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b _ b' _ hb hb' e Φ f₀ f hee hinf hf₀ _ hf
  have key := mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := mem_latO_iff_actO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.VacMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastPt


set_option maxHeartbeats 4000000 in
theorem kernel_eq_sum : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  intro D c v χ Q hc hv h hr hτ s₁ hχ X₁ X₂ h₁ h₂ α S hS d₁ d₂ hd₁ hd₂
  classical
  have hs := Q.hs
  have hsc : Q.sc Q.s ≠ 0 := Q.sc_ne Q.s
  obtain ⟨T₁, hT₁, hX₁⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D Q.k Q.q Q.unit _ _ _ _ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 rfl) c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd Q.s (by omega)) (hv.sd (Q.s + 1) (by omega)) (Q.latY _ _ _) (Q.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (_root_.GlobalTheory.LocMod.indicator_vac D Q.k Q.q Q.unit _ _ _ _ (Q.FY (Q.s + 1) 0 rfl) Q.FT c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd (Q.s + 1) (by omega)) hv.sdT (Q.latY _ _ _) Q.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D Q.k (ofSplit Q.q) _ 0 (Q.sc Q.s) hsc).1 (c.B Q.s 0 h)
    (Q.FX Q.s (by omega))).1
  have hjac := Q.jac Q.s 0 h 0 (by omega)
  obtain ⟨U₁, hU₁, hfl⟩ := _root_.GlobalTheory.FlatBFLoc.flatBF_of_laws D (_root_.GlobalTheory.Unf.Flat.flatLaw D) (_root_.GlobalTheory.FinPl.flatLaws_all D) (_root_.GlobalTheory.LocOm.omLoc D) Q.k (ofSplit Q.q) Q.ν Q.unitVol.1
    c.ψ Q.ψk Q.char 0 (c.B Q.s 0 h) (c.J Q.s 0 h) s₁ (Q.sc Q.s) hsc _ _ 0 (Q.FX Q.s (by omega)) F₀
    (Q.FY Q.s (0 + 1) (by omega)) (Q.FX (Q.s + 1) le_rfl) (Q.FY (Q.s + 1) 0 rfl) hF₀ (Q.bes Q.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, hres, hext⟩ := GlobalTheory.LevelLast.splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit Q.q) c.ψ (c.jac Q.s 0 h).d (Q.FX (Q.s + 1) le_rfl)
    (Q.FY (Q.s + 1) 0 rfl) Q.FT hjac.2.1 T₂ hT₂
  let Φ₁ : SB _ := ⟨_, Q.reg.1 Q.s 0 rfl⟩
  let Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) :=
    ⟨om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl), om_mem_SB _ _ _ (Q.reg.1 Q.s 0 rfl)⟩
  let Φ₂ : SB _ := ⟨_, Q.reg.2.1⟩
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1))⟩
  let Ψα : SB _ := ⟨_, ((GlobalTheory.LocFlat.flat_SB_onto Q.k Q.ψk Q.ν Q.cond.continuous Q.unitVol.1 _ _ 0 (0 + 1) le_rfl).1
    le_rfl).1 _ Φα.2⟩
  obtain ⟨Y₂, hY₂⟩ := hres Φ₂
  have a₁ : comb c.ψ _ _ (Q.eL Q.s) X₁ = T₁ Φ₁ := by
    rw [← hX₁ O₁ rfl]
    exact ((Q.eL_at Q.s 0 rfl).2 T₁ hT₁ O₁ Φ₁ rfl rfl).symm
  have a₂ : comb c.ψ _ _ Q.eLT X₂ = T₂ Φ₂ := by
    rw [← hX₂ O₂ rfl]
    exact (Q.eLT_at.2 T₂ hT₂ O₂ Φ₂ rfl rfl).symm
  have a₃ := _root_.GlobalTheory.QPl.exchange_posOne_last D c v χ Q hc h s₁ hχ α T₁ hT₁ Φ₁ Φα rfl rfl
  have b₁ : flatBF s₁ (T₁ Φα) = U₁ Ψα := hfl Φα Ψα rfl
  have b₁' : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol (Q.X (Q.s + 1)) (Q.X Q.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext Φ₂ Y₂ hY₂
  have b₂' := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[Q.k]) ↔
        ∀ r (q : Q.X (Q.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[Q.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  rw [a₁, a₂, a₃, ← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
  unfold Comm.lst
  rw [b₁, b₁', b₂, b₂']
  obtain ⟨Λ, hΛ, hK⟩ := _root_.GlobalTheory.LastKerLoc.lastLoc D Q.k (ofSplit Q.q) Q.ν Q.unitVol.1 c.ψ hc.std Q.ψk Q.char 0 (c.B Q.s 0 h) (c.X (Q.s + 1))
    (c.X (Q.s + 1 + 1)) c.T c.Lz (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hr hτ (Q.sc Q.s) Q.z₀ hsc (Q.tau h) _ _ _
    (Q.FX Q.s (by omega)) F₀ (Q.FX (Q.s + 1) le_rfl) Q.FT Q.FM hF₀ Q.last U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Ψα Y₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁' O₂'
  have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
  haveI := Q.unitVol.1
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
  let P₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s)⟩
  let P₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.Z ⊕ Unit) (Q.X (Q.s + 1))⟩
  let E₁ := fun yb => (⟨_, (_root_.GlobalTheory.QPl.LastTwo.entries_mem_SB D c v χ Q α yb).1⟩ : SB _)
  let E₂ := fun yb => (⟨_, (_root_.GlobalTheory.QPl.LastTwo.entries_mem_SB D c v χ Q α yb).2⟩ : SB _)
  let E := fun yb => (⟨fun q => (E₁ yb).1 q.1 * (E₂ yb).1 q.2, GlobalTheory.FinPl.Comm.prod_mem_SB (E₁ yb).2 (E₂ yb).2 (s := id)
    continuous_fst continuous_snd continuous_id fun _ => rfl⟩ :
      SB (Matrix (Q.X (Q.s + 1)) (Q.X Q.s) Q.k × Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k))
  have hsum : Ξ = ∑ yb ∈ S, E yb := Subtype.ext (funext fun q => by
    have e : (fun y => Ψα.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = Q.T.Psi (Q.rep Q.s 0 rfl α) q.1 :=
      funext fun y => GlobalTheory.LevelLast.flCol_one _ _ _ _
    rw [hΞ q, hY₂, e, (GlobalTheory.Couple.psi_eq_sum_coupIdx Q.k Q.s Q.X Q.Z Q.T Q.A Q.c₁ Q.c₂ Q.adapt Q.ψk Q.cond.continuous Q.ν (-1) S hS
      _ ((Q.rep_bij Q.s 0 rfl).mapsTo (Set.mem_univ α)) q.1).2, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun yb _ => mul_left_comm _ _ _)
  have hone : ∀ q, Ξ'.1 q = P₁.1 q.1 * P₂.1 q.2 := fun q => by
    have e : (fun y => O₁'.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        P₁.1 q.1 * cosetInd (box _ (1 : Q.kˣ)) (Submodule.Quotient.mk 0) y :=
      funext fun y => GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [hΞ' q, e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int Q.cond Q.unitVol hv1]
    simp only [P₂, O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  refine Eq.trans (funext hΞK) ?_
  show Λ Ξ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun yb _ => ?_
  refine ((_root_.GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) c.ψ _ _ _).1 _ _ _ _ _ _ Λ (d₁ yb) (d₂ yb) (E₁ yb) P₁ (E₂ yb) P₂ (E yb) Ξ' hΛ
    (hd₁ yb) (hd₂ yb) rfl rfl (fun _ => rfl) hone).trans ?_
  exact congrArg _ (funext hΞ'K).symm

end GlobalTheory.QPl.LastPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentativeDiamondTranslateSumScalarForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.rd_dia_sum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y (c : {c // A.chOf j c = b}), (∑ᶠ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s))) = (∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c.1 (φ ((I.fm l u a).dil j v s c.1))) y := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj φ hφ i v hv g hg b y c
  obtain ⟨e, he⟩ := _root_.GlobalTheory.AdForm.DiaChart.ptOf_gl_dia I hok hpins l Z u a Ch A hA k ι p β Q L hT j hj i v hv g hg b c
  have hs : ∀ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s)) =
      (I.fm l u a).dilT j v (e s) c.1 (φ ((I.fm l u a).dil j v (e s) c.1)) y := by
    intro s
    obtain ⟨z, hz, hpt⟩ := he s
    have hG : A.h j b c * (β j i).gl (g s) ∈ GfC _ := mul_mem (hA.h j hj b c).1 (GlobalTheory.FrameGfCImg.gl_mem_GfC (β j i) (g s))
    have hch : A.chOf j ((I.stp u a j).cl c.1.1 (((I.atIn u a).A j).diaPt v (e s) c.1)) = b :=
      (GlobalTheory.AdForm.chOf_dil I hok hpins l Z u a Ch A hA j hj v (e s) c.1).trans c.2
    have hco : cosetIn (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1) =
        cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1.1 (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1))) :=
      (GlobalTheory.Mem.Col2.DiaChart.cosetIn_dia _ v (e s)).trans (GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v (e s) c.1).symm
    exact _root_.GlobalTheory.AdForm.rd_trTo I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b c.1 _ _ z hG hz hpt hch hco y
  rw [finsum_congr hs]
  rw [finsum_comp_equiv e (f := fun s' => (I.fm l u a).dilT j v s' c.1 (φ ((I.fm l u a).dil j v s' c.1)) y)]
  rw [finsum_apply]
  exact Set.toFinite _
end

