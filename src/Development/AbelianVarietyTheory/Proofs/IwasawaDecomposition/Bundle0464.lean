module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
public import Formalism.LocalToGlobal.Columns.Bundle0038
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
public import Formalism.LocalToGlobal.Columns.Bundle0029
public import Formalism.LocalToGlobal.Columns.Bundle0039
public import Formalism.LocalToGlobal.Columns.Bundle0046
public import Formalism.LocalToGlobal.Columns.Bundle0044
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkEqcar
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainComparisonTransferOtherLaterStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem chT_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hS bb Φ rep Top c jA t jA' hjA
  have hP := (_root_.GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T Ks A R F y y' hS).2.1
  obtain ⟨htup, htupT, hPY, hPW⟩ := hS
  rcases y' with ⟨tup', tupT', tupT_tup', tup0', hm', hTop', hinj', PY', PW', ιW', isomFin', frameMatch', hF', stdPsi'⟩
  have e1 : tup' = (y.tup) := eq_of_heq ((htup))
  have e2 : tupT' = (y.tupT) := eq_of_heq ((htupT))
  subst e1 e2
  have e3 : jA' = (jA) := eq_of_heq ((hjA))
  subst e3
  have hCC := chain_CC b F y.tupT y.hm y.hTop
  have hCCX := chain_CCX b F y.tupT y.hm y.hTop
  have hCCP := chain_CCP b F y.tupT y.hm y.hTop
  have hCCXP := chain_CCXP b F y.tupT y.hm y.hTop
  have hEEc := chain_EEc b F y.tupT y.hm y.hTop
  letI := alg b iK
  refine ⟨{
    jE := (t.jE)
    jM := (t.jM)
    jX := (t.jX)
    jE_inj := (t.jE_inj)
    jE_range := by
      have e : LinearMap.range t.jE = _ := t.jE_range.trans (congrFun hEEc bb)
      exact (e)
    jE_ip := (t.jE_ip)
    jM_inj := (t.jM_inj)
    jM_range := fun μ hU j h1 h2 => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j ≤ a.D.R.m - 1 := (h2)
      have e : LinearMap.range (t.jM μa j) = _ := (t.jM_range μa hUa j h1 h2a).trans (congrFun (congrFun (congrFun hCCP bb) μa) j)
      exact (e)
    jM_ip := (t.jM_ip)
    jX_inj := (t.jX_inj)
    jX_range := fun μ hU => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have e : LinearMap.range (t.jX μa) = _ := (t.jX_range μa hUa).trans (congrFun (congrFun hCCXP bb) μa)
      exact (e)
    jX_ip := (t.jX_ip)
    io0 := fun μ hU x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa 1).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) 1
      have h0 : t.jM μa 1 va ∈ (y.C F).CC bb μa 1 := cast (congrArg (t.jM μa 1 va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) 0 (t.jM μa 1 va) ((h)) h0
      have e' := (t.io0 μa hUa x va h0).trans (congrArg (fun z => (y.C F).ipE bb (t.jE x) z) hv.symm)
      run_tac Lean.Elab.Tactic.withMainContext do
        let goal ← Lean.Elab.Tactic.getMainGoal
        let some decl := (← Lean.getLCtx).findFromUserName? `e' | throwError "missing proof"
        goal.assign (Lean.mkFVar decl.fvarId)
        Lean.Elab.Tactic.replaceMainGoal []
    io := fun μ hU j h1 h2 x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j + 1 ≤ a.D.R.m - 1 := (h2)
      let va : (c.Mult μa (j + 1)).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) (j + 1)
      have h0 : t.jM μa (j + 1) va ∈ (y.C F).CC bb μa (j + 1) := cast (congrArg (t.jM μa (j + 1) va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) j (t.jM μa (j + 1) va) ((h)) h0
      have e' := (t.io μa hUa j h1 h2a x va h0).trans (congrArg (fun z => (y.C F).ipP bb μa j (t.jM μa j x) z) hv.symm)
      run_tac Lean.Elab.Tactic.withMainContext do
        let goal ← Lean.Elab.Tactic.getMainGoal
        let some decl := (← Lean.getLCtx).findFromUserName? `e' | throwError "missing proof"
        goal.assign (Lean.mkFVar decl.fvarId)
        Lean.Elab.Tactic.replaceMainGoal []
    ioTop := fun μ hU x v v' hvv h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa a.D.R.m).T := (v)
      let va' : (c.Mult μa (a.D.R.m - 1 + 1)).T := (v')
      have hvva : HEq va' va := (hvv)
      have e := congrFun (congrFun hCCX bb) μa
      have h0 : t.jX μa (c.multTop μa va) ∈ (y.C F).CCX bb μa := cast (congrArg (t.jX μa (c.multTop μa va) ∈ ·) e.symm) ((h))
      have hv := chain_ioX b (R := R) y.hm y.hTop (y.tupT μa) (t.jX μa (c.multTop μa va)) ((topMult_tr b y.hTop)) ((h)) h0
      have e' := (t.ioTop μa hUa x va va' hvva h0).trans
        (congrArg (fun z => (y.C F).ipP bb μa (a.D.R.m - 1) (t.jM μa (a.D.R.m - 1) x) z) hv.symm)
      exact (e')
    junk := (t.junk)
    ft := fun π => by
      rw [eq_of_heq (hP bb (rep π))]
      exact (t.ft π)
    disj := fun π π' hne => by
      rw [eq_of_heq (hP bb (rep π)), eq_of_heq (hP bb (rep π'))]
      exact (t.disj π π' hne)
    top := (t.top) }, (HEq.refl t.jE), (HEq.refl t.jM), (HEq.refl t.jX)⟩

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  first | exact @GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | exact GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | (intros; apply GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.SymFrame.conj_symLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hpin hIs hplg hDiv heG ψ0 hψ0 π hπ red b hred hfix hw
  classical
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.Mem.SymFrameRed.symVec_red D X h hpin b (fun kv => (hfix kv).1) hw π
  obtain ⟨ψ', a, hψ'1, hchi⟩ := _root_.GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root D X h hpin hw
  have hsc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ d : Fin D.R.r → (ZMod (D.host.g kv.1))ˣ,
      ∀ u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), u ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k →
        ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * u.val i j else 0) =
          (ψ0 (plg kv)).compAddMonoidHom (iso kv).toAddMonoidHom
            (edgeSum (symEdge D.R.rS D.R.k) ((GlobalTheory.SeeConjRead.diagGL d)⁻¹ * u * GlobalTheory.SeeConjRead.diagGL d)) := by
    intro kv
    have := Fact.mk (D.host.g_prime kv.1)
    refine GlobalTheory.SeeConjScale.scale_conj (Field.toIsField _) D.R.rS D.R.k (ψ' kv) _ (hψ'1 kv) ?_ (a kv)
    intro h1
    apply hψ0 _ (plg kv).2
    ext y
    have := DFunLike.congr_fun h1 ((iso kv).symm y)
    simpa using this
  choose d hd using hsc
  let c : G0g D.nd := fun kv => P kv * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j))
  refine ⟨c, fun k hk => ?_⟩
  let Ns : G0g D.nd := fun kv => Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).toMonoidHom
    ((P kv)⁻¹ * red k kv * P kv)
  have hNs : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) = (((((P kv)⁻¹ * red k kv * P kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).submatrix π π := by
    intro kv
    ext i j
    simp [Ns, Matrix.reindex_apply]
  have hMat : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2)
      (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
    intro kv
    rw [hNs kv]
    exact GlobalTheory.Mem.SymFrame.isMatIn_perm _ k _ π (_root_.GlobalTheory.Mem.SymFrame.isMatIn_basisChange D X red b hfix kv (hw kv) (P kv) _ (hP kv) k hk)
  have hval : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) =
      Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) ≃+* kP (plg kv).1) : ZMod (D.host.g kv.1) →+* kP (plg kv).1)
        ((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) := by
    intro kv
    have e1 : (c⁻¹ * red k * c) kv = (GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) := by
      simp only [c, Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc]
    have e2 := heG (eR.symm (c⁻¹ * red k * c)) kv
    rw [MulEquiv.apply_symm_apply, e1] at e2
    apply Units.ext
    ext i j
    have e3 : ((reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) i j =
        ((R.eG (eR.symm (c⁻¹ * red k * c)) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) (π i) (π j) := by
      simp [reord, Matrix.reindex_apply]
    rw [e3, e2]
    show (iso kv) ((((GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (π i) (π j)) =
      (iso kv) (((((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j)
    rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, GlobalTheory.SeeConjRead.diagGL_conj_apply, hNs kv]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hmemiff : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k := by
    show _ ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    constructor
    · intro H kv
      have h1 := H (plg kv) (Set.mem_univ _)
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc] at h1
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).2 h1
    · intro H PP _
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc]
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).1 (H kv)
  have hK2 := _root_.GlobalTheory.Mem.GroupLoc.membership_iff_unipSym D X h hpin hw k hk Ns hMat
  refine ⟨hK2.trans hmemiff.symm, fun hx => ?_⟩
  have hU := hmemiff.1 hx
  have hk2 : k ∈ X.K2 := hK2.2 hU
  rw [hchi k hk2 Ns hMat hU]
  have hchiv : (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hx⟩ : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ψ0 PP.1 (edgeSum (symEdge D.R.rS D.R.k) (reord π (R.eG (eR.symm (c⁻¹ * red k * c))) PP)) := by
    have hp {α β ι : Type} [Monoid α] [CommMonoid β] (s : Finset ι)
        (f : ι → α →* β) (x : α) : (s.prod f) x = s.prod (fun i => f i x) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, ih]
    unfold PsharpSym LevelP.ofLocal at hx ⊢
    dsimp only at hx ⊢
    rw [hp, Units.coe_prod]
    rfl
  rw [hchiv]
  refine (Fintype.prod_equiv plg _ _ (fun _ => rfl)).symm.trans (Finset.prod_congr rfl fun kv _ => ?_)
  rw [hval kv, GlobalTheory.Mem.SymFrame.edgeSum_bc, hd kv _ (hU kv)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResiduesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  exact @GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem n1_span_unitary {D : D7} (z : unitary D.host.E) : TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) := by
  refine (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_iff_mul_conj (D := D) _).2 ?_
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.cS_span (D := D), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.span_singleton_mul_span_singleton_host (D := D)]
  have hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj (D := D)]
    exact Unitary.mul_star_self_of_mem z.2
  rw [hz, ← Submodule.one_eq_span]

end GlobalTheory.Mem.Col2.TC.RcHyp

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem n1_detStd (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {n : ℕ}
    {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 (I.rec7 l Z) (TaylorLogMetric.detId (I.rec7 l Z) (StandardLatticesGL3.stdL (I.rec7 l Z) n) N) := by
  have h := GlobalTheory.CharValCompare.normOne_detIdeal_transportedLattice (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hN
  rwa [seamOf_lat] at h


set_option maxHeartbeats 1000000 in
theorem jetsRat_chi (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (hJ : ColIn.JetsIn I)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (a : I.ι) (u : B.Word)
    (i : ℕ) (hi : i < B.R.m) :
    (I.J.amb B χ).JetsRatDeg (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (stepDeg (Pr := B.primes X) B.wts u i) := by
  intro N N' c x hx m hm
  have hf : Th.chiFac B.host χ (B.R.N i) (B.R.N (i + 1)) N N' = Th.chiFac B.host I.chi (B.R.N i) (B.R.N (i + 1)) N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (n1_detStd I l Z hx.1),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (n1_detStd I l Z hx.2.1)]
  have e3 : (I.J.amb B χ).e (B.R.N i) (B.R.N (i + 1)) N N' = I.A.e (B.R.N i) (B.R.N (i + 1)) N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x =
      I.A.thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  obtain ⟨y, hy⟩ := hJ a u i hi N N' c x hx m fun τ => by
    show ((degAt m τ : ℕ) : ℤ) = _
    rw [hm τ]
    exact chain_degree_eq B.fields (B.primes X) B.R B.wts u i hi τ
  refine ⟨y, ?_⟩
  rw [e4]
  exact hy.trans (by rw [show I.A.chiF (B.R.N i) (B.R.N (i + 1)) N N' = (I.J.amb B χ).chiF (B.R.N i) (B.R.N (i + 1)) N N' from hf.symm]; rfl)

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem idxMatNF_of_isTw (I : TC B X) (h : I.Ok) (ht : I.IsTw) (a : I.ι) : GlobalTheory.QNF.IdxMatNF (I.idx a) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hD := ht.deep
  have hK : TwCstQ (Pr := B.primes X) I.sel (I.tup a) I.glob :=
    twCstQ_of (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a) (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)
  have hN := twNormAt_all (twNormDC_of (unfoldingNonvanishingDoubleCoset_holds (Ch := I.Ch) I.glob hm hK)) (fun P _ => degOne_of_ok h a P)
  rw [ht.idx_eq a]
  intro j b v hv hj1 hj2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have H := twSt_cand (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (by omega) (hN i (by omega)) b v hv
  exact GlobalTheory.Proof.TwistedNormalForms.twNF_imp_matNF _ _ _ _ _ hv _ H.2.1

theorem evaluationDatum_ok_baseTuple (I : TC B X) (u : B.Word) :
    (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have := hX.cplxK
  exact GlobalTheory.CoreHt.evGSD_ok_of_eq_one B.fields hX (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup I.mu0) I.Ps u hPr I.trueColumn_tuple_trivial_eq_one

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}


set_option maxHeartbeats 1000000 in
theorem chTh_ok_chi (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hJ : ColIn.JetsIn I) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
    (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2)) := by
  obtain ⟨hX, hPr, hW, -⟩ := base_fields_primes_ok B X
  have hX1 : B.fields.AbelianUnramifiedExtensionConditions := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hL := h.idx_ok a
  have hs := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ0 : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hχ1 : TaylorLogMetric.IsChi (I.rec7 l Z) χ := by
    refine ⟨fun 𝔞 𝔟 h𝔞 h𝔟 => ?_, fun z => ?_⟩
    · rw [hχ _ h𝔞, hχ _ h𝔟, hχ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_mul (D := I.rec7 l Z) h𝔞 h𝔟)]
      exact hχ0.1 𝔞 𝔟 h𝔞 h𝔟
    · rw [hχ _ (n1_span_unitary (D := I.rec7 l Z) z)]
      exact hχ0.2 z
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have hg : XiOffG (B.primes X) (I.tup a : Chr B.fields.F B.fields.E B.fields.K) := xiOffG_of_mem hPr h.g_mem
  have hTies : LawTies B.wts I.Ch I.sel (I.tup a) (I.cst a) I.glob :=
    lawTies_of_ok B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hL hW ⟨I.C.eta, h.ch_tied⟩
  have hLa : ∀ i, (I.J.amb B χ).LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) := fun i => by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have hL0 := Formalism.L2.Ker.laHyp_ambOf_top (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) χ I.J.cD (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      hs hδ (he i) (he (i + 1)) ∅ (fun P hP => absurd hP (Finset.notMem_empty P)) (fun P hP => absurd hP (Finset.notMem_empty P))
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact ⟨hL0.1, hL0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
      (bad P hP).2.2.1 (by simp), hL0.2.2.2.2⟩
  have hSm : ∀ i, (I.J.amb B χ).ESmooth (B.R.N i) (B.R.N (i + 1)) := fun i => by
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact Formalism.L2.Ker.Cd.ambOf_eSmooth (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ I.J.δ_ne_zero (he i) (he (i + 1))
  have hRat := jetsRat_chi I l Z hJ χ hχ a u
  have hst : ∀ i, i < B.R.m → ThEquivP (stepT (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u i (B.wts.lamTrue u (i + 1)))
      (Sall (Pr := B.primes X) I.sel (I.tup a) u) (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u i).rho (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u (i + 1)).rho := fun i hi => by
    choose e he' using fun τ => (B.hc τ).e_int ⟨i, hi⟩
    have hLa' := hLa i
    have hRat' := hRat i hi
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G] at hLa' hRat' ⊢
    exact Cd.CarC.thEquivP_ambOf_tiesD (X := B.fields) (Pr := B.primes X) (R := B.R) (W := B.wts) (Ch := I.Ch) (sel := I.sel)
      (mu := I.tup a) (cst := I.cst a) (G := I.glob) u (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ hχ1 hX1 hPr h.sel_ok hg hTies
      (hPr.T_prime u).pos hi e (fun τ => (he' τ).symm) hLa' hRat'
  have hlaws := chThT_laws_of (Pr := B.primes X) (W := B.wts) (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (cst := I.cst a)
    (A := I.J.amb B χ) (u := u) hm hst
  have hTh : ThHypD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) := by
    refine ⟨fun i hi => ⟨hLa i, hSm i, hRat i (by omega)⟩, ?_, hlaws.1, hlaws.2⟩
    have e' : B.R.N B.R.m = B.R.N (B.R.m - 2 + 1 + 1) := by rw [← hm]
    rw [e']
    exact ⟨hLa _, hSm _, hRat _ (by omega)⟩
  exact chTh_ok_ambD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) (by omega) (hPr.T_prime u).pos
    (muqTie_of_ok I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) hL) hTh

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem hyps_of_isTw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.IsTw → ColIn.JetsIn I → ∀ (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) → ∀ (a : I.ι) (u : B.Word), (∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok) ∧ (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok ∧ GlobalTheory.QNF.IdxMatNF (I.idx a) ∧ ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps := by
  intro B X I h _ l Z ht hJ χ hχ a u
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact ⟨ht.chF_ok h B.wts a u, evaluationDatum_ok_baseTuple I u, idxMatNF_of_isTw I h ht a, fun b hY =>
    KerRat.kerEquivC (Pr := B.primes X) B.wts (I.J.amb B χ) u hX hPr h.sel_ok ⟨h.T_mem u, h.g_mem⟩ (h.idx_ok a) (h.sharp a)
      (chTh_ok_chi I h l Z hJ χ hχ a u) b hY⟩

end GlobalTheory.Mem.Col2.TC.RcHyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepGroupElementOfChartLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT


set_option maxHeartbeats 4000000 in
theorem exists_stepElt_of_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ (((K (chOf c)).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ' : B.LLˣ) : B.LL) ∧ ∀ (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb hchi κ
  obtain ⟨x, hxchi, ⟨q, hq⟩, hxκ⟩ := GlobalTheory.T.exists_levelElement_same_character_near_bad I hOk hPins l Z u a i hi bad Ch chOf K k hR c hchi κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  have hg := h3.1
  have hact := h3.2.1
  have hcos := h3.2.2
  refine ⟨κ', ⟨hg, hcos⟩, ?_, ?_⟩
  · rw [← hxchi]
    exact hR.chr c x κ' hg (hact ▸ hq)
  · intro P g hL
    obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' hg (hact ▸ hq) P
    obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
    exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) (fb P) _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
      (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) (hfb P).1 (hfb P).2

end GlobalTheory.Mem.Col2.AdT

end
end

