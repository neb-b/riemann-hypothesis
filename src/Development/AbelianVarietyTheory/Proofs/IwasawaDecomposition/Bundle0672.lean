module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCoset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAuxiliaryHeckeCharacterToricListOfGridAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridLambdaData

theorem isAuxiliaryHeckeCharacter_toricListOfGrid : ∀ (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (sc : GlobalTheory.ChiGrid.Consts) (G : GlobalTheory.ChiGrid.GridData L sc) (w0 : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0 → ∀ a : Fin D.R.m, GlobalTheory.LamTie.IsAuxiliaryHeckeCharacter D.host (G.pl.w G.pl.v0) ((GlobalTheory.BigTop.Fun.lamOf G).c a) ((GlobalTheory.BigTop.Fun.lamOf G).chi a) := by
  intro D T L sc G _ _ a
  have hw0 : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hS1 : ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.LamTie.Over4 D.host w → w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D := by
    intro w h
    rw [GlobalTheory.ChiGrid.S1_mem_OmF]
    rcases h with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · exact Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)
      · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk))
    · exact Or.inr (Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
    · exact Or.inr (Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_under hk)))
  have hOv : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ GlobalTheory.ChiGrid.S1 D → GlobalTheory.LamTie.Over4 D.host w := by
    intro w h
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl ⟨0, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inl ⟨1, GlobalTheory.BigTop.Fun.natCast_mem_of_under h⟩
    · exact Or.inr (Or.inl (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
    · exact Or.inr (Or.inr (GlobalTheory.BigTop.Fun.natCast_mem_of_under h))
  have a1 : 1 ≤ a.1 + 1 := by omega
  have a2 : a.1 + 1 ≤ D.R.m := a.2
  refine ⟨GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ a1 a2), G.ch.triv _ a1 a2,
    GlobalTheory.BigTop.Fun.lamOf_hasInfQ G a, fun w h4 h0 => ?_, fun w h4 => ?_, fun w he => ?_⟩
  · refine G.ch.unr _ a1 a2 w fun hw => ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hw with h | h
    · exact h0 (h.trans hw0.symm)
    · exact h4 (hOv w h)
  · obtain ⟨l2, l1⟩ := G.ch.lev1 _ a1 a2 w (hS1 w h4)
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 1) l2 l1
  · have e : w.under (𝓞 D.host.F) = G.pl.v0 :=
      (show w.under (𝓞 D.host.F) = (G.pl.w G.pl.v0).under (𝓞 D.host.F) from he).trans hw0
    obtain ⟨l1, l0⟩ := G.ch.lev0 _ a1 a2 w e
    exact GlobalTheory.LamTie.GridCharacters.expAt_succ (n := 0) l1 fun h => l0 (((G.ch.chiH _).unrAt_iff w).2 h)

end GlobalTheory.GridLambdaData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

section TopLevProof

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsExist_top (R : RealDat D A Ks) (hl : R.toLevCh.Is A.μ0) (t : T) (g0 : G0 R.Pg D.R.r) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ := by
  obtain ⟨c, hc⟩ := hl.βX
  exact _root_.GlobalTheory.ParahoricLift.liftsExist D.sp.X' R.βX (R.datXt t) _ _ hc (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).1
    (GlobalTheory.ChainEquiv.places_sep R.toLevCh _ hl t).2 g0


set_option maxHeartbeats 2000000 in
theorem topLev_of_clauses (R : RealDat D A Ks) (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hc : R.IsChain)
    (hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j)) : TopLev R F := by
  intro b t y hy
  have hm : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  have hrel : ∀ p : (R.levR F b).H, GlobalTheory.ChainEquiv.Rel R t p (D.R.m - 1) (R.ioX t y)
      ((((R.levR F b).chi p : ℂˣ) : ℂ) • R.ioX t y) := by
    intro p
    have hL := liftsExist_top R hl t (p : G0 R.Pg D.R.r)
    refine hL.elim fun κ' hκ' => ?_
    intro κ hκ v g
    have hF : ∀ w h, (((((R.levR F b).chi p : ℂˣ) : ℂ) • y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w h =
        (levChi _ R.βX (flagL (R.datXt t)) κ')⁻¹ * (y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w (h * κ') := by
      intro w h
      have hT : HasType D.sp.X' R.βX (withP (R.datXt t) (R.levR F b)) ((y : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) :=
        (GlobalTheory.ChainEquiv.multT_value _ _ _ _ _ hy w).2
      rw [← GlobalTheory.KeepLevel.eigen_of_hasType hT p hκ' h]
      rfl
    have key := GlobalTheory.ChainEquiv.step R.ψ R.θ hM.inf _ _ (R.ωX t) (hc.ωX t) _ _ _ _ (R.vX t) (hc.ptX t) (R.MY (D.R.m - 1))
      (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) rfl _ (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).1 _
      (GlobalTheory.ChainEquiv.meas_chain hM.νY hM.νY' t _ hm).2
      (hS t _ hm) R.ItX (hc.ItX t).ne _ (GlobalTheory.ChainEquiv.range_left R.cX R.prX (R.HX t) _ _ (hM.HX t).2.1) R.βX (R.datXt t) _
      (hM.νX t).1.1 _ (hM.νX t).2 (R.ioX t) (hc.ioX t) (p : G0 R.Pg D.R.r) κ hκ (p : G0 R.Pg D.R.r) κ' hκ' _
      (_root_.GlobalTheory.StepLaw.last_step_law R hl hM.inf hc.ωX hc.vX t (p : G0 R.Pg D.R.r) κ κ' hκ hκ') y _ hF v g
    have e := (R.ioX t).map_smul (((R.levR F b).chi p : ℂˣ) : ℂ) y
    exact (congrArg (fun U : R.CC t (D.R.m - 1) => (U : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) v g)
      e).symm.trans key
  have hU := (GlobalTheory.KeepLevel.mem_lvlPart_iff (R := R) (R.levR F b) t (D.R.m - 1) (R.ioX t y)).2 hrel
  exact (mem_multT R.θ (R.MY (D.R.m - 1)) _ _ _).2 hU

end TopLevProof


set_option maxHeartbeats 2000000 in
theorem topLev_holds : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH
  exact topLev_of_clauses R.toRealDat F.lv2 hP.char.base.lev hP.char.base.models
    (RealDat.chain_of_weak hP.char.base.chain hH.aux.ex)
    (fun _ _ _ => GlobalTheory.MultFinite.schurMult hC.2.2.2.2 _ _)

end GlobalTheory.Mem.R3.DTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem mem_sgL_iff (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (PP : Pl X.toD7.host.E) :
    PP ∈ sgL X I U t ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t := by
  rw [hL.Pg, hL.Q t, Col2.ColIn.Q, tup_ixOf I t]
  classical
  exact Finset.mem_union

theorem isSplitSet_sgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  intro X px I U L _ hL t PP h PP' h' hc
  have hc' : Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP PP' := fun c hm =>
    ⟨Formalism.DivisionValues.cO X.toD7.host.E c, (hc c (Formalism.DivisionValues.cO X.toD7.host.E c) rfl).1 hm, rfl⟩
  exact GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL.is t ((mem_sgL_iff X I U L hL t PP).1 h)
    ((mem_sgL_iff X I U L hL t PP').1 h') hc'

end GlobalTheory.Mem.R3.LiftBrg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTransla
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))
    (d : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG)) :
    (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowProjHolds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

theorem rowProj_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.RowProj R.toRealDat F.lv2 := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hPins hHolds
  have hb := hPins.char.base
  intro b t w hw
  have h1 := GlobalTheory.KeepLevel.goodProjector_levelMultiplicitySpace_mem_goodRows hb.lev hb.models.inf hb.grp.record (R.toRealDat.levR F.lv2 b) t hw
  refine ⟨h1, fun c hc => ?_⟩
  have hcfix : postOn (R.MY 0) R.e0 c = c := sub_eq_zero.1 (LinearMap.mem_ker.1 hc.2)
  have hc0 : c ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    have := GlobalTheory.Mem.Th.multAt_le R.toRealDat (R.toRealDat.levR F.lv2 b) t 0 ((GlobalTheory.Mem.Th.multAt_zero R.toRealDat _ t).symm ▸ hc.1)
    rwa [GlobalTheory.Mem.Th.multAt_zero] at this
  have hw0 : w ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    have := GlobalTheory.Mem.Th.multAt_le R.toRealDat (R.toRealDat.levR F.lv2 b) t 0 hw
    rwa [GlobalTheory.Mem.Th.multAt_zero] at this
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec (R.MY 0) (GlobalTheory.GardingVec.sm_ne_bot D _ _ (R.MY 0))
  have ha : 0 < (RealDat.nP F.lv2 b)⁻¹ := inv_pos.2 (GlobalTheory.KapRedII.nP_pos' F.lv2 b)
  rw [GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ ha v hv, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ ha v hv]
  congr 1
  conv_lhs => rw [← hcfix]
  exact GlobalTheory.ProjectorAdjoint.ipM_gaL (L := R.dat0 R.triv) hP hb.models.inf hb.models.ν0.1.1 hb.models.ν0.2 R.eG _
    (GlobalTheory.ProjectorAdjoint.eC_inv R.toRealDat hb.grp.record) hc0 hw0

end GlobalTheory.Mem.R3.DTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_operators_lifts_doubleCoset : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).A.heckeL i t)
      (fun x => 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank) (LiftBrg.envL X I hX U Xg tr L cV i t).isT
      (LiftBrg.envL X I hX U Xg tr L cV i t).isLoc) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | exact GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie <;> assumption)
end

