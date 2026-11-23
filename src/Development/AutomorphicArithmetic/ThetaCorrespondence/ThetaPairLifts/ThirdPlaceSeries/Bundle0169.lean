module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0167
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0531
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0116
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiStdEqConstMulLocXi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0166
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0528
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCFunOfFun0Fit
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_fun_of_fun0Fit_alt : ∀ Fld : GlobalTheory.BigTop.Fun.FldT, _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigTop.Fun.HasGrid @Fld b.pt CF) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 σ := by
  intro Fld h
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF 𝒜 σ hD hR hG => ?_⟩
  exact _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigTop.Fun.HasGrid @Fld p CF)
    (fun C CH _ _ _ p => (p.S false).FUN (p.N C CH))
    ((h CF hCF).imp fun Fm CH _ a hN =>
      ⟨0, le_rfl, _root_.GlobalTheory.BigTop.Fun.evPt_mono (a hN) fun _ _ _ _ _ b hg C _ => b hg C⟩) 𝒜 σ hD hR hG
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAtTypeTop
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000
namespace GlobalTheory.Fam.TopLoc
section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
theorem exists_atType_with_same_psi_and_phi_max (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) {row col} (hR : _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl) (n : Fin a.n)
    (hϖ : valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) :
    ∃ S' : SymData (a.G n).k (a.G n).s B.R.k, S'.ψ = (a.G n).S.ψ ∧ (S'.T (Fin B.R.t)).PhiTop = ((a.G n).S.T (Fin B.R.t)).PhiTop ∧
      ∀ (b : I.ι) (P : BadPr I b), P.1 = (a.pl n).1 →
        AtType I.Ch I.sel (I.tup b) (I.cst b) B.embLL P (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) S' := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain ⟨hid, hv⟩ := hR.idem n
  obtain ⟨hi, hd⟩ := SymChainAt.place_facts (a.G n).q hid
  have hPm : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  obtain ⟨i, g1, g2, -, g4, -⟩ := LevelData.type_prime hPm
  obtain ⟨ϖ, hϖq, -⟩ := LevelData.exists_unif (ι := (a.G n).q.pr.comp (incA (I.rec7 l Z))) hi hd (g1 ▸ g4)
  obtain ⟨S', e1, e2, e3, e4, e5⟩ := exists_normal_top (a.G n).S ϖ
    (by rw [hϖq, map_natCast, Valuation.map_sub_swap]; exact hϖ) B.R.t
  refine ⟨S', e2, e5, fun b P hP => ?_⟩
  obtain ⟨PP, hPP⟩ := P
  obtain rfl : PP = (a.pl n).1 := hP
  have ok := hW.tr.ok
  have hok := ok.idx_ok b
  have f1 : Formalism.L2.Col.psi0P I.Ch (a.pl n).1 = I.Ch.psi0 ⟨_, hPm⟩ := dif_pos hPm
  have f2 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 = Formalism.L2.Col.chiAt I.Ch ⟨_, hPm⟩ := dif_pos hPm
  refine ⟨hPm, hs.symm, hok.cst_ok, ok.sharp _, by rw [hW.tr.tw.cst_eq]; exact Nat.le_succ _,
    fun x hx => hok.psi0 ⟨_, hPP⟩ x hPm hx, ⟨hi, hd, rfl, e1 ▸ hϖq⟩, fun x hx => ?_, fun j x v h1 h2 h3 => ?_⟩
  · rw [e2]
    exact psi_tie (a.G n).q hv hi hd (g1 ▸ g2) (g1 ▸ g4) (hok.xiUnitAtPrime ⟨_, hPP⟩).1 (_root_.GlobalTheory.Fam.pk_z W).ψ W.Q.stdChar B.embLL _
      (fun z c h => f1 ▸ ok.weil ⟨_, hPm⟩ z c h) _ (a.G n).char x hx
  · rw [Formalism.L2.Col.LocE.unitV, dif_pos h2]
    by_cases hj : j < B.R.m
    · rw [e3 _ (by omega)]
      have key := chi_tie (a.G n).q hid hi hd (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta (j + 1)
        (c := (Units.map (B.embLL : B.fields.K →* ℂ)).comp (Formalism.L2.Col.chiP I.Ch (a.pl n).1 j)) (hW.tr.chr ⟨j, hj⟩)
        (fun y x c hx hy => Units.ext (by
          have h := hok.mu0G ⟨j, hj⟩ ⟨_, hPm⟩ x y c hx hy
          have e3 : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = I.Ch.chi ⟨j, hj⟩ ⟨_, hPm⟩ := (congrFun f2 j).trans (dif_pos hj)
          rw [e3]
          exact h.symm))
        W.Q.charW.base.lev.eta
        (fun y x c hx hy => ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr (a.pl n).1 _ (by
          have hy' : y ∉ (a.pl n).1.asIdeal := fun h => by
            haveI := (a.pl n).1.isPrime
            exact c.ne_zero (hy.trans (Ideal.Quotient.eq_zero_iff_mem.2 h))
          change Valued.v (((x : (I.rec7 l Z).host.E)) : (a.pl n).1.adicCompletion (I.rec7 l Z).host.E) = 1
          rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hx]
          exact ((a.pl n).1.valuation_eq_one_iff_notMem (K := (I.rec7 l Z).host.E)).2 hy')).symm)
        _ (hR.mu n (j + 1) (by omega) hj) x v h2.unit h1 rfl h3
      rw [key]
      rfl
    · rw [e4 _ (by omega), ((congrFun f2 j).trans (dif_neg hj) : Formalism.L2.Col.chiP I.Ch (a.pl n).1 j = 1)]
      simp
end Normal
theorem loc_top_common_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 1 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr hiA n j hj hjm
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  obtain rfl : j = (a.G n).s + 1 := by omega
  have hR := (hIs.tie (fun t => (GlobalTheory.Fam.TopLocFac.nonempty_rowCh (D := I.rec7 l Z) _ _ u a.g hTr.pinX.std t).some)
    fun t => (GlobalTheory.Fam.TopLocFac.nonempty_colCh (D := I.rec7 l Z) u _).some).2
  obtain ⟨S', hψ, hΦ, hAt⟩ := _root_.GlobalTheory.Fam.TopLoc.exists_atType_with_same_psi_and_phi_max hW a hR n (_root_.GlobalTheory.LevUnif.unif_of_gRead_alt W hW u a _ _ hR n)
  have hxi : ∀ yb, (S'.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) S'.ψ (a.G n).ν (-1) yb =
      ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1) yb := fun yb => by
    unfold Chain.xiTop
    rw [hΦ, hψ]
    rfl
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)))
      (e : GlobalTheory.StepData.Ix (Fin B.R.k ⊕ Fin ((a.G n).s + 1)) (Fin B.R.t) ((a.G n).s + 2) ⊕ Unit ≃ Fin (B.R.N B.R.m)),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd (Sum.elim GlobalTheory.SymBridge.zPos fun _ => B.R.N B.R.m - 1) e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (y : Formalism.L2.Col.HomE B.fields.E (B.R.N ((a.G n).s + 1)) (B.R.N B.R.m)) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
       (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : B.fields.E) * y' i)) →
       ((a.G n).S.T (Fin B.R.t)).xiTop (box _ (1 : (a.G n).kˣ)) (a.G n).S.ψ (a.G n).ν (-1)
           (Submodule.Quotient.mk fun r => _root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n (y' (e' r))) (GlobalTheory.SymBridge.toLoc (_root_.GlobalTheory.Fam.TopLoc.embeddingAtLocalFactor a n) e e' y) =
         C * B.embLL (GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P y y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hAt _ P₀ hP₀
      obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
      obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_topOrd B.R (a.G n).s hs
      obtain ⟨C, hC0, hC⟩ := (GlobalTheory.SymBridge.matchAtType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀).2.2 e'₀
        (e₀.trans (finCongr (congrArg B.R.N hs))) he'₀ (fun r => he₀ r)
      refine ⟨C, hC0, fun e' e he' he t P hP y y' hy => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀.trans (finCongr (congrArg B.R.N hs)) := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      have hA := hAt _ P hP
      have hPP : P₀.1 = P.1 := hP₀.trans hP.symm
      have hy₀ : ∀ i, Formalism.L2.Col.IntAt P₀.1 ((Formalism.L2.Col.qOf P₀.1 : B.fields.E) * y' i) := by rw [hPP]; exact hy
      refine ((congrFun (hxi _) _).symm.trans (hC y y' hy₀)).trans ?_
      exact congrArg (fun x => C * B.embLL x)
        (locTop_eq_of_type I.Ch I.sel _ _ _ _ P₀ P hPP hA₀.mem (hA₀.sharp.trans hA.sharp.symm) hA₀.psi0 hA.psi0 _ y y' hy₀)
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ => ⟨_root_.GlobalTheory.Fam.TopLoc.standardXi a n, _root_.GlobalTheory.Fam.TopLocFac.isLocFac_xiStd_alt W hW u a hIs hTr n, fun P hP z => ?_⟩⟩
  rw [_root_.GlobalTheory.Fam.TopFrames.xiStd_eq_const_mul_locXi_alt W hW u a hIs hTr hiA n t J hJ α γ P hP C (fun e' e he' he y y' hy => hC e' e he' he t P hP y y' hy) hj z,
    ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
end GlobalTheory.Fam.TopLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCommonVacua
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CommonVac
end GlobalTheory.CommonVac
namespace GlobalTheory.CommonVac
theorem exists_common_vacua_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, _root_.GlobalTheory.Fam.CommutingVectorTie (⟨mkGeo m b, j, row, col⟩ : _root_.GlobalTheory.Fam.FamilyCharacter W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  intro D L hT Gi Gl Kc Yd cX ex W u hpk a y m b v hc hτ hNT hgP hTy hb hbT hLT hmT hN hvb hvbT htP
  have hQ : ∀ p ∈ v.gP, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D p ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = p), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = p) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = p)) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = p) = GlobalTheory.FinPl.latV V Λ (· = p)) := by
    intro p hp
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact _root_.GlobalTheory.T.type_places_split_idempotents_alt W hpk hTy PP hPP
  have hY : ∀ j, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, j + 1 < D.R.m →
      GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True)
        (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)))) ∧
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (b j, b (j + 1))
        (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) 1)) ≠ 0 := by
    intro j
    by_cases hj : j + 1 < D.R.m
    · obtain ⟨M, hM, hMv⟩ := _root_.GlobalTheory.T.exists_selfDual_lattice_moves W hpk j (by omega) (b j)
      obtain ⟨M', hM', hM'v⟩ := _root_.GlobalTheory.T.exists_selfDual_lattice_moves W hpk (j + 1) hj (b (j + 1))
      obtain ⟨hvac, hnz⟩ := _root_.GlobalTheory.T.self_dual_lattices_consecutive_step_alt W hpk j hj (b j) (b (j + 1)) (hb j) (hb (j + 1)) M M' hM hM' hMv hM'v
      obtain ⟨o, ho, hoV⟩ := _root_.GlobalTheory.VacRebase.rebase_vac D (_root_.GlobalTheory.Fam.pk_z W).ψ hc.std (Yc D j) (Yc D (j + 1)) M (v.N j) M' (v.N (j + 1)) v.gP hM
        (hN j (by omega)).1 hM' (hN (j + 1) hj).1 hQ (fun p hp =>
          ⟨latV_eq_of_moves (hMv (· = p)) ((hN j (by omega)).2 (· = p) (fun p' hp' => hp' ▸ hp)),
            latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp))⟩)
      have hv1 := hvac 1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      simp only [one_mul] at hv1
      exact ⟨o, fun _ => ⟨ho, fun P x hx x' hx' => (hoV _ (hvac P x hx x' hx')).1, (hoV _ hv1).2 hnz⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose O hO using hY
  have hTs : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ o : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ, GlobalTheory.FinPl.CombAt (· ∈ v.gP) o ∧
      (∀ P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True)
        (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)))) ∧
      comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) 1)) ≠ 0 := by
    intro j h
    have hj : j + 1 < D.R.m := by omega
    obtain ⟨M', hM', hM'v⟩ := _root_.GlobalTheory.T.exists_selfDual_lattice_moves W hpk (j + 1) hj (b (j + 1))
    obtain ⟨hvac, hnz⟩ := _root_.GlobalTheory.T.self_dual_lattices_top_step_alt W hpk j h (b (j + 1)) a.bT (hb (j + 1)) hbT M' a.LT hM' hLT hM'v hmT
    have hNT' : IsSelfDualC D.sp.X' v.NT := hNT ▸ hLT
    obtain ⟨o, ho, hoV⟩ := _root_.GlobalTheory.VacRebase.rebase_vac D (_root_.GlobalTheory.Fam.pk_z W).ψ hc.std (Yc D (j + 1)) D.sp.X' M' (v.N (j + 1)) a.LT v.NT v.gP hM'
      (hN (j + 1) hj).1 hLT hNT' hQ (fun p hp =>
        ⟨latV_eq_of_moves (hM'v (· = p)) ((hN (j + 1) hj).2 (· = p) (fun p' hp' => hp' ▸ hp)), by rw [hNT]⟩)
    exact ⟨o, ho, fun P => (hoV _ (hvac P)).1, (hoV _ (hvac 1)).2 hnz⟩
  choose OT hOT using hTs
  refine ⟨fun j P x x' => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (O j) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (x * b j, x' * b (j + 1)) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)),
    fun j h P => comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (OT j h) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (b (j + 1), a.bT) (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)),
    fun j hj P x hx x' hx' => (hO j hj).2.1 P x hx x' hx', fun j h P => (hOT j h).2.1 P, ?_⟩
  intro j' row col
  exact {
    b := fun j => by rw [hvb]
    bT := ⟨hvbT, hNT⟩
    gP := hgP
    tP := htP
    moves := fun j hj P hP => (hN j hj).2 P hP
    movesT := hmT
    Ψ := fun j hj => ⟨O j, (hO j hj).1, fun P x x' => rfl⟩
    ΨT := fun j h => ⟨OT j h, (hOT j h).1, fun P => rfl⟩
    nz := ⟨fun j hj => ⟨1, by simpa only [one_mul] using (hO j hj).2.2⟩, fun j h => ⟨1, (hOT j h).2.2⟩⟩ }
end GlobalTheory.CommonVac
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIntegralMultipleHolds
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Filter Asymptotics
namespace GlobalTheory.BigTop.Fun
theorem existsIntegralMultiple_holds_alt : _root_.GlobalTheory.BigTop.Fun.ScaleCondition := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := exists_log_le_two_rpow he
  refine ⟨x0, fun x hx hle i p _ => ?_⟩
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hx
  have hZx : p.Z.x = x := hsx
  have hZb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  show 1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
  rw [hZx, hZb, Real.log_exp]
  have h1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1.le he.le
  exact ⟨hx1.le, h1, by linarith [hx0 x hle]⟩
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FockVecEqSum
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FockVecSum
theorem fockVec_eq_sum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t j, j + 1 < D.R.m → ∀ [Fintype (_root_.GlobalTheory.Fam.complexLevelStructure W).H], ∃ κ : (_root_.GlobalTheory.Fam.complexLevelStructure W).H → GA D (Yc D j), (∀ p, κ p ∈ levS (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W))) ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) ((_root_.GlobalTheory.Fam.pk_z W).vac j) v → ∀ Q, pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) v Q = ∑ p, (levChi (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) (κ p))⁻¹ • ((_root_.GlobalTheory.Fam.pk_z W).ωY t j (κ p, 1)) ((_root_.GlobalTheory.Fam.pk_z W).ptY t j Q) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW t j hj _
  have hC := hW.bot.hyp.2.2.2.1
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hC.lev
  have hj' : j < D.R.m := Nat.lt_of_succ_lt hj
  have hlift := GlobalTheory.ChainEquiv.lifts_chain (_root_.GlobalTheory.Fam.pk_z W).toLevCh W.P.A3.A.μ0 hL t j hj'
  choose κ hκ using fun p : (_root_.GlobalTheory.Fam.complexLevelStructure W).H => hlift p.1
  refine ⟨κ, fun p => ⟨(hκ p).1, (hκ p).2.1, (hκ p).2.2 ▸ p.2⟩, fun v hv Q => ?_⟩
  obtain ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩ := GlobalTheory.StepVecLaw.levRes_chrStep hL t ⟨j, hj'⟩
  obtain ⟨c, hc⟩ := hL.βY j hj'
  obtain ⟨c', hc'⟩ := hL.βY (j + 1) hj
  have hω := hC.chain.ωY t j hj
  have hvY := hC.chain.vY t j hj
  have hsum := GlobalTheory.StepVecSum.stepVec_eq_sum D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) (Yc D (j + 1)) _ _ ((_root_.GlobalTheory.Fam.pk_z W).ωY t j) _ _
    ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) v hω
    (D.sp.Y_sig _) (D.sp.Y_sig _) (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY j))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hj'))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (j + 1) hj)) hc.1 hc'.1 D.R.r D.R.t j (r_le_Y j)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj'.le]; rfl)
    (by rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj.le]; rfl)
    (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) (_root_.GlobalTheory.levCh_unramified_places D _ _ _ hL t).1 (_root_.GlobalTheory.Fam.pk_z W).chi ((_root_.GlobalTheory.Fam.pk_z W).xiR t) (_root_.GlobalTheory.Fam.complexLevelStructure W) hvY hv
    (fun PP hP => ⟨a1 PP hP, b1 PP hP⟩) (fun PP hP => ⟨a2 PP hP, b2 PP hP⟩) a3 b3 κ hκ
  have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hvY.1.2.inf
  have hf : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vY t j) := by
    have := hC.chain.ptY t j hj 1
    rwa [RealDat.ptY, GlobalTheory.FiniteFock.pureTensorO_one] at this
  rw [hsum, GlobalTheory.SpecFac.pureTensorO_sum hω.std hθ _ _ _ _ Finset.univ _ _ (fun p _ => hω.om_pres _ _ hf)]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hk := GlobalTheory.FiniteFock.compAt_mt_of_finite (_root_.GlobalTheory.Fam.pk_z W).θ
  refine ((GlobalTheory.OrientedHeis.om_pureTensorO D _ _ _ _ _ _ _ hω hθ _ _ _ _ _ _ _ _ (κ p) 1
    (fun τ => by rw [hk τ (hκ p).1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hk τ (hκ p).1, Matrix.one_mul])
    (fun τ => by rw [hk τ (one_mem _), Matrix.one_mul]) _ hf Q).2).symm
end GlobalTheory.FockVecSum
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrsFMemGlintRedVEq
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
namespace GlobalTheory.Fam.LevelFrames
set_option maxHeartbeats 1000000 in
theorem frsF_mem_glint_redV_eq_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (t : W.P.T) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (j : ℕ), j + 1 ≤ B.R.m → ∀ (β : J.Ch₀ j) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
    Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N j) P.1 ∧
    ∀ x ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1, Formalism.L2.Col.redV P.1 (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P x) = Formalism.L2.Col.redV P.1 x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ _ n t J hJ j hj β P hP
  letI := GlobalTheory.Mem.Col2.starE B
  have hPv : P.1 ∈ (B.primes X).vGs := hP ▸ (hW.lev.2.1 _).1 (a.pl n).2
  refine ⟨?_, fun x hx => redV_eq_of_near (fun r s => ?_) hx⟩
  · have e : Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 P = (J.A.p0 j β).1.1.deco.1.liftFr ⟨P.1, hPv⟩ :=
      dif_pos hPv
    have h := (GlobalTheory.TopStep.liftFr_spec (J.A.p0 j β).1.1.deco.2 ⟨P.1, hPv⟩).1
    have hN := (hJ.is.base j (by omega) β).2
    rw [e]
    intro x
    refine Iff.trans ?_ (h x)
    exact Iff.of_eq (congrArg (fun N => _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N) hN.symm)
  · rcases hj.eq_or_lt with h | h
    · exact _root_.GlobalTheory.Fam.TopFrames.valuation_frs_sub_kronecker_lt_one hW hJ P hPv h β r s
    · have key := MidLoc.frame_cong hW.tr.ok (J.A.p0 j β).1.1 (hJ.std j h β ▸ (hJ.is.base j (by omega) β).1) P hPv r s
      rwa [if_congr Fin.ext_iff rfl rfl] at key
end GlobalTheory.Fam.LevelFrames
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpbOfLamLow
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
noncomputable section
namespace GlobalTheory.BigTop.Fun.IPbProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end GlobalTheory.BigTop.Fun.IPbProof
namespace GlobalTheory.BigTop.Fun
open GlobalTheory.BigTop.Fun.IPbProof
theorem ipb_of_lamLow_alt : _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound := by
  intro hL
  refine ⟨0, ?_⟩
  intro CF hCF
  refine hL.imp ?_
  intro eps Fm CH heps h hdiv
  refine ⟨max 0 (max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3))), fun C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 9, fun x hx hle i p hp d _ => ?_⟩
  have h6 := hx0 x hx (le_of_max_le_left hle) i p hp C
  have hC0 : 0 ≤ C := (le_max_left _ _).trans hC
  have hC1 : max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3)) ≤ C := (le_max_right _ _).trans hC
  have hb : 1 ≤ p.Z.b := one_le_b (Fm.L x i)
  have hlb : Real.log p.Z.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by rw [← hlb]; exact Real.log_nonneg hb
  set P5 := Fm.params x hx i
  have hS := Fm.sizes x hx i
  have hx9 : 9 ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact le_of_max_le_right hle
  have hLp := Formalism.L2.DIV.Arith4S.Lp_le_La (Fm.L x i) p.Del p.h0 P5 hS hx9
  rw [Formalism.L2.DIV.ofRecord_La, Fm.params_CYL x hx i, Fm.Ct_eq x i] at hLp
  have hLa := La_le_three (Fm.L x i) hS
  have hY : 0 < Fm.CYL := (Fm.params_CYL x hx i) ▸ P5.CYL_pos
  set c : ℝ := 3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3) with hc
  have hc0 : 0 ≤ c := by have := le_max_right Fm.Ct 5; rw [hc]; linarith
  set Lp := (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).Lp
  have hLp0 : 0 ≤ Lp := Formalism.L2.DIV.NumDatum.Lp_nonneg _
  have hLp3 : Lp ≤ 3 * c * (Fm.L x i).sc.L := by nlinarith
  have hNV : ((Fm.D x i).R.nV : ℝ) ≤ (d.O.N : ℝ) := by
    have hm := (Fm.D x i).R.two_le_m
    have h1 : (Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1 ≤
        (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (Fm.D x i).R.nV ≤ d.O.N := by
      show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t ≤
        (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)
      omega
    exact_mod_cast h2
  have hf0 : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnv0 : (0 : ℝ) ≤ ((Fm.D x i).R.nV : ℝ) := Nat.cast_nonneg _
  have hsq : ((Fm.D x i).R.nV : ℝ) ^ 2 ≤ (d.O.N : ℝ) ^ 2 := pow_le_pow_left₀ hnv0 hNV 2
  have hA0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp := by positivity
  have hA : ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp ≤
      ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L) := by
    gcongr
  have hB0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by positivity
  have hcs : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
      3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by
    have e1 : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    have e2 : max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L)) :=
      mul_le_mul_of_nonneg_left hA (le_max_right _ _)
    have e3 : max Fm.Csz 0 * c * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤
        C * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) :=
      mul_le_mul_of_nonneg_right hC1 hB0
    nlinarith
  refine GlobalTheory.InfinitePlacesProbe.clauseB_of_lifts (p.S false) (p.S true) (p.N C CH) d.O hC0 hb ⟨rfl, rfl, rfl⟩ h6
    (by simp; rfl) fun j => ?_
  have hm0 : 0 ≤ ∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ :=
    Finset.sum_nonneg fun ρ _ => Real.log_natCast_nonneg _
  have e : (p.N C CH).l6 j = (∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ) -
      Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) - C * 0 := rfl
  rw [e, hlb]
  show -(3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ _
  linarith
end GlobalTheory.BigTop.Fun
end
end
end

