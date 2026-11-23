module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0066
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FractionToIntegralSectionSmulEq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDvdOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ → IsTypeAt θ V τ S φ := by
  first | exact @GlobalTheory.ClosureSeries.closure_to_series | exact GlobalTheory.ClosureSeries.closure_to_series | (intros; apply GlobalTheory.ClosureSeries.closure_to_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ChosenFormsRestrictBasisFunctionField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.HeightDefinite.Basis

open GlobalTheory.SectionBasis


open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem basis_descends_record {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hB : InBasis G la)
    {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
    (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z) {Dd N : ℕ} (hD : Dd = WeightFamilies.dimY D j) (e : Fin G.N ≃ Fin (N + 1))
    (j0 : ι → Fin (N + 1)) (v : ∀ Z, Fin G.N → Ω Z) (hvF : ∀ Z k, gF Z (X.inc wL (G.w k)) = v Z k)
    (x : ∀ Z, Fin N → Ω Z) (hv : ∀ Z, v Z (e.symm (j0 Z)) ≠ 0)
    (hx : ∀ Z k, x Z k = v Z (e.symm ((j0 Z).succAbove k)) / v Z (e.symm (j0 Z)))
    (hind : ∀ Z, AlgebraicIndependent B.KO (sImg (D := Dd) (j0 Z) (x Z)))
    (hfin : ∀ Z, FiniteDimensional (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N))
    (g0 : B.Cusp j wF) (θ : Fin G.del → ∀ Z, Ω Z) (hθ : ∀ k Z, gF Z (X.inc wF (G.th' k)) = θ k Z)
    (g : ∀ Z, Ω Z) (hgF : ∀ Z, gF Z (X.inc wF g0) = g Z) (hg : ∀ Z, g Z ≠ 0)
    (E : letI : ∀ Z, Module (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w ⧸
          Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w)) := fun Z =>
        ((Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))).comp
          (algebraMap (Kp X la G.N) (RZs X la G.N (Ω Z) (gF Z) G.w))).toModule
      SectionSheafQuotient X la G.w wF ≃ₗ[Kp X la G.N] ∀ Z, RZs X la G.N (Ω Z) (gF Z) G.w ⧸
                           Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (hE : ∀ (F : B.Cusp j wF) Z, E (resF G la F) Z *
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF g0)))) =
        Ideal.Quotient.mk (Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
          (lwZ X la G.N (Ω Z) (gF Z) G.w (algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF F))))) :
    ∑ Z, Module.finrank (IntermediateField.adjoin B.KO (Set.range (sImg (D := Dd) (j0 Z) (x Z))))
      (OmS (Ω Z) Dd N) = G.del ∧
    (∀ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO,
      (∀ Z, ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z) = 0) → ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Ω Z) Dd N, ∃ q : MvPolynomial (TVar Dd N) B.KO, (∀ Z, sHom (j0 Z) (x Z) q ≠ 0) ∧
      ∃ p : Fin G.del → MvPolynomial (TVar Dd N) B.KO, ∀ Z, sHom (j0 Z) (x Z) q * y Z =
        ∑ k, sHom (j0 Z) (x Z) (p k) * algebraMap (Ω Z) (OmS (Ω Z) Dd N) (θ k Z / g Z)) := by
  let iK : Algebra B.KO (Kp X la G.N) :=
    ((algebraMap (X.Kl la) (Kp X la G.N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la G.N) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨h1, h2⟩ := coords_of_equiv _ (tL G la) hB.1 hB.2 E
  refine basis_descends_loc (Kl := X.Kl la) hD e j0 v x hv hx hind hfin _ (GlobalTheory.CurveRecord.tv_indep X la G.N)
    (fun Z i => rzMap X la G.N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la G.w i))
    (fun Z i => by rw [GlobalTheory.CurveRecord.rzMap_sec_eq]; simp only [hvF])
    (fun Z => Ideal.map (phiZ X la G.N (Ω Z) (gF Z) G.w) (Jid X la G.w))
    (fun Z => GlobalTheory.CurveRecord.map_Jid_eq X la G.N (Ω Z) (gF Z) G.w) _ (fun _ _ => rfl) θ g hg
    (fun k Z => E (tL G la k) Z) (fun k Z => ?_) h1 h2
  have := hE (G.th' k) Z
  rw [lwZ_alg, lwZ_alg, rzMap_emb, rzMap_emb, hgF, hθ] at this
  exact this


open ReciprocityTheory.ChartRestriction.G.T0 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem chosenForms_basis_of_value_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) {n : ℕ}
    (θ : Fin n → ∀ Z : Comp Xo c, Om Z) (g : ∀ Z : Comp Xo c, Om Z) (hg : ∀ Z, g Z ≠ 0) (eδ : Fin d.del ≃ Fin n)
    (h1 : ∀ p : Fin n → MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z) = 0) →
        ∀ k, p k = 0)
    (h2 : ∀ y : ∀ Z, OmS (Om Z) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, sHom (d.jc Z) (d.x Z) q ≠ 0) ∧
      ∃ p : Fin n → MvPolynomial (TVar d.D d.N) c.F, ∀ Z, sHom (d.jc Z) (d.x Z) q * y Z =
        ∑ k, sHom (d.jc Z) (d.x Z) (p k) * algebraMap (Om Z) (OmS (Om Z) d.D d.N) (θ k Z / g Z))
    (sel : Fin d.del → Fin d.np)
    (hsel : ∀ i Z, d.thp (sel i) Z = AddMonoidAlgebra.single d.wF (θ (eδ i) Z)) : A4Selection d sel := by
  refine ⟨fun Z => AddMonoidAlgebra.single d.wF (g Z), fun Z => ⟨mem_AG.2 ⟨_, rfl⟩, by simpa using hg Z⟩,
    fun p hp k => ?_, fun y => ?_⟩
  · have := h1 (fun k => p (eδ.symm k)) (fun Z => by
      rw [← hp Z, ← eδ.sum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsel, ratio_single _ _ _ (hg Z), eδ.symm_apply_apply]
      rfl) (eδ k)
    exact (congrArg p (eδ.symm_apply_apply k)).symm.trans this
  · obtain ⟨q, hq, p, hp⟩ := h2 y
    refine ⟨q, hq, fun k => p (eδ k), fun Z => (hp Z).trans ?_⟩
    rw [← eδ.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsel, ratio_single _ _ _ (hg Z)]
    rfl


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem chosenForms_restrict_basis_functionField : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → CurveHyp h j hj hG ka wL wF G S g0 → InBasis G la → ∃ eδ : Fin d.del ≃ Fin G.del, ∀ sel : Fin d.del → Fin d.np, (∀ i, d.thp (sel i) = valC hG (wtA wF) wF.n (G.th' (eδ i)).1) → d.wF = wtZ (wtA wF) wF.n → A4Selection d sel := by
  intro D T h j hj hG ka wL wF G S g0 la _ d e hD hw hb hH hB
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hA1 := independent_differentials_ratios_cusp_forms_trdeg D T h j hj hG ka wL wF G d e hD hw hb hH.2.1.2
  have hS := fun Z => GlobalTheory.genericSection_field (D := d.D) (d.jc Z) (d.x Z) (hfg Z) ((htr Z).trans (by rw [hD])) (hA1 Z)
  have hg := GlobalTheory.CurveRecord.evC_ne_zero h j hj hG hT (GlobalTheory.Reg.genValInj_record D T h j hj hG)
    (GlobalTheory.Reg.compSplit_record D T h j hj hG) G hH.2.1 g0 hH.2.2.2
  obtain ⟨⟨E, hE⟩, -⟩ := GlobalTheory.SectionProduct.tieS D T h j hj hG ka wL wF G hT S g0 la hH hB
  have hw' : ∀ i Z, d.w i Z = AddMonoidAlgebra.single (wtZ (wtA wL) wL.n) (evC hG Z (G.w (e.symm i)).1) := by
    intro i Z
    have := congrFun (hw (e.symm i)) Z
    rwa [e.apply_symm_apply] at this
  have hq : ∀ Z, evC hG Z (G.w (e.symm (d.jc Z))).1 ≠ 0 := by
    intro Z h0
    apply hb Z
    rw [hw', h0]
    simp
  have hx : ∀ Z k, d.x Z k =
      evC hG Z (G.w (e.symm ((d.jc Z).succAbove k))).1 / evC hG Z (G.w (e.symm (d.jc Z))).1 := by
    intro Z k
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.x
    rw [hw', hw']
    exact ratio_single _ _ _ (hq Z)
  obtain ⟨h0, h1, h2⟩ := basis_descends_record (recPlus h j hj) la G hB (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) hD e d.jc (fun Z k => evC hG Z (G.w k).1)
    (fun Z k => formsEvR_inc h j hj hG hT Z wL (G.w k)) d.x hq hx (fun Z => (hS Z).1) (fun Z => (hS Z).2.1) g0
    (fun k Z => evC hG Z (G.th' k).1) (fun k Z => formsEvR_inc h j hj hG hT Z wF (G.th' k))
    (fun Z => evC hG Z g0.1) (fun Z => formsEvR_inc h j hj hG hT Z wF g0) hg E hE
  have hdel : d.del = G.del := h0
  refine ⟨finCongr hdel, fun sel hsel hF => ?_⟩
  exact chosenForms_basis_of_value_basis d (fun k Z => evC hG Z (G.th' k).1) (fun Z => evC hG Z g0.1) hg (finCongr hdel) h1 h2 sel
    (fun i Z => by rw [hsel, hF]; rfl)

end GlobalTheory.HeightDefinite.Basis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.XiFun

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CharRead


set_option maxHeartbeats 1000000 in
theorem exists_sec_char_val (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → FnAlgClosed (Xo := Xo) (c := c) → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → (∀ h : GA D V, ∃ a : c.F, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (h))) : ℂˣ)) → ∃ f ∈ sec Xo c 0 0, (∀ m : ℕ, (∀ h : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V (h))) ^ m = 1) → f ^ m = 1) ∧ (∀ y : FrPt Xo c (CAt σ), ∃ a : c.F, evR Xo c f y = algebraMap c.F (CAt σ) a) ∧ ∀ h γ : GA D V, MarkBy U V hr dict io F ik φ h γ → rdU U f (dict h).1 (dict h).2 = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
  intro hio hpos hA hgood hW hD hdom hcl xi h1 h2 h3
  subst hr
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have htr : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hD.1.1 k a b, hG k, (hW k).2]
  have key : ∀ h γ h' γ', MarkBy U V rfl dict io F ik φ h γ → MarkBy U V rfl dict io F ik φ h' γ' →
      ik (dict h).1 = ik (dict h').1 → xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) =
        xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) := by
    intro h γ h' γ' hm hm' hi
    refine xi_eq_of_index F V io hio.emb _ _ hi _ _ _ _ (SetLike.ext' (hm.2.1.trans (Set.image_id _)))
      (SetLike.ext' (hm'.2.1.trans (Set.image_id _))) (φ _) (φ _) _ ?_ (htr _) (htr _) hm.2.2 hm'.2.2 xi h1 h2
    rw [← (hW (dict h).1).2]
    exact neg_ne_zero.2 (U.X _).ξ0_ne
  have hv : ∀ i : Fin F.n, ∃ a : c.F, (∃ u : GA D V, σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V u)) : ℂˣ)) ∧
      ∀ h γ, MarkBy U V rfl dict io F ik φ h γ → ik (dict h).1 = i →
        σ a = (xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) := by
    intro i
    by_cases hex : ∃ h γ, MarkBy U V rfl dict io F ik φ h γ ∧ ik (dict h).1 = i
    · obtain ⟨h, γ, hm, hi⟩ := hex
      obtain ⟨a, ha⟩ := h3 (γ * h)
      exact ⟨a, ⟨_, ha⟩, fun h' γ' hm' hi' => by rw [ha, key h γ h' γ' hm hm' (hi.trans hi'.symm)]⟩
    · obtain ⟨a, ha⟩ := h3 1
      exact ⟨a, ⟨_, ha⟩, fun h γ hm hi => absurd ⟨h, γ, hm, hi⟩ hex⟩
  choose v hv1 hv2 using hv
  obtain ⟨f, hf, hf1, hf2⟩ := GlobalTheory.T.exists_weightZero_section_of_periodSpace_function D.host.E H Dw l Xo c σ g _ F hpos hgood
    ((_root_.GlobalTheory.Relab.relab_good _ H l c σ hgood).2.2.2 Dw g e) hA hcl v
  refine ⟨f, hf, fun m hm => hf1 m fun i => σ.injective ?_, fun y => ?_, fun h γ hm => ?_⟩
  · obtain ⟨u, hu⟩ := hv1 i
    rw [map_pow, map_one, hu, ← Units.val_pow_eq_pow_val, hm u, Units.val_one]
  · obtain ⟨i, P, hP, hx⟩ := F.onto y.x y.x_over
    exact ⟨v i, hf2 y i P hP hx.symm⟩
  · obtain ⟨Pm, -, hP, hx, -⟩ := hD.1.2 (dict h).1 ⟨(dict h).2, hdom h⟩
    rw [← hv2 _ h γ hm rfl, ← hf2 _ _ Pm hP hx]
    exact dif_pos (hdom h)

theorem evR_ne_zero_of_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f f' : Rul Xo c) (m : ℕ) (hm : 0 < m)
    (hf : f ^ m = 1) (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k) (h : evR Xo c f' y ≠ 0) :
    evR Xo c f y ≠ 0 := by
  unfold evR evalAt at h ⊢
  split_ifs at h ⊢ with hy
  · intro h0
    have h1 := congrArg (· ^ m) h0
    simp only [zero_pow hm.ne'] at h1
    rw [← map_pow, ← Pi.pow_apply, ← Pi.pow_apply, hf] at h1
    simp at h1
  · exact h

variable {D : D7}

theorem normOne_det (V : HSp D) (h : GA D V) : NormOne (D := D) (Matrix.GeneralLinearGroup.det (finHom V h)) := by
  have h1 := GlobalTheory.RecDict.det_finHom_norm V h
  have h2 : ∀ z : AfE D, barF D z = sigR (Af D.host.F) D.sp.cm.sig z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  unfold NormOne
  rw [h2, Matrix.GeneralLinearGroup.val_det_apply]
  exact h1

theorem det_rat (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ a : D.host.E, ((Matrix.GeneralLinearGroup.det (finHom V γ) : (AfE D)ˣ) : AfE D) = 1 ⊗ₜ a := by
  obtain ⟨γ', h⟩ := exists_isRat_of_mem_GQ V hγ
  refine ⟨γ'.1.det, ?_⟩
  unfold IsRat at h
  have : (finHom V γ).1 = ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom.comp
      (incA D)).mapMatrix γ'.1 := by
    unfold finHom
    rw [MonoidHom.comp_apply, h]
    rfl
  change (finHom V γ).1.det = _
  rw [this, ← RingHom.map_det]
  rfl

theorem FO_le_of_pins (Q : Par D) (h : Q.Pins) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have := h.2.2.1 (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at this
  have e : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := this
  rw [e]
  exact (Q.eO.symm y : Q.c.F).2

theorem iotaOK_of_latIsom (Q : Par D) (h : Q.Pins) (j : ℕ) (hj : InR D j) (V : HSp D) (hV : V = D.sp.W j)
    (ι : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (h1 : LatEmb V ι) (h2 : LatIsom V (Q.Dw j).EF ι) :
    IotaOK (Q.Dw j) V ι := by
  subst hV
  obtain ⟨ε, hε⟩ := h2
  let s : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (D.sp.W j).V := (D.sp.W j).frame.equivFun.symm
  have hs : ε = 1 := by
    refine sign_eq_one D Q.H (Q.Dw j) j hj h.1.2.1 h.1.2.2.1 (h.2.2.2 j hj).1 (h.2.2.2 j hj).2.1
      ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) ε (s.injective.comp h1.1) ?_ hε
    have e1 : Set.range ((s.toLinearMap.restrictScalars (𝓞 D.host.E)) ∘ₗ ι) =
        s.toLinearMap '' (latG (D.sp.W j) 1 : Set _) := by
      rw [← h1.2, LinearMap.coe_range, ← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, (_root_.GlobalTheory.Member.latG_lattice_and_completion D _ 1).2.1, Submodule.map_top, LinearEquiv.range]
  subst hs
  exact ⟨h.1.2.1, h.1.2.2.1, h1, fun x y => by simpa using hε x y⟩


set_option maxHeartbeats 1000000 in
theorem exists_fun_xiAt : ∀ (D : D7) (J : CoreJ D), LawsJ J → ∀ j, InR D j → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)) (d : DeltaDat (J.Q.Xo j) J.Q.c 0) (xi : (AfE D)ˣ →* ℂˣ), CoverOK d p I → FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) → XiOK D p xi → ∃ f : Rul d.Xo₂ d.c₂, CoverOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) p I ∧ RootOK ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) ∧ XiAt J j ({ d with cδ := f } : DeltaDat (J.Q.Xo j) J.Q.c 0) xi := by
  intro D J hJ j hj p I d xi hd hcl hxi
  obtain ⟨hp, hI, hlev, hA, hnab⟩ := hd
  have hg := J.toCore.good_σ₀
  have hpin := hJ.pins
  obtain ⟨hr, -, -, -, -, -, -, hemb, hisom, -⟩ := hJ.adPin j hj _ hg
  have hio := iotaOK_of_latIsom J.Q hpin j hj _ (hJ.spaceW j hj _ hg) _ hemb hisom
  have hpq := (exists_iotaOK D J.Q hpin j hj).2
  have hpos : 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q := by omega
  have hσ : d.c₂.F.val.toRingHom = J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ (J.σ₀.comp (d.eF.symm : d.c₂.F →+* J.Q.c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨hr', hW⟩ := hJ.modelW j hj _ hg
  have hU := hJ.unf j hj _ hg
  let k₀ := (J.dict j J.σ₀ 1).1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D J.Q.H (J.Q.Dw j) d.l₂ d.Xo₂ d.c₂ _ _ D.R.r hr _ hio hpos hA hg₂).2.2
    (J.x₀ j J.σ₀) (fun τ hτ => by
      have h1 := hJ.familyUniformisationBasePointOrthogonal j hj _ hg k₀ τ (((hU.2.1 k₀).2 τ).2 hτ)
      rwa [(hW k₀).1, (hU.2.1 k₀).1] at h1)
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (J.V j J.σ₀) d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  have hM : d.l₂.M = D.host.g 0 * D.host.g 1 * p := by rw [hlev.2.1, hpin.2.1.1, hp]
  obtain ⟨m, hm, hxm⟩ := hxi.fin
  obtain ⟨f, hf, hfm, hfv, hfx⟩ := exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => hxi.tame _ (normOne_det _ u) (by
      rw [← hM]; unfold CongOne; rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu))
    (fun γ hγ => by
      obtain ⟨a, ha⟩ := det_rat _ γ hγ
      exact hxi.rat _ a ha (normOne_det _ γ))
    (fun h => ⟨⟨_, d.hF.symm ▸ FO_le_of_pins J.Q hpin (hxi.val _ (normOne_det _ h))⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m fun h => hxm _ (normOne_det _ h)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨hp, hI, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hA, hnab⟩, ⟨⟨m, hm, hfm'⟩, ?_⟩, ?_⟩
  · exact evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · change ∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F,
      evR d.Xo₂ d.c₂ f y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a
    rw [hσ]
    exact hfv
  · refine ⟨hr, fun _ => C.unf un, fun _ => dict, 1, ⟨1, one_pos, one_pow 1⟩, fun _ => ⟨hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩⟩
    · rw [← hCι, ← hCx]
      exact hdl
    · rw [one_mul]
      rw [← hCι] at hmk
      exact hfx h γ hmk

end GlobalTheory.XiFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberIn

theorem finite_mem {K : Type} [Field K] [NumberField K] {a : 𝓞 K} (ha : a ≠ 0) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | a ∈ 𝔭.asIdeal}.Finite := by
  have h : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  refine (Ideal.finite_factors h).subset ?_
  intro 𝔭 h𝔭
  exact Ideal.dvd_span_singleton.2 h𝔭

theorem finite_norm_mem {K : Type} [Field K] [NumberField K] (S : Finset ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.absNorm 𝔭.asIdeal ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 K) | Ideal.absNorm I ≠ 0 ∧ Ideal.absNorm I ∈ S}.Finite := by
    refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (S.sup id)).subset ?_
    intro I hI
    exact Finset.le_sup (f := id) hI.2
  refine (h.preimage (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro 𝔭 h𝔭
  exact ⟨fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), h𝔭⟩

theorem numberField_adjoin (K L : IntermediateField ℚ ℂ) [NumberField L] (S : Set ℂ)
    [NumberField (IntermediateField.adjoin K S)] : NumberField (IntermediateField.adjoin L S) := by
  have h1 : FiniteDimensional ℚ ((IntermediateField.adjoin K S).restrictScalars ℚ) :=
    (inferInstance : FiniteDimensional ℚ (IntermediateField.adjoin K S))
  have hle : IntermediateField.adjoin ℚ S ≤ (IntermediateField.adjoin K S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin K S)
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have h3 : FiniteDimensional ℚ ((IntermediateField.adjoin L S).restrictScalars ℚ) := by
    have e := IntermediateField.restrictScalars_adjoin_eq_sup ℚ L S
    have h5 : FiniteDimensional ℚ (L ⊔ IntermediateField.adjoin ℚ S : IntermediateField ℚ ℂ) := inferInstance
    rw [← e] at h5
    exact h5
  have h4 : FiniteDimensional ℚ (IntermediateField.adjoin L S) := h3
  exact NumberField.mk

theorem weberSet_subset : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [_root_.NumberField.IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  intro K L _ _ _ h h2 hd P hP n hn hR
  obtain ⟨inst, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd P hP n hn
  haveI := numberField_adjoin K L (weberSet P n)
  have hn0 : (n : 𝓞 L) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  haveI : NumberField (⊥ : IntermediateField L ℂ) := NumberField.of_module_finite L _
  have hle : IntermediateField.adjoin L (weberSet P n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split L ℂ ⊥ (IntermediateField.adjoin L (weberSet P n)) ?_
    refine ((finite_mem hn0).union (finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hR 𝔓 hc.1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine _root_.GlobalTheory.SplitCompositum.ncard_eq_finrank_adjoin K L h (weberSet P n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1)
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin L _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberIn
end

