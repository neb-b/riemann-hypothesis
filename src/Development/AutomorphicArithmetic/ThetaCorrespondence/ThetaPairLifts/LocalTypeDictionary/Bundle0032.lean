module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFockMapFirstOrderOfRealLift
section
section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.RealLift.FockFirst
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end SlopeTestRemainingChoices
theorem exists_fockMap_first_order_of_real_lift (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (h : IsTriple B G X om om') :
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ)
      (Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w)) ∧
      (∀ w, G.V.θ w * A w = A w * Jm (a - G.p) G.p) ∧
      LinearMap.range Φ = G.M.Pol B.ψ B.emb ∧
      ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (fockAct1 (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q)) c := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hder : DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hder
  have hsec : LieSecond := _root_.GlobalTheory.T.real_lift_lie_second_order hP hder hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl)
  have hfst : LieFirst := GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond hsec
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  exact ⟨A, Φ, _, hA1, hAθ, hr, hW1⟩
end GlobalTheory.RealLift.FockFirst
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_lift_exists_fock_map : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : NumberField.InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : NumberField.InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c := by
  first | exact @_root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | exact _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift | (intros; apply _root_.GlobalTheory.RealLift.FockFirst.exists_fockMap_first_order_of_real_lift <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasDerivAtThetaSumAlongLine
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
noncomputable section
open scoped Classical
namespace GlobalTheory.ThetaLineDerFirst
theorem hasDerivAt_thetaSum_along_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) (f i) (f₁ i)) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)))) 0 := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hψ hG hW γ hγ m f f₁ φ hφ hD u
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 :=
    fun i => ((hφ i).2.and hG.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ i (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (φ i) ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun i g => GlobalTheory.TensUniq.pure_mem_schA g (φ i) (hφ i).1 (hstd i)
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW).pres
  have hcurve : (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))))
      = fun t => ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hpres _ _ (hmem i (f i)))
  have hend : GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) =
      ∑ i, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j)))) :=
    GlobalTheory.ThetaLineDer.rho_sum M ψ hψ u _ (fun i => hmem i (f₁ i))
  have hi : ∀ i, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (f₁ i) (fun x => ∏ᶠ v, φ i v fun j => evFin F v (x j))))) 0 :=
    fun i => _root_.GlobalTheory.T.thetaSum_differentiable_along_line hP M ψ χX χW om hψ hG hW γ hγ (f i) (f₁ i) _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hφ i).1 (hstd i)) (hD i) u
  rw [hcurve, hend]
  have := HasDerivAt.sum (u := Finset.univ) fun i _ => hi i
  simpa [Finset.sum_fn] using this
end GlobalTheory.ThetaLineDerFirst
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormFiniteSumExpansion
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KFinCuspSum
theorem kFinite_cusp_form_eq_sum_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj ψ hψ hW
  obtain ⟨n, F, u, hF, hsum⟩ :=
    _root_.GlobalTheory.T.cuspForm_gelfandKirillov_finite_decomposition hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf ψ hψ.1 hψ.2.1 hψ.2.2 hW
  choose Tm hTm hext using fun l =>
    _root_.GlobalTheory.T.gelfandKirillov_globalization hP R.θ (G.V i j).V (G.V i j).S (G.V i j).M hR.inf (F l) (hF l)
  choose v hv hTv using fun l => hext l (u l)
  refine ⟨n, Tm, v, hTm, fun g => ?_⟩
  rw [hsum g]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hTv l]
end GlobalTheory.KFinCuspSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_form_finite_sum_expansion : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  first | exact @_root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | exact _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values | (intros; apply _root_.GlobalTheory.KFinCuspSum.kFinite_cusp_form_eq_sum_values <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteSubspaceKStableIffLieStable
section
section
noncomputable section
namespace GlobalTheory.KStableLie
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open scoped Classical in
theorem kStable_of_lie_stable_subspace (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hw : M.IsWeil B.ψ χX χW om) {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi)
    (hlie : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N)
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    {f₁ : SInf F (Fin n × Fin d)} (hact1 : Acts (evI F) (om (1, k)) f f₁) (hfN : p f ∈ N) : p f₁ ∈ N := by
  have hAL : ActsLaws := GlobalTheory.RealLift.actsLaws
  have hfr : GlobalTheory.RealLift.FrameEx := _root_.GlobalTheory.RealLift.frameEx_holds
  have hder : GlobalTheory.RealLift.DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hvl : GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : GlobalTheory.RealLift.FockEx := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hder
  have hls : GlobalTheory.RealLift.LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl
  have hpr : GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl
  have hkl : GlobalTheory.RealLift.KLine := GlobalTheory.RealLift.kLine_of_lineEx _root_.GlobalTheory.RealLift.exists_line_of_upq
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    hkl F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _
    (fun w => GlobalTheory.PolCompact.locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := _root_.GlobalTheory.ExpAct.expAct_fock F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  set N' : Submodule ℂ (Tens F r s r' s') := N.comap (p ∘ₗ Φ) with hN'
  have hstab : ∀ y ∈ N', sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y ∈ N' := by
    intro y hy
    have hsd := hact γ hγ Yg hgen y
    have had : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ y)
        (Φ (sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y)) :=
      (hAL F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hsd
    have hy' : Φ y ∈ M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ y
    exact hlie γ hγ _ hy' _ had hy
  have hUT : U T ∈ N' := mem_of_isExp hU N' hstab hfN
  have h1 := hSA T
  change SA (om (1, γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at h1
  rw [hγ1] at h1
  have hA2 : Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) :=
    (hAL F (Fin n × Fin d) (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) h1
  have he : f₁ = Φ (U T) := (hAL F (Fin n × Fin d) (Φ T) f₁ (Φ (U T))).2.2.2.1 _ hact1 hA2
  rw [he]
  exact hUT
theorem lie_stable_subspace_kStable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        R.p f ∈ N → R.p f₁ ∈ N) →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.W Bs.emb, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf h N hlie k hk f hf f₁ hact hN
  exact _root_.GlobalTheory.KStableLie.kStable_of_lie_stable_subspace hP h.triple.base h.triple.geo.hV h.triple.geo.hW h.triple.weil R.p N hlie hk hf hact hN
end GlobalTheory.KStableLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_subspace_kStable_iff_lie_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        R.p f ∈ N → R.p f₁ ∈ N) →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.W Bs.emb, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
  first | exact @_root_.GlobalTheory.KStableLie.lie_stable_subspace_kStable | exact _root_.GlobalTheory.KStableLie.lie_stable_subspace_kStable | (intros; apply _root_.GlobalTheory.KStableLie.lie_stable_subspace_kStable <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieActionMemKerPolarizationProjection
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerLie
theorem lie_action_mem_ker_polarizationProjection : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V', ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm γ hγ f hf f₁ hf₁
    hact φ hφ hv
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hM : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hW : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hD0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  have hD1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f₁, φ, hf₁, hφ, hv, rfl⟩
  obtain ⟨Ψ, hΨ, hΨD⟩ := hO.algB' _ hD0
  obtain ⟨Ψ₁, hΨ₁, hΨ₁D⟩ := hO.algB' _ hD1
  rw [mem_kerPD hstd]
  refine ⟨hD1, Ψ₁, hΨ₁, hΨ₁D, ?_⟩
  have hstd' : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hv.and hM.std).mono fun v h => h.1.trans h.2
  have hrest := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ hstd'
  have hder : ∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0 := by
    intro z
    obtain ⟨u, rfl⟩ := cB.surjective z
    have h1 := _root_.GlobalTheory.T.thetaSum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hstd hM hW γ hγ f f₁ _ hrest hact u
    have hval : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (γ (Multiplicative.ofAdd t), 1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin D.host.F v (x i))))) =
        ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t)), 1) Ψ (cB u) := by
      intro t
      have h := (hO.weilB _ Ψ hΨD (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t))) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one] at h
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t))) =
          γ (Multiplicative.ofAdd t) := (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).apply_symm_apply _
      rw [e1] at h
      exact h
    have h2 := hΨ₁D.2 u
    have e3 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t)), 1) Ψ (cB u)) =
        fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (γ (Multiplicative.ofAdd t), 1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin D.host.F v (x i))))) :=
      funext fun t => (hval t).symm
    rw [e3, ← h2]
    exact h1
  exact _root_.GlobalTheory.T.weil_coinvariants_vanish_on_line_derivatives hP D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ hstd hTr hm Γ.V' hO.JW₁ γ hγ Ψ hΨ Ψ₁ hΨ₁ hder
end GlobalTheory.SquareAgree.KerLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_lie_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V', ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection | exact _root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection | (intros; apply _root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection <;> assumption)
end
end

