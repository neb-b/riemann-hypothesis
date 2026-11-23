module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterWeilOperatorDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenberg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ExchPf

open GlobalTheory.PairLift GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

def withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) : HSp D :=
  { V with hT := h, herm := e ▸ V.herm, nondeg := e ▸ V.nondeg, baseLattice_isUnimodular := e ▸ V.baseLattice_isUnimodular }

theorem HR_withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) :
    HR (AF D.host.F) D.sp.cm.sig V.gram = HR (AF D.host.F) D.sp.cm.sig (withForm V h e).gram := by
  subst e; rfl

theorem datum_withForm {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (h : B.V →ₗ⋆[D.host.E] B.V →ₗ[D.host.E] D.host.E) (e : h = B.hT)
    (ω : GA D A × GA D (withForm B h e) →* Module.End ℂ (WO A (withForm B h e) → ℂ))
    (hd : IsWeilDatumO ψ A (withForm B h e) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap (MulEquiv.subgroupCongr (HR_withForm B h e)).toMonoidHom)) := by
  subst e
  exact hd

theorem datum_negneg {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (ω : GA D A × GA D (negSp (negSp B)) →* Module.End ℂ (WO A (negSp (negSp B)) → ℂ))
    (hd : IsWeilDatumO ψ A (negSp (negSp B)) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap ((negGA B).trans (negGA (negSp B))).toMonoidHom)) := by
  have key := datum_withForm (ψ := ψ) (A := A) (B := B) (χ := χ) (χ' := χ') (-(-B.hT)) (neg_neg _) ω hd
  have e : ((negGA B).trans (negGA (negSp B))).toMonoidHom =
      (MulEquiv.subgroupCongr (HR_withForm B (-(-B.hT)) (neg_neg _))).toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [e]
  exact key

theorem exch_eq_cj (A B : HSp D) (f : WO A B → ℂ) : exch A B f = cj id (dag A B f) := by
  funext x; simp [GlobalTheory.CoreOnto.exch, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag]

theorem theta_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (f : WO A B → ℂ) :
    IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  rw [exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).1 (dag A B f)).2]
  exact ⟨hAB.theta f, fun h => by simpa only [GlobalTheory.WeilConj.dag_dag hAB] using hBA.theta _ h⟩

theorem heis_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x : WO (negSp B) A)
    (f : WO A B → ℂ) : heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  rw [exch_eq_cj, exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).2 x (dag A B f)).2, hAB.Heisenberg₂]

theorem sympl_negB (A B : HSp D) (x x' : WO B A) : symplO (negSp B) A x x' = -symplO B A x x' := by
  have e : hO (negSp B) A x x' = -hO B A x x' := by
    unfold hO
    rw [negSp_gram, GlobalTheory.CjNeg.inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem sympl_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x x' : WO (negSp B) A) :
    symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x') := by
  rw [(GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).sympl, sympl_negB]

theorem bij_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) :
    Function.Bijective (adjO A B) :=
  Function.bijective_iff_has_inverse.2 ⟨adjO B A, fun x => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A).invol x,
    fun y => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).invol y⟩

theorem covol_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    (m : Measure (Mx D B.rank A.rank)) (X : Set (Mx D B.rank A.rank)) (hX : IsCovolOne (ratL B A) m X) :
    ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧ ∀ f f' : WO A B → ℂ,
      ∫ w in X, f w * starRingEnd ℂ (f' w) ∂m = ∫ w in X', exch A B f w * starRingEnd ℂ (exch A B f' w) ∂m' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  obtain ⟨hμ, h𝓕, h1⟩ := hX
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank B.rank
  haveI : BorelSpace (WO A B) := ⟨rfl⟩
  haveI : BorelSpace (WO B A) := ⟨rfl⟩
  let eA : WO A B ≃+ WO B A :=
    { toFun := adjO B A
      invFun := adjO A B
      left_inv := fun x => hAB.invol x
      right_inv := fun y => hBA.invol y
      map_add' := hBA.add }
  let eH : WO A B ≃ₜ WO B A := ⟨eA.toEquiv, hBA.cont, hAB.cont⟩
  let eM : WO A B ≃ᵐ WO B A := eH.toMeasurableEquiv
  have hHaar : (m.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map m eA hBA.cont hAB.cont
  have hmp : MeasurePreserving eM m (m.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (m.map eM) m := MeasurePreserving.symm eM hmp
  let eG : ratL B A → ratL A B := fun g => ⟨adjO B A g, (hBA.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO A B g, (hAB.rat g).2 g.2⟩, Subtype.ext (hBA.invol g)⟩⟩
    have e := congrArg (fun x : ratL A B => adjO A B (x : WO B A)) hg
    simp only [eG, hAB.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL A B) (eM.symm ⁻¹' X) (m.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO A B (adjO B A g + x) = (g : WO A B) + adjO A B x
    rw [hAB.add, hAB.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' X) = X := by
    ext a; simp
  refine ⟨m.map eM, eM.symm ⁻¹' X, ⟨hHaar, hF, ?_⟩, fun f f' => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · symm
    rw [MeasurableEquiv.restrict_map, integral_map_equiv, hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (adjO A B (adjO B A x)) * starRingEnd ℂ (f' (adjO A B (adjO B A x))) = _
    rw [hAB.invol]

theorem weil_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ)) (hω : IsWeilDatumO ψ (negSp B) A χS χT ω) :
    ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  have h1 := GlobalTheory.ConjWeil.weil_conjSource D ψ (negSp B) A χS χT ω hω
  obtain ⟨ω₃, h3, R⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ (negSp (negSp B)) A χS⁻¹ χT⁻¹ (conjSource ω) h1
  refine ⟨_, datum_negneg ω₃ h3, fun f _ g h => ?_⟩
  have hadj : ∀ y : WO A B, adjO (negSp (negSp B)) A y = adjO B A y := by
    intro y; simp only [adjO, negSp_gram, neg_neg]
  have hf : dag (negSp (negSp B)) A (cj id (exch A B f)) = f := by
    funext y
    simp only [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, GlobalTheory.CoreOnto.exch, Complex.conj_conj, hadj, hAB.invol]
  have R' := R ((negGA (negSp B)) (negGA B h)) g (cj id (exch A B f))
  rw [hf] at R'
  show _ = exch A B (ω₃ (g, (negGA (negSp B)) (negGA B h)) f)
  rw [R', GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  funext x
  simp only [GlobalTheory.CoreOnto.exch, dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj, hadj, hBA.invol]

theorem exchLaw : ∀ D : D7, ExchLaw D := by
  intro D ψ A B hψ
  exact ⟨theta_exch hψ A B, heis_exch hψ A B, sympl_exch hψ A B, bij_exch hψ A B,
    fun m X hX => covol_exch hψ A B m X hX, fun χS χT ω hω => weil_exch hψ A B χS χT ω hω⟩

end GlobalTheory.ExchPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanWeilLineIntertwinesHeisenbergRight
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

noncomputable section

theorem GlobalTheory.ArchLineAct.intertwine_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, Continuous fun t => A t w) ∧ (∀ s t, A (s + t) = (A s).comp (A t)) ∧ A 0 = LinearMap.id ∧
          ∀ (t : ℝ) (p q : (Fin n × Fin d → mixedEmbedding.mixedSpace F)) (f g : SInf F (Fin n × Fin d)),
            ⇑g = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) p q ⇑f →
            ⇑(T t g) = GlobalTheory.GaussLine.heisFun (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f) := by
  intro F E _ _ _ _ _ σ _hcm n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hWeil γ hγ T hTact
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hRsh : ∀ x z, At (evI F) z → R (x + z) = R x := (hR 0).1
  let L : ℝ → Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    fun t => GlobalTheory.ArchLineAct.rmulT (mat (γ (Multiplicative.ofAdd t)))
  have hmat : ∀ g h : UA σ W.J, mat (g * h) = mat g * mat h := fun _ _ => rfl
  have hmat1 : mat (1 : UA σ W.J) = 1 := rfl
  refine ⟨fun t => GlobalTheory.ArchLineAct.archMap M.co (L t), fun w => ?_, fun s t => ?_, ?_, fun t p q f g hg => ?_⟩
  · have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      (Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))).matrix_transpose
    set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift w.1, GlobalTheory.ArchLineAct.archLift w.2) with hu
    let K := M.co.e.toLinearMap ∘ₗ (GlobalTheory.ArchLineAct.lmulL (k := d) u)
    haveI : IsModuleTopology (AF F) (Matrix (Fin d) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin d → Fin d → AE F E))
    have hK : Continuous K := IsModuleTopology.continuous_of_linearMap K
    have hc : Continuous fun t : ℝ => M.co.e (L t u) := hK.comp hm
    show Continuous fun t : ℝ => (GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).1,
      GlobalTheory.ArchLineAct.archPart (M.co.e (L t u)).2)
    exact Continuous.prodMk
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_fst.comp hc)))
      (continuous_pi fun i => GlobalTheory.ArchLineAct.continuous_evI.comp ((continuous_apply i).comp (continuous_snd.comp hc)))
  · show GlobalTheory.ArchLineAct.archMap M.co (L (s + t)) =
      (GlobalTheory.ArchLineAct.archMap M.co (L s)).comp (GlobalTheory.ArchLineAct.archMap M.co (L t))
    rw [GlobalTheory.ArchLineAct.archMap_comp]
    congr 1
    refine LinearMap.ext fun x => ?_
    show x * (mat (γ (Multiplicative.ofAdd (s + t))))ᵀ =
      (x * (mat (γ (Multiplicative.ofAdd t)))ᵀ) * (mat (γ (Multiplicative.ofAdd s)))ᵀ
    rw [ofAdd_add, map_mul, hmat, Matrix.transpose_mul, Matrix.mul_assoc]
  · show GlobalTheory.ArchLineAct.archMap M.co (L 0) = LinearMap.id
    have hL : L 0 = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      change x * (mat (γ (Multiplicative.ofAdd 0)))ᵀ = LinearMap.id x
      rw [LinearMap.id_apply, ofAdd_zero, map_one, hmat1, Matrix.transpose_one, Matrix.mul_one]
    rw [hL, GlobalTheory.ArchLineAct.archMap_id]
  · set u := M.co.e.symm (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) with hu
    have hue : M.co.e u = (GlobalTheory.ArchLineAct.archLift p, GlobalTheory.ArchLineAct.archLift q) :=
      LinearEquiv.apply_symm_apply _ _
    have hu' : At (evI F) (L t u) := GlobalTheory.ArchLineAct.at_lin _ (GlobalTheory.ArchLineAct.at_symm _ p q)
    have hue' := GlobalTheory.ArchLineAct.coord_eq M.co hu'
    have himpl := hW.impl (1, γ (Multiplicative.ofAdd t)) u (tens (evI F) (⇑f) R) (hR f).2
    have hact : GlobalTheory.WeilM.actAB (cA σ) ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) u = L t u := by
      show ((1 : UA σ X.J) : GL (Fin n) (AE F E)).1 * u * (mat (γ (Multiplicative.ofAdd t)))ᵀ =
        u * (mat (γ (Multiplicative.ofAdd t)))ᵀ
      rw [show ((1 : UA σ X.J) : GL (Fin n) (AE F E)).1 = 1 from rfl, Matrix.one_mul]
    rw [hact, GlobalTheory.ArchLineAct.rho_tens hψ M.co u p q hue (⇑f) R hRsh, ← hg, hTact t g R (hR g),
      hTact t f R (hR f), GlobalTheory.ArchLineAct.rho_tens hψ M.co (L t u) _ _ hue' _ R hRsh] at himpl
    funext x
    have h := congrFun himpl (GlobalTheory.ArchLineAct.archLift x)
    rw [GlobalTheory.ArchLineAct.tens_archLift _ R hRsh, GlobalTheory.ArchLineAct.tens_archLift _ R hRsh] at h
    exact mul_right_cancel₀ hR0 h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasicModelsOfFunctoriality
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem exists_dsModel_cart {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, SignedHC.IsRegular (S τ)) (hc : ∀ τ, (S τ).card = V.rank)
    (hm : ∀ τ, SignedHC.nMinus (S τ) = (V.sig (tauE D τ)).2)
    (hP : ∀ τ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by

  have hperm : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε :=
    fun τ => GlobalTheory.GridJoin.exists_perm_onb hV τ (hS τ) (hc τ) (hm τ) (h τ)
  choose σ lam ε hEn hGr hCa using hperm
  obtain ⟨M, hMc, -⟩ := GlobalTheory.dsModel_of_onb_cart D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hEn τ, hP τ (lam τ) (ε τ) (hEn τ), hGr τ⟩) (fun τ => ⟨ε τ, hGr τ, hCa τ⟩)
  exact ⟨M, hMc⟩

private theorem exists_int_eq_half_add_of_mem_parPi (G : GlobalTheory.SignedHC.GridData) (hs : Odd G.s) (i : ℕ) (x : ℚ) (b : Bool)
    (hx : (x, b) ∈ G.parPi i) : ∃ z : ℤ, x = 1 / 2 + z := by
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hx with ⟨l, -, hl⟩ | ⟨hc, -⟩ | ⟨l, -, -, hl, -⟩
  · simp only [Prod.mk.injEq] at hl
    refine ⟨G.v 2 + ((G.m : ℤ) + 1 - l) * G.ga, ?_⟩
    rw [hl.1, GlobalTheory.SignedHC.GridData.a]
    push_cast
    ring
  · dsimp only at hc
    obtain ⟨j, -, -, hj⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hc
    refine ⟨G.v j - 1, ?_⟩
    rw [hj, GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    ring
  · dsimp only at hl
    obtain ⟨w, hw⟩ := hs
    obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.inCoset_block _ _ x hl
    refine ⟨G.cen l + w + z, ?_⟩
    have hlen : ((G.s - 1 : ℕ) : ℚ) = 2 * w := by
      rw [hw, Nat.add_sub_cancel]; push_cast; ring
    rw [hz, hlen]
    push_cast
    ring

theorem isHCParam_parPi (D : D7) (C : ℝ) (i : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankP D i) (hE : IsEnum ((num D C τ).parPi i) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ (num D C τ).parPi i := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  obtain ⟨z, hz⟩ := exists_int_eq_half_add_of_mem_parPi (num D C τ) (odd_sLen D) i (q a) (ε a) hmem
  obtain ⟨k, hk⟩ := even_rankP D i
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

theorem coreModels_of_upq (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) : CoreModels := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have hin : (Node.core i).InRange D.R.m := hi
  obtain ⟨hrank, hsig, hsg, -⟩ := G.isV hin (fun j h => by cases h)
  have hg : 0 < (gap D sc.cGap) := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
  have hs1 : 1 ≤ sLen D := by unfold sLen; omega
  refine exists_dsModel_cart hDS hsig (Node.par D sc.cGap (.core i)) (W.onb (.core i)) (W.cart (.core i))
    (fun τ => ?_) (fun τ => ?_) (fun τ => ?_) (fun τ lam ε hE => ?_) (W.onb_is (.core i) hin)
  · exact GlobalTheory.PiCounts.isRegular_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi
  · exact (GlobalTheory.PiCounts.card_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi).trans
      ((num_ranks D sc.cGap τ i 0).2.1.trans hrank.symm)
  · show nMinus ((num D sc.cGap τ).parPi i) = _
    rw [GlobalTheory.PiCounts.nMinus_parPi hg i, hsg (tauE D τ)]
    rfl
  · exact isHCParam_parPi D sc.cGap i τ lam ε hrank hE

end GlobalTheory.SepRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSylvester

theorem neg_card_eq_sig : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau),
    (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  intro D V hV A τ
  set ε := A.ε τ with hε
  set a := (Finset.univ.filter fun i => ε i = true).card with ha_def
  set b := (Finset.univ.filter fun i => ε i = false).card with hb_def
  have ha : Fintype.card {i // ε i = true} = a := by rw [Fintype.card_subtype]
  have hb : Fintype.card {i // ¬ ε i = true} = b := by
    rw [Fintype.card_subtype]; simp [b]
  let e0 : Fin V.rank ≃ Fin a ⊕ Fin b :=
    (Equiv.sumCompl (fun i => ε i = true)).symm.trans
      (Equiv.sumCongr (Fintype.equivFinOfCardEq ha) (Fintype.equivFinOfCardEq hb))
  have hl : ∀ k : Fin a, ε (e0.symm (Sum.inl k)) = true := fun k => by
    simp [e0]
    exact ((Fintype.equivFinOfCardEq ha).symm k).2
  have hr : ∀ k : Fin b, ε (e0.symm (Sum.inr k)) = false := fun k => by
    simp [e0]
    simpa using ((Fintype.equivFinOfCardEq hb).symm k).2
  have hcard : Fintype.card (Fin V.rank) = a + b := by simpa using Fintype.card_congr e0
  set F := A.fr τ with hF_def
  have hF : IsUnit F := A.fr_unit τ
  have hFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hF)
  have hJ : (F⁻¹)ᴴ * gramAt D V τ * F⁻¹ = Formalism.REAL.Jm ε := by
    rw [← A.fr_gram τ]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = (F * F⁻¹)ᴴ * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFi]; simp
  let Q : Matrix (Fin V.rank) (Fin a ⊕ Fin b) ℂ := (F⁻¹).submatrix id e0.symm
  have hQ : Qᴴ * gramAt D V τ * Q = Formalism.UG.Jpq a b := by
    have h2 : Qᴴ * gramAt D V τ * Q = ((F⁻¹)ᴴ * gramAt D V τ * F⁻¹).submatrix e0.symm e0.symm := by
      ext r s; simp only [Q, Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]
    rw [h2, hJ]
    ext (r | r) (s | s) <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, e0.symm.injective.eq_iff] <;>
      split_ifs <;> simp
  have hsig1 : Formalism.UG.HasSignature (V.gram.map (tauE D τ)) a b :=
    GlobalTheory.FrameComplement.hasSignature_of_frame hcard Q hQ
  have hsig2 := hV (tauE D τ)
  have heq : a = (V.sig (tauE D τ)).1 := GlobalTheory.SylvesterInertia.hasSignature_fst_unique hsig1 hsig2
  obtain ⟨e2, _, _⟩ := hsig2
  have h2 : V.rank = (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 := by simpa using Fintype.card_congr e2
  have h3 : V.rank = a + b := by simpa using hcard
  omega

end GlobalTheory.FrameSylvester
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem GlobalTheory.HeisOrbit.dOp_contDiff_family {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (Pv Qv : ℝ → (κ → mixedEmbedding.mixedSpace F)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pv → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Qv →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (Pv p.1) (Qv p.1) (G p.1) p.2) := by
  intro hG hP hQ
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (ℝ × (κ → mixedEmbedding.mixedSpace F)) × (κ → mixedEmbedding.mixedSpace F) => (G x.1.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) x.2) :=
    hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (κ → mixedEmbedding.mixedSpace F)) (y : (κ → mixedEmbedding.mixedSpace F)) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) hf contDiff_snd
      (le_of_eq (by simp))
  have hD' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => fderiv ℝ (fun y : (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) y) p.2 (Pv p.1)) :=
    hD.clm_apply (hP.comp contDiff_fst)
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ∑ i, p.2 i * Qv p.1 i) := by
    refine ContDiff.sum (fun i _ => ?_)
    exact ((contDiff_apply ℝ _ i).comp contDiff_snd).mul
      ((contDiff_apply ℝ _ i).comp (hQ.comp contDiff_fst))
  have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, p.2 i * Qv p.1 i) : ℝ) : ℂ)) := by
    have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z) :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toContinuousLinearMap.contDiff
    exact Complex.ofRealCLM.contDiff.comp (hl.comp hS)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => (G p.1 : (κ → mixedEmbedding.mixedSpace F) → ℂ) p.2) := hG
  unfold GlobalTheory.HeisOrbit.dOp
  exact hD'.sub ((contDiff_const.mul hT).mul hg)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientMatrixCoefficientContinuousOnUnita
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coefA_dual_coef_continuousOn :
    ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  intro D V θ c hθ hc τ f v
  letI := c.nW
  letI := c.iW
  haveI := c.fW
  have h1 : Continuous fun h : GA D V => c.ρ h v := hc.2.2.1 v
  have hinv : Continuous (fun h : GA D V => h⁻¹) := continuous_inv
  have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
  exact (hf.comp (h1.comp hinv)).comp_continuousOn (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ)

end GlobalTheory
end

