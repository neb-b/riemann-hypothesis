module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientExternalProductEqMulOrthogonalSum
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.BoxCoef

theorem wcoef_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ νB 𝓕B νW 𝓕W νH 𝓕H, IsCovolOne (ratL B A) νB 𝓕B → IsCovolOne (ratL W A) νW 𝓕W → IsCovolOne (ratL H A) νH 𝓕H → ∀ Φ Φ', IsThetaFunO ψ A W Φ → IsThetaFunO ψ A H Φ' → ∀ g, wcoef omB νB 𝓕B (o.boxT A Φ Φ') (o.boxT A Φ Φ') g = wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H Φ' Φ' g := by
  intro D ψ A B W H o χA χW omB omW omH hB hW hH νB 𝓕B νW 𝓕W νH 𝓕H cB cW cH Φ Φ' hΦ hΦ' g
  have hψ := hB.std
  have hB' : IsWeilDatumO ψ A B χA (χW * 1) omB := by rwa [mul_one]
  have hom := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ B W H o A).om_box χA χW 1 omB omW omH hB' hW hH g 1 1 Φ Φ'
    hΦ hΦ'
  have e1 : o.emb ((1 : GA D W), (1 : GA D H)) = 1 := map_one o.emb
  rw [e1] at hom
  have hF1t : IsThetaFunO ψ A W (omW (g, 1) Φ) := hW.om_pres _ _ hΦ
  have hF2t : IsThetaFunO ψ A H (omH (g, 1) Φ') := hH.om_pres _ _ hΦ'
  simp only [wcoef, ip]
  rw [hom]
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) B.rank A.rank
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) W.rank A.rank
  haveI := GlobalTheory.WeilSliceUnit.borel_Mx (D := D) H.rank A.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D W.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D H.rank A.rank
  haveI := cW.1
  haveI := cH.1
  let e : WO A B ≃ₜ (WO A W × WO A H) :=
    { (o.resT A).toEquiv with continuous_toFun := o.continuous_resT A, continuous_invFun := o.continuous_resT_symm A }
  let em := e.toMeasurableEquiv
  let μP : Measure (WO A W × WO A H) := νW.prod νH
  let μ' : Measure (WO A B) := μP.map em.symm
  haveI : μ'.IsAddHaarMeasure :=
    (o.resT A).symm.isAddHaarMeasure_map μP (o.continuous_resT_symm A) (o.continuous_resT A)
  have hmp : MeasurePreserving em μ' μP := ⟨em.measurable, em.map_map_symm⟩
  have hprod := GlobalTheory.WeilSliceUnit.isAddFundamentalDomain_prod cW.2.1 cH.2.1
  have hmem : ∀ γ : (ratL W A).prod (ratL H A), (o.resT A).symm (γ : WO A W × WO A H) ∈ ratL B A := fun γ => by
    rw [o.mem_ratL_resT, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 γ.2
  have hP : IsAddFundamentalDomain (ratL B A) (em ⁻¹' (𝓕W ×ˢ 𝓕H)) μ' := by
    refine hprod.preimage_of_equiv hmp.quasiMeasurePreserving (e := fun γ => ⟨_, hmem γ⟩)
      ⟨fun γ γ' h => ?_, fun h => ?_⟩ fun γ x => ?_
    · exact Subtype.ext ((o.resT A).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resT A h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resT A h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resT A).symm_apply_apply h
    · change o.resT A ((o.resT A).symm (γ : WO A W × WO A H) + x) = (γ : WO A W × WO A H) + o.resT A x
      rw [map_add (f := _), AddEquiv.apply_symm_apply]
  have hvol : μ' (em ⁻¹' (𝓕W ×ˢ 𝓕H)) = 1 := by
    rw [← em.map_apply, hmp.map_eq, Measure.prod_prod, cW.2.2, cH.2.2, one_mul]
  have hcov : IsCovolOne (ratL B A) μ' (em ⁻¹' (𝓕W ×ˢ 𝓕H)) := ⟨inferInstance, hP, hvol⟩
  have hper := GlobalTheory.Size.mul_conj_periodic hψ (o.isThetaFunO_boxT hF1t hF2t) (o.isThetaFunO_boxT hΦ hΦ')
  refine (covolOne_integral_eq cB hcov (fun w => o.boxT A (omW (g, 1) Φ) (omH (g, 1) Φ') w * conj (o.boxT A Φ Φ' w)) hper).symm.trans ?_
  have hfun : (fun w => o.boxT A (omW (g, 1) Φ) (omH (g, 1) Φ') w * conj (o.boxT A Φ Φ' w)) =
      fun w => (fun y : WO A W × WO A H =>
        (omW (g, 1) Φ y.1 * conj (Φ y.1)) * (omH (g, 1) Φ' y.2 * conj (Φ' y.2))) (em w) := by
    funext w
    show omW (g, 1) Φ (o.resT A w).1 * omH (g, 1) Φ' (o.resT A w).2 * conj (Φ (o.resT A w).1 * Φ' (o.resT A w).2) =
      omW (g, 1) Φ (o.resT A w).1 * conj (Φ (o.resT A w).1) * (omH (g, 1) Φ' (o.resT A w).2 * conj (Φ' (o.resT A w).2))
    rw [map_mul]; ring
  rw [hfun]
  refine (hmp.setIntegral_preimage_emb em.measurableEmbedding (fun y : WO A W × WO A H =>
    (omW (g, 1) Φ y.1 * conj (Φ y.1)) * (omH (g, 1) Φ' y.2 * conj (Φ' y.2))) (𝓕W ×ˢ 𝓕H)).trans ?_
  rw [← Measure.prod_restrict]
  exact integral_prod_mul (fun u => omW (g, 1) Φ u * conj (Φ u)) (fun v => omH (g, 1) Φ' v * conj (Φ' v))

end GlobalTheory.Core.Rk.BoxCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumProductCompatibility
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrKernel

variable {D : D7}

theorem continuous_ofAdj (S T : HSp D) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T) := by
  have h : Continuous fun z : Mx D S.rank T.rank => giA T ⬝ (adj z ⬝ gA S) :=
    continuous_const.matrix_mul
      ((GlobalTheory.MixModel.continuous_adj (D := D) (m := S.rank) (n := T.rank)).matrix_mul continuous_const)
  exact h.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) :=
  (continuous_ofAdj B.L S).comp (continuous_const.matrix_mul continuous_id)

theorem integrable_of_cont_bdd {m n : ℕ} (μ : Measure (Mx D m n)) [IsFiniteMeasure μ] (f : Mx D m n → ℂ)
    (hc : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem symm_resS_symm {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply, add_comm]; rfl

theorem symm_resT_symm {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u : WO S B) (v : WO S A) :
    (o.symm.resT S).symm (u, v) = (o.resT S).symm (v, u) := by
  rw [OrthDec.resT_symm_apply, OrthDec.resT_symm_apply, add_comm]; rfl

theorem kernel_doubleStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → ∀ h₀ h₁ h₂, ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ = omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  have TS := _root_.GlobalTheory.TensorSrc.tensorSource D ψ hstd B.V₀ B.A B.L B.o J.W₀
  have TT := _root_.GlobalTheory.TensorTargetRule.tensorTarget D ψ hstd B'.V₀ B'.A B'.L B'.o J.W₀
  have hw₁ : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s₁.χW s₁.om₀ := hV ▸ s₁.weil₀
  have hw₂ : IsWeilDatumO ψ J.W₀ B'.V₀ s₂.χV (χA' * χz) s₂.om₀ := hW ▸ s₂.weil₀
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI : BorelSpace (WO B.L J.W₀) := ⟨rfl⟩

  have hS₁ : ∀ u, IsThetaFunO ψ B.L J.W₀ fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z)) := (TS.slice_theta Ξ₁ hΞ₁).2
  have hS₂ : ∀ v, IsThetaFunO ψ J.W₀ B'.L fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) := (TT.slice_theta Ξ₂ hΞ₂).2

  obtain ⟨Hf, hHf⟩ : ∃ Hf : WO B.A J.W₀ → WO B.L J.W₀ → ℂ,
      Hf = fun u z => omz (1, h₁) (fun z' => Ξ₁ ((B.o.resS J.W₀).symm (u, z'))) z := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : WO J.W₀ B'.A → WO J.W₀ B'.L → ℂ,
      Gf = fun v w => omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) w := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁d⟩ : ∃ F₁ : WO B.V₀ J.W₀ → ℂ, F₁ = fun x => Hf (B.o.resS J.W₀ x).1 (B.o.resS J.W₀ x).2 := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂d⟩ : ∃ F₂ : WO J.W₀ B'.V₀ → ℂ, F₂ = fun x => Gf (B'.o.resT J.W₀ x).1 (B'.o.resT J.W₀ x).2 :=
    ⟨_, rfl⟩
  have hF₁s : ∀ u z, F₁ ((B.o.resS J.W₀).symm (u, z)) = Hf u z := by
    intro u z; rw [hF₁d]; simp only [AddEquiv.apply_symm_apply]
  have hF₂s : ∀ v w, F₂ ((B'.o.resT J.W₀).symm (v, w)) = Gf v w := by
    intro v w; rw [hF₂d]; simp only [AddEquiv.apply_symm_apply]

  have hF₁ : IsThetaFunO ψ B.V₀ J.W₀ F₁ := by
    have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.L B.A J.W₀ B.o.symm χz s₁.χW omz hoz Ξ₁ hΞ₁ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (1, h₁)).1
    have e : F₁ = fun x => omz (1, h₁) (fun u => Ξ₁ ((B.o.symm.resS J.W₀).symm (u, (B.o.symm.resS J.W₀ x).2)))
        (B.o.symm.resS J.W₀ x).1 := by
      funext x; rw [hF₁d, hHf]; simp only [symm_resS_symm]; rfl
    rw [e]; exact h
  have hF₂ : IsThetaFunO ψ J.W₀ B'.V₀ F₂ := by
    have h := (_root_.GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target D ψ B'.V₀ B'.L B'.A J.W₀ B'.o.symm s₂.χV χz omz' hoz' Ξ₂ hΞ₂ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (h₁, 1)).1
    have e : F₂ = fun x => omz' (h₁, 1) (fun u => Ξ₂ ((B'.o.symm.resT J.W₀).symm (u, (B'.o.symm.resT J.W₀ x).2)))
        (B'.o.symm.resT J.W₀ x).1 := by
      funext x; rw [hF₂d, hGf]; simp only [symm_resT_symm]; rfl
    rw [e]; exact h

  obtain ⟨b₁, hb₁d⟩ : ∃ b₁ : WO J.W₀ B'.L → ℂ, b₁ = fun w => oma (h₀, h₁) (fun u => Hf u (l.κ J.W₀ w)) 0 := ⟨_, rfl⟩
  have hA : ∀ w, s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = b₁ w := by
    intro w
    rw [(TS.om_slice χA χz s₁.χW s₁.om₀ oma omz hw₁ hoa hoz h₀ 1 h₁ Ξ₁ hΞ₁ (l.κ J.W₀ w)).2 0, hb₁d, hHf]
  have hB : ∀ w, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) = omb (h₁, h₂) (fun v => Gf v w) 0 := by
    intro w
    rw [(TT.om_slice s₂.χV χA' χz s₂.om₀ omb omz' hw₂ hob hoz' h₁ h₂ 1 Ξ₂ hΞ₂ w).2 0, hGf]

  have hb₁int : Integrable b₁ (vL.μ.restrict vL.𝓕) := by
    have th := hw₁.om_pres (B.o.emb (h₀, 1), h₁) Ξ₁ hΞ₁
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded B.V₀ J.W₀ ψ hstd _ th
    have e : b₁ = fun w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) :=
      funext fun w => (hA w).symm
    rw [e]
    exact integrable_of_cont_bdd _ _ (th.cont.comp ((B.o.continuous_resS_symm J.W₀).comp
      (continuous_const.prodMk (continuous_kappa l J.W₀)))) ⟨C, fun w => hC _⟩
  have hGint : ∀ v, Integrable (Gf v) (vL.μ.restrict vL.𝓕) := by
    intro v
    have th := hoz'.om_pres (h₁, 1) _ (hS₂ v)
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded J.W₀ B'.L ψ hstd _ th
    have e : Gf v = omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) := by rw [hGf]
    rw [e]
    exact integrable_of_cont_bdd _ _ th.cont ⟨C, hC⟩

  have hLine : ∀ u v, ∫ w, Gf v w * Hf u (l.κ J.W₀ w) ∂(vL.μ.restrict vL.𝓕) = contr l J.W₀ vL Ξ₁ Ξ₂ u v := by
    intro u v
    have hrank : B.L.rank = B'.L.rank := B.line.1.trans B'.line.1.symm
    have hgram := (GlobalTheory.T.besselLineLink_gram_similitude_bijective D (σ + 1) B B'.L B'.ζ B'.line l).1
    have CL := _root_.GlobalTheory.ConjLine.conj_line D ψ B.L B'.L J.W₀ l.τ hrank hgram χz s₁.χW s₂.χV omz omz' hoz hoz'
      (fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z))) (hS₁ u)
    have CU := _root_.GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B'.L s₂.χV χz omz' hoz' vL (h₁, 1) _ _ (hS₂ v) CL.1
    rw [CL.2 h₁] at CU
    simp only [thPair, star_star] at CU
    rw [hGf, hHf]
    exact CU

  have hInner : ∀ v, oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 =
      ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := by
    intro v
    have e : (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) =
        fun u => ∫ w, Gf v w * F₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w)) ∂(vL.μ.restrict vL.𝓕) := by
      funext u; rw [← hLine u v]; simp only [hF₁s]
    rw [e, (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa F₁ hF₁ (WO J.W₀ B'.L) (vL.μ.restrict vL.𝓕)
      (l.κ J.W₀) (Gf v) (continuous_kappa l J.W₀).measurable (hGint v) (h₀, h₁)).2 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF₁s, hF₂s, id, hb₁d]
    exact mul_comm _ _
  have hOuter := (_root_.GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target D ψ B'.V₀ B'.A B'.L J.W₀ B'.o s₂.χV χA' omb hob F₂ hF₂ (WO J.W₀ B'.L)
    (vL.μ.restrict vL.𝓕) id b₁ measurable_id hb₁int (h₁, h₂)).2 0
  have e : (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) =
      fun v => ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := funext hInner
  rw [e, hOuter]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hA, hB, hF₂s, id]
  exact mul_comm _ _

end GlobalTheory.ContrKernel

end
end

