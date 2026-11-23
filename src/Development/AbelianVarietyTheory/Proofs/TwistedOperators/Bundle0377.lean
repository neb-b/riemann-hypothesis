module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open scoped Matrix Classical

namespace GlobalTheory.ArchLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}


open Classical in
def archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d)) : SInf F (Fin n × Fin d) :=
  if hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁ then hx.choose else 0

def archAct (M : Model σ X W) (h : UA σ W.J)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  coordI M (actAB (cA σ) ((1 : UA σ X.J), h) (M.co.e.symm (liftV v.1, liftV v.2)))

theorem acts_archOp (om : Rep σ X W) (h : UA σ W.J) (f : SInf F (Fin n × Fin d))
    (hx : ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) ⇑f ⇑f₁) :
    Acts (evI F) (om (1, h)) ⇑f ⇑(archOp om h f) := by
  classical
  unfold archOp
  rw [dite_eq_left hx]
  exact hx.choose_spec

theorem archAct_one (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    archAct M 1 v = v := by
  unfold archAct
  simp [actAB, coordI_lift]

end GlobalTheory.ArchLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineTransposeGramUnitaryEqExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LineDecomp

theorem toUX_surj (D : D7) (X : HSp D) {J : Matrix (Fin X.rank) (Fin X.rank) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig J) : ∃ g : GA D X, GlobalTheory.TripleRead.toUX X (Equiv.refl _) hJ g = u := by
  have h : (u.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J * (u.1.1).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J := u.2
  generalize hm : u.1.1 = m at h
  have e0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J = Formalism.L2.Theta.incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    rw [hJ]
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _
  rw [e0, Matrix.mul_smul, Matrix.smul_mul] at h
  have hu : IsUnit (Formalism.L2.Theta.incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have h2 := hu.smul_left_cancel.1 h
  have h3 := congrArg Matrix.transpose h2
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h3
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := rfl
  rw [e, ← hm] at h3
  refine ⟨⟨u.1, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact GlobalTheory.TripleRead.toUX_val X (Equiv.refl _) hJ _


set_option maxHeartbeats 1000000 in
theorem mem_GinfC_of_at (D : D7) (X : HSp D) (g : GA D X)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Formalism.L2.Theta.mt X g - 1)) : g ∈ GinfC X := by
  let a : AF D.host.F := ((0 : Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  have ha : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F a = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := h a ha
  let φ := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  have key : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E, φ (a • x) = φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul b c =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]
      congr 1
      exact one_mul _
    | add x y hx hy =>
      have e1 : a • (x + y) = a • x + a • y := smul_add a x y
      rw [e1, map_add φ (a • x) (a • y), map_add φ x y, hx, hy]
  show finHom X g = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt X g).map φ = 1
  ext i j
  have h2 := congrArg φ (congrFun (congrFun h1 i) j)
  rw [Matrix.smul_apply, key, Matrix.zero_apply, map_zero, Matrix.sub_apply, map_sub, sub_eq_zero] at h2
  rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem line_eq_expInf : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws, ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := by
  intro D θ hθ X Ws hJ γ hγ
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ X
  choose g hg using fun t : ℝ => toUX_surj D X hJ (γ (Multiplicative.ofAdd t))
  have hmat : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) = Formalism.L2.Theta.mt X (g t) := fun t => by
    rw [← hg t]
    show (GlobalTheory.TripleRead.toUX X _ hJ (g t)).1.1 = _
    rw [GlobalTheory.TripleRead.toUX_val]
    rfl
  have inj : ∀ a b : GA D X, Formalism.L2.Theta.mt X a = Formalism.L2.Theta.mt X b → a = b := fun a b h =>
    Subtype.ext (Units.ext h)
  have mtmul : ∀ a b : GA D X, Formalism.L2.Theta.mt X (a * b) = Formalism.L2.Theta.mt X a * Formalism.L2.Theta.mt X b := fun a b => by
    simp [Formalism.L2.Theta.mt, map_mul]
  have hmul : ∀ s t, g (s + t) = g s * g t := fun s t => inj _ _ (by
    rw [mtmul, ← hmat, ← hmat, ← hmat, ofAdd_add, map_mul]
    rfl)
  have g0 : g 0 = 1 := inj _ _ (by
    rw [← hmat, ofAdd_zero, map_one]
    rfl)
  have hinf : ∀ t, g t ∈ GinfC X := fun t => mem_GinfC_of_at D X (g t) (by rw [← hmat]; exact hγ.2 _)
  have hcont : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.1.comp continuous_ofAdd))
  have hu : ∀ τ, Continuous fun t : ℝ => infMat D.sp.cm.sig X.gram (θ τ) (g t) := fun τ => by
    refine ((hcont.matrix_map (GlobalTheory.Member.Arch.continuous_inf _ _)).matrix_map
      (GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ))).congr fun t => ?_
    rw [hmat]
    rfl
  choose Y hY hYe using fun τ => GlobalTheory.T.oneParamUnitaryMatrix_eq_exp_lieAlgebra (gramAt D X τ) (fun t => infMat D.sp.cm.sig X.gram (θ τ) (g t)) (hu τ)
    (by rw [g0]; simp [infMat, HA.mat]; exact Matrix.map_one _ (by simp) (by simp))
    (fun s t => by rw [hmul]; exact R.2.2.2.1 _ _ _)
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ X (g t) τ)
  let L : GlobalTheory.SmoothForms.LieN X := fun τ => ⟨Y τ, hY τ⟩
  refine ⟨L, fun t => ?_⟩
  have hE := GlobalTheory.SmoothForms.isExpFam_expInf R (t • L)
  have e : GlobalTheory.SmoothForms.expInf θ X (t • L) = g t := R.2.2.1 _ hE.1 _ (hinf t) fun τ => by
    rw [hE.2 τ, hYe τ t]
    rfl
  rw [e]
  exact (hg t).symm

end GlobalTheory.LineDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def zlQ (B : BesL D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (GlobalTheory.Unf.FB.eLast D (σ + 1))

theorem rat_zlQ (B : BesL D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zEll B.L (σ + 1) B.ζ := by
  rw [zEll, ← GlobalTheory.Unf.FB.ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem gramQ_zlQ_mulVec_last (B : BesL D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply,
    GlobalTheory.Unf.FB.eLast, Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := _root_.GlobalTheory.Asc.FBx.exists_rat_eq_xLast D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := GlobalTheory.Unf.FB.gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (xLast B.d (vecB B.o B.ζ)) ⬝ (gA B.V ⬝ xLast B.d (vecB B.o B.ζ)) =
      adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by
    rw [← hx, ← rat_zlQ, ← GlobalTheory.Unf.FB.rat_gramQ, ← GlobalTheory.Unf.FB.rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [GlobalTheory.Unf.FB.rat_gramQ, hx, hA]
    have hz : zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) ⬝ u.1)
          = adj (zEll B.L (σ + 1) B.ζ ⬝ u.1) ⬝ (gA B.L ⬝ (zEll B.L (σ + 1) B.ζ ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by rw [hz]
  · ext g
    rw [hx]
    exact ((_root_.GlobalTheory.Asc.FBL.besGrp_act_xLast D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, GlobalTheory.Unf.FB.pairS_mul,
      GlobalTheory.Unf.FB.pairS_mul, hA]

end GlobalTheory.Asc.FBL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedDownIsTameThetaFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandTame

theorem integral_prod_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (F : α × β × γ × δ → ℂ) (hF : Integrable F (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))) :
    ∫ y, F y ∂(μ₁.prod (μ₂.prod (μ₃.prod μ₄))) = ∫ a, ∫ b, ∫ c, ∫ d, F (a, b, c, d) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hF]
  refine integral_congr_ae (hF.prod_right_ae.mono fun a ha => ?_)
  simp only
  rw [integral_prod _ ha]
  refine integral_congr_ae (ha.prod_right_ae.mono fun b hb => ?_)
  simp only
  rw [integral_prod _ hb]

theorem sfinite_of_finite {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simp only [hh f hf]; exact h.cont f hf
  · simp only [hh f hf]; exact h.bdd f hf
  · simp only [hh f hf]; rw [e _ hI]; exact h.sup f hf m α hα hI

theorem rapid_core {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {G : GA D S → ℂ} (hG : RapidDec S G) (k : ℕ) :
    ∃ C : ℝ, ∀ n ∈ flagN d, ∀ h, ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := _root_.GlobalTheory.HtWitt.quotHeight_witt D S S₀ ρ d
  obtain ⟨C', hC'⟩ := hG.decay (a * k)
  refine ⟨|C| ^ k * C', fun n hn h => ?_⟩
  have h1 : quotHeight S₀ h ≤ |C| * quotHeight S (n * d.emb0 h) ^ a :=
    (hC n hn h).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k
      ≤ ‖G (n * d.emb0 h)‖ * (|C| * quotHeight S (n * d.emb0 h) ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos S₀ h).le h1 k) (norm_nonneg _)
    _ = |C| ^ k * (‖G (n * d.emb0 h)‖ * quotHeight S (n * d.emb0 h) ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * C' := mul_le_mul_of_nonneg_left (hC' _) (by positivity)

theorem rapid_theta {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χ χz om) {φ : GA D S → ℂ} (hφ : RapidDec S φ) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀)
    (k : ℕ) : ∃ C : ℝ, ∀ h v, ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ S L χ χz om hom Φ₀ hΦ
  obtain ⟨C', hC'⟩ := hφ.decay (a + k)
  refine ⟨|C| * C', fun h v => ?_⟩
  have h1 : ‖om (h, 1) Φ₀ v‖ ≤ |C| * quotHeight S h ^ a := by
    have := hC h 1 v
    rw [quotHeight_of_mem L (one_mem _), mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k
      ≤ ‖φ h‖ * (|C| * quotHeight S h ^ a) * quotHeight S h ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (pow_pos (quotHeight_pos S _) k).le
    _ = |C| * (‖φ h‖ * quotHeight S h ^ (a + k)) := by ring
    _ ≤ |C| * C' := mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)

theorem handP₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B),
    ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G →
    IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ hφ hG hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.L.rank J.W₀.rank
  haveI : SecondCountableTopology (WO J.W₀ B.L) := i3
  haveI : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; exact ENNReal.one_ne_top)
  let Y : Type := GA D B.A × flagN B.d × GA D J.W₀ × WO J.W₀ B.L
  let m : Measure Y := (B.vA.μ.restrict B.vA.𝓕).prod ((B.vN.ν.restrict B.vN.𝓝).prod
    ((J.v0.μ.restrict J.v0.𝓕).prod (vL.μ.restrict vL.𝓕)))
  haveI : IsFiniteMeasure m := by dsimp only [m]; infer_instance
  haveI : SFinite m := sfinite_of_finite m
  let c : Y → ℂ := fun y => G (y.2.1.1 * embA B.d B.o y.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1) *
    (φ y.2.2.1 * star (omz (y.2.2.1, 1) Φ₀ y.2.2.2))
  have hn : Continuous fun y : Y => (y.2.1.1 : GA D B.V) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h0 : Continuous fun y : Y => y.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun y : Y => y.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have he : Continuous fun y : Y => B.o.emb (y.1, 1) := B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)
  have hw : Continuous fun y : Y => (B.o.resT J.W₀).symm (0, y.2.2.2) :=
    (B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk hv)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V).2.2.2.2.1
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ
  have hc : Continuous c :=
    ((hG.continuous.comp (hn.mul (B.d.continuous_embed.comp he))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))).mul
      ((hφ.continuous.comp h0).mul (continuous_star.comp (hJ.comp ((h0.prodMk continuous_const).prodMk hv))))
  have hint : ∀ k : ℕ, Integrable
      (fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k) m := by
    intro k
    obtain ⟨C₁, h₁⟩ := rapid_core B.d hG k
    obtain ⟨C₂, h₂⟩ := rapid_theta homz hφ hΦ k
    have hcc : Continuous fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k :=
      hc.norm.mul ((((continuous_quotHeight _).comp h0).mul ((continuous_quotHeight _).comp he)).pow k)
    refine Integrable.of_bound hcc.measurable.aestronglyMeasurable (C₁ * C₂) (.of_forall fun y => ?_)
    have p1 := quotHeight_pos J.W₀ y.2.2.1
    have p2 := quotHeight_pos B.V₀ (B.o.emb (y.1, 1))
    have n1 : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1‖ = 1 := hψ.1.2.1 _
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := h₁ _ y.2.1.2 (B.o.emb (y.1, 1))
    have a2 := h₂ y.2.2.1 y.2.2.2
    calc ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k
        = (‖G (y.2.1.1 * B.d.emb0 (B.o.emb (y.1, 1)))‖ * quotHeight B.V₀ (B.o.emb (y.1, 1)) ^ k) *
          (‖φ y.2.2.1‖ * ‖omz (y.2.2.1, 1) Φ₀ y.2.2.2‖ * quotHeight J.W₀ y.2.2.1 ^ k) := by
          simp only [c, norm_mul, norm_star, n1, embA_apply, mul_pow]; ring
      _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)
  obtain ⟨hI, hT⟩ := _root_.GlobalTheory.KerTame.kernel_tame D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ Y m c (fun y => y.2.2.1) (fun y => B.o.emb (y.1, 1))
    (fun y => (B.o.resT J.W₀).symm (0, y.2.2.2)) hc.measurable h0 he hw hint
  refine tame_congr hψ hT fun f hf => ?_
  refine Eq.trans ?_ (integral_prod_four _ _ _ _ _ (hI f hf)).symm
  simp only [BesL.per, besPer, GlobalTheory.MixPer.besFun, handP, contractT, thPair]
  refine integral_congr_ae (.of_forall fun a => ?_)
  refine integral_congr_ae (.of_forall fun b => ?_)
  simp only
  rw [mul_assoc, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [c]
  ring

end GlobalTheory.HandTame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfTensEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchCancel

theorem eq_of_tens_eq : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (r : (κ → AF F) → ℂ),
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) → (∃ x, r x ≠ 0) →
    ∀ f₁ f₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₂ r → f₁ = f₂ := by
  intro F _ _ κ _ r hr hne f₁ f₂ h
  obtain ⟨x₀, hx₀⟩ := hne
  refine DFunLike.ext f₁ f₂ fun y => ?_
  let z : κ → AF F := fun i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)), 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
    show u * z i = 0
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      show u.2 * 0 = 0
      rw [mul_zero]
  have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x₀ + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x₀ i).1 +
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i))) = y i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) + (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)) = y i
    exact add_sub_cancel _ _
  have h2 := congrFun h (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at h2
  rw [hev, hr x₀ z hz] at h2
  exact mul_right_cancel₀ hx₀ h2

end GlobalTheory.ArchCancel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStabStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) = 0) →
    ∀ T₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∃ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
      (l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J),
    T₀ ⊆ S ∧ (∀ x ∈ l, x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F x.1)) ∧
    h = (l.map Prod.snd).prod * k ∧
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  first | exact @GlobalTheory.FinDecomp.exists_prod_local_mul_latStab | exact GlobalTheory.FinDecomp.exists_prod_local_mul_latStab | (intros; apply GlobalTheory.FinDecomp.exists_prod_local_mul_latStab <;> assumption)
end

