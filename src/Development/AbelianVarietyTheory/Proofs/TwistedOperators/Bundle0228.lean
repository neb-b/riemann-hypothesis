module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProduc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanProd

variable {D : D7}

theorem symplOH_iso_mid {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a + midPart V V' W B x) = 0 := by
  have rat_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
      (N : Matrix (Fin m) (Fin n) D.host.E) :
      GlobalTheory.MixModel.rat (M * N) = GlobalTheory.MixModel.rat M * GlobalTheory.MixModel.rat N := Matrix.map_mul
  have adj_mul {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hO_eq_trace (T : HSp D) (x y : WO V T) :
      hO V T x y = (GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA T * x))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  set P : Mx D r V.rank := GlobalTheory.MixModel.rat (adj D C * V.gram) with hP
  set Q : Mx D V'.rank V.rank := GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) with hQ
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  have hG' := GlobalTheory.MixModel.gramInv_conjTranspose V'
  have hU := GlobalTheory.MixModel.gram_isUnit_det V
  have hC0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hO : adj D C * V.gram * B = 0 := hs.orth
  have k1 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj P = 0 := by
    rw [hP, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (Cᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * C = 0 at hC0
      rw [Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc (Cᴴ * V.gram),
        ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, hC0]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have k2 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj Q = 0 := by
    rw [hP, hQ, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * Bᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * B = 0 at hO
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, hG', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc (Cᴴ * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, ← Matrix.mul_assoc, hO, Matrix.zero_mul]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have e1 : isoPart V W C (q₀.map (incA D)) = GlobalTheory.MixModel.rat q₀ * P := rfl
  have e2 : isoPart V W C a + midPart V V' W B x = a * P + x * Q := rfl
  have k3 : P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) = 0 := by
    rw [GlobalTheory.MixModel.adj_add, adj_mul, adj_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, k1, k2, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [GlobalTheory.MixModel.symplOH_eq, hO_eq_trace, e1, e2]
  have e3 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * P + x * Q) * (GlobalTheory.MixModel.gA W * (GlobalTheory.MixModel.rat q₀ * P))) =
      (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) * P := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  have e4 : P * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q) * GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) =
      (P * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj (a * P + x * Q)) * (GlobalTheory.MixModel.gA W * GlobalTheory.MixModel.rat q₀) := by
    simp only [Matrix.mul_assoc]
  rw [e4, k3, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem iso_periodic {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (γ + a) + midPart V V' W B x) = f (isoPart V W C a + midPart V V' W B x) := by
  rintro _ ⟨q₀, rfl⟩ a
  have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
  have hadd : isoPart V W C (q₀.map (incA D) + a) = isoPart V W C (q₀.map (incA D)) + isoPart V W C a :=
    Matrix.add_mul _ _ _
  have hrat : ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := Matrix.map_mul
  rw [e3, hadd, add_assoc, ← hrat, hf.quasi, hrat, symplOH_iso_mid hs, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.IsoMeanProd

namespace GlobalTheory.IsoMeanProd

theorem mean_iso_mul_star : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' F G hF hG
  have hμ1 : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI hfin1 : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hμ' h𝓕').2⟩
  haveI hsf1 : SigmaFinite (μ.restrict 𝓨) := @IsFiniteMeasure.toSigmaFinite _ _ _ hfin1
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ hsf1
  haveI : SigmaFinite (μ'.restrict 𝓕') := inferInstance
  haveI : SFinite (μ'.restrict 𝓕') := inferInstance
  obtain ⟨cF, hcF⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hF
  obtain ⟨cG, hcG⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hG
  have ciso : Continuous (fun y : Mx D W.rank r => isoPart V W C y) := continuous_id.matrix_mul continuous_const
  have cmid : Continuous (fun x : WO V' W => midPart V V' W B x) := continuous_id.matrix_mul continuous_const
  obtain ⟨H, hH⟩ : ∃ H : Mx D W.rank r → Mx D W.rank r → WO V' W → ℂ, H = fun y y' x =>
      F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) := ⟨_, rfl⟩
  have hHb : ∀ y y' x, ‖H y y' x‖ ≤ cF * cG := by
    intro y y' x
    rw [hH, norm_mul, norm_star]
    exact mul_le_mul (hcF _) (hcG _) (norm_nonneg _) ((norm_nonneg _).trans (hcF 0))
  have hHc : Continuous fun p : Mx D W.rank r × Mx D W.rank r × WO V' W => H p.1 p.2.1 p.2.2 := by
    rw [hH]
    exact (hF.cont.comp ((ciso.comp (continuous_fst.add continuous_snd.fst)).add (cmid.comp continuous_snd.snd))).mul
      (continuous_star.comp (hG.cont.comp ((ciso.comp continuous_snd.fst).add (cmid.comp continuous_snd.snd))))
  have hint : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X)
      [IsFiniteMeasure ν] (g : X → ℂ), Continuous g → (∀ z, ‖g z‖ ≤ cF * cG) → Integrable g ν :=
    fun ν _ g hg hb => Integrable.of_bound hg.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hI1 : ∀ y, Integrable (Function.uncurry fun y' x => H y y' x) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    fun y => hint _ _ (hHc.comp (continuous_const.prodMk continuous_id)) fun z => hHb _ _ _
  have hI3 : Integrable (fun q : (Mx D W.rank r × WO V' W) × Mx D W.rank r => H q.1.1 q.2 q.1.2)
      (((μ.restrict 𝓨).prod (μ'.restrict 𝓕')).prod (μ.restrict 𝓨)) :=
    hint _ _ (hHc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))) fun z => hHb _ _ _
  have hI2 : Integrable (Function.uncurry fun y x => ∫ y', H y y' x ∂(μ.restrict 𝓨))
      ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := hI3.integral_prod_left
  have hI4 : ∀ x, Integrable (Function.uncurry fun y y' => H y y' x) ((μ.restrict 𝓨).prod (μ.restrict 𝓨)) :=
    fun x => hint _ _ (hHc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) fun z => hHb _ _ _
  have step4 : ∀ x y', ∫ y in 𝓨, H y y' x ∂μ =
      res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) := by
    intro x y'
    rw [hH]
    simp only
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.MixModel.covolOne_integral_add hμ1 (fun a => F (isoPart V W C a + midPart V V' W B x))
      (iso_periodic hs hF x) y'
  have step5 : ∀ x, ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ =
      res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_conj
  have e0 : ∀ y y' x, F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) = H y y' x := by
    intro y y' x; rw [hH]
  simp only [e0]
  calc ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', H y y' x ∂μ' ∂μ ∂μ
      = ∫ y in 𝓨, ∫ x in 𝓕', ∫ y' in 𝓨, H y y' x ∂μ ∂μ' ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_integral_swap (hI1 y))
    _ = ∫ x in 𝓕', ∫ y in 𝓨, ∫ y' in 𝓨, H y y' x ∂μ ∂μ ∂μ' := integral_integral_swap hI2
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, ∫ y in 𝓨, H y y' x ∂μ ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_integral_swap (hI4 x))
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          integral_congr_ae (Filter.Eventually.of_forall fun y' => step4 x y'))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => step5 x)

end GlobalTheory.IsoMeanProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModel
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HCModIrred

open GlobalTheory.TypeSum Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

section Model

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_of_dense (h : Std ε σ) {W : Submodule ℂ H} (hd : Dense (W : Set H))
    (hW : ∀ w ∈ W, IsKFin ε σ w) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) {v : H} (hv : IsKFin ε σ v) :
    v ∈ W := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  have havgW : ∀ e : KG ε → ℂ, Continuous e → ∀ x ∈ W, kAvg ε σ e x ∈ W := by
    intro e he x hx
    obtain ⟨S, hS, hxS, hKS⟩ := hW x hx
    haveI := hS
    haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
    have hKSW : IsKStableOn ε σ (S ⊓ W) := fun g hg y hy =>
      Submodule.mem_inf.2 ⟨hKS g hg y (Submodule.mem_inf.1 hy).1, hK g hg y (Submodule.mem_inf.1 hy).2⟩
    exact (Submodule.mem_inf.1 (c4 e he _ inferInstance hKSW x (Submodule.mem_inf.2 ⟨hxS, hx⟩))).2
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ W := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (W ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right W F
    have hcl : IsClosed (Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (W : Set H) ⊆ Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact havgW e hc x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hd w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hKS⟩ := hv
  haveI := hS
  haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ W).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hKS⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hKS y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

theorem inner_exp_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hXg : inG ε X) (hX : ∀ w ∈ W, dRep σ X w ∈ W)
    {a : H} (ha : a ∈ W) {y : H} (hy : y ∈ Wᗮ) (t : ℝ) :
    ⟪y, σ (NormedSpace.exp (t • X)) a⟫_ℂ = 0 := by
  have hXl : X ∈ GlobalTheory.SmoothGlob.lieSet ε := hXg
  have hsplit : ∀ s t : ℝ, NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
    intro s t
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left t |>.smul_right (s - t))]
    congr 1
    rw [← add_smul]; congr 1; ring
  have hderiv : ∀ v, IsKFin ε σ v → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (σ (NormedSpace.exp (t • X)) (dRep σ X v)) t := by
    intro v hv t
    have han := (hHC.analytic hU hI hv).analytic_exp (one_mem_UJ ε) hXg 0
    simp only [one_mul] at han
    have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (dRep σ X v) 0 :=
      han.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) v) (dRep σ X v) t := by
      have := HasDerivAt.comp_sub_const (f := fun s : ℝ => σ (NormedSpace.exp (s • X)) v) t t (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp (s • X)) v = σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((s - t) • X)) v)
    rw [hsplit s t, sigma_mul hU (exp_mem_UJ hXl t) (exp_mem_UJ hXl (s - t))]
  have hmem : ∀ k : ℕ, (dRep σ X)^[k] a ∈ W := by
    intro k
    induction k with
    | zero => exact ha
    | succ k ih => rw [Function.iterate_succ_apply']; exact hX _ ih
  let f : ℕ → ℝ → ℂ := fun k s => ⟪y, σ (NormedSpace.exp (s • X)) ((dRep σ X)^[k] a)⟫_ℂ
  have hf : ∀ k s, HasDerivAt (f k) (f (k + 1) s) s := by
    intro k s
    have h := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hderiv _ (hW _ (hmem k)) s)
    simp only [f, Function.iterate_succ_apply']
    exact h
  have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ, ih]; funext s; exact (hf k s).deriv
  have hA : AnalyticOnNhd ℝ (f 0) Set.univ := by
    intro s _
    have := ((hHC.analytic hU hI (hW a ha)).clm ((innerSL ℂ y).restrictScalars ℝ)).analytic_exp (one_mem_UJ ε) hXg s
    simp only [one_mul] at this
    exact this
  have h0 : ∀ k, f k 0 = 0 := by
    intro k
    simp only [f, zero_smul, NormedSpace.exp_zero, sigma_one hU]
    exact Submodule.inner_left_of_mem_orthogonal (hmem k) hy
  have htop : analyticOrderAt (f 0) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)]
    intro i _
    rw [hit, h0]
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)

theorem dense_of_stable (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    (hX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) (h0 : W ≠ ⊥) :
    Dense (W : Set H) := by
  have hexp : ∀ X, inG ε X → ∀ x ∈ W.topologicalClosure, σ (NormedSpace.exp X) x ∈ W.topologicalClosure := by
    intro X hXg x hx
    have hW1 : ∀ a ∈ W, σ (NormedSpace.exp X) a ∈ W.topologicalClosure := by
      intro a ha
      rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
      intro y hy
      have := inner_exp_eq_zero hHC hU hI hW hXg (hX X hXg) ha hy 1
      rwa [one_smul] at this
    have hcl : IsClosed ((σ (NormedSpace.exp X)) ⁻¹' (W.topologicalClosure : Set H)) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
    exact closure_minimal (fun a ha => hW1 a ha) hcl hx
  have hKc : ∀ k ∈ Kset ε, ∀ x ∈ W.topologicalClosure, σ k x ∈ W.topologicalClosure := fun k hk x hx =>
    map_mem_closure (σ k).continuous hx (hK k hk)
  have hinv : ∀ g ∈ UJset ε, ∀ x ∈ W.topologicalClosure, σ g x ∈ W.topologicalClosure := by
    intro g hg x hx
    obtain ⟨k, P, hk, hP, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
    have hPl : P ∈ GlobalTheory.SmoothGlob.lieSet ε := hP.1
    have hPe : NormedSpace.exp P ∈ UJset ε := by simpa using exp_mem_UJ hPl 1
    rw [sigma_mul hU (K_le_UJ hk) hPe]
    exact hKc k hk _ (hexp P hP.1 x hx)
  rcases hI _ (Submodule.isClosed_topologicalClosure W) hinv with h | h
  · exact absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) h0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end Model


open Formalism.IndefR.Mult in
theorem kFin_le_of_stable : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →
    (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  intro hHC D V S M τ W hWk hX hK h0
  obtain ⟨hc, -, hU, hI, -⟩ := M.ds τ
  haveI := hc
  have hfr : IsUnit (M.fr τ) := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hW : ∀ w ∈ W, IsKFin (M.ε τ) (M.σ τ) w := fun w hw => hWk hw
  have hX' : ∀ X, inG (M.ε τ) X → ∀ w ∈ W, dRep (M.σ τ) X w ∈ W := by
    intro X hXg w hw
    have hXg' : Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X = 0 := hXg
    have hmem : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
      show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
      rw [← M.fr_gram τ]
      have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
      calc ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ) +
            (M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ)
          = (M.fr τ)ᴴ * Xᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Jm (M.ε τ) * M.fr τ +
            (M.fr τ)ᴴ * Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * X * M.fr τ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (M.fr τ)ᴴ * (Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X) * M.fr τ := by
            rw [h1, Matrix.mul_nonsing_inv _ hd]
            simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hXg']; simp
    have e : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
      unfold dRep
      congr 1
      funext t
      rw [DSModel.rep, GlobalTheory.SmVec.exp_conj_inv hfr X t]
      congr 2
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [← e]
    exact hX _ hmem w hw
  have hK' : ∀ k ∈ Kset (M.ε τ), ∀ w ∈ W, M.σ τ k w ∈ W := by
    intro k hk w hw
    have e : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hm : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      show M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [e]; exact hk
    have := hK _ hm w hw
    rwa [DSModel.rep, e] at this
  have hdense := dense_of_stable hHC hU hI hW hX' hK' h0
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  intro v hv
  exact mem_of_dense hstd hdense hW hK' hv

end GlobalTheory.HCModIrred

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefined
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrPhiOK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}

theorem phiOK_of (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [Field k] [Algebra F k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace (HA k σ J)] [SecondCountableTopology (HA k σ J)]
    [T2Space (HA k σ J)] (hfin : Finite (Cls P k))
    (hU : ∀ μ : Measure (HA k σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (hpr : ∀ g : HA k σ J, IsRegSS (matHom k σ J g).1 → IsProperOrbit (cent g) g)
    (μ : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ) [hμ : μ.IsHaarMeasure]
    [hdt : dt.IsHaarMeasure] (hf : Continuous f) (hc : HasCompactSupport f) : PhiOK (J := J) μ dt f := by
  refine ⟨Set.toFinite _, fun x φ h => ?_⟩
  haveI := hU μ hμ
  set q : XSet P k J := ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ with hq
  obtain ⟨hx0, h0⟩ := q.2.choose_spec.choose_spec
  set x0 := q.2.choose
  set φ0 := q.2.choose_spec.choose
  change HasOrbInt μ (gam h) (centMeas h dt) f (orbInt μ (gam h0) (centMeas h0 dt) f)

  have halg0 := _root_.GlobalTheory.TrEll.gam_charpoly_regular_cent F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e0, he0, hm0⟩ := _root_.GlobalTheory.TorCentTop.torEquiv_cent F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e, he, hm⟩ := _root_.GlobalTheory.TorCentTop.torEquiv_cent F E σ hσ r n P J hJ k x φ h
  haveI : (centMeas h0 dt).IsHaarMeasure := by rw [hm0]; exact e0.isHaarMeasure_map dt
  haveI : (centMeas h0 dt).IsMulRightInvariant :=
    isMulRightInvariant_cent (isMulCommutative_cent_HA halg0.2.1) _
  have H0 : HasOrbInt μ (gam h0) (centMeas h0 dt) f (orbInt μ (gam h0) (centMeas h0 dt) f) :=
    (hpr _ halg0.2.1).hasOrbInt hf hc

  obtain ⟨g, hg⟩ := (_root_.GlobalTheory.TrEll.cls_conj_torus F E σ hσ r n P J hJ k x0 φ0 h0 x φ h).1 (by rw [hx0])
  have hgam : g * gam h0 * g⁻¹ = gam h := (hg _).symm
  have hmeas : centMeas h dt = (centMeas h0 dt).map (centEquiv (conjEquiv g) (gam h0) hgam) := by
    rw [hm, hm0, Measure.map_map (map_continuous _).measurable (map_continuous _).measurable]
    congr 1
    funext t
    apply Subtype.ext
    change (e t).1 = g * (e0 t).1 * g⁻¹
    rw [he, he0, hg]
  rw [hmeas]
  exact ((hasOrbInt_conj (dh := μ) (dt := centMeas h0 dt) g hgam f _).1).2 H0

end GlobalTheory.TrPhiOK


open GlobalTheory.TrPhiOK in
theorem GlobalTheory.TrPhiOK.phiOK_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  intro F E _ _ _ _ _ σ hσ r n P J hJ
  have hfin := _root_.GlobalTheory.SqCls.finite_cls F E σ hσ r P
  refine ⟨fun v μ dt f hμ hdt hf hc => ?_, fun w μ dt f hμ hdt hf hc => ?_⟩
  · have hU := (GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ n J hJ v).1
    exact phiOK_of hσ hJ (Fv F v) (hfin.1 v) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GLoc hσ hJ hg) μ dt f hf hc
  · haveI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := σ) w.Completion hσ hJ).1
    exact phiOK_of hσ hJ w.Completion (hfin.2 w) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GArch hσ hJ hg) μ dt f hf hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

noncomputable section

namespace GlobalTheory.LeviNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phase (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace))

def resNorm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)) (f : WO V W → ℂ) (u : Mx D W.rank r) : ℂ :=
  ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x *
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x) ∂μ'

theorem phase_apply (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) :
    phase ψ W y u = ψ (Algebra.trace (AF D.host.F) (AE D)
      (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace)) := rfl

end GlobalTheory.LeviNorm

end
end

