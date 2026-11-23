module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationIntertwines
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

theorem hasDbl_transp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (incM F X.J) d' d₁' T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij T hTe d' d₁' hd' hd₁'
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hM₁ he
  obtain ⟨e', hL', hinv⟩ := _root_.GlobalTheory.LocOpInv.isLocOp_inv e hL hbij
  have hTe' : ∀ Φ ∈ schA F (Fin n × Fin d), T.symm Φ = e' Φ := by
    intro Φ hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    rw [← hTe Ψ hΨ, LinearEquiv.symm_apply_apply, hTe Ψ hΨ, hinv Ψ hΨ]
  have hmem : ∀ Φ, Φ ∈ schA F (Fin n × Fin d) ↔ T Φ ∈ schA F (Fin n × Fin d) := by
    intro Φ
    constructor
    · intro h
      rw [hTe Φ h]
      exact hbij.mapsTo h
    · intro h
      obtain ⟨Ψ, hΨ, hΨe⟩ := hbij.surjOn h
      have h1 : T Ψ = T Φ := (hTe Ψ hΨ).trans hΨe
      rw [← T.injective h1]
      exact hΨ
  have hn : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hd1 : (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d), T (d'.rho B.ψ w Φ) = d₁'.rho B.ψ w (T Φ) := by
    intro w Φ hΦ
    have e1 : ∀ Ψ, d'.rho B.ψ w Ψ = M.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd' wᵀ, Matrix.transpose_transpose]
    have e2 : ∀ Ψ, d₁'.rho B.ψ w Ψ = M₁.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd₁' wᵀ, Matrix.transpose_transpose]
    have hρ : M.co.rho B.ψ wᵀ Φ ∈ schA F (Fin n × Fin d) :=
      GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ _ Φ hΦ
    have h := he.Heisenberg₂ wᵀ Φ hΦ
    rw [hn, hd1, Matrix.one_mul, Matrix.mul_one] at h
    rw [e1, e2, hTe _ hρ, hTe Φ hΦ, h]
  have hunit : ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨C, hC⟩ := GlobalTheory.ModelTrUnit.exists_const hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij μ hμ
    exact ⟨C, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hC Φ hΦ⟩
  exact hasDbl_of_loc (cA σ) (-1) (incM F W.J) (incM F X.J) B.ψ hψ d' d₁' T e e' hL hL' hTe hTe' hmem Heisenberg₂ hunit

end GlobalTheory.DblTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesSchwartz
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

namespace GlobalTheory.DblInt

theorem evDbl_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
    (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem hasDbl_of_tame {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E]
    (c : E →ₐ[AF F] E) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (hT : IsGoodInt (adeleClass F) ψ d d₁ T) (ht : IsTame F T.toLinearMap) (hti : IsTame F T.symm.toLinearMap) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  obtain ⟨hsp, hheis, hadm, hunit⟩ := hT
  have hS : IsTame F (conjMap T.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ ht
  have hSi : IsTame F (conjMap T.symm.toLinearMap) := GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hti
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hS
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ ht
  have hRi : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ hSi
  have hLi : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hti
  have hD : IsTame F (dblE T).toLinearMap := hR.comp hL
  have hDi : IsTame F (dblE T).symm.toLinearMap := hLi.comp hRi
  have hstar : ∀ φ : (κ → AF F) → ℂ, φ ∈ schA F κ → star φ ∈ schA F κ := fun φ hφ =>
    GlobalTheory.SchAConj.star_mem_schA F κ φ hφ
  have hSsp : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    rw [conjE_apply]
    constructor
    · intro h
      exact hstar _ ((hsp _).1 (hstar _ h))
    · intro h
      have h1 : T (star φ) ∈ schA F κ := by simpa using hstar _ h
      simpa using hstar _ ((hsp _).2 h1)
  have hTL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := hunit
  have hSL : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨c₀, hc₀⟩ := hunit μ hμ
    refine ⟨c₀, fun φ hφ => ?_⟩
    have h := hc₀ (star φ) (hstar φ hφ)
    simp only [conjMap_apply, Pi.star_apply, enorm_eq_nnnorm, nnnorm_star, LinearEquiv.coe_coe] at h ⊢
    exact h
  refine ⟨dblCo c d₁, dblE T, conjE T, dblCo_isDblCoord c d₁,
    ⟨fun φ => ⟨fun h => hD.mapsTo φ h, fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hD.comp_adm hl, fun hl => ?_⟩,
      fun μ hμ => ?_⟩, hSsp, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hDi.mapsTo _ h
    rw [show (dblE T).symm.toLinearMap ((dblE T) φ) = φ from (dblE T).symm_apply_apply φ] at this
    exact this
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨w.toCols₁, w.toCols₂, (Matrix.fromCols_toCols w).symm⟩
    have e1 : dd.rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d.e w₁).1 (d.e w₂).1, Sum.elim (d.e w₁).2 (-(d.e w₂).2)) := by
      unfold Darboux.rho; rw [hdd]
    have e2 : (dblCo c d₁).rho ψ (Matrix.fromCols w₁ w₂) =
        schr ψ (Sum.elim (d₁.e w₁).1 (d₁.e w₂).1, Sum.elim (d₁.e w₁).2 (-(d₁.e w₂).2)) := by
      unfold Darboux.rho; rw [dblCo_isDblCoord]
    rw [e1, e2]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hDi.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨c₁, hc₁⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ T.toLinearMap ht hTL).1 μ hμ
    obtain ⟨c₂, hc₂⟩ := (GlobalTheory.T.weil_operator_haar_norm_proportional F κ κ (conjMap T.toLinearMap) hS hSL).2 μ hμ
    refine ⟨c₁ * c₂, fun Φ hΦ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) Φ) x‖ₑ ^ 2 ∂μ = _
    rw [hc₁ _ (hR.mapsTo Φ hΦ), hc₂ Φ hΦ, mul_assoc]

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTs : ∀ x, x ∈ schA F (Fin n × Fin d) ↔ T x ∈ schA F (Fin n × Fin d) := fun x => by
    constructor
    · intro hx
      rw [hTe x hx]
      exact hbij.mapsTo hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
      have : T y = T x := by rw [hTe y hy, hyx]
      rw [← T.injective this]
      exact hy
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        _root_.GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (_root_.GlobalTheory.ModelAdm.model_admissible_iff_evaluation hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans
        (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := _root_.GlobalTheory.ModelTrUnit.exists_const hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  have ht : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, inst, P, g', hg', hPe⟩ := GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hpair.good hM₁ hev g hg
    refine ⟨ι, inst, P, g', hg', fun f => ?_⟩
    rw [← hPe f]
    exact hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  have hti : IsTame F T.symm.toLinearMap :=
    _root_.GlobalTheory.InvTame.isTame_inv hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T.symm.toLinearMap
      (fun Φ hΦ => by rw [← hTe Φ hΦ]; simp)
  exact hasDbl_of_tame (cA σ) B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) (-1) _ _ M.co M₁.co T hgood ht hti

end GlobalTheory.DblInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulEqZeroOfMemMap
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.LiftSys

theorem algHom_mem_map {R B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (I : Ideal R) (α : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    α b ∈ I.map (algebraMap R B') := by
  have h := Ideal.mem_map_of_mem (α : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

theorem mul_eq_zero_of_mem_map {R B' : Type} [CommRing R] [CommRing B'] [Algebra R B'] {I : Ideal R}
    (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) :
    x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI B'] at h
  simpa using h

theorem exists_unique_formExt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (U : AffOp X₀) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (p : B →+* Sec s₀ U.unop.1), SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ (α : B →ₐ[R] B') (E : GlobForm s₀ →+ B'), (∀ (r : R) w, E (π r • w) = r • E w) → (∀ w, E w ∈ I.map (algebraMap R B')) → ∃! θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) ∧ (∀ w, θ w ∈ I.map (algebraMap R B')) ∧ ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar U B B' _ _ _ _ p hsemi hsurj hker α E hE hEmem
  have hb : IsBaseChange (Sec s₀ U.unop.1) (evForm s₀ U) := hpar U
  let l : Sec s₀ U.unop.1 → B := Function.surjInv hsurj
  have hl : ∀ s, p (l s) = s := Function.surjInv_eq hsurj
  have key : ∀ b b' : B, p b = p b' → ∀ x ∈ I.map (algebraMap R B'), α b * x = α b' * x := by
    intro b b' h x hx
    have h1 : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have h2 := mul_eq_zero_of_mem_map hI (algHom_mem_map I α h1) hx
    rw [map_sub, sub_mul] at h2
    exact sub_eq_zero.1 h2
  let g : Sec s₀ U.unop.1 → GlobForm s₀ →+ B' := fun s =>
    AddMonoidHom.mk' (fun w => α (l s) * E w) (fun w w' => by simp [mul_add])
  let f : Sec s₀ U.unop.1 →+ GlobForm s₀ →+ B' :=
    AddMonoidHom.mk' g (fun s t => by
      ext w
      show α (l (s + t)) * E w = α (l s) * E w + α (l t) * E w
      rw [key (l (s + t)) (l s + l t) (by rw [map_add (f := _), hl, hl, hl]) _ (hEmem w), map_add (f := _), add_mul])
  have hf : ∀ (r : R₀) (s : Sec s₀ U.unop.1) (w : GlobForm s₀), f (r • s) w = f s (r • w) := by
    intro r s w
    obtain ⟨r', rfl⟩ := hπ r
    show α (l (π r' • s)) * E w = α (l s) * E (π r' • w)
    rw [key (l (π r' • s)) (r' • l s) (by rw [hl, hsemi, hl]) _ (hEmem w), hE, map_smul,
      smul_mul_assoc, mul_smul_comm]
  let T := TensorProduct.liftAddHom f hf
  let θ : Ω[Sec s₀ U.unop.1⁄R₀] →+ B' := T.comp (hb.equiv.symm.toLinearMap.toAddMonoidHom)
  have hθ : ∀ x, θ x = T (hb.equiv.symm x) := fun _ => rfl
  have hsm : ∀ (b : B) (t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀), T (p b • t) = α b * T t := by
    intro b t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show α (l (p b • s)) * E w = α b * (α (l s) * E w)
      rw [key (l (p b • s)) (b * l s) (by rw [hl, map_mul, hl, smul_eq_mul]) _ (hEmem w), map_mul, mul_assoc]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  have hmem : ∀ t : Sec s₀ U.unop.1 ⊗[R₀] GlobForm s₀, T t ∈ I.map (algebraMap R B') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w => exact Ideal.mul_mem_left _ _ (hEmem w)
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  have hev : ∀ w : GlobForm s₀, θ (w.1 U) = E w := by
    intro w
    have h1 : hb.equiv.symm (w.1 U) = 1 ⊗ₜ w := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]; rfl
    rw [hθ, h1, TensorProduct.liftAddHom_tmul]
    show α (l 1) * E w = E w
    rw [key (l 1) 1 (by rw [hl, map_one]) _ (hEmem w), map_one, one_mul]
  refine ⟨θ, ⟨fun b w => ?_, fun w => hmem _, hev⟩, fun y ⟨hy1, _, hy3⟩ => ?_⟩
  · rw [hθ, hθ, LinearEquiv.map_smul, hsm]
  · ext x
    refine hb.inductionOn x ?_ ?_ ?_
    · intro w
      exact (hy3 w).trans (hev w).symm
    · intro s n hn
      rw [← hl s, hy1, hn, hθ, hθ, LinearEquiv.map_smul, hsm]
    · intro n₁ n₂ h₁ h₂
      rw [map_add (f := _), map_add (f := _), h₁, h₂]

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

variable {S P : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {h₁ : H₁.left ⟶ P} {h₂ : H₂.left ⟶ P}
  {pS : P ⟶ S}

theorem mul_mem_range (e₁ : h₁ ≫ pS = H₁.hom) (e₂ : h₂ ≫ pS = H₂.hom) [IsOpenImmersion h₂]
    (hm : MulAgree H₁ H₂ h₁ h₂) {T : Scheme.{0}} {t : T ⟶ S} (a b : Over.mk t ⟶ H₁)
    (ha : ∀ y, h₁ (a.left y) ∈ Set.range h₂) (hb : ∀ y, h₁ (b.left y) ∈ Set.range h₂) :
    ∀ y, h₁ ((a * b).left y) ∈ Set.range h₂ := by
  have lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) →
      ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂ := by
    intro c hc
    let c'' := IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)
    have ec : c'' ≫ h₂ = c.left ≫ h₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk c'' ?_, ec.symm⟩
    show c'' ≫ H₂.hom = t
    rw [← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]
    rfl
  obtain ⟨a', ea⟩ := lift a ha
  obtain ⟨b', eb⟩ := lift b hb
  have := hm T t t a b a' b' ea eb
  intro y
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end GlobalTheory.OpenSubgrp

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_inv' {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) :
    ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  (Category.assoc _ _ _).symm

theorem range_subset : ∀ (S P : Scheme.{0}) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P), ∀ pS : P ⟶ S, h₁ ≫ pS = H₁.hom → h₂ ≫ pS = H₂.hom → IsOpenImmersion h₁ →
    IsOpenImmersion h₂ → Smooth H₁.hom → GeometricallyConnected H₁.hom → MulAgree H₁ H₂ h₁ h₂ →
    OneAgree (𝟙 S) (𝟙 S) H₁ H₂ h₁ h₂ → Set.range h₁ ⊆ Set.range h₂ := by
  intro S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho
  have : GeometricallyIntegral H₁.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁
  let WO : H₁.left.Opens := h₁ ⁻¹ᵁ h₂.opensRange
  have hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂ := fun x => Iff.rfl

  have hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s := by
    intro s
    refine ⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩
    · rw [hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  let f := fst H₁ H₁
  let g := snd H₁ H₁
  let a : H₁ ⊗ H₁ ⟶ H₁ := g⁻¹ * f
  let O : (H₁ ⊗ H₁).left.Opens := a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO
  let Y : Over S := Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)
  let j : Y ⟶ H₁ ⊗ H₁ := Over.homMk O.ι rfl
  have e1 : (j ≫ g) * (j ≫ a) = j ≫ f := by
    rw [MonObj.comp_mul, comp_inv', mul_inv_cancel_left]
  have inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂ := by
    rw [← e1]
    exact OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)
  have hg : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))
  have m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hone (H₁.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁ := lift f (f * g⁻¹)
    have b1 : b ≫ a = g := by
      rw [MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have b2 : b ≫ f = f := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  rintro _ ⟨z, rfl⟩
  have hi : IsIrreducible (f.left ⁻¹' {z}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn
  obtain ⟨w, hw, e⟩ := m1 z
  obtain ⟨w', hw', e'⟩ := m2 z
  obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
  have := inW ⟨y, k₁, k₂⟩
  convert this using 2
  exact hy.symm

end GlobalTheory.OpenSubgrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem unitAt_fnMap_of {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩

end GlobalTheory.CoverNorm
end
end

