module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partLe (U : ((κ → A) → ℂ) ≃ₗ[ℂ] ((κ₁ → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁ ⊕ κ' → A) → ℂ) :=
  { partLₗ U.toLinearMap with
    invFun := partL U.symm
    left_inv := fun Φ => by
      show partL U.symm (partL U Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.symm_apply_apply]
      exact partL_id Φ
    right_inv := fun Φ => by
      show partL U (partL U.symm Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.apply_symm_apply]
      exact partL_id Φ }

def partRe (U : ((κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁' → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ₁' → A) → ℂ) :=
  { partRₗ U.toLinearMap with
    invFun := partR U.symm
    left_inv := fun Φ => by
      show partR U.symm (partR U Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.symm_apply_apply]
      exact partR_id Φ
    right_inv := fun Φ => by
      show partR U (partR U.symm Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.apply_symm_apply]
      exact partR_id Φ }

end Blocks

def conjE {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) :=
  { conjLin U.toLinearMap with
    invFun := conjLin U.symm.toLinearMap
    left_inv := fun φ => by
      funext x
      simp [conjLin_apply]
    right_inv := fun φ => by
      funext x
      simp [conjLin_apply] }

theorem conjE_apply {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) : conjE U φ = conjLin U.toLinearMap φ := rfl

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem partL_eq_of_eqOn {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ → AF F) → ℂ) → (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partL T Φ = partL e Φ :=
  partL_congr fun b => h _ (sliceL_mem hΦ b)

theorem partR_eq_of_eqOn {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ' → AF F) → ℂ) → (κ₁' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ', T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partR T Φ = partR e Φ :=
  partR_congr fun a => h _ (sliceR_mem hΦ a)

theorem conjLin_eq_of_eqOn {κ κ₁ : Type} [Fintype κ] {T e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) : ∀ Φ ∈ schA F κ, conjLin T Φ = conjLin e Φ := fun Φ hΦ => by
  funext y
  rw [conjLin_apply, conjLin_apply, h _ (GlobalTheory.ConjSch.conj_mem_schA Φ hΦ)]

theorem adm_congr {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ)
    (hl : l' ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => by rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT]⟩

theorem dbl_eq {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partR (conjLin U.toLinearMap) (partL U Φ) = partR (conjLin u) (partL u Φ) ∧
      partR (conjLin u) (partL u Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partL U Φ = partL u Φ := partL_eq_of_eqOn hUu hΦ
  have h2 : partL u Φ ∈ schA F (κ ⊕ κ) := partL_mem u hu Φ hΦ
  refine ⟨?_, partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) _ h2⟩
  rw [h1]
  exact partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) h2

theorem dbl_eq' {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partL U (partR (conjLin U.toLinearMap) Φ) = partL u (partR (conjLin u) Φ) ∧
      partL u (partR (conjLin u) Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partR (conjLin U.toLinearMap) Φ = partR (conjLin u) Φ :=
    partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) hΦ
  have h2 : partR (conjLin u) Φ ∈ schA F (κ ⊕ κ) :=
    partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) Φ hΦ
  refine ⟨?_, partL_mem u hu _ h2⟩
  rw [h1]
  exact partL_eq_of_eqOn hUu h2

end Gen

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Main

variable {F : Type} [Field F] [NumberField F]

theorem hasDbl_of_loc {E' : Type} [CommRing E'] [Algebra (AF F) E'] (c : E' →ₐ[AF F] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E') (JA : Matrix α α E') (JB : Matrix β β E') {κ : Type}
    [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (hL : IsLocOp e) (hL' : IsLocOp e') (hTe : ∀ Φ ∈ schA F κ, T Φ = e Φ)
    (hTe' : ∀ Φ ∈ schA F κ, T.symm Φ = e' Φ) (hmem : ∀ Φ, Φ ∈ schA F κ ↔ T Φ ∈ schA F κ)
    (Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d₁.rho ψ w (T Φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hconj : ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := fun Φ hΦ =>
    GlobalTheory.ConjSch.conj_mem_schA Φ hΦ

  have hSmem : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    constructor
    · intro hφ
      have := hconj _ ((hmem _).1 (hconj φ hφ))
      exact this
    · intro hφ
      have h1 : (fun x => starRingEnd ℂ (conjE T φ x)) = T (fun x => starRingEnd ℂ (φ x)) := by
        funext x; simp [conjE_apply, conjLin_apply]
      have h2 := hconj _ hφ
      rw [h1, ← hmem] at h2
      have h3 := hconj _ h2
      simpa using h3

  have hLmem : ∀ Φ ∈ schA F (κ ⊕ κ), partL T Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    rw [partL_eq_of_eqOn hTe hΦ]; exact partL_mem e hL Φ hΦ
  have hRmem : ∀ Φ ∈ schA F (κ ⊕ κ), partR (conjE T) Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    have h := partR_eq_of_eqOn (κ := κ) (conjLin_eq_of_eqOn (T := T.toLinearMap) hTe) hΦ
    rw [show partR (conjE T) Φ = partR (conjLin T.toLinearMap) Φ from rfl, h]
    exact partR_mem (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) Φ hΦ

  have heis₂ : ∀ w, ∀ φ ∈ schA F κ, conjE T (d.rho ψ⁻¹ w φ) = d₁.rho ψ⁻¹ w (conjE T φ) := fun w φ hφ => by
    funext y
    rw [conjE_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d.rho ψ⁻¹ w φ x)) = d.rho ψ w (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv ψ hψ _ _ _
    rw [LinearEquiv.coe_coe, h1, Heisenberg₂ w _ (hconj φ hφ)]
    exact conj_schr ψ hψ _ _ _

  have hunitS : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖conjE T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := fun μ hμ => by
    obtain ⟨C, hC⟩ := hunit μ hμ
    refine ⟨C, fun Φ hΦ => ?_⟩
    have h1 := hC _ (hconj Φ hΦ)
    have hce : ∀ z : ℂ, ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := fun z => by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      ext
      simp
    simp only [conjE_apply, conjLin_apply, LinearEquiv.coe_coe, hce] at h1 ⊢
    exact h1
  set Td : ((κ ⊕ κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → AF F) → ℂ) := (partLe (κ' := κ) T).trans (partRe (κ := κ) (conjE T))
    with hTd
  have hTd_apply : ∀ Φ, Td Φ = partR (conjE T) (partL T Φ) := fun Φ => rfl
  have hTd_symm : ∀ Φ, Td.symm Φ = partL T.symm (partR (conjE T).symm Φ) := fun Φ => rfl
  have hTeq : ∀ Φ ∈ schA F (κ ⊕ κ), Td Φ = partR (conjLin e) (partL e Φ) ∧ partR (conjLin e) (partL e Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq T e hL hTe hΦ
  have hTeq' : ∀ Φ ∈ schA F (κ ⊕ κ), Td.symm Φ = partL e' (partR (conjLin e') Φ) ∧
      partL e' (partR (conjLin e') Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq' T.symm e' hL' hTe' hΦ
  refine ⟨GlobalTheory.DblSchr.dblD c d₁, Td, conjE T, GlobalTheory.DblSchr.isDblCoord_dblD c d₁, ⟨fun Φ => ?_, fun w Φ hΦ => ?_,
    fun l => ?_, fun μ hμ => ?_⟩, hSmem, fun φ₁ _ φ₂ _ => ?_⟩
  · constructor
    · intro hΦ
      rw [(hTeq Φ hΦ).1]; exact (hTeq Φ hΦ).2
    · intro hΦ
      have := (hTeq' _ hΦ)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this.1]; exact this.2
  · rw [← Matrix.fromCols_toCols w, rho_dbl c ξ JA JB d dd hdd, rho_dbl c ξ JA JB d₁ _ (GlobalTheory.DblSchr.isDblCoord_dblD c d₁),
      hTd_apply, hTd_apply]
    have hc1 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partL T (partR (d.rho ψ⁻¹ w.toCols₂) Ψ) =
        partR (d.rho ψ⁻¹ w.toCols₂) (partL T Ψ) := fun Ψ => partL_partR_rho T.toLinearMap d ψ⁻¹ _ Ψ
    have hc2 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partR (conjE T) (partL (d₁.rho ψ w.toCols₁) Ψ) =
        partL (d₁.rho ψ w.toCols₁) (partR (conjE T) Ψ) := fun Ψ => partR_partL_rho (conjE T).toLinearMap d₁ ψ _ Ψ
    rw [partL_intertwine T (d.rho ψ w.toCols₁) (d₁.rho ψ w.toCols₁) T _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      hc1, hc2,
      partR_intertwine (conjE T) (d.rho ψ⁻¹ w.toCols₂) (d₁.rho ψ⁻¹ w.toCols₂) (conjE T) _ (fun φ hφ => heis₂ _ φ hφ)
        (fun a => sliceR_mem (hLmem Φ hΦ) a)]
  · constructor
    · intro hl
      refine adm_congr (l' := (l ∘ₗ partRₗ (conjLin e)) ∘ₗ partLₗ e) (fun Φ hΦ => ?_)
        (partL_adm e hL _ (partR_adm (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) l hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [(hTeq Φ hΦ).1]
    · intro hl
      refine adm_congr (l' := ((l ∘ₗ Td.toLinearMap) ∘ₗ partLₗ e') ∘ₗ partRₗ (conjLin e')) (fun Φ hΦ => ?_)
        (partR_adm (conjLin e') (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e' hL') _ (partL_adm e' hL' _ hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [← (hTeq' Φ hΦ).1, LinearEquiv.apply_symm_apply]
  · obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.DblEval.lintegral_partL_eq T.toLinearMap hunit hLmem μ hμ
    obtain ⟨C₂, hC₂⟩ := _root_.GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA (κ := κ) (conjE T).toLinearMap hunitS hRmem μ hμ
    refine ⟨C₂ * C₁, fun φ hφ => ?_⟩
    rw [hTd_apply]
    have h2 := hC₂ _ (hLmem φ hφ)
    have h1 := hC₁ φ hφ
    simp only [LinearEquiv.coe_coe] at h1 h2
    rw [h2, h1, mul_assoc]
  · funext y
    rw [hTd_apply]
    simp only [partR, partL, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : (fun x => T (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = T φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl

end Main

end GlobalTheory.DblTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OneMapAll


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.OnCmp.const_upTo_center : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, GlobalTheory.AdTh.SerOf (O i) (κ i) (v₀ i (sg0 D A)) (u • cc) 1 → ∃ z ∈ Subgroup.center G, ∃ (ζ : D.what₂.LL) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g, (O i).phi (u • cc) f g = D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins hU hIo h0 hPh hSpan cc hcc u hser
  have hP := hpins.2
  obtain ⟨hE, ⟨hLL, -, -, hcU, -, z, hz, hrowT⟩, -⟩ := hPh h0
  obtain ⟨ζ, hζL, ⟨m, hm, hζm⟩, hT1⟩ := hrowT ()
  obtain ⟨ζ', rfl⟩ := (AlgHom.mem_fieldRange).1 hζL
  have hζ : D.what₂.embLL.toRatAlgHom ζ' = D.what₂.embLL ζ' := rfl
  rw [hζ] at hζm hT1
  clear hζL
  have hs0 : ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (lieFac_pos _ _ _).ne'
  have gen : ∀ x, (O i).Plc () x → ∀ Fr ∈ sec (T.J.Q.Xo ((i : ℕ) + 1)) (O i).c' (wtA (κ i)) (Vc D i).rank,
      IsSum (O i) () x Fr → ∀ q,
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro x hx Fr hF hsum q
    have h1 := (hT1 x hx).2 Fr hF hsum q
    obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple ()).reps
    obtain ⟨y, hy⟩ := (hPl x).1 hx
    have h2 := hser.2.2 () h J' hR _ x hy Fr hF hsum q.out
    have h3 : actLev (O i).c' (O i).lev2 1 Fr = Fr := actL_one _ _ _ hP.act.2.total hP.act.2.func hP.act.2.one hF.1
    rw [hA _ x hy] at h1
    unfold geo
    rw [h3]
    simp only [jFn, onQ, adel, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul, one_mul] at h1 h2 ⊢
    linear_combination h1 - h2
  have span : ∀ q, ∀ Fr ∈ cuspOver (O i) (κ i),
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro q Fr hF
    have hF' := hSpan hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨hgc, x, hx, hgx⟩ := hg
      exact gen x hx g ((mem_cusp _ _ _ _ _ _).1 hgc).1 hgx q
    | zero =>
      set_option synthInstance.maxHeartbeats 200000 in
      have e := geo_smul (O i) (u • cc) 1 0 0 q
      set_option synthInstance.maxHeartbeats 200000 in
      have e' := geo_smul (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z 0 0 q
      rw [zero_smul] at e e'
      rw [e, e']
      simp
    | add f g _ _ hf hg => rw [geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf => rw [geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have rep : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ q : AutQ (Wc D i),
      (O i).phi (u • cc) f q.out =
        D.what₂.embLL ζ' * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) q.out := by
    intro f hf q
    rw [hn] at hf
    have hfs : f ∈ sec _ _ (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hf).1
    have hF := ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O i).hle _ (T.J.U ((i : ℕ) + 1)) _ _ _ hfs).2).2 hf
    have hBC := GlobalTheory.FieldBCModel.isBC_rulBC (O i).hle hfs.1
    have hs1 : ∀ k, ![f] k ∈ sec _ T.J.Q.c (wtA (κ i)) (Vc D i).rank := fun k => by
      rw [Subsingleton.elim k 0]; exact hfs
    have e := span q _ hF
    rw [geo_of_isBC (O i) hP.act.1 _ 1 (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q,
      geo_of_isBC (O i) hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q] at e
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
    have h1 : actLev T.J.toCore.Q.c (O i).lev2 1 f = f :=
      actL_one _ _ _ hP.act.1.total hP.act.1.func hP.act.1.one hfs.1
    rw [h1] at e
    exact mul_left_cancel₀ hs0 (e.trans (by ring))
  have hcomp : ∀ γ ∈ GQ (Wc D i), ∀ g, ((O i).dict (γ * g)).1 = ((O i).dict g).1 := by
    obtain ⟨th, hr, -, hd⟩ := hT.j.dictU ((i : ℕ) + 1) (inR i) _ T.J.good_σ₀
    have key : ∀ (W : HSp D) (hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = W), ∀ γ ∈ GQ W, ∀ g,
        (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) (γ * g)).1 = (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) g).1 := by
      rintro W rfl γ hγ g
      obtain ⟨γ', -, he⟩ := hd.1 γ hγ g
      have e := congrArg Sigma.fst he
      exact e
    exact key _ (O i).hV
  have hsplit : ∀ (c' : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (f : T.J.R ((i : ℕ) + 1)) g,
      (O i).phi c' f g = c' ((O i).dict g).1 * (O i).phi (fun _ => 1) f g := by
    intro c' f g
    show c' _ * _ * _ = c' _ * (1 * _ * _)
    ring
  have hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = Wc D i := (O i).hV
  have hinv : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f (γ * g) = (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f g :=
    fun f hf => GlobalTheory.OneMapTuples.psi_inv T.J _ hV hT.j (inR i) (dom_wtA (κ i)) hf
  refine ⟨z, hz, ζ', m, hm, ?_, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, map_one]
    exact hζm
  intro f hf g
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hzf := (hE z k hk f hf).1
  have hq : g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ ∈ GQ (Wc D i) :=
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (GQ (Wc D i))) g)
  set γ := g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ with hγ
  have hg : g = γ * (⟦g⟧ : AutQ (Wc D i)).out := by rw [hγ, inv_mul_cancel_right]
  have hL : (O i).phi (u • cc) f g = (O i).phi (u • cc) f (⟦g⟧ : AutQ (Wc D i)).out := by
    have e := hinv f hf γ hq (⟦g⟧ : AutQ (Wc D i)).out
    rw [← hg] at e
    rw [hsplit (T.J.cE _ _) f g, hsplit (T.J.cE _ _) f, hg, hcomp γ hq] at e
    rw [← hg] at e
    have hne : T.J.cE ((i : ℕ) + 1) (O i).s0 ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 ≠ 0 :=
      norm_ne_zero_iff.1 ((hcU _).trans_ne one_ne_zero)
    have hc : ((O i).dict g).1 = ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 := by
      have := hcomp γ hq (⟦g⟧ : AutQ (Wc D i)).out
      rwa [← hg] at this
    rw [hsplit (u • cc) f g, hsplit (u • cc) f, hc, mul_left_cancel₀ hne e]
  rw [hL, rep f hf, ← hinv _ hzf γ hq, ← hg]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.CexLetter

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem zc_eq_act (a : ℕ) : zc E a = act (Op.lie (fun i j => if i = j then 1 else 0) : Op E a) := rfl

theorem zc_mapsTo {a : ℕ} (π : CuspSub E a) : ∀ φ ∈ π.V, zc E a φ ∈ π.V := fun φ hφ => by
  rw [zc_eq_act]; exact π.stable _ φ hφ

theorem exists_scalar (x : Letter E) : ∃ c : ℂ, ∀ φ ∈ x.2.V, zc E x.1 φ = c • φ := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CuspSchur.schur E x.1 x.2 ((zc E x.1).restrict (zc_mapsTo x.2)) (by
    intro o φ
    apply Subtype.ext
    have := congrArg (fun f : Module.End ℂ (Sm E x.1) => f φ.1) ((_root_.GlobalTheory.ResW.zc_comm_mem_eigen E x.1).1 o)
    simpa [LinearMap.restrict_apply, CuspSub.op] using this)
  exact ⟨c, fun φ hφ => by simpa using congrArg Subtype.val (hc ⟨φ, hφ⟩)⟩

theorem cex_spec (x : Letter E) : ∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ := by
  unfold cex; exact Classical.epsilon_spec (exists_scalar x)

theorem cex_unique (x : Letter E) (c : ℂ) (h : ∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) : cex x = c := by
  obtain ⟨φ, hφ, hne, hc⟩ := h
  have h1 := cex_spec x φ hφ
  rw [hc] at h1
  exact (smul_left_injective ℂ hne h1).symm

theorem cex_tw (x : Letter E) (t : ℝ) : cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t := by
  obtain ⟨χ, h1, -, -, h4⟩ := _root_.GlobalTheory.ResW.exists_abs_cpow E (t : ℂ)
  have hχ : χ = nu E t := by have := h4 (Complex.ofReal_im t); rwa [Complex.ofReal_re] at this
  subst hχ
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
  apply cex_unique
  refine ⟨mulChi x.1 (nu E t) φ, ?_, ?_, ?_⟩
  · exact ⟨φ, hφ, rfl⟩
  · exact fun h0 => hne ((mulChi x.1 (nu E t)).injective (h0.trans (map_zero _).symm))
  · show zc E x.1 (mulChi x.1 (nu E t) φ) = _
    rw [h1, cex_spec x φ hφ, ← add_smul, map_smul]
    rfl

theorem rexp_tw (x : Letter E) (hx : 1 ≤ x.1) (t : ℝ) : rexp (tw x t) = rexp x + t := by
  have hd : (0:ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha : (0:ℝ) < x.1 := by exact_mod_cast hx
  have hne : (x.1 : ℝ) * Module.finrank ℚ E ≠ 0 := (mul_pos ha hd).ne'
  unfold rexp
  rw [cex_tw]
  show (cex x + (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ)).re / ((x.1:ℝ) * Module.finrank ℚ E) = _
  rw [show (x.1 : ℂ) * (Module.finrank ℚ E : ℂ) * (t : ℂ) = (((x.1:ℝ) * Module.finrank ℚ E * t : ℝ) : ℂ) by
    push_cast; ring, Complex.add_re, Complex.ofReal_re]
  field_simp

theorem cex_eq_zero_iff (x : Letter E) : cex x = 0 ↔ IsNormalised x.2 := by
  constructor
  · intro h φ hφ t g
    have := ((_root_.GlobalTheory.ResW.zc_comm_mem_eigen E x.1).2.2 φ 0).1 (by rw [← h]; exact cex_spec x φ hφ) t g
    simpa using this
  · intro hN
    obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x.2.ne_bot
    exact cex_unique x 0 ⟨φ, hφ, hne, ((_root_.GlobalTheory.ResW.zc_comm_mem_eigen E x.1).2.2 φ 0).2 (fun t g => by simpa using hN φ hφ t g)⟩

end GlobalTheory.ResW.CexLetter


open GlobalTheory.ResW.CexLetter in
theorem GlobalTheory.ResW.letter_centralExponent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Letter E), (∀ φ ∈ x.2.V, zc E x.1 φ = cex x • φ) ∧ (∀ t : ℝ, cex (tw x t) = cex x + x.1 * (Module.finrank ℚ E : ℂ) * t) ∧ (1 ≤ x.1 → ∀ t : ℝ, rexp (tw x t) = rexp x + t) ∧ (cex x = 0 ↔ IsNormalised x.2) ∧ ∀ c : ℂ, (∃ φ ∈ x.2.V, φ ≠ 0 ∧ zc E x.1 φ = c • φ) → cex x = c := by
  intro E _ _ _ x
  exact ⟨cex_spec x, cex_tw x, rexp_tw x, cex_eq_zero_iff x, fun c h => cex_unique x c h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  first | exact @GlobalTheory.InertVacLagP.exists_lagr_inv_vac | exact GlobalTheory.InertVacLagP.exists_lagr_inv_vac | (intros; apply GlobalTheory.InertVacLagP.exists_lagr_inv_vac <;> assumption)
end

