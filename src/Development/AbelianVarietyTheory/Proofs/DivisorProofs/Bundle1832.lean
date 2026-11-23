module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalLagrangianInvariantFormUnique
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.LagrUniq

theorem exists_lagrInt_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd : IsStd B.ψ := hB.std
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ : Matrix (Fin (nT + nT)) (Fin nT) E :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, if_true, if_false, map_one, map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm : WOF F E nS nT →ₗ[AF F] (κ → AF F) × (κ → AF F) := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u) Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u => thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u := by
      rw [map_add (f := _)]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0

theorem lagr_invariant_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd : IsStd B.ψ := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co hco
  obtain ⟨l₂, hl₂, he⟩ := GlobalTheory.LagrThetaAdm.exists_admitted_eq_diagonalLagrangian_thetaIntegral_alt F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_lagrInt_ne_zero F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact GlobalTheory.LagrThetaInv.lagrInt_rho_inv F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]; rfl⟩

end GlobalTheory.LagrUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cols_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F))
    (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD X v, h *ᵥ z ∈ GlobalTheory.DblVac.latD X v)
    {w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E)} (hw₁ : w₁ ∈ latAtV X Y v) (hw₂ : w₂ ∈ latAtV X Y v) :
    ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v ∧
      ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v := by
  let T₁ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₁)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₁]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₁, Matrix.add_mul] }
  let T₂ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₂)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₂]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₂, Matrix.add_mul] }
  let S := (latAtV X Y v).comap T₁ ⊓ (latAtV X Y v).comap T₂
  have key : ∀ y ∈ Y.L, ∀ z ∈ GlobalTheory.DblVac.latD X v,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z ∈ S := by
    intro y hy z hz
    have hz' := hh z hz
    refine ⟨?_, ?_⟩
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inl) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₁, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.1
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inr) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₂, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.2
  let A₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols wᵀ 0
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  let A₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols 0 wᵀ
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  have hA₁ : latAtV X Y v ≤ S.comap A₁ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₁ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim (a • fun i => inclR (F := F) (AF F) (x i)) 0) := by
      ext i j
      cases j with
      | inl j =>
        simp only [A₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inl, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inl, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
      | inr j => simp [A₁, Matrix.vecMulVec_apply]
    show A₁ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    · rw [Sum.elim_comp_inr]; exact zero_mem _
  have hA₂ : latAtV X Y v ≤ S.comap A₂ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₂ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (x i))) := by
      ext i j
      cases j with
      | inl j => simp [A₂, Matrix.vecMulVec_apply]
      | inr j =>
        simp only [A₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inr, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inr, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
    show A₂ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact zero_mem _
    · rw [Sum.elim_comp_inr]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
  have hsum : Matrix.fromCols w₁ᵀ w₂ᵀ = A₁ w₁ + A₂ w₂ := by
    ext i j; cases j <;> simp [A₁, A₂]
  have hm : Matrix.fromCols w₁ᵀ w₂ᵀ ∈ S := hsum ▸ add_mem (hA₁ hw₁) (hA₂ hw₂)
  exact ⟨hm.1, hm.2⟩

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := cols_mem G.V G.W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ
        (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ := by
    change Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J)
    (dbl (incM F G.V.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

end GlobalTheory.DblVacTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactor
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblTargetRestrict

theorem restrict_boxFun : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat om hom
    ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let h : Formalism.IndefR.DatumF.GAF σ JT := ⟨g.1, GlobalTheory.TransportF.mem_HR_target hA g⟩
  let hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := ⟨gd.1, GlobalTheory.TransportF.mem_HR_target rfl gd⟩
  have hh : Formalism.IndefR.DatumF.mtF σ JT h = g.1.1 := rfl
  have hhd : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd = gd.1.1 := rfl
  have h1 : Formalism.IndefR.DatumF.mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    show (Formalism.IndefR.DatumF.matHomF σ JS 1).1 = _
    rw [map_one, inv_one]
    first | rfl | simp | exact Matrix.transpose_one.symm
  have hdm : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) := by
    rw [hhd, hgd, hh]
  have t1 := hom g 1 1 h hh h1 φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ hφ₁ φ₂ hφ₂
  have hΦ' := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ t1.1 φ₂ hφ₂
  have t2 := homp gd 1 1 hd hhd h1 _ hΦ
  have hφ₂' := _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection F κ φ₂ hφ₂
  let τ := Fintype.equivFin κ
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hA hB', co.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      GlobalTheory.TransportF.numCoordF co τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  have thf : ∀ Φ ∈ schA F κ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := fun Φ hΦ => by
    rw [GlobalTheory.TransportF.thetaTr_eqF co τ]
    exact _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (GlobalTheory.TransportF.numCoordF co τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  have key := t2.2.trans ((congrArg (ωd (1, hd)) (GlobalTheory.T.thetaTransform_doubledTarget_boxProduct F E σ B hB hω.std nS nT JT JA JB ξ hA κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((_root_.GlobalTheory.DblTargetRestrictCore.restrict_core F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT ω hω ωd hωd h hd hdm _ _ (thf φ₁ hφ₁) (thf _ hφ₂')).trans
      ((congrArg (fun f => GlobalTheory.DblTargetDelta.deltaT f
        (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.thetaTransform_doubledTarget_boxProduct F E σ B hB hω.std nS nT JT JA JB ξ hA κ co _ t1.1 φ₂ hφ₂).symm)))
  let τ' := Fintype.equivFin (κ ⊕ κ)
  have key' := (GlobalTheory.TransportF.thetaTr_eqF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' ((omp (gd, 1)) (boxFun φ₁ φ₂))).symm.trans
    (key.trans (GlobalTheory.TransportF.thetaTr_eqF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' (boxFun ((om (g, 1)) φ₁) φ₂)))
  have h2 := GlobalTheory.TransportF.thV_injOn hR hψ (GlobalTheory.TransportF.comp_mem_schA τ' t2.1) (GlobalTheory.TransportF.comp_mem_schA τ' hΦ')
    ((GlobalTheory.TransportF.numCoordF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ').surjective.injective_comp_right key')
  funext x
  have hx : (x ∘ τ'.symm) ∘ τ' = x := by
    funext i
    simp
  have hhx := congrFun h2 (x ∘ τ'.symm)
  rw [hx] at hhx
  exact hhx

end GlobalTheory.DblTargetRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSpStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  first | exact @GlobalTheory.DblVac.kD_stab_latDbl | exact GlobalTheory.DblVac.kD_stab_latDbl | (intros; apply GlobalTheory.DblVac.kD_stab_latDbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfOrthonormalConjBlockUpperTriangular
section
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin

namespace GlobalTheory.ScalarPoin.BlockFree

theorem eq_one_of_gm_toBlocks₁₂ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, (∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) → γ = 1 := by
  intro E _ _ _ r X x0 ho γ hγ h
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : r - (r - X.p0) = X.p0 := Nat.sub_sub_self X.p0_le
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - (r - X.p0) → ¬ (a : ℕ) < r - (r - X.p0) → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x0 τ)⁻¹ * mat (lact γ x0) τ * b = b * t := by
    intro τ
    refine GlobalTheory.FreeOnDomain.exists_conj_block hj _ ?_
    ext u v
    have e1 : (GlobalTheory.TrueCx.idx hj).symm (Sum.inl u) = KU.eT X (Sum.inl u) := by
      apply Fin.ext
      rw [GlobalTheory.TrueCx.idx_symm_inl, KU.eT_inl]
      simp only [ExF.qI]
      omega
    have e2 : (GlobalTheory.TrueCx.idx hj).symm (Sum.inr v) = KU.eT X (Sum.inr (Fin.cast hp v)) := by
      apply Fin.ext
      rw [GlobalTheory.TrueCx.idx_symm_inr, KU.eT_inr]
      simp
    have hz := congrFun (congrFun (h τ) u) (Fin.cast hp v)
    simp only [KU.gm, KU.tl, toBlocks₁₂, of_apply, submatrix_apply, Matrix.zero_apply] at hz
    simp only [toBlocks₁₂, reindex_apply, of_apply, submatrix_apply, Matrix.zero_apply, e1, e2]
    rw [← hz, Matrix.mul_assoc]
    rfl
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x0) τ * b τ = mat x0 τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x0 fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (fun τ a c h1 h2 => hb0 τ a c (by rw [hp]; exact h1)
      (by rw [hp]; exact h2))) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x0 _).trans (funext e')

end GlobalTheory.ScalarPoin.BlockFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bump_shintani_alt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  first
  | exact @GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | exact GlobalTheory.JSW.BumpShintani.exists_bump_shintani
  | (intros; apply GlobalTheory.JSW.BumpShintani.exists_bump_shintani <;> assumption)
end

