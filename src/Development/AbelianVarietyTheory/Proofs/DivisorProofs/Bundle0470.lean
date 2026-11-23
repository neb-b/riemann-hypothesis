module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainValueOnThickeningHomEqSubOfGlued

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem cm_type_normSq_prod_eq_abs_norm (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (d : E) :
    ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ d
    rw [eq_ratCast] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ τ ∈ Ψ, (starRingEnd ℂ) (τ d) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      rw [hΨ, hcc]; exact hτ
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      exact (hΨ τ).mp hτ
    · intro τ _; exact hcc τ
    · intro τ _; exact hcc τ
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have hsub : ∏ τ : Ψ, τ.1 d = ∏ τ ∈ Ψ, τ d := Finset.prod_coe_sort Ψ (fun τ => τ d)
  set P := ∏ τ ∈ Ψ, τ d with hP
  have h2 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ((Complex.normSq P : ℝ) : ℂ) := by
    rw [h1, ← Finset.prod_mul_prod_compl Ψ, hcompl, ← map_prod, Complex.mul_conj]
  have h3 : ((Algebra.norm ℚ d : ℚ) : ℝ) = Complex.normSq P := by
    have := h2
    rw [show ((Algebra.norm ℚ d : ℚ) : ℂ) = (((Algebra.norm ℚ d : ℚ) : ℝ) : ℂ) by push_cast; rfl] at this
    exact_mod_cast this
  rw [hsub, h3, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGramDetEqIndex
section
open NumberField

namespace GlobalTheory.DualIndex

theorem relIndex_dvd_of_le_right {G : Type*} [AddCommGroup G] (H K K' : AddSubgroup G)
    (h1 : H ≤ K') (h2 : K ≤ K') : H.relIndex K ∣ H.relIndex K' := by
  rw [← AddSubgroup.relIndex_sup_left K H,
    ← AddSubgroup.relIndex_mul_relIndex H (H ⊔ K) K' le_sup_left (sup_le h1 h2)]
  exact dvd_mul_right _ _

theorem absNorm_eq_index' {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem inv_relIndex_dvd {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (K : AddSubgroup F) (hK : ∀ f ∈ K, ∀ i ∈ I, i • f ∈ (1 : Submodule (𝓞 F) F)) :
    (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex K ∣ I.toAddSubgroup.index := by
  by_cases hI : I = ⊥
  · rw [← absNorm_eq_index', hI]; simp
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haI)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := FaithfulSMul.algebraMap_injective _ _
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha
  have hmul : Function.Injective (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a)) :=
    mul_right_injective₀ haF
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha hJ
  have hle : (Ideal.span {a}).toAddSubgroup ≤ J.toAddSubgroup := by
    have : Ideal.span {a} ≤ J := Ideal.dvd_iff_le.1 ⟨I, by rw [hJ, mul_comm]⟩
    exact this
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex J.toAddSubgroup = I.toAddSubgroup.index := by
    have := AddSubgroup.relIndex_mul_index hle
    rw [← absNorm_eq_index', ← absNorm_eq_index', hJ, map_mul] at this
    rw [← absNorm_eq_index', hJ]
    exact mul_right_cancel₀ hJ0 this
  rw [← h1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hmul,
    ← AddSubgroup.relIndex_map_map_of_injective (f := (algebraMap (𝓞 F) F).toAddMonoidHom)
      (Ideal.span {a}).toAddSubgroup _ hinj]
  have e : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a))
      (1 : Submodule (𝓞 F) F).toAddSubgroup =
      AddSubgroup.map (algebraMap (𝓞 F) F).toAddMonoidHom (Ideal.span {a}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c * a, ⟨c, rfl⟩, by simp [mul_comm]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, by simp [mul_comm]⟩
  rw [e]
  refine relIndex_dvd_of_le_right _ _ _ (AddSubgroup.map_mono hle) ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hK f hf a haI)
  refine ⟨c, ?_, by simpa [Algebra.smul_def] using hc⟩
  have : I * Ideal.span {c} ≤ I * J := by
    rw [← hJ, Ideal.mul_le]
    intro i hi s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (hK f hf i hi)
    refine Ideal.mem_span_singleton'.2 ⟨t * d, hinj ?_⟩
    simp only [map_mul, hc, hd, Algebra.smul_def]
    ring
  have h2 : J ∣ Ideal.span {c} := by
    rw [← Ideal.dvd_iff_le] at this
    exact (mul_dvd_mul_iff_left hI).1 this
  exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 h2)

variable {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (B : LinearMap.BilinForm F V)

theorem dual_anti {M L : Submodule (𝓞 F) V} (h : M ≤ L) :
    B.dualSubmodule L ≤ B.dualSubmodule M := fun _ hy x hx => hy x (h hx)

theorem dual_step (M : Submodule (𝓞 F) V) (x : V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup := by
  have e1 : M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup =
      (M.comap (LinearMap.toSpanSingleton (𝓞 F) V x)).toAddSubgroup.index := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left]
    have := AddSubgroup.index_comap M.toAddSubgroup
      (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom
    rw [show (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom.range =
      (Submodule.span (𝓞 F) {x}).toAddSubgroup from by
        ext z; simp [Submodule.mem_span_singleton]] at this
    exact this.symm
  have e2 : (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup =
      ((1 : Submodule (𝓞 F) F).toAddSubgroup.comap (B.flip x).toAddMonoidHom) ⊓
        (B.dualSubmodule M).toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, LinearMap.BilinForm.mem_dualSubmodule,
      AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    constructor
    · intro h
      exact ⟨h x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)),
        fun z hz => h z (Submodule.mem_sup_left hz)⟩
    · rintro ⟨h1, h2⟩ z hz
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_add (f := _), LinearMap.map_smul_of_tower]
      exact add_mem (h2 m hm) (Submodule.smul_mem _ c h1)
  rw [e1, e2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  refine inv_relIndex_dvd _ _ ?_
  rintro _ ⟨y, hy, rfl⟩ i hi
  have := hy (i • x) hi
  rwa [LinearMap.map_smul_of_tower] at this

theorem dual_relIndex_dvd (M : Submodule (𝓞 F) V) (s : Finset V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) (s : Set V))).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) (s : Set V)).toAddSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s _ ih =>
    have e : M ⊔ Submodule.span (𝓞 F) ((insert x s : Finset V) : Set V) =
        (M ⊔ Submodule.span (𝓞 F) (s : Set V)) ⊔ Submodule.span (𝓞 F) {x} := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_assoc, sup_comm (Submodule.span _ {x})]
    rw [e]
    set N := M ⊔ Submodule.span (𝓞 F) (s : Set V) with hN
    have hMN : M ≤ N := le_sup_left
    rw [← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup N.toAddSubgroup
      (N ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup hMN (le_sup_left (a := N)),
      ← AddSubgroup.relIndex_mul_relIndex _ (B.dualSubmodule N).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup (dual_anti B (le_sup_left (a := N))) (dual_anti B hMN),
      mul_comm]
    exact mul_dvd_mul ih (dual_step B N x)

theorem dual_relIndex_dvd' {M L : Submodule (𝓞 F) V} (h : M ≤ L) (hL : L.FG) :
    (B.dualSubmodule L).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨s, hs⟩ := hL
  have := dual_relIndex_dvd B M s
  rwa [hs, sup_eq_right.2 h] at this

theorem span_eq_closure [Module ℚ V] [IsScalarTower ℚ F V] {n : ℕ} (b : Module.Basis (Fin n) F V) :
    (Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup =
      AddSubgroup.closure (Set.range ((integralBasis F).smulTower b)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine sum_mem fun j _ => ?_
    rw [← (RingOfIntegers.basis F).sum_repr (f j), Finset.sum_smul]
    refine sum_mem fun i _ => ?_
    rw [smul_assoc]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
      (Set.mem_range.2 ⟨(i, j), ?_⟩)) _
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem relIndex_span_eq_norm {n : ℕ} (b c : Module.Basis (Fin n) F V)
    (h : Submodule.span (𝓞 F) (Set.range b) ≤ Submodule.span (𝓞 F) (Set.range c)) :
    (((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 F) (Set.range c)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ (c.det b)| := by
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
  haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Free F V := Module.Free.of_basis b
  rw [AddSubgroup.relIndex_eq_abs_det _ _ h _ _ (span_eq_closure b) (span_eq_closure c)]
  set f : V →ₗ[F] V := (c.equiv b (Equiv.refl _)).toLinearMap with hf
  have h1 : (b : Fin n → V) = f ∘ c := by ext i; simp [hf]
  have h2 : (((integralBasis F).smulTower b : Module.Basis _ ℚ V) : _ → V) =
      (f.restrictScalars ℚ) ∘ ((integralBasis F).smulTower c) := by
    ext ⟨i, j⟩
    simp only [Function.comp_apply, Module.Basis.smulTower_apply, LinearMap.restrictScalars_apply,
      map_smul]
    rw [h1]; rfl
  rw [h2, Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_restrictScalars]
  conv_rhs => rw [h1, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem mem_one_iff (z : F) : z ∈ (1 : Submodule (𝓞 F) F) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨c, rfl⟩; exact c.isIntegral_coe
  · intro h; exact ⟨⟨z, h⟩, rfl⟩

end GlobalTheory.DualIndex


open GlobalTheory.DualIndex in
theorem GlobalTheory.abs_norm_det_gram_eq_relIndex : ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (n : ℕ) (b : Module.Basis (Fin n) F V) (B : LinearMap.BilinForm F V) (L : AddSubgroup V), B.IsSymm → B.Nondegenerate → (∀ i, b i ∈ L) → (∀ (a : 𝓞 F) x, x ∈ L → a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (B x y)) → |((Algebra.norm ℚ (Matrix.of fun i j => B (b i) (b j)).det : ℚ) : ℝ)| = (L.relIndex (AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)}) : ℝ) * ((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex L : ℝ) ^ 2 := by
  intro F _ _ V _ _ _ _ n b B L hs hB hb hL hint
  classical
  let Λ : Submodule (𝓞 F) V :=
    { L.toAddSubmonoid with smul_mem' := fun a x hx => hL a x hx }
  have hΛ : Λ.toAddSubgroup = L := rfl
  set M := Submodule.span (𝓞 F) (Set.range b) with hM
  have hcl : AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)} =
      (B.dualSubmodule Λ).toAddSubgroup := by
    rw [← AddSubgroup.closure_eq (B.dualSubmodule Λ).toAddSubgroup]
    congr 1
    ext y
    change (∀ x ∈ L, IsIntegral ℤ (B x y)) ↔ ∀ x ∈ L, B y x ∈ (1 : Submodule (𝓞 F) F)
    refine forall₂_congr fun x _ => ?_
    rw [mem_one_iff, hs.eq x y]
  have hML : M ≤ Λ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hLL : Λ ≤ B.dualSubmodule Λ := fun x hx y hy => (mem_one_iff _).2 (hint x hx y hy)
  have hLM : B.dualSubmodule Λ ≤ B.dualSubmodule M := dual_anti B hML
  have hdual := B.dualSubmodule_span_of_basis (R := 𝓞 F) hB b
  have hdd := B.dualSubmodule_dualSubmodule_of_basis (R := 𝓞 F) hB hs b
  rw [← hM] at hdual hdd
  have hfg : (B.dualSubmodule M).FG := by
    rw [hdual]; exact Submodule.fg_span (Set.finite_range _)
  have hfgΛ : Λ.FG := Submodule.FG.of_le hfg (hLL.trans hLM)
  have d1 := dual_relIndex_dvd' B hML hfgΛ
  have d2 := dual_relIndex_dvd' B hLM hfg
  rw [hdd] at d2
  have hΛdd : Λ ≤ B.dualSubmodule (B.dualSubmodule Λ) := fun x hx y hy => by
    rw [hs.eq x y]; exact hy x hx
  have d3 := relIndex_dvd_of_le_right M.toAddSubgroup Λ.toAddSubgroup
    (B.dualSubmodule (B.dualSubmodule Λ)).toAddSubgroup (hML.trans hΛdd) hΛdd
  have hb' := Nat.dvd_antisymm d1 (d3.trans d2)
  have hle : M ≤ Submodule.span (𝓞 F) (Set.range (B.dualBasis hB b)) := by
    rw [← hdual]; exact hML.trans (hLL.trans hLM)
  have ha := relIndex_span_eq_norm b (B.dualBasis hB b) hle
  rw [← hM, ← hdual, ← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup Λ.toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hML (hLL.trans hLM),
    ← AddSubgroup.relIndex_mul_relIndex Λ.toAddSubgroup (B.dualSubmodule Λ).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hLL hLM, hb'] at ha
  have hdet : (B.dualBasis hB b).det b = (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.BilinForm.dualBasis_repr_apply]
  rw [hdet, hΛ] at ha
  rw [hcl, ← Rat.cast_abs, ← ha]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem omegaFactor_pow_two_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 : Frac F) (s : ℕ), (omegaFactor 𝔞 : ℂ) ^ (2 * s) = ((|(discr F : ℚ)| ^ s * FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ^ (2 * s) : ℚ) : ℂ) := by
  intro F _ _ _ 𝔞 s
  have hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2) := by
    simp only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ) := by
    push_cast; rw [pow_mul]
  rw [h2, hsq]
  push_cast
  rw [mul_pow, ← pow_mul]
  congr 2
  rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem constTerm_eq_zetaVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  intro F _ _ _ k z C Z hk hz hZ
  obtain ⟨Z', hZ', e⟩ := hz C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have h : Z (1 - (k : ℂ)) = Z' (1 - (k : ℂ)) :=
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (C := C) (Z := Z) (Z' := Z') hZ hZ' hne
  rw [h, e]
  push_cast
  rw [div_eq_mul_inv, mul_comm, inv_pow]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
section
noncomputable section

namespace GlobalTheory.RiemConst

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def angles (θ : Fin (r - 1) → ℝ) (a : Fin r) : ℝ :=
  if h : (a : ℕ) < r - 1 then θ ⟨a, h⟩ else -∑ k, θ k

def phaseFrame {Ψ : Finset (E →+* ℂ)} (θ : Ψ → Fin (r - 1) → ℝ) : Frame Ψ r :=
  fun τ => Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))

def inFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (Y : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  (mat x τ)⁻¹ * Matrix.of (Y τ) * mat x τ

abbrev ChartSp (X : Data E r) : Type := ReciprocityTheory.L2DbarEstimates.V (nd X) × (X.Ψ → Fin (r - 1) → ℝ)

end GlobalTheory.RiemConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackFormsIntersectionEqChartLocalization
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_comap_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi
  have hloc := GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p
  ext w
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  constructor
  · intro hw
    obtain ⟨N, hN⟩ := (hloc _).1 hw
    have hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I :=
      Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj =>
        Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N
    have hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1 := by
      rw [← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]
      intro j _
      have h1 := hx.pd.ne i
      have h2 := hx.pd.ne j
      field_simp
    have hm : (∏ j ∈ I, x j / x i) ^ N • w ∈
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) := by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        ← algebraMap_smul K, map_smul, map_pow]
      exact hN
    have := (Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)
    rwa [Subalgebra.smul_def, smul_smul, hfg, one_smul] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      refine (hloc _).2 ⟨0, ?_⟩
      rw [pow_zero, one_smul]
      exact hz
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subalgebra.smul_def, ← algebraMap_smul K, map_smul]
      refine ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_
      exact (integralClosure (rA k x I) K).algebraMap_mem r

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolutionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBoundedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (exact GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (intros; apply GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR

theorem cmpO_injective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    Function.Injective (cmpO s) := by
  intro R _ X s
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
  have hg' : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V),
      g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a) :=
    fun U V a ↦ congrFun (congrFun (congrFun hg U) V) a
  have ex : ∀ T : TT s, ∃ G : T.obj.B, ∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p :=
    fun T ↦ GlobalTheory.T.exists_glue_functions_spec_from_pairs T.obj.B (pt T) (hSec f g T) fun p q hpq ↦ GlobalTheory.T.cocycle_local_sections_restrict_compatibly f g hg' T p q hpq
  choose G hG using ex
  exact H1.mk_eq_zero.2 ⟨G, funext fun T ↦ funext fun T' ↦ funext fun φ ↦
    (_root_.GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued f g hg' φ (G T) (G T') (hG T) (hG T')).symm⟩

end GlobalTheory.CechDR
end
end

