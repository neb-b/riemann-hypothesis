module

public import Mathlib
public import GroundTheory.AutomorphicForms.GKModules.GKModule

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.CoeToRepresentationApply
section
noncomputable section

namespace GroundTheory.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

open Set Module

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]

def GKModule.rep (M : h.GKModule K V) :
    Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) V :=
  FreeMonoid.lift (Sum.elim (fun X => M.ρ X) fun k => M.σ k)

@[simp] theorem GKModule.rep_of_inl (M : h.GKModule K V) (X : h.lieSubalgebra) :
    M.rep (FreeMonoid.of (Sum.inl X)) = M.ρ X :=
  rfl

@[simp] theorem GKModule.rep_of_inr (M : h.GKModule K V) (k : K) :
    M.rep (FreeMonoid.of (Sum.inr k)) = M.σ k :=
  rfl

def GKModule.IsIrreducible (M : h.GKModule K V) : Prop := M.rep.IsIrreducible

theorem GKModule.rep_comm (M : h.GKModule K V) {T : End ℂ V} (hρ : ∀ X, M.ρ X * T = T * M.ρ X)
    (hσ : ∀ k, M.σ k * T = T * M.σ k) (a : FreeMonoid (h.lieSubalgebra ⊕ K)) :
    M.rep a * T = T * M.rep a := by
  induction a using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x a ih =>
    rw [map_mul, mul_assoc, ih, ← mul_assoc, ← mul_assoc]
    congr 1
    rcases x with X | k
    · exact hρ X
    · exact hσ k

theorem GKModule.apply_σ_mem (M : h.GKModule K V) (Y : Subrepresentation M.rep) (k : K) {y : V}
    (hy : y ∈ Y.toSubmodule) : M.σ k y ∈ Y.toSubmodule :=
  Y.apply_mem_toSubmodule (FreeMonoid.of (Sum.inr k)) hy

section SubQuot

variable (M : h.GKModule K V) (U : Subrepresentation M.rep) (U₀ : Submodule ℂ U.toSubmodule)
  (hU₀ : ∀ a, U₀ ≤ U₀.comap (U.toRepresentation a))

abbrev quotRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) (U.toSubmodule ⧸ U₀) :=
  U.toRepresentation.quotient U₀ hU₀

theorem quotRep_mk (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    quotRep M U U₀ hU₀ a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation a u) :=
  rfl

theorem exists_form_extend (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) :
    ∃ ψ : Dual ℂ V, ∀ u : U.toSubmodule, φ (Submodule.Quotient.mk u) = ψ u := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (φ ∘ₗ U₀.mkQ)
  exact ⟨ψ, fun u => (LinearMap.congr_fun hψ u).symm⟩

theorem coe_toRepresentation_apply (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    ((U.toRepresentation a u : U.toSubmodule) : V) = M.rep a u :=
  rfl

def subQuotρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (U.toSubmodule ⧸ U₀) where
  toFun X := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inl X))
  map_add' X Y := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.add_apply,
      ← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_add, coe_toRepresentation_apply, GKModule.rep_of_inl, map_add (f := _),
      LinearMap.add_apply]
  map_smul' r X := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    rw [Submodule.coe_smul_of_tower]
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inl, map_smul, LinearMap.smul_apply]
  map_lie' {X Y} := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_sub, coe_toRepresentation_apply, GKModule.rep_of_inl, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply]

def subQuotσ : Representation ℂ K (U.toSubmodule ⧸ U₀) where
  toFun k := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inr k))
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.one_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_one, Module.End.one_apply]
  map_mul' k₁ k₂ := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.mul_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_mul, Module.End.mul_apply]

theorem subQuotρ_mk (X : h.lieSubalgebra) (u : U.toSubmodule) :
    subQuotρ M U U₀ hU₀ X (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inl X)) u) :=
  rfl

theorem subQuotσ_mk (k : K) (u : U.toSubmodule) :
    subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inr k)) u) :=
  rfl

theorem subQuot_locallyFinite (q : U.toSubmodule ⧸ U₀) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => subQuotσ M U U₀ hU₀ k q)) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hfin := M.locallyFinite u
  set S : Submodule ℂ U.toSubmodule :=
    Submodule.span ℂ (range fun k : K => U.toRepresentation (FreeMonoid.of (Sum.inr k)) u)
  have hS : FiniteDimensional ℂ S := by
    have hle : S.map U.toSubmodule.subtype ≤ Submodule.span ℂ (range fun k : K => M.σ k u) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    have : FiniteDimensional ℂ (S.map U.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ U.toSubmodule.injective_subtype S).symm
  have hle : Submodule.span ℂ (range fun k : K =>
      subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u)) ≤ S.map U₀.mkQ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem subQuot_hasContinuousCoeff : Representation.HasContinuousCoeff (subQuotσ M U U₀ hU₀) := by
  intro φ q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have : (fun k : K => φ (subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u))) =
      fun k => ψ (M.σ k u) := by
    funext k
    rw [subQuotσ_mk, hψ]
    rfl
  rw [this]
  exact M.hasContinuousCoeff ψ u

theorem subQuot_hasDerivAt (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K)
    (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) (q : U.toSubmodule ⧸ U₀) :
    HasDerivAt (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩ q))
      (φ (subQuotρ M U U₀ hU₀ (h.toLie X) q)) 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have h1 : (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩
      (Submodule.Quotient.mk u))) = fun t => ψ (M.σ ⟨h.expG (t • X), hX t⟩ u) := by
    funext t
    rw [subQuotσ_mk, hψ]
    rfl
  have h2 : φ (subQuotρ M U U₀ hU₀ (h.toLie X) (Submodule.Quotient.mk u)) =
      ψ (M.ρ (h.toLie X) u) := by
    rw [subQuotρ_mk, hψ]
    rfl
  rw [h1, h2]
  exact M.hasDerivAt_coeff X hX ψ u

theorem subQuot_map_ρ (k : K) (X : 𝔤) (q : U.toSubmodule ⧸ U₀) :
    subQuotσ M U U₀ hU₀ k (subQuotρ M U U₀ hU₀ (h.toLie X) q) =
      subQuotρ M U U₀ hU₀ (h.toLie (h.Ad k X)) (subQuotσ M U U₀ hU₀ k q) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [subQuotρ_mk, subQuotσ_mk, subQuotσ_mk, subQuotρ_mk]
  congr 1
  exact Subtype.ext (M.map_ρ k X u)

def GKModule.subQuot : h.GKModule K (U.toSubmodule ⧸ U₀) where
  ρ := subQuotρ M U U₀ hU₀
  σ := subQuotσ M U U₀ hU₀
  locallyFinite := subQuot_locallyFinite M U U₀ hU₀
  hasContinuousCoeff := subQuot_hasContinuousCoeff M U U₀ hU₀
  hasDerivAt_coeff := subQuot_hasDerivAt M U U₀ hU₀
  map_ρ := subQuot_map_ρ M U U₀ hU₀

theorem GKModule.subQuot_rep : (M.subQuot U U₀ hU₀).rep = quotRep M U U₀ hU₀ :=
  FreeMonoid.hom_eq fun x => by
    rcases x with X | k <;> rfl

end SubQuot

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.CompactRep
section
noncomputable section

namespace GroundTheory.Automorphic

namespace CompactRep

open MeasureTheory Module Set

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {σ : Representation ℂ K W}

theorem exists_isCompl_stable (hσ : Representation.HasContinuousCoeff σ) (U : Submodule ℂ W)
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U) :
    ∃ C : Submodule ℂ W, IsCompl U C ∧ ∀ k, ∀ c ∈ C, σ k c ∈ C := by
  classical
  borelize K
  let K₀ : TopologicalSpace.PositiveCompacts K :=
    ⟨⟨univ, isCompact_univ⟩, by simp [interior_univ]⟩
  set μ : Measure K := Measure.haarMeasure K₀
  have hμ1 : μ univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := K₀)
    simpa [K₀] using this
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  set d := finrank ℂ W
  let b := Module.finBasis ℂ W
  let e : W ≃ₗ[ℂ] (Fin d → ℂ) := b.equivFun

  let S : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k =>
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ σ k ∘ₗ e.symm.toLinearMap)
  have hSapply : ∀ k w, S k (e w) = e (σ k w) := fun k w => by
    simp [S]
  have hSmul : ∀ a c, S (a * c) = (S a).comp (S c) := fun a c => by
    ext x : 1
    simp [S, map_mul]
  have hS : Continuous S := by
    refine continuous_clm_apply.2 fun y => continuous_pi fun i => ?_
    have := hσ (b.coord i) (e.symm y)
    refine this.congr fun k => ?_
    simp [S, e, Basis.equivFun_apply, Basis.coord_apply]

  obtain ⟨C₀, hC₀⟩ := U.exists_isCompl
  let p : W →ₗ[ℂ] W := U.subtype ∘ₗ Submodule.projectionOnto U C₀ hC₀
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    show ((Submodule.projectionOnto U C₀ hC₀ u : U) : W) = u
    rw [Submodule.projectionOnto_apply_of_mem_left _ hu]
  have hpmem : ∀ w, p w ∈ U := fun w => Subtype.prop _
  let P₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ p ∘ₗ e.symm.toLinearMap)
  have hP₀ : ∀ w, P₀ (e w) = e (p w) := fun w => by simp [P₀]
  let f : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k => (S k).comp (P₀.comp (S k⁻¹))
  have hf : Continuous f := hS.clm_comp (continuous_const.clm_comp (hS.comp continuous_inv))
  have hfi : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x, Integrable (fun k => f k x) μ := fun x =>
    (hf.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfapply : ∀ k w, f k (e w) = e (σ k (p (σ k⁻¹ w))) := fun k w => by
    simp only [f, ContinuousLinearMap.comp_apply, hSapply, hP₀]
  set P := ∫ k, f k ∂μ

  have hPU : ∀ u ∈ U, P (e u) = e u := by
    intro u hu
    rw [ContinuousLinearMap.integral_apply hfi]
    have : ∀ k, f k (e u) = e u := fun k => by
      rw [hfapply, hpU _ (hU _ _ hu), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simp only [this, integral_const]
    rw [show μ.real univ = 1 by simp [Measure.real, hμ1], one_smul]

  let R : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (LinearMap.id - p) ∘ₗ e.symm.toLinearMap)
  have hPmem : ∀ w, e.symm (P (e w)) ∈ U := by
    intro w
    have h1 : R (P (e w)) = 0 := by
      rw [ContinuousLinearMap.integral_apply hfi, ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
      have : ∀ k, R (f k (e w)) = 0 := fun k => by
        rw [hfapply]
        simp only [R, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.sub_apply,
          LinearMap.id_apply, hpU _ (hU _ _ (hpmem _)), sub_self, map_zero]
      simp [this]
    have h2 : e.symm (P (e w)) - p (e.symm (P (e w))) = 0 := by
      have := congrArg e.symm h1
      simpa [R] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    exact hpmem _

  have hPcomm : ∀ g x, P (S g x) = S g (P x) := by
    intro g x
    rw [ContinuousLinearMap.integral_apply hfi, ContinuousLinearMap.integral_apply hfi,
      ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
    have h1 : ∀ k, f k (S g x) = S k (P₀ (S (k⁻¹ * g) x)) := by
      intro k
      rw [hSmul]
      rfl
    have h2 : ∀ k, S g (f k x) = S (g * k) (P₀ (S ((g * k)⁻¹ * g) x)) := by
      intro k
      rw [hSmul g k, show (g * k)⁻¹ * g = k⁻¹ by group]
      rfl
    simp only [h1, h2]
    exact (integral_mul_left_eq_self (μ := μ) (fun y => S y (P₀ (S (y⁻¹ * g) x))) g).symm

  let Q : W →ₗ[ℂ] U := LinearMap.codRestrict U
    (e.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ e.toLinearMap) fun w => hPmem w
  have hQ : ∀ x : U, Q x = x := fun x => Subtype.ext (by
    simp [Q, hPU _ x.2])
  refine ⟨LinearMap.ker Q, LinearMap.isCompl_of_proj hQ, fun k c hc => ?_⟩
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : P (e c) = 0 := by
    have := congrArg (fun y : U => e (y : W)) hc
    simpa [Q] using this
  refine Subtype.ext ?_
  simp only [Q, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearMap.coe_coe, ZeroMemClass.coe_zero]
  rw [← hSapply, hPcomm, hc', map_zero, map_zero]

end CompactRep

end GroundTheory.Automorphic
end
end

