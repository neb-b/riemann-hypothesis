module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0064
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightSpaceEqBotOutsideSupport

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightComponentsMemInvariant
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem weight_components_mem_invariant [CharZero K] (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (s : Finset (Fin n → ℤ)) : ∀ f : (Fin n → ℤ) → V, (∀ mu ∈ s, f mu ∈ weightSp E mu) →
      ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W :=
  _root_.UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant E W hW s

theorem weightSpace_independent [CharZero K] (E : GLOps n K V) : iSupIndep (weightSp E) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv h0 i hi
  have := weight_components_mem_invariant E ⊥ (fun a x hx => by simp [(Submodule.mem_bot K).1 hx]) s v hv (by simp [h0]) i hi
  simpa using this

variable (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)

@[simp] theorem restricted_operator_coe (a b : Fin n) (x : W) : ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

theorem restricted_mem_weightSpace_iff (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isHWV_iff (lam : Fin n → ℤ) (v : W) : IsHWV (restrictStableOperators E W h) lam v ↔ IsHWV E lam (v : V) := by
  unfold IsHWV
  rw [restricted_mem_weightSpace_iff]
  refine and_congr (by simp) (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => ?_
  rw [Subtype.ext_iff]
  simp

theorem restricted_isGLRep [CharZero K] (hE : IsGLRep E) : IsGLRep (restrictStableOperators E W h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    ext x
    have h1 := congrArg (fun f : Module.End K V => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restricted_operator_coe]
    rw [h1]
    split_ifs <;> simp
  · intro x
    obtain ⟨W0, hfd, hx0, hst⟩ := hE.2.1 (x : V)
    refine ⟨W0.comap W.subtype, ?_, hx0, fun a b y hy => hst a b _ hy⟩
    have h1 : FiniteDimensional K ((W0.comap W.subtype).map W.subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective W.subtype W.injective_subtype (W0.comap W.subtype)).symm
  · rw [eq_top_iff]
    intro x _
    have hx : (x : V) ∈ ⨆ mu, weightSp E mu := by rw [hE.2.2]; trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
    have hmem := weight_components_mem_invariant E W (fun a => h a a) f.support f (fun mu _ => hf mu)
      (by have : ∑ mu ∈ f.support, f mu = (x : V) := hsum
          rw [this]; exact x.2)
    have hx2 : x = ∑ mu ∈ f.support.attach, (⟨f mu.1, hmem mu.1 mu.2⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only
      rw [Finset.sum_attach f.support (fun mu => f mu)]
      exact hsum.symm
    rw [hx2]
    refine Submodule.sum_mem _ fun mu _ => ?_
    exact Submodule.mem_iSup_of_mem mu.1 ((restricted_mem_weightSpace_iff E W h mu.1 _).2 (hf mu.1))

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionDiagonalApplyEqSmul
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

@[simp] theorem restrictRepresentation_coe (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (a b : Fin n) (x : W) :
    ((restrictRepresentation E W h a b x : W) : V) = E a b x := rfl

@[simp] theorem homRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (f : V →ₗ[K] V') (x : V) :
    homRepresentation E E' a b f x = E' a b (f x) - f (E a b x) := by
  simp [homRepresentation]

theorem restrict_mem_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictRepresentation E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSp_iff_diagonal_apply, mem_weightSp_iff_diagonal_apply]
  constructor
  · intro hx a
    have e := congrArg Subtype.val (hx a)
    simpa using e
  · intro hx a
    ext
    simpa using hx a

theorem restrictRepresentation_isRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V)
    (h : IsSubrepresentation E W) : IsGLRep (restrictRepresentation E W h) := by
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    have e := congrArg (fun f => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restrictRepresentation_coe]
    rw [e]
    split_ifs <;> simp
  · obtain ⟨s, π, -, hinv, -, hmem, hsum⟩ := weight_projections_exist E hE
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ mu ∈ s, (⟨π mu x, hinv mu W (fun a y hy => h a a y hy) x x.2⟩ : W) := by
      ext
      simp [hsum]
    rw [hx]
    refine Submodule.sum_mem _ fun mu _ => ?_
    refine Submodule.mem_iSup_of_mem mu ?_
    rw [restrict_mem_weightSpace_iff]
    exact hmem mu x

theorem weightProjection_diagonal_apply_eq_smul [CharZero K] (E : GLOps n K V) (hE : IsGLRep E) (nu : Fin n → ℤ) (π : Module.End K V)
    (hπ : IsWtProj E nu π) (a : Fin n) (x : V) : π (E a a x) = (nu a : K) • π x := by
  have hx : x ∈ (⨆ mu, weightSp E mu) := hE.2.2 ▸ Submodule.mem_top
  refine Submodule.iSup_induction (p := weightSp E) (motive := fun y => π (E a a y) = (nu a : K) • π y) hx
    (fun mu y hy => ?_) ?_ (fun y w hy hw => ?_)
  · rw [(mem_weightSp_iff_diagonal_apply E mu y).1 hy a, map_smul]
    by_cases hmu : mu = nu
    · subst hmu
      rfl
    · rw [hπ.2 mu hmu y hy, smul_zero, smul_zero]
  · simp
  · simp only [map_add (f := _), hy, hw, smul_add]

theorem homRepresentation_isRep [CharZero K] [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V)
    (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (homRepresentation E E') := by
  refine ⟨fun a b c d => ?_, fun f => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · ext f x
    have h1 := congrArg (fun g => g (f x)) (hE'.1 a b c d)
    have h2 := congrArg (fun g => f (g x)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, homRepresentation_apply, map_sub]
    split_ifs at h1 h2 ⊢ <;>
      simp only [LinearMap.zero_apply, map_zero, sub_zero, zero_sub, homRepresentation_apply, map_sub,
        map_neg] at h1 h2 ⊢ <;>
      (rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]; abel)
  · obtain ⟨s, π, hπ, -, -, -, hsum⟩ := weight_projections_exist E hE
    obtain ⟨s', π', -, -, -, hmem', hsum'⟩ := weight_projections_exist E' hE'
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ mu ∈ s, ∑ mu' ∈ s', (π' mu').comp (f.comp (π mu)) := by
      ext x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_sum]
      rw [hsum x, hsum' (f x)]
    rw [hf]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun mu' _ => ?_
    refine Submodule.mem_iSup_of_mem (mu' - mu) ?_
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [weightProjection_diagonal_apply_eq_smul E hE mu (π mu) (hπ mu) a x, map_smul, map_smul,
      (mem_weightSp_iff_diagonal_apply E' mu' _).1 (hmem' mu' _) a]
    simp only [Pi.sub_apply, Int.cast_sub, sub_smul]

theorem root_differences_bddAbove [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E W, ∃ nu ∈ wtsOf E W, ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  refine ⟨s.sup fun mu => s.sup fun nu => Finset.univ.sup fun a => (mu a - nu a).toNat, ?_⟩
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
  have hmu' : mu ∈ s := by
    by_contra hc
    apply hmu
    rw [weightSpace_eq_bot_outside_support E s hs mu hc, bot_inf_eq]
  have hnu' : nu ∈ s := by
    by_contra hc
    apply hnu
    rw [weightSpace_eq_bot_outside_support E s hs nu hc, bot_inf_eq]
  have hk : mu a - nu a = (k : ℤ) := by
    have e := congrFun heq a
    simp only [Pi.sub_apply, Pi.smul_apply, rootW, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      sub_zero, smul_eq_mul, mul_one] at e
    exact e
  have hk' : k ≤ (mu a - nu a).toNat := by omega
  exact Finset.le_sup_of_le hmu' (Finset.le_sup_of_le hnu' (Finset.le_sup_of_le (Finset.mem_univ a) hk'))

end

theorem restriction_is_representation : RestrictionIsRepresentation := by
  intro n K V _ _ _ _ _ E hE W h
  exact restrictRepresentation_isRep E hE W h

theorem hom_space_is_representation : HomSpaceIsRepresentation := by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE'
  exact homRepresentation_isRep E E' hE hE'

end Formalism.MainNotions.G.GLWeightTheory
end
end

