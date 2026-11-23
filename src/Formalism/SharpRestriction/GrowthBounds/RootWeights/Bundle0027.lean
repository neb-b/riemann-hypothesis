module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0026

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.LatticeTheoremSingleRepLinf
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem lattice_theorem_single_rep_linf (h : InvariantDenominatorLinftyBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation) (hInv : InvariantProjectionExists)
    (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (hE : IsGLRep E)
    (M : Submodule O V) (hM : UZLattice E M) (hMQ : MQ (K := KK O) M = ⊤)
    (lam : Fin n → ℤ) (hdom : Dominant lam) (e : Module.End (KK O) V) (he : IsIsoProj E lam e) (x : V)
    (hx : x ∈ M) :
    ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) • e x ∈ M := by
  have : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime
  by_cases hv : ∃ v0, IsHWV E lam v0
  · obtain ⟨v0, hv0⟩ := hv
    have hL := cyclicSubmodule_isSubrepresentation E v0
    obtain ⟨d, b, hbM, hbc⟩ := hB O V M hM.2 hMQ (cyclicSubmodule E v0)
    have hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E) :=
      hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE
    obtain ⟨P, hP⟩ := hInv n (KK O) _ _ hEH
    obtain ⟨hl1, hl2⟩ := hLat O n V E hE M hM hMQ _ hL
    have key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) •
        P ((b.coord i).smulRight x) (b i) ∈ M := by
      intro i
      have hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0) := by
        intro y hy
        obtain ⟨o, ho⟩ := hbc y hy i
        rw [LinearMap.smulRight_apply, ho, algebraMap_smul]
        exact M.smul_mem _ hx
      have h1 := h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf
      have h2 := h1 (b i) (hbM i)
      rw [LinearMap.smul_apply] at h2
      refine pow_smul_mem_of_le' M _ ?_ h2
      refine Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)
      rw [hl2, hMQ]
      exact linf_homRep_le_ell_add E hE lam hdom v0 hv0 hL
    rw [← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm,
      Finset.smul_sum]
    exact M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)
  · have h0 : e x = 0 := by
      have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e := by
        refine iSup_le fun mu => ?_
        by_cases hmu : mu = lam
        · subst hmu
          refine Submodule.span_le.2 ?_
          rintro y ⟨u, _, v, hv', _⟩
          exact absurd ⟨v, hv'⟩ hv
        · intro y hy
          exact he.2 mu hmu y hy
      have : x ∈ (⨆ mu, isoSub E mu) := by rw [hTop n (KK O) V E hE]; trivial
      exact hle this
    rw [h0, smul_zero]; exact M.zero_mem

theorem isotypicProjectorTheoremField_of_linfty_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : IsotypicProjectorTheoremField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw hSw e he x hx
  rw [Finset.smul_sum]
  refine M.sum_mem fun lam hlam => ?_
  have h1 := lattice_theorem_single_rep_linf h (isotypic_submodules_span_top D h2) restriction_is_representation hom_space_is_representation (invariant_projection_exists D h2) (isotypic_projector_trace_formula D h2)
    lattice_adapted_basis_exists hom_lattice_dividedPower_stable p n' O S hG n V E hE M hM hMQ lam (hSw lam hlam) (e lam) (he lam hlam) x hx
  refine pow_smul_mem_of_le' M _ ?_ h1
  exact Finset.le_sup (f := fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam)) hlam

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanHighestComponentIntegral
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def loweringOperatorSpan (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x}

theorem loweringSpanOfHeight_le_total (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringOperatorSpan (O := O) E lam v := by
  unfold loweringSpanOfHeight loweringOperatorSpan
  exact Submodule.span_mono fun x ⟨nu, h, _⟩ => ⟨nu, h⟩

private theorem eq_of_isLoweringWord_of_weight_eq {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : nu = lam → x = v := by
  cases h with
  | base => intro _; rfl
  | step c d hdc l hl nu' x' h' =>
    intro heq
    have h1 := loweringWord_height_ge_highest h'
    have h2 := weight_height_add_root_smul nu' c d l
    rw [heq] at h2
    have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hl
    have hcd : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast (Fin.lt_iff_val_lt_val.mp hdc)
    nlinarith

theorem loweringSpan_divided_power_stable [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : UZStable (O := O) E (loweringOperatorSpan (O := O) E lam v) := by
  intro u hu y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    have hxL : x ∈ loweringSpanOfHeight (O := O) E lam v (weightHeightAscending nu - weightHeightAscending lam) :=
      Submodule.subset_span ⟨nu, hnu, by omega⟩
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · refine loweringSpanOfHeight_le_total E lam v ((weightHeightAscending nu - weightHeightAscending lam).toNat) ?_
        exact raising_dividedPower_loweringSpan hE hv _ nu x hnu (by omega) a b h k
      · exact loweringSpanOfHeight_le_total E lam v _ (loweringSpan_lower_dividedPower_mem E lam v h k _ x hxL)
    · have hw := loweringWord_mem_weightSpace hE hv.2.1 hnu
      rw [binomial_diagonal_on_weight hw a k]
      have : ((Ring.choose (nu a) k : ℤ) : KK O) = algebraMap O (KK O) ((Ring.choose (nu a) k : ℤ) : O) := by
        simp
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨nu, hnu⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

theorem loweringSpan_highest_component_integral {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : ∀ y ∈ loweringOperatorSpan (O := O) E lam v,
      ∃ c : O, y - (algebraMap O (KK O) c) • v ∈ otherWts E lam := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    by_cases h : nu = lam
    · refine ⟨1, ?_⟩
      rw [eq_of_isLoweringWord_of_weight_eq hnu h, map_one, one_smul, sub_self]
      exact Submodule.zero_mem _
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_smul, sub_zero]
      exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h (loweringWord_mem_weightSpace hE hv.2.1 hnu))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    have : x + y - algebraMap O (KK O) (c1 + c2) • v =
        (x - algebraMap O (KK O) c1 • v) + (y - algebraMap O (KK O) c2 • v) := by
      rw [map_add (f := _), add_smul]; abel
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨a * c, ?_⟩
    rw [map_mul, mul_smul, algebraMap_smul, ← smul_sub]
    exact Submodule.smul_of_tower_mem _ a h

theorem highest_vector_mem_nabla [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : v ∈ Nabla (O := O) E lam v := by
  intro u hu
  exact loweringSpan_highest_component_integral hE hv (u v)
    (integral_enveloping_preserves_submodule (loweringSpan_divided_power_stable hE hv) hu v (Submodule.subset_span ⟨lam, IsLoweringWord.base⟩))

end hw

theorem highest_vector_integrality : HighestWeightVectorIntegrality := by
  intro p n' O _ _ _ S hG n _ lam V _ _ _ _ E v hI
  haveI := dvr_fraction_field_char_zero_prime S hG.prime
  exact highest_vector_mem_nabla hI.1 hI.2.2.1

end Formalism.MainNotions.G.GLWeightTheory
end
end

