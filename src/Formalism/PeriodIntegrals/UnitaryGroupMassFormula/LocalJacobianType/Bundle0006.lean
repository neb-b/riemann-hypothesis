module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0005
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DiagonalPhaseFirstVector
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem continuous_tr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)

theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]

theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add (f := _), psiV_add', hy x hx, hy' x hx, mul_one]

theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]

def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ

theorem trE_mem_Aset {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (j : Fin (Module.finrank F E)) :
    trE (E := E) v y j ∈ PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v) := by
  intro c hc
  have e : c * trE (E := E) v y j =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
    rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [e]
  exact hy _ (smul_bas_mem v hc j)

variable (hK : OpenKer v ψ)
include hK

theorem conductor_isClosed : IsClosed (D1 (E := E) v ψ) := by
  have e : D1 (E := E) v ψ = ⋂ x ∈ OEv (E := E) v,
      {y | psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1} := by
    ext y; simp [D1]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_eq ((continuous_psiV_of v ψ hK).comp
    ((continuous_tr v).comp (continuous_const.mul continuous_id))) continuous_const

theorem conductor_isCompact (hnt : ∃ r, psiV F ψ v r ≠ 1) : IsCompact (D1 (E := E) v ψ) := by
  obtain ⟨y0, -, hy0⟩ := PI.OmFibreUniq.W.SdChar.Aset_bdd v (psiV F ψ v) (psiV_add' v ψ)
    (norm_psiV_of v ψ hK) hnt
  set C : Set (Fin (Module.finrank F E) → Fv F v) :=
    Set.univ.pi fun _ => (fun s => y0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
  refine (hC.image (continuous_trE_symm (E := E) v)).of_isClosed_subset (conductor_isClosed v ψ hK) ?_
  intro y hy
  refine ⟨trE (E := E) v y, fun j _ => ?_, by simp⟩
  obtain ⟨s, hs, e⟩ := hy0 _ (trE_mem_Aset v ψ hy j)
  exact ⟨s, hs, e.symm⟩

theorem conductor_mem_nhds : D1 (E := E) v ψ ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  obtain ⟨m, w, hw, hgen⟩ := exists_gens (E := E) v
  have hA := PI.OmFibreUniq.W.SdChar.Aset_mem_nhds v (psiV F ψ v) (continuous_psiV_of v ψ hK)
    (psiV_add' v ψ) (norm_psiV_of v ψ hK)
  have hN : (⋂ k, {y : Fv F v ⊗[F] E | Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) ∈
      PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v)}) ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
    refine Filter.iInter_mem.2 fun k => ?_
    have hc : Continuous fun y : Fv F v ⊗[F] E => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) :=
      (continuous_tr v).comp (continuous_const.mul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hA)
  refine Filter.mem_of_superset hN fun y hy x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc, rfl⟩ := hgen x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, psiV_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact hy k (c k) (hc k)

theorem conductor_isOpen : IsOpen (D1 (E := E) v ψ) :=
  AddSubgroup.isOpen_of_mem_nhds (D1sub (E := E) v ψ) (conductor_mem_nhds v ψ hK)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

theorem unit_forall {P : Unit → Prop} : (∀ i, P i) ↔ P () := ⟨fun h => h (), fun h _ => h⟩

theorem parabolic_volume : VolPP σ v := by
  intro g r T T' m hS hg hT μ hμ hm l
  obtain ⟨D⟩ := exists_SD hS
  have hp0 : ∀ s t, D.p 0 (D.pt s t) = s := fun s t => (D.p_pt s t).1
  have hp1 : ∀ s t, D.p 1 (D.pt s t) = t := fun s t => (D.p_pt s t).2
  have hg0 : (g : Fv F v) ≠ 0 := natCast_ne_zero v hg
  have hgO : (g : Fv F v) ∈ v.adicCompletionIntegers F := natCast_mem _ g
  have hsh : ∀ X : Set (Unit → Fv F v ⊗[F] E), μ ((D.shear id) ⁻¹' X) = μ X :=
    haar_shear μ (D.shear id) (Obox (E := E) v Unit) (obox_compact Unit) (obox_open Unit)
      (obox_nonempty Unit) (D.shear_box id)
  by_cases hl : (l : ℕ) < r
  · have ha : alp v r l ^ 2 ≠ 0 := pow_ne_zero _ (alp_ne_zero v r l)
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' (Set.univ.pi fun _ : Unit =>
          {c | D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈
            OEv (E := E) v}) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_pos hl, unit_forall]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul, D.shear_first_coordinate, D.shear_second_coordinate]
      simp only [map_add (f := _), (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        refine ⟨⟨?_, h2⟩, h3, ?_⟩
        · have e1 : alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 0 (c ()) =
              (g : Fv F v) * (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()))) -
                alp v r l ^ 2 * (g : Fv F v)⁻¹ * D.p 1 (c ()) := by
            field_simp <;> ring
          rw [e1]
          exact sub_mem (mul_mem hgO h3) h2
        · rwa [add_comm (D.p 1 (c ()))]
    have hu : ∀ _ : Unit, IsUnit (D.pt (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) (alp v r l ^ 2 * (g : Fv F v)⁻¹)) :=
      fun _ => D.isUnit_pt (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero hg0))) (mul_ne_zero ha (inv_ne_zero hg0))
    rw [hset, hsh, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt]
    rw [absV_mul, absV_mul, absV_mul, absV_pow, absV_pow, absV_inv]
    have hA := absV_pos v (alp_ne_zero v r l)
    have hG := absV_pos v hg0
    field_simp
  · have hlr : alp v r l = 1 := by unfold alp; rw [if_neg hl]
    obtain ⟨k, hk⟩ := hT
    have hk' : ((T : Fv F v) - (T' : Fv F v)) = (g : Fv F v) * (k : Fv F v) := by
      have := congrArg (Int.cast : ℤ → Fv F v) hk
      push_cast at this
      exact this
    have hset : (fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l =
        (D.shear id) ⁻¹' ((fun w => w + fun _ : Unit => D.pt ((T : Fv F v) + T') (T : Fv F v)) ⁻¹'
          (Set.univ.pi fun _ : Unit =>
            {c | D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹ * c ∈ OEv (E := E) v})) := by
      ext c
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, PPTyp,
        if_neg hl, unit_forall, Pi.add_apply]
      rw [D.mem_sc_mul, D.mem_sc_mul, D.mem_pt_mul]
      simp only [map_add (f := _), D.shear_first_coordinate, D.shear_second_coordinate, hp0, hp1, map_natCast, (D.p_sig _).1, (D.p_sig _).2, id]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, _⟩
        refine ⟨?_, h2⟩
        have e1 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') := by ring
        rw [e1]; exact h3
      · rintro ⟨h3, h2⟩
        have e0 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + T + T') =
            ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
        refine ⟨⟨?_, h2⟩, by rw [e0]; exact h3, ?_⟩
        · have e1 : (g : Fv F v)⁻¹ * (D.p 0 (c ()) + T) =
              (g : Fv F v) * (((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T'))) -
                (g : Fv F v)⁻¹ * (D.p 1 (c ()) + T) + (g : Fv F v)⁻¹ * ((T : Fv F v) - T') := by
            field_simp <;> ring
          have e2 : (g : Fv F v)⁻¹ * ((T : Fv F v) - T') = (k : Fv F v) := by
            rw [hk']; field_simp
          rw [e1, e2]
          exact add_mem (sub_mem (mul_mem hgO h3) h2) (intCast_mem _ k)
        · have e2 : ((g : Fv F v)⁻¹) ^ 2 * (D.p 1 (c ()) + D.p 0 (c ()) + T + T') =
              ((g : Fv F v)⁻¹) ^ 2 * (D.p 0 (c ()) + D.p 1 (c ()) + ((T : Fv F v) + T')) := by ring
          rw [e2]; exact h3
    have hu : ∀ _ : Unit, IsUnit (D.pt (((g : Fv F v)⁻¹) ^ 2) (g : Fv F v)⁻¹) :=
      fun _ => D.isUnit_pt (pow_ne_zero _ (inv_ne_zero hg0)) (inv_ne_zero hg0)
    rw [hset, hsh, measure_preimage_add_right, BM.box_measure_mul (E := E) v Unit μ _ hu, hm]
    simp only [Finset.univ_unique, Finset.prod_singleton, D.norm_pt, hlr, absV_one]
    rw [absV_mul, absV_pow, absV_inv]
    have hG := absV_pos v hg0
    field_simp

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

