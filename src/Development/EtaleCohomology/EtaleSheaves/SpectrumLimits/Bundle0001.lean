module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.QuotCop
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

theorem quotCop : QuotCop := by
  intro A A' B _ _ _ φ χ ι l hl I hcop R _ g c hg
  have hg' : ∀ i, ((g i).comp (Ideal.Quotient.mk (I.map φ))).comp φ = c.comp (Ideal.Quotient.mk I) := by
    intro i
    rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, hg i]
  obtain ⟨h', ⟨h'l, h'c⟩, h'u⟩ := hcop R _ _ hg'
  have hk : ∀ b ∈ I.map χ, h' b = 0 := by
    intro b hb
    have : I.map χ ≤ RingHom.ker h' := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change h' (χ a) = 0
      rw [← RingHom.comp_apply, h'c, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hb
  refine ⟨Ideal.Quotient.lift _ h' hk, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, lq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' (l i), h'l i, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, qm, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' χ, h'c, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    have : h2.comp (Ideal.Quotient.mk _) = h' := by
      apply h'u
      refine ⟨fun i => ?_, ?_⟩
      · rw [RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk (le_l φ χ (l i) (hl i) I), ← RingHom.comp_assoc]
        exact congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (I.map φ))) (h2l i)
      · rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, h2c]
    rw [this]
    ext x
    simp

end LateralTheory.E.LevelsGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.TensCop
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

open PiTensorProduct in
theorem tensCop : TensCop := by
  intro A A' _ _ φ n
  letI : Algebra A A' := φ.toAlgebra
  refine ⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom,
    fun i => ?_, ?_, ?_⟩
  · exact (singleAlgHom (A := fun _ => A') i).comp_algebraMap
  · rw [eq_top_iff]
    intro x _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [Algebra.smul_def]
      refine Subring.mul_mem _ ?_ ?_
      · rw [← (singleAlgHom (A := fun _ => A') 0).commutes r]
        exact Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)
      · have : tprod A f = ∏ i, singleAlgHom (A := fun _ => A') i (f i) := by
          simp only [singleAlgHom_apply, ← tprod_prod]
          congr 1
          exact (Finset.univ_prod_mulSingle f).symm
        rw [this]
        exact Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)
    | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  · intro R _ g c hg
    letI : Algebra A R := c.toAlgebra
    have hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r := fun i r => by
      change g i (φ r) = c r
      rw [← RingHom.comp_apply, hg i]
    let ga : Fin (n + 1) → (A' →ₐ[A] R) := fun i => AlgHom.mk (g i) (hc i)
    let F : (Π _ : Fin (n + 1), A') →ₘₗ[A] R :=
      (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)
    let H := liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])
    have hH : ∀ i a, H (singleAlgHom (A := fun _ => A') i a) = g i a := by
      intro i a
      change lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _
      rw [lift.tprod]
      simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [Finset.prod_eq_single i]
      · simp [ga]
      · intro j _ hj
        simp [ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      · simp
    refine ⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
    · ext a
      exact hH i a
    · ext a
      exact H.commutes a
    · have hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r := fun r => by
        change h2 (algebraMap A _ r) = c r
        rw [← RingHom.comp_apply, h2c]
      let H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R := AlgHom.mk h2 hc2
      have : H2 = H := by
        apply PiTensorProduct.algHom_ext
        intro i
        ext a
        change h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)
        rw [hH]
        exact RingHom.congr_fun (h2l i) a
      exact congrArg AlgHom.toRingHom this

end LateralTheory.E.LevelsGenPf
end
end

