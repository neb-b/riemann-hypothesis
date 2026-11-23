module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero
section
namespace PI.PowBddIntWork

open Matrix Polynomial

theorem eval₂_int_map_eq_zero {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by
  have e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [← e, ← Polynomial.hom_eval₂, h, map_zero]

theorem stepB : StepB := by
  intro E _ k γ hγ i
  obtain ⟨p, hpm, hp⟩ := hγ
  let F := AlgebraicClosure E
  let γ' : Matrix (Fin k) (Fin k) F := γ.map (algebraMap E F)
  have hp' : p.eval₂ (algebraMap ℤ (Matrix (Fin k) (Fin k) F)) γ' = 0 :=
    eval₂_int_map_eq_zero (algebraMap E F).mapMatrix p γ hp

  have hroot : ∀ μ ∈ γ'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have hs : μ ∈ spectrum F γ' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic γ').ne_zero).1 hμ
    have h1 := spectrum.subset_polynomial_aeval γ' (p.map (algebraMap ℤ F)) ⟨μ, hs, rfl⟩
    have h2 : Polynomial.aeval γ' (p.map (algebraMap ℤ F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp']
    rw [h2] at h1
    refine ⟨p, hpm, ?_⟩
    have h3 : (p.map (algebraMap ℤ F)).eval μ = p.eval₂ (algebraMap ℤ F) μ := Polynomial.eval_map _ _
    rw [← h3]
    by_contra hne
    rw [spectrum.mem_iff, sub_zero] at h1
    exact h1 ((Ne.isUnit hne).map _)
  have hcp : γ'.charpoly = γ.charpoly.map (algebraMap E F) := Matrix.charpoly_map γ _
  have hinj : Function.Injective ((algebraMap E F).toIntAlgHom) := (algebraMap E F).injective
  rw [← isIntegral_algHom_iff _ hinj]
  show IsIntegral ℤ (algebraMap E F (γ.charpoly.coeff i))
  rw [← Polynomial.coeff_map, ← hcp]

  have hq : γ'.charpoly.Monic := Matrix.charpoly_monic _
  have hcard : Multiset.card γ'.charpoly.roots = γ'.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  by_cases hi : i ≤ γ'.charpoly.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hi, hq.leadingCoeff, one_mul]
    refine IsIntegral.mul (IsIntegral.pow (IsIntegral.neg isIntegral_one) _) ?_
    show _ ∈ integralClosure ℤ F
    unfold Multiset.esymm
    refine Subalgebra.multiset_sum_mem _ ?_
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
    refine Subalgebra.multiset_prod_mem _ ?_
    intro x hx
    exact hroot x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hs).1 hx)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact isIntegral_zero

end PI.PowBddIntWork
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports
section
namespace PI.PowBddIntWork

open Matrix NumberField

theorem stepA : StepA := by
  intro E _ _ k γ N hN hint
  classical
  let L : (Fin k → Fin k → 𝓞 E) →ₗ[ℤ] Matrix (Fin k) (Fin k) E :=
    { toFun := fun B => Matrix.of fun i j => ((N : E))⁻¹ * algebraMap (𝓞 E) E (B i j)
      map_add' := fun B C => by ext i j; simp [mul_add]
      map_smul' := fun c B => by
        ext i j
        first | (simp [zsmul_eq_mul]; ring) | simp [zsmul_eq_mul] }
  have hfg : (Submodule.map L ⊤).FG := Module.Finite.fg_top.map L
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ {γ}) ≤ Submodule.map L ⊤ := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro x hx
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
    refine ⟨fun i j => IsIntegralClosure.mk' (𝓞 E) ((N : E) * (γ ^ n) i j) (hint n i j), trivial, ?_⟩
    have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
    ext i j
    simp [L, IsIntegralClosure.algebraMap_mk', hN']
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  exact isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ {γ}) (isNoetherian_of_le hle) γ
    (Algebra.subset_adjoin (Set.mem_singleton γ))

end PI.PowBddIntWork
end

