module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
section
noncomputable section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace Ad3P.EigenformCoefficientExpansion

theorem exp_of {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ) := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

theorem coef_zero {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) : coef f 0 = 0 := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  exact CuspFormClass.qExpansion_coeff_zero f one_pos hp

end Ad3P.EigenformCoefficientExpansion

open Ad3P.EigenformCoefficientExpansion in
theorem Ad3P.sEig : Ad3P.SEig := by
  intro k N _ _ χ g
  refine ⟨⟨fun γ hγ => g.char γ hγ, fun τ => exp_of g.f τ⟩, coef_zero g.f, g.one, fun p n hp => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Eigenform.a, mul_zero, dvd_zero, if_true, Nat.zero_div, coef_zero, add_zero]
  · have h := g.eig p hp n hn
    simp only [Eigenform.a]
    rw [← h]
    split_ifs <;> ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
section
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

namespace Ad3P.DihedralUnramifiedPlaces

def toH (η : HeckeCharacter ℚ) : Formalism.L2.Host.HChar ℚ :=
  ⟨Circle.toUnits.comp η.toIdele, by
    refine ⟨?_, fun k => ?_⟩
    · refine Units.continuous_iff.2 ⟨continuous_subtype_val.comp η.continuous_toIdele, ?_⟩
      have h : (fun x => ((((Circle.toUnits.comp η.toIdele) x)⁻¹ : ℂˣ) : ℂ)) =
          fun x => (((Circle.toUnits.comp η.toIdele) x⁻¹ : ℂˣ) : ℂ) := by
        funext x
        rw [map_inv]
      rw [h]
      exact continuous_subtype_val.comp (η.continuous_toIdele.comp continuous_inv)
    · exact (congrArg Circle.toUnits (η.toIdele_diagonal k)).trans (map_one _)⟩

theorem ord_eq (v : Ad3.Pl) {x : Ad3.Qv v} (hx : x ≠ 0) : ord x = -WithZero.log (Valued.v x) := by
  have h1 := norm_eq_absNorm_zpow_neg_ord v hx
  have h2 := normalizedAbv_eq_zpow v hx
  rw [normalizedAbv_apply] at h2
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal v
  have := zpow_right_injective₀ (by linarith) hq.ne' (h1.symm.trans h2)
  omega

theorem loc_eq (η : HeckeCharacter ℚ) (v : Ad3.Pl) (x : (Ad3.Qv v)ˣ) : (toH η).loc v x = localChar η v x := rfl

end Ad3P.DihedralUnramifiedPlaces
end
end

