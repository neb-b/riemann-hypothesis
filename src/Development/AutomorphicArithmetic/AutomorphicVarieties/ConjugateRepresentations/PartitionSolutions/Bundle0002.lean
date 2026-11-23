module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatFacts
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satFacts :
    SatFacts := by
  intro Γ V S _ _ _ d G T K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ s p
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ, t, ht, ?_, ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hT
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact hK
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ⁻¹, t, ht, ?_, ?_⟩
      · rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hT
      · rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hK
  · intro hK s
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨γ, t, ht, hT, hp⟩
    have hc : Continuous fun q : V => t • (G.ρ γ) q :=
      continuous_const.smul (G.ρ γ).continuous
    filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq
    exact ⟨γ, t, ht, hT, hq⟩
  · rintro K' hKK' s p ⟨γ, t, ht, hT, hp⟩
    exact ⟨γ, t, ht, hT, hKK' hp⟩
  · intro s p t ht
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]
    constructor
    · rintro ⟨γ, u, hu, hT, hK⟩
      exact ⟨γ, u * t, mul_pos hu ht, hT, hK⟩
    · rintro ⟨γ, u, hu, hT, hK⟩
      refine ⟨γ, u / t, div_pos hu ht, hT, ?_⟩
      rwa [div_mul_cancel₀ u ht.ne']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFactsAlt
section
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep UpperTheory.V.Lit.Dr

private theorem sand_split (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ) (p : HV E a) :
    sand (GeneralLinearGroup.map (pInf E) (GlobalTheory.UnitaryBC.splitCentre E a t)) p = (Real.exp t * Real.exp t) • p := by
  rw [GlobalTheory.UnitaryBC.splitCentre, pInf_infGL]
  refine Subtype.ext ?_
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp t • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  change Matrix.of (sand _ p).1 = (Real.exp t * Real.exp t) • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]

theorem UpperTheory.V.Cj.A.splitFacts :
    SplitFacts := by
  intro E _ _ _ a
  refine ⟨fun t => ⟨pFin_infGL _, _, mul_pos (Real.exp_pos t) (Real.exp_pos t), sand_split E a t⟩,
    fun r hr => ⟨Real.log r / 2, fun p => ?_⟩⟩
  rw [sand_split, ← Real.exp_add, add_halves, Real.exp_log hr]
end

