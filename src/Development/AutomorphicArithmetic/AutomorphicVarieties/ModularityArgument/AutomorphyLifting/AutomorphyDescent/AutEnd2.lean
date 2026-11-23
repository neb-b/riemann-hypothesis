module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AutEnd2OfAutPt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Across2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001

@[expose] public section

open UpperTheory.GalN.V

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open UpperTheory.V.Z.Win UpperTheory.V.Z
open scoped Matrix

private theorem detAlg (H : Af.HypothesesH) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {W : G ℚ Ω →* GL (Fin 2) (Qbar l)} (hW : Continuous W) {M : ℕ} (hM : 1 ≤ M) (hχ : Af.KillsMu M (Matrix.GeneralLinearGroup.det.comp W)) :
    Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W) := by
  have : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω M
  let k := Fintype.card (ZMod M)ˣ
  have hk : 0 < k := Fintype.card_pos
  have hpow (s : G ℚ Ω) : (Matrix.GeneralLinearGroup.det.comp W s) ^ k = 1 := by
    rw [← map_pow]
    refine hχ _ fun ζ hζ => ?_
    have hfix := hμ.autToPow_spec ℚ (s ^ k)
    dsimp [k] at hfix
    rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod,
      ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at hfix
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one hζ
    rw [map_pow, ← hfix]
  refine (Af.algOfCyc H ℚ Ω l ι).1 _ (Matrix.GeneralLinearGroup.continuous_det.comp hW) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  exact ⟨A, hA, 0, k, hk, fun s _ => by rw [neg_zero, zpow_zero, mul_one, hpow]⟩

private theorem polTwo {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (h : Af.IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W)) (c : G ℚ Ω)
    (hc : Sd.IsCC c) : Af.Sol.Pol ι (W.comp (Base.galEmb ℚ K Ω)) := by
  let J : GL (Fin 2) (Qbar l) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
  have hJ (A : Matrix (Fin 2) (Fin 2) (Qbar l)) :
      Aᵀ * J.val * A = A.det • J.val := by
    change Aᵀ * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
  refine ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, c, J * W c⁻¹, h, Ws.auSign _, hc, fun s s' hconj => ?_⟩
  let t := Base.galEmb ℚ K Ω s
  have hs' : Base.galEmb ℚ K Ω s' = c * t * c⁻¹ := hconj
  have hmul : W c⁻¹ * W (c * t * c⁻¹) = W t * W c⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  have hval : (W c⁻¹).val * (W (c * t * c⁻¹)).val = (W t).val * (W c⁻¹).val :=
    congrArg Units.val hmul
  change (W t).valᵀ * (J * W c⁻¹).val * (W (Base.galEmb ℚ K Ω s')).val =
    (W t).val.det • (J * W c⁻¹).val
  rw [hs', Units.val_mul, ← Matrix.smul_mul, ← hJ]
  simp only [Matrix.mul_assoc, hval]
