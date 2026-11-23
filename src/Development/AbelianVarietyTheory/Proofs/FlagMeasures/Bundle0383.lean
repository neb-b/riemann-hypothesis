module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFibreMeasuresArchimedeanGramMap
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ArchGramFibre

open Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation PI.VolStabS

theorem exists_real_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y := by
  have : IsTotallyReal F := hCM.1
  obtain ⟨k, eK, hK⟩ := exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := exists_coord_pi eK hK (Fin M)
  obtain ⟨n, eV, hV⟩ := exists_coord_pi e1 h1 (Fin a)
  obtain ⟨k2, e2, h2⟩ := exists_coord_pi eK hK (Fin a)
  obtain ⟨N, eM, hM⟩ := exists_coord_pi e2 h2 (Fin a)
  have hdiv : ∀ n : ℕ, 0 < n → ∀ S ∈ HermR (Ainf F) σ a, ∃ T ∈ HermR (Ainf F) σ a, n • T = S := by
    intro n hn S hS
    let c : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1 / n)
    have hsc : sigR (Ainf F) σ c = c :=
      (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
    refine ⟨c • S, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hsc]
      rw [hS i j]
    · have hc1 : (n : Ainf F ⊗[F] E) * c = 1 := by
        simp only [c]
        rw [← map_natCast (algebraMap F (Ainf F ⊗[F] E)) n, ← map_mul]
        have : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_one_div_cancel this, map_one]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, ← mul_assoc, hc1, one_mul]
  obtain ⟨m, eH, hH⟩ := exists_coord_sub (X := Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) eM hM
    (HermR (Ainf F) σ a) (isClosed_HermR (Ainf F) σ a) hdiv
  exact ⟨n, m, eV, eH, hV, hH⟩

theorem gramB_surj_of_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
      ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S := by
  intro X hX S
  have := semisimpleTens_holds F E σ hCM
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let s := sigR (Ainf F) σ
  let Z : Fin a → Fin M → Ainf F ⊗[F] E :=
    fun i => Matrix.vecMul (fun l => s (X i l)) (JR (F := F) (Ainf F) J)
  have hZh : ∀ i y, hR (Ainf F) σ J (X i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) (Ainf F) J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) (Ainf F)) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR (Ainf F))).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _
  have hZ : LinearIndependent (Ainf F ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → Ainf F ⊗[F] E := fun l => ∑ i, g i * s (X i l)
    have hv0 : Matrix.vecMul v (JR (F := F) (Ainf F) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Ainf F) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • X i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum, map_mul, s, sigR_invol (Ainf F) σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hX _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol (Ainf F) σ hσ, map_zero] at e2
    exact e2
  let half : Ainf F ⊗[F] E := algebraMap F (Ainf F ⊗[F] E) (1/2)
  have hh : half + half = 1 := by
    simp only [half, ← map_add (f := _)]; norm_num
    first | rfl | exact Algebra.TensorProduct.one_def.symm
  have hsh : s half = half := (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes _
  have hw : ∀ j, ∃ w : Fin M → Ainf F ⊗[F] E, ∀ i, ∑ k, Z i k * w k =
      half * (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) i j :=
    fun j => exists_dual_of_linIndep Z hZ _
  choose Y hY using hw
  refine ⟨Y, ?_⟩
  funext i j
  have h1 : hR (Ainf F) σ J (X i) (Y j) = half * (S : Matrix _ _ _) i j := by rw [hZh]; exact hY j i
  have h2 : hR (Ainf F) σ J (Y i) (X j) = half * (S : Matrix _ _ _) i j := by
    rw [← hR_herm (Ainf F) σ hσ J hJ.1 (X j) (Y i), hZh, hY i j]
    simp only [map_mul]
    rw [show sigR (Ainf F) σ half = half from hsh, S.2 i j]
  show hR (Ainf F) σ J (X i) (Y j) + hR (Ainf F) σ J (Y i) (X j) = _
  rw [h1, h2, ← add_mul, hh, one_mul]

theorem exists_submersion_coords (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) :
    ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
      (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
      (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
      (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
        gramR (Ainf F) σ J X) ∧
      ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X)) := by
  obtain ⟨n, m, eV, eH, hV, hH⟩ := exists_real_coords F E σ hCM M a
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  let Q : (Fin a → Fin M → Ainf F ⊗[F] E) → HermR (Ainf F) σ a := gramH (Ainf F) σ hσ J hJ.1
  let β : (Fin a → Fin M → Ainf F ⊗[F] E) → (Fin a → Fin M → Ainf F ⊗[F] E) →
      HermR (Ainf F) σ a := fun X Y => ⟨gramB (Ainf F) σ J X Y, gramB_mem (Ainf F) σ hσ J hJ.1 X Y⟩
  have hβc : Continuous (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (Fin a → Fin M → Ainf F ⊗[F] E) => β p.1 p.2) := by
    exact (continuous_gramB (Ainf F) σ J).subtype_mk _
  have hβa : ∀ x y z, β (x + y) z = β x z + β y z := by
    intro x y z; apply Subtype.ext; funext i j
    show gramB (Ainf F) σ J (x + y) z i j = gramB (Ainf F) σ J x z i j + gramB (Ainf F) σ J y z i j
    simp only [gramB, Pi.add_apply, PI.VolStabS.hR_add_left, PI.VolStabS.hR_add_right]
    abel
  have hβs : ∀ x y, β x y = β y x := by
    intro x y; apply Subtype.ext; funext i j
    simp only [β, gramB]; exact add_comm _ _
  have hQ : ∀ x, β x x = Q x + Q x := by
    intro x; apply Subtype.ext; funext i j; rfl
  obtain ⟨hC, hD⟩ := quadCoord_holds _ _ n m eV eH Q β hV hH hβc hβa hβs hQ
  refine ⟨n, m, eV, eH, fun y => eH (Q (eV.symm y)), hV, hH, hC, fun X => ?_, fun X hX => ?_⟩
  · simp [Q, gramH]
  · intro t
    obtain ⟨Y, hY⟩ := gramB_surj_of_free F E σ hCM M a J hJ X hX (eH.symm t)
    refine ⟨eV Y, ?_⟩
    rw [hD X Y]
    have : β X Y = eH.symm t := Subtype.ext hY
    rw [this, Homeomorph.apply_symm_apply]

theorem gram_densities (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Ainf F) σ J) Subtype.val ν {X | LinearIndependent (Ainf F ⊗[F] E) X} := by
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ := exists_submersion_coords F E σ hCM M a J hJ
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μ.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (ν.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map ν (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := submDens_holds n m _ _ hμ' hν' f' hC
  refine densAll_transport μ ν (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

theorem exists_fibreFamily : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M a : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J →
    ∀ (μ : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a)),
      μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
      ∃ fib : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib := by
  intro F E _ _ _ _ _ σ hCM M a J hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hCM.2.2.2
  exact fib_of_tens PI.VolStabS.DiscreteGroups.fibOfDens_holds
    (tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)) μ ν hμ hν
    (gram_densities F E σ hCM M a J hJ μ ν hμ hν)

end GlobalTheory.ArchGramFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPadicLiftMulPrincipalCongruenceOfReduction
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LiftRed

theorem liftred_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, Valued.v z < 1 → ‖θ z‖ < 1) → ∀ (A : GL (Fin n) (v.adicCompletion F)) (γ : GL (Fin n) (ZMod g)), (∀ a b, Valued.v ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1) → ∃ k ∈ (GlobalTheory.GLp.red g n).ker, Matrix.GeneralLinearGroup.map θ.toRingHom A = GlobalTheory.GLp.lift g n γ * GlobalTheory.GLp.inc g n k := by
  intro F _ _ v g n _ θ hθ A γ hA

  have hent : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ < 1 := by
    intro a b
    have h := hθ _ (hA a b)
    rwa [map_sub, map_natCast] at h
  have hle : ∀ a b, ‖θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b)‖ ≤ 1 := by
    intro a b
    have h1 : ‖((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])‖ ≤ 1 := by
      exact_mod_cast PadicInt.norm_le_one ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g])
    have := IsUltrametricDist.norm_add_le_max
      (θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b) -
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g]))
      ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le (le_of_lt (hent a b)) h1)
  let Mx : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => ⟨θ ((A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b), hle a b⟩
  have hred : Mx.map (PadicInt.toZMod (p := g)) = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext a b
    simp only [Matrix.map_apply]
    have hm : Mx a b - ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : ℤ_[g]) ∈
        RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast]
      exact hent a b
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero] at hm
    exact hm
  have hdet : IsUnit Mx.det := by
    by_contra hnu
    have hm : Mx.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnu
    rw [RingHom.mem_ker, RingHom.map_det,
      show (PadicInt.toZMod (p := g)).mapMatrix Mx = (γ : Matrix (Fin n) (Fin n) (ZMod g)) from hred] at hm
    have hu : IsUnit (γ : Matrix (Fin n) (Fin n) (ZMod g)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    rw [hm] at hu
    exact not_isUnit_zero hu
  let M : GL (Fin n) ℤ_[g] := Matrix.nonsingInvUnit Mx hdet
  have hMred : GlobalTheory.GLp.red g n M = γ := by
    ext a b
    have := congrFun (congrFun hred a) b
    exact this
  have hMinc : GlobalTheory.GLp.inc g n M = Matrix.GeneralLinearGroup.map θ.toRingHom A := by
    ext a b
    rfl
  set N := Function.invFun (GlobalTheory.GLp.red g n) γ with hN
  have hNred : GlobalTheory.GLp.red g n N = γ := Function.invFun_eq ⟨M, hMred⟩
  refine ⟨N⁻¹ * M, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hNred, hMred, inv_mul_cancel]
  · rw [GlobalTheory.GLp.lift, ← hN, ← map_mul, mul_inv_cancel_left, hMinc]

end GlobalTheory.LiftRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.AutInhab

noncomputable section

namespace GlobalTheory.PerpInst

theorem exists_drop {n : ℕ} (ε : Fin n → Bool) (k : Fin n) :
    ∃ (m : ℕ) (f : Fin m → Fin n), m + 1 = n ∧ Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      ∀ b, (univ.filter fun a => ε (f a) = b).card + (if ε k = b then 1 else 0) =
        (univ.filter fun a => ε a = b).card := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  refine ⟨m, k.succAbove, rfl, Fin.succAbove_right_injective, k.succAbove_ne, fun b => ?_⟩
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ k, add_comm]

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem form_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (J G : Matrix (Fin n) (Fin n) E)
    (y x : Fin n → E) : star (G *ᵥ y) ⬝ᵥ (J *ᵥ (G *ᵥ x)) = star y ⬝ᵥ ((Gᴴ * J * G) *ᵥ x) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem hasSignature_all (I : AutInst) {P Q : ℕ} (h : HasSig I P Q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) P Q := by
  have key : ∃ v, φ = I.φ v ∨ φ = ComplexEmbedding.conjugate (I.φ v) := by
    refine ⟨(InfinitePlace.mk φ).comap (algebraMap I.F I.E), ?_⟩
    rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk φ) with h | h <;>
      rcases InfinitePlace.embedding_mk_eq φ with h' | h'
    · exact Or.inl (h'.symm.trans h)
    · right
      rw [← h, h']; simp
    · exact Or.inr (h'.symm.trans h)
    · left
      exact star_injective (h'.symm.trans h)
  obtain ⟨v, rfl | rfl⟩ := key
  · rw [← (h v).1, ← (h v).2]; exact hasSignature_inst I v
  · rw [← (h v).1, ← (h v).2]
    refine hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ((I.P_unit v).map (starRingEnd ℂ).mapMatrix) ?_
    have h1 := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
    simp only [Matrix.map_mul] at h1
    have h2 : (Formalism.REAL.Jm (I.ε v)).map (starRingEnd ℂ) = Formalism.REAL.Jm (I.ε v) := by
      rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext a
      split_ifs <;> simp
    rw [h2] at h1
    exact h1

theorem exists_point (I : AutInst) (ε : Fin I.n → Bool) (γ : GL (Fin I.n) I.E)
    (hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = signMat I.E ε) :
    ∃ xf : I.Gf, ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I (1, xf) ↔ z ∈ intLat I.E I.n := by
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  have hsur : Function.Surjective G.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 γ.isUnit
  have hinj : Function.Injective G.mulVec := Matrix.mulVec_injective_iff_isUnit.2 γ.isUnit
  let Λ : Submodule (𝓞 I.E) (Fin I.n → I.E) := (intLat I.E I.n).map (G.mulVecLin.restrictScalars (𝓞 I.E))
  have hΛ : ∀ z, G *ᵥ z ∈ Λ ↔ z ∈ intLat I.E I.n := fun z =>
    ⟨fun ⟨w, hw, e⟩ => (hinj e : w = z) ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
  obtain ⟨xf, hxf⟩ := _root_.GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ (Submodule.IsLattice.of_fg I.E ((intLat_fg _).map _)) (by
      intro x
      obtain ⟨x, rfl⟩ := hsur x
      rw [hΛ, intLat_dual ε]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        have := h y hy
        rw [hform_eq, ← hγ, ← form_mulVec, ← hform_eq] at this
        exact this
      · intro h y hy
        have := h _ ((hΛ y).2 hy)
        rwa [hform_eq, form_mulVec, hγ, ← hform_eq] at this)
  exact ⟨xf, fun z => hxf ▸ hΛ z⟩

theorem exists_isPerpInst : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  intro I P Q h _ s hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  set ε := I.ε v with hε
  have hP : (univ.filter fun a => ε a = true).card = P := (h v).1
  have hQ : (univ.filter fun a => ε a = false).card = Q := (h v).2
  obtain ⟨k, hk⟩ : ∃ k, ε k = s := by
    have : 0 < (univ.filter fun a => ε a = s).card := by
      cases s
      · rw [hQ]; exact hs
      · rw [hP]; exact hs
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.FlagMeas.sameKindIsometric I.E I.cm.cmUnram I.n I.J (signMat I.E ε) I.J_herm (signMat_isHerm ε)
    I.J_det (signMat_det ε) ⟨I.L, Submodule.IsLattice.of_fg I.E I.L_fg, fun x => by simpa only [hform_eq] using I.L_dual x⟩
    ⟨intLat I.E I.n, Submodule.IsLattice.of_fg I.E (intLat_fg _), fun x => by simpa only [hform_eq] using intLat_dual ε x⟩
    (fun φ => ⟨P, Q, hasSignature_all I h φ, by
      rw [signMat_map, ← hP, ← hQ]
      exact hasSignature_of_frame (P := 1) isUnit_one (by simp)⟩)
  obtain ⟨xf, hxf⟩ := exists_point I ε γ hγ
  obtain ⟨m, f, hm, hf, hfk, hcard⟩ := exists_drop ε k
  set G : Matrix (Fin I.n) (Fin I.n) I.E := γ.val with hG
  let C : Matrix (Fin I.n) (Fin m) I.E := (1 : Matrix (Fin I.n) (Fin I.n) I.E).submatrix id f
  refine ⟨ofSigns I.cm (fun a => ε (f a)), RingEquiv.refl I.E, G *ᵥ Pi.single k 1, G * C, xf,
    ⟨fun _ => rfl, hm, ?_, ?_, ?_, ?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · rw [form_mulVec, hγ]
    simp [signMat, sgn, hk]
  · have : star (G *ᵥ Pi.single k 1) ᵥ* (I.J * (G * C)) = star (Pi.single k 1) ᵥ* ((Gᴴ * I.J * G) * C) := by
      rw [star_mulVec, vecMul_vecMul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    funext j
    simp [signMat, C, vecMul, dotProduct, Pi.single_apply, Matrix.one_apply, hfk j]
    rfl
  · have : (G * C)ᴴ * I.J * (G * C) = Cᴴ * (Gᴴ * I.J * G) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    refine this.trans ?_
    rw [hγ]
    change _ = signMat I.E fun a => ε (f a)
    ext i j
    rw [Matrix.mul_apply]
    simp [signMat, C, Matrix.one_apply, Matrix.diagonal_apply, hf.eq_iff]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · exact (hxf _).2 (Submodule.subset_span ⟨k, by simp⟩)
  · change ∀ y : Fin m → I.E, y ∈ intLat I.E m ↔ (G * C) *ᵥ y ∈ lamX I (1, xf)
    intro y
    rw [← mulVec_mulVec, hxf, mem_intLat, mem_intLat]
    constructor
    · intro hy i
      change ∑ j, C i j * y j ∈ _
      refine sum_mem fun j _ => mul_mem ?_ (hy j)
      simp only [C, submatrix_apply, id, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro hy j
      have := hy (f j)
      simpa [C, mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using this
  · change (univ.filter fun a => ε (f a) = true).card = _
    have := hcard true
    rw [hP, hk] at this
    cases s <;> simp at this ⊢ <;> omega
  · change (univ.filter fun a => ε (f a) = false).card = _
    have := hcard false
    rw [hQ, hk] at this
    cases s <;> simp at this ⊢ <;> omega

end GlobalTheory.PerpInst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamily
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGenAll

theorem famGen : GlobalTheory.SnFam.FamGen := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  exact _root_.GlobalTheory.SnFamGen.genFam D X Y u u'
    (fun t ht t' ht' _ hs hc => _root_.GlobalTheory.ScalSymm.scal_symm D X Y u u' t t' (hG t ht) (hG t' ht') hs hc)
    (fun t ht t' ht' t'' ht'' _ _ hs hc hs' hc' =>
      _root_.GlobalTheory.ScalTrans.scalar_pair_trans D X Y u u' t t' t'' (hG t ht) (hG t' ht') (hG t'' ht'') hs hc hs' hc')

end GlobalTheory.SnFamGenAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLatticeStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), 1 ≤ Tu D u → IsBase D u F0 → IsRowLat D F0 Λ → (IsSplit D F0 Λ → Λ ⊓ toO (hS D) (Wb D) ∈ glueSet D u (L0X D Λ (lf D F0)) ∧ Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X) ∧ (∀ L' : LatW D, ∀ L ∈ glueSet D u L', IsRowLat D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ IsSplit D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ (XS D F0 ⊔ L ⊔ YS D) ⊓ toO (hS D) (Wb D) = L) := by
  first | exact @GlobalTheory.LoopC.RowGlue.main | exact GlobalTheory.LoopC.RowGlue.main | (intros; apply GlobalTheory.LoopC.RowGlue.main <;> assumption)
end

