module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.UniqGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdDual

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreUniqueness
section
noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

theorem td_of_inj {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    [TotallyDisconnectedSpace α] (e : β → α) (he : Continuous e) (hi : Function.Injective e) :
    TotallyDisconnectedSpace β :=
  ⟨fun t _ ht x hx y hy =>
    hi ((isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (ht.image e he.continuousOn)) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

theorem gram_map_fibre_uniqueness : FibUniq := by
  intro F E _ _ _ _ _ σ n J v a μ ν hν fib fib' h h'
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨ι, _, ⟨e⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
  have : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := td_of_inj e e.continuous e.injective
  have : LocallyCompactSpace (Fv F v ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : T2Space (Fv F v ⊗[F] E) := e.isEmbedding.t2Space
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  have := hν
  have hfree : IsOpen (IndepV (E := E) (n := n) v a) :=
    isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
      (a := a) (M := n)
  have hA : ∀ S : Set (HermR (Fv F v) σ a), MeasurableSet S →
      MeasurableSet (gramR (Fv F v) σ J ⁻¹' (Subtype.val '' S)) := by
    intro S hS
    letI : MeasurableSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := borel _
    haveI : BorelSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) := ⟨rfl⟩
    have hcl : IsClosedEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
    have hemb : MeasurableEmbedding
        (Subtype.val : HermR (Fv F v) σ a → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      hcl.measurableEmbedding
    exact (hemb.measurableSet_image.2 hS).preimage (continuous_gramR (Fv F v) σ J).measurable
  exact fib_unique μ ν (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a) hA
    Subtype.val_injective hfree fib fib' h h'

theorem omUnique_of_sdEx (h0 : SdEx) {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) : OmUnique σ J ψ v a :=
  omUnique_of σ J ψ v a h0 gram_map_fibre_existence gram_map_fibre_uniqueness

end PI.OmFibreUniq.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst
section
noncomputable section

namespace PI.OmFibreUniq.W.SdInst

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem BR_symm (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n a : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X Y : Fin a → Fin n → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y = BR (Fv F v) σ J Y X := by
  let φ : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) :=
    Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hφ : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z = φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hinv : ∀ z, φ (φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, Algebra.TensorProduct.map_tmul, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  let e := AlgEquiv.ofBijective φ (Function.Involutive.bijective hinv)
  have htr : ∀ z, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z := by
    intro z
    rw [hφ]
    exact Algebra.trace_eq_of_algEquiv e z
  have hss : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z) = z := by
    intro z
    rw [hφ, hφ]
    exact hinv z
  have hsJ : ∀ i j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (JR (Fv F v) J i j) = JR (Fv F v) J j i := by
    intro i j
    simp [JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul, hJ]
  have hsym : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J x y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (hR (Fv F v) σ J y x) := by
    intro x y
    unfold hR Formalism.UG.hform
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hss, hsJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  unfold BR
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hsym, htr]

theorem BR_cont_joint (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (fun p : (Fin a → Fin n → Fv F v ⊗[F] E) × (Fin a → Fin n → Fv F v ⊗[F] E) =>
      BR (Fv F v) σ J p.1 p.2) := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) := by
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  let φ : (Fv F v ⊗[F] E) →ₐ[Fv F v] (Fv F v ⊗[F] E) :=
    Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ
  have hφ : ∀ z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z = φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hsg : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) := by
    have h1 : ⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) = ⇑(φ.toLinearMap) := funext hφ
    rw [h1]
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  unfold BR hR Formalism.UG.hform
  fun_prop

theorem pairHerm_symm (σ : E →ₐ[F] E) (a : ℕ) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S T = pairHerm (Fv F v) σ a T S := by
  unfold pairHerm
  have h : ∑ i, ∑ j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j * (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i =
      ∑ i, ∑ j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [h]

theorem pairHerm_smul (σ : E →ₐ[F] E) (a : ℕ) (c : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (c • S) T = c * pairHerm (Fv F v) σ a S T := by
  unfold pairHerm
  have h : ∑ i, ∑ j, ((c • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j *
      (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i =
      c • ∑ i, ∑ j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j *
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact smul_mul_assoc c _ _
  rw [h, map_smul, smul_eq_mul]
  ring

theorem pairHerm_cont_joint (σ : E →ₐ[F] E) (a : ℕ) :
    Continuous (fun p : HermR (Fv F v) σ a × HermR (Fv F v) σ a =>
      pairHerm (Fv F v) σ a p.1 p.2) := by
  have htr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) := by
    first
    | exact IsModuleTopology.continuous_of_linearMap _
    | exact LinearMap.continuous_of_finiteDimensional _
  unfold pairHerm
  refine continuous_const.mul (htr.comp (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_))
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i j).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem j i)

theorem sdEx_of_psiNT (hP : PsiNT) : SdEx := by
  intro F E _ _ _ _ _ σ n J ψ v a hS
  obtain ⟨hCM, hJ, hψ, hstd⟩ := hS
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hc : Continuous (psiV F ψ v) := continuous_psiV ψ hψ.1 v
  have hadd := psiV_add ψ v
  have hn : ∀ r, ‖psiV F ψ v r‖ = 1 := fun r => hψ.2.1 _
  have hnt := hP ψ v hψ hstd hCM.1
  constructor
  · obtain ⟨μ, hμ⟩ := exists_selfDual_measure v (BR (Fv F v) σ J (n := a)) (psiV F ψ v) hc hadd hn hnt
      (fun x x' y => BR_add (Fv F v) σ J x' x y) (fun c x y => BR_smul_left v σ J c x y)
      (BR_symm v σ hσ J hJ.1) (BR_cont_joint v σ J)
      (dualAt_alt v (Module.finBasis F E) σ J (nondeg_BR v σ hσ J hJ.2))
    exact ⟨μ, hμ⟩
  · obtain ⟨μ, hμ⟩ := exists_selfDual_measure v (pairHerm (Fv F v) σ a) (psiV F ψ v) hc hadd hn hnt
      (fun x x' y => pairHerm_add (Fv F v) σ a x' x y) (fun c x y => pairHerm_smul v σ a c x y)
      (pairHerm_symm v σ a) (pairHerm_cont_joint v σ a)
      (dualAt_H v (Module.finBasis F E) σ hσ a)
    exact ⟨μ, hμ⟩

end PI.OmFibreUniq.W.SdInst
end
end

