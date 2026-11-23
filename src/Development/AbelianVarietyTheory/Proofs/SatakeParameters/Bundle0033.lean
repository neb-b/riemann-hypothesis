module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardQuotMatrixRangeDvrEqResiduePowCorank
section
open GlobalTheory.LatHecke GlobalTheory.SatakeInv

namespace GlobalTheory.IdxRank

theorem mem_smul_top_of_forall_mem {O : Type} [CommRing O] (I : Ideal O) {r : ℕ}
    (z : Fin r → O) (hz : ∀ i, z i ∈ I) : z ∈ I • (⊤ : Submodule O (Fin r → O)) := by
  have h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial

theorem card_quot_range (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O)
    (hA : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤
      LinearMap.range A.mulVecLin) :
    Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) =
      qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  classical
  set F := IsLocalRing.ResidueField O with hF
  set res : O →+* F := IsLocalRing.residue O with hres
  set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb
  set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR
  let π : (Fin r → O) →ₗ[O] (Fin r → F) := (Algebra.linearMap O F).compLeft (Fin r)
  have hπ : ∀ x i, π x i = res (x i) := fun x i => rfl
  have hπs : Function.Surjective π := by
    intro y
    refine ⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩
    ext i
    exact (IsLocalRing.residue_surjective (y i)).choose_spec
  have hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x) := by
    intro x
    ext i
    have h2 : π x = res ∘ x := rfl
    rw [h2, hπ]
    exact RingHom.map_mulVec res A x i
  let φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R) := (R.mkQ.restrictScalars O).comp π
  have hφs : Function.Surjective φ :=
    (Submodule.mkQ_surjective R).comp hπs
  have hker : LinearMap.ker φ = LinearMap.range A.mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : π x ∈ R := by
        have : R.mkQ (π x) = 0 := hx
        simpa using this
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨y', rfl⟩ := hπs y
      have hy2 : π (A.mulVec y') = π x := by
        rw [hπA]; exact hy
      have hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin := by
        apply hA
        apply mem_smul_top_of_forall_mem
        intro i
        have h1 : π (x - A.mulVec y') i = 0 := by
          rw [map_sub, hy2, sub_self]; rfl
        rw [hπ] at h1
        exact (IsLocalRing.residue_eq_zero_iff _).1 h1
      have : x = (x - A.mulVec y') + A.mulVecLin y' := by
        simp
      rw [this]
      exact Submodule.add_mem _ hz ⟨y', rfl⟩
    · rintro ⟨y, rfl⟩
      show R.mkQ (π (A.mulVec y)) = 0
      rw [hπA]
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨π y, rfl⟩
  have e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hφs)).toEquiv
  rw [Nat.card_congr e]
  have hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r := by
    have := Submodule.finrank_quotient_add_finrank R
    simpa using this
  have hrank : Ab.rank = Module.finrank F R := rfl
  have hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank := by
    omega
  have : Finite ((Fin r → F) ⧸ R) := Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  rfl

end GlobalTheory.IdxRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormula
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem trDR_projection : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L),
    trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  intro k K L _ _ _ _ _ _ _ _ _ α β
  obtain ⟨m, b, ω, rfl⟩ := (GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β
  have hT := (GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]

end GlobalTheory.W1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertAtOfUniqueUnramifiedPrimeStatement
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInertAt_of_unique_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ semiLoc v)) → (∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E, (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInertAt (maximalRealSubfield E) E v P := by
  first | exact @GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | exact GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | (intros; apply GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexGlMapStandardLatticeOfIntegral
section
open GlobalTheory.LatHecke GlobalTheory.SatakeInv

noncomputable section
namespace GlobalTheory.LatHecke

def coordIncl (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) :
    (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

theorem coordIncl_apply {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} (x : Fin r → O) :
    coordIncl O K r x = fun i => algebraMap O K (x i) := rfl

theorem coordIncl_injective {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] {r : ℕ} : Function.Injective (coordIncl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem std_eq_map_top (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (r : ℕ) :
    (std O K r).1 = (⊤ : Submodule O (Fin r → O)).map (coordIncl O K r) := by
  rw [← (Pi.basisFun O (Fin r)).span_eq, Submodule.map_span, ← Set.range_comp]
  show Submodule.span O (Set.range (Pi.basisFun K (Fin r))) = _
  congr 2
  funext i
  funext j
  simp [coordIncl_apply, Pi.single_apply]

theorem glMap_std_eq {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K)
    (hg : (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K)) :
    glMap g (std O K r).1 = (LinearMap.range A.mulVecLin).map (coordIncl O K r) := by
  rw [glMap, std_eq_map_top, ← Submodule.map_comp, LinearMap.range_eq_map,
    ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply, coordIncl_apply, hg]
  funext i
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

end GlobalTheory.LatHecke


open GlobalTheory.LatHecke in
theorem GlobalTheory.LatHecke.relIndex_glMap_std_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  intro O K _ _ _ _ _ _ r A g hg
  rw [glMap_std_eq A g hg, std_eq_map_top]
  refine ⟨?_, ?_⟩
  · have h := AddSubgroup.relIndex_map_map_of_injective (f := (coordIncl O K r).toAddMonoidHom)
      (LinearMap.range A.mulVecLin).toAddSubgroup (⊤ : Submodule O (Fin r → O)).toAddSubgroup
      coordIncl_injective
    refine h.trans ?_
    rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    rfl
  · intro h
    rw [← Submodule.map_smul''] at h
    exact (Submodule.map_le_map_iff_of_injective coordIncl_injective _ _).1 h
end
end

