module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEq
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCard

section general
variable {G : Type} [Group G]

def dcos (J : Subgroup G) (g : G) : Set G := {x | ∃ a ∈ J, ∃ b ∈ J, x = a * g * b}

theorem dcos_eq_iUnion (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    dcos J g = ⋃ j ∈ R, (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G) := by
  ext x
  simp only [dcos, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨j', ⟨hj'R, hj'⟩, -⟩ := h2 a ha
    refine ⟨j', hj'R, ?_⟩
    have e : (j' * g)⁻¹ * (a * g * b) = ((j' * g)⁻¹ * (a * g)) * b := by group
    rw [e]; exact J.mul_mem hj' hb
  · rintro ⟨j, hjR, hj⟩
    exact ⟨j, h1 j hjR, (j * g)⁻¹ * x, hj, by group⟩

theorem pairwiseDisjoint_cosets (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    (R : Set G).PairwiseDisjoint (fun j => (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G)) := by
  intro j₁ hj₁ j₂ hj₂ hne
  refine Set.disjoint_left.2 fun x hx₁ hx₂ => hne ?_
  simp only [Set.mem_preimage, SetLike.mem_coe] at hx₁ hx₂
  have hm : (j₁ * g)⁻¹ * (j₂ * g) ∈ J := by
    have e : (j₁ * g)⁻¹ * (j₂ * g) = ((j₁ * g)⁻¹ * x) * ((j₂ * g)⁻¹ * x)⁻¹ := by group
    rw [e]; exact J.mul_mem hx₁ (J.inv_mem hx₂)
  have hself : (j₂ * g)⁻¹ * (j₂ * g) ∈ J := by simp
  exact (h2 j₂ (h1 j₂ (Finset.mem_coe.1 hj₂))).unique ⟨Finset.mem_coe.1 hj₁, hm⟩ ⟨Finset.mem_coe.1 hj₂, hself⟩

theorem dcos_inv (J : Subgroup G) (g : G) : dcos J g⁻¹ = Inv.inv ⁻¹' dcos J g := by
  ext x
  simp only [dcos, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by group⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, ?_⟩
    rw [← inv_inv x, h]; group

theorem measure_dcos [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (J : Subgroup G) (hJ : MeasurableSet (J : Set G)) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    μ (dcos J g) = R.card * μ J := by
  rw [dcos_eq_iUnion J g R h1 h2, measure_biUnion_finset (pairwiseDisjoint_cosets J g R h1 h2)
    (fun j _ => measurable_const_mul _ hJ)]
  simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]

theorem card_eq_of_unimodular [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (J : Subgroup G) (hJo : IsOpen (J : Set G)) (hJt : μ J ≠ ⊤) (g : G) (R R' : Finset G)
    (h1 : ∀ j ∈ R, j ∈ J) (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J)
    (h1' : ∀ j ∈ R', j ∈ J) (h2' : ∀ j ∈ J, ∃! j', j' ∈ R' ∧ (j' * g⁻¹)⁻¹ * (j * g⁻¹) ∈ J) :
    R.card = R'.card := by
  haveI : μ.IsInvInvariant := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have h0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have e1 := measure_dcos μ J hJo.measurableSet g R h1 h2
  have e2 := measure_dcos μ J hJo.measurableSet g⁻¹ R' h1' h2'
  rw [dcos_inv, Measure.measure_preimage_inv, e1] at e2
  have h := (ENNReal.mul_left_inj h0 hJt).1 e2
  exact_mod_cast h

end general

theorem card_isReps_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k)
    (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ) :
    IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  intro hR hR'
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI : IsTopologicalGroup (GL (A ⊕ D) k) := inferInstance
  haveI : LocallyCompactSpace (GL (A ⊕ D) k) := inferInstance
  haveI : SecondCountableTopology (GL (A ⊕ D) k) := inferInstance
  haveI : BorelSpace (GL (A ⊕ D) k) := GlobalTheory.SplitFlip.borel_GL
  obtain ⟨hJo, hJc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric k A D
  haveI : (Measure.haar : Measure (GL (A ⊕ D) k)).IsMulRightInvariant :=
    GlobalTheory.SplitFlip.isMulRightInvariant_of_haar _
  refine ⟨card_eq_of_unimodular (Measure.haar : Measure (GL (A ⊕ D) k)) (parahoric k A D) hJo
    hJc.measure_lt_top.ne g R R' (fun j hj => (hR.1 j hj).1) hR.2
    (fun j hj => (hR'.1 j hj).1) hR'.2, ?_⟩
  obtain ⟨j', ⟨hj', -⟩, -⟩ := hR.2 1 (one_mem _)
  exact ⟨j', hj'⟩

end GlobalTheory.ParHeckeCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPartIso

section Swap

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (φ : A →+* B) (h : Continuous φ) : Continuous (bc (n := Fin n) φ) :=
  Continuous.units_map _ (continuous_id.matrix_map h)

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  have h2 := congrArg (fun M => M.map φ) hg'
  simp only [Matrix.map_mul, hJ] at h2
  have e1 : cT σ' (g.1.map φ) = (cT σ g.1).map φ := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, h]
  change cT σ' (g.1.map φ) * J' * g.1.map φ = J'
  rw [e1]; exact h2

def ujEquiv {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (σ : A →+* A) (σ' : B →+* B) (φ : A ≃+* B) (hc : Continuous φ) (hc' : Continuous φ.symm)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') : UJ σ J ≃ₜ* UJ σ' J' where
  toFun g := ⟨bc φ.toRingHom g.1, bc_mem _ _ φ.toRingHom h _ _ hJ g.2⟩
  invFun g := ⟨bc φ.symm.toRingHom g.1, bc_mem _ _ φ.symm.toRingHom (fun x => φ.injective (by
      change φ (σ (φ.symm x)) = φ (φ.symm (σ' x))
      rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])) _ _
      (hJ ▸ Matrix.ext fun _ _ => φ.symm_apply_apply _) g.2⟩
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.symm_apply_apply _))
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.apply_symm_apply _))
  map_mul' g h := Subtype.ext (map_mul (bc φ.toRingHom) g.1 h.1)
  continuous_toFun := ((continuous_bc φ.toRingHom hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_bc φ.symm.toRingHom hc').comp continuous_subtype_val).subtype_mk _

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

def swapR : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem continuous_swapR :
    @Continuous _ _ _ (tensTopL (F := F) (E := E) R) (swapR (F := F) (E := E) R) ∧
    @Continuous _ _ (tensTopL (F := F) (E := E) R) _ (swapR (F := F) (E := E) R).symm := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) R
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  haveI := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let L : R ⊗[F] E ≃ₗ[R] E ⊗[F] R :=
    { (swapR (F := F) (E := E) R).toAddEquiv with
      map_smul' := fun c y => by
        change swapR (F := F) (E := E) R (c • y) = c • swapR (F := F) (E := E) R y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  exact ⟨IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [TopologicalSpace R] in
theorem swapR_sig (x : R ⊗[F] E) :
    Formalism.UG.sigR σ R (swapR R x) = swapR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def swapU : letI := tensTopL (F := F) (E := E) R; HA R σ J ≃ₜ* UPts σ J R :=
  letI := tensTopL (F := F) (E := E) R
  ujEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapR R) (continuous_swapR R).1 (continuous_swapR R).2
    (swapR_sig R σ) (JR R J) (J.map (inclE (F := F) R)) (Matrix.ext fun _ _ => rfl)

end Swap

section Fin

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def finEquiv : finPts σ J ≃ₜ* GFin σ J where
  toFun g := projFin σ J g.1
  invFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  left_inv g := Subtype.ext (ext_inf_fin σ J ((projInf_ofFin σ J _).trans (mem_finPts.1 g.2).symm)
    (projFin_ofFin σ J _))
  right_inv y := projFin_ofFin σ J y
  map_mul' g h := map_mul (projFin σ J) g.1 h.1
  continuous_toFun := (continuous_projFin σ J).comp continuous_subtype_val
  continuous_invFun := (continuous_ofFin σ J).subtype_mk _

end Fin

theorem exists_finIso : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); ∃ e : ↥(GfC V) ≃ₜ* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ∀ g, (e g).1.1 = finM V hn g.1 := by
  intro D V n hn
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  exact ⟨(finEquiv D.sp.cm.sig V.gram).trans
    (swapU (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.sp.cm.sig V.gram), fun g => rfl⟩

end GlobalTheory.FinPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DenseKFiniteVectorsUnitaryGroupRepStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_kFinite_vectors_unitaryGroupRep : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ → Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v} := by
  first | exact @GlobalTheory.CompactRep.dense_isKFin | exact GlobalTheory.CompactRep.dense_isKFin | (intros; apply GlobalTheory.CompactRep.dense_isKFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBases
section
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPosNoShortIntegralVectorFromPoint
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo


open FirstMinPos in
theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinMEqOneIffMemGinfC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem finM_eq_one_iff_mem_GinfC :
    ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V), finM V hn g = 1 ↔ g ∈ GinfC V := by
  intro D V n hn g
  subst hn
  have e0 : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by simp [finM]
  have e : (Formalism.L2.Theta.mt V g).map (toEAf D) = (finHom V g).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e0, e]
  constructor
  · intro h
    show finHom V g = 1
    apply Units.ext
    have hinj := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    apply Matrix.map_injective hinj
    show (finHom V g).val.map _ = (1 : Matrix _ _ _).map _
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro hk
    have h : finHom V g = 1 := hk
    have h2 : (finHom V g).val = 1 := by rw [h]; rfl
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstCoupledKernelFiniteDatumLevelSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  first | exact @GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | exact GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp | (intros; apply GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp <;> assumption)
end

