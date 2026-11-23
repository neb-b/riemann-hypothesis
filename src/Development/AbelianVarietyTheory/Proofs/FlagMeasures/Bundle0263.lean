module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTupleHaarInvariant
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.LocalUnitaryHaar

open PI.VolSemiDirect.W.Cj Measure
open scoped NNReal Matrix

theorem stableRankOne_field (K : Type) [Field K] : HasStableRangeOne K := by
  intro a b x y h
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    simpa using isUnit_iff_ne_zero.2 hb
  · exact ⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩

theorem map_mulVec_eq_of_preserves_form {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (hA : HasStableRangeOne A) (k : ℕ) (G X : Matrix (Fin k) (Fin k) A)
    (hG : IsUnit G.det) (hXG : X.transpose * G * X = G)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map X.mulVec = μ := by
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) A := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) A := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

theorem map_lin_eq_of_stableRankOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (hR1 : HasStableRangeOne R) (g : HA R σ J)
    (μ : Measure (Fin M → R ⊗[F] E)) [μ.IsAddHaarMeasure] :
    μ.map (lin R σ J g) = μ := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M R
  set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := R) _
  let ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → R) →ₗ[R] (Fin k → R) :=
    e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F R)
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F R G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]
    rfl
  have key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'
  have hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

theorem haar_tuple_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  let ν : Measure (Fin n → Fv F v ⊗[F] E) := addHaar
  have hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν :=
    fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩
  have hpi := measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν
  have e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) =
      fun X i => lin (Fv F v) σ J g (X i) := rfl
  rw [isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1,
    hpi.map_eq]
  rw [e1]
  exact hpi.measurable.aemeasurable

end GlobalTheory.LocalUnitaryHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalUnitaryTop

theorem linearIndependent_iff_smul_basis {K S V ι α : Type} [Field K] [CommRing S] [Algebra K S]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower K S V] [Fintype ι] [Fintype α]
    (b : Module.Basis ι K S) (X : α → V) :
    LinearIndependent S X ↔ LinearIndependent K fun p : ι × α => b p.1 • X p.2 := by
  refine ⟨fun h => linearIndependent_smul b.linearIndependent h, fun h => ?_⟩
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 := h (fun p => b.repr (g p.2) p.1) (by
    rw [← hg, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr (g j), Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => (smul_assoc _ _ _).symm)
  exact b.ext_elem fun k => by simpa using h0 (k, i)

theorem isOpen_linearIndependent {K S ι α β : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [CommRing S] [Algebra K S] [TopologicalSpace S] [IsModuleTopology K S] [IsTopologicalRing S]
    [Fintype ι] [Fintype α] [Fintype β] (b : Module.Basis ι K S) :
    IsOpen {X : α → β → S | LinearIndependent S X} := by
  let e : (β → S) ≃ₗ[K] (β → ι → K) := LinearEquiv.piCongrRight fun _ => b.equivFun
  have hb : Continuous b.equivFun :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc : Continuous fun (X : α → β → S) (p : ι × α) => e (b p.1 • X p.2) := by
    refine continuous_pi fun p => continuous_pi fun j => ?_
    have : Continuous fun X : α → β → S => b p.1 * X p.2 j := by fun_prop
    exact hb.comp this
  have ho := (isOpen_setOfPred_linearIndependent (𝕜 := K) (E := β → ι → K) (ι := ι × α)).preimage hc
  convert ho using 1
  ext X
  rw [Set.mem_ofPred_eq, linearIndependent_iff_smul_basis b]
  exact (e.toLinearMap.linearIndependent_iff e.ker).symm

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  intro F E _ _ _ _ _ σ _ n J _ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hr : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Fv F v) σ n J
  refine ⟨hr, e.isClosedEmbedding.locallyCompactSpace, e.isEmbedding.t2Space,
    e.secondCountableTopology, inferInstanceAs (IsTopologicalGroup (HR (Fv F v) σ J)), h1, h3, h2,
    fun a => ⟨?_, ?_⟩⟩
  · letI : NontriviallyNormedField (Fv F v) :=
      Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact isOpen_linearIndependent (K := Fv F v)
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))
  · have hm : Continuous fun g : HA (Fv F v) σ J => HA.mat (Fv F v) σ J g :=
      continuous_subtype_val
    have hv : Continuous fun g : HA (Fv F v) σ J =>
        ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := Units.continuous_val.comp hm
    refine continuous_pi fun b => ?_
    exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.LocalUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocks
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.BlockMeas

abbrev Yf (k r : ℕ) : Type := (NEntry.Idx k r → ℂ) × (UTr r → ℂ) × (Fin r → ℝ)

abbrev Ys (k r : ℕ) : Type :=
  ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ)) × ((UTr r → ℂ) × (Fin r → ℝ))

abbrev Zb (ι : Type) (k r : ℕ) : Type :=
  (UTr r → ι → ℂ) × (Fin r → ι → Fin (k + 1) → ℂ) × (UTr r → ι → ℂ) × (Fin r → ι → ℝ)

def sp (ι : Type) (k r : ℕ) (y : ι → Yf k r) : Zb ι k r :=
  (fun p w => (y w).1 (NEntry.idx k r (.inl p)), fun a w j => (y w).1 (NEntry.idx k r (.inr (a, j))),
    fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

def sq (ι : Type) (k r : ℕ) (y : ι → Ys k r) : Zb ι k r :=
  (fun p w => (y w).1.1 p, fun a w => (y w).1.2 a, fun p w => (y w).2.1 p, fun a w => (y w).2.2 a)

theorem sq_mp (ι : Type) [Fintype ι] (k r : ℕ) : MeasurePreserving (sq ι k r) volume volume := by
  have h1 := volume_measurePreserving_arrowProdEquivProdArrow ((UTr r → ℂ) × (Fin r → Fin (k + 1) → ℂ))
    ((UTr r → ℂ) × (Fin r → ℝ)) ι
  have h2 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → Fin (k + 1) → ℂ) ι
  have h3 := volume_measurePreserving_arrowProdEquivProdArrow (UTr r → ℂ) (Fin r → ℝ) ι
  have s1 : MeasurePreserving (fun (f : ι → UTr r → ℂ) (p : UTr r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℂ)
  have s2 : MeasurePreserving (fun (f : ι → Fin r → Fin (k + 1) → ℂ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure (Fin (k + 1) → ℂ))
  have s3 : MeasurePreserving (fun (f : ι → Fin r → ℝ) (p : Fin r) (i : ι) => f i p) volume volume :=
    ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u1 : SigmaFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t1 : SigmaFinite (volume : Measure (ι → UTr r → ℂ)) := inferInstance
  haveI t2 : SigmaFinite (volume : Measure (ι → Fin r → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  have a := s1.prod s2
  have b := s1.prod s3
  have c := (a.prod b).comp ((h2.prod h3).comp h1)
  exact (volume_preserving_prodAssoc).comp c

theorem pi_smul (ι : Type) [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (c : NNReal) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => ν) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • ν) := by
    have e : (c : ℝ≥0∞) • ν = c • ν := by
      ext s _
      simp [Measure.smul_apply]
    rw [e]
    infer_instance
  refine Measure.pi_eq fun s hs => ?_
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib, smul_eq_mul]

theorem mem_iff (ι : Type) (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)) (x : ι → Mt k r) :
    (∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β) ↔
      sp ι k r (fun w => nCoords k r (x w)) ∈
        Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG := by
  simp only [Sum.forall, Set.mem_prod, Set.mem_univ_pi]
  exact Iff.rfl

theorem measure_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  intro ι _ k r DU DH DC DG hU hH hC hG
  obtain ⟨⟨hσ, -, hnull, -⟩, -, -, hmap⟩ := _root_.GlobalTheory.SnMass.NEntry.haarLie_entries k r
  set μ := haarLie (Nset k r) 1 with hμ
  set e := r * (r - 1) + r * (k + 1) with he
  set F : (ι → Mt k r) → (ι → Yf k r) := fun x w => nCoords k r (x w) with hFdef
  set R : Set (Zb ι k r) := Set.univ.pi DU ×ˢ Set.univ.pi DH ×ˢ Set.univ.pi DC ×ˢ Set.univ.pi DG with hRdef
  have hF : Measurable F :=
    Measurable.of_eval fun w => NEntry.cont_nCoords.measurable.comp (measurable_pi_apply w)
  have hsp : Measurable (sp ι k r) := by
    unfold sp
    fun_prop
  have hR : MeasurableSet R :=
    (MeasurableSet.univ_pi hU).prod ((MeasurableSet.univ_pi hH).prod
      ((MeasurableSet.univ_pi hC).prod (MeasurableSet.univ_pi hG)))
  have hNm : MeasurableSet {x : Mt k r | Matrix.of x ∈ Nset k r} := by
    have : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := GlobalTheory.Amp.NLie.closed_N
    exact this.measurableSet
  have hNi : MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
        Set.univ.pi fun _ => {x : Mt k r | Matrix.of x ∈ Nset k r} := by
      ext x
      simp
    rw [this]
    exact MeasurableSet.univ_pi fun _ => hNm
  have hS : {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
      ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} =
      (sp ι k r ∘ F) ⁻¹' R ∩ {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
    rw [mem_iff]
    exact and_comm
  rw [hS]
  refine ⟨((hsp.comp hF) hR).inter hNi, ?_⟩
  have hconull : (Measure.pi fun _ : ι => μ) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
    have : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ ⊆
        ⋃ w, Function.eval w ⁻¹' {x : Mt k r | Matrix.of x ∉ Nset k r} := by
      intro x hx
      simpa using hx
    refine measure_mono_null this (measure_iUnion_null fun w => ?_)
    exact Measure.pi_eval_preimage_null _ hnull
  rw [measure_inter_conull hconull]
  have hc : ((2 : ℝ≥0∞) ^ e) = ((2 ^ e : NNReal) : ℝ≥0∞) := by
    push_cast
    rfl
  haveI : SigmaFinite (μ.map (nCoords k r)) := by
    rw [hmap, hc]
    have e' : ((2 ^ e : NNReal) : ℝ≥0∞) • (volume : Measure (Yf k r)) = (2 ^ e : NNReal) • volume := by
      ext s _
      simp [Measure.smul_apply]
    rw [e']
    infer_instance
  have hpi : (Measure.pi fun _ : ι => μ).map F = Measure.pi fun _ : ι => μ.map (nCoords k r) :=
    Measure.pi_map_pi (fun _ => NEntry.cont_nCoords.measurable.aemeasurable)
  have hpre : (sp ι k r ∘ F) ⁻¹' R = F ⁻¹' (sp ι k r ⁻¹' R) := rfl
  rw [hpre, ← Measure.map_apply hF (hsp hR), hpi, hmap, hc, pi_smul, Measure.smul_apply, smul_eq_mul]

  have hΦ : MeasurePreserving (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) volume volume :=
    volume_preserving_pi (f := fun _ : ι => Prod.map (NEntry.glue (k := k) (r := r)) id)
      fun _ => (NEntry.glue_mp (k := k) (r := r)).1.prod (MeasurePreserving.id _)
  have hcomp : (fun (y : ι → Ys k r) w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) ⁻¹' (sp ι k r ⁻¹' R) =
      sq ι k r ⁻¹' R := by
    ext y
    have : sp ι k r (fun w => ((NEntry.glue (y w).1, (y w).2) : Yf k r)) = sq ι k r y := by
      simp [sp, sq, NEntry.glue]
    simp only [Set.mem_preimage, this]
  have hvol : (Measure.pi fun _ : ι => (volume : Measure (Yf k r))) (sp ι k r ⁻¹' R) = volume R := by
    have h1 := hΦ.measure_preimage (hsp hR).nullMeasurableSet
    rw [hcomp, (sq_mp ι k r).measure_preimage hR.nullMeasurableSet] at h1
    exact h1.symm
  haveI u0 : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  haveI u2 : SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t3 : SigmaFinite (volume : Measure (UTr r → ι → ℂ)) := inferInstance
  haveI t4 : SigmaFinite (volume : Measure (Fin r → ι → Fin (k + 1) → ℂ)) := inferInstance
  haveI t5 : SigmaFinite (volume : Measure (Fin r → ι → ℝ)) := inferInstance
  have hpow : ((2 ^ e : NNReal) : ℝ≥0∞) ^ Fintype.card ι = (2 : ℝ≥0∞) ^ (Fintype.card ι * e) := by
    rw [← hc, ← pow_mul, mul_comm]
  rw [hvol, hRdef, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, volume_pi_pi, volume_pi_pi, volume_pi_pi, hpow]
  simp only [mul_assoc]

end GlobalTheory.SnMass.VolN.BlockMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TopFacts
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.ArchUnitaryTop

theorem top_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n a : ℕ) (J : Matrix (Fin n) (Fin n) E), ContinuousSMul (HA (Ainf F) σ J) (Fin a → Fin n → Ainf F ⊗[F] E) ∧ BorelSpace (Fin a → Fin n → Ainf F ⊗[F] E) ∧ SecondCountableTopology (Fin a → Fin n → Ainf F ⊗[F] E) ∧ T2Space (Fin a → Fin n → Ainf F ⊗[F] E) ∧ IsTopologicalGroup (HA (Ainf F) σ J) ∧ LocallyCompactSpace (HA (Ainf F) σ J) ∧ SecondCountableTopology (HA (Ainf F) σ J) ∧ T2Space (HA (Ainf F) σ J) := by
  intro F E _ _ _ _ _ σ n a J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field F
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (Ainf F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Ainf F) σ n J
  refine ⟨⟨?_⟩, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsTopologicalGroup (HR (Ainf F) σ J)), h1, h2, h3⟩
  have hm : Continuous fun g : HA (Ainf F) σ J => HA.mat (Ainf F) σ J g :=
    continuous_subtype_val
  have hv : Continuous fun g : HA (Ainf F) σ J =>
      ((HA.mat (Ainf F) σ J g : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := Units.continuous_val.comp hm
  refine continuous_pi fun b => ?_
  exact (hv.comp continuous_fst).matrix_mulVec ((continuous_apply b).comp continuous_snd)

end GlobalTheory.ArchUnitaryTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (_root_.GlobalTheory.SnMass.NEntry.haarLie_entries k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem record_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  intro D u
  refine ⟨(GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (D.T_mod_cond u)).1,
    D.nd.g_split, D.T_ne_g u, ?_, D.R.N_zero, ?_,
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D 0 (Nat.zero_le _)).ne_zero⟩
  · rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
    ring
  · let _ := D.host.cmStar
    have h := D.sp.baseGram_isHermitian
    refine Matrix.ext fun i j => ?_
    exact congrFun (congrFun h (Fin.cast D.R.N_zero i)) (Fin.cast D.R.N_zero j)

end GlobalTheory.St.G
end

