module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle0006
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExp
section
noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HExp

variable {n : ℕ}

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem haar_exp_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    ∃ d : ℝ, 0 < d ∧ DensOn (fun S => μ (expSet S)) d := by
  letI mV : MeasurableSpace (gV ε) := borel _
  haveI : BorelSpace (gV ε) := ⟨rfl⟩
  let eC : GCo ε ≃L[ℝ] gV ε := (gE ε).toContinuousLinearEquiv
  let lam : Measure (gV ε) := Measure.map eC volume
  haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hlamH : lam.IsAddHaarMeasure := eC.isAddHaarMeasure_map volume
  obtain ⟨c, hc0, hct, hup, hdown⟩ := (ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _
    inferInstance inferInstance μ inferInstance lam (by exact hlamH)
  have himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S := by
    intro S
    ext g
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
      exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨eC s, ⟨s, hs, rfl⟩, h⟩
  have hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S) := fun S hS =>
    eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S := by
    intro S hS
    rw [Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]
  have hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') →
      eC '' S ⊆ ball (0 : gV ε) δ := by
    intro δ hδ
    obtain ⟨δ', hδ', h⟩ := Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ
    refine ⟨δ', hδ', fun S hS => ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h (x := s) (by simpa using hS s hs)
    simpa using this
  set d := c.toReal with hd
  have hdpos : 0 < d := ENNReal.toReal_pos hc0 hct
  have hc : c = ENNReal.ofReal d := (ENNReal.ofReal_toReal hct).symm
  refine ⟨d, hdpos, fun η hη => ?_⟩
  have hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
    obtain ⟨δ, hδ, h⟩ := hup (Real.toNNReal ((1 + η) * d)) (by
      rw [hc]
      show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith)
    obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
    refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
    have := h (eC '' S) (hmeas S hS) (h' S hSδ)
    rw [himg, hlam S hS] at this
    exact this
  have hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S) := by
    by_cases hη1 : (1 - η) * d ≤ 0
    · refine ⟨1, one_pos, fun S _ _ => ?_⟩
      rw [ENNReal.ofReal_of_nonpos hη1, zero_mul]
      exact bot_le
    · have hη1' : 0 < (1 - η) * d := not_le.mp hη1
      obtain ⟨δ, hδ, h⟩ := hdown (Real.toNNReal ((1 - η) * d)) (by
        rw [hc]
        show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d
        rw [ENNReal.ofReal_lt_ofReal_iff hdpos]
        nlinarith)
      obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
      refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
      have := h (eC '' S) (hmeas S hS) (h' S hSδ)
      rw [himg, hlam S hS] at this
      exact this
  obtain ⟨δ1, hδ1, h1⟩ := hU
  obtain ⟨δ2, hδ2, h2⟩ := hL
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩
  · exact h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)
  · exact h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)

end Normed

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaPQ
section
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

variable {P Q : ℕ}

def gToLieMat (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool} (s : GCo ε) :
    Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  Matrix.reindex e.symm e.symm (gMat s)

theorem gToLieMat_mem (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    gToLieMat e s ∈ Formalism.BasicNotions.lieU P Q :=
  (OmegaPQAux.mem_reindex_iff e he1 he2 (gMat s)).2 (OmegaPQAux.gMat_mem s)

def gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) (s : GCo ε) :
    Formalism.BasicNotions.lieU P Q :=
  ⟨gToLieMat e s, gToLieMat_mem e he1 he2 s⟩

namespace OmegaPQAux

def gToLieL (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    GCo ε →ₗ[ℝ] Formalism.BasicNotions.lieU P Q where
  toFun := gToLie e he1 he2
  map_add' s t := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_add]
  map_smul' c s := by
    apply Subtype.ext
    ext i j
    simp [gToLie, gToLieMat, gMat_smul]

theorem gToLieL_bij (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Function.Bijective (gToLieL e he1 he2) := by
  have hre : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
    intro M; rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
  constructor
  · intro s t h
    have h2 := congrArg (fun X : Formalism.BasicNotions.lieU P Q =>
      Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) h
    simp only [gToLieL, LinearMap.coe_mk, AddHom.coe_mk, gToLie, gToLieMat, hre] at h2
    rw [← coordOf_gMat s, ← coordOf_gMat t, h2]
  · intro X
    set Y := Matrix.reindex e e (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) with hYdef
    have hX : Matrix.reindex e.symm e.symm Y = X := by
      rw [hYdef, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    have hY := (mem_reindex_iff e he1 he2 Y).1 (by rw [hX]; exact X.2)
    refine ⟨coordOf Y, Subtype.ext ?_⟩
    change Matrix.reindex e.symm e.symm (gMat (coordOf (ε := ε) Y)) = X
    rw [gMat_coordOf Y hY, hX]

end OmegaPQAux

theorem isOmegaLeb_gToLie (e : Fin P ⊕ Fin Q ≃ Fin n) {ε : Fin n → Bool}
    (he1 : ∀ i, ε (e (Sum.inl i)) = true) (he2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.IsOmegaLeb (ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) • Measure.map (gToLie e he1 he2) volume) := by
  have : BorelSpace (Formalism.BasicNotions.lieU P Q) := ⟨rfl⟩
  set Lin := LinearEquiv.ofBijective _ (OmegaPQAux.gToLieL_bij e he1 he2) with hLin
  set CL := Lin.toContinuousLinearEquiv with hCL
  have hcoe : (CL : GCo ε → Formalism.BasicNotions.lieU P Q) = gToLie e he1 he2 := rfl
  have hG : Measurable (gToLie e he1 he2) := by rw [← hcoe]; exact CL.continuous.measurable
  constructor
  · have hd : (volume : Measure (Fin n → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hk : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hp : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hK : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have hGv : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    have h1 := ContinuousLinearEquiv.isAddHaarMeasure_map CL (volume : Measure (GCo ε))
    rw [hcoe] at h1
    exact Measure.IsAddHaarMeasure.smul _ (by simp) ENNReal.ofReal_ne_top
  · have hSF : SigmaFinite (volume : Measure (GCo ε)) := Measure.prod.instSigmaFinite
    set c := ENNReal.ofReal (2 ^ (n * (n - 1) / 2)) with hc
    set E : Fin n × Fin n ≃ (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) := (e.prodCongr e).symm with hE
    set R := MeasurableEquiv.piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E
    have hGl : Measurable (OmegaPQAux.Gl ε) :=
      (LinearMap.continuous_of_finiteDimensional (OmegaPQAux.Gl ε)).measurable
    have hPm : Measurable (OmegaPQAux.pairMap ε) := by
      rw [OmegaPQAux.pairMap_eq]
      exact (OmegaPQAux.mp_Amap ε).measurable.comp (hGl.comp (OmegaPQAux.mp_Fmap ε).measurable)
    have hcomp : (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) ∘
          Prod.map (gToLie e he1 he2) (gToLie e he1 he2) = R ∘ OmegaPQAux.pairMap ε := by
      funext st ij
      obtain ⟨i, j⟩ := ij
      have hij : ((i, j) : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)) = E (e i, e j) := by simp [hE]
      conv_rhs => rw [hij]
      simp only [Function.comp_apply, R, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply_apply]
      simp [Formalism.BasicNotions.entries, gToLie, gToLieMat, OmegaPQAux.pairMap, Matrix.reindex_apply]
    have hval : ∀ i j, Measurable (fun X : Formalism.BasicNotions.lieU P Q =>
        (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j) := fun i j =>
      (continuous_subtype_val.matrix_elem i j).measurable
    have hFm : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
        Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
          Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
      refine Measurable.of_eval fun ij => ?_
      have h1 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_fst
      have h2 : Measurable (fun ab : Formalism.BasicNotions.lieU P Q × Formalism.BasicNotions.lieU P Q =>
          (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
        (hval ij.1 ij.2).comp measurable_snd
      exact h1.add (measurable_const.mul h2)
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul _ hFm.aemeasurable,
      Measure.map_prod_map _ _ hG hG, Measure.map_map hFm (hG.prodMap hG), hcomp,
      ← Measure.map_map R.measurable hPm, ← Measure.volume_eq_prod, OmegaPQAux.map_pairMap,
      Measure.map_smul _ R.measurable.aemeasurable,
      (volume_measurePreserving_piCongrLeft (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) E).map_eq,
      smul_smul, hc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow]
    norm_num

end ReciprocityTheory.ChartRestriction.DS
end
end

