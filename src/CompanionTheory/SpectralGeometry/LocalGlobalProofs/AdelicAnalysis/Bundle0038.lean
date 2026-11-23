module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresIntegralFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuity
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LocFin

theorem null_of_fibres_null {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V}
    {ν : Measure X} {B : Set X} {fib : X → Measure V}
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) {W : Set V} (hW : MeasurableSet W)
    (h0 : ∀ b, fib b W = 0) : μ (W ∩ U) = 0 := by
  have key := h.2.1 (W.indicator 1) (measurable_one.indicator hW)
  simp only [lintegral_indicator_one hW, h0, lintegral_zero] at key
  rwa [Measure.restrict_apply hW] at key

theorem fibre_loc_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm S
  haveI : IsTopologicalRing R := hR.1
  haveI : LocallyCompactSpace R := hR.2.1
  haveI : SecondCountableTopology R := hR.2.2.1
  haveI : T2Space R := hR.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  obtain ⟨h1, h2, h3, h4, h5⟩ := HermTop.herm_top F E σ hσ R n
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨g, hgc, hg⟩ := h5 M J hJ
  have hKU := _root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hKU.isOpen_range.preimage hdet
  have hUeq : {X | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hg]
  have hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hUeq]
    exact hm
  obtain ⟨hloc, -, -, -⟩ := FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hgc hg _ hBo m hfib
  refine ⟨hloc S, ?_⟩
  rintro U hU ⟨X₀, hX₀U, hX₀S, hX₀⟩ h0
  obtain ⟨κ, -, -, -, hκ⟩ := _root_.GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous F E σ hσ M J hJ R hR n μ ν m hμ hν hm
  have hSdet : IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det := by
    rw [← hX₀S]
    exact hX₀
  obtain ⟨B₁, gs, hB₁, hSB₁, hgs, hgs1, hgsS⟩ := _root_.GlobalTheory.CompanionTheory.SW.exists_local_section F E σ hσ R hR n S hSdet
  obtain ⟨a1, a2, a3, -, -⟩ := GramAlg.gram_algebra F E σ hσ M J hJ R n
  have hgX₀ : g X₀ = S := Subtype.ext ((hg X₀).symm.trans hX₀S)
  have hr : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × Matrix (Fin n) (Fin n) (R ⊗[F] E) =>
      rmul R p.1 p.2 := by
    unfold rmul
    refine continuous_pi fun a => continuous_pi fun i => continuous_finsetSum _ fun c _ => ?_
    exact ((continuous_apply_apply c i).comp continuous_fst).mul (continuous_snd.matrix_elem c a)
  let T : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E) := fun X =>
    rmul R X (((gs (g X))⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hTc : ContinuousOn T (g ⁻¹' B₁) := by
    refine hr.comp_continuousOn (ContinuousOn.prodMk continuousOn_id ?_)
    exact Units.continuous_val.comp_continuousOn
      ((hgs.comp hgc.continuousOn fun X hX => hX).inv)
  have hU'o : IsOpen (g ⁻¹' B₁ ∩ T ⁻¹' U) := hTc.isOpen_inter_preimage (hB₁.preimage hgc) hU
  have hnull : ∀ S' : HermR R σ n, m S' (g ⁻¹' B₁ ∩ T ⁻¹' U) = 0 := by
    intro S'
    by_cases hS' : S' ∈ B₁
    · have e := hκ (gs S') S S' (hgsS S' hS')
      have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
        (hr.comp (Continuous.prodMk continuous_id continuous_const)).measurable
      rw [e, Measure.smul_apply, Measure.map_apply hmeas hU'o.measurableSet]
      have hsub : (fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U) ⊆
          U ∪ (gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det})ᶜ := by
        intro X hX
        by_cases hXf : X ∈ gramR R σ J ⁻¹' {Subtype.val S} ∩ {X | IsUnit (gramR R σ J X).det}
        · left
          have hXS : gramR R σ J X = S := hXf.1
          have hgr : g (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = S' := by
            apply Subtype.ext
            rw [← hg, a1, hXS, ← hgsS S' hS']
          have hT : T (rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) :
              Matrix (Fin n) (Fin n) (R ⊗[F] E))) = X := by
            simp only [T]
            rw [hgr, a2, Units.mul_inv, a3]
          have := hX.2
          simp only [Set.mem_preimage] at this
          rwa [hT] at this
        · exact Or.inr hXf
      have hz : m S ((fun X : Fin n → Fin M → R ⊗[F] E =>
          rmul R X ((gs S' : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ⁻¹'
            (g ⁻¹' B₁ ∩ T ⁻¹' U)) = 0 :=
        measure_mono_null hsub (measure_union_null h0 (hm.1 S))
      rw [hz, smul_zero]
    · refine measure_mono_null ?_ (hm.1 S')
      intro X hX hXf
      have hgX : g X = S' := Subtype.ext ((hg X).symm.trans hXf.1)
      exact hS' (hgX ▸ hX.1)
  have hμ0 := null_of_fibres_null hm hU'o.measurableSet hnull
  have hO : IsOpen ((g ⁻¹' B₁ ∩ T ⁻¹' U) ∩ {X | IsUnit (gramR R σ J X).det}) := by
    rw [hUeq]
    exact hU'o.inter (hBo.preimage hgc)
  refine hO.measure_ne_zero μ ⟨X₀, ⟨?_, ?_⟩, hX₀⟩ hμ0
  · show g X₀ ∈ B₁
    rw [hgX₀]
    exact hSB₁
  · show T X₀ ∈ U
    simp only [T]
    rw [hgX₀, hgs1, inv_one, Units.val_one, a3]
    exact hX₀U

end GlobalTheory.CompanionTheory.SW.LocFin
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneFiberMeasureBlockExtension
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem nnreal_eq_of_smul_haar {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  have h1 : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have h2 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC0).ne'
  have h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C := by
    have h' : (c • μ) C = (e • μ) C := by rw [h]
    rwa [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul] at h'
  have h4 := (ENNReal.mul_left_inj h2 h1).1 h3
  exact_mod_cast h4

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sclMat : R →* Matrix (Fin 1) (Fin 1) (R ⊗[F] E) where
  toFun u := Matrix.of fun _ _ => u ⊗ₜ[F] (1 : E)
  map_one' := by
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  map_mul' u v := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem sclMat_apply (u : R) (i j : Fin 1) :
    sclMat (F := F) (E := E) R u i j = u ⊗ₜ[F] (1 : E) := rfl

def unitTens : Rˣ →* (R ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E).toMonoidHom

theorem unitTens_coe (u : Rˣ) :
    ((unitTens (F := F) (E := E) R u : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (1 : E) := rfl

theorem rmul_sclMat {M : ℕ} (X : Fin 1 → Fin M → R ⊗[F] E) (u : R) :
    rmul R X (sclMat (F := F) (E := E) R u) = scl (u ⊗ₜ[F] (1 : E)) X := by
  funext a i
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp only [rmul, scl, Fin.sum_univ_one, sclMat_apply]

theorem cT_sclMat_mul (σ : E →ₐ[F] E) (u s : R) :
    ((hermScal R σ (u ^ 2 * s) : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) (sclMat (F := F) (E := E) R u) *
        ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        sclMat (F := F) (E := E) R u := by
  ext i j
  have h1 : sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by simp [sigR]
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, sclMat_apply, h1]
  change (u ^ 2 * s) ⊗ₜ[F] (1 : E) = u ⊗ₜ[F] (1 : E) * s ⊗ₜ[F] (1 : E) * u ⊗ₜ[F] (1 : E)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  ring

end Alg

theorem fibre_scale_modulus_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  intro F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁
  have hR0 := hR
  obtain ⟨i1, i2, i3, i4, -⟩ := hR0
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨k1, k2, k3, k4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  haveI := hK
  obtain ⟨κ, hκc, -, hκ1, hκ⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁
  have hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have h : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id
        continuous_const
    refine h.congr fun r => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcs : Continuous (sclMat (F := F) (E := E) R) :=
    continuous_pi fun _ => continuous_pi fun _ => hinc
  have hg : Continuous (Units.map (sclMat (F := F) (E := E) R)) := Continuous.units_map _ hcs
  have hu : Continuous (unitTens (F := F) (E := E) R) := Continuous.units_map _ hinc
  obtain ⟨χ, hχc, hχ⟩ := exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam)
    (R ⊗[F] E)ˣ
  let tU : (R ⊗[F] E)ˣ :=
    Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom
      (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))
  have htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t) := rfl
  have hq : ∀ u : Rˣ, ((unitTens (F := F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) =
      (u : R) ⊗ₜ[F] (algebraMap F E t) := by
    intro u
    rw [Units.val_mul, unitTens_coe, htU]
    change (u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u),
    fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_,
    hχc.comp (hu.mul continuous_const), ?_, ?_⟩
  · intro u
    have h := hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t))
      (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)
    rw [h]
    congr 2
    funext X
    exact rmul_sclMat R X (u : R)
  · intro u
    have e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        fun v => (unitTens (F := F) (E := E) R u * tU) • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, hq]
    rw [e]
    exact hχ _
  · intro c hc
    have e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, htU]
    rw [e, hχ tU] at hc
    have := nnreal_eq_of_smul_haar (coordK R b lam) hc
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

