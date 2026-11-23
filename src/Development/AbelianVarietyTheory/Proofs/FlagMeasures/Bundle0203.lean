module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamily
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.HomCovolumeFamily

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

theorem exists_twist {E : Type} [Field E] (φ : E →+* ℂ) :
    ∃ σ : ℂ ≃ₐ[ℝ] ℂ, (∀ x, ‖σ x‖ = ‖x‖) ∧ ∀ x, (InfinitePlace.mk φ).embedding x = σ (φ x) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun x => by rw [h]; rfl⟩
  · exact ⟨Complex.conjAe, fun x => by simp, fun x => by rw [h]; rfl⟩

theorem det_map_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) :
    (A.map σ).det = σ A.det := by
  have := RingHom.map_det (σ : ℂ →+* ℂ) A
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

theorem map_inv_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) (hA : A.det ≠ 0) :
    (A⁻¹).map σ = (A.map σ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

variable {E : Type} [Field E] [NumberField E]

theorem detNorm_twist {ι : Type} [Fintype ι] (e : ι ≃ InfinitePlace E) (σ : ι → ℂ ≃ₐ[ℝ] ℂ)
    (hσ : ∀ v x, ‖σ v x‖ = ‖x‖) {j : ℕ} (G : ι → Matrix (Fin j) (Fin j) ℂ) :
    detNorm E j (fun w => Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹) =
      (∏ v, ‖(G v).det‖ ^ 2)⁻¹ := by
  change ∏ w, ‖(Matrix.of (Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹)).det‖ ^ 2 = _
  rw [← Finset.prod_inv_distrib, ← e.prod_comp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
    inv_pow, det_map_twist, hσ]

theorem covAt_eq (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (g : MatInf E j) (hg : 0 < detNorm E j g) :
    covAt E j (latAt E j Λ g) = covStd j Λ / detNorm E j g := by
  obtain ⟨κ, -, h⟩ := (GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have h1 : detNorm E j (fun _ a b => if a = b then 1 else 0) = 1 := by
    have h2 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
    simp only [detNorm, h2, Matrix.det_one, norm_one, one_pow, Finset.prod_const_one]
  have h3 : covStd j Λ = κ := ((h _ (h1.symm ▸ one_pos)).2.1.trans (congrArg (κ / ·) h1)).trans (div_one κ)
  rw [(h g hg).2.1, h3]

theorem homCovolume_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  intro E _ _ hE ι _ φ hφ r s Λ Λ' hΛ hΛ' G G' hG hG' L hL
  let e : ι ≃ InfinitePlace E := Equiv.ofBijective _ hφ
  choose σ hσ hσφ using fun v => exists_twist (φ v)
  have he : ∀ v x, (e v).embedding x = σ v (φ v x) := hσφ
  let Φ : (ι → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ) :=
    { toFun := fun z w i k => σ (e.symm w) (z (e.symm w) i k)
      invFun := fun y v i k => (σ v).symm (y (e v) i k)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun c z => funext fun w => funext fun i => funext fun k =>
        (σ (e.symm w)).toLinearEquiv.map_smul c (z (e.symm w) i k)
      left_inv := fun _ => by ext; simp
      right_inv := fun _ => by ext; simp }
  have hΦ : ∀ z v i k, Φ z (e v) i k = σ v (z v i k) := fun z v i k => by
    change σ (e.symm (e v)) (z (e.symm (e v)) i k) = _
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Φ.toContinuousLinearEquiv volume volume := by
    refine GlobalTheory.HomCovolume.measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      change (∀ w i k, ‖Φ x w i k‖ ≤ 1) ↔ _
      rw [e.forall_congr_right.symm]
      simp only [hΦ, hσ]
    · simp [volume_pi_closedBall _ zero_le_one, Fintype.card_congr e]
  have hD : 0 < ∏ v, ‖(G v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG v)) _
  have hD' : 0 < ∏ v, ‖(G' v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG' v)) _
  have hn := detNorm_twist e σ hσ G
  have hn' := detNorm_twist e σ hσ G'
  have hp := hn ▸ inv_pos.2 hD
  have hp' := hn' ▸ inv_pos.2 hD'
  let L' : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ) :=
    L.comap (Φ.symm.toLinearMap.restrictScalars ℤ)
  have hLL : ∀ z, z ∈ L ↔ Φ z ∈ L' := fun z => by
    change _ ↔ Φ.symm (Φ z) ∈ L
    rw [Φ.symm_apply_apply]
  have hmain := GlobalTheory.HomCovolume.homCovolume E hE r s Λ Λ' hΛ hΛ' _ _ hp hp' L' (fun y => by
    obtain ⟨z, rfl⟩ := Φ.surjective y
    rw [← hLL, hL]
    refine exists_congr fun T => and_congr Iff.rfl ?_
    rw [← e.forall_congr_right]
    refine forall_congr' fun v => ?_
    have h1 : Matrix.of (Φ z (e v)) = (Matrix.of (z v)).map (σ v) := by
      ext i k; exact hΦ z v i k
    have h2 : T.map (e v).embedding = (T.map (φ v)).map (σ v) := by
      ext i k; exact he v _
    have h3 : IsUnit ((G v).map (σ v)).det := by
      rw [det_map_twist]; exact ((map_ne_zero _).2 (hG v)).isUnit
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply, h1, h2,
      Matrix.nonsing_inv_nonsing_inv _ h3, ← map_inv_twist _ _ (hG' v), ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (σ v).injective).eq_iff.symm)
  rw [covAt_eq hE Λ hΛ _ hp, covAt_eq hE Λ' hΛ' _ hp', hn, hn', div_inv_eq_mul, div_inv_eq_mul] at hmain
  exact GlobalTheory.HomCovolume.HasCov.of_measurePreserving Φ.toContinuousLinearEquiv hmp hLL hmain

end GlobalTheory.HomCovolumeFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteGLHaarMeasureEqPiLocal
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarPi

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hrw : ∀ z : E × (Fin n → E),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm z i) =
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [hrw]
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i))
      (hf 0).aemeasurable, ih (fun i => f i.succ) (fun i => hf i.succ),
      Fin.prod_univ_succ]
    · exact (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hrw : ∀ y : Fin (Fintype.card ι) → E,
      ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k) := by
    intro y
    rw [← e.prod_comp]
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hrw]
  rw [lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]
  exact e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

theorem haarGL_eq_pi : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  intro E _ _ j
  set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)
  have hF : Measurable F := by
    have hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := continuous_id.matrix_det
    exact ENNReal.measurable_ofReal.comp
      (((hc.norm.pow 2).measurable.inv).pow_const j)
  have : SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F) :=
    inferInstanceAs (SigmaFinite (haarLoc j))
  have hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F := rfl
  simp only [hloc]
  rw [pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]
  congr 1
  unfold MatInf at x
  unfold detNorm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]

end GlobalTheory.HaarPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open GlobalTheory.LatFacts Module

noncomputable section

namespace GlobalTheory.CovProd

variable (E : Type) [Field E] [NumberField E] (k : ℕ)

def splitVec : (VecInf E 1 × VecInf E k) ≃ₗ[ℝ] VecInf E (k + 1) where
  toFun p w := Fin.cons (p.1 w 0) (p.2 w)
  invFun x := (fun w _ => x w 0, fun w => Fin.tail (x w))
  map_add' p q := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  map_smul' c p := by
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext w a
      rw [Subsingleton.elim a 0]
      simp
    · funext w
      simp
  right_inv x := by
    funext w
    simp

theorem mem_fd_prod {ι κ : Type} [Fintype ι] [Fintype κ] (b : Basis ι ℝ (VecInf E 1)) (c : Basis κ ℝ (VecInf E k))
    (x : VecInf E (k + 1)) :
    x ∈ ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) ↔
      ((splitVec E k).symm x).1 ∈ ZSpan.fundamentalDomain b ∧
        ((splitVec E k).symm x).2 ∈ ZSpan.fundamentalDomain c := by
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_eq_preimage_symm, Set.mem_preimage,
    ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, ZSpan.mem_fundamentalDomain, Sum.forall]
  simp only [Basis.prod_repr_inl, Basis.prod_repr_inr]

private theorem measurePreserving_splitVec_symm :
    MeasurePreserving (fun x : VecInf E (k + 1) => (splitVec E k).symm x) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : InfinitePlace E → Fin (k + 1) → ℂ) w =>
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) 0 (x w))
      (Measure.pi fun _ => Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => (volume : Measure ℂ).prod (Measure.pi fun _ : Fin k => (volume : Measure ℂ))) :=
    measurePreserving_pi _ _ fun _ => measurePreserving_piFinSuccAbove (fun _ => volume) 0
  have h2 := measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (InfinitePlace E)
    (fun _ => (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin k => (volume : Measure ℂ))
  have h3 : MeasurePreserving
      (fun (y : InfinitePlace E → ℂ) w => (MeasurableEquiv.funUnique (Fin 1) ℂ).symm (y w))
      (Measure.pi fun _ => (volume : Measure ℂ))
      (Measure.pi fun _ => Measure.pi fun _ : Fin 1 => (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun _ =>
      MeasurePreserving.symm _ (measurePreserving_funUnique (volume : Measure ℂ) (Fin 1))
  have h4 := (h3.prod (MeasurePreserving.id
    (Measure.pi fun _ : InfinitePlace E => Measure.pi fun _ : Fin k => (volume : Measure ℂ)))).comp (h2.comp h1)
  convert h4 using 1
  all_goals rfl

theorem covAt_prod (b : Basis (Idx E 1) ℝ (VecInf E 1)) (c : Basis (Idx E k) ℝ (VecInf E k)) :
    covAt E (k + 1) (Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k)))) =
      covAt E 1 (Submodule.span ℤ (Set.range b)) * covAt E k (Submodule.span ℤ (Set.range c)) := by
  rw [covAt_span, covAt_span, covAt_span]
  have hs : ZSpan.fundamentalDomain ((b.prod c).map (splitVec E k)) =
      (fun x => (splitVec E k).symm x) ⁻¹' (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) := by
    ext x
    rw [mem_fd_prod]
    rfl
  have hm : MeasurableSet (ZSpan.fundamentalDomain b ×ˢ ZSpan.fundamentalDomain c) :=
    (ZSpan.fundamentalDomain_measurableSet b).prod (ZSpan.fundamentalDomain_measurableSet c)
  rw [hs, measureReal_def, (measurePreserving_splitVec_symm E k).measure_preimage hm.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, measureReal_def, measureReal_def]

theorem latAt_oneInf (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) :
    latAt E j Λ (oneInf E j) = Submodule.span ℤ (emb E j '' (Λ : Set (Fin j → E))) := by
  simp only [latAt, of_oneInf, inv_one, one_mulVec]
  rfl

theorem span_prod {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module ℝ M] [Module ℝ N] {ι κ : Type}
    (b : Basis ι ℝ M) (c : Basis κ ℝ N) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inl_fst]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [Basis.prod_apply_inl_snd]
        exact zero_mem _
    · refine Submodule.mem_prod.2 ⟨?_, ?_⟩
      · rw [Basis.prod_apply_inr_fst]
        exact zero_mem _
      · rw [Basis.prod_apply_inr_snd]
        exact Submodule.subset_span ⟨i, rfl⟩
  · rintro ⟨x, y⟩ hxy
    rw [Submodule.mem_prod] at hxy
    have hx : Submodule.span ℤ (Set.range b) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inl ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inl_fst b c i) (Basis.prod_apply_inl_snd b c i)
    have hy : Submodule.span ℤ (Set.range c) ≤
        (Submodule.span ℤ (Set.range (b.prod c))).comap (LinearMap.inr ℤ M N) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr i, ?_⟩
      exact Prod.ext (Basis.prod_apply_inr_fst b c i) (Basis.prod_apply_inr_snd b c i)
    have h := add_mem (Submodule.mem_comap.1 (hx hxy.1)) (Submodule.mem_comap.1 (hy hxy.2))
    simpa using h

theorem covAt_latAt_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) := by
  intro E _ _ hE k Λ Λ₀ Λ' h₀ h' hΛ
  rw [latAt_oneInf, latAt_oneInf, latAt_oneInf]
  obtain ⟨b, hb⟩ := exists_basis E 1 Λ₀ h₀
  obtain ⟨c, hc⟩ := exists_basis E k Λ' h'

  set s : (VecInf E 1 × VecInf E k) →ₗ[ℤ] VecInf E (k + 1) :=
    (splitVec E k).toLinearMap.restrictScalars ℤ with hs
  have hsv : ∀ p, s p = splitVec E k p := fun p => rfl

  have hemb : ∀ y : Fin (k + 1) → E,
      emb E (k + 1) y = s (emb E 1 (fun _ => y 0), emb E k (Fin.tail y)) := by
    intro y
    rw [hsv]
    funext w a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · simp [splitVec, emb, Fin.tail]
  have key : Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E))) =
      Submodule.span ℤ (Set.range ((b.prod c).map (splitVec E k))) := by
    have hr : Set.range ((b.prod c).map (splitVec E k)) = s '' Set.range (b.prod c) := by
      rw [Basis.coe_map, Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, span_prod, ← hb, ← hc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have hy' := (hΛ y).1 hy
      refine Submodule.mem_map.2 ⟨(emb E 1 (fun _ => y 0), emb E k (Fin.tail y)),
        Submodule.mem_prod.2 ⟨Submodule.subset_span ⟨_, hy'.1, rfl⟩,
          Submodule.subset_span ⟨_, hy'.2, rfl⟩⟩, (hemb y).symm⟩
    · rw [Submodule.map_le_iff_le_comap]
      rintro ⟨u, v⟩ huv
      rw [Submodule.mem_prod] at huv
      have hu : Submodule.span ℤ (emb E 1 '' (Λ₀ : Set (Fin 1 → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inl ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hz0 : (fun _ : Fin 1 => z 0) = z := by
          funext i
          rw [Subsingleton.elim i 0]
        have hmem : (Fin.cons (z 0) (0 : Fin k → E) : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · simpa only [Fin.cons_zero] using hz0 ▸ hz
          · simpa only [Fin.tail_cons] using zero_mem Λ'
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons, map_zero]
        simp only [Fin.cons_zero, hz0, LinearMap.comp_apply, LinearMap.inl_apply]
      have hv : Submodule.span ℤ (emb E k '' (Λ' : Set (Fin k → E))) ≤
          (Submodule.span ℤ (emb E (k + 1) '' (Λ : Set (Fin (k + 1) → E)))).comap
            (s.comp (LinearMap.inr ℤ _ _)) := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        have hmem : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
          refine (hΛ _).2 ⟨?_, ?_⟩
          · convert zero_mem Λ₀ using 1
            funext i
            simp
          · rw [Fin.tail_cons]
            exact hz
        refine Submodule.subset_span ⟨_, hmem, ?_⟩
        rw [hemb, Fin.tail_cons]
        simp only [Fin.cons_zero, LinearMap.comp_apply, LinearMap.inr_apply]
        congr 2
        exact map_zero (emb E 1)
      have h := add_mem (Submodule.mem_comap.1 (hu huv.1)) (Submodule.mem_comap.1 (hv huv.2))
      rw [Submodule.mem_comap]
      simpa [← map_add (f := _)] using h
  rw [key, hb, hc]
  exact covAt_prod E k b c

end GlobalTheory.CovProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselFubiniIntegrandProd
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.SgInf

theorem prod_integrand_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hF := _root_.GlobalTheory.SgInf.fubini_bound k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv v hv
  obtain ⟨hz, hT, hπ, hHaarS, _⟩ := hSide
  have : SigmaFinite μS := hHaarS.1
  have : SigmaFinite μG := hStd.2.2.2.2.1.1
  obtain ⟨-, -, hPiB, hPiC, -⟩ := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ
  have hS : IsClosedSub k r (Sset k r z) := (closedSub_groups k r z hz hT).2.2.2.1

  set T : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ Sset k r z} with hTdef
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hTm : MeasurableSet T := (hS.2.1.preimage hof).measurableSet
  have haeT : ∀ᵐ x ∂μS, x ∈ T := ae_iff.2 hHaarS.2.2.1

  have hinv : ContinuousOn (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T := by
    intro x hx
    have hg : (Matrix.of x : Mat k r)ᴴ * Hpk k r * (Matrix.of x : Mat k r) = Hpk k r := hS.1 hx
    have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
    have hdet : IsUnit (Matrix.of x : Mat k r).det := by
      rw [isUnit_iff_ne_zero]
      intro h0
      have h1 := congrArg Matrix.det hg
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
      exact hH.ne_zero h1.symm
    have hc : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact ((continuousAt_matrix_inv _ hc).comp hof.continuousAt).continuousWithinAt
  have hmaps : Set.MapsTo (fun x : Mt k r => (Matrix.of x : Mat k r)⁻¹) T (Sset k r z) :=
    fun x hx => hS.2.2.2.2 _ hx
  have hgc : ContinuousOn
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) T :=
    ((hPiC.comp hinv hmaps).clm_apply continuousOn_const).inner continuousOn_const
  have hgm : AEStronglyMeasurable
      (fun x : Mt k r => ⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ) μS := by
    have h1 := hgc.aestronglyMeasurable (μ := μS) hTm
    rwa [Measure.restrict_eq_self_of_ae_mem haeT] at h1

  have hbd : ∀ x ∈ T,
      ‖⟪PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ, ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖ξ‖ := by
    intro x hx
    have h1 := (hPiB _ (hmaps hx)).1
    calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹ ξ‖ * ‖ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * ‖ξ‖ := by
        gcongr
        calc _ ≤ ‖PiS (psiGen k r z c) π (Matrix.of x : Mat k r)⁻¹‖ * ‖ξ‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖ξ‖ := by gcongr
          _ = ‖ξ‖ := one_mul _
  have haeP : ∀ᵐ p ∂(μG.prod μS), p.2 ∈ T := by
    rw [ae_iff]
    have h1 : {p : Mt k r × Mt k r | ¬ p.2 ∈ T} = Set.univ ×ˢ {x | ¬ x ∈ T} := by
      ext p; simp
    rw [h1, Measure.prod_prod, ae_iff.1 haeT, mul_zero]
  refine hF.mul_bdd (c := ‖ξ‖ * ‖ξ‖)
    (hgm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd) ?_
  filter_upwards [haeP] with p hp
  exact hbd p.2 hp

end GlobalTheory.SgInf
end
end

