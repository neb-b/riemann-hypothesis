module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiCoord
section
noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

theorem measurePreserving_piCurry_symm {V : Type} [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    {X : ∀ v, α v → Type} [∀ v a, MeasurableSpace (X v a)] (μ : ∀ v a, Measure (X v a))
    [∀ v a, SigmaFinite (μ v a)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm (Measure.pi fun v => Measure.pi fun a => μ v a)
      (Measure.pi fun p : Σ v, α v => μ p.1 p.2) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun v => Set.univ.pi fun a => s ⟨v, a⟩ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    exact Iff.rfl
  rw [e, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

theorem measurePreserving_of_normSq {ι V : Type} [Fintype ι] [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v))) (hbij : Function.Bijective T)
    (hn : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) :
    MeasurePreserving T volume (Measure.pi fun _ => volume) := by

  let F : (∀ v, EuclideanSpace ℝ (α v)) →ₗ[ℝ] EuclideanSpace ℝ (Σ v, α v) :=
    { toFun := fun z => WithLp.toLp 2 (fun p : Σ v, α v => z p.1 p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hFn : ∀ z, ‖F z‖ ^ 2 = ∑ v, ‖z v‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hF : MeasurePreserving F (Measure.pi fun v => volume) volume := by
    have h1 := measurePreserving_pi (fun v => (volume : Measure (EuclideanSpace ℝ (α v))))
      (fun v => (volume : Measure (α v → ℝ)))
      (fun v => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (α v))
    have h2 := measurePreserving_piCurry_symm (X := fun v (_ : α v) => ℝ) (fun _ _ => (volume : Measure ℝ))
    have h3 := PiLp.volume_preserving_toLp (Σ v, α v)
    simp only [← MeasureTheory.volume_pi] at h2
    exact (h3.comp (h2.comp h1))
  have hGn : ∀ x, ‖F (T x)‖ = ‖x‖ := by
    intro x
    have := hFn (T x)
    rw [hn x] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  let G : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Σ v, α v) := ⟨F ∘ₗ T, hGn⟩
  have hFi : Function.Injective F := by
    intro z z' h
    funext v
    ext a
    have := congrArg (fun w : EuclideanSpace ℝ (Σ v, α v) => w ⟨v, a⟩) h
    exact this
  have hFs : Function.Surjective F := by
    intro w
    exact ⟨fun v => WithLp.toLp 2 (fun a => w ⟨v, a⟩), rfl⟩
  have hGs : Function.Surjective G := (hFs.comp hbij.2)
  let Ge := LinearIsometryEquiv.ofSurjective G hGs
  have hGe : MeasurePreserving Ge volume volume := Ge.measurePreserving
  let Fe : (∀ v, EuclideanSpace ℝ (α v)) ≃ᵐ EuclideanSpace ℝ (Σ v, α v) :=
    { toEquiv := Equiv.ofBijective F ⟨hFi, hFs⟩
      measurable_toFun := hF.measurable
      measurable_invFun := by
        have : ⇑(Equiv.ofBijective F ⟨hFi, hFs⟩).symm =
            fun (w : EuclideanSpace ℝ (Σ v, α v)) (v : V) => (WithLp.toLp 2 (fun a => w ⟨v, a⟩) : EuclideanSpace ℝ (α v)) := by
          funext w
          apply (Equiv.ofBijective F ⟨hFi, hFs⟩).injective
          rw [Equiv.apply_symm_apply]
          rfl
        rw [this]
        exact Measurable.of_eval fun v =>
          (PiLp.volume_preserving_toLp (α v)).measurable.comp
            (Measurable.of_eval fun a => (measurable_pi_apply _).comp (PiLp.volume_preserving_ofLp _).measurable) }
  have hFe : MeasurePreserving Fe (Measure.pi fun v => volume) volume := hF
  have key := hFe.symm.comp hGe
  convert key using 1
  funext x
  show T x = Fe.symm (F (T x))
  exact (Fe.symm_apply_apply (T x)).symm

def piProdEquiv {V : Type} (A B : V → Type) [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSpace (B v)] :
    (∀ v, A v × B v) ≃ᵐ (∀ v, A v) × (∀ v, B v) where
  toFun z := (fun v => (z v).1, fun v => (z v).2)
  invFun p v := (p.1 v, p.2 v)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (Measurable.of_eval fun v => measurable_fst.comp (measurable_pi_apply v)).prodMk
    (Measurable.of_eval fun v => measurable_snd.comp (measurable_pi_apply v))
  measurable_invFun := Measurable.of_eval fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk ((measurable_pi_apply v).comp measurable_snd)

theorem measurePreserving_piProdEquiv {V : Type} [Fintype V] (A B : V → Type) [∀ v, MeasurableSpace (A v)]
    [∀ v, MeasurableSpace (B v)] (μ : ∀ v, Measure (A v)) (ν : ∀ v, Measure (B v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] :
    MeasurePreserving (piProdEquiv A B) (Measure.pi fun v => (μ v).prod (ν v))
      ((Measure.pi fun v => μ v).prod (Measure.pi fun v => ν v)) := by
  refine ⟨(piProdEquiv A B).measurable, ?_⟩
  refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
    (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
    · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
  · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
    rw [MeasurableEquiv.map_apply]
    rw [show (piProdEquiv A B) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        (Set.univ.pi fun i ↦ s i ×ˢ t i) by
        ext; simp [Set.mem_pi, forall_and, piProdEquiv]]
    simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end PI.AprimeInfG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens
section
noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [Measure.pi_of_empty]
  | succ n ih =>
    have hmp := measurePreserving_piFinSuccAbove μ 0
    have hg : Measurable fun y : (j : Fin n) → E (Fin.succAbove 0 j) =>
        ∏ j, f (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
    calc ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : (i : Fin (n + 1)) → E i,
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
            (MeasurableEquiv.piFinSuccAbove E 0 x) ∂(Measure.pi μ) := by
          congr 1
          funext x
          rw [Fin.prod_univ_succ]
          (try simp only [Fin.succAbove_zero]) <;> rfl
      _ = ∫⁻ z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j)
            ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
          hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
            (fun z : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)) =>
              f 0 z.1 * ∏ j, f (Fin.succAbove 0 j) (z.2 j))
      _ = (∫⁻ a, f 0 a ∂μ 0) *
            ∫⁻ y, ∏ j, f (Fin.succAbove 0 j) (y j) ∂(Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
          lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
          rw [ih (fun j => f (Fin.succAbove 0 j)) (fun j => hf _), Fin.prod_univ_succ]
          simp [Fin.succAbove_zero]

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  have h1 : ∀ y : (i' : Fin (Fintype.card ι)) → E (e i'),
      ∏ i, f i ((MeasurableEquiv.piCongrLeft E e) y i) = ∏ i', f (e i') (y i') := by
    intro y
    exact (Fintype.prod_equiv e (fun i' => f (e i') (y i')) _
      (fun i' => by simp [MeasurableEquiv.piCongrLeft_apply_apply])).symm
  simp_rw [h1]
  rw [lintegral_fin_prod (fun i' => f (e i')) (fun i' => hf (e i'))]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem withDensity_pi {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (lam : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (lam i)] (D : (i : ι) → E i → ℝ)
    (hD : ∀ i, Measurable (D i)) :
    (Measure.pi lam).withDensity (fun z => ∏ i, ENNReal.ofReal (D i (z i))) =
      Measure.pi (fun i => (lam i).withDensity (fun x => ENNReal.ofReal (D i x))) := by
  classical
  haveI : ∀ i, SigmaFinite ((lam i).withDensity fun x => ENNReal.ofReal (D i x)) :=
    fun i => SigmaFinite.withDensity_ofReal (D i)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h1 : (univ.pi s).indicator (fun z : (i : ι) → E i => ∏ i, ENNReal.ofReal (D i (z i))) =
      fun z => ∏ i, (s i).indicator (fun x => ENNReal.ofReal (D i x)) (z i) := by
    funext z
    by_cases hz : z ∈ univ.pi s
    · rw [indicator_of_mem hz]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hz i (mem_univ i)) (fun x => ENNReal.ofReal (D i x))).symm
    · simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      have hz' : z ∉ univ.pi s := fun h => hi (h i (mem_univ i))
      rw [indicator_apply, if_neg hz']
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_apply, if_neg hi])).symm
  rw [h1, lintegral_fintype_prod (fun i => (s i).indicator (fun x => ENNReal.ofReal (D i x))) (fun i => (ENNReal.measurable_ofReal.comp (hD i)).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

theorem pi_chart_dens {V : Type} [Fintype V] {X E : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (E v)] (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)]
    (lam : ∀ v, Measure (E v)) [∀ v, SigmaFinite (lam v)]
    (Φ : ∀ v, E v → X v) (hΦm : ∀ v, Measurable (Φ v)) (U : ∀ v, Set (E v)) (hU : ∀ v, MeasurableSet (U v))
    (hinj : ∀ v, InjOn (Φ v) (U v))
    (D : ∀ v, E v → ℝ) (hD : ∀ v, Measurable (D v))
    (h : ∀ v, ∀ A ⊆ U v, MeasurableSet A → μ v (Φ v '' A) = ∫⁻ z in A, ENNReal.ofReal (D v z) ∂lam v)
    (A : Set (∀ v, E v)) (hAU : A ⊆ univ.pi U) (hA : MeasurableSet A)
    (hAi : MeasurableSet ((fun z v => Φ v (z v)) '' A)) :
    Measure.pi μ ((fun z v => Φ v (z v)) '' A) =
      ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
  classical
  set Ψ : (∀ v, E v) → (∀ v, X v) := fun z v => Φ v (z v) with hΨ
  have hΨm : Measurable Ψ := Measurable.of_eval fun v => (hΦm v).comp (measurable_pi_apply v)
  let S : ∀ v, Set (X v) := fun v => Φ v '' U v
  let ν : ∀ v, Measure (E v) := fun v => (lam v).withDensity fun x => ENNReal.ofReal (D v x)
  haveI : ∀ v, SigmaFinite (ν v) := fun v => SigmaFinite.withDensity_ofReal (D v)
  have hκ : ∀ v, ((ν v).restrict (U v)).map (Φ v) = (μ v).restrict (S v) := by
    intro v
    ext C hC
    rw [Measure.map_apply (hΦm v) hC, Measure.restrict_apply (hΦm v hC), Measure.restrict_apply hC]
    have hsub : Φ v ⁻¹' C ∩ U v ⊆ U v := Set.inter_subset_right
    have hme : MeasurableSet (Φ v ⁻¹' C ∩ U v) := (hΦm v hC).inter (hU v)
    rw [show ν v (Φ v ⁻¹' C ∩ U v) = ∫⁻ z in Φ v ⁻¹' C ∩ U v, ENNReal.ofReal (D v z) ∂lam v from
      withDensity_apply _ hme, ← h v _ hsub hme]
    congr 1
    ext x
    constructor
    · rintro ⟨z, ⟨hzC, hzU⟩, rfl⟩
      exact ⟨hzC, z, hzU, rfl⟩
    · rintro ⟨hxC, z, hzU, rfl⟩
      exact ⟨z, ⟨hxC, hzU⟩, rfl⟩
  have hrestr : (Measure.pi μ).restrict (univ.pi S) = Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hrestr2 : (Measure.pi ν).restrict (univ.pi U) = Measure.pi fun v => (ν v).restrict (U v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.restrict_apply (MeasurableSet.univ_pi hB), ← Set.pi_inter_distrib, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Measure.restrict_apply (hB v)]
  have hmap : (Measure.pi fun v => (ν v).restrict (U v)).map Ψ =
      Measure.pi fun v => (μ v).restrict (S v) := by
    refine (Measure.pi_eq fun B hB => ?_).symm
    rw [Measure.map_apply hΨm (MeasurableSet.univ_pi hB)]
    have hpre : Ψ ⁻¹' univ.pi B = univ.pi fun v => Φ v ⁻¹' B v := by
      ext z
      simp [hΨ]
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← hκ v, Measure.map_apply (hΦm v) (hB v)]
  have hΦA : Ψ '' A ⊆ univ.pi S := by
    rintro _ ⟨z, hz, rfl⟩ v -
    exact ⟨z v, hAU hz v (mem_univ v), rfl⟩
  calc Measure.pi μ (Ψ '' A) = (Measure.pi μ).restrict (univ.pi S) (Ψ '' A) := by
        rw [Measure.restrict_apply hAi, Set.inter_eq_left.2 hΦA]
    _ = (Measure.pi fun v => (ν v).restrict (U v)).map Ψ (Ψ '' A) := by rw [hrestr, hmap]
    _ = (Measure.pi fun v => (ν v).restrict (U v)) (Ψ ⁻¹' (Ψ '' A)) := Measure.map_apply hΨm hAi
    _ = (Measure.pi ν).restrict (univ.pi U) (Ψ ⁻¹' (Ψ '' A)) := by rw [hrestr2]
    _ = Measure.pi ν A := by
        rw [Measure.restrict_apply (hΨm hAi)]
        congr 1
        ext z
        constructor
        · rintro ⟨⟨z', hz', hzz⟩, hzU⟩
          have hzz' : z' = z := by
            funext v
            exact hinj v (hAU hz' v (mem_univ v)) (hzU v (mem_univ v)) (congrFun hzz v)
          rw [← hzz']
          exact hz'
        · intro hz
          exact ⟨⟨z, hz, rfl⟩, hAU hz⟩
    _ = ∫⁻ z in A, ∏ v, ENNReal.ofReal (D v (z v)) ∂Measure.pi lam := by
        rw [← withDensity_apply _ hA, withDensity_pi lam D hD]

end PI.AprimeInfG
end
end

