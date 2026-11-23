module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NormOneVol

theorem exists_domain {Γ X : Type} [Group Γ] [Countable Γ] [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) (act : Γ → X → X) (h1 : ∀ x, act 1 x = x)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x)) (hm : ∀ g, Measurable (act g))
    (hμ : ∀ g s, MeasurableSet s → μ (act g ⁻¹' s) = μ s)
    (T : Subgroup Γ) [Finite T] (C A : Set X) (hC : MeasurableSet C) (hA : MeasurableSet A)
    (hinv : ∀ g, ∀ x ∈ A, act g x ∈ A) (hcov : ∀ x ∈ A, ∃ g, act g x ∈ C)
    (hT : ∀ x ∈ C, ∀ g, act g x ∈ C ↔ g ∈ T) (hfree : ∀ x ∈ C, ∀ g, act g x = x → g = 1) :
    ∃ F : Set X, MeasurableSet F ∧ (∀ x ∈ A, ∃ g, act g x ∈ F) ∧
      (Nat.card T : ENNReal) * μ F = μ (C ∩ A) ∧
      ∀ D : Set X, MeasurableSet D → (∀ x ∈ A, ∃ g, act g x ∈ D) → μ F ≤ μ D := by
  classical
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real X
  set F : Set X := (C ∩ A) ∩ ⋂ t : T, {x | f x ≤ f (act t x)} with hFdef
  have hF : MeasurableSet F := (hC.inter hA).inter
    (MeasurableSet.iInter fun t => measurableSet_le hf.measurable (hf.measurable.comp (hm t)))
  have huniq : ∀ x ∈ F, ∀ g, act g x ∈ F → g = 1 := by
    intro x hx g hg
    have hgT : g ∈ T := (hT x hx.1.1 g).1 hg.1.1
    have a1 : f x ≤ f (act g x) := Set.mem_iInter.1 hx.2 ⟨g, hgT⟩
    have a2 : f (act g x) ≤ f (act g⁻¹ (act g x)) := Set.mem_iInter.1 hg.2 ⟨g⁻¹, T.inv_mem hgT⟩
    rw [← hmul, inv_mul_cancel, h1] at a2
    exact hfree x hx.1.1 g (hf.injective (le_antisymm a2 a1))
  have hdisj : Pairwise (Function.onFun Disjoint fun g : Γ => act g ⁻¹' F) := by
    intro g h hgh
    refine Set.disjoint_left.2 fun x hx hx' => hgh ?_
    have : act (h * g⁻¹) (act g x) ∈ F := by
      rw [← hmul, inv_mul_cancel_right]; exact hx'
    have := huniq _ hx _ this
    exact (mul_inv_eq_one.1 this).symm
  have hcovT : ∀ x ∈ C ∩ A, ∃ t : T, act t x ∈ F := by
    intro x hx
    obtain ⟨t, ht⟩ := Finite.exists_min (fun t : T => f (act t x))
    refine ⟨t, ⟨(hT x hx.1 t).2 t.2, hinv _ _ hx.2⟩, Set.mem_iInter.2 fun s => ?_⟩
    have := ht (s * t)
    simpa [hmul] using this
  refine ⟨F, hF, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨g, hg⟩ := hcov x hx
    obtain ⟨t, ht⟩ := hcovT _ ⟨hg, hinv _ _ hx⟩
    exact ⟨t * g, by rwa [hmul]⟩
  · have e : C ∩ A = ⋃ t : T, act t ⁻¹' F := by
      ext x
      refine ⟨fun hx => Set.mem_iUnion.2 (hcovT x hx), fun hx => ?_⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hx
      have e : x = act (t : Γ)⁻¹ (act t x) := by rw [← hmul, inv_mul_cancel, h1]
      rw [e]
      exact ⟨(hT _ ht.1.1 _).2 (T.inv_mem t.2), hinv _ _ ht.1.2⟩
    rw [e, measure_iUnion (f := fun t : T => act t ⁻¹' F) (fun s t hst => hdisj (fun h => hst (Subtype.ext h))) (fun t => hm _ hF)]
    simp only [hμ _ _ hF]
    have := Fintype.ofFinite T
    simp [tsum_fintype]
  · intro D hD hDc
    calc μ F ≤ μ (⋃ g : Γ, act g⁻¹ ⁻¹' (act g ⁻¹' F ∩ D)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨g, hg⟩ := hDc x hx.1.2
          refine Set.mem_iUnion.2 ⟨g⁻¹, ?_, by simpa using hg⟩
          show act g⁻¹ (act g⁻¹⁻¹ x) ∈ F
          rwa [← hmul, mul_inv_cancel, h1]
      _ ≤ ∑' g : Γ, μ (act g⁻¹ ⁻¹' (act g ⁻¹' F ∩ D)) := measure_iUnion_le _
      _ = ∑' g : Γ, μ (act g ⁻¹' F ∩ D) := by
          refine tsum_congr fun g => hμ _ _ ((hm _ hF).inter hD)
      _ = μ (⋃ g : Γ, act g ⁻¹' F ∩ D) := by
          refine (measure_iUnion (fun g h hgh => ?_) (fun g => (hm _ hF).inter hD)).symm
          exact (hdisj hgh).mono Set.inter_subset_left Set.inter_subset_left
      _ ≤ μ D := measure_mono (Set.iUnion_subset fun g => Set.inter_subset_right)

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
open scoped Pointwise Classical in
theorem volume_cone_le (K : Type) [Field K] [NumberField K] (s : ℝ) :
    volume (fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s}) =
      volume (normLeOne K) * ENNReal.ofReal s := by
  rcases le_or_gt s 0 with hs | hs
  · have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have := norm_pos_of_mem hx.1
      have h2 : mixedEmbedding.norm x ≤ s := hx.2
      linarith
    rw [this, ENNReal.ofReal_of_nonpos hs]; simp
  · have hn : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
    set c : ℝ := s ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hc
    have hc0 : 0 < c := Real.rpow_pos_of_pos hs _
    have hcs : c ^ Module.finrank ℚ K = s := Real.rpow_inv_natCast_pow hs.le hn
    have : fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ s} = c • normLeOne K := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0.ne', mem_normLeOne,
        smul_mem_iff_mem (inv_ne_zero hc0.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc0),
        inv_pow, hcs, inv_mul_le_iff₀ hs, mul_one]
      rfl
    rw [this, Measure.addHaar_smul, mixedEmbedding.finrank, hcs, abs_of_pos hs, mul_comm]

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone in
open scoped Classical in
theorem lintegral_cone_slab (K : Type) [Field K] [NumberField K] :
    ∫⁻ x in fundamentalCone K ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < Real.exp 1},
      ENNReal.ofReal (mixedEmbedding.norm x)⁻¹ = volume (normLeOne K) := by
  have hN : Measurable (fun x : mixedSpace K => mixedEmbedding.norm x) :=
    (mixedEmbedding.continuous_norm K).measurable
  have hV : volume (normLeOne K) ≠ ⊤ := by
    rw [volume_normLeOne]; finiteness
  set e := Real.exp 1 with he
  have he1 : 1 < e := Real.one_lt_exp_iff.2 one_pos
  set S := fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ e} with hS
  have hSm : MeasurableSet S := (measurableSet_fundamentalCone K).inter (measurableSet_le hN measurable_const)
  have : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ, hS, volume_cone_le]
    exact ENNReal.mul_lt_top hV.lt_top ENNReal.ofReal_lt_top⟩
  have hmap : (volume.restrict S).map (fun x : mixedSpace K => mixedEmbedding.norm x) =
      volume (normLeOne K) • volume.restrict (Set.Ioc 0 e) := by
    refine Measure.ext_of_Iic _ _ fun t => ?_
    rw [Measure.map_apply hN measurableSet_Iic, Measure.restrict_apply' hSm, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
    have e1 : (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Iic t ∩ S =
        fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ min t e} := by
      ext x; simp [hS]; tauto
    have e2 : Set.Iic t ∩ Set.Ioc 0 e = Set.Ioc 0 (min t e) := by
      ext x; simp; tauto
    rw [e1, e2, volume_cone_le, Real.volume_Ioc, sub_zero]
  have e3 : fundamentalCone K ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < e} =
      (fun x : mixedSpace K => mixedEmbedding.norm x) ⁻¹' Set.Ico 1 e ∩ S := by
    ext x
    simp only [hS, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.2, h.1, h.2.2.le⟩, fun h => ⟨h.2.1, h.1⟩⟩
  rw [e3, ← Measure.restrict_restrict (hN measurableSet_Ico),
    ← setLIntegral_map (f := fun t : ℝ => ENNReal.ofReal t⁻¹) measurableSet_Ico (by fun_prop) hN, hmap,
    Measure.restrict_smul, lintegral_smul_measure, Measure.restrict_restrict measurableSet_Ico]
  have e4 : Set.Ico 1 e ∩ Set.Ioc 0 e = Set.Ico 1 e :=
    Set.inter_eq_left.2 fun x hx => ⟨by linarith [hx.1], hx.2.le⟩
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 e :=
    intervalIntegral.intervalIntegrable_inv (f := id) (fun x hx => by
      rw [Set.uIcc_of_le he1.le] at hx; exact (by linarith [hx.1] : 0 < x).ne') continuousOn_id
  rw [e4, Measure.restrict_congr_set Ico_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint.1, ← intervalIntegral.integral_of_le he1.le,
    integral_inv_of_pos one_pos (by linarith), div_one, he, Real.log_exp]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact inv_nonneg.2 (by linarith [hx.1])

section Lattices
variable {E : Type} [Field E] [NumberField E]

open scoped nonZeroDivisors

theorem mulVec_one (γ : Matrix (Fin 1) (Fin 1) E) (y : Fin 1 → E) : γ *ᵥ y = γ 0 0 • y := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [Matrix.mulVec, dotProduct]

theorem gl_one_ne_zero (γ : GL (Fin 1) E) : (γ : Matrix (Fin 1) (Fin 1) E) 0 0 ≠ 0 := by
  have := γ.det_ne_zero
  simpa [Matrix.det_unique] using this

theorem exists_gl_one {c : E} (hc : c ≠ 0) : ∃ γ : GL (Fin 1) E, (γ : Matrix (Fin 1) (Fin 1) E) 0 0 = c :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => c) (by simpa [Matrix.det_unique] using hc), rfl⟩

theorem eq_const (y : Fin 1 → E) : y = fun _ => y 0 := by
  ext i; rw [Subsingleton.elim i 0]

theorem exists_ideal (Λ : Submodule (𝓞 E) (Fin 1 → E)) (h : Submodule.IsLattice E Λ) (hΛ : Λ ≠ ⊥) :
    ∃ I : (FractionalIdeal (𝓞 E)⁰ E)ˣ, ∀ y, y ∈ Λ ↔ y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  let I : FractionalIdeal (𝓞 E)⁰ E :=
    ⟨Λ.map (LinearMap.proj 0), FractionalIdeal.isFractional_of_fg (h.fg.map _)⟩
  have hI : ∀ y, y ∈ Λ ↔ y 0 ∈ I := by
    intro y
    refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    have : y = z := by rw [eq_const y, eq_const z]; ext; exact hzy.symm
    rwa [this]
  have h0 : I ≠ 0 := by
    intro h0
    apply hΛ (le_bot_iff.mp ?_)
    intro y hy
    have hy0 := (hI y).1 hy
    rw [h0, FractionalIdeal.mem_zero_iff] at hy0
    rw [eq_const y, hy0]
    exact Submodule.zero_mem _
  exact ⟨Units.mk0 I h0, hI⟩

theorem exists_lattice (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    ∃ Λ : Submodule (𝓞 E) (Fin 1 → E), Submodule.IsLattice E Λ ∧ Λ ≠ ⊥ ∧
      ∀ y, y ∈ Λ ↔ y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  let e : E →ₗ[𝓞 E] (Fin 1 → E) := LinearMap.pi fun _ => LinearMap.id
  have hm : ∀ y, y ∈ ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).map e ↔
      y 0 ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
    intro y
    refine ⟨?_, fun hy => ⟨y 0, hy, (eq_const y).symm⟩⟩
    rintro ⟨z, hz, rfl⟩
    exact hz
  refine ⟨_, Submodule.IsLattice.of_fg E ((FractionalIdeal.fg_unit I).map e), ?_, hm⟩
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger I.ne_zero
  have hx0' : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx0
  intro hbot
  have hy := (hm (fun _ => algebraMap (𝓞 E) E x)).2 hx
  rw [hbot, Submodule.mem_bot] at hy
  exact hx0' (congrFun hy 0)

theorem mul_principal_eq_iff (I J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (c : Eˣ) :
    I * toPrincipalIdeal (𝓞 E) E c = J ↔
      ∀ t : E, (c : E) * t ∈ (J : FractionalIdeal (𝓞 E)⁰ E) ↔ t ∈ (I : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [← Units.val_inj, Units.val_mul, coe_toPrincipalIdeal, mul_comm]
  constructor
  · intro h t
    rw [← h, FractionalIdeal.mem_singleton_mul]
    refine ⟨?_, fun ht => ⟨t, ht, rfl⟩⟩
    rintro ⟨y, hy, e⟩
    rwa [mul_left_cancel₀ c.ne_zero e]
  · intro h
    ext t
    rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨?_, fun ht => ⟨(c : E)⁻¹ * t, (h _).1 (by rwa [mul_inv_cancel_left₀ c.ne_zero]), by
      rw [mul_inv_cancel_left₀ c.ne_zero]⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact (h y).2 hy

private abbrev RankOneLattice (E : Type) [Field E] [NumberField E] :=
  {Λ : Submodule (𝓞 E) (Fin 1 → E) // Submodule.IsFullLattice E Λ}

private abbrev carries (Λ Λ' : RankOneLattice E) : Prop :=
  ∃ γ : GL (Fin 1) E, ∀ y, (γ : Matrix (Fin 1) (Fin 1) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1

private theorem rankOne_ne_bot (Λ : RankOneLattice E) : Λ.1 ≠ ⊥ := by
  intro h
  have hspan : Submodule.span E (Λ.1 : Set (Fin 1 → E)) = ⊥ := by
    refine Submodule.span_eq_bot.mpr fun x hx => ?_
    change x ∈ Λ.1 at hx
    simpa only [h, Submodule.mem_bot] using hx
  rw [Λ.2.span_eq_top] at hspan
  exact top_ne_bot hspan

private theorem rankOne_full (Λ : Submodule (𝓞 E) (Fin 1 → E))
    (hΛ : Submodule.IsLattice E Λ) (hne : Λ ≠ ⊥) : Submodule.IsFullLattice E Λ := by
  obtain ⟨x, hx, hxne⟩ := Λ.ne_bot_iff.mp hne
  have hx₀ : x 0 ≠ 0 := by
    intro h
    apply hxne
    funext i
    fin_cases i
    exact h
  refine { toIsLattice := hΛ, span_eq_top := eq_top_iff.mpr fun y _ => ?_ }
  have hy : y = (y 0 / x 0) • x := by
    funext i
    fin_cases i
    exact (div_mul_cancel₀ (y 0) hx₀).symm
  rw [hy]
  exact (Submodule.span E _).smul_mem _ (Submodule.subset_span hx)

private theorem exists_classGroupEquiv : Nonempty (Quot (carries (E := E)) ≃ ClassGroup (𝓞 E)) := by
  classical
  choose ψ hψ using fun Λ : RankOneLattice E => exists_ideal Λ.1 Λ.2.toIsLattice (rankOne_ne_bot Λ)
  let q := QuotientGroup.mk' (toPrincipalIdeal (𝓞 E) E).range
  have key : ∀ Λ Λ', carries Λ Λ' ↔ q (ψ Λ) = q (ψ Λ') := by
    intro Λ Λ'
    rw [QuotientGroup.mk'_eq_mk']
    constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨_, ⟨Units.mk0 _ (gl_one_ne_zero γ), rfl⟩, (mul_principal_eq_iff _ _ _).2 fun t => ?_⟩
      have := hγ (fun _ => t)
      rw [mulVec_one, hψ Λ' _, hψ Λ _] at this
      exact this
    · rintro ⟨_, ⟨c, rfl⟩, h⟩
      obtain ⟨γ, hγ⟩ := exists_gl_one c.ne_zero
      refine ⟨γ, fun y => ?_⟩
      rw [mulVec_one, hψ Λ' _, hψ Λ _, hγ]
      exact (mul_principal_eq_iff _ _ _).1 h _
  let F := Quot.lift (q ∘ ψ) (fun a b h => (key a b).1 h)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ h
      exact Quot.sound ((key a b).2 h)
    · intro x
      obtain ⟨I, rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨Λ, hΛ, hne, h⟩ := exists_lattice I
      let L : RankOneLattice E := ⟨Λ, rankOne_full Λ hΛ hne⟩
      have hI : ψ L = I := by
        ext t
        exact (hψ L fun _ => t).symm.trans (h fun _ => t)
      exact ⟨Quot.mk _ L, congrArg q hI⟩
  exact ⟨(Equiv.ofBijective F hF).trans (ClassGroup.equiv E).symm.toEquiv⟩

theorem mem_autGL_iff (Λ : Submodule (𝓞 E) (Fin 1 → E)) (h : Submodule.IsLattice E Λ)
    (hΛ : Λ ≠ ⊥) (x : MatInf E 1) :
    x ∈ autGL E 1 Λ ↔ ∃ u : (𝓞 E)ˣ, ∀ w a b, x w a b = w.embedding ((u : 𝓞 E) : E) := by
  obtain ⟨I, hI⟩ := exists_ideal Λ h hΛ
  constructor
  · rintro ⟨γ, hγ, hx⟩
    have h1 : I * toPrincipalIdeal (𝓞 E) E (Units.mk0 _ (gl_one_ne_zero γ)) = I :=
      (mul_principal_eq_iff _ _ _).2 fun t => by
        have := hγ (fun _ => t)
        rw [mulVec_one, hI, hI] at this
        exact this
    rw [mul_eq_left, toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
    obtain ⟨u, hu⟩ := h1
    refine ⟨u⁻¹, fun w a b => ?_⟩
    rw [hx, Subsingleton.elim a 0, Subsingleton.elim b 0]
    congr 1
    have := congrArg (fun t => u⁻¹ • t) hu
    simp only [inv_smul_smul, Units.val_mk0] at this
    rw [this, Units.smul_def, Algebra.smul_def, mul_one]
  · rintro ⟨u, hu⟩
    obtain ⟨γ, hγ⟩ := exists_gl_one (c := ((u : 𝓞 E) : E)) (by simp)
    refine ⟨γ, fun y => ?_, fun w a b => ?_⟩
    · rw [mulVec_one, hγ]
      have : ((u : 𝓞 E) : E) • y = u • y := by
        rw [Units.smul_def, ← algebraMap_smul E (u : 𝓞 E) y]
      rw [this]
      exact Λ.smul_mem_iff' u
    · rw [hu, Subsingleton.elim a 0, Subsingleton.elim b 0, hγ]

end Lattices

section Transport
variable (E : Type) [Field E] [NumberField E]

open NumberField.mixedEmbedding NumberField.InfinitePlace

noncomputable def act (u : (𝓞 E)ˣ) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    InfinitePlace E → Fin 1 → Fin 1 → ℂ := fun w => w.embedding ((u : 𝓞 E) : E) • x w

noncomputable def toMixed (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) : mixedSpace E :=
  (0, fun w => x w.1 0 0)

variable {E}

theorem isEmpty_real (hE : IsTotallyComplex E) : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => not_isReal_iff_isComplex.2 (hE.isComplex w.1) w.2⟩

theorem toMixed_act (hE : IsTotallyComplex E) (u : (𝓞 E)ˣ) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    toMixed E (act E u x) = u • toMixed E x := by
  have := isEmpty_real hE
  refine Prod.ext (Subsingleton.elim _ _) ?_
  ext w
  simp [toMixed, act]

theorem norm_toMixed (hE : IsTotallyComplex E) (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) :
    mixedEmbedding.norm (toMixed E x) = detNorm E 1 x := by
  rw [mixedEmbedding.norm_apply]
  show _ = ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [normAtPlace_apply_of_isComplex (hE.isComplex w), mult_isComplex ⟨w, hE.isComplex w⟩]
  simp [toMixed, Matrix.det_unique]

open scoped Classical in
theorem measurePreserving_toMixed (hE : IsTotallyComplex E) : MeasurePreserving (toMixed E) volume volume := by
  have := isEmpty_real hE
  have h1 : MeasurePreserving (fun (x : InfinitePlace E → Fin 1 → Fin 1 → ℂ) (w : InfinitePlace E) => x w 0 0)
      volume volume :=
    volume_preserving_pi fun w =>
      (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℂ)
    (Equiv.subtypeUnivEquiv (p := IsComplex) hE.isComplex)).symm
  have h3 : MeasurePreserving (fun z : {w : InfinitePlace E // IsComplex w} → ℂ => ((0, z) : mixedSpace E))
      volume volume := by
    refine ⟨measurable_prodMk_left, ?_⟩
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace E // IsReal w} => ℝ),
      Measure.pi_of_empty _ 0, Measure.dirac_prod]
  exact h3.comp (h2.comp h1)

theorem measurable_act (u : (𝓞 E)ˣ) : Measurable (act E u) := by
  unfold act; fun_prop

theorem measurePreserving_act (hE : IsTotallyComplex E) (u : (𝓞 E)ˣ) :
    MeasurePreserving (act E u) volume volume := by
  classical
  let L : (InfinitePlace E → Fin 1 → Fin 1 → ℂ) →ₗ[ℂ] (InfinitePlace E → Fin 1 → Fin 1 → ℂ) :=
    LinearMap.pi fun w => (w.embedding ((u : 𝓞 E) : E) • LinearMap.id).comp (LinearMap.proj w)
  have hd : LinearMap.det (L.restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_pi, map_prod]
    have := prod_eq_abs_norm ((u : 𝓞 E) : E)
    rw [NumberField.Units.norm] at this
    push_cast at this
    rw [← this]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex ⟨w, hE.isComplex w⟩, LinearMap.det_smul, LinearMap.det_id, Complex.normSq_eq_norm_sq,
      ← norm_embedding_eq]
    simp [Module.finrank_pi_fintype]
  refine ⟨measurable_act u, ?_⟩
  have : (volume : Measure (Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ)) (f := L.restrictScalars ℝ) (by rw [hd]; norm_num)
  rw [hd, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at this
  exact this

open scoped Classical in
theorem torsion_mul_covol (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin 1 → E))
    (h : Submodule.IsLattice E Λ) (hΛ : Λ ≠ ⊥) :
    (Units.torsionOrder E : ENNReal) *
      covol (autGL E 1 Λ) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} =
      volume (fundamentalCone.normLeOne E) := by
  have hN : Measurable (fun x : mixedSpace E => mixedEmbedding.norm x) :=
    (mixedEmbedding.continuous_norm E).measurable
  have hφ := measurePreserving_toMixed hE
  have hdet : Measurable (fun x : InfinitePlace E → Fin 1 → Fin 1 → ℂ => detNorm E 1 x) := by
    simp only [← norm_toMixed hE]; exact hN.comp hφ.measurable
  have hdact : ∀ u x, detNorm E 1 (act E u x) = detNorm E 1 x := fun u x => by
    rw [← norm_toMixed hE, ← norm_toMixed hE, toMixed_act hE, norm_unit_smul]
  let μ : Measure (InfinitePlace E → Fin 1 → Fin 1 → ℂ) :=
    volume.withDensity fun x => ENNReal.ofReal ((detNorm E 1 x)⁻¹ ^ 1)
  let A : Set (InfinitePlace E → Fin 1 → Fin 1 → ℂ) := {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1}
  have hA : MeasurableSet A := hdet (measurableSet_Ico (a := 1) (b := Real.exp 1))
  have hC : MeasurableSet (toMixed E ⁻¹' fundamentalCone E) := hφ.measurable (measurableSet_fundamentalCone E)
  have : StandardBorelSpace (Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : StandardBorelSpace (Fin 1 → Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : StandardBorelSpace (InfinitePlace E → Fin 1 → Fin 1 → ℂ) := StandardBorelSpace.pi_countable
  have : Countable (𝓞 E) := Countable.of_equiv _ (RingOfIntegers.basis E).equivFun.symm.toEquiv
  have : Countable (𝓞 E)ˣ := Units.val_injective.countable
  obtain ⟨F, hF, hcov, hvol, hmin⟩ := exists_domain μ (act E) (fun x => by ext; simp [act])
    (fun g h x => by ext; simp [act, mul_assoc]) measurable_act
    (fun g s hs => by
      rw [withDensity_apply _ hs, withDensity_apply _ (measurable_act g hs),
        ← (measurePreserving_act hE g).setLIntegral_comp_preimage hs (by fun_prop)]
      simp only [hdact])
    (Units.torsion E) (toMixed E ⁻¹' fundamentalCone E) A hC hA
    (fun g x hx => by simpa only [A, Set.mem_setOf_eq, hdact] using hx)
    (fun x hx => by
      obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem (x := toMixed E x)
        (by rw [norm_toMixed hE]; exact (lt_of_lt_of_le one_pos hx.1).ne')
      exact ⟨u, by rwa [Set.mem_preimage, toMixed_act hE]⟩)
    (fun x hx g => by
      rw [Set.mem_preimage, toMixed_act hE]
      exact fundamentalCone.unit_smul_mem_iff_mem_torsion hx g)
    (fun x hx g hg => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
      have h0 := fundamentalCone.normAtPlace_pos_of_mem hx w
      rw [normAtPlace_apply_of_isComplex (hE.isComplex w), norm_pos_iff] at h0
      have h1 : w.embedding ((g : 𝓞 E) : E) * x w 0 0 = x w 0 0 := congrFun (congrFun (congrFun hg w) 0) 0
      have h2 : w.embedding ((g : 𝓞 E) : E) = 1 := (mul_eq_right₀ h0).1 h1
      rw [map_eq_one_iff _ w.embedding.injective] at h2
      ext
      simpa using h2)
  have hiff : ∀ (D : Set (MatInf E 1)) (x : MatInf E 1),
      (∃ γ ∈ autGL E 1 Λ, γ * x ∈ D) ↔ ∃ u, act E u x ∈ D := by
    intro D x
    have hm : ∀ (u : (𝓞 E)ˣ) (γ : MatInf E 1), (∀ w a b, γ w a b = w.embedding ((u : 𝓞 E) : E)) →
        γ * x = act E u x := by
      intro u γ hγ
      funext w a b
      show (Matrix.of (γ w) * Matrix.of (x w)) a b = w.embedding ((u : 𝓞 E) : E) * x w a b
      rw [Subsingleton.elim a 0]
      simp [Matrix.mul_apply, hγ]
    constructor
    · rintro ⟨γ, hγ, hx⟩
      obtain ⟨u, hu⟩ := (mem_autGL_iff Λ h hΛ γ).1 hγ
      exact ⟨u, by rwa [← hm u γ hu]⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun w _ _ => w.embedding ((u : 𝓞 E) : E), (mem_autGL_iff Λ h hΛ _).2 ⟨u, fun _ _ _ => rfl⟩, ?_⟩
      rwa [hm u _ fun _ _ _ => rfl]
  have hc : covol (autGL E 1 Λ) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} = μ F := by
    apply le_antisymm
    · exact iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le (fun x hx => (hiff F x).2 (hcov x hx)) le_rfl))
    · exact le_iInf fun D => le_iInf fun hD => le_iInf fun hDc => hmin D hD fun x hx => (hiff D x).1 (hDc x hx)
  rw [hc, Units.torsionOrder, hvol, ← lintegral_cone_slab, withDensity_apply _ (hC.inter hA),
    ← hφ.setLIntegral_comp_preimage
      (s := fundamentalCone E ∩ {x | 1 ≤ mixedEmbedding.norm x ∧ mixedEmbedding.norm x < Real.exp 1}) ((measurableSet_fundamentalCone E).inter
      (hN (measurableSet_Ico (a := 1) (b := Real.exp 1)))) (by fun_prop)]
  simp only [A, pow_one, ← norm_toMixed hE]
  rfl

end Transport

open InfinitePlace in
private theorem denseRange_embeddings {E : Type} [Field E] [NumberField E]
    (hE : IsTotallyComplex E) : DenseRange (fun (a : E) (w : InfinitePlace E) => w.embedding a) := by
  let f := Pi.map (fun w : InfinitePlace E => (Completion.extensionEmbedding w : w.Completion → ℂ))
  have hf : DenseRange f :=
    DenseRange.piMap fun w => (Completion.surjective_extensionEmbedding_of_isComplex (hE.isComplex w)).denseRange
  have hc : Continuous f :=
    continuous_pi fun w => (Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
  have he : (fun (a : E) (w : InfinitePlace E) => w.embedding a) =
      f ∘ algebraMap E (InfiniteAdeleRing E) := by
    funext a w
    change w.embedding a = Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) a w)
    rw [InfiniteAdeleRing.algebraMap_apply, Completion.extensionEmbedding_coe]
    rfl
  rw [he]
  exact hf.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

-- The zero lattice has the whole rational general linear group as its stabilizer.
private theorem covol_bot {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E) :
    covol (autGL E 1 ⊥) (haarGL E 1) {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} = 0 := by
  classical
  let V := InfinitePlace E → Fin 1 → Fin 1 → ℂ
  let oneMat : V := fun _ _ _ => 1
  have hdet : Continuous (fun x : V => detNorm E 1 x) := by
    simp only [detNorm, Matrix.det_unique]
    exact continuous_finsetProd _ fun w _ => (show Continuous (fun x : V => x w 0 0) by fun_prop).norm.pow 2
  have hdet_one : detNorm E 1 oneMat = 1 := by simp [detNorm, Matrix.det_unique, oneMat]
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hdet_zero : detNorm E 1 (0 : V) = 0 := by
    refine Finset.prod_eq_zero (i := w₀) (Finset.mem_univ _) ?_
    change ‖(Matrix.of (fun _ _ : Fin 1 => (0 : ℂ))).det‖ ^ 2 = 0
    simp [Matrix.det_unique]
  have : (volume : Measure (Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin 1 → Fin 1 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure V).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hsingleton : (volume : Measure V) {oneMat} = 0 := by
    rw [volume_pi, Measure.pi_singleton]
    apply Finset.prod_eq_zero (Finset.mem_univ w₀)
    rw [volume_pi, Measure.pi_singleton]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 1))
    rw [volume_pi, Measure.pi_singleton]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 1)) (measure_singleton _)
  apply le_antisymm _ bot_le
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨U, hU, hUo, hUμ⟩ := ({oneMat} : Set V).exists_isOpen_lt_of_lt (μ := volume) (ε / 2) (by
    rw [hsingleton]
    exact ENNReal.div_pos hε.ne' ENNReal.ofNat_ne_top)
  let D : Set V := U ∩ {x | (1 / 2 : ℝ) < detNorm E 1 x}
  have hDo : IsOpen D := hUo.inter (isOpen_lt continuous_const hdet)
  have hD1 : oneMat ∈ D := ⟨hU (Set.mem_singleton _), by
    change (1 / 2 : ℝ) < detNorm E 1 oneMat
    rw [hdet_one]
    norm_num⟩
  have hcov : ∀ x : MatInf E 1, x ∈ {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1} →
      ∃ γ ∈ autGL E 1 ⊥, γ * x ∈ D := by
    intro x hx
    have hx0 (w : InfinitePlace E) : x w 0 0 ≠ 0 := by
      intro hw
      have hz : detNorm E 1 x = 0 :=
        Finset.prod_eq_zero (i := w) (Finset.mem_univ _) (by simp [Matrix.det_unique, hw])
      exact zero_lt_one.not_ge (hz ▸ hx.1)
    let g (z : InfinitePlace E → ℂ) : V := fun w a b => z w * x w a b
    have hg : Continuous g := by unfold g; fun_prop
    have h1 : g (fun w => (x w 0 0)⁻¹) = oneMat := by
      funext w a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      exact inv_mul_cancel₀ (hx0 w)
    obtain ⟨a, ha⟩ := (denseRange_embeddings hE).exists_mem_open (hDo.preimage hg)
      ⟨_, by show g _ ∈ D; rwa [h1]⟩
    change g (fun w => w.embedding a) ∈ D at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h : g (fun w => w.embedding 0) = 0 := by
        funext w i j
        change w.embedding 0 * x w i j = 0
        rw [map_zero, zero_mul]
      rw [h] at ha
      have hpos : (1 / 2 : ℝ) < detNorm E 1 (0 : V) := ha.2
      rw [hdet_zero] at hpos
      norm_num at hpos
    obtain ⟨γ, hγ⟩ := exists_gl_one ha0
    let aInf : MatInf E 1 := fun w _ _ => w.embedding a
    refine ⟨aInf, ⟨γ, fun y => ?_, fun w i j => ?_⟩, ?_⟩
    · rw [mulVec_one, hγ, Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun h => (smul_eq_zero.mp h).resolve_left ha0, fun h => by simp [h]⟩
    · rw [Subsingleton.elim i 0, Subsingleton.elim j 0, hγ]
    · have hmul : aInf * x = g (fun w => w.embedding a) := by
        funext w i j
        change (Matrix.of (fun _ _ : Fin 1 => w.embedding a) * Matrix.of (x w)) i j = _
        rw [Subsingleton.elim i 0]
        simp [Matrix.mul_apply, g]
      rwa [hmul]
  calc
    _ ≤ haarGL E 1 D := iInf_le_of_le D (iInf_le_of_le hDo.measurableSet (iInf_le _ hcov))
    _ = ∫⁻ x in D, ENNReal.ofReal (detNorm E 1 x)⁻¹ ∂(volume : Measure V) := by
      change (volume : Measure V).withDensity (fun x : V => ENNReal.ofReal ((detNorm E 1 x)⁻¹ ^ 1)) D = _
      simp only [pow_one, withDensity_apply _ hDo.measurableSet]
    _ ≤ ∫⁻ _ in D, (2 : ENNReal) ∂(volume : Measure V) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      rw [← ENNReal.ofReal_ofNat 2]
      apply ENNReal.ofReal_le_ofReal
      have hd : (1 / 2 : ℝ) < detNorm E 1 x := hx.2
      exact (inv_le_comm₀ ((by norm_num : (0 : ℝ) < 1 / 2).trans hd) (by norm_num)).2
        (by simpa only [one_div] using hd.le)
    _ < ε := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_of_lt_div' ((measure_mono (Set.inter_subset_left : D ⊆ U)).trans_lt hUμ)

theorem glVol_one : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    glVol E 1 = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  intro E _ _ hE
  classical
  obtain ⟨e⟩ := exists_classGroupEquiv (E := E)
  have hw : (Units.torsionOrder E : ENNReal) ≠ 0 := by exact_mod_cast (Units.torsionOrder_pos E).ne'
  have hw' : (0 : ℝ) < Units.torsionOrder E := by exact_mod_cast (Units.torsionOrder_pos E)
  let F (c : Quot (carries (E := E))) :=
    (Units.torsionOrder E : ENNReal) *
      covol (autGL E 1 (Quot.out c).1) (haarGL E 1)
        {x | 1 ≤ detNorm E 1 x ∧ detNorm E 1 x < Real.exp 1}
  have hsum : (∑' c, F c) = (Units.torsionOrder E : ENNReal) *
      ENNReal.ofReal (dedekindZeta_residue E *
        Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
    have hF (c : ClassGroup (𝓞 E)) :
        F (e.symm c) = volume (mixedEmbedding.fundamentalCone.normLeOne E) :=
      torsion_mul_covol hE _ (Quot.out (e.symm c)).2.toIsLattice (rankOne_ne_bot (Quot.out (e.symm c)))
    rw [← e.symm.tsum_eq, tsum_fintype]
    simp_rw [hF]
    rw [Finset.sum_const, Finset.card_univ, mixedEmbedding.fundamentalCone.volume_normLeOne]
    have hr : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have hf : Formalism.HermitianLatticesTheory.fDeg E = InfinitePlace.nrComplexPlaces E := by
      rw [Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hr, zero_add]
    have hf0 : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) ≠ 0 := by
      rw [Formalism.HermitianLatticesTheory.fDeg]; exact_mod_cast Fintype.card_ne_zero
    have hd : 0 < |(discr E : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
    have hv : Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E = Real.sqrt |(discr E : ℝ)| / 2 ^ Formalism.HermitianLatticesTheory.fDeg E := by
      rw [Formalism.HermitianLatticesTheory.vInv, div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hd.le, Real.sqrt_eq_rpow]
      congr 2
      field_simp
    have hs := Real.sqrt_pos.2 hd
    have key : (Units.torsionOrder E : ℝ) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) =
        classNumber E * (Real.pi ^ InfinitePlace.nrComplexPlaces E * Units.regulator E) := by
      rw [hv, dedekindZeta_residue_def, hr, hf, mul_pow]
      field_simp
    rw [← ENNReal.ofReal_natCast (Units.torsionOrder E), ← ENNReal.ofReal_mul hw'.le, key,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow Real.pi_pos.le, hr, pow_zero, one_mul, nsmul_eq_mul, classNumber,
      ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [← ENNReal.mul_right_inj hw (ENNReal.natCast_ne_top _), glVol, ← ENNReal.tsum_mul_left]
  exact hsum

end GlobalTheory.NormOneVol
