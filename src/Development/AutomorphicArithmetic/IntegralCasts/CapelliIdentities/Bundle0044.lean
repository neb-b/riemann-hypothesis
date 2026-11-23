module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapMulVolumeOfSubgroup
section
open MeasureTheory Set

private noncomputable def mulE {n : ℕ} (a x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  Matrix.of.symm (Matrix.of a * Matrix.of x)

private lemma mulE_apply {n : ℕ} (a x : Fin n → Fin n → ℂ) (i j : Fin n) :
    mulE a x i j = ∑ k, a i k * x k j := by
  simp [mulE, Matrix.mul_apply]

private lemma continuous_mulE {n : ℕ} :
    Continuous (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => mulE p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulE_apply]
  fun_prop

private lemma measurable_mulE {n : ℕ} (a : Fin n → Fin n → ℂ) : Measurable (mulE a) :=
  (continuous_mulE.comp (Continuous.prodMk_right a)).measurable

private lemma continuous_detE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ => (Matrix.of v).det) :=
  Continuous.matrix_det (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma continuous_adjE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ =>
      (Matrix.of.symm (Matrix.of v).adjugate : Fin n → Fin n → ℂ)) :=
  Continuous.matrix_adjugate (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma haarE (n : ℕ) :
    (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure ℂ)
  exact Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure (Fin n → ℂ))

private lemma exists_pair (n : ℕ) :
    ∃ V K : Set (Fin n → Fin n → ℂ), IsCompact V ∧ IsCompact K ∧ 0 < volume V ∧
      ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K := by
  haveI := haarE n
  have hU : IsOpen {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} :=
    isOpen_ne_fun continuous_detE continuous_const
  have h1 : (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) ∈
      {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} := by
    simp only [Set.mem_ofPred_eq, Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨V, hV, hi, hsub⟩ := exists_compact_subset hU h1
  refine ⟨V, (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    ((Matrix.of p.2).det)⁻¹ • mulE p.1 (Matrix.of.symm (Matrix.of p.2).adjugate)) '' (V ×ˢ V),
    hV, ?_, Measure.measure_pos_of_nonempty_interior _ ⟨_, hi⟩, ?_⟩
  · refine (hV.prod hV).image_of_continuousOn ?_
    refine ContinuousOn.fun_smul ?_ ?_
    · exact (continuous_detE.comp continuous_snd).continuousOn.inv₀ fun p hp => hsub hp.2
    · exact (continuous_mulE.comp
        (continuous_fst.prodMk (continuous_adjE.comp continuous_snd))).continuousOn
  · rintro y v hv w hw rfl
    refine ⟨(mulE y v, v), ⟨hw, hv⟩, ?_⟩
    have hd : (Matrix.of v).det ≠ 0 := hsub hv
    have : mulE (mulE y v) (Matrix.of.symm (Matrix.of v).adjugate) = (Matrix.of v).det • y := by
      simp only [mulE, Equiv.apply_symm_apply, Matrix.mul_assoc, Matrix.mul_adjugate,
        Matrix.mul_smul, Matrix.mul_one]
      rfl
    simp only [this, smul_smul, inv_mul_cancel₀ hd, one_smul]

private lemma mulE_cancel {n : ℕ} {a y v w : Fin n → Fin n → ℂ} (ha : (Matrix.of a).det ≠ 0)
    (h : mulE (mulE a y) v = mulE a w) : mulE y v = w := by
  have hu : IsUnit (Matrix.of a) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit ha)
  have h' : Matrix.of a * (Matrix.of y * Matrix.of v) = Matrix.of a * Matrix.of w := by
    rw [← Matrix.mul_assoc]
    exact h
  exact hu.mul_left_cancel h'

private lemma key {n : ℕ} {G : Set (Fin n → Fin n → ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
    [SFinite μ] (hG : μ Gᶜ = 0) (hdet : ∀ a ∈ G, (Matrix.of a).det ≠ 0)
    (hvol : ∀ a ∈ G, Measure.map (mulE a) volume = volume)
    (hinv : ∀ a ∈ G, Measure.map (mulE a) μ = μ)
    {V K B D : Set (Fin n → Fin n → ℂ)} (hV : IsCompact V) (hB : IsCompact B)
    (hD : MeasurableSet D)
    (hK : ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K)
    (hBD : ∀ g ∈ B, ∀ v ∈ V, mulE g v ∈ D) :
    volume V * μ B ≤ μ K * volume D := by
  set S : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    (fun p => (p.1, mulE p.1 p.2)) '' (B ×ˢ V) with hS
  have hSm : MeasurableSet S :=
    ((hB.prod hV).image (continuous_fst.prodMk continuous_mulE)).measurableSet
  have hae : ∀ᵐ g ∂μ, g ∈ G := hG
  have h1 : volume V * μ B ≤ (μ.prod volume) S := by
    rw [Measure.prod_apply hSm, ← lintegral_indicator_const hB.measurableSet]
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hgB : g ∈ B
    · rw [indicator_of_mem hgB]
      have hm : MeasurableSet (Prod.mk g ⁻¹' S) := measurable_prodMk_left hSm
      calc volume V ≤ volume (mulE g ⁻¹' (Prod.mk g ⁻¹' S)) :=
            measure_mono fun v hv => ⟨(g, v), ⟨hgB, hv⟩, rfl⟩
        _ = volume (Prod.mk g ⁻¹' S) := by
            rw [← Measure.map_apply (measurable_mulE g) hm, hvol g hg]
    · rw [indicator_of_notMem hgB]
      exact zero_le
  have h2 : (μ.prod volume) S ≤ μ K * volume D := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const hD]
    refine lintegral_mono fun x => ?_
    have hm : MeasurableSet ((fun g => (g, x)) ⁻¹' S) := measurable_prodMk_right hSm
    by_cases hne : (((fun g => (g, x)) ⁻¹' S) ∩ G).Nonempty
    · obtain ⟨a, ⟨⟨a', w⟩, ⟨haB, hw⟩, he⟩, haG⟩ := hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      show μ _ ≤ _
      rw [indicator_of_mem (hBD _ haB _ hw), ← hinv _ haG,
        Measure.map_apply (measurable_mulE _) hm, hinv _ haG]
      refine measure_mono ?_
      rintro y ⟨⟨g, v⟩, ⟨-, hv⟩, he'⟩
      obtain ⟨rfl, h'⟩ := Prod.mk.inj he'
      exact hK y v hv w hw (mulE_cancel (hdet _ haG) h')
    · have : μ ((fun g => (g, x)) ⁻¹' S) = 0 := by
        refine measure_mono_null ?_ hG
        intro g hg hgG
        exact hne ⟨g, hg, hgG⟩
      show μ _ ≤ _
      rw [this]
      exact zero_le
  exact h1.trans h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapPiScale
section
open MeasureTheory in
theorem UpperTheory.Reformulated.B.MapPiScale.map_pi_scale :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by
  intro ι _ α _ μ _ g hg c _ hc h
  have hs : ∀ i, SigmaFinite ((μ i).map (g i)) := by
    intro i
    rw [h i, ← ENNReal.coe_toNNReal (hc i)]
    exact (inferInstance : SigmaFinite ((c i).toNNReal • μ i))
  rw [Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  refine Measure.pi_eq fun s _ => ?_
  simp only [h, Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapSurj
section
theorem UpperTheory.Reformulated.B.Qk2.map_surj :
    ∀ {A E : Type} [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] {E' : Type} [inst_3 : Ring E'] [inst_4 : Algebra A E'] (f : E' →ₐ[A] E),
    Function.Surjective (⇑f : E' → E) →
      ∀ (S : Type) [inst_5 : CommRing S] [inst_6 : Algebra A S],
        Function.Surjective
          (⇑(Algebra.TensorProduct.map (AlgHom.id S S) f) : TensorProduct A S E' → TensorProduct A S E) := by
  intro A E _ _ _ E' _ _ f hf S _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s e =>
    obtain ⟨e', rfl⟩ := hf e
    exact ⟨TensorProduct.tmul A s e', by simp⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapTor
section
noncomputable def UpperTheory.Reformulated.B.H71.wt1 :
    Fin (3 : ℕ) → ℤ :=
    fun (i : Fin (3 : ℕ)) ↦ (1 : ℤ) - (↑(↑i : ℕ) : ℤ)

theorem UpperTheory.Reformulated.B.H71.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.mul_inv, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux3.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (t : Rˣ),
      ((Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R)) *
          Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
        (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R) := by
  intro R _ t
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.inv_mul, Matrix.diagonal_one]

noncomputable def UpperTheory.Reformulated.B.H71.torGL.{u_1} :
    {R : Type u_1} → [inst : CommRing R] → Rˣ → GL (Fin (3 : ℕ)) R :=
    fun {R : Type u_1} [CommRing R] (t : Rˣ) ↦
      { val := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R),
        inv := Matrix.diagonal fun (i : Fin (3 : ℕ)) ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i)⁻¹ : R),
        val_inv := UpperTheory.Reformulated.B.H71.aux2 t, inv_val := UpperTheory.Reformulated.B.H71.aux3 t : (Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R)ˣ }

theorem UpperTheory.Reformulated.B.H71.aux5.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R], UpperTheory.Reformulated.B.H71.torGL (1 : Rˣ) = (1 : GL (Fin (3 : ℕ)) R) := by
  intro R _
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((1 : Rˣ) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) = 1
  simp only [one_zpow, Units.val_one, Matrix.diagonal_one]

theorem UpperTheory.Reformulated.B.H71.aux6.{u_1} :
    ∀ (R : Type u_1) [inst : CommRing R] (s t : Rˣ),
      UpperTheory.Reformulated.B.H71.torGL (s * t) = UpperTheory.Reformulated.B.H71.torGL s * UpperTheory.Reformulated.B.H71.torGL t := by
  intro R _ s t
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((s * t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑(s ^ UpperTheory.Reformulated.B.H71.wt1 i) : R)) *
      Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : R))
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_zpow, Units.val_mul]

noncomputable def UpperTheory.Reformulated.B.H71.tor.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → Rˣ →* GL (Fin (3 : ℕ)) R :=
    fun (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.H71.torGL, map_one' := UpperTheory.Reformulated.B.H71.aux5 R, map_mul' := UpperTheory.Reformulated.B.H71.aux6 R :
        Rˣ →* GL (Fin (3 : ℕ)) R }

theorem UpperTheory.Reformulated.B.H71.map_tor :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (t : Aˣ),
      (Matrix.GeneralLinearGroup.map f : GL (Fin (3 : ℕ)) A → GL (Fin (3 : ℕ)) B)
          ((UpperTheory.Reformulated.B.H71.tor A : Aˣ → GL (Fin (3 : ℕ)) A) t) =
        (UpperTheory.Reformulated.B.H71.tor B : Bˣ → GL (Fin (3 : ℕ)) B) ((Units.map (↑f : A →* B) : Aˣ → Bˣ) t) := by
  intro A B _ _ f t
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ UpperTheory.Reformulated.B.H71.wt1 i) : A))).map f =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑((Units.map (f : A →* B) t) ^ UpperTheory.Reformulated.B.H71.wt1 i) : B))
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow, Units.coe_map]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr
section
noncomputable def UpperTheory.Reformulated.B.Qf5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Qf5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Qf5.MatIrr U a → UpperTheory.Reformulated.B.Qf5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hb | ht
  · left
    rw [Submodule.eq_bot_iff] at hb ⊢
    intro w hw
    have h0 := hb ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) (by rw [hmem, hcancel]; exact hw)
    rw [← hcancel w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at ht ⊢
    intro w
    have h1 := (hmem _).1 (ht ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w))
    rwa [hcancel] at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrrConj
section
noncomputable def UpperTheory.Reformulated.B.Ua5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Ua5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Ua5.MatIrr U a → UpperTheory.Reformulated.B.Ua5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hbot | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [hmem, hcancel]
      exact hw
    rw [hbot, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← hcancel w, h1, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : (↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w ∈
        W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
      rw [htop]
      exact Submodule.mem_top
    rwa [hmem, hcancel] at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatchStatement
section
theorem UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main.{u_1} :
    ∀ {Ω : Type} [inst : Field Ω] (W : ValuationSubring Ω) {κ : Type u_1} [Finite κ] (x : κ → Ω),
      (∃ (j : κ), x j ≠ (0 : Ω)) → ∃ (c : κ), x c ≠ (0 : Ω) ∧ ∀ (j : κ), x j / x c ∈ W := by
  intro Ω _ W κ _ x ⟨j0, hj0⟩
  have : Nonempty κ := ⟨j0⟩
  obtain ⟨c, hc⟩ := Finite.exists_max (fun j => W.valuation (x j))
  have hc0 : x c ≠ 0 := by
    intro h
    have h1 := hc j0
    simp only [h, map_zero] at h1
    exact hj0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  refine ⟨c, hc0, fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  have hpos : W.valuation (x c) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (hc j)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeanValueUniqueness
section
theorem UpperTheory.mean_value_uniqueness :
    ∀ {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [CompactSpace K]
        [MeasurableSpace K] [OpensMeasurableSpace K] (κ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure κ]
        (a : K → G) (p : K → ℂ), Continuous a → Continuous p → ∀ φ ψ : G → ℂ, Continuous φ → Continuous ψ →
        (∀ g, ∫ k, p k * φ (g * a k) ∂κ = φ g) → (∀ g, ∫ k, p k * ψ (g * a k) ∂κ = ψ g) →
        ∀ g, ∫ k, p k * (φ + ψ) (g * a k) ∂κ = (φ + ψ) g := by
  intro G K _ _ _ _ _ _ _ κ _ a p ha hp φ ψ hφ hψ h1 h2 g
  have key : ∀ f : G → ℂ, Continuous f →
      MeasureTheory.Integrable (fun k => p k * f (g * a k)) κ := by
    intro f hf
    have hc : Continuous (fun k => p k * f (g * a k)) :=
      hp.mul (hf.comp (continuous_const.mul ha))
    exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable κ
  simp only [Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add (key φ hφ) (key ψ hψ), h1 g, h2 g]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurableMatrixInv
section
theorem UpperTheory.measurable_matrix_inv :
    ∀ n : ℕ, Measurable (fun x : Fin n → Fin n → ℂ => (Matrix.of.symm ((Matrix.of x : Matrix (Fin n) (Fin n) ℂ)⁻¹) : Fin n → Fin n → ℂ)) := by
  intro n
  have hc : Continuous (fun x : Fin n → Fin n → ℂ => (Matrix.of x : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_id
  have hdet : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).det) := hc.matrix_det.measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hadj : Measurable (fun x : Fin n → Fin n → ℂ =>
      (Matrix.of x : Matrix (Fin n) (Fin n) ℂ).adjugate i j) :=
    (hc.matrix_adjugate.matrix_elem i j).measurable
  have h := hdet.inv.mul hadj
  convert h using 1
  funext x
  simp only [Matrix.of_symm_apply, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv,
    smul_eq_mul, Pi.mul_apply, Pi.inv_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurableOfSeparatingFunctionals
section
theorem UpperTheory.Reformulated.B.Qk65.measurable_of_separating_functionals :
    ∀ {G V ι : Type} [inst : MeasurableSpace G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (l : ι → V →ₗ[ℂ] ℂ),
    (∀ (a : V), (∀ (y : ι), (l y : V → ℂ) a = (0 : ℂ)) → a = (0 : V)) →
      ∀ (T : G → V),
        (∀ (y : ι), Measurable fun (g : G) ↦ (l y : V → ℂ) (T g)) →
          ∀ (L : V →ₗ[ℂ] ℂ), Measurable fun (g : G) ↦ (L : V → ℂ) (T g) := by
  intro G V ι _ _ _ _ l hl T hT L
  have hL : L ∈ Submodule.span ℂ (Set.range l) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro a ha
    have h0 : a = 0 := hl a fun y => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ha y)
    rw [h0]
    exact Submodule.zero_mem _
  induction hL using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact hT y
  | zero => exact measurable_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_mul c
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeasurePreservingSwapPi
section
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qe3b.mp_left.{u_1, u_2, u_3}
    {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2)
      (Measure.pi fun (_ : ι) ↦ Measure.pi fun (_ : κ) ↦ ν)
      (Measure.pi fun (_ : ι × κ) ↦ ν) := by
  have hm : Measurable (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) := by fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have h : (fun (f : ι → κ → X) (p : ι × κ) ↦ f p.1 p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp [Set.mem_pi]
  rw [h, Measure.pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qe3b.mp_right.{u_1, u_2, u_3}
    {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] :
    MeasurePreserving (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
      (Measure.pi fun (_ : κ) ↦ Measure.pi fun (_ : ι) ↦ ν)
      (Measure.pi fun (_ : ι × κ) ↦ ν) := by
  have hm : Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) := by fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have h : (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1) ⁻¹' Set.univ.pi s
      = Set.univ.pi fun k ↦ Set.univ.pi fun i ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
    exact forall_comm
  rw [h, Measure.pi_pi, Fintype.prod_prod_type_right]
  exact Finset.prod_congr rfl fun i _ ↦ Measure.pi_pi _ _

theorem UpperTheory.Reformulated.B.Qe3b.measurePreserving_swapPi.{u_1, u_2, u_3} :
    ∀ {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
    [inst_2 : MeasurableSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite ν],
    MeasureTheory.MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) ↦ f i k)
      (MeasureTheory.Measure.pi fun (x : ι) ↦ MeasureTheory.Measure.pi fun (x : κ) ↦ ν)
      (MeasureTheory.Measure.pi fun (x : κ) ↦ MeasureTheory.Measure.pi fun (x : ι) ↦ ν) := by
  intro ι κ X _ _ _ ν _
  let e : (κ → ι → X) ≃ᵐ (ι × κ → X) :=
    { toFun := fun f p ↦ f p.2 p.1
      invFun := fun g k i ↦ g (i, k)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun := by
        change Measurable (fun (f : κ → ι → X) (p : ι × κ) ↦ f p.2 p.1)
        fun_prop
      measurable_invFun := by
        change Measurable (fun (g : ι × κ → X) (k : κ) (i : ι) ↦ g (i, k))
        fun_prop }
  exact (MeasureTheory.MeasurePreserving.symm e
    (UpperTheory.Reformulated.B.Qe3b.mp_right (ι := ι) (κ := κ) ν)).comp (UpperTheory.Reformulated.B.Qe3b.mp_left ν)
end

