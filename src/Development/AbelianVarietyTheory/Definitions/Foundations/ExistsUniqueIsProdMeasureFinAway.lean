module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292

@[expose] public section

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal ENNReal Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain

section Generic

variable {G ι κ : Type} {H : ι → Type} {P : κ → Type} [Group G] [∀ i, Group (H i)] [∀ k, Group (P k)]
  (p : ∀ i, G →* H i) (q : ∀ k, G →* P k) (K : ∀ k, Subgroup (P k))

def cyl (S : Finset κ) (A : ∀ i, Set (H i)) (B : ∀ k, Set (P k)) : Set G :=
  {g | (∀ i, p i g ∈ A i) ∧ (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k}

theorem mem_cyl {S : Finset κ} {A : ∀ i, Set (H i)} {B : ∀ k, Set (P k)} {g : G} :
    g ∈ cyl p q K S A B ↔ (∀ i, p i g ∈ A i) ∧ (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k := Iff.rfl


variable [TopologicalSpace G] [∀ i, TopologicalSpace (H i)] [∀ k, TopologicalSpace (P k)]

structure IsRestrGroup : Prop where
  cont_p : ∀ i, Continuous (p i)
  cont_q : ∀ k, Continuous (q k)
  isOpen_K : ∀ k, IsOpen (K k : Set (P k))
  isOpen_all : IsOpen {g | ∀ k, q k g ∈ K k}
  isCompact_cyl : ∀ S A B, (∀ i, IsCompact (A i)) → (∀ k ∈ S, IsCompact (B k)) → IsCompact (cyl p q K S A B)
  exists_comp : ∀ (S : Finset κ) (x : ∀ i, H i) (y : ∀ k : S, P k),
    ∃ g, (∀ i, p i g = x i) ∧ (∀ k : S, q k g = y k) ∧ ∀ k ∉ S, q k g ∈ K k

variable [Fintype ι] [MeasurableSpace G] [∀ i, MeasurableSpace (H i)] [∀ k, MeasurableSpace (P k)]

structure IsRestrProd (μi : ∀ i, Measure (H i)) (μf : ∀ k, Measure (P k)) (μ : Measure G) : Prop where
  haar_inf : ∀ i, (μi i).IsHaarMeasure
  haar_fin : ∀ k, (μf k).IsHaarMeasure
  vol_one : ∀ᶠ k in cofinite, μf k (K k) = 1
  haar : μ.IsHaarMeasure
  measure_cyl : ∀ S : Finset κ, (∀ k ∉ S, μf k (K k) = 1) → ∀ A B, (∀ i, MeasurableSet (A i)) →
    (∀ k ∈ S, MeasurableSet (B k)) → μ (cyl p q K S A B) = (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k)

variable {p q K} {μi : ∀ i, Measure (H i)} {μf : ∀ k, Measure (P k)} {μ : Measure G}


omit [∀ k, TopologicalSpace (P k)] in
theorem exists_finset_vol_one (h : ∀ᶠ k in cofinite, μf k (K k) = 1) : ∃ S : Finset κ, ∀ k ∉ S, μf k (K k) = 1 :=
  ⟨(eventually_cofinite.1 h).toFinset, fun k hk => by simpa using hk⟩

theorem IsRestrProd.smul_inf [DecidableEq ι] [MeasurableConstSMul G G]
    (h : IsRestrProd p q K μi μf μ) (i : ι) [MeasurableConstSMul (H i) (H i)] {c : ℝ≥0} (hc : c ≠ 0) :
    IsRestrProd p q K (Function.update μi i (c • μi i)) μf (c • μ) := by
  have := h.haar
  have := h.haar_inf
  refine ⟨fun j => ?_, h.haar_fin, h.vol_one, .nnreal_smul _ hc, fun S hS A B hA hB => ?_⟩
  · by_cases e : j = i
    · subst j; rw [Function.update_self]; exact .nnreal_smul _ hc
    · rw [Function.update_of_ne e]; exact h.haar_inf j
  · rw [Measure.smul_apply, h.measure_cyl S hS A B hA hB, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => Function.update μi i (c • μi i) j (A j)) (Finset.mem_univ i),
      Function.update_self, Finset.prod_congr (f := fun j => Function.update μi i (c • μi i) j (A j))
        (g := fun j => μi j (A j)) rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_assoc]

variable [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, BorelSpace (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, SecondCountableTopology (H i)] [∀ i, T2Space (H i)]
  [∀ k, IsTopologicalGroup (P k)] [∀ k, BorelSpace (P k)] [∀ k, LocallyCompactSpace (P k)]
  [∀ k, SecondCountableTopology (P k)] [∀ k, T2Space (P k)]


omit [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [∀ i, SecondCountableTopology (H i)] [∀ k, SecondCountableTopology (P k)] [MeasurableSpace G] [Group G]
  [TopologicalSpace G] in
theorem exists_box_pos (μi : ∀ i, Measure (H i)) (μf : ∀ k, Measure (P k))
    [∀ i, (μi i).IsHaarMeasure] [∀ k, (μf k).IsHaarMeasure] (S : Finset κ) :
    ∃ (A : ∀ i, Set (H i)) (B : ∀ k, Set (P k)), (∀ i, MeasurableSet (A i)) ∧ (∀ k, MeasurableSet (B k)) ∧
      (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k) ≠ 0 ∧ (∏ i, μi i (A i)) * ∏ k ∈ S, μf k (B k) ≠ ∞ := by
  let A := fun i => (Classical.arbitrary (TopologicalSpace.PositiveCompacts (H i)))
  let B := fun k => (Classical.arbitrary (TopologicalSpace.PositiveCompacts (P k)))
  exact ⟨fun i => A i, fun k => B k, fun i => (A i).isCompact.measurableSet, fun k => (B k).isCompact.measurableSet,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => (Measure.measure_pos_of_nonempty_interior _ (A i).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun k _ => (Measure.measure_pos_of_nonempty_interior _ (B k).interior_nonempty).ne'),
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun i _ => (A i).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun k _ => (B k).isCompact.measure_lt_top.ne)⟩



omit [∀ i, SecondCountableTopology (H i)] [∀ k, SecondCountableTopology (P k)] in
theorem IsRestrProd.unique {μ' : Measure G} (h : IsRestrProd p q K μi μf μ) (h' : IsRestrProd p q K μi μf μ') :
    μ = μ' := by
  have := h.haar
  have := h'.haar
  have := h.haar_inf
  have := h.haar_fin
  obtain ⟨S, hS⟩ := exists_finset_vol_one h.vol_one
  obtain ⟨A, B, hA, hB, h0, ht⟩ := exists_box_pos μi μf S
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have e1 := h.measure_cyl S hS A B hA fun k _ => hB k
  rw [e, Measure.smul_apply, h'.measure_cyl S hS A B hA fun k _ => hB k, ENNReal.smul_def, smul_eq_mul] at e1
  have e2 : Measure.haarScalarFactor μ μ' = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 (e1.trans (one_mul _).symm)
  rw [e, e2, one_smul]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

def IsProdMeasure (μi : ∀ w, Measure (GArch σ J w)) (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GAd σ J)) : Prop :=
  IsRestrProd (projArch σ J) (proj σ J) (stabLoc σ J L) μi μf μ

def IsProdMeasureFin (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GFin σ J)) : Prop :=
  IsRestrProd (H := fun _ : Empty => Unit) (fun _ => 1) (projFinLoc σ J) (stabLoc σ J L) (fun e => e.elim) μf μ

section Unfold

omit [NumberField E]

variable {σ J L}

theorem isRestrProd_empty_iff {G κ : Type} {P : κ → Type} [Group G] [∀ k, Group (P k)] [TopologicalSpace G]
    [∀ k, TopologicalSpace (P k)] [MeasurableSpace G] [∀ k, MeasurableSpace (P k)] {q : ∀ k, G →* P k}
    {K : ∀ k, Subgroup (P k)} {μf : ∀ k, Measure (P k)} {μ : Measure G} :
    IsRestrProd (H := fun _ : Empty => Unit) (fun _ => 1) q K (fun e => e.elim) μf μ ↔
      (∀ k, (μf k).IsHaarMeasure) ∧ (∀ᶠ k in cofinite, μf k (K k) = 1) ∧ μ.IsHaarMeasure ∧
      ∀ S : Finset κ, (∀ k ∉ S, μf k (K k) = 1) → ∀ B : ∀ k, Set (P k), (∀ k ∈ S, MeasurableSet (B k)) →
        μ {g | (∀ k ∈ S, q k g ∈ B k) ∧ ∀ k ∉ S, q k g ∈ K k} = ∏ k ∈ S, μf k (B k) :=
  ⟨fun h => ⟨h.2, h.3, h.4, fun S hS B hB => by
      simpa [cyl] using h.5 S hS (fun _ => Set.univ) B (fun e => e.elim) hB⟩,
    fun h => ⟨fun e => e.elim, h.1, h.2.1, h.2.2.1, fun S hS A B _ hB => by simpa [cyl] using h.2.2.2 S hS B hB⟩⟩

theorem isProdMeasureFin_iff {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GFin σ J)} :
    IsProdMeasureFin σ J L μf μ ↔ (∀ v, (μf v).IsHaarMeasure) ∧
      (∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) ∧ μ.IsHaarMeasure ∧
      ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S, μf v (stabLoc σ J L v) = 1) →
        ∀ B : ∀ v, Set (GLoc σ J v), (∀ v ∈ S, MeasurableSet (B v)) →
          μ {g | (∀ v ∈ S, projFinLoc σ J v g ∈ B v) ∧ ∀ v ∉ S, projFinLoc σ J v g ∈ stabLoc σ J L v} =
            ∏ v ∈ S, μf v (B v) := isRestrProd_empty_iff

theorem comp_glue {S : Finset (HeightOneSpectrum (𝓞 F))} (a : ∀ w, GArch σ J w) (b : ∀ v : S, GLoc σ J v) :
    (∀ w, projArch σ J w (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = a w) ∧
    (∀ v : S, proj σ J v (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = b v) ∧
    ∀ v ∉ S, proj σ J v (ofInf σ J (embArchPi σ J a) * embAt σ J S b) = 1 := by
  have h := mem_atPts.1 (embAt_mem σ J S b)
  exact ⟨fun w => by simp [mem_finPts_iff_forall.1 h.1 w], fun v => by simp, fun v hv => by simp [h.2 v hv]⟩

end Unfold

theorem isCompact_of_ext {X : Type} [TopologicalSpace X] {s t : Set X} (h : IsCompact t) (e : ∀ x, x ∈ s ↔ x ∈ t) :
    IsCompact s := (Set.ext e : s = t) ▸ h

variable [Submodule.IsFullLattice E L]

theorem isRestrGroup_GAd : IsRestrGroup (projArch σ J) (proj σ J) (stabLoc σ J L) := by
  refine {
    cont_p := continuous_projArch σ J
    cont_q := continuous_proj σ J
    isOpen_K := isOpen_stabLoc σ J L
    isOpen_all := ?_
    isCompact_cyl := ?_
    exists_comp := ?_ }
  · convert isOpen_levelOpen σ J L using 1
    exact Set.ext fun _ => mem_levelOpen.symm
  · intro S A B hA hB
    have hc := ((((isCompact_univ_pi hA).image (continuous_embArchPi σ J)).image (continuous_ofInf σ J)).mul
      ((isCompact_univ_pi fun v : S => hB v v.2).image (continuous_embAt σ J S))).mul (isCompact_levelOff σ J L S)
    refine isCompact_of_ext hc fun g => ?_
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨e1, e2, e3⟩ := comp_glue (fun w => projArch σ J w g) (projAt σ J S g)
      refine ⟨_, ⟨_, ⟨_, ⟨fun w => projArch σ J w g, fun w _ => h1 w, rfl⟩, rfl⟩, _,
        ⟨projAt σ J S g, fun v _ => h2 v v.2, rfl⟩, rfl⟩, _⁻¹ * g,
        mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩, mul_inv_cancel_left _ _⟩
      · rw [map_mul, map_inv, e1, inv_mul_cancel]
      · rw [map_mul, map_inv, e2 ⟨v, hv⟩, projAt_apply, inv_mul_cancel]
      · rw [map_mul, map_inv, e3 v hv, inv_one, one_mul]; exact h3 v hv
    · rintro ⟨_, ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, k, hk, rfl⟩
      obtain ⟨e1, e2, e3⟩ := comp_glue a b
      obtain ⟨k1, k2, k3⟩ := mem_levelOff.1 hk
      refine ⟨fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · rw [map_mul, e1, mem_finPts_iff_forall.1 k1, mul_one]; exact ha w trivial
      · rw [map_mul, e2 ⟨v, hv⟩, k2 v hv, mul_one]; exact hb ⟨v, hv⟩ trivial
      · rw [map_mul, e3 v hv, one_mul]; exact k3 v hv
  · intro S x y
    exact ⟨_, (comp_glue x y).1, (comp_glue x y).2.1, fun v hv => by
      rw [(comp_glue x y).2.2 v hv]; exact one_mem _⟩

theorem isRestrGroup_GFin :
    IsRestrGroup (H := fun _ : Empty => Unit) (fun _ => 1) (projFinLoc σ J) (stabLoc σ J L) := by
  refine {
    cont_p := fun e => e.elim
    cont_q := continuous_projFinLoc σ J
    isOpen_K := isOpen_stabLoc σ J L
    isOpen_all := ?_
    isCompact_cyl := ?_
    exists_comp := ?_ }
  · simpa using (isRestrGroup_GAd σ J L).isOpen_all.preimage (continuous_ofFin σ J)
  · intro S A B _ hB
    have := (Function.LeftInverse.isClosedEmbedding (projFin_ofFin σ J) (continuous_projFin σ J)
      (continuous_ofFin σ J)).isCompact_preimage
      ((isRestrGroup_GAd σ J L).isCompact_cyl S (fun _ => {1}) B (fun _ => isCompact_singleton) hB)
    convert this using 1
    ext g
    simp [mem_cyl]
  · intro S _ y
    obtain ⟨g, -, h2, h3⟩ := (isRestrGroup_GAd σ J L).exists_comp S 1 y
    exact ⟨projFin σ J g, fun e => e.elim, by simpa using h2, by simpa using h3⟩

section Away

variable (T : Finset (HeightOneSpectrum (𝓞 F)))

omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem exists_away (S : Finset {v // v ∉ T}) (x : ∀ w, GArch σ J w) (y : ∀ v : S, GLoc σ J v.1) :
    ∃ g ∈ awayPts σ J T, (∀ w, projArch σ J w g = x w) ∧ (∀ v : S, proj σ J v.1 g = y v) ∧
      ∀ v ∉ S, proj σ J v.1 g ∈ stabLoc σ J L v := by
  classical
  obtain ⟨e1, e2, e3⟩ := comp_glue (S := S.map (Function.Embedding.subtype _)) x fun v =>
    y ⟨⟨v.1, Finset.property_of_mem_map_subtype S v.2⟩, by
      obtain ⟨u, hu, e⟩ := Finset.mem_map.1 v.2
      convert hu using 1
      exact Subtype.ext e.symm⟩
  exact ⟨_, mem_awayPts.2 fun v hv => e3 v fun h => Finset.property_of_mem_map_subtype S h hv, e1,
    fun v => e2 ⟨v.1.1, Finset.mem_map_of_mem _ v.2⟩, fun v hv => by
      rw [e3 v (by simpa [v.2] using hv)]; exact one_mem _⟩

instance (U : Subgroup (GAd σ J)) : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _

end Away

def stabCompacts (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (GLoc σ J v) :=
  ⟨⟨stabLoc σ J L v, isCompact_stabLoc σ J L v⟩, by
    rw [(isOpen_stabLoc σ J L v).interior_eq]; exact ⟨1, one_mem _⟩⟩

def haarLoc (v : HeightOneSpectrum (𝓞 F)) : Measure (GLoc σ J v) := Measure.haarMeasure (stabCompacts σ J L v)

instance (v : HeightOneSpectrum (𝓞 F)) : (haarLoc σ J L v).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

@[simp] theorem haarLoc_stabLoc (v : HeightOneSpectrum (𝓞 F)) : haarLoc σ J L v (stabLoc σ J L v) = 1 :=
  Measure.haarMeasure_self (K₀ := stabCompacts σ J L v)

variable {σ J L}


end GlobalTheory.AdelicU

end
