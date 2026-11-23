module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctions
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatMeasurable

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def oneInf : MatInf E j := fun _ a b => (1 : Matrix (Fin j) (Fin j) ℂ) a b

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := rfl

theorem detNorm_oneInf : 0 < detNorm E j (oneInf E j) := by
  unfold detNorm
  simp [of_oneInf]

variable {E j}

theorem isUnit_det_of_pos {g : MatInf E j} (hg : 0 < detNorm E j g) (w : InfinitePlace E) :
    IsUnit (Matrix.of (g w)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hz : detNorm E j g = 0 := by
    unfold detNorm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h0])
  linarith

def act (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) : VecInf E j →ₗ[ℤ] VecInf E j where
  toFun x w := A w *ᵥ x w
  map_add' x y := by funext w; simp [Matrix.mulVec_add]
  map_smul' c x := by funext w; exact Matrix.mulVec_smul (A w) c (x w)

theorem act_apply (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x : VecInf E j) (w : InfinitePlace E) :
    act A x w = A w *ᵥ x w := rfl

theorem act_act {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ} (h : ∀ w, A w * B w = 1) (x : VecInf E j) :
    act A (act B x) = x := by
  funext w
  simp only [act_apply, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem latAt_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) :
    latAt E j Λ g = (latAt E j Λ (oneInf E j)).map (act fun w => (Matrix.of (g w))⁻¹) := by
  unfold latAt
  rw [Submodule.map_span, ← Set.image_comp]
  congr 2
  funext y w
  simp [act_apply, of_oneInf]

private lemma dualAt_act_transpose (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x y : VecInf E j) :
    ∑ w, (act A x w ⬝ᵥ y w).re = ∑ w, (x w ⬝ᵥ act (fun w => (A w)ᵀ) y w).re := by
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [act_apply]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

theorem dualAt_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) :
    dualAt E j (L.map (act A)) = (dualAt E j L).map (act fun w => (B w)ᵀ) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  have hT : ∀ y, act (fun w => (B w)ᵀ) (act (fun w => (A w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, h w, Matrix.transpose_one]) y
  have hT' : ∀ y, act (fun w => (A w)ᵀ) (act (fun w => (B w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, hBA w, Matrix.transpose_one]) y
  unfold dualAt
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    refine ⟨act (fun w => (A w)ᵀ) y, fun x hx => ?_, hT y⟩
    obtain ⟨z, hz⟩ := hy _ (Submodule.mem_map_of_mem hx)
    exact ⟨z, by rw [← dualAt_act_transpose A x y]; exact hz⟩
  · rintro ⟨y', hy', rfl⟩ x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz⟩ := hy' x' hx'
    exact ⟨z, by rw [dualAt_act_transpose A x' _, hT' y']; exact hz⟩

theorem tsum_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) (Φ : VecInf E j → ENNReal) :
    ∑' x : {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0}, Φ x.1 =
      ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ (act A x.1) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  let e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0} :=
    { toFun := fun x => ⟨act A x.1, Submodule.mem_map_of_mem x.2.1, fun h0 => x.2.2 (by
          rw [← act_act hBA x.1, h0, map_zero])⟩
      invFun := fun y => ⟨act B y.1, by
          obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2.1
          rw [← hxy, act_act hBA]
          exact hx, fun h0 => y.2.2 (by rw [← act_act h y.1, h0, map_zero])⟩
      left_inv := fun x => Subtype.ext (act_act hBA x.1)
      right_inv := fun y => Subtype.ext (act_act h y.1) }
  exact (e.tsum_eq (fun x => Φ x.1)).symm

def pairL (y : VecInf E j) : VecInf E j →ₗ[ℝ] ℝ where
  toFun x := ∑ w, (x w ⬝ᵥ y w).re
  map_add' x x' := by simp [add_dotProduct, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_dotProduct, Finset.mul_sum]

theorem pairL_injective : Function.Injective (pairL : VecInf E j → _) := by
  classical
  intro y y' hyy
  have key : ∀ (w : InfinitePlace E) (a : Fin j) (c : ℂ), (c * y w a).re = (c * y' w a).re := by
    intro w a c
    have hv : ∀ z : VecInf E j, pairL z (Pi.single w (Pi.single a c)) = (c * z w a).re := by
      intro z
      show ∑ v, ((Pi.single w (Pi.single a c) : VecInf E j) v ⬝ᵥ z v).re = _
      rw [Finset.sum_eq_single w (fun v _ hne => by simp [hne]) (by simp)]
      simp [single_dotProduct]
    rw [← hv y, ← hv y', hyy]
  funext w a
  apply Complex.ext
  · simpa using key w a 1
  · simpa using key w a Complex.I

theorem countable_dualAt (L : Submodule ℤ (VecInf E j)) (hL : Submodule.span ℝ (L : Set (VecInf E j)) = ⊤) :
    Countable (dualAt E j L) := by
  have hsym : ∀ x y : VecInf E j, pairL y x = pairL x y := fun x y => by
    show ∑ w, (x w ⬝ᵥ y w).re = ∑ w, (y w ⬝ᵥ x w).re
    exact Finset.sum_congr rfl fun w _ => by rw [dotProduct_comm]
  have hint : ∀ y ∈ dualAt E j L, ∀ x ∈ L, ∃ z : ℤ, pairL x y = z := by
    intro y hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨z, hz⟩ := hy' x hx
      exact ⟨z, by rw [← hsym x y]; exact hz⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨c, hc⟩ := h2
      exact ⟨a + c, by rw [map_add (f := _), ha, hc]; push_cast; ring⟩
    | smul n y _ h1 =>
      obtain ⟨a, ha⟩ := h1
      exact ⟨n * a, by rw [map_zsmul, ha, zsmul_eq_mul]; push_cast; ring⟩
  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set (VecInf E j))
  haveI : Finite b := hbli.finite
  choose φ hφ using fun (y : dualAt E j L) (i : b) => hint y.1 y.2 i.1 (hbL i.2)
  refine Function.Injective.countable (f := φ) ?_
  intro y y' hyy
  apply Subtype.ext
  apply pairL_injective
  refine LinearMap.ext_on (s := (b : Set (VecInf E j))) (hbspan.trans hL) ?_
  intro x hx
  have e1 := hφ y ⟨x, hx⟩
  have e2 := hφ y' ⟨x, hx⟩
  dsimp only at e1 e2
  rw [hsym x y.1, hsym x y'.1, e1, e2, hyy]

theorem measurable_of_continuous {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (w : InfinitePlace E) (f : Matrix (Fin j) (Fin j) ℂ → β) (hf : Continuous f) :
    Measurable fun g : MatInf E j => f (Matrix.of (g w)) := by
  have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => f (Matrix.of (g w)) :=
    hf.comp (continuous_apply w)
  exact hc.measurable

theorem measurable_detNorm : Measurable (detNorm E j) := by
  unfold detNorm
  exact Finset.measurable_prod _ fun w _ =>
    measurable_of_continuous w (fun M => ‖M.det‖ ^ 2) (continuous_id.matrix_det.norm.pow 2)

theorem measurable_act_inv (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))⁻¹) x := by
  refine Measurable.of_eval fun w => ?_
  simp only [act_apply]
  have hinv : ∀ M : Matrix (Fin j) (Fin j) ℂ, M⁻¹ = (M.det)⁻¹ • M.adjugate := fun M => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hinv]
  have hd : Measurable fun g : MatInf E j => (Matrix.of (g w)).det :=
    measurable_of_continuous w (fun M => M.det) continuous_id.matrix_det
  refine Measurable.of_eval fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun b _ => ?_
  exact (hd.inv.mul (measurable_of_continuous w (fun M => M.adjugate a b)
    (continuous_id.matrix_adjugate.matrix_elem a b))).mul_const _

theorem measurable_act_transpose (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))ᵀ) x := by
  refine Measurable.of_eval fun w => ?_
  simp only [act_apply]
  exact measurable_of_continuous w (fun M => Mᵀ *ᵥ x w)
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const)

theorem measurable_indicator_of_eqOn {f f' : MatInf E j → ENNReal} (hf' : Measurable f')
    (h : ∀ g, 0 < detNorm E j g → f g = f' g) :
    Measurable fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator f g := by
  have hS : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
    measurableSet_lt measurable_const measurable_detNorm
  convert hf'.indicator hS using 1
  funext g
  exact congrFun (Set.indicator_congr fun g hg => h g hg) g

private lemma countable_nonzero_lattice_vectors (L : Submodule ℤ (VecInf E j)) [Countable L] :
    Countable {x : VecInf E j // x ∈ L ∧ x ≠ 0} :=
  Function.Injective.countable (f := fun x : {x : VecInf E j // x ∈ L ∧ x ≠ 0} => (⟨x.1, x.2.1⟩ : L))
    fun _ _ hab => Subtype.ext (congrArg (fun y : L => (y : VecInf E j)) hab)

theorem measurable_latFun : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsFullLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  intro E _ _ hE j wt Φ hw hΦ Λ hΛ
  obtain ⟨κ, -, hK⟩ := (_root_.GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  obtain ⟨⟨hd, hz⟩, -, -, -⟩ := hK (oneInf E j) (detNorm_oneInf E j)
  haveI : Countable (latAt E j Λ (oneInf E j)) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  haveI : Countable (dualAt E j (latAt E j Λ (oneInf E j))) := countable_dualAt _ hz.span_top
  haveI := countable_nonzero_lattice_vectors (latAt E j Λ (oneInf E j))
  haveI := countable_nonzero_lattice_vectors (dualAt E j (latAt E j Λ (oneInf E j)))
  have hinv : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))⁻¹ * Matrix.of (g w) = 1 :=
    fun g hg w => Matrix.nonsing_inv_mul _ (isUnit_det_of_pos hg w)
  have htr : ∀ g : MatInf E j, 0 < detNorm E j g →
      ∀ w, (Matrix.of (g w))ᵀ * ((Matrix.of (g w))⁻¹)ᵀ = 1 := by
    intro g hg w
    rw [← Matrix.transpose_mul, hinv g hg w, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_indicator_of_eqOn (f' := fun g => wt (κ / detNorm E j g))
      (hw.comp (measurable_const.div measurable_detNorm)) fun g hg => by simp only [(hK g hg).2.1]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ (oneInf E j) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))⁻¹) x.1))
      (Measurable.tsum fun x => hΦ.comp (measurable_act_inv x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, tsum_map _ (hinv g hg) Φ]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ (oneInf E j)) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))ᵀ) x.1))
      (Measurable.tsum fun x => hΦ.comp (measurable_act_transpose x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, dualAt_map _ (hinv g hg), tsum_map _ (htr g hg) Φ]

end GlobalTheory.LatMeasurable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolume
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.StrictDomain

theorem null_of_translate_disjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X)
    (U D : Set X) (hc : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x)
    (hinv : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hmul : ∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x))
    (hi : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hU : MeasurableSet U) (hUS : ∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) (hDU : D ⊆ U)
    (hcov : ∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) →
      covol S μ A = μ (A ∩ D))
    (γ : X) (hγ : γ ∈ S) (B : Set X) (hB : MeasurableSet B) (hfin : μ B ≠ ⊤)
    (hBD : B ⊆ D) (hBγ : ∀ x ∈ B, γ * x ∈ D) (hdis : ∀ x ∈ B, γ * x ∉ B) : μ B = 0 := by
  obtain ⟨δ, hδ, hδγ, hγδ⟩ := hi γ hγ
  set A : Set X := U ∩ ⋃ ε ∈ S, (fun x => ε * x) ⁻¹' B with hA
  have hmemA : ∀ x, x ∈ A ↔ x ∈ U ∧ ∃ ε ∈ S, ε * x ∈ B := by
    intro x
    simp [hA]
  have hAm : MeasurableSet A :=
    hU.inter (MeasurableSet.biUnion hc fun ε hε => hm ε hε hB)
  have hAinv : ∀ η ∈ S, ∀ x ∈ A, η * x ∈ A := by
    intro η hη x hx
    obtain ⟨hxU, ε, hε, hεx⟩ := (hmemA x).1 hx
    obtain ⟨η', hη', h1, -⟩ := hi η hη
    obtain ⟨κ, hκ, hκe⟩ := hmul ε hε η' hη'
    exact (hmemA _).2 ⟨hUS η hη x hxU, κ, hκ, by rw [hκe, h1]; exact hεx⟩
  have hle : μ (A ∩ D) ≤ μ B := by
    rw [← hcov A hAm Set.inter_subset_left hAinv]
    unfold covol
    exact iInf_le_of_le B (iInf_le_of_le hB (iInf_le_of_le (fun x hx => ((hmemA x).1 hx).2) le_rfl))
  set B' : Set X := (fun x => δ * x) ⁻¹' B with hB'
  have hB'm : MeasurableSet B' := hm δ hδ hB
  have hB'μ : μ B' = μ B := by
    rw [hB', ← Measure.map_apply (hm δ hδ) hB, hinv δ hδ]
  have hdj : Disjoint B B' := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have := hdis _ hx'
    rw [hγδ] at this
    exact this hx
  have hsub : B ∪ B' ⊆ A ∩ D := by
    rintro x (hx | hx)
    · obtain ⟨κ, hκ, hκe⟩ := hmul δ hδ γ hγ
      exact ⟨(hmemA x).2 ⟨hDU (hBD hx), κ, hκ, by rw [hκe, hδγ]; exact hx⟩, hBD hx⟩
    · have hxD : x ∈ D := by
        have := hBγ _ hx
        rwa [hγδ] at this
      exact ⟨(hmemA x).2 ⟨hDU hxD, δ, hδ, hx⟩, hxD⟩
  have h2 : μ B + μ B ≤ μ B + 0 := by
    calc μ B + μ B = μ (B ∪ B') := by rw [measure_union hdj hB'm, hB'μ]
      _ ≤ μ (A ∩ D) := measure_mono hsub
      _ ≤ μ B + 0 := by rw [add_zero]; exact hle
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h2) zero_le

theorem measure_inter_translate_eq_zero : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  intro X _ _ _ S μ _ U D hc hm hinv hmul hi hU hUS hD hDU hcov γ hγ hfree
  obtain ⟨V, hVm, hV⟩ := exists_seq_separating X MeasurableSet.univ (Set.univ : Set X)
  have key : ∀ (W : Set X), MeasurableSet W → ∀ m : ℕ,
      μ (D ∩ (fun x => γ * x) ⁻¹' D ∩ W ∩ (fun x => γ * x) ⁻¹' Wᶜ ∩ spanningSets μ m) = 0 := by
    intro W hW m
    refine null_of_translate_disjoint S μ U D hc hm hinv hmul hi hU hUS hDU hcov γ hγ _
      ((((hD.inter (hm γ hγ hD)).inter hW).inter (hm γ hγ hW.compl)).inter
        (measurableSet_spanningSets μ m))
      (ne_top_of_le_ne_top (measure_spanningSets_lt_top μ m).ne
        (measure_mono Set.inter_subset_right)) ?_ ?_ ?_
    · intro x hx
      exact hx.1.1.1.1
    · intro x hx
      exact hx.1.1.1.2
    · intro x hx hx'
      exact hx.1.2 hx'.1.1.2
  have hsub : {x | x ∈ D ∧ γ * x ∈ D} ⊆ ⋃ n : ℕ, ⋃ m : ℕ,
      ((D ∩ (fun x => γ * x) ⁻¹' D ∩ V n ∩ (fun x => γ * x) ⁻¹' (V n)ᶜ ∩ spanningSets μ m) ∪
       (D ∩ (fun x => γ * x) ⁻¹' D ∩ (V n)ᶜ ∩ (fun x => γ * x) ⁻¹' (V n)ᶜᶜ ∩ spanningSets μ m)) := by
    rintro x ⟨hx, hγx⟩
    have hne := hfree x (hDU hx)
    obtain ⟨n, hn⟩ : ∃ n, ¬ (γ * x ∈ V n ↔ x ∈ V n) := by
      by_contra h
      push_neg at h
      exact hne (hV _ (Set.mem_univ _) _ (Set.mem_univ _) h)
    have hm' : x ∈ ⋃ m, spanningSets μ m := by rw [iUnion_spanningSets]; exact Set.mem_univ _
    obtain ⟨m, hm'⟩ := Set.mem_iUnion.1 hm'
    refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
    by_cases hxV : x ∈ V n
    · exact Or.inl ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun _ => hxV, fun _ => h⟩⟩, hm'⟩
    · exact Or.inr ⟨⟨⟨⟨hx, hγx⟩, hxV⟩, fun h => hn ⟨fun h' => (h h').elim, fun h' => (hxV h').elim⟩⟩, hm'⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => measure_iUnion_null fun m => ?_)
  exact measure_union_null (key _ (hVm n) m) (key _ (hVm n).compl m)

end GlobalTheory.StrictDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPl
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov.Transp

private theorem measurePreserving_curry_symm_pi (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A).symm (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ)
      (Measure.pi fun _ : ι × κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ A).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have hpre : (MeasurableEquiv.curry ι κ A).symm ⁻¹' Set.univ.pi s
      = Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext f
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem curry_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ A) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h := MeasurePreserving.symm _ (measurePreserving_curry_symm_pi ι κ A μ)
  rwa [MeasurableEquiv.symm_symm] at h

theorem swap_mp (ι κ A : Type) [Fintype ι] [Fintype κ] [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] :
    MeasurePreserving (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v)
      (Measure.pi fun _ => Measure.pi fun _ => μ) (Measure.pi fun _ => Measure.pi fun _ => μ) := by
  have h1 := measurePreserving_curry_symm_pi ι κ A μ
  have h2 := measurePreserving_piCongrLeft (fun _ : κ × ι => μ) (Equiv.prodComm ι κ)
  have h3 := curry_mp κ ι A μ
  have key : (fun (f : ι → κ → A) (v : κ) (i : ι) => f i v) =
      (MeasurableEquiv.curry κ ι A) ∘ (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => A) (Equiv.prodComm ι κ)) ∘
        (MeasurableEquiv.curry ι κ A).symm := by
    funext f v i
    simp [MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
  rw [key]
  exact h3.comp (h2.comp h1)

theorem glue_mp {ι A B A' B' : Type} [Fintype ι] [MeasureSpace A] [MeasureSpace B] [MeasureSpace A'] [MeasureSpace B']
    [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]
    [SigmaFinite (volume : Measure A')] [SigmaFinite (volume : Measure B')]
    {f : A' → ι → A} {g : B' → ι → B}
    (hf : MeasurePreserving f volume (Measure.pi fun _ : ι => (volume : Measure A)))
    (hg : MeasurePreserving g volume (Measure.pi fun _ : ι => (volume : Measure B))) :
    MeasurePreserving (fun (p : A' × B') (v : ι) => (f p.1 v, g p.2 v)) volume
      (Measure.pi fun _ : ι => (volume : Measure (A × B))) := by
  have h1 := hf.prod hg
  have h2 := MeasurePreserving.symm _
    (measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => (volume : Measure A)) (fun _ => (volume : Measure B)))
  exact h2.comp h1

theorem sigmaFinite_volume_pi_family (I A : Type) [Fintype I] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → A)) := by
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure A))
  infer_instance

theorem sigmaFinite_volume_pi_double_family (I J A : Type) [Fintype I] [Fintype J] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    SigmaFinite (volume : Measure (I → J → A)) := by
  have := sigmaFinite_volume_pi_family J A
  show SigmaFinite (Measure.pi fun _ : I => (volume : Measure (J → A)))
  infer_instance

theorem swap_vol (I ι A : Type) [Fintype I] [Fintype ι] [MeasureSpace A] [SigmaFinite (volume : Measure A)] :
    MeasurePreserving (fun (f : I → ι → A) (v : ι) (i : I) => f i v) volume
      (Measure.pi fun _ : ι => (volume : Measure (I → A))) := by
  have := sigmaFinite_volume_pi_family I A
  exact swap_mp I ι A volume

end GlobalTheory.DegVol.RefCov.Transp

namespace GlobalTheory.DegVol.RefCov

theorem atP_measurePreserving : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ),
    MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume
      (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  intro ι _ k r j β
  have s0 := Transp.sigmaFinite_volume_pi_family (Fin (k + 1)) ℂ
  have s1 := Transp.sigmaFinite_volume_pi_family (UTin β) ℂ
  have s2 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} (Fin (k + 1) → ℂ)
  have s3 := Transp.sigmaFinite_volume_pi_family {p : UT r // j ≤ p.1.1.val} ℂ
  have s4 := Transp.sigmaFinite_volume_pi_family {a : Fin r // j ≤ a.val} ℝ
  have t1 := Transp.sigmaFinite_volume_pi_double_family (UTin β) ι ℂ
  have t2 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have t3 := Transp.sigmaFinite_volume_pi_double_family {p : UT r // j ≤ p.1.1.val} ι ℂ
  have t4 := Transp.sigmaFinite_volume_pi_double_family {a : Fin r // j ≤ a.val} ι ℝ
  have p1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ℝ)))
    infer_instance
  have p2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ))))
    infer_instance
  have q1 : SigmaFinite (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))) := by
    show SigmaFinite ((volume : Measure ({p : UT r // j ≤ p.1.1.val} → ι → ℂ)).prod (volume : Measure ({a : Fin r // j ≤ a.val} → ι → ℝ)))
    infer_instance
  have q2 : SigmaFinite (volume : Measure (({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) × (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ)))) := by
    show SigmaFinite ((volume : Measure ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ)).prod (volume : Measure (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))))
    infer_instance
  have e1 := Transp.swap_vol (UTin β) ι ℂ
  have e2 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι (Fin (k + 1) → ℂ)
  have e3 := Transp.swap_vol {p : UT r // j ≤ p.1.1.val} ι ℂ
  have e4 := Transp.swap_vol {a : Fin r // j ≤ a.val} ι ℝ
  have g := Transp.glue_mp e1 (Transp.glue_mp e2 (Transp.glue_mp e3 e4))
  exact g

end GlobalTheory.DegVol.RefCov
end
end

