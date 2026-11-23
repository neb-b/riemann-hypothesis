module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
public import Formalism.PeriodIntegrals.Bundle0020
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.GenericWeilRepresentation
section
open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Bruhat

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_bruhat_left (μS : Measure G) [SFinite μS] (S : Set G) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ β : G → ℝ≥0∞, Measurable β ∧ ∀ y : G, ∫⁻ s, β (s⁻¹ * y) ∂μS = 1 := by

  obtain ⟨O, hOo, hOc, hcov⟩ : ∃ O : ℕ → Set G, (∀ n, IsOpen (O n)) ∧
      (∀ n, ∃ L : Set G, IsCompact L ∧ O n ⊆ L) ∧ ∀ y : G, ∃ n, y ∈ O n := by
    let K := CompactExhaustion.choice G
    exact ⟨fun n => interior (K (n + 1)), fun n => isOpen_interior,
      fun n => ⟨K (n + 1), K.isCompact _, interior_subset⟩,
      fun y => ⟨K.find y, K.subset_interior_succ _ (K.mem_find y)⟩⟩

  obtain ⟨f, hf⟩ : ∃ f : ℕ → G → ℝ≥0∞,
      ∀ n y, f n y = ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS := ⟨_, fun _ _ => rfl⟩
  have hm : ∀ n y, Measurable (fun s : G => (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) :=
    fun n y => (measurable_one.indicator (hOo n).measurableSet).comp (measurable_inv.mul_const y)
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    have h2 : Measurable (fun q : G × G => (O n).indicator (1 : G → ℝ≥0∞) (q.2⁻¹ * q.1)) :=
      (measurable_one.indicator (hOo n).measurableSet).comp (measurable_snd.inv.mul measurable_fst)
    rw [show f n = fun y => ∫⁻ s, (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS from funext (hf n)]
    exact h2.lintegral_prod_right'
  have hf_eq : ∀ n y, f n y = μS ((fun s : G => s⁻¹ * y) ⁻¹' O n) := by
    intro n y
    rw [hf n y, ← lintegral_indicator_one ((hOo n).measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hf_fin : ∀ n y, f n y < ⊤ := by
    intro n y
    obtain ⟨L, hL, hOL⟩ := hOc n
    have hc : IsCompact ((fun k : G => y * k⁻¹) '' L) := hL.image (by fun_prop)
    rw [hf_eq]
    refine lt_of_le_of_lt (measure_mono ?_) (hfin _ hc)
    intro s hs
    exact ⟨s⁻¹ * y, hOL hs, by group⟩
  have hf_pos : ∀ n y, y ∈ O n → 0 < f n y := by
    intro n y hy
    rw [hf_eq]
    refine hpos _ (IsOpen.preimage (f := fun s : G => s⁻¹ * y) (by fun_prop) (hOo n)) ?_
    show (1 : G)⁻¹ * y ∈ O n
    rwa [inv_one, one_mul]
  have hf_inv : ∀ n, ∀ t ∈ S, ∀ y, f n (t⁻¹ * y) = f n y := by
    intro n t ht y
    calc f n (t⁻¹ * y) = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) ((t * r)⁻¹ * y) ∂μS := by
          rw [hf n]
          refine lintegral_congr fun r => ?_
          rw [mul_inv_rev, mul_assoc]
      _ = ∫⁻ r, (O n).indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂(μS.map (fun x => t * x)) :=
          (lintegral_map (hm n y) (measurable_const_mul t)).symm
      _ = f n y := by rw [hinv t ht, hf n y]

  have hZm : Measurable (fun x : G => ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x) :=
    Measurable.tsum fun n => (measurable_const.mul (hfm n).inv).mul (hfm n)
  have hTm : Measurable (fun x : G =>
      ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) :=
    Measurable.tsum fun n =>
      (measurable_const.mul (hfm n).inv).mul (measurable_one.indicator (hOo n).measurableSet)
  refine ⟨fun x => (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * (O n).indicator (1 : G → ℝ≥0∞) x) *
      (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n x)⁻¹ * f n x)⁻¹, hTm.mul hZm.inv, fun y => ?_⟩
  have hterm : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    rcases eq_or_ne (f n y) 0 with h | h
    · rw [h, mul_zero]
      exact zero_le
    · rw [mul_assoc, ENNReal.inv_mul_cancel h (hf_fin n y).ne, mul_one]
  have hZtop : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hZ0 : (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) ≠ 0 := by
    obtain ⟨n, hn⟩ := hcov y
    have hpos' := hf_pos n y hn
    have h1 : (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [mul_assoc, ENNReal.inv_mul_cancel hpos'.ne' (hf_fin n y).ne, mul_one]
    refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum n))
    rw [h1]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) n
  have hae : ∀ᵐ s ∂μS, s ∈ S := by
    rw [ae_iff]
    exact hSc
  calc ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n (s⁻¹ * y))⁻¹ * f n (s⁻¹ * y))⁻¹ ∂μS
        = ∫⁻ s, (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y)) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ ∂μS := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with s hs
        have hs' : ∀ n, f n (s⁻¹ * y) = f n y := fun n => hf_inv n s hs y
        simp only [hs']
    _ = (∫⁻ s, ∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ *
          (O n).indicator (1 : G → ℝ≥0∞) (s⁻¹ * y) ∂μS) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hZ0)
    _ = (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y) *
          (∑' n, (2 : ℝ≥0∞)⁻¹ ^ n * (f n y)⁻¹ * f n y)⁻¹ := by
        rw [lintegral_tsum fun n => ((hm n y).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun n => ?_
        rw [lintegral_const_mul _ (hm n y), ← hf n y]
    _ = 1 := ENNReal.mul_inv_cancel hZ0 hZtop

theorem weil_of_bruhat (μG μS : Measure G) [SFinite μG] [μG.IsMulLeftInvariant] [SFinite μS]
    (S : Set G) (_hS : MeasurableSet S) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν := by
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat_left μS S hSc hinv hpos hfin
  refine ⟨μG.withDensity β, fun f hf => ?_⟩
  have hF : Measurable (fun x : G => ∫⁻ s, f (s * x) ∂μS) :=
    (hf.comp (measurable_snd.mul measurable_fst)).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hF]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, β (s⁻¹ * x) ∂μS) * f x ∂μG := by
        simp only [hβ, one_mul]
    _ = ∫⁻ x, ∫⁻ s, β (s⁻¹ * x) * f x ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        exact (lintegral_mul_const _ (hβm.comp (measurable_inv.mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, β (s⁻¹ * x) * f x ∂μG ∂μS :=
        lintegral_lintegral_swap ((hβm.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, β x * f (s * x) ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          (lintegral_mul_left_eq_self (fun x => β (s⁻¹ * x) * f x) s).symm
    _ = ∫⁻ x, ∫⁻ s, β x * f (s * x) ∂μS ∂μG :=
        lintegral_lintegral_swap ((hβm.comp measurable_snd).mul
          (hf.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, (β * fun x => ∫⁻ s, f (s * x) ∂μS) x ∂μG := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul _ (hf.comp (measurable_id.mul_const x))

end Bruhat

theorem generic_weil_representation : GenWeil := by
  unfold GenWeil
  intro G _ _ _ _ _ _ _ _ μG μS _ _ _ S hS hSc hinv hpos hfin
  exact weil_of_bruhat μG μS S hS hSc hinv hpos hfin

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs
section
noncomputable section

open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

def instFvec {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    Fin r ⊕ Fin r ⊕ Unit → Fin I.n → I.E
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def instBmat (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) : Matrix (Fin I.n) (Fin r ⊕ Fin r ⊕ Unit) ℂ :=
  Matrix.of fun i j => rv I v (instFvec e f z j) i

def InstExpFix : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ), X.IsHermitian → ∀ w : Fin n → ℂ,
    NormedSpace.exp X *ᵥ w = w ↔ X *ᵥ w = 0

def InstAdaptBasis : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (ε' : Fin n → Bool) (T : Finset (Fin n)),
      Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε' ∧
      (∀ i ∈ T, ∃ c : ι → ℂ, A *ᵥ Pi.single i 1 = B *ᵥ c) ∧
      (∀ j : ι, ∃ c : Fin n → ℂ, (∀ i ∉ T, c i = 0) ∧ B *ᵥ Pi.single j 1 = A *ᵥ c)

def InstPlaceDecomp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) ι ℂ),
    IsUnit (Bᴴ * Formalism.REAL.Jm ε * B) →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε g → g * B = B →
    ∃ k p σ : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inUJ ε k ∧ Formalism.REAL.inUJ ε p ∧ Formalism.REAL.inUJ ε σ ∧
      k * B = B ∧ p * B = B ∧ σ * B = B ∧ g = k * p ∧ σ * σ = 1 ∧ σ * p * σ * p = 1 ∧
      ∃ C : Set (Formalism.REAL.UJ ε), IsCompact C ∧ (1 : Formalism.REAL.UJ ε) ∈ interior C ∧
        ∀ x y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.uMat y * k = k * Formalism.MainNotions.S.uMat x → (y ∈ C ↔ x ∈ C)

def InstFrameGram : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E), IsFrame I e f z →
    ∀ v, IsUnit ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ModOne
section
open MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Conj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    N ≃* N where
  toFun x := ⟨g * x * g⁻¹, h1 x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, h2 x x.2⟩
  left_inv x := Subtype.ext (show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group)
  right_inv x := Subtype.ext (show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x by group)
  map_mul' x y := Subtype.ext (show g * ((x : G) * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group)

theorem continuous_conjSub (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2) := by
  show Continuous fun x : N => (⟨g * x * g⁻¹, h1 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

theorem continuous_conjSub_symm (N : Subgroup G) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) : Continuous (conjSub N g h1 h2).symm := by
  show Continuous fun x : N => (⟨g⁻¹ * x * g, h2 x x.2⟩ : N)
  exact Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

variable [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem conj_eq_smul (N : Subgroup G) (hN : IsClosed (N : Set G)) (g : G) (h1 : ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, g⁻¹ * x * g ∈ N) :
    ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN := by
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := by
    first
      | exact TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
      | exact Topology.IsInducing.subtypeVal.secondCountableTopology
      | exact inducing_subtype_val.secondCountableTopology
      | infer_instance
  have hφc := continuous_conjSub N g h1 h2
  have hφs := continuous_conjSub_symm N g h1 h2
  haveI := MulEquiv.isHaarMeasure_map (Measure.haar : Measure N) (conjSub N g h1 h2) hφc hφs
  refine ⟨Measure.haarScalarFactor ((Measure.haar : Measure N).map (conjSub N g h1 h2)) Measure.haar, ?_⟩
  have hc : Measurable (fun x : G => g * x * g⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : (fun x : G => g * x * g⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (conjSub N g h1 h2) :=
    rfl
  unfold haarSub
  rw [Measure.map_map hc measurable_subtype_coe, hcomp,
    ← Measure.map_map measurable_subtype_coe hφc.measurable]
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul ((Measure.haar : Measure N).map (conjSub N g h1 h2))
    Measure.haar]
  rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]

end Conj

theorem genModOne_of (hHaar : GenHaarSub) : GenModOne := by
  intro G _ _ _ _ _ _ _ _ N H hN hnorm hdec h hh
  obtain ⟨_, _, _, _, hfin, hpos⟩ := hHaar G N hN
  have hm : ∀ a : G, Measurable (fun x : G => a * x * a⁻¹) := fun a =>
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : ∀ a b : G, (fun x : G => a * b * x * (a * b)⁻¹) =
      (fun x : G => a * x * a⁻¹) ∘ (fun x : G => b * x * b⁻¹) := fun a b => by
    funext x
    simp only [Function.comp, mul_inv_rev, mul_assoc]
  have hmap : ∀ a b : G, (haarSub N hN).map (fun x => a * b * x * (a * b)⁻¹) =
      ((haarSub N hN).map (fun x => b * x * b⁻¹)).map (fun x => a * x * a⁻¹) := fun a b => by
    rw [Measure.map_map (hm a) (hm b), hcomp]
  have hid : ∀ a : G, (haarSub N hN).map (fun x => a * a⁻¹ * x * (a * a⁻¹)⁻¹) = haarSub N hN :=
    fun a => by
      simp only [mul_inv_cancel, one_mul, inv_one, mul_one]
      exact Measure.map_id'
  have hsc : ∀ g ∈ H, ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN :=
    fun g hg => conj_eq_smul N hN g (hnorm g hg) (fun x hx => by
      simpa using hnorm g⁻¹ (H.inv_mem hg) x hx)
  obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC, hC1, hCk⟩ := hdec h hh
  have hCpos : 0 < haarSub N hN C :=
    lt_of_lt_of_le (hpos _ isOpen_interior hC1) (measure_mono interior_subset)
  have hCfin : haarSub N hN C < ⊤ := hfin C hC
  have key : ∀ a b : ℝ≥0∞, a * haarSub N hN C = b * haarSub N hN C → a = b := fun a b hab => by
    first
      | exact (ENNReal.mul_left_inj hCpos.ne' hCfin.ne).mp hab
      | exact (ENNReal.mul_eq_mul_right hCpos.ne' hCfin.ne).mp hab
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_right_inj hCpos.ne' hCfin.ne).mp hab)
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_eq_mul_left hCpos.ne' hCfin.ne).mp hab)
  have cancel : ∀ c d : ℝ≥0, c • haarSub N hN = d • haarSub N hN → c = d := fun c d hcd => by
    have e := congrArg (fun μ : Measure G => μ C) hcd
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact_mod_cast key _ _ e
  have hk1 : (haarSub N hN).map (fun x => k * x * k⁻¹) = haarSub N hN := by
    obtain ⟨ck, hck⟩ := hsc k hk
    have hpre : (fun x : G => k * x * k⁻¹) ⁻¹' C = C := Set.ext fun x => hCk x
    have e1 : (haarSub N hN).map (fun x => k * x * k⁻¹) C = haarSub N hN C := by
      rw [Measure.map_apply (hm k) hC.measurableSet, hpre]
    rw [hck] at e1
    have e3 : (ck : ℝ≥0∞) * haarSub N hN C = 1 * haarSub N hN C := by
      simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e1
      rw [one_mul]
      exact e1
    have hck1 : ck = 1 := by exact_mod_cast key _ _ e3
    rw [hck, hck1, one_smul]
  have hp1 : (haarSub N hN).map (fun x => p * x * p⁻¹) = haarSub N hN := by
    obtain ⟨cp, hcp⟩ := hsc p hp
    obtain ⟨cs, hcs⟩ := hsc σ hσ
    obtain ⟨cs', hcs'⟩ := hsc σ⁻¹ (H.inv_mem hσ)
    have e1 : (cs' * cs) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid σ
      rw [hmap, hcs', Measure.map_smul _ (hm σ).aemeasurable, hcs, smul_smul] at e
      rw [e, one_smul]
    have hss : cs' * cs = 1 := cancel _ _ e1
    have hpinv : (fun x : G => p⁻¹ * x * p⁻¹⁻¹) =
        (fun x : G => σ * p * σ⁻¹ * x * (σ * p * σ⁻¹)⁻¹) := by
      rw [hσp]
    have e2 : (haarSub N hN).map (fun x => p⁻¹ * x * p⁻¹⁻¹) = (cs' * cp * cs) • haarSub N hN := by
      rw [hpinv, hmap (σ * p) σ⁻¹, hcs', Measure.map_smul _ (hm (σ * p)).aemeasurable,
        hmap σ p, hcp, Measure.map_smul _ (hm σ).aemeasurable, hcs, smul_smul, smul_smul]
    have e3 : (cs' * cp * cs * cp) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid p
      rw [hmap p p⁻¹, e2, Measure.map_smul _ (hm p).aemeasurable, hcp, smul_smul] at e
      rw [e, one_smul]
    have hcp1 : cp = 1 := by
      have h4 := cancel _ _ e3
      have h5 : cp * cp = 1 := by
        calc cp * cp = (cs' * cs) * (cp * cp) := by rw [hss, one_mul]
          _ = cs' * cp * cs * cp := by ring
          _ = 1 := h4
      have h6 : (cp : ℝ) * cp = 1 := by exact_mod_cast h5
      have h7 : (cp : ℝ) = 1 := by nlinarith [cp.2]
      exact_mod_cast h7
    rw [hcp, hcp1, one_smul]
  rw [hkp, hmap, hp1, hk1]

end PI.ScMuExists.UnitaryGroupMassFormula
end
end

