module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.Dec

def IsURep {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ (∀ a b, σ (a * b) = (σ a).comp (σ b)) ∧ (∀ g v, ‖σ g v‖ = ‖v‖) ∧ ∀ v, Continuous fun g => σ g v

def IsIrr {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : G → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤

def IsFdegG {G H : Type} [MeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure G)
    (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H, Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def IsOpOf {G H : Type} [MeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure G)
    (π : G → (H →L[ℂ] H)) (φ : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  Integrable φ μ ∧ ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def IsHaarSub {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (N : Set G) (ν : Measure G) : Prop :=
  ν ≠ 0 ∧ IsFiniteMeasureOnCompacts ν ∧ ν Nᶜ = 0 ∧ ∀ m ∈ N, ν.map (fun x => m * x) = ν

def IsIsoC {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) : Prop :=
  W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, herm (Jm ε) x y = 0

def NW {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) : Set (UJ ε) :=
  {g | (∀ x ∈ W, (umat g - 1) *ᵥ x = 0) ∧
    (∀ y, (∀ x ∈ W, herm (Jm ε) x y = 0) → (umat g - 1) *ᵥ y ∈ W) ∧
    ∀ y, ∀ x ∈ W, herm (Jm ε) x ((umat g - 1) *ᵥ y) = 0}

def muInf (I : AutInst) : Measure I.Ginf := Measure.pi fun v => muG (I.ε v)

def dSum (I : AutInst) (g : I.Ginf) : ℝ := ∑ v, dOp (uMat (g v))

def SmoothInf (I : AutInst) (a : I.Ginf → ℂ) : Prop :=
  ∀ x : I.Ginf, ∃ F : (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) → ℂ,
    ContDiffAt ℝ ∞ F (fun v i j => uMat (x v) i j) ∧ ∀ᶠ g in nhds x, a g = F (fun v i j => uMat (g v) i j)


open Classical in
def slice (I : AutInst) (f : I.GA → ℂ) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ → ℂ :=
  fun y => if h : ∃ g : UJ (I.ε v), uMat g = y then f (x * (Pi.mulSingle v h.choose, 1)) else 0

def zOp (I : AutInst) (v : InfinitePlace I.F) (m : ℕ) (f : I.GA → ℂ) : I.GA → ℂ :=
  fun x => gelf (I.ε v) m (slice I f x v) 1

def IsSmoothMG (I : AutInst) (g : ℕ) (f : I.GA → ℂ) : Prop :=
  (∀ γ ∈ I.GFset, ∀ x, f (γ * x) = f x) ∧ (∀ k ∈ I.Kg g, ∀ x, f (x * (1, k)) = f x) ∧
    ∀ xf : I.Gf, SmoothInf I (fun y => f (y, xf)) ∧
      ∃ C N : ℝ, ∀ y : I.Ginf, ‖f (y, xf)‖ ≤ C * Real.exp (N * dSum I y)

abbrev Kinf (I : AutInst) : Type := ∀ v : InfinitePlace I.F, KG (I.ε v)

def majPh (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (g : B.I.Ginf) : ℝ :=
  (∏ v, d v) * ∏ v, decE (rkR (B.I.ε v)) h (dOp (uMat (g v)))

def LocDec (B : RowsAut) (h : ℝ) : Prop :=
  ∀ v (g : UJ (B.I.ε v)), ‖⟪B.w v, B.σ v (uMat g) (B.w v)⟫_ℂ‖ ≤ decE (rkR (B.I.ε v)) h (dOp (uMat g))

def HBig (B : RowsAut) (c h : ℝ) : Prop :=
  ∀ v, c * (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) ≤ h

def kerC (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  (∏ v, d v) * (B.e 1).re * (3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) * (2 * Real.exp (2 * (B.I.n : ℝ) ^ 2)) ^ B.I.f

def IsContRep (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ B.I.GFset, ∀ x, f (γ * x) = f x) ∧
    (y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] f

def phG {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntG {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def slopeD {K V : Type} [Field K] [AddCommGroup V] [Module K V] (d : Submodule K V → ℝ) (A B : Submodule K V) : ℝ :=
  (d B - d A) / ((Module.finrank K B : ℝ) - (Module.finrank K A : ℝ))

def IsChainD {K V : Type} [Field K] [AddCommGroup V] [Module K V] (d : Submodule K V → ℝ) (s : ℕ)
    (W : ℕ → Submodule K V) : Prop :=
  FiniteDimensional K V ∧ W 0 = ⊥ ∧ W s = ⊤ ∧ (∀ i < s, W i < W (i + 1)) ∧
    (∀ i, i + 2 ≤ s → slopeD d (W (i + 1)) (W (i + 2)) < slopeD d (W i) (W (i + 1))) ∧
    ∀ i < s, ∀ U : Submodule K V, W i < U → U ≤ W (i + 1) → slopeD d (W i) U ≤ slopeD d (W i) (W (i + 1))

theorem IsURep.integrable_coef {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : G → (H →L[ℂ] H)} (hπ : IsURep π)
    {μ : Measure G} {φ : G → ℂ} (hφ : Integrable φ μ) (x y : H) :
    Integrable (fun g => φ g * ⟪x, π g y⟫_ℂ) μ := by
  have hc : Continuous fun g => ⟪x, π g y⟫_ℂ := continuous_const.inner (hπ.2.2.2 y)
  refine Integrable.mono' (hφ.norm.mul_const (‖x‖ * ‖y‖))
    (hφ.aestronglyMeasurable.mul hc.aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  gcongr
  calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [hπ.2.2.1]

theorem IsURep.exists_isOpOf {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : G → (H →L[ℂ] H)} (hπ : IsURep π) {μ : Measure G} {φ : G → ℂ} (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, IsOpOf μ π φ T ∧ ‖T‖ ≤ ∫ g, ‖φ g‖ ∂μ := by
  have hI : ∀ x y, Integrable (fun g => φ g * ⟪x, π g y⟫_ℂ) μ := hπ.integrable_coef hφ
  have hC : 0 ≤ ∫ g, ‖φ g‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hbound : ∀ x y, ‖∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ‖ ≤ (∫ g, ‖φ g‖ ∂μ) * ‖x‖ * ‖y‖ := by
    intro x y
    calc ‖∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ‖ ≤ ∫ g, ‖φ g * ⟪x, π g y⟫_ℂ‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ g, ‖φ g‖ * (‖x‖ * ‖y‖) ∂μ := by
          refine integral_mono (hI x y).norm (hφ.norm.mul_const _) fun g => ?_
          simp only [norm_mul]
          gcongr
          calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
            _ = ‖x‖ * ‖y‖ := by rw [hπ.2.2.1]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖x‖ * ‖y‖ := by rw [integral_mul_const]; ring
  let B0 : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ)
    (fun x x' y => by
      simp only [inner_add_left, mul_add]
      exact integral_add (hI x y) (hI x' y))
    (fun c x y => by
      simp only [inner_smul_left, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext g
      ring)
    (fun x y y' => by
      simp only [map_add (f := _), inner_add_right, mul_add]
      exact integral_add (hI x y) (hI x y'))
    (fun c x y => by
      simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1
      funext g
      ring)
  let B : H →L⋆[ℂ] H →L[ℂ] ℂ := B0.mkContinuous₂ (∫ g, ‖φ g‖ ∂μ) fun x y => hbound x y
  let T : H →L[ℂ] H := ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin B)
  have hT : ∀ x y, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
    intro x y
    simp only [T, ContinuousLinearMap.adjoint_inner_right,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
    rfl
  refine ⟨T, ⟨hφ, hT⟩, ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_⟩
  have key : ‖T y‖ * ‖T y‖ ≤ (∫ g, ‖φ g‖ ∂μ) * ‖T y‖ * ‖y‖ := by
    calc ‖T y‖ * ‖T y‖ = RCLike.re ⟪T y, T y⟫_ℂ := (inner_self_eq_norm_mul_norm (T y)).symm
      _ ≤ ‖⟪T y, T y⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ _ := by rw [hT]; exact hbound _ _
  rcases (norm_nonneg (T y)).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith

theorem isHaarSub_univ {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] : IsHaarSub (Set.univ : Set G) μ := by
  refine ⟨NeZero.ne μ, inferInstance, by simp, fun m _ => ?_⟩
  exact map_mul_left_eq_self μ m

theorem isHaarSub_map {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (hN : IsClosed (N : Set G))
    (ν : Measure N) [ν.IsHaarMeasure] : IsHaarSub (N : Set G) (ν.map Subtype.val) := by
  have hval : Measurable (Subtype.val : N → G) := measurable_subtype_coe
  refine ⟨(Measure.map_ne_zero_iff hval.aemeasurable).mpr (NeZero.ne ν), ⟨fun K hK => ?_⟩, ?_, fun m hm => ?_⟩
  · rw [Measure.map_apply hval hK.measurableSet]
    exact (hN.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top
  · rw [Measure.map_apply hval hN.measurableSet.compl]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext x
      simp
    rw [this, measure_empty]
  · have hmul : Measurable fun x : N => (⟨m, hm⟩ : N) * x :=
      ((measurable_const_mul m).comp hval).subtype_mk
    rw [Measure.map_map (measurable_const_mul m) hval]
    have e : (fun x => m * x) ∘ (Subtype.val : N → G) = Subtype.val ∘ fun x : N => (⟨m, hm⟩ : N) * x := rfl
    rw [e, ← Measure.map_map hval hmul, map_mul_left_eq_self]

def nwSub {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) : Subgroup (UJ ε) where
  carrier := NW ε W
  one_mem' := by
    have e : umat (1 : UJ ε) = 1 := rfl
    refine ⟨fun x _ => ?_, fun y _ => ?_, fun y x _ => ?_⟩ <;> simp [e, herm]
  mul_mem' := by
    intro g h hg hh
    have e : ∀ y, (umat (g * h) - 1) *ᵥ y = (umat g - 1) *ᵥ y + (umat g - 1) *ᵥ ((umat h - 1) *ᵥ y) +
        (umat h - 1) *ᵥ y := by
      intro y
      have : umat (g * h) = umat g * umat h := rfl
      rw [this, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec]
      congr 1
      noncomm_ring
    refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
    · rw [e, hh.1 x hx, hg.1 x hx]; simp
    · rw [e, hg.1 _ (hh.2.1 y hy), add_zero]
      exact W.add_mem (hg.2.1 y hy) (hh.2.1 y hy)
    · have h1 := hg.2.2 y x hx
      have h2 := hg.2.2 ((umat h - 1) *ᵥ y) x hx
      have h3 := hh.2.2 y x hx
      rw [e]
      simp only [herm, star_add, add_dotProduct] at *
      rw [h1, h2, h3]; simp
  inv_mem' := by
    intro g hg
    have i1 : umat g⁻¹ * umat g = 1 := Units.inv_mul _
    have i2 : umat g * umat g⁻¹ = 1 := Units.mul_inv _
    have e1 : ∀ y, (umat g⁻¹ - 1) *ᵥ y = -((umat g - 1) *ᵥ y) - (umat g⁻¹ - 1) *ᵥ ((umat g - 1) *ᵥ y) := by
      intro y
      rw [Matrix.mulVec_mulVec, ← Matrix.neg_mulVec, ← Matrix.sub_mulVec]
      congr 1
      rw [sub_mul, mul_sub, i1]
      noncomm_ring
    have e2 : ∀ y, (umat g⁻¹ - 1) *ᵥ y = -((umat g - 1) *ᵥ (umat g⁻¹ *ᵥ y)) := by
      intro y
      rw [Matrix.mulVec_mulVec, ← Matrix.neg_mulVec, sub_mul, i2]
      congr 1
      noncomm_ring
    have f : ∀ x ∈ W, (umat g⁻¹ - 1) *ᵥ x = 0 := by
      intro x hx
      rw [e1, hg.1 x hx]; simp
    refine ⟨f, fun y hy => ?_, fun y x hx => ?_⟩
    · rw [e1, f _ (hg.2.1 y hy), sub_zero]
      exact W.neg_mem (hg.2.1 y hy)
    · have h1 := hg.2.2 (umat g⁻¹ *ᵥ y) x hx
      rw [e2]
      simp only [herm, star_neg, neg_dotProduct] at *
      rw [h1, neg_zero]

@[simp] theorem coe_nwSub {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) :
    ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)) = NW ε W := rfl

theorem isClosed_NW {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) : IsClosed (NW ε W) := by
  have hc : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  have hv : ∀ y, Continuous fun g : UJ ε => (umat g - 1) *ᵥ y := fun y =>
    (hc.sub continuous_const).matrix_mulVec continuous_const
  have hW : IsClosed (W : Set (Fin n → ℂ)) := W.closed_of_finiteDimensional
  have e : NW ε W = (⋂ x ∈ W, {g : UJ ε | (umat g - 1) *ᵥ x = 0}) ∩
      (⋂ y ∈ {y | ∀ x ∈ W, herm (Jm ε) x y = 0}, (fun g : UJ ε => (umat g - 1) *ᵥ y) ⁻¹' (W : Set (Fin n → ℂ))) ∩
      (⋂ y, ⋂ x ∈ W, {g : UJ ε | herm (Jm ε) x ((umat g - 1) *ᵥ y) = 0}) := by
    ext g
    simp [NW, and_assoc]
  rw [e]
  refine ((isClosed_biInter fun x _ => isClosed_eq (hv x) continuous_const).inter
    (isClosed_biInter fun y _ => hW.preimage (hv y))).inter
    (isClosed_iInter fun y => isClosed_biInter fun x _ => isClosed_eq ?_ continuous_const)
  simp only [herm]
  exact ((hv y).star).dotProduct continuous_const

theorem exists_isHaarSub_NW {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν := by
  have hN : IsClosed ((nwSub ε W : Subgroup (UJ ε)) : Set (UJ ε)) := by
    rw [coe_nwSub]
    exact isClosed_NW ε W
  have : LocallyCompactSpace (nwSub ε W) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have h := isHaarSub_map (nwSub ε W) hN (Measure.haar)
  rw [coe_nwSub] at h
  exact ⟨_, h⟩


theorem Eword_congr {n : ℕ} (ε : Fin n → Bool) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w f g = Eword ε w f' g := by
  induction w with
  | nil => exact h
  | cons p w ih =>
    intro g hg
    have hcurve : ∀ X, inG ε X → (fun t : ℝ => Eword ε w f (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => Eword ε w f' (g * NormedSpace.exp ((t : ℂ) • X)) := fun X hX =>
      funext fun t => ih _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))
    have hm := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    simp only [Eword, Eab, Ec, Rd]
    rw [hcurve _ hm.1, hcurve _ hm.2.1]


namespace ProjEx


end ProjEx

end GlobalTheory.Dec
