module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem pow_mem_of_mul {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a : 𝔸} (ha : a ∈ S) (n : ℕ) :
    a ^ n ∈ S := by
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hm _ ih _ ha

def lieSub (S : Set 𝔸) (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Submodule ℝ 𝔸 where
  carrier := {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S}
  zero_mem' := by intro t; simpa [NormedSpace.exp_zero] using h1
  add_mem' := by
    intro X Y hX hY t
    rw [smul_add]
    refine hc.mem_of_tendsto (Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter (t • X) (t • Y)) (Eventually.of_forall fun n => ?_)
    refine pow_mem_of_mul h1 hm (hm _ ?_ _ ?_) n
    · rw [smul_smul]; exact hX _
    · rw [smul_smul]; exact hY _
  smul_mem' := by
    intro c X hX t
    rw [smul_smul]; exact hX _

theorem exp_smul_mem_of_tendsto {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) {y : ℕ → 𝔸} {u : 𝔸}
    (hy0 : Tendsto y atTop (𝓝 0)) (hne : ∀ n, y n ≠ 0) (hS : ∀ n, NormedSpace.exp (y n) ∈ S)
    (hu : Tendsto (fun n => ‖y n‖⁻¹ • y n) atTop (𝓝 u)) (t : ℝ) : NormedSpace.exp (t • u) ∈ S := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have key : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • u) ∈ S := by
    intro t ht
    have hpos : ∀ n, 0 < ‖y n‖ := fun n => norm_pos_iff.2 (hne n)
    have hn0 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using hy0.norm
    have hk : Tendsto (fun n => ((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) atTop (𝓝 t) := by
      have hl : Tendsto (fun n => t - ‖y n‖) atTop (𝓝 t) := by simpa using hn0.const_sub t
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) (fun n => ?_)
      · have h := (Nat.lt_floor_add_one (t / ‖y n‖)).le
        rw [div_le_iff₀ (hpos n)] at h
        show t - ‖y n‖ ≤ _
        nlinarith
      · have h := Nat.floor_le (div_nonneg ht (hpos n).le)
        rw [le_div_iff₀ (hpos n)] at h
        exact h
    have hlim := (NormedSpace.exp_continuous.tendsto _).comp (hk.smul hu)
    refine hc.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have e : (((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) • ‖y n‖⁻¹ • y n = (⌊t / ‖y n‖⌋₊ : ℕ) • y n := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos n).ne', mul_one, Nat.cast_smul_eq_nsmul]
    simp only [Function.comp]
    rw [e, NormedSpace.exp_nsmul]
    exact pow_mem_of_mul h1 hm (hS n) _
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have := hi _ (key (-t) (by linarith))
    rwa [neg_smul, neg_neg] at this

theorem eventually_eq_zero [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {W : Submodule ℝ 𝔸} (hW : Disjoint (lieSub S hc h1 hm) W) :
    ∀ᶠ y in 𝓝 (0 : 𝔸), y ∈ W → NormedSpace.exp y ∈ S → y = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨y, hy0, hy⟩ := exists_seq_forall_of_frequently hcon
  push_neg at hy
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  have hsph : ∀ n, ‖y n‖⁻¹ • y n ∈ Metric.sphere (0 : 𝔸) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hy n).2.2)]
  obtain ⟨u, hu1, φ, hφ, hu⟩ := (isCompact_sphere (0 : 𝔸) 1).tendsto_subseq hsph
  have huL : u ∈ lieSub S hc h1 hm :=
    exp_smul_mem_of_tendsto hc h1 hm hi (y := y ∘ φ) (hy0.comp hφ.tendsto_atTop) (fun n => (hy _).2.2)
      (fun n => (hy _).2.1) hu
  have huW : u ∈ W :=
    W.closed_of_finiteDimensional.mem_of_tendsto hu (Eventually.of_forall fun n => W.smul_mem _ (hy _).1)
  have h0 : u = 0 := (Submodule.disjoint_def.1 hW) u huL huW
  rw [h0] at hu1
  simp at hu1

theorem map_exp_mul_exp (p : 𝔸 →L[ℝ] 𝔸) :
    map (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z)) (𝓝 0) = 𝓝 (1 : 𝔸) := by
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have h1 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z)) ((1 : 𝔸 →L[ℝ] 𝔸).comp p) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (by rw [map_zero]; exact hexp) p.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h3 := h1.mul' h2
  have h4 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z))
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine h3.congr_fderiv ?_
    ext z
    simp [NormedSpace.exp_zero]
  have h5 := h4.map_nhds_eq_of_equiv
  simpa [NormedSpace.exp_zero] using h5

theorem eventually_exists_exp [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {U : Set 𝔸} (hU : U ∈ 𝓝 (0 : 𝔸)) :
    ∀ᶠ g in 𝓝 (1 : 𝔸), g ∈ S → ∃ X ∈ U, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ S) ∧ NormedSpace.exp X = g := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap ((lieSub S hc h1 hm).projection W hW)
  have hpL : ∀ z, p z ∈ lieSub S hc h1 hm := fun z => Submodule.projection_apply_mem hW z
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  rw [← map_exp_mul_exp p, eventually_map]
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  filter_upwards [hp0.eventually hU, hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint)] with z hz1 hz2 hg
  have hneg : NormedSpace.exp (-p z) ∈ S := by simpa using hpL z (-1)
  have hq : NormedSpace.exp (z - p z) ∈ S := by
    have h := hm _ hneg _ hg
    rwa [← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl (p z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero, one_mul] at h
  refine ⟨p z, hz1, hpL z, ?_⟩
  rw [hz2 (hqW z) hq, NormedSpace.exp_zero, mul_one]

end Banach

theorem unrealify_realify {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

theorem unrealify_mem_lieOf {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {x : EuclideanSpace ℝ (Fin m × Fin m × Bool)} (hx : x ∈ lieE S) : unrealify x ∈ lieOf S := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have hL : ∀ X, X ∈ lieOf S ↔ X ∈ lieSub S hS.1 hS.2.1 hS.2.2.1 := fun X => by
    simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]; rfl
  rw [hL]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    rw [unrealify_realify]; exact (hL X).1 hX
  | zero =>
    have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : unrealify (x + y) = unrealify x + unrealify y := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : unrealify (c • x) = c • unrealify x := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.smul_mem _ _ hx

theorem eventually_exists_exp_matrix {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {U : Set (Matrix (Fin m) (Fin m) ℂ)} (hU : U ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ)) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), g ∈ S → ∃ X ∈ U, X ∈ lieOf S ∧ NormedSpace.exp X = g := by
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := fun Z hZ => by
    rw [Matrix.exp_neg]; exact (hS.2.2.2 _ hZ).1
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have h := eventually_exists_exp hS.1 hS.2.1 hS.2.2.1 hi hU
  simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]
  exact h

theorem closed_subgroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  intro m S hS
  refine ⟨fun X => unrealify_mem_lieOf hS X.2, fun ρ hρ => ?_⟩
  let R : Matrix (Fin m) (Fin m) ℂ → EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    fun X => (WithLp.equiv 2 _).symm (realifyFun X)
  have hR : Continuous R := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
    obtain ⟨i, j, b⟩ := p
    cases b
    · simp only [realifyFun]; simp; fun_prop
    · simp only [realifyFun]; simp; fun_prop
  have hR0 : R 0 = 0 := by
    ext p; simp [R, realifyFun]
  have hU : R ⁻¹' Metric.ball 0 ρ ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ) :=
    hR.continuousAt.preimage_mem_nhds (by rw [hR0]; exact Metric.ball_mem_nhds _ hρ)
  have h := eventually_exists_exp_matrix hS hU
  obtain ⟨δ, hδ, hb⟩ := (Metric.eventually_nhds_iff (α := Fin m → Fin m → ℂ)).1 h
  refine ⟨δ, hδ, fun g hg hgδ => ?_⟩
  obtain ⟨X, hXU, hXL, rfl⟩ := @hb g (by
    refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => ?_
    rw [dist_eq_norm]; exact hgδ i j) hg
  refine ⟨⟨R X, Submodule.subset_span ⟨X, hXL, rfl⟩⟩, ?_, ?_⟩
  · rw [mem_ball_zero_iff]; exact mem_ball_zero_iff.1 hXU
  · simp only [R]; rw [unrealify_realify]

end GlobalTheory.ClosedMatGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem Hpk_ne_zero' (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have h1 : Hpk k r ⟨r + k, by omega⟩ ⟨r + k, by omega⟩ = -1 := by
    simp [Hpk]
  rw [h] at h1
  simp at h1

theorem IsClosedSub.mul_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {a : Mat k r} (ha : a ∈ S) :
    a * a⁻¹ = 1 := by
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hm : a⁻¹ ∈ GG k r := hS.1 (hS.2.2.2.2 a ha)
    rw [h0] at hm
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    simp at this
    exact Hpk_ne_zero' k r this.symm

theorem IsClosedSub.isMatGroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S :=
  ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, fun a ha => ⟨hS.2.2.2.2 a ha, hS.mul_inv ha⟩⟩

theorem haarOn_locFinite_openPos :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ →
      (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  intro k r S μ hS hμ
  have hμ' : PI.IsHaarOnM S μ := hμ
  obtain ⟨-, hK, hU⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S μ hS.isMatGroup hμ'
  refine ⟨fun C hC => ?_, hU⟩
  have hA : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS.2.1
  have h1 : μ C ≤ μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) + μ (C \ {x : Mt k r | Matrix.of x ∈ S}) :=
    measure_le_inter_add_sdiff μ C _
  have h2 : μ (C \ {x : Mt k r | Matrix.of x ∈ S}) = 0 :=
    measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have h3 : μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) < ⊤ :=
    hK _ (hC.inter_right hA) (fun x hx => hx.2)
  rw [h2, add_zero] at h1
  exact lt_of_le_of_lt h1 h3

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticeProperties
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.RealSpan

section General

variable {E A : Type} [Field E] [CommRing A] {n : ℕ}

theorem span_image_span (ι : E →+* A) (S : Set (Fin n → E)) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) =
      Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) ''
        (Submodule.span E S : Set (Fin n → E))) := by
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext i; simp
    simp only [this]
    exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => ι ((y + z) i)) = (fun i => ι (y i)) + fun i => ι (z i) := by funext i; simp
    simp only [this]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (fun i => ι ((c • y) i)) = ι c • fun i => ι (y i) := by funext i; simp
    simp only [this]
    exact Submodule.smul_mem _ _ hy

theorem span_image_univ (ι : E →+* A) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem map_mulVec_image (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    Y.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((Y *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_mem (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S T : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u ∈ T) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' T) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact Submodule.subset_span ⟨Y *ᵥ w, h w hw, (map_mulVec_image ι Y w).symm⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem map_mulVec_eq_zero (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u = 0) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [map_mulVec_image, h w hw]
    funext i; simp
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]

variable (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (hc : ∀ e, s (ι e) = ι (σ e))
  (J : Matrix (Fin n) (Fin n) E)

include hc

theorem isSkew_map (Y : Matrix (Fin n) (Fin n) E) (h : IsSkew σ J Y) :
    IsSkew s (J.map ι) (Y.map ι) := by
  rw [← GlobalTheory.CoverRadiiEq.skew_iff] at h ⊢
  have h1 : Formalism.UG.cT s (Y.map ι) = (Formalism.UG.cT σ Y).map ι := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [h1, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), h]
  simp

theorem inNil_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InNil σ J W Y) :
    InNil s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨isSkew_map σ s ι hc J Y h1, fun u => ?_, fun u hu => ?_, map_mulVec_eq_zero ι Y _ h4⟩
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc]
    exact map_mulVec_mem ι Y Set.univ _ (fun u _ => h2 u) u (by rw [span_image_univ]; trivial)
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
    exact map_mulVec_mem ι Y _ _ h3 u hu

theorem inCen_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InCen σ J W Y) :
    InCen s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  refine ⟨inNil_map σ s ι hc J W Y h.1, fun u hu => ?_⟩
  rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
  exact map_mulVec_eq_zero ι Y _ h.2 u hu

end General

section Lattice

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | (apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main ..)

omit [NumberField E] in
theorem mem_perpSet_span (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (y : Fin n → E) :
    y ∈ perpSet σ J (Submodule.span E S) ↔ ∀ w ∈ S, Formalism.UG.hform σ J w y = 0 := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp [Formalism.UG.hform]
  | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_left, hu, mul_zero]

theorem span_perp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (Λ R : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (Submodule.span E (Submodule.span (𝓞 E) {y | y ∈ Λ ∧ ∀ s ∈ R, Formalism.UG.hform σ J s y = 0} :
      Set (Fin n → E)) : Set (Fin n → E)) = perpSet σ J (Submodule.span E (R : Set (Fin n → E))) := by
  rw [Submodule.span_span_of_tower]
  ext y
  rw [mem_perpSet_span]
  constructor
  · intro hy w hw
    induction hy using Submodule.span_induction with
    | mem u hu => exact hu.2 w hw
    | zero => simp [Formalism.UG.hform]
    | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_right, hu, mul_zero]
  · intro hy
    obtain ⟨c, hc, hcy⟩ := exists_smul_mem Λ y (by rw [hΛ]; trivial)
    have hc1 : algebraMap (𝓞 E) E c ≠ 0 := by simpa using hc
    rw [← algebraMap_smul E c] at hcy
    have : y = (algebraMap (𝓞 E) E c)⁻¹ • algebraMap (𝓞 E) E c • y := by
      rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hcy, fun w hw => ?_⟩)
    rw [Formalism.UG.P.csScale_hform_smul_right, hy w hw, mul_zero]

end Lattice

theorem conj_emb (I : AutInst) (v : InfinitePlace I.F) (e : I.E) :
    starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
  (I.cm.cmUnram.2.1 (I.φ v) e).symm

theorem spanAt_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  intro I x R
  have h1 : ∀ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) v, spanAt I R v = Submodule.span ℂ
      ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) ''
        (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E))) :=
    fun R v => span_image_span (I.φ v) _
  have hΛ := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  refine ⟨h1 R, fun v => ?_, fun v => ?_, fun Y hY v => ?_, fun Y hY v => ?_⟩
  · rw [h1, hΛ]
    exact span_image_univ _
  · rw [h1, h1, GlobalTheory.PerpBaseChange.perpSet_baseChange _ _ (starRingEnd I.E) _ _ _ _ _ (conj_emb I v), perpIn,
      span_perp _ _ _ _ hΛ]
  · rw [h1]
    exact inNil_map _ _ _ (conj_emb I v) _ _ Y hY
  · rw [h1]
    exact inCen_map _ _ _ (conj_emb I v) _ _ Y hY

end GlobalTheory.RealSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

def lev (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def wC (k r : ℕ) : Mat k r := bigCell k r (fun _ => 1) 1

def torD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal fun i =>
  if h : i.val < r then x ⟨i.val, h⟩
  else if h' : r + k < i.val then -star (x ⟨2 * r + k - i.val, by omega⟩) else 0

def um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) : Matrix (Fin m) (Fin m) ℂ :=
  unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

abbrev EE (k r : ℕ) : Type :=
  (lieE (Nset k r) × lieE (Nset k r)) × ((Fin r → ℂ) × lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def chart (k r : ℕ) (v : EE k r) : Mat k r :=
  wC k r * (NormedSpace.exp (-um v.1.1) * bigCell k r (fun a => 1 + v.2.1 a) 1 * NormedSpace.exp (um v.2.2) *
    NormedSpace.exp (um v.1.2))

def dchart (k r : ℕ) (v : EE k r) : Mat k r :=
  -(wC k r * um v.1.1 * wC k r) + torD k r v.2.1 + um v.2.2 + um v.1.2

end GlobalTheory.CellDens
end
end

