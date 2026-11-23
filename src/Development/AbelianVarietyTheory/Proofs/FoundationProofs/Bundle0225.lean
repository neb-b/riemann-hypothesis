module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSupBall

open MeasureTheory Filter Set
open scoped Pointwise

theorem integral_le_of_disjoint_translates {ι : Type} [Fintype ι]
    (A : AddSubgroup (EuclideanSpace ℂ ι)) [Countable A]
    (D t : Set (EuclideanSpace ℂ ι)) (hD : IsAddFundamentalDomain A D volume)
    (ht : MeasurableSet t)
    (hd : ∀ y₁ y₂ : A, y₁ ≠ y₂ → Disjoint (y₁ +ᵥ t) (y₂ +ᵥ t))
    (f : EuclideanSpace ℂ ι → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfc : Continuous f)
    (hf : ∀ (y : A) u, f (y +ᵥ u) = f u) (hi : IntegrableOn f D) :
    ∫ u in t, f u ≤ ∫ u in D, f u := by
  haveI : VAddInvariantMeasure A (EuclideanSpace ℂ ι) volume :=
    ⟨fun g s _ => measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hi).ne ?_
  calc ∫⁻ u in t, ENNReal.ofReal (f u)
      = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f (-y +ᵥ u)) :=
        hD.setLIntegral_eq_tsum' (fun u => ENNReal.ofReal (f u)) t
    _ = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by simp_rw [hf]
    _ = ∫⁻ u in ⋃ y : A, (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by
        refine (lintegral_iUnion₀ (fun y => ?_) ?_ _).symm
        · exact (ht.const_vadd y).nullMeasurableSet.inter hD.nullMeasurableSet
        · intro y₁ y₂ h
          exact (((hd y₁ y₂ h).inf_left _).inf_right _).aedisjoint
    _ ≤ ∫⁻ u in D, ENNReal.ofReal (f u) :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right)

theorem factorial_div_le (g : ℕ) {v r : ℝ} (hv : 1 ≤ v) (hr : r ^ 2 = 1 / (4 * v)) :
    (g.factorial : ℝ) / (Real.pi ^ g * r ^ (2 * g)) ≤ (2 * (g : ℝ) * v + 1) ^ g := by
  have hv0 : 0 < v := by linarith
  have hpi := Real.pi_gt_three
  rw [pow_mul, hr, ← mul_pow]
  have h1 : (g.factorial : ℝ) ≤ (g : ℝ) ^ g := by exact_mod_cast Nat.factorial_le_pow g
  calc (g.factorial : ℝ) / (Real.pi * (1 / (4 * v))) ^ g
      ≤ (g : ℝ) ^ g / (Real.pi * (1 / (4 * v))) ^ g := by gcongr
    _ = ((g : ℝ) / (Real.pi * (1 / (4 * v)))) ^ g := by rw [div_pow]
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ g
        rw [div_le_iff₀ (by positivity)]
        have h2 : (2 * (g : ℝ) * v + 1) * (Real.pi * (1 / (4 * v)))
            = Real.pi / 2 * g + Real.pi / (4 * v) := by field_simp; ring
        rw [h2]
        have h3 : 0 ≤ Real.pi / (4 * v) := by positivity
        have h4 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        nlinarith

theorem sup_le_mean_square : ∀ (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ) (Fd : Set (EuclideanSpace ℂ ι)) (G : EuclideanSpace ℂ ι → ℂ), 1 ≤ v → (∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2) → MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume → MeasureTheory.volume Fd = 1 → Differentiable ℂ G → (∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) → MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd → ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * ∫ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro ι _ A v Fd G hv hA hD _ hG hinv hint z
  have hv0 : 0 < v := by linarith
  set r : ℝ := Real.sqrt (1 / (4 * v)) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 1 / (4 * v) := Real.sq_sqrt (by positivity)
  set N : EuclideanSpace ℂ ι → ℝ := fun u => ‖G u‖ ^ 2 * Real.exp (-Real.pi * ‖u‖ ^ 2) with hN
  have hN0 : ∀ u, 0 ≤ N u := fun u => by positivity
  have hGc := hG.continuous
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hdisj : ∀ y₁ y₂ : A, y₁ ≠ y₂ →
      Disjoint (y₁ +ᵥ Metric.ball z r) (y₂ +ᵥ Metric.ball z r) := by
    intro y₁ y₂ hne
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' : (y₂ : EuclideanSpace ℂ ι) + q = (y₁ : EuclideanSpace ℂ ι) + p := hpq
    have hy : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) = q - p := by
      rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, ← hpq', add_comm]
    have hne' : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp (Subtype.ext h0))
    have h1 := hA _ (y₁ - y₂ : A).2 hne'
    rw [hy] at h1
    have h2 : ‖q - p‖ < 2 * r := by
      have hp' : dist p z < r := hp
      have hq' : dist q z < r := hq
      rw [← dist_eq_norm]
      calc dist q p ≤ dist q z + dist z p := dist_triangle _ _ _
        _ < 2 * r := by rw [dist_comm z p]; linarith
    have h3 : ‖q - p‖ ^ 2 < (2 * r) ^ 2 := by gcongr
    have h4 : (2 * r) ^ 2 = 1 / v := by rw [mul_pow, hr2]; field_simp; norm_num
    linarith
  haveI : Countable A := by
    rw [← Set.countable_univ_iff]
    refine Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y : A => y +ᵥ Metric.ball z r) (fun a _ b _ h => hdisj a b h) ?_ ?_
    · intro y _
      exact Metric.isOpen_ball.vadd (y : EuclideanSpace ℂ ι)
    · intro y _
      exact ⟨y +ᵥ z, z, Metric.mem_ball_self hr0, rfl⟩
  have hpk : ∫ u in Metric.ball z r, N u ≤ ∫ u in Fd, N u := by
    refine integral_le_of_disjoint_translates A Fd _ hD measurableSet_ball hdisj N hN0 hNc ?_ hint
    intro y u
    have e : y +ᵥ u = u + (y : EuclideanSpace ℂ ι) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    rw [e]
    exact hinv y y.2 u
  set φ : EuclideanSpace ℂ ι → ℂ :=
    fun u => G u * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z (u - z)) with hφ
  have hφd : Differentiable ℂ φ := by
    refine hG.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    exact (innerSL ℂ z).differentiable.comp (differentiable_id.sub_const z)
  have hφi : IntegrableOn (fun u => ‖φ u‖ ^ 2) (Metric.ball z r) :=
    GlobalTheory.integrableOn_norm_pow_ball volume hφd.continuous.continuousOn 2
  have hsub := GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball hr0 hφd.differentiableOn 2 hφi
  rw [finrank_euclideanSpace] at hsub
  have hφz : φ z = G z := by simp [hφ]
  rw [hφz] at hsub
  have hpt : ∀ u ∈ Metric.ball z r,
      ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * N u := by
    intro u hu
    have hu' : ‖u - z‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : ‖u - z‖ ^ 2 ≤ 1 / 4 := by
      have : ‖u - z‖ ^ 2 ≤ r ^ 2 := by gcongr
      refine this.trans ?_
      rw [hr2]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + 2 * (inner ℂ z (u - z)).re + ‖u - z‖ ^ 2 := by
      have := norm_add_sq (𝕜 := ℂ) z (u - z)
      rwa [add_sub_cancel] at this
    have h3 : Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ 3 := by
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖u - z‖])
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h4 : ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
        = Real.exp (Real.pi * ‖u - z‖ ^ 2) * N u := by
      simp only [hφ, hN]
      rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
        mul_left_comm, ← Real.exp_add, h2]
      congr 2
      simp only [innerSL_apply_apply, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
      push_cast
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (hN0 u)
  have hNi : IntegrableOn N (Metric.ball z r) :=
    (hNc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hb : (∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ 3 * ∫ u in Metric.ball z r, N u := by
    rw [← integral_mul_const, ← integral_const_mul]
    exact setIntegral_mono_on (hφi.mul_const _) (hNi.const_mul _) measurableSet_ball hpt
  have hnum := factorial_div_le (Fintype.card ι) hv hr2
  have hI0 : 0 ≤ ∫ u in Fd, N u := integral_nonneg hN0
  set c : ℝ := ((Fintype.card ι).factorial : ℝ) /
    (Real.pi ^ Fintype.card ι * r ^ (2 * Fintype.card ι)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ (c * ∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le
    _ ≤ c * (3 * ∫ u in Metric.ball z r, N u) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hc0
    _ ≤ c * (3 * ∫ u in Fd, N u) := by gcongr
    _ ≤ (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * (3 * ∫ u in Fd, N u) := by gcongr
    _ = _ := by ring

end GlobalTheory.ThetaSupBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Complex
open scoped BigOperators ComplexConjugate Real

noncomputable section

namespace GlobalTheory.UnitaryTheta

section General

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsPosHerm (H : Sesq V) : Prop :=
  (∀ z w, H z w = conj (H w z)) ∧ ∀ z, z ≠ 0 → 0 < (H z z).re

def Heisenberg₂ (H : Sesq V) (x : V) (G : V → ℂ) : V → ℂ :=
  fun z => G (z + x) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2)

def kerTerm (H : Sesq V) (x w z : V) : ℂ :=
  cexp ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2)

def kerSum (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (z : V) : V → ℂ :=
  fun w => ∑' x : Λ, α x * kerTerm H x w z

def IsSemichar (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) : Prop :=
  (∀ x ∈ Λ, α x = 1 ∨ α x = -1) ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, (H x y).im = m) ∧
    ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * cexp (-((π : ℂ) * I) * ((H x y).im : ℂ))

end General

def formV (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (fun z z' w => by simp [Hf, add_mul, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_assoc, mul_div_assoc'])
    (fun z w w' => by simp [Hf, mul_add, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_left_comm, mul_div_assoc'])

open NumberField Classical in
open Complex in
open scoped BigOperators ComplexConjugate Real in
theorem _root_.GlobalTheory.UnitaryTheta.isPosHerm_formV (D : _root_.Formalism.BasicNotions.D7) (T : _root_.Formalism.MainNotions.TaylorLogMetric.Tor D)
    (N N' : ℕ) (h : 0 < _root_.Formalism.MainNotions.TaylorLogMetric.area T.abelian₂) :
    _root_.GlobalTheory.UnitaryTheta.IsPosHerm (_root_.GlobalTheory.UnitaryTheta.formV D T N N') := by
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [_root_.GlobalTheory.UnitaryTheta.formV, LinearMap.mk₂'ₛₗ_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, map_div₀, map_sum, map_mul,
      Complex.conj_conj, Complex.conj_ofReal]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have hsum : ∀ τ i j, z τ i j * conj (z τ i j) = ((Complex.normSq (z τ i j) : ℝ) : ℂ) :=
      fun τ i j => Complex.mul_conj _
    simp only [_root_.GlobalTheory.UnitaryTheta.formV, LinearMap.mk₂'ₛₗ_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, hsum]
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
    refine div_pos ?_ h
    obtain ⟨τ, i, j, hz⟩ : ∃ τ i j, z τ i j ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz (funext fun τ => funext fun i => funext fun j => hne τ i j)
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨τ, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 hz⟩

end GlobalTheory.UnitaryTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerate
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TraceSemisimple

def spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) :
    Subalgebra K (Matrix (Fin a) (Fin a) K) :=
  (Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))).toSubalgebra
    (Submodule.subset_span ⟨1, by simp⟩)
    (by
      intro x y hx hy
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp⟩)

theorem mem_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K)
    (x : Matrix (Fin a) (Fin a) K) :
    x ∈ spanAlg ρ ↔ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) := Iff.rfl

theorem isSemisimpleRing_spanAlg {Γ K : Type} [Group Γ] [Field K] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K)
    (h : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) :
    IsSemisimpleRing (spanAlg ρ) := by
  have : IsArtinianRing (spanAlg ρ) := IsArtinianRing.of_finite K _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply Subtype.ext
  refine h x.1 x.2 fun g => ?_
  let y : spanAlg ρ := ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩
  have hxy : x * y ∈ Ring.jacobson (spanAlg ρ) := Ideal.mul_mem_right _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson (spanAlg ρ)) := IsSemiprimaryRing.isNilpotent
  have h1 : (x * y) ^ n = 0 := by
    have := Ideal.pow_mem_pow hxy n
    rw [hn] at this
    simpa using this
  have h2 : IsNilpotent ((x * y : spanAlg ρ) : Matrix (Fin a) (Fin a) K) :=
    ⟨n, by simpa using congrArg Subtype.val h1⟩
  exact (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero

theorem isSSRep_of_trace_nondegenerate :
    ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K),
    (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) →
    IsSSRep ρ := by
  intro Γ K _ _ a ρ h W hW
  have := isSemisimpleRing_spanAlg ρ h
  let f : spanAlg ρ →+* Module.End K (Fin a → K) :=
    ((Matrix.toLinAlgEquiv' (R := K) (n := Fin a)).toAlgHom.comp (spanAlg ρ).val).toRingHom
  let : Module (spanAlg ρ) (Fin a → K) := Module.compHom _ f
  have hW' : ∀ x ∈ Submodule.span K
      (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)),
      ∀ v ∈ W, x.mulVec v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g v hv
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  let U : Submodule (spanAlg ρ) (Fin a → K) :=
    { toAddSubmonoid := W.toAddSubmonoid
      smul_mem' := fun x v hv => hW' x.1 x.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  let W' : Submodule K (Fin a → K) :=
    { toAddSubmonoid := U'.toAddSubmonoid
      smul_mem' := fun c v hv => by
        have : (c • (1 : Matrix (Fin a) (Fin a) K)).mulVec v ∈ U' :=
          U'.smul_mem ⟨c • 1, (spanAlg ρ).smul_mem (spanAlg ρ).one_mem c⟩ hv
        rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this }
  refine ⟨W', fun g v hv => ?_, ?_, ?_⟩
  · exact U'.smul_mem ⟨(ρ g : GL (Fin a) K), Submodule.subset_span ⟨g, rfl⟩⟩ hv
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    exact (Submodule.disjoint_def.1 hU.disjoint) v hv hv'
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hx hy

end GlobalTheory.TraceSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ProdTheta

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_differentiable (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (k : Fin r) : Differentiable ℂ (coordB D T b k) := by
  unfold coordB
  fun_prop

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b g hP hL hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB
    have hc := coordB_differentiable D T b
    fun_prop
  · intro x hx z
    have hx' := (hL x).1 hx
    choose m hm hU using fun k => hq _ (hx' k)
    have hre : Real.sqrt D.host.d / 2 * (Hf D T x x).re = ((∑ k, m k : ℤ) : ℝ) := by
      unfold Hf
      rw [hP, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T x = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
      unfold U U1 pullB Hf
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
      simp only [coordB_add]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.ProdTheta
end

