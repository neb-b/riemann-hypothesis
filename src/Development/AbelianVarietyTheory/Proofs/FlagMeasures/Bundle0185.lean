module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NeZeroOfMemRoots
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.SerSys.LabLoc

open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_roots_eq {f h : (ZMod g)[X]} (hf : f.Monic) (hh : h.Monic)
    (e : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar h) : f = h := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  rw [(IsAlgClosed.splits (f.map _)).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (h.map _)).eq_prod_roots_of_monic (hh.map _)]
  exact congrArg (fun m : Multiset (Formalism.CyclotomicNorms.Fbar g) => (m.map fun a => X - C a).prod) e

theorem ne_zero_of_mem_roots {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : x ≠ 0 := by
  rintro rfl
  have hf : f.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) ≠ 0 := (mem_roots'.1 hx).1
  have := (mem_roots'.1 hx).2
  rw [IsRoot, eval_map, eval₂_at_zero] at this
  exact h0 ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (by simpa using this))

theorem map_eq_map {τ : Formalism.CyclotomicNorms.Fbar g →* ℂ} (hτ : Set.InjOn τ {x | x ≠ 0}) {A B : Multiset (Formalism.CyclotomicNorms.Fbar g)}
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0) (e : A.map τ = B.map τ) : A = B := by
  rw [Multiset.ext]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Multiset.count_eq_zero.2 (fun h => hA 0 h rfl), Multiset.count_eq_zero.2 (fun h => hB 0 h rfl)]
  have key : ∀ C : Multiset (Formalism.CyclotomicNorms.Fbar g), (∀ y ∈ C, y ≠ 0) → C.count x = (C.map τ).count (τ x) := by
    intro C hC
    rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun y hy => ⟨fun h => h ▸ rfl, fun h => hτ hx (hC y hy) h⟩
  rw [key A hA, key B hB, e]

theorem actK_finset_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {ι : Type} (T : Finset ι) (a : ι → MonoidAlgebra ℂ (Gn g n)) :
    actK ρ (∑ i ∈ T, a i) = ∑ i ∈ T, actK ρ (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [actK]
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_one_of_mem {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 ρ) : actK ρ 1 v = v := by
  have hs : actK ρ 1 = ρ (lift g n 1) := by
    unfold actK
    rw [MonoidAlgebra.one_def, Finset.sum_eq_single 1]
    · simp
    · intro y _ hy
      simp [Finsupp.single_eq_of_ne hy]
    · simp
  have hk : red g n (Function.invFun (red g n) 1) = 1 := Function.invFun_eq ⟨1, map_one _⟩
  rw [hs, lift]
  have := (Submodule.mem_iInf _).1 hv ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  simpa using this

end GlobalTheory.SerSys.LabLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.KType

theorem cdom_step {n : ℕ} {ε : Fin n → Bool} {ν μ : Fin n → ℝ} (h : CDom ε ν μ) {a b : Fin n}
    (hab : a < b) (he : ε a = ε b) : CDom ε (ν - Formalism.REAL.root a b) μ := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩
  · intro i j hij
    by_cases h0 : c i j = 0
    · by_cases hj : j = b
      · by_cases hi : i = a
        · subst hi; subst hj; exact ⟨hab, he⟩
        · simp [h0, hi] at hij
      · simp [h0, hj] at hij
    · exact hc i j h0
  · have : μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b := by abel
    rw [this, hs]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cdom_word {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) : CDom ε (μ + wordWeightShift w) μ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have := cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1 := by
      simp only [wordWeightShift, Formalism.REAL.root]; abel
    rw [e]; exact this

theorem not_cdom_add {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + Pi.single a 1 - Pi.single b 1) μ := by
  rintro ⟨c, hc, hs⟩
  have e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1 := by abel
  rw [e] at hs
  have h1 := congrArg heightFunctional hs
  rw [height_functional_root] at h1
  have hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0 := by
    refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
    · intro x y hx hy; rw [height_functional_add]; linarith
    · intro i _
      refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
      · intro x y hx hy; rw [height_functional_add]; linarith
      · intro j _
        have h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j) := by
          rw [← height_functional_root i j]
          simp only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h2]
        by_cases h0 : c i j = 0
        · simp [h0]
        · have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem cdom_of_mem {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ V} (hR : KRel ε F) (hU : KUnit ε F) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε F μ x) (hy : y ∈ kSpan ε F x) (hy0 : y ≠ 0) (hw : IsWeight F ν y) :
    CDom ε ν μ := by
  by_contra hn
  rw [compact_span_eq_lowering hR hx] at hy
  have : lowSpan ε F x ≤ (ℂ ∙ y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw
      (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_
    rintro rfl
    exact hn (cdom_word μ w hw')
  exact hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))

theorem kType_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (μ : Fin n → ℝ) (u : V), u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → IsKTypeOf ε σ μ ((kSpan ε E u).map V.subtype)) ∧ ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H) (u : V), IsKTypeOf ε σ μ S → S ≤ V → (u : H) ∈ S → u ≠ 0 → IsWtOn (Kset ε) σ μ (u : H) → KHighest ε E μ u ∧ (kSpan ε E u).map V.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ V E hσ hD
  obtain ⟨-, hst, hwt⟩ := _root_.GlobalTheory.Jet.Coef.coef_flow n ε H σ V E hσ hD
  have hR : KRel ε E := glRel_kRel ε E hD.1
  have hU : KUnit ε E := isUnitary_kUnit ε E hD.2.1
  have hIrr : KIrr := kIrr_of highestWeightExists_holds
    (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))
  have hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S := by
    intro S hS
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS]
  have hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S →
      FiniteDimensional ℂ (S.comap V.subtype) := by
    intro S hS _
    exact (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  refine ⟨?_, ?_⟩
  · intro μ u hu0 hu hf
    have hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype) := inferInstance
    refine ⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩
    · intro S' hS' hK
      have hV : S' ≤ V := hS'.trans (Submodule.map_subtype_le V _)
      have hf' : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
      have hk : KStable ε E (S'.comap V.subtype) :=
        (hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)
      have hle : S'.comap V.subtype ≤ kSpan ε E u := by
        have := Submodule.comap_mono (f := V.subtype) hS'
        rwa [Submodule.comap_map_eq_of_injective V.injective_subtype] at this
      rcases hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h
      · left; rw [← hmc S' hV, h, Submodule.map_bot]
      · right; rw [← hmc S' hV, h]
    · exact ⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩
    · rintro ν _ ⟨y, hy, rfl⟩ hy0 hw
      exact cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)
  · rintro μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw
    have hw' : IsWeight E μ u := (hwt μ u).2 hw
    have hfc := hfd S hV hf
    have hk : KStable ε E (S.comap V.subtype) := (hst _ hfc).2 (by rw [hmc S hV]; exact hK)
    have hle : kSpan ε E u ≤ S.comap V.subtype := compact_span_le_stable huS hk
    have hfk : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hle
    refine ⟨⟨hw', ?_⟩, ?_, hfk⟩
    · intro a b hab he
      by_contra hne
      exact not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h))
        ((hwt _ _).1 (compact_weight_shift hR hw' he)))
    · rcases hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h
      · exfalso
        have : (u : H) ∈ (kSpan ε E u).map V.subtype := ⟨u, mem_compact_span_self u, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hu0 (Subtype.ext this)
      · exact h

end GlobalTheory.Jet.KType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.PoissonV

variable (ι κ : Type) [Fintype ι] [Fintype κ]


open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : MeasurePreserving (MeasurableEquiv.curry ι κ ℂ).symm volume volume := by
    refine ⟨(MeasurableEquiv.curry ι κ ℂ).symm.measurable, ?_⟩
    have hv : (volume : Measure (ι × κ → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [hv]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
      ext x
      simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using h.symm

def coords : EuclideanSpace ℂ (ι × κ) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a => x (w, a)
      invFun := fun y => WithLp.toLp 2 fun p => y p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords :
    MeasurePreserving (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ) volume volume :=
  (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry ι κ).comp (_root_.GlobalTheory.volume_preserving_ofLp_complex _)

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
theorem _root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords (x : EuclideanSpace ℂ (ι × κ)) :
    ∑ w, ∑ a, ‖_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ x w a‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

end GlobalTheory.FlagBase.PoissonV

namespace GlobalTheory.FlagBase

open PoissonV

open MeasureTheory NumberField Matrix Finset in
variable (ι κ : Type) [Fintype ι] [Fintype κ] in
private theorem inner_toLp_conj_eq_sum_re_dotProduct (u : EuclideanSpace ℂ (ι × κ))
    (y : ι → κ → ℂ) :
    inner ℝ u (WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2) : EuclideanSpace ℂ (ι × κ)) =
      ∑ w, (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ u w ⬝ᵥ y w).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [_root_.GlobalTheory.FlagBase.PoissonV.coords, dotProduct, Complex.re_sum, Complex.mul_re]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => mul_comm _ _


open MeasureTheory NumberField Matrix Finset in
theorem _root_.GlobalTheory.FlagBase.poisson_gaussV (E : Type) [Field E] [NumberField E] (j : ℕ)
    (L : Submodule ℤ (_root_.GlobalTheory.FlagBase.VecInf E j))
    [DiscreteTopology L] (hL : IsZLattice ℝ L) :
    Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) ∧
      Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) ∧
      ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x =
        (_root_.GlobalTheory.FlagBase.covAt E j L)⁻¹ *
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y ∧
      ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = 1 := by
  classical
  haveI := hL
  let e := _root_.GlobalTheory.FlagBase.PoissonV.coords (InfinitePlace E) (Fin j)
  let L' := ZLattice.comap ℝ L
    (e : EuclideanSpace ℂ (InfinitePlace E × Fin j) →ₗ[ℝ] _root_.GlobalTheory.FlagBase.VecInf E j)
  have hmemL : ∀ u, u ∈ L' ↔ e u ∈ L := fun u => Iff.rfl
  have hg : ∀ u, _root_.GlobalTheory.FlagBase.gaussV E j (e u) = Real.exp (-Real.pi * ‖u‖ ^ 2) := by
    intro u
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖e u w a‖ ^ 2) = _
    rw [_root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords]
  have hg' : ∀ x, _root_.GlobalTheory.FlagBase.gaussV E j x = Real.exp (-Real.pi * ‖e.symm x‖ ^ 2) := by
    intro x
    rw [← hg, ContinuousLinearEquiv.apply_symm_apply]
  let eL : L ≃ L' :=
    { toFun := fun y => ⟨e.symm y, by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact y.2⟩
      invFun := fun x => ⟨e x, (hmemL x).1 x.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  let ψ : _root_.GlobalTheory.FlagBase.VecInf E j ≃ EuclideanSpace ℂ (InfinitePlace E × Fin j) :=
    { toFun := fun y => WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2)
      invFun := fun z w a => starRingEnd ℂ (z (w, a))
      left_inv := fun y => by funext w a; simp
      right_inv := fun z => by ext p; simp }
  have hψ : ∀ y, _root_.GlobalTheory.FlagBase.gaussV E j y = Real.exp (-Real.pi * ‖ψ y‖ ^ 2) := by
    intro y
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖y w a‖ ^ 2) = _
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [ψ]
  have hinner : ∀ u y, inner ℝ u (ψ y) = ∑ w, (e u w ⬝ᵥ y w).re :=
    fun u y => inner_toLp_conj_eq_sum_re_dotProduct _ _ u y
  have hdual : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔
      ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
    intro y
    unfold _root_.GlobalTheory.FlagBase.dualAt
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => intro x _; exact ⟨0, by simp⟩
      | add y y' _ _ h h' =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        obtain ⟨z', hz'⟩ := h' x hx
        refine ⟨z + z', ?_⟩
        simp only [Pi.add_apply, dotProduct_add, Complex.add_re, Finset.sum_add_distrib, hz, hz']
        push_cast
        ring
      | smul n y _ h =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        refine ⟨n * z, ?_⟩
        simp only [Pi.smul_apply, dotProduct_smul, Complex.smul_re]
        rw [← Finset.smul_sum, hz, zsmul_eq_mul]
        push_cast
        ring
    · intro hy
      exact Submodule.subset_span hy
  have hmem : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔ ψ y ∈ _root_.GlobalTheory.dualLattice L' := by
    intro y
    rw [hdual, _root_.GlobalTheory.mem_dualLattice]
    constructor
    · intro h u hu
      obtain ⟨z, hz⟩ := h (e u) ((hmemL u).1 hu)
      exact ⟨z, by rw [hinner, hz]⟩
    · intro h x hx
      obtain ⟨m, hm⟩ := h (e.symm x) (by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact hx)
      refine ⟨m, ?_⟩
      rw [hm, hinner, ContinuousLinearEquiv.apply_symm_apply]
  let dL : _root_.GlobalTheory.FlagBase.dualAt E j L ≃ _root_.GlobalTheory.dualLattice L' := ψ.subtypeEquiv hmem
  let f : EuclideanSpace ℂ (InfinitePlace E × Fin j) → ℝ := fun u => Real.exp (-Real.pi * ‖u‖ ^ 2)
  have hsL : Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) :=
    ((eL.summable_iff (f := fun x : L' => f x)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L' Real.pi_pos)).congr fun x => by rw [hg']; rfl
  have hsD : Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) :=
    ((dL.summable_iff (f := fun z : _root_.GlobalTheory.dualLattice L' => f z)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq _ Real.pi_pos)).congr fun y => by rw [hψ]; rfl
  have hT1 : ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L', f x :=
    calc ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L, f (eL x) :=
          tsum_congr fun x => by rw [hg']; rfl
      _ = ∑' x : L', f x := eL.tsum_eq (fun x : L' => f x)
  have hT2 : ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
      ∑' z : _root_.GlobalTheory.dualLattice L', f z :=
    calc ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, f (dL y) :=
          tsum_congr fun y => by rw [hψ]; rfl
      _ = ∑' z : _root_.GlobalTheory.dualLattice L', f z := dL.tsum_eq (fun z : _root_.GlobalTheory.dualLattice L' => f z)
  haveI : (volume : Measure (_root_.GlobalTheory.FlagBase.VecInf E j)).IsAddHaarMeasure := by
    rw [← (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).map_eq]
    exact e.isAddHaarMeasure_map volume
  have hcov : _root_.GlobalTheory.FlagBase.covAt E j L = ZLattice.covolume L' volume := by
    show ZLattice.covolume L volume = _
    exact (ZLattice.covolume_comap L volume volume
      (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords _ _)).symm
  have hP := _root_.GlobalTheory.tsum_gaussian_lattice_eq_dualLattice L' one_pos
  simp only [mul_one, Real.one_rpow, div_one] at hP
  refine ⟨hsL, hsD, ?_, ?_⟩
  · rw [hT1, hT2, hcov]
    exact hP
  · have hI : ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = ∫ u, f u :=
      ((_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).integral_comp
        e.toHomeomorph.measurableEmbedding (_root_.GlobalTheory.FlagBase.gaussV E j)).symm.trans
        (integral_congr_ae (Filter.Eventually.of_forall fun u => hg u))
    rw [hI]
    show ∫ u, Real.exp (-Real.pi * ‖u‖ ^ 2) = 1
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm Real.pi_pos, div_self Real.pi_ne_zero,
      Real.one_rpow]

end GlobalTheory.FlagBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundOfDecGap
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem ptBound_of_decGap : GlobalTheory.DSId.DecGap → GlobalTheory.Deep.PtBound := by
  intro hD B d p q h hDS hsig hgap hh
  obtain ⟨him, hre, hle, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hrk : ∀ v, rkR (B.I.ε v) = min p q := fun v => by
    rw [← (hsig v).1, ← (hsig v).2]; rfl
  have hw : ∀ v, ‖B.w v‖ = 1 := fun v => (hDS v).2.2.1.1
  have hdec := fun v (g : UJ (B.I.ε v)) =>
    hD B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) (hDS v).1 (hDS v).2.1 h (hgap v)
      (by rw [hrk v]; exact hh) (uMat g) g.2 (B.w v) (hDS v).2.2.1.2 (B.w v) (hDS v).2.2.1.2
  have hd : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hDS v).2.2.2.1.le
  have key : ∀ (y : B.I.GA) (c : InfinitePlace B.I.F → ℝ),
      (∀ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ c v) →
      ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, c v := by
    intro y c hc
    have h1 : ∏ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ ∏ v, c v :=
      Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hc v
    have h0 : 0 ≤ ∏ v, c v := (Finset.prod_nonneg fun v _ => norm_nonneg _).trans h1
    unfold phe ph
    rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hd, mul_right_comm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hle _) hd) h1
      (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg hd hre)
  refine ⟨fun _ y => key y _ fun v => ?_, fun y => ?_, ?_, him, hre, fun y hy => ?_, fun v g => ?_⟩
  · have := (hdec v (y.1 v)).1
    rw [hw, mul_one, mul_one, hrk] at this
    exact this
  · have := key y (fun _ => 1) fun v => by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [(hDS v).2.1.2.2.1.2.1 _ (y.1 v).2, hw, mul_one]
    simpa using this
  · have h1 : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.GA).1 v)) (B.w v)⟫_ℂ = 1 := fun v => by
      have e : uMat ((1 : B.I.GA).1 v) = 1 := rfl
      rw [e, (hDS v).2.1.2.2.1.1.1]
      simp [inner_self_eq_norm_sq_to_K, hw]
    unfold phe ph
    simp only [h1, Finset.prod_const_one, star_one, mul_one]
    rfl
  · exact B.e_adm.2.2.2.2.1 _ (right_ne_zero_of_mul hy)
  · have := (hdec v g).2
    rwa [hw, mul_one, mul_one] at this

end GlobalTheory.Deep
end

