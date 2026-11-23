module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.SemistableReduction.Bundle0001
public import Mathlib
public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
section
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem ae_eval_ne_zero_of_ne_zero_fin : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0} :=
      ((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      have hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := hfin.measure_zero (volume : Measure ℂ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval_ne_zero_linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by
  set e := Fintype.equivFin ι
  set g := MvPolynomial.rename e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)
  set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
  have hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f := by
    intro x
    have hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x := by
      funext i
      simp [L', LinearEquiv.funCongrLeft_apply]
    simp only [g, MvPolynomial.eval_rename, hc]
  have hac : μ.map L' ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)
  have hmeasL : Measurable L' := L'.toContinuousLinearEquiv.continuous.measurable
  have hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0} :=
    (MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl
  rw [ae_map_iff hmeasL.aemeasurable hmeasS] at h1
  filter_upwards [h1] with x hx
  rwa [← hL']

theorem eval_blockScale_eq_prod_pow_mul {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ j, r b ^ s (b, j) = r b ^ a b
    rw [Finset.prod_pow_eq_pow_sum, hF s hs b]
  rw [h1]
  ring

def blockCoordEquiv (B n : ℕ) : (Fin B → EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (Fin B × Fin n → ℂ) :=
  (LinearEquiv.piCongrRight fun _ => WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (LinearEquiv.curry ℂ ℂ (Fin B) (Fin n)).symm

theorem blockCoordEquiv_apply {B n : ℕ} (y : Fin B → EuclideanSpace ℂ (Fin n)) (p : Fin B × Fin n) :
    blockCoordEquiv B n y p = WithLp.ofLp (y p.1) p.2 := rfl

theorem ae_toSphere (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  set E := EuclideanSpace ℂ (Fin n)
  set νS := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}
  have hZ : MeasurableSet Z := by
    have : Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      refine continuous_pi fun p => ?_
      unfold blockPoint spherePoint
      fun_prop
    exact this.measurable (measurableSet_singleton 0)
  have : (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : IsFiniteMeasure νS := by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance
  have : SigmaFinite ρ := by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance
  have hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)),
      MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0 :=
    ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0
  set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}
  have hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlin] with y hy
    exact hy
  have hSm : MeasurableSet S := by
    have : Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      exact (blockCoordEquiv B n).toContinuousLinearEquiv.continuous
    exact this.measurable (measurableSet_singleton 0)
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hprodSF : SigmaFinite (νS.prod ρ) := inferInstance
  have hT := measurePreserving_pi (hν := fun _ => hprodSF)
    (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
    (fun _ => νS.prod ρ) (fun _ => h1)
  have hA := measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
    (fun _ => νS) (fun _ => ρ)
  set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
  set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
    fun x b => homeomorphUnitSphereProd E (x b)
  have hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ)))) :=
    hZ.prod MeasurableSet.univ
  have hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ)) := A.measurable hW
  have e1 := Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS)
    (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ
  rw [← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet] at e1
  set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)
  have hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx
    have hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0 := by
      simpa [A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hx
    have hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) *
        blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p := by
      funext p
      have hne : ‖(x p.1 : E)‖ ≠ 0 := norm_ne_zero_iff.2 (x p.1).2
      simp only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]
      rw [← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]
    show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0
    have hsc := eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ))
      (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))
    rw [hcoord, hsc, hx', mul_zero]
  have hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      Subtype.val = (volume : Measure E).restrict {0}ᶜ :=
    fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _
  have hmSF : ∀ i : Fin B, SigmaFinite
      (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val) := by
    intro i; rw [hmap i]; infer_instance
  have hG : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G =
      Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ := by
    rw [Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]
    exact congrArg _ (funext hmap)
  have hGm : Measurable G := Measurable.of_eval fun b => measurable_subtype_coe.comp
    (measurable_pi_apply b)
  have hzero : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0 := by
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)
  have hρ : ρ Set.univ ≠ 0 := by
    intro h
    have h2 := measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h
    have h3 := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩
    rw [show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3] at h2
    rw [ENNReal.ofReal_eq_zero] at h2
    have h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1) := by
      positivity
    exact absurd h2 (not_le.2 h4)
  have hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hρ
  rw [hzero] at e1
  have hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0 := by
    rcases mul_eq_zero.1 e1.symm with h | h
    · exact h
    · exact absurd h hpiρ
  rw [measure_eq_zero_iff_ae_notMem] at hZ0
  filter_upwards [hZ0] with z hz
  exact hz

theorem blockSphereMeasure_eq (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem ae_blockSphere_eval_ne_zero (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  rw [blockSphereMeasure_eq]
  exact Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

def blockIndexWeight {B n : ℕ} (b : Fin B) : Fin B × Fin n → ℕ := fun p => if p.1 = b then 1 else 0

theorem weight_lh0BlockWt_apply {B n : ℕ} (b : Fin B) (s : Fin B × Fin n →₀ ℕ) :
    Finsupp.weight (blockIndexWeight (n := n) b) s = ∑ j : Fin n, s (b, j) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [blockIndexWeight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b (fun x _ hx => by simp [hx]) (by simp)]
  simp

theorem isMultiHomogeneous_iff_forall_weighted_lh0BlockWt {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by
  simp only [IsMultiHomogeneous, IsWeightedHomogeneous, weight_lh0BlockWt_apply, mem_support_iff]
  constructor
  · intro h b d hd
    exact h d hd b
  · intro h s hs b
    exact h b hs

theorem eval_mul_of_isMultiHomogeneous {B n : ℕ} {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (c : ℂ) (z : Fin B × Fin n → ℂ) :
    eval (fun p => c * z p) g = c ^ (∑ b, a b) * eval z g := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hdeg : ∑ p, s p = ∑ b, a b := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun b _ => hg s hs b
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private lemma sum_primitiveRoot_pow_mul_inv_pow_eq_ite {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ}
    (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (ζ ^ a * ζ⁻¹ ^ b) ^ (j : ℕ) = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hz : ζ ≠ 0 := hζ.ne_zero hN.ne'
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ a * ζ⁻¹ ^ b) ^ j) N]
  split_ifs with hab
  · subst hab
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    simp
  · have hω1 : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rwa [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hz)] at h
    have hωN : (ζ ^ a * ζ⁻¹ ^ b) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a, Nat.mul_comm b, pow_mul, pow_mul, inv_pow,
        hζ.pow_eq_one]
      simp
    rw [geom_sum_eq hω1, hωN]
    simp

theorem exists_torus_coeff_le {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖AddMonoidAlgebra.coeff g s‖ ≤ ‖eval z g‖ := by
  classical
  by_cases hs : s ∈ g.support
  swap
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [show AddMonoidAlgebra.coeff g s = 0 by simpa using hs, norm_zero]
    exact norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = g.totalDegree + 1 := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by omega
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hN0⟩
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN0
  have hlt : ∀ d ∈ g.support, ∀ i, d i < N := by
    intro d hd i
    have h1 : d i ≤ d.sum fun _ e => e := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    have h2 := le_totalDegree hd
    omega
  let z : (ι → Fin N) → ι → ℂ := fun k i => ζ ^ (k i : ℕ)
  let c : (ι → Fin N) → ℂ := fun k => ∏ i, ζ⁻¹ ^ ((k i : ℕ) * s i)
  have key : ∑ k, eval (z k) g * c k = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
    calc ∑ k, eval (z k) g * c k
        = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * ∏ i, ∑ j : Fin N, (ζ ^ d i * ζ⁻¹ ^ s i) ^ (j : ℕ) := by
          simp only [eval_eq', Finset.sum_mul, z, c]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm (d i), Nat.mul_comm (s i)]
      _ = ∑ d ∈ g.support, AddMonoidAlgebra.coeff g d * (if d = s then (N : ℂ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          congr 1
          simp_rw [sum_primitiveRoot_pow_mul_inv_pow_eq_ite hζ (hlt d hd _) (hlt s hs _)]
          split_ifs with hds
          · subst hds
            simp
          · obtain ⟨i, hi⟩ : ∃ i, d i ≠ s i := by
              by_contra h
              push_neg at h
              exact hds (Finsupp.ext h)
            exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      _ = (N : ℂ) ^ Fintype.card ι * AddMonoidAlgebra.coeff g s := by
          rw [Finset.sum_eq_single s (fun d _ hd => by simp [hd]) (fun h => absurd hs h)]
          simp [mul_comm]
  by_contra hcon
  push_neg at hcon
  have hlt2 : ∀ k, ‖eval (z k) g * c k‖ < ‖AddMonoidAlgebra.coeff g s‖ := by
    intro k
    have hc : ‖c k‖ = 1 := by simp [c, norm_prod, norm_pow, norm_inv, hζn]
    rw [norm_mul, hc, mul_one]
    exact hcon (z k) (fun i => by simp [z, norm_pow, hζn])
  have hsum := norm_sum_le (Finset.univ : Finset (ι → Fin N)) (fun k => eval (z k) g * c k)
  have hsum2 : ∑ k, ‖eval (z k) g * c k‖ < ∑ _k : ι → Fin N, ‖AddMonoidAlgebra.coeff g s‖ :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hlt2 k)
  rw [key, norm_mul, norm_pow, Complex.norm_natCast] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul] at hsum2
  push_cast at hsum2
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.BWPolyB
section
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem bwp_ext_poly {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ) (g D : (σ → ℂ) → ℂ)
    (w : σ → ℂ) (hw : ∀ z, {s : ℂ | D (z + s • w) = 0}.Finite)
    (hD : ∀ z v, D z ≠ 0 → {t : ℂ | D (z + t • v) = 0}.Finite)
    (hL : ∀ z v, {t : ℂ | D (z + t • v) = 0}.Finite → ∃ Q : ℂ[X], Q.natDegree ≤ k ∧
      ∀ t, D (z + t • v) ≠ 0 → g (z + t • v) = Q.eval t) :
    ∃ F : MvPolynomial σ ℂ, ∀ z, D z ≠ 0 → g z = MvPolynomial.eval z F := by

  have hw' := fun y => hL y w (hw y)
  choose Qw hQd hQ using hw'

  have hv' := fun (y v : σ → ℂ) (h : D y ≠ 0) => hL y v (hD y v h)
  choose P hPd hP using hv'
  let G : (σ → ℂ) → ℂ := fun y => (Qw y).eval 0
  have hsep : ∀ y m, ∃ Q : ℂ[X], Q.natDegree ≤ k ∧ ∀ t, G (Function.update y m t) = Q.eval t := by
    intro y m
    set z : σ → ℂ := Function.update y m 0
    set e : σ → ℂ := Pi.single m 1
    have hupd : ∀ t, Function.update y m t = z + t • e := by
      intro t; ext i
      by_cases hi : i = m
      · subst hi; simp [z, e]
      · simp [z, e, Function.update_apply, hi, Pi.single_apply]
    let Pc : ℂ → ℂ[X] := fun c => if h : D (z + c • w) = 0 then 0 else P (z + c • w) e h
    let R : Finset ℂ → ℂ[X] := fun S =>
      ∑ c ∈ S, Polynomial.C ((Lagrange.basis S id c).eval 0) * Pc c
    have hRdeg : ∀ S, (R S).natDegree ≤ k := by
      intro S
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      simp only [Pc]
      split_ifs with h
      · simp
      · exact hPd _ _ h

    have key : ∀ S : Finset ℂ, S.card = k + 1 → (∀ c ∈ S, D (z + c • w) ≠ 0) →
        ∀ t, (∀ c ∈ S, D ((z + t • e) + c • w) ≠ 0) → G (z + t • e) = (R S).eval t := by
      intro S hS hSz t ht
      simp only [G, R]
      rw [bwp_eval_eq_lagrange S (Qw (z + t • e)) k hS (hQd _) 0, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Polynomial.eval_mul, Polynomial.eval_C, ← hQ _ c (ht c hc)]
      congr 1
      simp only [Pc, dif_neg (hSz c hc)]
      rw [← hP _ _ (hSz c hc) t (by rw [add_right_comm]; exact ht c hc), add_right_comm]
    have hbad : ∀ S : Finset ℂ, (∀ c ∈ S, D (z + c • w) ≠ 0) →
        {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0}.Finite := by
      intro S hSz
      have : {t : ℂ | ∃ c ∈ S, D ((z + t • e) + c • w) = 0} =
          ⋃ c ∈ S, {t : ℂ | D ((z + c • w) + t • e) = 0} := by
        ext t; simp [add_right_comm]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet (fun c hc => hD _ e (hSz c hc))
    obtain ⟨S0, hS0, hS0z⟩ := bwp_exists_nodes {s | D (z + s • w) = 0} (hw z) k
    refine ⟨R S0, hRdeg S0, fun t0 => ?_⟩
    rw [hupd]
    obtain ⟨S1, hS1, hS1z⟩ := bwp_exists_nodes
      ({s | D (z + s • w) = 0} ∪ {s | D ((z + t0 • e) + s • w) = 0})
      ((hw z).union (hw (z + t0 • e))) k
    have hS1a : ∀ c ∈ S1, D (z + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inl h)
    have hS1b : ∀ c ∈ S1, D ((z + t0 • e) + c • w) ≠ 0 := fun c hc h => hS1z c hc (Or.inr h)
    have hS0a : ∀ c ∈ S0, D (z + c • w) ≠ 0 := fun c hc h => hS0z c hc h
    have hRR : R S0 = R S1 := by
      refine bwp_poly_eq_of_eval_eq_off _ _ _ ((hbad S0 hS0a).union (hbad S1 hS1a)) (fun t ht => ?_)
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at ht
      rw [← key S0 hS0 hS0a t ht.1, ← key S1 hS1 hS1a t ht.2]
    rw [hRR, key S1 hS1 hS1a t0 hS1b]
  obtain ⟨F, hF⟩ := bwp_sepPoly k G hsep
  refine ⟨F, fun z hz => ?_⟩
  rw [← hF]
  have := hQ z 0 (by simpa using hz)
  simpa [G] using this

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.FinrankRestrictTotalDegree
section
namespace ReciprocityTheory.MultiplicativeHeights

noncomputable def degreeLeEquivAntidiag (D e : ℕ) :
    {α : Fin D →₀ ℕ // α.degree ≤ e} ≃
      ((Finset.univ : Finset (Fin (D + 1))).finsuppAntidiag e) where
  toFun α := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (e - α.1.degree) (⇑α.1)), by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    have := α.2
    omega⟩
  invFun β := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail ⇑β.1), by
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    ext i
    simp
  right_inv β := by
    apply Subtype.ext
    ext i
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero]
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
      omega
    · simp [Fin.tail]

theorem card_degree_le (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by
  rw [Nat.card_congr (degreeLeEquivAntidiag D e), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show D + 1 + e - 1 = D + e by omega, ← Nat.choose_symm_add, add_comm]

end ReciprocityTheory.MultiplicativeHeights
end

