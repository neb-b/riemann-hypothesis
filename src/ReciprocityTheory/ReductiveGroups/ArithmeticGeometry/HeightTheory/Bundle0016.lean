module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0014
public import ReciprocityTheory.SemistableReduction.Bundle0018
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormB

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AeEvTNeZero
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem ae_evT_ne_zero (sg : K →+* ℂ) (q : KTp K d.D d.N) (hq : q ≠ 0) (m : Fin (d.D + 1) → ℕ)
    (hm : m 0 = 0) (hqm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m q) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)), d.evT sg 0 (d.tOf z) q ≠ 0 := by
  classical
  have hnpos : 0 < d.N + 1 := Nat.succ_pos _
  have hqm' : ∀ s ∈ q.support, ∀ b, ∑ j, s (b, j) = m b := hqm

  let ψ : Fin d.D × Fin (d.N + 1) → TVar d.D d.N := fun p => (p.1.succ, p.2)
  have hψ : Function.Injective ψ := by
    intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (Fin.succ_injective _ h1) h2
  have hvars : (q.vars : Set (TVar d.D d.N)) ⊆ Set.range ψ := by
    intro v hv
    rcases v with ⟨i, j⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exfalso
      obtain ⟨s, hs, hsv⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h0 := hqm' s hs 0
      rw [hm] at h0
      have hz : s ((0 : Fin (d.D + 1)), j) = 0 :=
        (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      exact (Finsupp.mem_support_iff.1 hsv) hz
    · exact ⟨(k, j), rfl⟩
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q ψ hψ hvars
  obtain ⟨g, hgdef⟩ : ∃ g : MvPolynomial (Fin d.D × Fin (d.N + 1)) ℂ,
      g = MvPolynomial.map sg q' := ⟨_, rfl⟩

  have hev : ∀ z, d.evT sg 0 (d.tOf z) q = MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) g := by
    intro z
    rw [hgdef, MvPolynomial.eval_map, ← hq']
    unfold ReciprocityTheory.ChartRestriction.G.T0.Data.evT
    rw [MvPolynomial.eval₂_rename]
    congr 1

  have hg : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin d.D => m b.succ) g := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous
    intro s hs b
    have hs' : AddMonoidAlgebra.coeff q' s ≠ 0 := by
      rw [hgdef, MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at hs
      intro h0
      rw [h0, map_zero] at hs
      exact hs rfl
    have hmem : Finsupp.mapDomain ψ s ∈ q.support := by
      rw [MvPolynomial.mem_support_iff, ← hq', MvPolynomial.coeff_rename_mapDomain ψ hψ]
      exact hs'
    exact (Finset.sum_congr rfl fun j _ => (Finsupp.mapDomain_apply_of_injective hψ s (b, j)).symm).trans
      (hqm' _ hmem b.succ)

  have hg0 : g ≠ 0 := by
    rw [hgdef]
    intro h
    apply hq
    rw [← hq']
    have h' : q' = 0 := MvPolynomial.map_injective (f := sg) sg.injective (by rw [h, map_zero])
    rw [h', map_zero]

  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.1 hg0
  obtain ⟨z, hz1, hzle⟩ := ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le g s
  have hz0 : MvPolynomial.eval z g ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzle
    exact hs (norm_le_zero_iff.1 hzle)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt ((d.N + 1 : ℕ) : ℝ))⁻¹ := ⟨_, rfl⟩
  have hrpos : 0 < r := by
    rw [hr]
    exact inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 hnpos))
  have hvec : ∀ b : Fin d.D, (WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
      EuclideanSpace ℂ (Fin (d.N + 1))) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 := by
    intro b
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    have hterm : ∀ j : Fin (d.N + 1), ‖(WithLp.toLp 2 (fun j : Fin (d.N + 1) => (r : ℂ) * z (b, j)) :
        EuclideanSpace ℂ (Fin (d.N + 1))) j‖ ^ 2 = r ^ 2 := by
      intro j
      show ‖(r : ℂ) * z (b, j)‖ ^ 2 = r ^ 2
      rw [norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hr, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      mul_inv_cancel₀ (Nat.cast_pos.2 hnpos).ne', Real.sqrt_one]
  let u : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) := fun b => ⟨_, hvec b⟩
  have hu : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint u) g ≠ 0 := by
    have hbp : ReciprocityTheory.MultiplicativeHeights.blockPoint u = fun p => (r : ℂ) * z p := by
      funext p
      rfl
    rw [hbp, ReciprocityTheory.MultiplicativeHeights.eval_mul_of_isMultiHomogeneous hg]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hrpos.ne')) hz0

  have key := ReciprocityTheory.MultiplicativeHeights.null_of_logBound hnpos ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (ReciprocityTheory.MultiplicativeHeights.blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
      hnpos d.D) _ g u hg hu
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ key
  intro w hw
  simp only [Set.mem_setOf_eq, not_not] at hw ⊢
  rw [← hev w]
  exact hw

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ContinuousTorusPoint
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed

section

variable {K : Type} [Field K] [NumberField K] {κ : Type} [Fintype κ]

theorem map_ne_zero_of_ne_zero {f : MvPolynomial κ K} (hf : f ≠ 0) (σ : K →+* ℂ) :
    MvPolynomial.map σ f ≠ 0 := fun h => hf ((MvPolynomial.map_injective σ σ.injective) (by rw [h, map_zero]))

end

theorem logHeight_le_torusHeight {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) :
    h0 f ≤ hTX5 f := by
  unfold h0 hTX5
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine add_le_add le_rfl (Finset.sum_le_sum fun σ _ => ?_)
  exact sphereLeTorus B n a _ hn (map_ne_zero_of_ne_zero hf σ) (isMultiHomogeneous_map_ring a f ha σ)

theorem continuous_torusPoint' {κ : Type} : Continuous (fun θ : κ → ℝ => torusPoint θ) := by
  unfold torusPoint
  exact continuous_pi fun i => Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))

theorem measurable_log_eval_torus {κ : Type} [Fintype κ] (f : MvPolynomial κ ℂ) :
    Measurable (fun θ : κ → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖) := (Real.measurable_log.comp (continuous_norm.comp ((MvPolynomial.continuous_eval f).comp continuous_torusPoint')).measurable)

theorem torusProb_map_comp {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) :
    Measure.map (fun θ : κ' → ℝ => θ ∘ e) (torusProb κ') = torusProb κ := by
  classical
  have hmeas : Measurable (fun θ : κ' → ℝ => θ ∘ e) :=
    Measurable.of_eval (fun a => measurable_pi_apply (e a))
  unfold torusProb
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun θ : κ' → ℝ => θ ∘ e) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.extend e s (fun _ => Set.univ)) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    constructor
    · intro h y
      by_cases hy : ∃ a, e a = y
      · obtain ⟨a, rfl⟩ := hy
        rw [he.extend_apply]
        exact h a
      · rw [Function.extend_apply' _ _ _ hy]
        trivial
    · intro h a
      have h1 := h (e a)
      rwa [he.extend_apply] at h1
  rw [hpre, Measure.pi_pi]
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hν : ν Set.univ = 1 := by simp [ν]
  calc ∏ y, ν (Function.extend e s (fun _ => Set.univ) y)
      = ∏ y ∈ Finset.univ.image e, ν (Function.extend e s (fun _ => Set.univ) y) := by
        refine (Finset.prod_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
        have hy' : ¬ ∃ a, e a = y := by simpa using hy
        rw [Function.extend_apply' _ _ _ hy', hν]
    _ = ∏ a, ν (s a) := by
        rw [Finset.prod_image (fun a _ b _ h => he h)]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        rw [he.extend_apply]

theorem torusMean_rename {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ → κ')
    (he : Function.Injective e) (f : MvPolynomial κ ℂ) :
    torusMean (MvPolynomial.rename e f) = torusMean f := by
  unfold torusMean
  simp_rw [MvPolynomial.eval_rename]
  rw [← torusProb_map_comp e he, MeasureTheory.integral_map]
  · rfl
  · exact (Measurable.of_eval fun i => measurable_pi_apply (e i)).aemeasurable
  · exact (measurable_log_eval_torus f).aestronglyMeasurable

theorem gaussAbs_rename_of_injective {K : Type} [Field K] [NumberField K] {κ κ' : Type} (e : κ → κ')
    (he : Function.Injective e) (w : FinitePlace K) (f : MvPolynomial κ K) :
    gaussAbs w (MvPolynomial.rename e f) = gaussAbs w f := by
  classical
  unfold gaussAbs
  rw [MvPolynomial.support_rename_of_injective he, Finset.sup_image]
  congr 1
  refine Finset.sup_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, MvPolynomial.coeff_rename_mapDomain e he]

theorem hTX5_rename {K : Type} [Field K] [NumberField K] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (e : κ → κ') (he : Function.Injective e) (f : MvPolynomial κ K) :
    hTX5 (MvPolynomial.rename e f) = hTX5 f := by
  unfold hTX5
  congr 2
  · exact finsum_congr fun w => by rw [gaussAbs_rename_of_injective e he w f]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MvPolynomial.map_rename, torusMean_rename e he]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DecompBlock0
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable abbrev sub0 (x : Fin (d.N + 1) → K) : KTp K d.D d.N →ₐ[K] KTp K d.D d.N :=
  MvPolynomial.aeval (fun v : TVar d.D d.N =>
    if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v)


set_option synthInstance.maxHeartbeats 400000 in
theorem finYX4 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI := d.algLE h c
    letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) (d.FracFieldPositiveRowsOmega c))) := by
  letI := d.algLE h c
  letI := (VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1))).toAlgebra
  letI := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := by
    classical
    obtain ⟨e, -, -, hsp⟩ := hd.a4
    refine ⟨⟨Finset.univ.image (fun k : Fin d.del => algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))), ?_⟩⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨q, hq, p, hp⟩ := hsp (fun c' => if hc : c' = c then hc ▸ y else 0)
    have hpc : d.sH c q * y = ∑ k, d.sH c (p k) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
        (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      have h1 := hp c
      first
        | (simp only [dif_pos (rfl : c = c)] at h1; exact h1)
        | simpa using h1
    have hq0 := hq c
    have hKT : ∀ r : KTp K d.D d.N, d.KTtoS h c (algebraMap _ _ r) = d.sH c r := fun r => by
      simp [Data.KTtoS]
    have hy : y = ∑ k, (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (p k) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q) •
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) := by
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_div₀, hKT,
        div_mul_eq_mul_div, ← Finset.sum_div, ← hpc]
      first
        | exact (mul_div_cancel_left₀ y hq0).symm
        | field_simp
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact Module.Finite.of_equiv_equiv d.eLX4 (d.eEX4 c)
    (RingHom.ext fun q => (d.fieldEquiv_compat_liftY h c q).symm)

set_option synthInstance.maxHeartbeats 400000 in
theorem decomp_block0 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ (L E : Type) (_ : Field L) (_ : Field E) (_ : Algebra L E) (_ : FiniteDimensional L E)
      (eL : KTf K d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (eE : OmS (Ω c) d.D d.N ≃+* FractionRing (MvPolynomial (Fin (d.N + 1)) E)),
      (∀ q : KTf K d.D d.N, eE (d.KTtoS h c q) = VariableBasisExtension.liftY (eL q)) ∧
      (∀ r : Ω c, ∃ e : E, eE (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap (MvPolynomial (Fin (d.N + 1)) E) (FractionRing (MvPolynomial (Fin (d.N + 1)) E))
          (MvPolynomial.C e)) ∧
      ∀ l : L, ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x P = P) ∧ (∀ x, d.sub0 x Q = Q) ∧
        eL.symm (algebraMap (MvPolynomial (Fin (d.N + 1)) L)
            (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (MvPolynomial.C l)) =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q := by
  letI := d.algLE h c
  refine ⟨d.FracFieldPositiveRowsBase, d.FracFieldPositiveRowsOmega c, inferInstance, inferInstance, inferInstance,
    FractionFieldVariableLift.finiteDimensional_of_liftY (σ := Fin (d.N + 1)) (d.finYX4 hd h c), d.eLX4, d.eEX4 c,
    fun q => d.fieldEquiv_compat_liftY h c q, fun r => ?_, fun l => ?_⟩
  · refine ⟨algebraMap (d.PolyRingPositiveRowsOmega c) (d.FracFieldPositiveRowsOmega c) (MvPolynomial.C r), ?_⟩
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq, d.eEX4_algebraMap, FractionFieldVariableLift.hE_C]
    simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := d.PolyRingPositiveRowsBase) l
    have hfix : ∀ (x : Fin (d.N + 1) → K) (p : d.PolyRingPositiveRowsBase),
        d.sub0 x (MvPolynomial.rename Subtype.val p) = MvPolynomial.rename Subtype.val p := by
      intro x p
      have hc : (d.sub0 x).comp (MvPolynomial.rename (R := K)
          (Subtype.val : {v : TVar d.D d.N // v.1 ≠ 0} → TVar d.D d.N)) =
          MvPolynomial.rename Subtype.val := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [Data.sub0, v.2]
      exact AlgHom.congr_fun hc p
    refine ⟨MvPolynomial.rename Subtype.val p, MvPolynomial.rename Subtype.val q, ?_,
      fun x => hfix x p, fun x => hfix x q, ?_⟩
    · exact fun h0 => nonZeroDivisors.ne_zero hq
        (MvPolynomial.rename_injective _ Subtype.val_injective (h0.trans (map_zero _).symm))
    · rw [RingEquiv.symm_apply_eq, map_div₀ d.eLX4, d.eLX4_algebraMap, d.eLX4_algebraMap,
        FractionFieldVariableLift.hL_rename, FractionFieldVariableLift.hL_rename]
      simp only [FractionFieldVariableLift.toFracY, RingHom.comp_apply, MvPolynomial.map_C]
      exact map_div₀ ((algebraMap (MvPolynomial (Fin (d.N + 1)) d.FracFieldPositiveRowsBase) _).comp MvPolynomial.C) _ _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DiscLocal
section
set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscOmL

open IsDedekindDomain IsLocalRing Module

variable {R F : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R F] in
theorem prod_zpow {κ G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset κ)
    (f : κ → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hx]

theorem disc_local (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (g : R) (hg : p = Ideal.span {g})
    (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c) (hli : LinearIndependent F b)
    (hb : ∀ k c, ∀ w ∈ HNm.OverR (R := R) (F := F) (L := L c) p,
      0 ≤ w (b k c) + (n c w : WithTop ℤ)) :
    ∃ a s : R, s ∉ p ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
        algebraMap R F g ^ (2 * ∑ c, ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
          (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w) *
        algebraMap R F s =
        algebraMap R F a := by
  classical
  let O := Localization.AtPrime p
  letI : Algebra O F := IsLocalization.localizationAlgebraOfSubmonoidLe O F p.primeCompl
    (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsScalarTower R O F := IsLocalization.localization_isScalarTower_of_submonoid_le O F
    p.primeCompl (nonZeroDivisors R) (Ideal.primeCompl_le_nonZeroDivisors p)
  haveI : IsFractionRing O F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl O F
  obtain ⟨hdvr, hirr⟩ := ValUFD.loc_dvr p hp g hg
  haveI := hdvr
  letI : ∀ c, Algebra O (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap O F)).toAlgebra
  haveI : ∀ c, IsScalarTower O F (L c) := fun c => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ c, Algebra R (L c) := fun c => ((algebraMap F (L c)).comp (algebraMap R F)).toAlgebra
  haveI : ∀ c, IsScalarTower R O (L c) := fun c => IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap F (L c) (algebraMap R F x) =
      algebraMap F (L c) (algebraMap O F (algebraMap R O x))
    rw [IsScalarTower.algebraMap_apply R O F x])
  have hded : ∀ c, IsDedekindDomain (integralClosure O (L c)) := fun c =>
    (ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F (L c)).1
  have hfr : ∀ c, IsFractionRing (integralClosure O (L c)) (L c) := fun c =>
    integralClosure.isFractionRing_of_finite_extension F (L c)
  have hset : ∀ c, ValPl.PlacesOver O (L c) = HNm.OverR (R := R) (F := F) (L := L c) p := fun c => by
    ext w
    simp only [ValPl.PlacesOver, HNm.OverR, Set.mem_ofPred_eq]
    rw [← ValPl.placesOver_iff_loc (R := R) p w]
    rfl
  have hG : ∀ c, ∃ gc : L c, gc ≠ 0 ∧ (∀ w ∈ ValPl.PlacesOver O (L c), w gc = n c w) ∧
      ∀ y, (∀ w ∈ ValPl.PlacesOver O (L c), 0 ≤ w y + (n c w : WithTop ℤ)) ↔
        gc * y ∈ integralClosure O (L c) := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨gc, hg0, hgv⟩ := HDiscVal.exists_val_eq O F (n c)
    refine ⟨gc, hg0, hgv, fun y => ?_⟩
    rw [HDiscVal.mem_integralClosure_iff O F]
    refine forall₂_congr fun w hw => ?_
    rw [AddValuation.map_mul, hgv w hw, add_comm]
  choose gc hgc0 hgcv hgciff using hG
  have hbI : ∀ k c, gc c * b k c ∈ integralClosure O (L c) := fun k c =>
    (hgciff c _).mp (fun w hw => hb k c w (hset c ▸ hw))
  obtain ⟨nn, t, u, -, hdisc⟩ := HDiscLat.lattice_main (R := O) (F := F) hirr gc hgc0 hm b hbI hli
  set Nc : ι → ℤ := fun c => ∑ᶠ (w : AddValuation (L c) (WithTop ℤ))
    (_ : w ∈ HNm.OverR (R := R) (F := F) (L := L c) p), (HNm.fz (F := F) w : ℤ) * n c w with hNc
  have hN : ∀ c, ∃ uc : O, IsUnit uc ∧ Algebra.norm F (gc c) =
      algebraMap R F g ^ Nc c * algebraMap O F uc := fun c => by
    haveI := hded c
    haveI := hfr c
    obtain ⟨uc, huc, hn⟩ := ValPl.norm_eq_places (O := O) (F := F) (gc c) (hgc0 c) hirr
    refine ⟨uc, huc, ?_⟩
    rw [hn, ← IsScalarTower.algebraMap_apply R O F g, hset c]
    congr 2
    refine finsum_congr fun w => finsum_congr fun hw => ?_
    rw [← hset c] at hw
    rw [hgcv c w hw, WithTop.untopD_coe]
    rfl
  choose uc huc hNe using hN
  set X := algebraMap R F g with hX
  have hX0 : X ≠ 0 := by
    rw [hX, map_ne_zero_iff _ (IsFractionRing.injective R F)]
    rintro rfl
    have : p = ⊥ := by rw [hg, Ideal.span_singleton_eq_bot]
    subst this
    simp at hp
  let U : Oˣ := ∏ c, (huc c).unit
  have hprod : ∏ c, Algebra.norm F (gc c) = X ^ (∑ c, Nc c) * algebraMap O F (U : O) := by
    rw [Finset.prod_congr rfl fun c _ => hNe c, Finset.prod_mul_distrib, HDiscOmL.prod_zpow hX0,
      ← map_prod]
    congr 2
    simp only [U, Units.coe_prod, IsUnit.unit_spec]
  rw [hprod] at hdisc
  set Dt := (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det with hDt
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective p.primeCompl
    ((u : O) * ((algebraMap R O g) ^ (2 * nn + t)) * ((U⁻¹ : Oˣ) : O) * ((U⁻¹ : Oˣ) : O))
  refine ⟨a, s, s.2, ?_⟩
  have hsF : algebraMap O F (IsLocalization.mk' O a s) * algebraMap R F s = algebraMap R F a := by
    rw [IsScalarTower.algebraMap_apply R O F s, IsScalarTower.algebraMap_apply R O F a, ← map_mul,
      IsLocalization.mk'_spec]
  simp only at has
  rw [← hsF, has]
  congr 1
  set V := algebraMap O F (U : O)
  set V' := algebraMap O F ((U⁻¹ : Oˣ) : O)
  have hU : V * V' = 1 := by
    simp only [V, V']
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : X ^ (2 * ∑ c, Nc c) = (X ^ (∑ c, Nc c)) ^ 2 := by
    rw [mul_comm, zpow_mul]
    norm_cast
  have e1 : algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t) * ((U⁻¹ : Oˣ) : O) *
      ((U⁻¹ : Oˣ) : O)) = algebraMap O F ((u : O) * (algebraMap R O g) ^ (2 * nn + t)) * V' * V' := by
    simp only [V', map_mul]
  rw [h2, e1, ← hdisc]
  calc Dt * (X ^ ∑ c, Nc c) ^ 2 = Dt * (X ^ ∑ c, Nc c) ^ 2 * (V * V') * (V * V') := by
        rw [hU]; ring
    _ = Dt * ((X ^ ∑ c, Nc c) * V) ^ 2 * V' * V' := by ring

end HDiscOmL

end ReciprocityTheory.ChartRestriction.G.T0
end

