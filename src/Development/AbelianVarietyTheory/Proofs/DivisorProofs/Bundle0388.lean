module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import GroundTheory.AutomorphicForms.GKModules.Garding
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_single : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (0 + 1) => GlobalTheory.CechOne.fB A B) (GlobalTheory.CechOne.fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_cone_one) | (exact GlobalTheory.CechOne.isLimit_cone_one) | (intros; apply GlobalTheory.CechOne.isLimit_cone_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquareStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (1 + 1) => GlobalTheory.CechOne.fB A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (GlobalTheory.CechOne.y1 A B) (GlobalTheory.CechOne.hy1 A B))) := by
  first | (exact @GlobalTheory.CechOne.isLimit_widePullback_tensor) | (exact GlobalTheory.CechOne.isLimit_widePullback_tensor) | (intros; apply GlobalTheory.CechOne.isLimit_widePullback_tensor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
section
noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights

theorem isProbabilityMeasure_gaussProb {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (gaussProb n) := by
  have hp := GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn
  haveI := (_root_.GlobalTheory.SphereMeanDrop.radProb_log_mean n hn).1
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  rw [← hp.map_eq]
  infer_instance

theorem eval_blockScale {B n : ℕ} (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hm : IsMultiHomogeneous a g) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    eval (fun p => r p.1 * x p) g = (∏ b, r b ^ a b) * eval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [eval_monomial, eval_monomial]
  have h1 : (s.prod fun p e => (r p.1 * x p) ^ e) =
      (s.prod fun p e => r p.1 ^ e) * s.prod fun p e => x p ^ e := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext p e
    rw [mul_pow]
  have h2 : (s.prod fun p e => r p.1 ^ e) = ∏ b, r b ^ a b := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ y, r b ^ s (b, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hm s hs b]
  rw [h1, h2]
  ring

theorem linSubst_incl {B N n : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) ℂ) :
    GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
                 if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by
  unfold GlobalTheory.ChowHt.linSubst
  have hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) p.2 k) * X (p.1, k)) =
      fun p => X (p.1, Fin.castLE h p.2) := by
    funext p
    rw [Fintype.sum_eq_single (Fin.castLE h p.2)]
    · simp
    · intro k hk
      have hne : (p.2 : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext (by rw [Fin.coe_castLE]; exact he.symm))
      simp [Matrix.of_apply, hne]
  rw [hfun]
  have hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) ℂ)) =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) :=
    MvPolynomial.algHom_ext fun p => by simp
  rw [hal]

theorem isMultiHomogeneous_rename_castLE {B N n : ℕ} (h : N ≤ n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (hm : IsMultiHomogeneous a f) :
    IsMultiHomogeneous a (rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f) := by
  have he : Function.Injective (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)
  intro s hs b
  rw [support_rename_of_injective he, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← hm t ht b]
  let emb : Fin N ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hsub : (Finset.univ.map emb) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finsupp.mapDomain_apply_of_injective he t (b, j)
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    apply hj
    simp only [Prod.mk.injEq] at hq
    rw [Finset.mem_map]
    exact ⟨q.2, Finset.mem_univ _, hq.2⟩

theorem gauss_blockMean {B n : ℕ} (hn : 0 < n) (δ : ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hg : g ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) g) :
    Integrable (fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
        Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖) (Measure.pi fun _ => gaussProb n) ∧
    ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ ∂(Measure.pi fun _ => gaussProb n) =
      blockSphereMean B n g + (B : ℝ) * δ * (radK (2 * n - 1) / radJ (2 * n - 1)) := by
  obtain ⟨hρ, hlogi, hlog⟩ := _root_.GlobalTheory.SphereMeanDrop.radProb_log_mean n hn
  haveI := hρ
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (gaussProb n) := isProbabilityMeasure_gaussProb hn
  have hΦm : Measurable fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
      Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ :=
    Real.measurable_log.comp (Continuous.measurable
      (continuous_norm.comp ((continuous_eval g).comp (by fun_prop))))

  have hpol : MeasurePreserving
      (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
        fun b => ((q.2 b : ℝ)) • ((q.1 b : EuclideanSpace ℂ (Fin n))))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
      (Measure.pi fun _ : Fin B => gaussProb n) := by
    have h1 := measurePreserving_pi (fun _ : Fin B => (sphereProb n).prod (radProb n))
      (fun _ => gaussProb n) (fun _ => GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn)
    have h2 := MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (UnitSphereC n)
      (Ioi (0:ℝ)) (Fin B) (fun _ => sphereProb n) (fun _ => radProb n))
    exact h1.comp h2

  have hpt : ∀ q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)), eval (blockPoint q.1) g ≠ 0 →
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    intro q hq
    have hr : ∀ b, (0:ℝ) < q.2 b := fun b => (q.2 b).2
    have hfun : (fun p : Fin B × Fin n =>
        WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) =
        fun p => ((q.2 p.1 : ℝ) : ℂ) * blockPoint q.1 p := by
      funext p
      simp [blockPoint, spherePoint, Complex.real_smul]
    have hprod : ‖∏ b, (((q.2 b : ℝ) : ℂ)) ^ δ‖ = ∏ b, ((q.2 b : ℝ)) ^ δ := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr b)]
    have hs := eval_blockScale (fun _ => δ) g hm (fun b => ((q.2 b : ℝ) : ℂ)) (blockPoint q.1)
    rw [hfun, hs, norm_mul, hprod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hr b).ne')
        (norm_ne_zero_iff.2 hq),
      Real.log_prod (fun b _ => pow_ne_zero _ (hr b).ne')]
    simp only [Real.log_pow]
    ring
  have hnull := _root_.GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero B n _ g hn hg hm
  have hae : ∀ᵐ q ∂((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)),
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    have h0 : ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
        {q | eval (blockPoint q.1) g = 0} = 0 := by
      have hs : {q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) | eval (blockPoint q.1) g = 0} =
          {z | eval (blockPoint z) g = 0} ×ˢ univ := by
        ext q; simp
      rw [hs, Measure.prod_prod]
      have : (Measure.pi fun _ : Fin B => sphereProb n) {z | eval (blockPoint z) g = 0} = 0 := hnull
      rw [this, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq using hpt q hq

  have hA : Integrable (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖)
      (Measure.pi fun _ : Fin B => sphereProb n) :=
    ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B n _ g hg hm
  have hRi : ∀ b : Fin B, Integrable (fun r : Fin B → Ioi (0:ℝ) => Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    exact (he.integrable_comp hlogi.aestronglyMeasurable).2 hlogi
  have hRint : ∀ b : Fin B, ∫ r, Real.log ((r : Fin B → Ioi (0:ℝ)) b : ℝ)
      ∂(Measure.pi fun _ => radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    have hm' : AEStronglyMeasurable (fun r : Ioi (0:ℝ) => Real.log (r : ℝ))
        (Measure.map (Function.eval b) (Measure.pi fun _ : Fin B => radProb n)) :=
      (Real.measurable_log.comp measurable_subtype_coe).aestronglyMeasurable
    have := integral_map he.measurable.aemeasurable hm'
    rw [he.map_eq] at this
    rw [← hlog, this]
  have hAi : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      Real.log ‖eval (blockPoint q.1) g‖)
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hA.comp_fst _
  have hRsum : Integrable (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) :=
    MeasureTheory.integrable_finsetSum _ fun b _ => (hRi b).const_mul _
  have hRi' : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hRsum.comp_snd _
  have hcomp := (hAi.add hRi').congr (hae.mono fun q h => h.symm)
  refine ⟨(hpol.integrable_comp hΦm.aestronglyMeasurable).1 hcomp, ?_⟩
  rw [← hpol.map_eq, integral_map hpol.measurable.aemeasurable hΦm.aestronglyMeasurable,
    integral_congr_ae hae, integral_add hAi hRi',
    integral_fun_fst (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖),
    integral_fun_snd (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ)),
    MeasureTheory.integral_finsetSum _ fun b _ => (hRi b).const_mul _]
  simp only [probReal_univ, one_smul, integral_const_mul, hRint, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [blockSphereMean, blockSphereProb]
  ring

theorem radRatio_sub {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    radK (2 * N - 1) / radJ (2 * N - 1) - radK (2 * n - 1) / radJ (2 * n - 1) =
      ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  have e2 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  rw [e1, e2, radRatio_odd, radRatio_odd]
  simp only [Nat.add_sub_cancel]
  ring

end GlobalTheory.SphereMeanDrop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}
      = connectedComponent (e p) := by
    ext x
    have h1 : (f ⁻¹' {f x} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    have h2 : f x = p := Subsingleton.elim _ _
    rw [Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]
  rw [hZ]
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : IsOpen (connectedComponent (e p)) := _root_.GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X hN (e p)
  refine ⟨hO, ?_⟩
  let U : X.Opens := ⟨connectedComponent (e p), hO⟩
  have hc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))
  have hi : IrreducibleSpace U.toScheme :=
    _root_.GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace k U.toScheme (U.ι ≫ f) inferInstance hc
  exact isIrreducible_iff_irreducibleSpace.mpr hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhdsStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothFunIntegralMulRight
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

theorem isSmoothFun_integral_mul_right : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ ν _ K hK hν κ hκ
  haveI := secondCountableTopology_subgroup_units G
  haveI := IsExpLieAlgebra.locallyCompactSpace (G := G) (𝔤 := 𝔤) h
  obtain ⟨ψ, hψ1, -, hψc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  have hae : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]; exact hν
  have e : (fun Y : 𝔤 => ∫ y, κ (g * h.expG Y * y) ∂ν) =
      fun Y => ∫ y, ((ψ y : ℝ) : ℂ) * κ (g * h.expG Y * y) ∂ν := by
    funext Y
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp [hψ1 hy]
  rw [e]
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hκg : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (fun x : G => κ (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hκ (contMDiff_const.mul contMDiff_id)
  set Φ : 𝔤 → G → ℂ := fun Y y => κ (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => Φ q.1 (y₀ * h.expG q.2)) := by
    intro y₀
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_fst y₀ contDiff_snd
    simpa [hΦdef, mul_assoc] using this
  have hΦY : ∀ y : G, ContDiff ℝ ∞ (fun Y => Φ Y y) := by
    intro y
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_id y (contDiff_const (c := (0 : 𝔤)))
    simpa [hΦdef, mul_assoc] using this
  have hD : ∀ (k : ℕ) (Y : 𝔤) (y : G),
      iteratedFDeriv ℝ k (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) Y =
        ((ψ y : ℝ) : ℂ) • iteratedFDeriv ℝ k (fun Y => Φ Y y) Y := by
    intro k Y y
    have e : (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) = ((ψ y : ℝ) : ℂ) • fun Y => Φ Y y := by
      funext Y; simp [smul_eq_mul]
    rw [e, iteratedFDeriv_const_smul_apply ((hΦY y).contDiffAt.of_le (by exact_mod_cast le_top))]
  change ContDiff ℝ ∞ fun Y : 𝔤 => ∫ y, ((ψ y : ℝ) : ℂ) * Φ Y y ∂ν
  refine contDiff_integral_of_iteratedFDeriv (μ := ν) (fun (Y : 𝔤) (y : G) => ((ψ y : ℝ) : ℂ) * Φ Y y)
    (fun y => contDiff_const.mul (hΦY y)) (fun k => ?_) (fun Y₀ => ?_)
  · have hc := h.continuous_iteratedFDeriv_param Φ hΦ k
    refine (((Complex.continuous_ofReal.comp ψ.continuous).comp continuous_snd).smul hc).congr fun q => ?_
    exact (hD k q.1 q.2).symm
  · refine ⟨Set.univ, Filter.univ_mem, tsupport ψ, hψc, fun Y _ y hy => ?_⟩
    simp [image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisQuotientIntegralClosureStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_quotient_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → ∀ (t : A), (∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a)) → ∀ (m : ℕ) (y : Fin m → A), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) → ∀ y' : Fin m → B, (∀ j, (y' j : K) = algebraMap F K (y j)) → IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y' j)) := by
  first | (exact @GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (exact GlobalTheory.isTranscendenceBasis_quotient_integralClosure) | (intros; apply GlobalTheory.isTranscendenceBasis_quotient_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivExpGLineEqRightDerivPow
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

theorem iteratedDeriv_expG_line_eq_rightDeriv_pow :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (X : 𝔤) (g : G) (n : ℕ), ContDiff ℝ ∞ (fun t : ℝ => f (g * h.expG (t • X))) ∧ ∀ s : ℝ, iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X))) s = (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
  intro 𝔸 _ _ _ _ G 𝔤 h f hf X g n
  have hd : ∀ (f : G → ℂ), h.IsSmoothFun f → ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f (g * h.expG (s • X))) s := by
    intro f hf s
    have h1 := h.hasDerivAt_rightDeriv hf X (g * h.expG (s • X))
    have h2 : HasDerivAt (fun t : ℝ => f (g * h.expG ((s + t) • X)))
        (h.rightDeriv X f (g * h.expG (s • X))) (s - s) := by
      rw [sub_self]
      simpa only [h.expG_add_smul, mul_assoc] using h1
    have h3 := h2.comp_sub_const s s
    simpa only [add_sub_cancel] using h3
  have hi : ∀ (n : ℕ) (f : G → ℂ), h.IsSmoothFun f →
      iteratedDeriv n (fun t : ℝ => f (g * h.expG (t • X)))
        = fun s : ℝ => (List.replicate n X).foldr h.rightDeriv f (g * h.expG (s • X)) := by
    intro n
    induction n with
    | zero => intro f _; simp
    | succ n ih =>
      intro f hf
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun t : ℝ => f (g * h.expG (t • X)))
          = fun t : ℝ => h.rightDeriv X f (g * h.expG (t • X)) := by
        funext s; exact (hd f hf s).deriv
      rw [hderiv, ih _ (h.isSmoothFun_rightDeriv hf X)]
      funext s
      rw [List.replicate_succ', List.foldr_append]
      rfl
  refine ⟨?_, fun s => by rw [hi n f hf]⟩
  have hc := (h.isSmoothFun_iff).1 hf g
  exact hc.comp (contDiff_id.smul contDiff_const)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ), (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧ (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧ a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧ (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧ ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  first | (exact @GlobalTheory.PD.omB_alg) | (exact GlobalTheory.PD.omB_alg) | (intros; apply GlobalTheory.PD.omB_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraComapSpanEqTopStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  first | (exact @GlobalTheory.PD.omB_comap_span_eq_top) | (exact GlobalTheory.PD.omB_comap_span_eq_top) | (intros; apply GlobalTheory.PD.omB_comap_span_eq_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraEqRangeExteriorPowerStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_eq_range_exteriorPower : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] [Algebra.Smooth k B] (q : ℕ), ∃ e : (⋀[B]^q Ω[B⁄k]) →ₗ[B] DR k K, Function.Injective e ∧ (∀ y, y ∈ omB k K B q ↔ ∃ z, e z = y) ∧ ∀ v : Fin q → B, e (exteriorPower.ιMulti B q fun j => D k B (v j)) = ExteriorAlgebra.ιMulti K q fun j => D k K (v j : K) := by
  first | (exact @GlobalTheory.PD.omB_eq_range_exteriorPower) | (exact GlobalTheory.PD.omB_eq_range_exteriorPower) | (intros; apply GlobalTheory.PD.omB_eq_range_exteriorPower  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerBaseChangedReductionEqSpanXStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_baseChangedReduction_eq_span_X : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [CommRing A₁] (f : A →+* A₁) (i : A →+* T) (i₁ : A₁ →+* T)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y)),
    RingHom.ker ρ = Ideal.span {algebraMap A[X] (Localization.AtPrime QA) Polynomial.X} →
    RingHom.ker (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) =
      Ideal.span {algebraMap A₁[X] (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) Polynomial.X} := by
  first | (exact @GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (exact GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X) | (intros; apply GlobalTheory.KeyOriginBC.ker_reduceLoc_eq_span_X  <;> assumption)
end

