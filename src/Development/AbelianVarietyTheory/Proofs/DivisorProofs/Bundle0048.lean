module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAndMean
section
namespace GlobalTheory.EmbeddingMean

theorem card_fibre {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] [DecidableEq (A →ₐ[K] C)]
    (f : A →ₐ[K] C) :
    (Finset.univ.filter (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B) = f)).card
      = Module.finrank A B := by
  letI : Algebra A C := f.toRingHom.toAlgebra
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [← AlgHom.card A B C, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun g => { g.1.toRingHom with
        commutes' := fun a => by
          have := DFunLike.congr_fun g.2 a
          exact this }
      invFun := fun h => ⟨h.restrictScalars K, AlgHom.ext fun a => h.commutes a⟩
      left_inv := fun g => Subtype.ext (AlgHom.ext fun _ => rfl)
      right_inv := fun h => AlgHom.ext fun _ => rfl }

theorem tower {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] :
    (∀ f : A →ₐ[K] C, ∃ g : B →ₐ[K] C, g.comp (IsScalarTower.toAlgHom K A B) = f) ∧
    ∀ F : (A →ₐ[K] C) → ℝ,
      (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B))) / (Module.finrank K B : ℝ)
        = (∑ f : A →ₐ[K] C, F f) / (Module.finrank K A : ℝ) := by
  classical
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  have hpos : 0 < Module.finrank A B := Module.finrank_pos
  refine ⟨fun f => ?_, fun F => ?_⟩
  · have h := card_fibre (B := B) f
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (h ▸ hpos)
    exact ⟨g, (Finset.mem_filter.mp hg).2⟩
  · have hsum : (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B)))
        = (Module.finrank A B : ℝ) * ∑ f : A →ₐ[K] C, F f := by
      rw [← Finset.sum_fiberwise Finset.univ
        (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => F f)
        (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
        Finset.sum_const, nsmul_eq_mul]
      congr 2
      convert card_fibre (B := B) f
    have hA : (Module.finrank K A : ℝ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := K) (M := A)).ne'
    have hB : (Module.finrank A B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hsum, ← Module.finrank_mul_finrank K A B]
    push_cast
    field_simp

end GlobalTheory.EmbeddingMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendLinearIndependentDifferentials
section
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem kaehler_baseChange_independent_extend :
    ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K]
      [Algebra.FiniteType R B] (d : ℕ) (ι : Type) (x : ι → B),
      Module.finrank K (K ⊗[B] Ω[B⁄R]) = d →
      LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (x i)) →
      ∃ (t : Fin d → B) (e : ι ↪ Fin d), (∀ i, t (e i) = x i) ∧
        LinearIndependent K (fun a => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B (t a)) := by
  intro R B K _ _ _ _ _ _ d ι x hd hx
  set g : B → K ⊗[B] Ω[B⁄R] := fun b => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B b with hg
  have hspan : Submodule.span K (Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul k ω =>
      have h1 : (1 : K) ⊗ₜ[B] ω ∈ Submodule.span K (Set.range g) := by
        have hω : ω ∈ Submodule.span B (Set.range (KaehlerDifferential.D R B)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hω using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨b, rfl⟩ := hy
          exact Submodule.subset_span ⟨b, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
        | smul c y _ hy =>
          rw [TensorProduct.tmul_smul, ← algebraMap_smul K c]
          exact Submodule.smul_mem _ _ hy
      have : k ⊗ₜ[B] ω = k • ((1 : K) ⊗ₜ[B] ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    | add a b ha hb => exact add_mem ha hb
  have hxinj : Function.Injective x := fun i j h => hx.injective (by simp [h])
  have hs : LinearIndepOn K g (Set.range x) := (linearIndepOn_range_iff hxinj g).2 hx
  obtain ⟨b, -, hsb, htb, hli⟩ := exists_linearIndepOn_extension hs (Set.subset_univ _)
  have hspanb : ⊤ ≤ Submodule.span K (Set.range (fun y : b => g y)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have := htb ⟨c, Set.mem_univ _, rfl⟩
    rwa [Set.image_eq_range] at this
  let bas := Module.Basis.mk hli hspanb
  haveI : Finite b := Module.Finite.finite_basis bas
  have hcard : Nat.card b = d := by
    rw [← hd, Module.finrank_eq_nat_card_basis bas]
  let eq : b ≃ Fin d := Finite.equivFinOfCardEq hcard
  refine ⟨fun a => (eq.symm a).1, ⟨fun i => eq ⟨x i, hsb ⟨i, rfl⟩⟩, ?_⟩, ?_, ?_⟩
  · intro i j h
    have := eq.injective h
    exact hxinj (congrArg Subtype.val this)
  · intro i
    show ((eq.symm (eq ⟨x i, hsb ⟨i, rfl⟩⟩)) : B) = x i
    rw [Equiv.symm_apply_apply]
  · exact hli.comp eq.symm eq.symm.injective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivIntegralMulKernelApply
section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace GlobalTheory

theorem fderiv_integral_mul_kernel_apply :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
      [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U →
      ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U →
      ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V,
      fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v =
        ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  intro V _ _ _ _ _ ν _ U hU α hα hαc hαU K hK x hx v
  have hUU : IsOpen (U ×ˢ U) := hU.prod hU
  have hα0 : ∀ y, y ∉ U → α y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hαU h))

  have hKd : ∀ p ∈ U ×ˢ U, HasFDerivAt K (fderiv ℝ K p) p := fun p hp =>
    ((hK.differentiableOn (by simp)) p hp).differentiableAt
      (hUU.mem_nhds hp) |>.hasFDerivAt
  have hKp : ∀ x' ∈ U, ∀ y ∈ U,
      HasFDerivAt (fun x'' => K (x'', y)) ((fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)) x' :=
    fun x' hx' y hy => (hKd (x', y) ⟨hx', hy⟩).comp x' (hasFDerivAt_prodMk_left x' y)
  have hcf : ContinuousOn (fderiv ℝ K) (U ×ˢ U) :=
    hK.continuousOn_fderiv_of_isOpen hUU (by exact_mod_cast le_top)
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp hU x hx
  set r := ε / 2 with hr
  have rpos : 0 < r := half_pos εpos
  have hcb : closedBall x r ⊆ U := (closedBall_subset_ball (half_lt_self εpos)).trans hε
  have hcomp : IsCompact (closedBall x r ×ˢ tsupport α) :=
    (isCompact_closedBall x r).prod hαc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (hcf.mono (Set.prod_mono hcb hαU))
  set F' : V → V → V →L[ℝ] ℂ :=
    fun x' y => α y • (fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V) with hF'
  have hcontF : ∀ x' ∈ U, Continuous (fun y => α y * K (x', y)) := by
    intro x' hx'
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_mul_subset_left).trans hαU)
    refine hα.continuousOn.mul ?_
    exact hK.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      (fun y hy => ⟨hx', hy⟩)
  have hcontF' : Continuous (F' x) := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((tsupport_smul_subset_left _ _).trans hαU)
    refine hα.continuousOn.smul ?_
    have h1 : ContinuousOn (fun y => fderiv ℝ K (x, y)) U :=
      hcf.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => ⟨hx, hy⟩)
    exact h1.clm_comp continuousOn_const
  have hbound : ∀ y, ∀ x' ∈ ball x r, ‖F' x' y‖ ≤ ‖α y‖ * C := by
    intro y x' hx'
    by_cases hy : y ∈ tsupport α
    · rw [hF', norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖(fderiv ℝ K (x', y)).comp (ContinuousLinearMap.inl ℝ V V)‖
          ≤ ‖fderiv ℝ K (x', y)‖ * ‖ContinuousLinearMap.inl ℝ V V‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖fderiv ℝ K (x', y)‖ * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℝ V V) (norm_nonneg _)
        _ ≤ C := by rw [mul_one]; exact hC _ ⟨ball_subset_closedBall hx', hy⟩
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hF', this]
  have hαi : Integrable α ν := hα.integrable_of_hasCompactSupport hαc
  have hF'i : Integrable (F' x) ν :=
    Integrable.mono' (hαi.norm.mul_const C) hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y x (mem_ball_self rpos))
  have hmain : HasFDerivAt (fun x' => ∫ y, α y * K (x', y) ∂ν) (∫ y, F' x y ∂ν) x := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball x r) (bound := fun y => ‖α y‖ * C)
      (ball_mem_nhds x rpos) ?_ ?_ hcontF'.aestronglyMeasurable
      (Eventually.of_forall fun y => hbound y) (hαi.norm.mul_const C) ?_
    · filter_upwards [hU.mem_nhds hx] with x' hx'
      exact (hcontF x' hx').aestronglyMeasurable
    · exact (hcontF x hx).integrable_of_hasCompactSupport (hαc.mul_right)
    · refine Eventually.of_forall fun y x' hx' => ?_
      by_cases hy : y ∈ U
      · exact (hKp x' (hcb (ball_subset_closedBall hx')) y hy).const_mul (α y)
      · have : α y = 0 := hα0 y hy
        simp only [hF', this, zero_mul, zero_smul]
        exact hasFDerivAt_const _ _
  rw [hmain.fderiv, ContinuousLinearMap.integral_apply hF'i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ U
  · simp only [hF', ContinuousLinearMap.smul_apply, smul_eq_mul, (hKp x hx y hy).fderiv]
  · simp [hF', hα0 y hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
section
open NumberField

namespace GlobalTheory

theorem fg_int_of_forall_isIntegral (K' : Type) [Field K'] [NumberField K']
    (M : Submodule ℤ K') (hM : ∀ y ∈ M, IsIntegral ℤ y) : M.FG := by
  let f : 𝓞 K' →ₗ[ℤ] K' := (algebraMap (𝓞 K') K').toIntAlgHom.toLinearMap
  have hle : M ≤ LinearMap.range f := fun y hy => ⟨⟨y, hM y hy⟩, rfl⟩
  have hfg : (M.comap f).FG := IsNoetherian.noetherian _
  have hmap := hfg.map f
  rwa [Submodule.map_comap_eq, inf_eq_right.mpr hle] at hmap

theorem fg_of_integral_functionals (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by
  apply Submodule.FG.of_restrictScalars ℤ
  suffices H : ∀ W : Submodule K C, (L.restrictScalars ℤ ⊓ W.restrictScalars ℤ).FG by
    simpa using H ⊤
  intro W
  induction W using WellFoundedLT.induction with
  | _ W ih =>
    by_cases hW : W = ⊥
    · subst hW
      have hbot : L.restrictScalars ℤ ⊓ (⊥ : Submodule K C).restrictScalars ℤ = ⊥ := by
        ext y
        simp
      rw [hbot]
      exact Submodule.fg_bot
    · obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨K', _, _, _, φ, hφx, hφL⟩ := h x hx0
      let f : C →ₗ[ℤ] K' := φ.toAddMonoidHom.toIntLinearMap
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left fun heq => hφx ?_
        have hx : x ∈ W ⊓ LinearMap.ker φ := by rw [heq]; exact hxW
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
      apply Submodule.fg_of_fg_map_of_fg_inf_ker f
      · apply fg_int_of_forall_isIntegral K'
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact hφL y (Submodule.mem_inf.mp hy).1
      · have heq : L.restrictScalars ℤ ⊓ W.restrictScalars ℤ ⊓ LinearMap.ker f
            = L.restrictScalars ℤ ⊓ (W ⊓ LinearMap.ker φ).restrictScalars ℤ := by
          ext y
          simp [f, and_assoc]
          exact fun _ _ => Iff.rfl
        rw [heq]
        exact ih _ hlt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinset
section
namespace GlobalTheory

open Submodule

theorem fg_localizationAway_span_finset
    {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R)
    [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A']
    (N : Submodule R' A') (hN : N.FG) :
    ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N →
      ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  classical
  obtain ⟨S, rfl⟩ := hN
  have hA : ∀ (c : R) (z : A),
      algebraMap A A' (c • z) = algebraMap R A' c * algebraMap A A' z := by
    intro c z
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hsurj : ∀ n : A', ∃ e : A, ∃ k : ℕ,
      n * algebraMap R A' g ^ k = algebraMap A A' e := by
    intro n
    obtain ⟨k, e, h⟩ := IsLocalization.Away.surj (algebraMap R A g) n
    exact ⟨e, k, by rw [IsScalarTower.algebraMap_apply R A A']; exact h⟩
  choose e k he using hsurj
  refine ⟨S.image e, ?_⟩
  have key : ∀ y ∈ Submodule.span R' (S : Set A'), ∃ m : ℕ,
      ∃ z ∈ Submodule.span R ((S.image e : Finset A) : Set A),
        algebraMap A A' z = algebraMap R A' g ^ m * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine ⟨k x, e x, Submodule.subset_span ?_, ?_⟩
      · simp only [Finset.coe_image]
        exact Set.mem_image_of_mem e hx
      · rw [← he, mul_comm]
    | zero => exact ⟨0, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m1, z1, hz1, h1⟩ := hx
      obtain ⟨m2, z2, hz2, h2⟩ := hy
      refine ⟨m1 + m2, g ^ m2 • z1 + g ^ m1 • z2,
        add_mem (smul_mem _ _ hz1) (smul_mem _ _ hz2), ?_⟩
      rw [map_add (f := _), hA, hA, h1, h2, map_pow, map_pow]
      ring
    | smul r' x _ hx =>
      obtain ⟨m, z, hz, h⟩ := hx
      obtain ⟨l, r, hr⟩ := IsLocalization.Away.surj g r'
      refine ⟨m + l, r • z, smul_mem _ _ hz, ?_⟩
      have hr' : algebraMap R A' r = algebraMap R' A' r' * algebraMap R A' g ^ l := by
        rw [IsScalarTower.algebraMap_apply R R' A', ← hr, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply]
      rw [hA, h, Algebra.smul_def, hr']
      ring
  intro b hb
  obtain ⟨m, z, hz, h⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ m * b) = 0 := by
    rw [map_sub, h, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, sub_self]
  obtain ⟨⟨x, hx⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  obtain ⟨c, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hx
  refine ⟨c + m, ?_⟩
  have hc' : algebraMap R A g ^ c * (z - algebraMap R A g ^ m * b) = 0 := hc
  have : algebraMap R A g ^ (c + m) * b = g ^ c • z := by
    rw [Algebra.smul_def, map_pow]
    linear_combination -hc'
  rw [this]
  exact smul_mem _ _ hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimes
section
open AlgebraicGeometry CategoryTheory Limits Topology

namespace GlobalTheory

theorem fibre_dense_affine_chart_primes : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  intro X T p W U V hU hV e hW b hb q
  set f := hU.fromSpec with hf
  have hemb : IsOpenEmbedding f := f.isOpenEmbedding

  have hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U := fun P => hU.range_fromSpec.le ⟨P, rfl⟩
  have hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P := fun P =>
    hemb.injective (hU.fromSpec_primeIdealOf _)
  have hcomap : ∀ P : PrimeSpectrum Γ(X, U),
      PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩ := by
    intro P
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)
    rw [hprime P] at this
    exact this
  set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA
  have hq : q ∈ closure (f ⁻¹' A) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hW (f q)
  refine closure_mono ?_ hq
  intro P hP
  obtain ⟨hPW, hPp⟩ := hP
  refine ⟨?_, ?_⟩
  · let _ : Algebra Γ(X, U) (X.presheaf.stalk (f P)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩
    haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)
    have h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0 := hb (f P) (hmemU P) hPW
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0
    exact ⟨s, hs, hsb⟩
  · show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q
    rw [hcomap P, hcomap q]
    have : p (f P) = p (f q) := hPp
    congr 2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldCase
section
namespace GlobalTheory.FieldCaseReduction

open Polynomial

theorem field_case (F : Type) [Field F] [Finite F] (t m f : F) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ a b : F, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  classical
  by_cases h2 : ringChar F = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two h2 f
    exact ⟨a, 0, by rw [ha]; ring⟩
  · haveI := Fintype.ofFinite F
    have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hp : (X ^ 2 : F[X]).degree = 2 := by simp
    have hq : (C (-(t ^ 2 - 4 * m)) * X ^ 2 + C 0 * X + C (-(4 * f)) : F[X]).degree = 2 :=
      degree_quadratic (neg_ne_zero.mpr hD)
    obtain ⟨x, b, hxb⟩ := FiniteField.exists_root_sum_quadratic hp hq hodd
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hxb
    refine ⟨(x - t * b) / 2, b, ?_⟩
    field_simp
    linear_combination hxb

theorem main (S : Type) [inst : CommRing S] [Finite S] [IsReduced S] (t m f : S)
    (hD : IsUnit (t ^ (2 : ℕ) - (4 : S) * m)) (_hf : IsUnit f) :
    ∃ (a : S) (b : S), a ^ (2 : ℕ) + t * a * b + m * b ^ (2 : ℕ) = f := by
  classical
  haveI : IsArtinianRing S := isArtinian_of_finite
  let e := (IsArtinianRing.equivPi S).toRingEquiv
  have key : ∀ I : MaximalSpectrum S, ∃ a b : S ⧸ I.asIdeal,
      a ^ 2 + e t I * a * b + e m I * b ^ 2 = e f I := by
    intro I
    haveI := I.isMaximal
    letI : Field (S ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (S ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    apply field_case
    have h := (hD.map ((Pi.evalRingHom (fun J : MaximalSpectrum S => S ⧸ J.asIdeal) I).comp
      e.toRingHom)).ne_zero
    simp only [map_sub, map_mul, map_pow, map_ofNat] at h
    exact h
  choose a b hab using key
  refine ⟨e.symm a, e.symm b, e.injective ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, RingEquiv.apply_symm_apply]
  funext I
  exact hab I

end GlobalTheory.FieldCaseReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystems
section
open Matrix

namespace GlobalTheory

theorem finite_joint_eigensystems : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  intro K _ n ι A hc
  let f : ι → Module.End K (Fin n → K) := fun i => Matrix.toLin' (A i)
  have hcf : ∀ i j, Commute (f i) (f j) := by
    intro i j
    exact (hc i j).map Matrix.toLinAlgEquiv'
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcf j i) φ)
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨c, hc0, hχ⟩
  show (⨅ i, (f i).maxGenEigenspace (χ i)) ≠ ⊥
  intro hbot
  apply hc0
  have hmem : c ∈ ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [Submodule.mem_iInf]
    intro i
    apply Module.End.eigenspace_le_maxGenEigenspace
    rw [Module.End.mem_eigenspace_iff]
    simpa [f] using hχ i
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end GlobalTheory
end

