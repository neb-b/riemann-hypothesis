module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentSeriesAdaptedBasisCoordsVanishBeyondFinra
section
open PowerSeries

namespace GlobalTheory

theorem inv_mulVec_coord_eq_zero_of_adapted_columns_injective {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (n : ℕ) (W : Submodule K (Fin n → K))
    (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank K W →
      (fun a => φ ((g : Matrix (Fin n) (Fin n) R) a j)) ∈ W)
    (y : Fin n → R) (hy : (fun a => φ (y a)) ∈ W)
    (a : Fin n) (ha : Module.finrank K W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a = 0 := by
  classical
  have hr : Module.finrank K W ≤ n := by
    have := Submodule.finrank_le W
    simpa using this
  set r := Module.finrank K W with hrdef
  let G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) R).map φ
  let H : Matrix (Fin n) (Fin n) K := ((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).map φ
  have hHG : H * G = 1 := by
    calc H * G = (RingHom.mapMatrix φ) (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R)) :=
          ((RingHom.mapMatrix φ).map_mul _ _).symm
      _ = 1 := by rw [Units.inv_mul, map_one]
  let e : Fin r → (Fin n → K) := fun i => Pi.single (Fin.castLE hr i) 1
  let v : Fin r → (Fin n → K) := fun i => fun b => G b (Fin.castLE hr i)
  have hHv : ∀ i, H.mulVec (v i) = e i := by
    intro i
    have : v i = G.mulVec (Pi.single (Fin.castLE hr i) 1) := by
      ext b; simp [v, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  have hcomp : (Matrix.toLin' H) ∘ v = e := by
    funext i; simp only [Function.comp_apply, Matrix.toLin'_apply, hHv]
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Matrix.toLin' H)
    rw [hcomp]
    exact (Pi.linearIndependent_single_one (Fin n) K).comp _ (Fin.castLE_injective hr)
  have hle : Submodule.span K (Set.range v) ≤ W := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact hg (Fin.castLE hr i) (by simp)
  have heq : Submodule.span K (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hy' : (fun b => φ (y b)) ∈ Submodule.span K (Set.range v) := heq ▸ hy
  have hmap : H.mulVec (fun b => φ (y b)) ∈ Submodule.span K (Set.range e) := by
    have := Submodule.mem_map_of_mem (f := Matrix.toLin' H) hy'
    rw [Submodule.map_span, ← Set.range_comp, hcomp, Matrix.toLin'_apply] at this
    exact this
  have hker : Submodule.span K (Set.range e) ≤ LinearMap.ker (LinearMap.proj a) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, e]
    apply Pi.single_eq_of_ne
    intro h
    have : ((Fin.castLE hr i : Fin n) : ℕ) = a := by rw [h]
    simp at this
    omega
  have h0 : (H.mulVec (fun b => φ (y b))) a = 0 := hker hmap
  have hcoe : φ ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a) =
      (H.mulVec (fun b => φ (y b))) a := by
    rw [RingHom.map_mulVec]
    rfl
  rw [h0] at hcoe
  exact (injective_iff_map_eq_zero φ).mp hφ _ hcoe

theorem adapted_coords_vanish (F : Type) [Field F] (n : ℕ)
    (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W)
    (y : Fin n → PowerSeries F) (hy : (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W)
    (a : Fin n) (ha : Module.finrank (LaurentSeries F) W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha

theorem adapted_coords_vanish_stmt : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  fun F _ n W g hg y hy a ha => adapted_coords_vanish F n W g hg y hy a ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeAddMulLogSqOfLeAddMulLog
section
open Filter Topology

namespace GlobalTheory

theorem le_add_mul_log_sq_of_le_add_mul_log :
    ∀ (α β r s : ℝ), 0 ≤ α → 0 ≤ β → 1 ≤ r → r ≤ s → s ≤ α + β * Real.log r →
      s ≤ α + β * Real.log ((α + 2 * β + 1) ^ 2) := by
  intro α β r s hα hβ hr hrs hs
  have hr0 : 0 < r := by linarith
  set t := Real.sqrt r with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg r
  have htt : t * t = r := Real.mul_self_sqrt hr0.le
  have ht1 : 1 ≤ t := by
    by_contra h
    push_neg at h
    nlinarith
  have htpos : 0 < t := by linarith
  have hlog : Real.log r ≤ 2 * t - 2 := by
    have h1 : Real.log r = 2 * Real.log t := by
      rw [← htt, Real.log_mul htpos.ne' htpos.ne']; ring
    have h2 := Real.log_le_sub_one_of_pos htpos
    linarith
  have hle : t ≤ α + 2 * β + 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_left h htpos, mul_nonneg hα (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_left hlog hβ]
  have hrc : r ≤ (α + 2 * β + 1) ^ 2 := by
    rw [← htt]; nlinarith
  have hl : Real.log r ≤ Real.log ((α + 2 * β + 1) ^ 2) := Real.log_le_log hr0 hrc
  nlinarith [mul_le_mul_of_nonneg_left hl hβ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMulSetIntegralImage2OfForallLe
section
open MeasureTheory

namespace GlobalTheory

theorem le_mul_setIntegral_image2_of_forall_le (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ)
    (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ)
    (hΘ : Continuous Θ) (hQ : IsCompact Q) (hB : IsCompact B) (hB1 : B ∈ nhds (1 : G))
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) →
      (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) →
      a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  have hBfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hQfin : (volume : Measure (Fin N → ℝ)) Q ≠ ⊤ := hQ.measure_lt_top.ne
  have hBpos : 0 < μ.real B :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds μ hB1).ne' hBfin
  refine ⟨K * (volume : Measure (Fin N → ℝ)).real Q / μ.real B, by positivity, ?_⟩
  intro F a hF hF0 ha
  set Ω : Set G := Set.image2 (fun t b => Θ t * b) Q B with hΩdef
  have hΩ : IsCompact Ω := by
    rw [hΩdef, ← Set.image_prod]
    exact (hQ.prod hB).image (by fun_prop)
  have hFΩ : IntegrableOn F Ω μ := hF.continuousOn.integrableOn_compact hΩ
  have hstep : ∀ t ∈ Q, ∫ x in B, F (Θ t * x) ∂μ ≤ ∫ x in Ω, F x ∂μ := by
    intro t ht
    rw [← (measurePreserving_mul_left μ (Θ t)).setIntegral_image_emb
      (measurableEmbedding_mulLeft (Θ t)) F B]
    refine setIntegral_mono_set hFΩ (Filter.Eventually.of_forall hF0) ?_
    refine Filter.Eventually.of_forall ?_
    rintro _ ⟨b, hb, rfl⟩
    exact Set.mem_image2_of_mem ht hb
  have hint : Integrable (Function.uncurry fun (x : G) (t : Fin N → ℝ) => F (Θ t * x))
      ((μ.restrict B).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact (hB.prod hQ) ?_
    exact (by fun_prop : Continuous fun p : G × (Fin N → ℝ) => F (Θ p.2 * p.1)).continuousOn
  have h1 : μ.real B * a ≤ ∫ x in B, K * ∫ t in Q, F (Θ t * x) ∂volume ∂μ := by
    have hc : μ.real B * a = ∫ _x in B, a ∂μ := by simp
    rw [hc]
    refine setIntegral_mono_on (integrableOn_const hBfin) ?_ hB.measurableSet ha
    exact hint.integral_prod_left.const_mul K
  have h2 : ∫ x in B, ∫ t in Q, F (Θ t * x) ∂volume ∂μ ≤
      (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ := by
    rw [integral_integral_swap hint]
    have hc : (volume : Measure (Fin N → ℝ)).real Q * ∫ x in Ω, F x ∂μ =
        ∫ _t in Q, (∫ x in Ω, F x ∂μ) := by simp
    rw [hc]
    exact setIntegral_mono_on hint.integral_prod_right (integrableOn_const hQfin)
      hQ.measurableSet hstep
  rw [integral_const_mul] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hBpos, mul_comm a, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeNatCastOfAddOneLe
section
namespace GlobalTheory.NatCastUpperBound

theorem le_natCast_of_add_one_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (1 : WithBot ℕ∞) ≤ (↑(n + (1 : ℕ)) : WithBot ℕ∞)) :
    a ≤ (↑n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, top_le_iff] at h
      exact ENat.coe_ne_top _ h
    | coe m =>
      have h1 : ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h3 : ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, ENat.coe_le_coe] at h
      rw [h3, WithBot.coe_le_coe, ENat.coe_le_coe]
      omega

end GlobalTheory.NatCastUpperBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSupKerMulOfLeSupMaximalMulSection
section
open scoped TensorProduct

namespace GlobalTheory

theorem nakayama_at_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  intro O P _ _ _ _ η J S hJ h
  set S' : Ideal P := S ⊔ RingHom.ker η * J with hS'
  set n : Ideal P := (IsLocalRing.maximalIdeal O).comap η with hn
  have hK : (Submodule.map S'.mkQ J).FG := Submodule.FG.map _ hJ
  have hle : Submodule.map S'.mkQ J ≤ n • Submodule.map S'.mkQ J := by
    rw [← Submodule.map_smul'']
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h hj)
    refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have : t - (s + t) = -s := by ring
    rw [this]
    exact S'.neg_mem (Ideal.mem_sup_left hs)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n _ hK hle
  intro j hj
  have h1 : r * j ∈ S' := by
    have := hr _ (Submodule.mem_map_of_mem hj)
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    simpa using this
  have hu : IsUnit (η r) := by
    by_contra hne
    have a : η r ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hne
    have b : η r - 1 ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.mem_comap.mp hr1
      simpa [map_sub] using this
    have c : (1:O) ∈ IsLocalRing.maximalIdeal O := by
      have := sub_mem a b
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr c)
  obtain ⟨u, hu'⟩ := hu
  have hk : r - algebraMap O P (η r) ∈ RingHom.ker η := by
    rw [RingHom.mem_ker]
    simp
  have h2 : (r - algebraMap O P (η r)) * j ∈ S' := Ideal.mem_sup_right (Ideal.mul_mem_mul hk hj)
  have h3 : algebraMap O P (η r) * j ∈ S' := by
    have e : algebraMap O P (η r) * j = r * j - (r - algebraMap O P (η r)) * j := by ring
    rw [e]
    exact S'.sub_mem h1 h2
  have h4 : algebraMap O P (↑u⁻¹) * (algebraMap O P (η r) * j) ∈ S' := S'.mul_mem_left _ h3
  rwa [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul] at h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthEqKerAddRange
section
namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]

lemma length_eq_ker_add_range {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (φ : M →ₗ[A] P) :
    Module.length A M =
      Module.length A (LinearMap.ker φ) + Module.length A (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))

lemma length_mid {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (h : Function.Exact f g) :
    Module.length A N₂ =
      Module.length A (LinearMap.range f) + Module.length A (LinearMap.range g) := by
  rw [length_eq_ker_add_range g, LinearMap.exact_iff.mp h]

lemma length_of_injective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (f : N₁ →ₗ[A] N₂) (hf : Function.Injective f) :
    Module.length A N₁ = Module.length A (LinearMap.range f) :=
  (LinearEquiv.ofInjective f hf).length_eq

lemma length_of_surjective {N₁ N₂ : Type} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (g : N₁ →ₗ[A] N₂) (hg : Function.Surjective g) :
    Module.length A (LinearMap.range g) = Module.length A N₂ := by
  rw [LinearMap.range_eq_top.mpr hg, Module.length_top]

variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

def kerMap (f : M₁ →ₗ[A] M₂) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₁ b) →ₗ[A] LinearMap.ker (LinearMap.lsmul A M₂ b) :=
  f.restrict (fun x hx => by
    simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
    rw [← map_smul, hx, map_zero])

def quotMap (f : M₁ →ₗ[A] M₂) (b : A) :
    (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) →ₗ[A]
      (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) :=
  Submodule.mapQ _ _ f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simp⟩)

end ScalarSnakeLength

end GlobalTheory

namespace GlobalTheory

namespace ScalarSnakeLength

variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]

lemma kerMap_injective (f : M₁ →ₗ[A] M₂) (hf : Function.Injective f) (b : A) :
    Function.Injective (kerMap f b) := fun x y hxy =>
  Subtype.ext (hf (congrArg Subtype.val hxy))

lemma exact_kerMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (kerMap f b) (kerMap g b) := by
  intro x
  constructor
  · intro hx
    have hx' : g x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hfg _).1 hx'
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show b • y = 0
    apply hf
    rw [map_smul, hy, map_zero]
    exact x.2
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((hfg _).2 ⟨y.1, rfl⟩)

lemma exact_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (b : A) : Function.Exact (quotMap f b) (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  constructor
  · intro hx
    have hx' : (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g x) = 0 := hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨w, hw⟩ := hx'
    obtain ⟨z, rfl⟩ := hg w
    have hw' : b • g z = g x := hw
    have h0 : g (x - b • z) = 0 := by rw [map_sub, map_smul, hw', sub_self]
    obtain ⟨y, hy⟩ := (hfg _).1 h0
    refine ⟨(LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ y, ?_⟩
    show (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (f y) = _
    rw [hy, map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [← hy]
    show (LinearMap.range (LinearMap.lsmul A M₃ b)).mkQ (g (f y)) = 0
    rw [(hfg _).2 ⟨y, rfl⟩, map_zero]

lemma quotMap_surjective (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g) (b : A) :
    Function.Surjective (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := hg x
  exact ⟨(LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ y, rfl⟩

noncomputable def delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    LinearMap.ker (LinearMap.lsmul A M₃ b) →ₗ[A] (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) :=
  SnakeLemma.δ' (LinearMap.lsmul A M₁ b) (LinearMap.lsmul A M₂ b) (LinearMap.lsmul A M₃ b)
    f g hfg f g hfg (by ext x; simp) (by ext x; simp)
    (LinearMap.ker (LinearMap.lsmul A M₃ b)).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A M₁ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf

lemma exact_kerMap_delta (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (kerMap g b) (delta f g hf hg hfg b) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.ker (LinearMap.lsmul A M₂ b)).subtype (LinearMap.exact_subtype_ker_map _)
    _ _ _ _ _ _ (kerMap g b) (by ext x; rfl) Subtype.val_injective

lemma exact_delta_quotMap (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) (b : A) :
    Function.Exact (delta f g hf hg hfg b) (quotMap f b) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ (LinearMap.exact_map_mkQ_range _)
    _ _ (quotMap f b) (by ext x; rfl) (Submodule.mkQ_surjective _)

end ScalarSnakeLength

theorem scalar_snake_length :
    ∀ (A : Type) [CommRing A] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [AddCommGroup M₂]
      [AddCommGroup M₃] [Module A M₁] [Module A M₂] [Module A M₃] (f : M₁ →ₗ[A] M₂)
      (g : M₂ →ₗ[A] M₃), Function.Injective f → Function.Surjective g → Function.Exact f g →
      ∀ b : A,
        Module.length A (M₂ ⧸ LinearMap.range (LinearMap.lsmul A M₂ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) =
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) +
            Module.length A (M₁ ⧸ LinearMap.range (LinearMap.lsmul A M₁ b)) +
            Module.length A (M₃ ⧸ LinearMap.range (LinearMap.lsmul A M₃ b)) ∧
        Module.length A (LinearMap.ker (LinearMap.lsmul A M₂ b)) ≤
          Module.length A (LinearMap.ker (LinearMap.lsmul A M₁ b)) +
            Module.length A (LinearMap.ker (LinearMap.lsmul A M₃ b)) := by
  intro A _ M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg b
  open ScalarSnakeLength in
  have e1 := length_of_injective (kerMap f b) (kerMap_injective f hf b)
  have e2 := length_mid (kerMap f b) (kerMap g b) (exact_kerMap f g hf hfg b)
  have e3 := length_mid (kerMap g b) (delta f g hf hg hfg b) (exact_kerMap_delta f g hf hg hfg b)
  have e4 := length_mid (delta f g hf hg hfg b) (quotMap f b)
    (exact_delta_quotMap f g hf hg hfg b)
  have e5 := length_mid (quotMap f b) (quotMap g b) (exact_quotMap f g hg hfg b)
  have e6 := length_of_surjective (quotMap g b) (quotMap_surjective g hg b)
  rw [e1, e2, e3, e4, e5, ← e6]
  constructor
  · ac_rfl
  · exact add_le_add le_rfl le_self_add

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndepIntBilinFormCharZeroCombinationEqZero
section
namespace GlobalTheory

theorem linIndep_intBilinForm_charZero_comb_eq_zero
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by
  intro hli hsum

  let L : LinearMap.BilinForm ℤ X →ₗ[ℤ] (X → X → ℚ) :=
    { toFun := fun B y z => ((B y z : ℤ) : ℚ)
      map_add' := by intro B C; funext y z; simp
      map_smul' := by intro n B; funext y z; simp }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro B hB
    ext y z
    have := congrFun (congrFun hB y) z
    simpa [L] using this
  have hZ : LinearIndependent ℤ (L ∘ gam) := hli.map' L hker
  have hQ : LinearIndependent ℚ (L ∘ gam) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
  funext j
  by_contra hj
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℚ (V := k) hj
  have hrel : ∑ i, ℓ (a i) • (L ∘ gam) i = 0 := by
    funext y z
    have h0 := congrArg ℓ (hsum y z)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply, smul_eq_mul, L,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (a i), ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have := (Fintype.linearIndependent_iff.mp hQ) _ hrel j
  exact hℓ this

end GlobalTheory
end

