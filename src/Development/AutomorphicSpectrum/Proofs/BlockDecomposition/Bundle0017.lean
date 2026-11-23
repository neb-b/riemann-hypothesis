module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUniqueSquareRootNearOne
section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.RingSqrt

theorem exists_local_sqrt : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V),
    Continuous ψ → Continuous ψ.symm →
    ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧
      (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  intro B V _ _ _ _ _ _ ψ hψ hψs
  let L : V → (V →L[ℝ] V) := fun x =>
    AddMonoidHom.toRealLinearMap
      { toFun := fun y => ψ (ψ.symm x * ψ.symm y)
        map_zero' := by simp
        map_add' := by intro a b; simp [mul_add] }
      (hψ.comp (continuous_const.mul hψs))
  have hL : ∀ x y, L x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  let A : V →L[ℝ] (V →L[ℝ] V) := AddMonoidHom.toRealLinearMap
      { toFun := L
        map_zero' := by ext y; simp [hL]
        map_add' := by intro a b; ext y; simp [hL, add_mul] }
      (continuous_clm_apply.2 fun y => hψ.comp (hψs.mul continuous_const))
  have hA : ∀ x y, A x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  obtain ⟨Q, hQdef⟩ : ∃ Q : V → V, Q = fun y => y + y + A y y := ⟨_, rfl⟩
  have hQ : ∀ y, (1 + ψ.symm y) * (1 + ψ.symm y) = 1 + ψ.symm (Q y) := by
    intro y
    simp only [hQdef, hA, map_add (f := _), AddEquiv.symm_apply_apply, mul_add, add_mul, one_mul, mul_one]
    abel
  have hQ0 : Q 0 = 0 := by simp [hQdef]
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)
  have hder : HasStrictFDerivAt Q (e : V →L[ℝ] V) 0 := by
    have h1 : HasStrictFDerivAt (fun y : V => y) (ContinuousLinearMap.id ℝ V) 0 :=
      hasStrictFDerivAt_id 0
    have h2 := A.hasStrictFDerivAt.clm_apply h1
    have h3 := (h1.add h1).add h2
    rw [hQdef]
    refine h3.congr_fderiv ?_
    ext v
    simp [e, two_smul, Units.smul_def]
  have hsub : Filter.Tendsto (fun h : B => ψ (h - 1)) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun h : B => ψ (h - 1) := hψ.comp (continuous_id.sub continuous_const)
    simpa using hc.tendsto 1
  have hg : Filter.Tendsto (hder.localInverse Q e 0) (𝓝 0) (𝓝 0) := by
    have := hder.localInverse_tendsto
    rwa [hQ0] at this
  have hr : ∀ᶠ y in 𝓝 (0 : V), Q (hder.localInverse Q e 0 y) = y := by
    have := hder.eventually_right_inverse
    rwa [hQ0] at this
  refine ⟨fun h => 1 + ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))),
    (fun x => ψ (x - 1)) ⁻¹' (hder.toOpenPartialHomeomorph Q).source, ?_, ?_, ?_, ?_⟩
  · exact hsub ((hder.toOpenPartialHomeomorph Q).open_source.mem_nhds
      hder.mem_toOpenPartialHomeomorph_source)
  · have h0 : Filter.Tendsto (fun h : B => ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))))
        (𝓝 1) (𝓝 0) := by
      have := (hψs.tendsto 0).comp (hg.comp hsub)
      simpa [Function.comp_def] using this
    simpa using (tendsto_const_nhds (x := (1 : B))).add h0
  · filter_upwards [hsub hr] with h hh
    rw [hQ, hh]
    simp
  · intro x hx y hy hxy
    have key : Q (ψ (x - 1)) = Q (ψ (y - 1)) := by
      have e1 := hQ (ψ (x - 1))
      have e2 := hQ (ψ (y - 1))
      simp only [AddEquiv.symm_apply_apply, add_sub_cancel] at e1 e2
      exact ψ.symm.injective (add_left_cancel (e1.symm.trans (hxy.trans e2)))
    have h1 : ψ (x - 1) = ψ (y - 1) := (hder.toOpenPartialHomeomorph Q).injOn hx hy key
    exact sub_left_inj.1 (ψ.injective h1)

end GlobalTheory.CompanionTheory.RingSqrt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapInjectiveOfInjective
section
namespace GlobalTheory.CompanionTheory.PiTensor

theorem map_injective_of_injective
    (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
    (f : ∀ i, M i →ₗ[K] N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (PiTensorProduct.map f) := by
  have hg : ∀ i, ∃ g : N i →ₗ[K] M i, g ∘ₗ f i = LinearMap.id := fun i =>
    LinearMap.exists_leftInverse_of_injective (f i) (LinearMap.ker_eq_bot.2 (hf i))
  choose g hg using hg
  have hcomp : PiTensorProduct.map g ∘ₗ PiTensorProduct.map f = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg]
    exact PiTensorProduct.map_id
  refine Function.LeftInverse.injective (g := PiTensorProduct.map g) fun x => ?_
  exact LinearMap.congr_fun hcomp x

end GlobalTheory.CompanionTheory.PiTensor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterFunEqOfMapLeftMul
section
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_eq_of_map_left_mul :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (ρ : Measure Q) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [ρ.IsMulRightInvariant] (δ : Q →* ℝ≥0), (∀ q : Q, ρ.map (fun x => q * x) = (δ q)⁻¹ • ρ) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ ρ _ _ _ δ h q
  have : ρ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hδ : (δ q⁻¹)⁻¹ = δ q := by
    rw [inv_eq_iff_eq_inv]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  have hcomp : (fun x : Q => x * q) ∘ Inv.inv = Inv.inv ∘ (fun y : Q => q⁻¹ * y) := by
    funext y
    simp [mul_inv_rev]
  have hmap : Measure.map (fun x : Q => x * q) ρ.inv = δ q • ρ.inv := by
    rw [Measure.inv_def, Measure.map_map (measurable_mul_const q) measurable_inv, hcomp,
      ← Measure.map_map measurable_inv (measurable_const_mul q⁻¹), h q⁻¹, Measure.map_smul, hδ]
    exact measurable_inv.aemeasurable
  rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ.inv q]
  simp only [hmap, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.ModChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonicFactorCoefficientsIntegral
section
open Polynomial

namespace GlobalTheory.CompanionTheory.IntFac

theorem isIntegral_coeff_of_eval (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ u : ℂ, IsIntegral ℂ (F.eval (algebraMap ℂ A u))) (k : ℕ) :
    IsIntegral ℂ (F.coeff k) := by
  classical
  set N := F.natDegree + 1 with hN
  by_cases hk : k < N
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact isIntegral_zero
  let φ := algebraMap ℂ A
  let v : Fin N → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun a b hab => Fin.ext (by simpa only [v, Nat.cast_inj] using hab)
  let V := Matrix.vandermonde v
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  let c : Fin N → A := fun j => F.coeff j
  let y : Fin N → A := fun i => F.eval (φ (v i))
  have hy : Matrix.mulVec (V.map φ) c = y := by
    funext i
    simp only [y, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply, c]
    rw [eval_eq_sum_range' (Nat.lt_succ_self _),
      ← Fin.sum_univ_eq_sum_range (fun j => F.coeff j * φ (v i) ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_pow, mul_comm]
  have hc : c = Matrix.mulVec (V⁻¹.map φ) y := by
    rw [← hy, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  have hmem : Matrix.mulVec (V⁻¹.map φ) y ⟨k, hk⟩ ∈ integralClosure ℂ A := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (h _)
  have hck : F.coeff k = c ⟨k, hk⟩ := rfl
  rw [hck, hc]
  exact hmem

theorem isIntegral_eval_of_coeff (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ k, IsIntegral ℂ (F.coeff k)) (u : ℂ) : IsIntegral ℂ (F.eval (algebraMap ℂ A u)) := by
  rw [eval_eq_sum_range]
  exact IsIntegral.sum _ fun i _ => (h i).mul (isIntegral_algebraMap.pow _)

theorem isIntegral_coeff_of_monic_dvd (A : Type) [CommRing A] [Algebra ℂ A] (F G : A[X])
    (hF : F.Monic) (hG : G.Monic) (hd : G ∣ F) (h : ∀ k, IsIntegral ℂ (F.coeff k)) (k : ℕ) :
    IsIntegral ℂ (G.coeff k) := by
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
    (f := algebraMap (integralClosure ℂ A) A) (p := F)
    ((lifts_iff_coeff_lifts F).mpr fun n => ⟨⟨F.coeff n, h n⟩, rfl⟩) hF
  have hd' : G ∣ q.map (algebraMap (integralClosure ℂ A) A) := by
    rw [hq]
    exact hd
  exact isIntegral_trans _ (isIntegral_coeff_of_dvd q G hqm hG hd' k)

end GlobalTheory.CompanionTheory.IntFac

theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic →
      (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) *
        Q.eval (algebraMap ℂ A (u + c₂)))) →
      ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  intro A _ _ P Q c₁ c₂ hP hQ h k
  set P₁ := P.comp (X + C (algebraMap ℂ A c₁)) with hP₁d
  set Q₁ := Q.comp (X + C (algebraMap ℂ A c₂)) with hQ₁d
  have hP₁ : P₁.Monic := hP.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQ.comp_X_add_C _
  have hH : ∀ j, IsIntegral ℂ ((P₁ * Q₁).coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A (P₁ * Q₁)
      (fun u => by simpa [hP₁d, hQ₁d, eval_comp] using h u)
  have i₁ : ∀ j, IsIntegral ℂ (P₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hP₁ (dvd_mul_right _ _) hH
  have i₂ : ∀ j, IsIntegral ℂ (Q₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hQ₁ (dvd_mul_left _ _) hH
  refine ⟨GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A P (fun u => ?_) k,
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A Q (fun u => ?_) k⟩
  · have h₁ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A P₁ i₁ (u - c₁)
    simpa [hP₁d, eval_comp] using h₁
  · have h₂ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A Q₁ i₂ (u - c₂)
    simpa [hQ₁d, eval_comp] using h₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativeCharacterOnCone
section
namespace GlobalTheory.CompanionTheory.StrictCone

theorem exists_char_of_mul_on_cone {G : Type*} [AddCommGroup G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (f : G → ℂ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ S) (hne : f s₀ ≠ 0)
    (arch : ∀ g : G, ∃ k : ℕ, 0 < k ∧ k • s₀ + g ∈ S) :
    ∃ φ : G → ℂˣ, (∀ g h, φ (g + h) = φ g * φ h) ∧ ∀ s ∈ S, f s = (φ s : ℂ) := by
  have hmem : ∀ k : ℕ, k • s₀ + s₀ ∈ S ∧ f (k • s₀ + s₀) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨hs₀, hne⟩
    | succ n ih =>
      have h1 : (n + 1) • s₀ + s₀ = (n • s₀ + s₀) + s₀ := by rw [succ_nsmul]
      rw [h1]
      refine ⟨hS _ ih.1 _ hs₀, ?_⟩
      rw [hf _ ih.1 _ hs₀]
      exact mul_ne_zero ih.2 hne
  have hmem' : ∀ k : ℕ, 0 < k → k • s₀ ∈ S ∧ f (k • s₀) ≠ 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [succ_nsmul]
    exact hmem n
  have hnz : ∀ z ∈ S, f z ≠ 0 := by
    intro z hz h0
    obtain ⟨k, hk, hw⟩ := arch (-z)
    have h2 : k • s₀ = z + (k • s₀ + -z) := by abel
    have h3 := (hmem' k hk).2
    rw [h2, hf _ hz _ hw, h0, zero_mul] at h3
    exact h3 rfl
  have wd : ∀ c₁ ∈ S, ∀ c₂ ∈ S, ∀ d₁ ∈ S, ∀ d₂ ∈ S, c₁ - c₂ = d₁ - d₂ →
      f c₁ / f c₂ = f d₁ / f d₂ := by
    intro c₁ h₁ c₂ h₂ d₁ h₃ d₂ h₄ h
    have e : c₁ + d₂ = d₁ + c₂ := by
      have : c₁ + d₂ - (d₁ + c₂) = (c₁ - c₂) - (d₁ - d₂) := by abel
      rw [← sub_eq_zero, this, h, sub_self]
    have e' := congrArg f e
    rw [hf _ h₁ _ h₄, hf _ h₃ _ h₂] at e'
    rw [div_eq_div_iff (hnz _ h₂) (hnz _ h₄)]
    exact e'
  choose k hk hd using arch
  have hc : ∀ g, k g • s₀ ∈ S := fun g => (hmem' _ (hk g)).1
  let φ : G → ℂˣ := fun g =>
    Units.mk0 (f (k g • s₀ + g) / f (k g • s₀)) (div_ne_zero (hnz _ (hd g)) (hnz _ (hc g)))
  refine ⟨φ, ?_, ?_⟩
  · intro g h
    apply Units.ext
    simp only [φ, Units.val_mul, Units.val_mk0]
    have := wd _ (hd (g + h)) _ (hc (g + h)) _ (hS _ (hd g) _ (hd h)) _ (hS _ (hc g) _ (hc h))
      (by abel)
    rw [this, hf _ (hd g) _ (hd h), hf _ (hc g) _ (hc h), mul_div_mul_comm]
  · intro s hs
    simp only [φ, Units.val_mk0]
    rw [hf _ (hc s) _ hs, mul_div_cancel_left₀ _ (hnz _ (hc s))]

theorem char_eq_prod {n : ℕ} (φ : (Fin n → ℤ) → ℂˣ) (h : ∀ g g', φ (g + g') = φ g * φ g') (x : Fin n → ℤ) :
    φ x = ∏ i, φ (Pi.single i 1) ^ x i := by
  let F : (Fin n → ℤ) →+ Additive ℂˣ :=
    AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
  have h3 := congrArg Additive.toMul h2
  simpa [F, toMul_sum] using h3

theorem zpow_sum_units (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem char_split {n : ℕ} (c : Fin n → ℤ) (Q : ℂˣ) (φ : (Fin n → ℤ) → ℂˣ)
    (h : ∀ g g', φ (g + g') = φ g * φ g') :
    ∃ ξ : Fin n → ℂˣ, ∀ x, φ x = Q ^ (∑ i, c i * x i) * ∏ i, ξ i ^ x i := by
  refine ⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩
  rw [char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]
  simp

def IsStrict {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

theorem IsStrict.add {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by
  intro i j hij
  have := hx i j hij
  have := hy i j hij
  simp only [Pi.add_apply]
  omega

theorem IsStrict.arch {n : ℕ} {s : Fin n → ℤ} (hs : IsStrict s) (g : Fin n → ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → IsStrict (k • s + g) := by
  refine ⟨1 + ∑ i, ∑ j, (g i - g j).natAbs, fun k hk i j hij => ?_⟩
  have h1 : (g j - g i).natAbs ≤ ∑ i, ∑ j, (g i - g j).natAbs :=
    (Finset.single_le_sum (f := fun j' => (g j' - g i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (by
        rw [Finset.sum_comm]
        exact Finset.single_le_sum (f := fun i' => ∑ j', (g j' - g i').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 : s j + 1 ≤ s i := hs i j hij
  have h3 : (k : ℤ) * (s j + 1) ≤ (k : ℤ) * s i :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (g j - g i) ≤ ((g j - g i).natAbs : ℤ) := by omega
  generalize (∑ i, ∑ j, (g i - g j).natAbs) = T at hk h1
  have h5 : (1 : ℤ) + T ≤ k := by exact_mod_cast hk
  have h6 : ((g j - g i).natAbs : ℤ) ≤ T := by exact_mod_cast h1
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  nlinarith

theorem mul_on_cone_eq_delta_char : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  intro a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩
  let S : Set ((Fin a → ℤ) × (Fin b → ℤ)) := {z | IsStrict z.1 ∧ IsStrict z.2}
  obtain ⟨φ, hφ, hfφ⟩ := exists_char_of_mul_on_cone S
    (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2)
    (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne
    (fun g => by
      obtain ⟨K₁, h₁⟩ := IsStrict.arch (s := x₀) hx₀ g.1
      obtain ⟨K₂, h₂⟩ := IsStrict.arch (s := y₀) hy₀ g.2
      refine ⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩
      · exact h₁ _ (by omega)
      · exact h₂ _ (by omega))
  let Q : ℂˣ := Units.mk0 q hq
  obtain ⟨ξa, ha⟩ := char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)
  obtain ⟨ξb, hb⟩ := char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)
  refine ⟨ξa, ξb, fun x y hx hy => ?_⟩
  have h1 : χ x y = (φ (x, y) : ℂ) := hfφ (x, y) ⟨hx, hy⟩
  have h2 : φ (x, y) = φ (x, 0) * φ (0, y) := by rw [← hφ]; simp
  rw [h1, h2, ha x, hb y]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]

end GlobalTheory.CompanionTheory.StrictCone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumeration
section
namespace GlobalTheory.CompanionTheory.Multiset

theorem exists_antitone_listing {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  classical
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let r : α → α → Prop := fun a b => f b ≤ f a
  haveI : DecidableRel r := fun _ _ => Classical.dec _
  haveI : Std.Total r := ⟨fun a b => le_total (f b) (f a)⟩
  haveI : IsTrans α r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  let l' := l.insertionSort r
  have hperm : l'.Perm l := List.perm_insertionSort r l
  have hsort : l'.Pairwise r := List.pairwise_insertionSort r l
  have hlt : ∀ i j : Fin l'.length, i < j → f (l'.get j) ≤ f (l'.get i) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hsort) i j hij
  refine ⟨l'.length, l'.get, ?_, ?_, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin l'.length)).val.map l'.get = ((List.ofFn l'.get : List α) : Multiset α) := by
      rw [Fin.univ_val_map]
    rw [h1, List.ofFn_get]
    exact Quot.sound hperm
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hlt i j h
    · subst h; exact le_rfl
  · intro i j hij hp
    exact absurd (hP _ _ hp) (not_lt.mpr (hlt i j hij))

end GlobalTheory.CompanionTheory.Multiset
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonZeroDivisorOfDenseOfStrict
section
namespace GlobalTheory.CompanionTheory.ComplReg

theorem nonZeroDivisor_of_dense_of_strict {B T : Type} [CommRing B] [CommRing T] (π : B)
    (g : B →+* T) (hH : IsHausdorff (Ideal.span {g π}) T)
    (hd : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M})
    (hk : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M})
    (hπ : π ∈ nonZeroDivisors B) : g π ∈ nonZeroDivisors T := by
  have key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M} := by
    intro t ht M
    obtain ⟨x, hx⟩ := hd M t
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨d, hd'⟩ := hx
    have hxπ : x * π ∈ Ideal.span {π ^ (M + 1)} := by
      apply hk (M + 1) (x * π)
      rw [Ideal.mem_span_singleton]
      exact ⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩
    rw [Ideal.mem_span_singleton] at hxπ
    obtain ⟨c, hc⟩ := hxπ
    have h0 : (x - π ^ M * c) * π = 0 := by
      rw [sub_mul, hc]
      ring
    have hxeq : x = π ^ M * c := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)
    have hgx : g x = g π ^ M * g c := by
      rw [hxeq, map_mul, map_pow]
    rw [Ideal.mem_span_singleton]
    exact ⟨d + g c, by linear_combination hd' + hgx⟩
  have main : ∀ t : T, t * g π = 0 → t = 0 := by
    intro t ht
    refine IsHausdorff.haus hH t (fun n => ?_)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact key t ht n
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩

end GlobalTheory.CompanionTheory.ComplReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe
section
namespace GlobalTheory.CompanionTheory.FinReversal

theorem prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl

end GlobalTheory.CompanionTheory.FinReversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZero
section
open Matrix

namespace GlobalTheory.CompanionTheory.RelIndex

theorem relIndex_ne_zero_of_isCompact_of_isOpen :
    ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  intro X _ _ _ A H hA hH _
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.RelIndex
end

