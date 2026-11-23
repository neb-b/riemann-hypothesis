module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.Bundle0003
public import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import GroundTheory.GlobalFields.IdeleGroups.Restricted
public import GroundTheory.GlobalFields.TateThesis.LocalConductor

@[expose] public section

-- bundled from GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
section
namespace GroundTheory.Global

open _root_.Complex

theorem re_eq_zero_of_norm_exp_one_cpow {s : ℂ}
    (h : ‖((Real.exp 1 : ℝ) : ℂ) ^ s‖ = 1) : s.re = 0 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos 1), Real.exp_one_rpow] at h
  exact Real.exp_eq_one_iff _ |>.mp h

theorem existsUnique_mul_I_of_re_eq_zero {P : ℂ → Prop} (h : ∃! s, P s)
    (hre : ∀ s, P s → s.re = 0) : ∃! τ : ℝ, P ((τ : ℂ) * I) := by
  obtain ⟨s, hs, hu⟩ := h
  have hs' : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre s hs]
  refine ⟨s.im, by show P ((s.im : ℂ) * I); rw [← hs']; exact hs, fun τ hτ => ?_⟩
  have := congrArg Complex.im (hu _ hτ)
  simpa using this

theorem existsUnique_prod_mul_I_of_re_eq_zero {α : Type*} {P : α × ℂ → Prop}
    (h : ∃! p, P p) (hre : ∀ p, P p → p.2.re = 0) :
    ∃! q : α × ℝ, P (q.1, (q.2 : ℂ) * I) := by
  obtain ⟨p, hp, hu⟩ := h
  have hp' : p = (p.1, (p.2.im : ℂ) * I) := by
    refine Prod.ext rfl ?_
    apply Complex.ext <;> simp [hre p hp]
  refine ⟨(p.1, p.2.im), by show P (p.1, (p.2.im : ℂ) * I); rw [← hp']; exact hp,
    fun q hq => ?_⟩
  have := hu _ hq
  refine Prod.ext ?_ ?_
  · simpa using congrArg Prod.fst this
  · simpa using congrArg (fun r : α × ℂ => r.2.im) this

theorem existsUnique_cpow_of_pos_circle (χ : {x : ℝ // 0 < x} →ₜ* Circle) :
    ∃! τ : ℝ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ ((τ : ℂ) * I) := by
  apply existsUnique_mul_I_of_re_eq_zero (existsUnique_cpow_of_pos (circleToUnits.comp χ))
  intro s hs
  apply re_eq_zero_of_norm_exp_one_cpow
  have h : (χ ⟨Real.exp 1, Real.exp_pos 1⟩ : ℂ) = ((Real.exp 1 : ℝ) : ℂ) ^ s :=
    hs ⟨Real.exp 1, Real.exp_pos 1⟩
  rw [← h, Circle.norm_coe]

theorem existsUnique_realUnits_circle (χ : ℝˣ →ₜ* Circle) :
    ∃! p : Fin 2 × ℝ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2)
    (existsUnique_realUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have h := hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')
  simp only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1),
    Complex.ofReal_one, one_pow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_complexUnits_circle (χ : ℂˣ →ₜ* Circle) :
    ∃! p : ℤ × ℝ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2)
    (existsUnique_complexUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  have h := hp (Units.mk0 _ hne)
  rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
    div_self hne, one_zpow, one_mul] at h
  rw [← h, Circle.norm_coe]

theorem existsUnique_addChar_real_units (χ : AddChar ℝ ℂˣ) (hχ : Continuous χ) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) :=
  existsUnique_exp_of_continuous χ hχ χ.map_add_eq_mul

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.Conductor
section
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
theorem coe_finiteComponent (v : HeightOneSpectrum (𝓞 K)) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finiteComponent v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem continuous_finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteComponent (K := K) v) :=
  Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)

def finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleSingle v)

theorem continuous_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteUnitsSingle (K := K) v) :=
  Units.continuous_map (continuous_finiteAdeleSingle v)

@[simp]
theorem finiteComponent_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finiteComponent v (finiteUnitsSingle v x) = x := by
  ext
  simp [finiteUnitsSingle]

theorem finiteComponent_finiteUnitsSingle_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteComponent w (finiteUnitsSingle v x) = 1 := by
  ext
  simp [finiteUnitsSingle, finiteAdeleSingle_apply_of_ne h]

def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)

theorem mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by
  simp only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)

theorem finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 :=
  finiteLevel_antitone fun v ↦ Nat.zero_le (n v)

theorem finiteUnitsSingle_mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ}
    {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} (hx : x ∈ unitsLevel v (n v)) :
    finiteUnitsSingle v x ∈ finiteLevel n := by
  refine mem_finiteLevel.2 fun w ↦ ?_
  by_cases h : w = v
  · subst h
    simpa using hx
  · rw [finiteComponent_finiteUnitsSingle_of_ne h]
    exact one_mem _

theorem finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x :=
  Units.ext rfl

theorem isOpen_finiteLevel_zero :
    IsOpen (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have h := (_root_.RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ))
    (fun v ↦ isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsEquiv K).continuous
  convert h using 1
  ext x
  simp only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage,
    Set.mem_ofPred_eq]
  exact forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl

theorem isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have : (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) =
      (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹'
        (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩,
      fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩
    by_cases hv : n v = 0
    · rw [hv]
      exact mem_finiteLevel.1 h0 v
    · exact h v (by simpa using hv)
  rw [this]
  exact isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦
    (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))

theorem exists_finiteLevel_subset {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

theorem exists_finiteLevel_le_ker (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker := by
  obtain ⟨L, ⟨S, n, h1, h0, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ L = finiteLevel n)
    (fun W hW ↦ by
      obtain ⟨S, n, h1, h0, h⟩ := exists_finiteLevel_subset hW
      exact ⟨_, ⟨S, n, h1, h0, rfl⟩, h⟩) hH χ hχ
  exact ⟨S, n, h1, h0, hL⟩

theorem exists_finiteLevel_le_ker_circle (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle)
    (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker :=
  exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ

def conductorExponentAt (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  conductorExponent v (χ.comp (finiteUnitsSingle v))

theorem finiteLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ χ.ker ↔ ∀ v, conductorExponentAt χ v ≤ n v := by
  have hloc : ∀ v, Continuous (χ.comp (finiteUnitsSingle v)) := fun v ↦
    hχ.comp (continuous_finiteUnitsSingle v)
  constructor
  · intro h v
    rw [conductorExponentAt, ← unitsLevel_le_ker_iff v hH _ (hloc v)]
    intro x hx
    exact h (finiteUnitsSingle_mem_finiteLevel hx)
  · intro h x hx
    classical
    obtain ⟨S, n₀, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
    set p := ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v x) with hp
    have hcomp : ∀ w, finiteComponent w p = if w ∈ S then finiteComponent w x else 1 := by
      intro w
      rw [hp, map_prod]
      split_ifs with hw
      · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (Ne.symm hv) _,
          finiteComponent_finiteUnitsSingle]
      · exact Finset.prod_eq_one fun v hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (fun h ↦ hw (by rw [h]; exact hv)) _
    have hy : x * p⁻¹ ∈ finiteLevel n₀ := by
      refine mem_finiteLevel.2 fun w ↦ ?_
      rw [map_mul, map_inv, hcomp]
      split_ifs with hw
      · rw [mul_inv_cancel]
        exact one_mem _
      · rw [inv_one, mul_one, h0 w hw]
        exact unitsLevel_antitone w (Nat.zero_le _) (mem_finiteLevel.1 hx w)
    have hpk : p ∈ χ.ker := Subgroup.prod_mem _ fun v _ ↦
      (unitsLevel_le_ker_iff v hH _ (hloc v)).2 (h v) (mem_finiteLevel.1 hx v)
    have hxp : x = x * p⁻¹ * p := by rw [inv_mul_cancel_right]
    rw [hxp]
    exact mul_mem (hker hy) hpk

theorem finite_support_conductorExponentAt (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    (support (conductorExponentAt χ)).Finite := by
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
  have h := (finiteLevel_le_ker_iff hH χ hχ n).1 hker
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  exact hv (Nat.eq_zero_of_le_zero ((h v).trans (h0 v hvS).le))

theorem conductorExponentAt_eq_zero_iff (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt χ v = 0 ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker :=
  conductorExponent_eq_zero_iff v hH _ (hχ.comp (continuous_finiteUnitsSingle v))

end Character

end IdeleGroup

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.TateThesis.GaussianComplexFourier
section
namespace GroundTheory.Global

open _root_.Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform

noncomputable section

theorem complexFourier_mul_self {f : ℂ → ℂ} (hf : Integrable f complexPlaceMeasure)
    (hf' : Integrable (fun z ↦ ‖z‖ * ‖f z‖) complexPlaceMeasure) {w : ℂ} {D : ℂ →L[ℝ] ℂ}
    (hD : HasFDerivAt (complexFourier f) D w) :
    -4 * π * I * complexFourier (fun z ↦ z * f z) w = D 1 - I * D I := by
  have h := VectorFourier.hasFDerivAt_fourierIntegral traceFormℂ hf hf' w
  rw [← complexFourier_eq_fourierIntegral] at h
  rw [hD.unique h]
  have hint : Integrable (fun z ↦ VectorFourier.fourierSMulRight traceFormℂ f z)
      complexPlaceMeasure := by
    refine ((hf'.const_mul (2 * π * ‖traceFormℂ‖))).mono' hf.1.fourierSMulRight ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have := VectorFourier.norm_fourierSMulRight_le traceFormℂ f z
    simpa [mul_assoc] using this
  rw [fourierIntegral_continuousLinearMap_apply' hint,
    fourierIntegral_continuousLinearMap_apply' hint]
  have hL : ∀ v : ℂ, traceFormℂ.toLinearMap₁₂ v w = 2 * (v * w).re :=
    fun v ↦ traceFormℂ_apply v w
  simp only [VectorFourier.fourierIntegral, VectorFourier.fourierSMulRight_apply, hL,
    traceFormℂ_apply]
  have i1 : ∀ h : ℂ, Integrable (fun z ↦ 𝐞 (-(2 * (z * w).re)) •
      (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
    intro h
    have : Integrable (fun z ↦ (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
      have := (hint.apply_continuousLinearMap h)
      simpa [VectorFourier.fourierSMulRight_apply] using this
    have := (fourierIntegral_convergent_iff' (μ := complexPlaceMeasure) traceFormℂ w).2 this
    simpa using this
  rw [← integral_const_mul, ← integral_sub (i1 1) ((i1 I).const_mul I), complexFourier,
    ← integral_const_mul]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_I_re]
  push_cast
  have hz : (z : ℂ) = z.re + z.im * I := (re_add_im z).symm
  linear_combination (norm := skip) (-4 * π * I * (𝐞 (-(2 * (z * w).re)) : ℂ) * f z) * hz
  ring_nf

theorem cexp_neg_two_pi_norm_sq (w : ℂ) :
    Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2) = Complex.exp (-2 * π * (w * conj w)) := by
  congr 2
  rw [mul_conj, normSq_eq_norm_sq]
  push_cast
  ring

theorem exists_hasFDerivAt_conj_pow_mul_gaussian (n : ℕ) (w : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦ conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) D w ∧
      D 1 - I * D I = -4 * π * (conj w ^ (n + 1) * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  simp only [cexp_neg_two_pi_norm_sq]
  have hc : HasFDerivAt (fun w : ℂ ↦ conj w) (conjCLE : ℂ →L[ℝ] ℂ) w :=
    (conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
  have hid : HasFDerivAt (fun w : ℂ ↦ w) (ContinuousLinearMap.id ℝ ℂ) w := hasFDerivAt_id w
  have hq := (hid.fun_mul hc).const_mul (-2 * π : ℂ)
  have hexp := hq.cexp
  have hp := hc.pow n
  refine ⟨_, hp.fun_mul hexp, ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_id', id, ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one,
    conj_I, smul_eq_mul, nsmul_eq_mul]
  rw [pow_succ]
  linear_combination (conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * (-2 * π) * (-w) +
    Complex.exp (-2 * π * (w * conj w)) * (n * conj w ^ (n - 1)) +
    2 * conj w * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π -
    4 * conj w ^ n * Complex.exp (-2 * π * (w * conj w)) * π * w) * I_sq

theorem complexGaussian_natCast (n : ℕ) :
    complexGaussian n = fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  simp [complexGaussian]

theorem complexGaussian_neg_natCast (n : ℕ) :
    complexGaussian (-(n : ℤ)) = fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  funext z
  rw [complexGaussian]
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp
  · simp

theorem complexFourier_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  induction n with
  | zero =>
    have h := complexFourier_complexGaussian_zero
    simp only [funext complexGaussian_zero] at h
    simpa using h
  | succ n ih =>
    funext w
    obtain ⟨D, hD, hD1⟩ := exists_hasFDerivAt_conj_pow_mul_gaussian n w
    have hF : HasFDerivAt (complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)))
        ((-I) ^ n • D) w := by
      rw [ih]; exact hD.const_mul _
    have hf : Integrable (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))
        complexPlaceMeasure := by
      simpa [complexGaussian_natCast] using integrable_complexGaussian n
    have hf' : Integrable (fun z ↦ ‖z‖ * ‖z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)‖)
        complexPlaceMeasure := by
      have := (integrable_norm_pow_smul_complexGaussian' n 1).norm
      refine this.congr (Filter.Eventually.of_forall fun z ↦ ?_)
      simp [complexGaussian_natCast]
    have key := complexFourier_mul_self hf hf' hF
    have e : (fun z : ℂ ↦ z * (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) =
        fun z ↦ z ^ (n + 1) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
      funext z; ring
    rw [e] at key
    have hne : (-4 * π * I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [this, I_ne_zero]
    apply mul_left_cancel₀ hne
    rw [key]
    simp only [smul_apply, smul_eq_mul]
    have hD1' : (-I) ^ n * D 1 - I * ((-I) ^ n * D I) = (-I) ^ n * (D 1 - I * D I) := by ring
    rw [hD1', hD1]
    rw [pow_succ]
    linear_combination (-4 * π * (-I) ^ n * (conj w ^ (n + 1) *
      Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2))) * I_sq

theorem complexFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    complexFourier (fun z ↦ conj (f z)) w = conj (complexFourier f (-w)) := by
  rw [complexFourier, complexFourier, ← integral_conj]
  congr 1
  funext z
  simp [Circle.smul_def, Real.fourierChar_apply, ← exp_conj, map_ofNat, neg_re, neg_im,
    mul_re, ofReal_sub, ofReal_mul]
  congr 2 <;> try ring <;> simp

theorem conj_cexp_neg_two_pi_norm_sq (z : ℂ) :
    conj (Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
  rw [← exp_conj]
  simp [map_mul, conj_ofReal, map_ofNat]

theorem complexFourier_conj_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  funext w
  have e : (fun z : ℂ ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun z ↦ conj (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) := by
    funext z
    rw [map_mul, map_pow, conj_cexp_neg_two_pi_norm_sq]
  rw [e, complexFourier_conj, complexFourier_pow_mul_gaussian]
  simp only [map_mul, map_pow, map_neg, conj_I, conj_conj, conj_cexp_neg_two_pi_norm_sq,
    norm_neg]
  ring

theorem complexFourier_complexGaussian (m : ℤ) :
    complexFourier (complexGaussian m) = fun w ↦ (-I) ^ m.natAbs * complexGaussian (-m) w := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [complexGaussian_natCast, complexFourier_pow_mul_gaussian, complexGaussian_neg_natCast]
    simp
  · rw [complexGaussian_neg_natCast, complexFourier_conj_pow_mul_gaussian, neg_neg,
      complexGaussian_natCast]
    simp

end

end GroundTheory.Global
end

