module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
section
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_of_norm_eq (R : H →L[ℂ] H) (hR : ∀ v, ‖R v‖ = ‖v‖) (v w : H) :
    ⟪R v, R w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have h := (LinearMap.norm_map_iff_inner_map_map R).mp hR
  exact h v w

private lemma exists_isometry_extension_of_dense_of_norm_eq {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (V : Submodule ℂ K) (hV : Dense (V : Set K)) (u : V →ₗ[ℂ] K) (hu : ∀ v, ‖u v‖ = ‖v‖) :
    ∃ U : K →L[ℂ] K, (∀ v : V, U v = u v) ∧ ∀ γ, ‖U γ‖ = ‖γ‖ := by
  let uc : V →L[ℂ] K := u.mkContinuous 1 (fun v => by rw [hu, one_mul])
  have hd : DenseRange V.subtypeL := by
    have hr : Set.range (V.subtypeL : V → K) = (V : Set K) := by
      ext x
      simp
    rw [DenseRange, hr]
    exact hV
  have hi : IsUniformInducing V.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  have heq : ∀ v : V, uc.extend V.subtypeL v = u v := fun v => by
    have := ContinuousLinearMap.extend_eq uc hd hi v
    simpa [uc] using this
  refine ⟨uc.extend V.subtypeL, heq, fun γ => ?_⟩
  have hfun := hd.equalizer (g := fun γ => ‖uc.extend V.subtypeL γ‖) (h := fun γ => ‖γ‖)
    (continuous_norm.comp (ContinuousLinearMap.continuous _)) continuous_norm
    (funext fun v => by
      simp only [Function.comp_apply]
      rw [ContinuousLinearMap.extend_eq uc hd hi v]
      simp [uc, hu])
  exact congr_fun hfun γ

lemma abstract {ι K : Type} [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H) (hn : ∀ i v, ‖ρ i v‖ = ‖v‖)
    (hinv : ∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hD : ∀ i, ∀ v ∈ D, ρ i v ∈ D) (J : K →L[ℂ] H) (hJ : Function.Injective J) (s : D → K)
    (hs : DenseRange s) (hJs : ∀ w, J (s w) = w)
    (hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖) :
    ∃ c : ℝ, ∀ γ : K, ‖J γ‖ ^ 2 = c * ‖γ‖ ^ 2 := by
  classical
  have hadd : ∀ a b : D, s (a + b) = s a + s b := fun a b =>
    hJ (by rw [map_add (f := _), hJs, hJs, hJs, Submodule.coe_add])
  have hsmul : ∀ (c : ℂ) (a : D), s (c • a) = c • s a := fun c a =>
    hJ (by rw [map_smul, hJs, hJs, Submodule.coe_smul])
  let sl : D →ₗ[ℂ] K := { toFun := s, map_add' := hadd, map_smul' := hsmul }
  have hinj : Function.Injective sl := fun a b hab => by
    apply Subtype.ext
    rw [← hJs a, ← hJs b]
    exact congrArg J hab
  let e := LinearEquiv.ofInjective sl hinj
  have he : ∀ w : D, e.symm ⟨s w, LinearMap.mem_range_self sl w⟩ = w := fun w => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [e, sl]
  have hVd : Dense ((LinearMap.range sl : Submodule ℂ K) : Set K) := by
    rw [LinearMap.coe_range]
    exact hs
  have hU : ∀ i, ∃ U : K →L[ℂ] K, (∀ w : D, U (s w) = s ⟨ρ i w, hD i w w.2⟩) ∧
      ∀ γ, ‖U γ‖ = ‖γ‖ := by
    intro i
    let r : D →ₗ[ℂ] D := (ρ i).toLinearMap.restrict (fun x hx => hD i x hx)
    let u : LinearMap.range sl →ₗ[ℂ] K := sl ∘ₗ r ∘ₗ e.symm.toLinearMap
    have hu : ∀ w : D, u ⟨s w, LinearMap.mem_range_self sl w⟩ = s ⟨ρ i w, hD i w w.2⟩ :=
      fun w => by
        simp only [u, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
        rfl
    obtain ⟨U, hUeq, hUn⟩ := exists_isometry_extension_of_dense_of_norm_eq _ hVd u (fun v => by
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp v.2
      have hv : v = ⟨s w, LinearMap.mem_range_self sl w⟩ := Subtype.ext hw.symm
      rw [hv, hu, hsn]
      rfl)
    refine ⟨U, fun w => ?_, hUn⟩
    have := hUeq ⟨s w, LinearMap.mem_range_self sl w⟩
    rw [hu] at this
    exact this
  choose U hUs hUn using hU
  have hUinv : ∀ i j, (∀ v, ρ i (ρ j v) = v) → ∀ γ, U i (U j γ) = γ := by
    intro i j hij γ
    have := hs.equalizer (g := fun γ => U i (U j γ)) (h := id)
      ((U i).continuous.comp (U j).continuous) continuous_id (funext fun w => by
        simp only [Function.comp_apply, id]
        rw [hUs j w, hUs i]
        congr 1
        exact Subtype.ext (hij w))
    exact congr_fun this γ
  have hJU : ∀ i γ, J (U i γ) = ρ i (J γ) := by
    intro i γ
    have := hs.equalizer (g := fun γ => J (U i γ)) (h := fun γ => ρ i (J γ))
      (J.continuous.comp (U i).continuous) ((ρ i).continuous.comp J.continuous)
      (funext fun w => by
        simp only [Function.comp_apply]
        rw [hUs i w, hJs, hJs])
    exact congr_fun this γ
  have hadj : ∀ i x, ContinuousLinearMap.adjoint J (ρ i x) = U i (ContinuousLinearMap.adjoint J x) := by
    intro i x
    obtain ⟨j, _, hij⟩ := hinv i
    apply ext_inner_right ℂ
    intro γ
    rw [ContinuousLinearMap.adjoint_inner_left]
    conv_rhs => rw [← hUinv i j hij γ]
    rw [inner_of_norm_eq (U i) (hUn i) (ContinuousLinearMap.adjoint J x) (U j γ),
      ContinuousLinearMap.adjoint_inner_left, hJU j,
      ← inner_of_norm_eq (ρ i) (hn i) x (ρ j (J γ)), hij]
  have hadjρ : ∀ i, ∃ i', ρ i' = ContinuousLinearMap.adjoint (ρ i) := by
    intro i
    obtain ⟨j, _, hij⟩ := hinv i
    refine ⟨j, ?_⟩
    ext v
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_of_norm_eq (ρ i) (hn i) (ρ j v) w, hij]
  let T : H →L[ℂ] H := J ∘L ContinuousLinearMap.adjoint J
  have hcomm : ∀ i, T ∘L ρ i = ρ i ∘L T := by
    intro i
    ext x
    simp only [T, ContinuousLinearMap.comp_apply]
    rw [hadj, hJU]
  obtain ⟨c, hc⟩ := hilbert_schur_of_adjoint_closed ι H ρ hadjρ hirr T hcomm
  have hJJ : ∀ γ, ContinuousLinearMap.adjoint J (J γ) = c • γ := by
    intro γ
    apply hJ
    have := congrArg (fun T' : H →L[ℂ] H => T' (J γ)) hc
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at this
    rw [this, map_smul]
  refine ⟨c.re, fun γ => ?_⟩
  have h1 : (⟪γ, γ⟫_ℂ).re = ‖γ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) γ
  have h2 : (⟪γ, γ⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) γ
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (J γ), ← ContinuousLinearMap.adjoint_inner_left J γ (J γ), hJJ,
    inner_smul_left, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im, h1, h2]
  ring

theorem norm_sq_eq : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℝ, ∀ w ∈ D, ‖A w‖ ^ 2 = c * ‖w‖ ^ 2 := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A hA hcl
  classical
  let g : D →ₗ[ℂ] WithLp 2 (H × E) :=
    (WithLp.linearEquiv 2 ℂ (H × E)).symm.toLinearMap ∘ₗ (D.subtype.prod (A ∘ₗ D.subtype))
  have hg : ∀ w : D, g w = WithLp.toLp 2 ((w : H), A w) := fun w => rfl
  let G : Submodule ℂ (WithLp 2 (H × E)) := LinearMap.range g
  let K : Submodule ℂ (WithLp 2 (H × E)) := G.topologicalClosure
  have : CompleteSpace K := G.isClosed_topologicalClosure.completeSpace_coe
  let J : K →L[ℂ] H := (WithLp.fstL 2 ℂ H E) ∘L K.subtypeL
  have hJapp : ∀ γ : K, J γ = (γ : WithLp 2 (H × E)).fst := fun γ => rfl
  let s : D → K := fun w => ⟨g w, G.le_topologicalClosure (LinearMap.mem_range_self g w)⟩
  have hJs : ∀ w, J (s w) = w := fun w => rfl
  have hns : ∀ x : D, ‖s x‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖A x‖ ^ 2 := fun x =>
    WithLp.prod_norm_sq_eq_of_L2 (g x)
  have hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖ := by
    intro i w
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hns, hns]
    show ‖ρ i w‖ ^ 2 + ‖A (ρ i w)‖ ^ 2 = _
    rw [hn, hA i w w.2]
  have hs : DenseRange s := by
    rw [Metric.denseRange_iff]
    intro γ ε hε
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hmem ε hε
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨w, hd⟩
  have hJ : Function.Injective J := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro γ hγ
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨x, hxG, hx⟩ := mem_closure_iff_seq_limit.mp hmem
    choose w hw using fun n => LinearMap.mem_range.mp (hxG n)
    have h1 : Tendsto (fun n => ((w n : D) : H)) atTop (𝓝 0) := by
      have := ((WithLp.fstL 2 ℂ H E).continuous.tendsto _).comp hx
      have h0 : (WithLp.fstL 2 ℂ H E) (γ : WithLp 2 (H × E)) = 0 := hγ
      rw [h0] at this
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h2 : Tendsto (fun n => A ((w n : D) : H)) atTop (𝓝 (γ : WithLp 2 (H × E)).snd) := by
      have := ((WithLp.sndL 2 ℂ H E).continuous.tendsto _).comp hx
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h3 := hcl (fun n => ((w n : D) : H)) _ (fun n => (w n).2) h1 h2
    have h4 : (γ : WithLp 2 (H × E)).fst = 0 := hγ
    apply Subtype.ext
    have h5 : ‖(γ : WithLp 2 (H × E))‖ ^ 2 = 0 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, h3, h4]
      simp
    simpa using h5
  obtain ⟨c, hc⟩ := abstract (H := H) ρ D hn hinv hirr hD J hJ s hs hJs hsn
  refine ⟨(1 - c) / c, fun w hw => ?_⟩
  have h : ‖w‖ ^ 2 = c * (‖w‖ ^ 2 + ‖A w‖ ^ 2) := by
    have := hc (s ⟨w, hw⟩)
    rw [hJs, hns] at this
    exact this
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul] at h
    have hw0 : w = 0 := by simpa using h
    subst hw0
    simp
  · rw [div_mul_eq_mul_div, eq_div_iff hc0]
    linear_combination (-1 : ℝ) * h

end GlobalTheory.ClosableSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameGenPowers
open scoped Pointwise

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

theorem finite_roots (K : Type) [Field K] (m : ℕ) (hm : m ≠ 0) :
    {u : Kˣ | u ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  have : Finite (rootsOfUnity m K) := inferInstance
  have h := Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)
  exact h.subset fun u hu => (mem_rootsOfUnity m u).2 hu

theorem eq_one_of_wild_prime (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (K : Type) [Field K] [TopologicalSpace K] [T2Space K]
    (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ) (hr : Continuous r) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : r σ ^ l = 1) : r σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite := (finite_roots K l hl.ne_zero).diff
  have hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hr
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : r σ ^ n = 1 := by
    have h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1}) := hsub hτ
    by_contra hne
    apply h2
    refine ⟨?_, by rwa [map_pow]⟩
    show r (σ ^ n) ^ l = 1
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem mem_zpowers_of_tameGen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (γ : Formalism.ConjugateSelfDual.G E Ω), TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ m : ℕ, ((m : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) → ∀ σ ∈ Ine (F := E) A, r σ ∈ Subgroup.zpowers (r γ) := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hm
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith
  have hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite := by
    refine (finite_roots K m hm0).subset ?_
    rintro u ⟨z, rfl⟩
    show (r γ ^ z) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]
  have hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
      Set (Formalism.ConjugateSelfDual.G E Ω)) := hfin.isClosed.preimage hr
  refine closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)
  rintro τ (rfl | hτ)
  · exact Subgroup.mem_zpowers _
  · show r τ ∈ Subgroup.zpowers (r γ)
    rw [hw τ hτ]
    exact one_mem _

end GlobalTheory.TameGenPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDet
section
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

namespace GlobalTheory

theorem reduction_blockTri_detDD : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  intro L _ _ _ s φ n r h g hφ hg
  have key : ∀ a b, (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = 0 ↔
      Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
    intro a b
    obtain ⟨hab, e⟩ := hg a b
    rw [e, hφ]
  refine ⟨?_, ?_⟩
  · rw [mem_blockTri]
    constructor
    · intro H a b ha hb
      rw [← key]
      apply H
      simp [blk2, hb, Nat.not_lt.mpr ha]
    · intro H i j hij
      rw [key]
      unfold blk2 at hij
      by_cases hj : j.val < r
      · by_cases hi : i.val < r
        · simp [hj, hi] at hij
        · exact H i j (Nat.not_lt.mp hi) hj
      · by_cases hi : i.val < r <;> simp [hj, hi] at hij
  · intro hT
    let M : Matrix {x : Fin n // r ≤ x.val} {x : Fin n // r ≤ x.val} (s.v.adicCompletionIntegers (maximalRealSubfield L)) :=
      fun a b => ⟨(h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a.1 b.1, (hg a.1 b.1).1⟩
    have hdet : NG.detDD s r h = (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype M.det := by
      rw [RingHom.map_det]
      rfl
    refine ⟨hdet ▸ (M.det).2, ?_⟩
    have e1 : (⟨NG.detDD s r h, hdet ▸ (M.det).2⟩ : s.v.adicCompletionIntegers (maximalRealSubfield L)) = M.det :=
      Subtype.ext hdet
    rw [e1, RingHom.map_det, diag_block_det_val 1 hT]
    let e : {a : Fin n // blk2 r a = 1} ≃ {x : Fin n // r ≤ x.val} :=
      Equiv.subtypeEquivRight (fun a => by
        unfold blk2
        split_ifs with h'
        · exact ⟨fun h0 => absurd h0 (by decide), fun h0 => absurd h' (Nat.not_lt.mpr h0)⟩
        · exact ⟨fun _ => Nat.not_lt.mp h', fun _ => rfl⟩)
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, M]
    exact (hg (e a).1 (e b).1).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameTau

theorem root_eq_of_close {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (m : ℕ) {ζ ζ' : Ω}
    (h : ζ ^ m = 1) (h' : ζ' ^ m = 1) (hm : ¬ A.valuation (m : Ω) < 1)
    (hc : A.valuation (ζ - ζ') < 1) : ζ = ζ' := by
  first
  | exact @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one
  | (apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowEqOneValuation.eq_of_pow_eq_one_of_valuation_sub_lt_one ..)

theorem ine_fix_root {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  refine root_eq_of_close A m (by rw [← map_pow, hζ, map_one]) hζ hm ?_
  exact hσ.2 ζ (valuation_eq_one_of_pow_eq_one A hm0 hζ).le

theorem quot_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {σ τ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1) {π : Ω} (hπ : π ≠ 0)
    {e : E} (he : π ^ m = algebraMap E Ω e) :
    (σ * τ) π / π = (σ π / π) * (τ π / π) := by
  have hτ : (τ π / π) ^ m = 1 := by
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hfix := ine_fix_root hσ m hm hτ
  have e1 : τ π = (τ π / π) * π := by field_simp
  have e2 : (σ * τ) π = σ (τ π / π) * σ π := by
    rw [AlgEquiv.mul_apply, ← map_mul, div_mul_cancel₀ _ hπ]
  rw [e2, hfix]
  field_simp

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopBlockEqOneIffMemColHK
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem topBlock_eq_one_iff_mem_colHK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  intro κ _ n r t _ hr g hg
  have hb : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (n := n) r) := by
    refine Formalism.L2.DIV.mem_blockTri.2 fun i j hij => ?_
    have hji : j.val < r ∧ ¬ i.val < r := by
      unfold Formalism.L2.DIV.blk2 at hij
      by_cases hj : j.val < r <;> by_cases hi : i.val < r <;> simp [hj, hi] at hij ⊢
    refine hg (show Formalism.L2.Col.coarse r [t] j.val < Formalism.L2.Col.coarse r [t] i.val from ?_)
    rw [Formalism.L2.Col.coarse_of_lt hji.1, Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hji.2)]
    exact Nat.succ_pos _
  rw [Formalism.L2.Col.mem_HK, Units.ext_iff, Formalism.L2.DIV.upper_block_val_submatrix hr hb, Units.val_one]
  constructor
  · intro h
    refine ⟨hg, fun i j hi hj => ?_⟩
    have h1 := congrFun (congrFun h ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.mk.injEq] at h1
    rw [Matrix.one_apply]
    simp only [Fin.ext_iff]
    exact h1
  · rintro ⟨-, h⟩
    ext i j
    rw [Matrix.submatrix_apply, h _ _ i.2 j.2]
    simp [Matrix.one_apply]

end GlobalTheory
end

