module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BijectiveOfIntertwining
section
namespace GlobalTheory.BijectiveIntertwining

theorem bijective_of_intertwining {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (h : Representation.IsIrreducible ρ) (h' : Representation.IsIrreducible ρ')
    (F : V →ₗ[ℂ] V') (hF : ∀ (g : G) (v : V), F (ρ g v) = ρ' g (F v)) (h0 : F ≠ 0) :
    Function.Bijective F := by
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker F
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hF, hv, map_zero] }
  let R : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range F
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, rfl⟩
        exact ⟨ρ g v, hF g v⟩ }
  constructor
  · rcases h.eq_bot_or_eq_top K with hK | hK
    · rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hK
    · exact absurd (LinearMap.ker_eq_top.mp (congrArg Subrepresentation.toSubmodule hK)) h0
  · rcases h'.eq_bot_or_eq_top R with hR | hR
    · exact absurd (LinearMap.range_eq_bot.mp (congrArg Subrepresentation.toSubmodule hR)) h0
    · rw [← LinearMap.range_eq_top]
      exact congrArg Subrepresentation.toSubmodule hR

end GlobalTheory.BijectiveIntertwining
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRange
section
namespace GlobalTheory

open Matrix

theorem bilinForm_injective_exists_mul_mem_range (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La)
    (hEF : Function.Injective EF) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ La
  let b : Module.Basis ι ℤ La := Module.Free.chooseBasis ℤ La
  let A : Matrix ι ι ℤ := fun i j => EF (b i) (b j)

  have key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j := by
    intro c j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0
    have hx : EF (∑ i, v i • b i) = 0 := by
      refine b.ext fun j => ?_
      rw [key, hvA]; simp
    have : (∑ i, v i • b i) = 0 := hEF (by rw [hx, map_zero])
    apply hv
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v this i
  set d := A.det
  refine ⟨d.natAbs * d.natAbs, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.2 hdet
    positivity
  · intro f
    let w : ι → ℤ := fun j => f (b j)
    refine ⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩
    refine b.ext fun j => ?_
    rw [key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    have hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' d
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]
    rw [← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CancelProdSummandNilpotentOrBijective
section
namespace GlobalTheory

section CancelSummand

variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]

theorem linearEquiv_of_prod_corner_bijective (e : (M × P) ≃ₗ[R] (M' × P))
    (hd : Function.Bijective ((LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P)) :
    Nonempty (M ≃ₗ[R] M') := by
  set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  let dE : P ≃ₗ[R] P := LinearEquiv.ofBijective d hd
  let c : M →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inl R M P
  let φ : M →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))
  let ψ : M' →ₗ[R] M := (LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  have hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2 := by
    intro x
    have hx : x = ((x.1, 0) : M × P) + (0, x.2) := by simp
    conv_lhs => rw [hx]
    rw [map_add (f := _)]
    rfl
  have hdd : ∀ p : P, d (dE.symm p) = p := fun p => dE.apply_symm_apply p
  have key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0) := by
    intro m
    ext
    · rfl
    · rw [hsplit]
      simp only [map_neg, hdd]
      simp
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply LinearMap.ext
    intro m'
    set x := e.symm (m', 0) with hx
    have hex : e x = (m', 0) := by simp [hx]
    have hp : -dE.symm (c x.1) = x.2 := by
      have h0 := hsplit x
      rw [hex] at h0
      have h1 : d x.2 = -c x.1 := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
      have h2 : dE.symm (d x.2) = x.2 := dE.symm_apply_apply x.2
      rw [h1, map_neg] at h2
      exact h2
    have hk := key x.1
    rw [hp] at hk
    have hψ : ψ m' = x.1 := rfl
    show φ (ψ m') = m'
    rw [hψ]
    have h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0) := by rw [← hk]; exact hex
    exact congrArg Prod.fst h3
  · apply LinearMap.ext
    intro m
    show ψ (φ m) = m
    have h : ψ (φ m) = (e.symm (φ m, 0)).1 := rfl
    rw [h, ← key m, LinearEquiv.symm_apply_apply]

theorem linearEquiv_cancel_of_nilpotent_or_bijective
    (hP : ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f)
    (e : (M × P) ≃ₗ[R] (M' × P)) : Nonempty (M ≃ₗ[R] M') := by
  set d : Module.End R P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  by_cases hd : Function.Bijective d
  · exact linearEquiv_of_prod_corner_bijective e hd
  let b : P →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P
  let c' : M' →ₗ[R] P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  let d' : Module.End R P := (LinearMap.snd R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inr R M' P
  have hsum : c' ∘ₗ b = 1 - d' * d := by
    apply LinearMap.ext
    intro p
    have h : e (0, p) = ((b p, 0) : M' × P) + (0, d p) := by
      ext
      · simp; rfl
      · simp; rfl
    have h2 := congrArg Prod.snd (e.symm_apply_apply (0, p))
    rw [h, map_add (f := _)] at h2
    show c' (b p) = p - d' (d p)
    rw [eq_sub_iff_add_eq]
    exact h2
  have hnil : IsNilpotent (d' * d) := by
    rcases hP (d' * d) with h | h
    · exact h
    · exfalso
      apply hd
      have hinj : Function.Injective d := fun x y hxy => h.1 (by
        show d' (d x) = d' (d y)
        rw [hxy])
      rcases hP d with ⟨n, hn⟩ | h2
      · have hsub : ∀ x : P, x = 0 := by
          intro x
          apply hinj.iterate n
          have h3 : (d ^ n) x = (d ^ n) 0 := by rw [hn]; simp
          simpa [Module.End.pow_apply] using h3
        exact ⟨hinj, fun y => ⟨0, by rw [map_zero, hsub y]⟩⟩
      · exact h2
  have hw : IsUnit (c' ∘ₗ b : Module.End R P) := by
    rw [hsum]; exact hnil.isUnit_one_sub
  let winv : Module.End R P := ↑(hw.unit⁻¹)
  let g : M' →ₗ[R] P := ((1 - d) * winv) ∘ₗ c'
  let τ : (M' × P) ≃ₗ[R] (M' × P) :=
    LinearEquiv.skewProd (LinearEquiv.refl R M') (LinearEquiv.refl R P) g
  have hcorner : (LinearMap.snd R M' P) ∘ₗ ((e.trans τ : (M × P) ≃ₗ[R] (M' × P)) :
      (M × P) →ₗ[R] (M' × P)) ∘ₗ LinearMap.inr R M P = LinearMap.id := by
    apply LinearMap.ext
    intro p
    have h1 : g (b p) = p - d p := by
      have h4 : (winv * (c' ∘ₗ b : Module.End R P)) p = p := by
        rw [hw.val_inv_mul]; rfl
      show ((1 - d) * winv) (c' (b p)) = p - d p
      change (1 - d) ((winv * (c' ∘ₗ b : Module.End R P)) p) = p - d p
      rw [h4]
      simp
    show (e (0, p)).2 + g ((e (0, p)).1) = p
    change d p + g (b p) = p
    rw [h1]
    abel
  exact linearEquiv_of_prod_corner_bijective (e.trans τ) (by rw [hcorner]; exact Function.bijective_id)

end CancelSummand

theorem cancel_summand_nilpotent_or_bijective : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ hP he
  obtain ⟨e⟩ := he
  exact linearEquiv_cancel_of_nilpotent_or_bijective hP e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldProdEmbeddingsRegroupMaximalReal
section
open NumberField

namespace GlobalTheory

theorem cm_eq_or_conj_of_comp_eq (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : InfinitePlace.mk τ = InfinitePlace.mk τ' := by
    apply (IsCMField.equivInfinitePlace E).injective
    rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
      InfinitePlace.comap_mk, InfinitePlace.comap_mk, h]
  rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr h2.symm

theorem cm_conj_comp_eq (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by
  have h := IsTotallyReal.complexEmbedding_isReal (τ.comp (algebraMap (maximalRealSubfield E) E))
  rw [ComplexEmbedding.isReal_iff] at h
  exact h

theorem cm_prod_regroup_maximalReal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (k : (E →+* ℂ) → ℤ) (hk : ∀ τ, k (ComplexEmbedding.conjugate τ) = k τ) :
    ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, ∀ g : (maximalRealSubfield E →+* ℂ) → ℂ,
      ∏ τ : E →+* ℂ, g (τ.comp (algebraMap (maximalRealSubfield E) E)) ^ k τ =
        ∏ φ, g φ ^ (2 * n φ) := by
  classical
  refine ⟨fun φ => k (ComplexEmbedding.lift E φ), fun g => ?_⟩
  rw [← Finset.prod_fiberwise Finset.univ
    (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E))]
  refine Finset.prod_congr rfl fun φ _ => ?_
  set τ₀ := ComplexEmbedding.lift E φ with hτ₀
  have h0 : τ₀.comp (algebraMap (maximalRealSubfield E) E) = φ :=
    ComplexEmbedding.lift_comp_algebraMap E φ
  have h1 : (ComplexEmbedding.conjugate τ₀).comp (algebraMap (maximalRealSubfield E) E) = φ := by
    rw [cm_conj_comp_eq, h0]
  have hne : τ₀ ≠ ComplexEmbedding.conjugate τ₀ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter
      (fun τ : E →+* ℂ => τ.comp (algebraMap (maximalRealSubfield E) E) = φ) =
      {τ₀, ComplexEmbedding.conjugate τ₀} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact cm_eq_or_conj_of_comp_eq E τ₀ τ (h.trans h0.symm)
    · rintro (rfl | rfl)
      · exact h0
      · exact h1
  rw [hfib, Finset.prod_pair hne, h0, h1, hk, mul_comm (2 : ℤ), zpow_mul, zpow_two]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjMemOfMemHeckeLevel
section
namespace GlobalTheory.HeckeCorr

variable {Gf : Type*} [Group Gf]

def heckeLevel (U : Subgroup Gf) (g : Gf) : Subgroup Gf := U ⊓ U.map (MulAut.conj g).toMonoidHom

theorem heckeLevel_le (U : Subgroup Gf) (g : Gf) : heckeLevel U g ≤ U := inf_le_left

theorem conj_mem_of_mem_heckeLevel {U : Subgroup Gf} {g u : Gf} (hu : u ∈ heckeLevel U g) : g⁻¹ * u * g ∈ U := by
  obtain ⟨-, v, hv, rfl⟩ := hu
  simpa [MulAut.conj_apply, mul_assoc] using hv

end GlobalTheory.HeckeCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCharUnitsComplex
section
namespace GlobalTheory

theorem continuous_char_units_complex : ∀ ψ : ℂˣ →* ℂˣ, Continuous ψ → ∃ (s : ℂ) (n : ℤ), ∀ z : ℂˣ,
    (ψ z : ℂ) = Complex.exp (s * Real.log ‖(z : ℂ)‖) * ((z : ℂ) / ‖(z : ℂ)‖) ^ n := by
  intro ψ hψ
  let E : ℂ → ℂˣ := fun w => Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)
  have hE : Continuous E := by
    refine Units.continuous_iff.2 ⟨Complex.continuous_exp, ?_⟩
    have : (fun w => ((E w)⁻¹ : ℂˣ).val) = fun w => (Complex.exp w)⁻¹ := by
      funext w; simp [E]
    rw [this]
    exact Complex.continuous_exp.inv₀ Complex.exp_ne_zero
  have hEadd : ∀ x y, E (x + y) = E x * E y := fun x y => Units.ext (Complex.exp_add x y)
  have hE0 : E 0 = 1 := Units.ext Complex.exp_zero
  let f : C(ℂ, {z : ℂ // z ≠ 0}) :=
    ⟨fun w => ⟨(ψ (E w) : ℂ), Units.ne_zero _⟩, (Units.continuous_val.comp (hψ.comp hE)).subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (Subtype.ext (by simp [f, hE0]))
  have hF' : ∀ w, Complex.exp (F w) = (ψ (E w) : ℂ) := fun w => congrArg Subtype.val (congrFun hF w)
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hc : Continuous fun y => F (x + y) - F y := by fun_prop
    have := Complex.isCoveringMap_exp.const_of_comp hc (fun y y' => Subtype.ext (by
      simp only [Complex.exp_sub, hF', hEadd, map_mul, Units.val_mul]
      rw [mul_div_assoc, mul_div_assoc, div_self (Units.ne_zero _), div_self (Units.ne_zero _)])) y 0
    simp only [add_zero, hF0, sub_zero] at this
    rw [← this]; ring
  let L : ℂ →L[ℝ] ℂ := (AddMonoidHom.mk' F hadd).toRealLinearMap F.continuous
  have hL : ∀ w, (ψ (E w) : ℂ) = Complex.exp (L w) := fun w => (hF' w).symm

  have hper : Complex.exp (L (2 * Real.pi * Complex.I)) = 1 := by
    rw [← hL]
    have : E (2 * Real.pi * Complex.I) = 1 := Units.ext Complex.exp_two_pi_mul_I
    rw [this, map_one, Units.val_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hper
  have hLI : L Complex.I = n * Complex.I := by
    have e : L (2 * Real.pi * Complex.I) = (2 * Real.pi : ℝ) • L Complex.I := by
      rw [← map_smul, Complex.real_smul]; push_cast; ring_nf
    rw [e, Complex.real_smul] at hn
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    push_cast at hn
    have : (2 * Real.pi : ℂ) * L Complex.I = (2 * Real.pi : ℂ) * (n * Complex.I) := by rw [hn]; ring
    exact mul_left_cancel₀ hpi this
  refine ⟨L 1, n, fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hnz : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hEz : E (Complex.log z) = z := Units.ext (Complex.exp_log hz)
  have hlog : Complex.log z = (Real.log ‖(z : ℂ)‖ : ℝ) • (1 : ℂ) + (Complex.arg z : ℝ) • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]; rfl
  have hunit : (z : ℂ) / ‖(z : ℂ)‖ = Complex.exp (Complex.arg z * Complex.I) := by
    rw [div_eq_iff hnz, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
  rw [← hEz, hL, hEz, hunit, ← Complex.exp_int_mul, ← Complex.exp_add, hlog, map_add (f := _), map_smul, map_smul,
    hLI, Complex.real_smul, Complex.real_smul]
  congr 1
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfValuationEq
section
open IsDedekindDomain Topology

namespace GlobalTheory.ValuationExtensionContinuous

theorem continuous_of_valuation_eq {A B Γ : Type} [Ring A] [Ring B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ]
    (hs : Function.Surjective (Valued.v : A → Γ)) (g : A →+* B)
    (hg : ∀ a, Valued.v (g a) = (Valued.v a : Γ)) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨k, hk⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hk0 : (Valued.v k : Γ) ≠ 0 := by
    rw [hk]
    exact (map_ne_zero _).mpr γ.ne_zero
  have hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0 := by simpa using hk0
  refine ⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]
  exact hx

theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R]
    [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K)) (u : HeightOneSpectrum R)
    (f : K →+* u.adicCompletion L)
    (hf : ∀ x : K, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (w.adicCompletion K) x) = f x) ∧
      ∀ y : w.adicCompletion K, Valued.v (φ y) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* u.adicCompletion L :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hg : Continuous g := by
    refine continuous_of_valuation_eq (fun c => ?_) g (fun a => hf _)
    obtain ⟨k, hk⟩ := w.valuation_surjective K c
    exact ⟨WithVal.toVal _ k, hk⟩
  let ψ := UniformSpace.Completion.extensionHom g hg
  let φ : w.adicCompletion K →+* u.adicCompletion L :=
    ψ.comp (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom
  have hψ : Continuous ψ := UniformSpace.Completion.continuous_extension
  have hφ : Continuous φ :=
    hψ.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w)
  have hφa : ∀ a : WithVal (w.valuation K),
      φ (HeightOneSpectrum.adicCompletion.ofCompletion (a : (w.valuation K).Completion))
        = f a.ofVal := fun a => UniformSpace.Completion.extensionHom_coe g hg a
  refine ⟨φ, hφ, fun x => hφa (WithVal.toVal _ x), fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero]
  have h1 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have h2 : (Valued.v (φ y) : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have hU := Filter.inter_mem (Valued.locally_const h1)
    (hφ.continuousAt.preimage_mem_nhds (Valued.locally_const h2))
  have hV := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).continuousAt
    (x := y.toCompletion) |>.preimage_mem_nhds hU
  obtain ⟨a, ha1, ha2⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hV
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ha1 ha2
  rw [← ha1, ← ha2, hφa, hf]
  exact (HeightOneSpectrum.adicCompletion.valued_coe K w a.ofVal).symm

end GlobalTheory.ValuationExtensionContinuous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndomorphismIndecomposableNilpotentOrBijective
section
namespace GlobalTheory

theorem endo_indecomposable_finite_length_nilpotent_or_bijective :
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1

end GlobalTheory
end

