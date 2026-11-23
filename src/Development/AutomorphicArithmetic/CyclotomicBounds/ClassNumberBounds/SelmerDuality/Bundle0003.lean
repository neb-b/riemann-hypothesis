module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.H1cEqH1

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.CardCokernelTransposeEqCardKernel
section
namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]

private theorem exists_annihilator_of_maximal [Finite R] (p : Ideal R) (hp : p.IsMaximal) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ p, x * a = 0 := by
  have hfin : Finite (Ideal R) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨I, hI, hmin⟩ := (wellFounded_lt (α := Ideal R)).has_min
    {I : Ideal R | ∀ t : R, (∀ x ∈ I, t * x = 0) → t ∈ p}
    ⟨⊤, fun t ht => by
      have : t = 0 := by simpa using ht 1 trivial
      simp [this]⟩
  by_cases h : ∀ t : R, (∀ x ∈ p • I, t * x = 0) → t ∈ p
  · exfalso
    have hle : p • I ≤ I := Submodule.smul_le_right
    have heq : p • I = I := by
      by_contra hne
      exact hmin _ h (lt_of_le_of_ne hle hne)
    obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul p I
      (IsNoetherian.noetherian I) heq.ge
    have hep : e ∈ p := hI e he
    have h1 : (1 : R) ∈ p := by simpa using p.sub_mem hep he1
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 h1)
  · push Not at h
    obtain ⟨t, ht, htp⟩ := h
    have h2 : ¬ ∀ x ∈ I, t * x = 0 := fun h => htp (hI t h)
    push Not at h2
    obtain ⟨b, hb, hb0⟩ := h2
    refine ⟨t * b, hb0, fun x hx => ?_⟩
    have := ht (x • b) (Submodule.smul_mem_smul hx hb)
    rw [← this, smul_eq_mul]
    ring

private theorem finite_module_dual_of_finite [Finite R] (M : Type*) [AddCommGroup M] [Module R M] [Finite M] :
    Finite (Module.Dual R M) :=
  Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

private theorem card_dual_mul_quotient (hR : Module.Baer R R) {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Nat.card (Module.Dual R M) =
      Nat.card (Module.Dual R (M ⧸ N)) * Nat.card (Module.Dual R N) := by
  have hs : Function.Surjective N.dualRestrict := fun g =>
    hR.extension_property N.subtype N.injective_subtype g
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker N.dualRestrict),
    Nat.card_congr (N.dualRestrict.quotKerEquivOfSurjective hs).toEquiv,
    Submodule.dualRestrict_ker_eq_dualAnnihilator,
    Nat.card_congr N.dualQuotEquivDualAnnihilator.toEquiv]

private theorem card_le_card_dual_of_simple [Finite R] (M : Type*) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Nat.card M ≤ Nat.card (Module.Dual R M) := by
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ‹IsSimpleModule R M›
  rw [Nat.card_congr e.toEquiv, ← Nat.card_congr e.dualMap.toEquiv]
  obtain ⟨a, ha, hpa⟩ := exists_annihilator_of_maximal p hp
  have hle : p ≤ LinearMap.ker (LinearMap.toSpanSingleton R R a) := fun x hx => hpa x hx
  have hge : LinearMap.ker (LinearMap.toSpanSingleton R R a) ≤ p := by
    refine (hp.eq_of_le ?_ hle).ge
    intro h
    have : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) := h ▸ trivial
    exact ha (by simpa using this)
  let ι : (R ⧸ p) →ₗ[R] R := Submodule.liftQ p (LinearMap.toSpanSingleton R R a) hle
  have hι : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hge
  have : Finite (R ⧸ p) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have := finite_module_dual_of_finite (R := R) (R ⧸ p)
  refine Nat.card_le_card_of_injective
    (fun y : R ⧸ p => (ι ∘ₗ LinearMap.mulLeft R y : Module.Dual R (R ⧸ p))) ?_
  intro y z hyz
  simpa using hι (LinearMap.congr_fun hyz 1)

private theorem card_le_card_dual [Finite R] (hR : Module.Baer R R) (k : ℕ) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] [Finite M], Nat.card M = k →
      Nat.card M ≤ Nat.card (Module.Dual R M) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M _ _ _ hk
    have := finite_module_dual_of_finite (R := R) M
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Nat.card_unique]
      exact Nat.card_pos
    by_cases h : ∀ N : Submodule R M, N = ⊥ ∨ N = ⊤
    · have : IsSimpleModule R M := { eq_bot_or_eq_top := h }
      exact card_le_card_dual_of_simple M
    push Not at h
    obtain ⟨N, h0, h1⟩ := h
    have hq : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
    have hN : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
    have hQ : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 h1
    have a1 : 1 < Nat.card N := Finite.one_lt_card
    have a2 : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
    have hc := Submodule.card_eq_card_quotient_mul_card N
    have b1 := ih (Nat.card N) (by rw [← hk, hc]; nlinarith) N rfl
    have b2 := ih (Nat.card (M ⧸ N)) (by rw [← hk, hc]; nlinarith) (M ⧸ N) rfl
    rw [card_dual_mul_quotient hR N, hc, mul_comm]
    exact Nat.mul_le_mul b2 b1

theorem card_dual_of_baer [Finite R] (hR : Module.Baer R R) (M : Type*) [AddCommGroup M]
    [Module R M] [Finite M] : Nat.card (Module.Dual R M) = Nat.card M := by
  classical
  refine le_antisymm ?_ (card_le_card_dual hR _ M rfl)
  have := Fintype.ofFinite M
  let g : (M → R) →ₗ[R] M := Fintype.linearCombination R id
  have hg : Function.Surjective g := fun x => ⟨Pi.single x 1, by simp [g]⟩
  have e := g.quotKerEquivOfSurjective hg
  have h1 := card_dual_mul_quotient hR (LinearMap.ker g)
  rw [← Nat.card_congr (dotProductEquiv R M).toEquiv,
    Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g), Nat.card_congr e.toEquiv,
    ← Nat.card_congr e.dualMap.toEquiv, mul_comm] at h1
  have h2 := card_le_card_dual hR _ (LinearMap.ker g) rfl
  have h3 : 0 < Nat.card (LinearMap.ker g) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ h3
  rw [h1]
  exact Nat.mul_le_mul_left _ h2

end KStar.Selmer
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthFrac
section
namespace KStar.Selmer

open Matrix Module

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

private noncomputable def fracInv (K : Type*) [Field K] [Algebra O K] (Φ : Matrix n n O) :
    (n → O) →ₗ[O] (n → FracMod O K) :=
  LinearMap.pi fun i => (1 : Submodule O K).mkQ ∘ₗ
    LinearMap.toSpanSingleton O K (algebraMap O K Φ.det)⁻¹ ∘ₗ LinearMap.proj i ∘ₗ
      Φ.adjugate.mulVecLin

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
private theorem fracInv_apply (Φ : Matrix n n O) (y : n → O) (i : n) :
    fracInv K Φ y i =
      (1 : Submodule O K).mkQ ((Φ.adjugate *ᵥ y) i • (algebraMap O K Φ.det)⁻¹) := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
private theorem mkQ_eq_zero_iff (z : K) :
    (1 : Submodule O K).mkQ z = 0 ↔ ∃ y : O, algebraMap O K y = z := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]

omit [IsDiscreteValuationRing O] in
private theorem ker_fracInv (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    LinearMap.ker (fracInv K Φ) = LinearMap.range Φ.mulVecLin := by
  have hK : algebraMap O K Φ.det ≠ 0 := fun h0 =>
    h (IsFractionRing.injective O K (by rw [h0, map_zero]))
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hy
    have : ∀ i, ∃ x : O, algebraMap O K x =
        (Φ.adjugate *ᵥ y) i • (algebraMap O K Φ.det)⁻¹ := fun i =>
      (mkQ_eq_zero_iff _).1 (congrFun hy i)
    choose x hx using this
    have h1 : Φ.det • x = Φ.adjugate *ᵥ y := by
      funext i
      apply IsFractionRing.injective O K
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hx, Algebra.smul_def]
      field_simp
    refine ⟨x, ?_⟩
    have h2 : Φ.det • (Φ *ᵥ x) = Φ.det • y := by
      rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    funext i
    exact mul_left_cancel₀ h (congrFun h2 i)
  · rintro ⟨x, rfl⟩
    funext i
    rw [fracInv_apply, Pi.zero_apply, mkQ_eq_zero_iff]
    refine ⟨x i, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
    field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem range_fracInv (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    LinearMap.range (fracInv K Φ) = H1c Φ (FracMod O K) := by
  have hK : algebraMap O K Φ.det ≠ 0 := fun h0 =>
    h (IsFractionRing.injective O K (by rw [h0, map_zero]))
  ext w
  rw [H1c, LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    funext i
    rw [coefMap_apply, Pi.zero_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fracInv_apply, ← map_smul, ← map_sum]
    rw [mkQ_eq_zero_iff]
    refine ⟨y i, ?_⟩
    simp only [smul_smul, ← Finset.sum_smul]
    have h2 : ∑ j, Φ i j * (Φ.adjugate *ᵥ y) j = Φ.det * y i := by
      have : (Φ *ᵥ (Φ.adjugate *ᵥ y)) i = Φ.det * y i := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec,
          Pi.smul_apply, smul_eq_mul]
      exact this
    rw [h2, Algebra.smul_def, map_mul]
    field_simp
  · intro hw
    choose z hz using fun i => (1 : Submodule O K).mkQ_surjective (w i)
    have : ∀ i, ∃ y : O, algebraMap O K y = ∑ j, Φ i j • z j := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← mkQ_eq_zero_iff, map_sum]
      have := congrFun hw i
      rw [coefMap_apply, Pi.zero_apply] at this
      simpa only [map_smul, hz] using this
    choose y hy using this
    refine ⟨y, funext fun i => ?_⟩
    rw [fracInv_apply, ← hz]
    congr 1
    have h3 : algebraMap O K ((Φ.adjugate *ᵥ y) i) = algebraMap O K Φ.det * z i := by
      have h4 : algebraMap O K ((Φ.adjugate *ᵥ y) i) =
          ∑ k, (Φ.adjugate * Φ) i k • z k := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hy, Matrix.mul_apply,
          Finset.sum_smul, ← Algebra.smul_def, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      rw [h4, Matrix.adjugate_mul, ← Algebra.smul_def]
      simp [Matrix.one_apply, ite_smul]
    rw [Algebra.smul_def, h3]
    field_simp

private theorem length_kernel_fraction_module_of_det_ne_zero (Φ : Matrix n n O) (h : Φ.det ≠ 0) :
    Module.length O (H1c Φ (FracMod O K)) = IsDiscreteValuationRing.addVal O Φ.det := by
  rw [← length_cokernel_eq_addVal_det, ← range_fracInv Φ h,
    ← (fracInv K Φ).quotKerEquivRange.length_eq]
  exact (Submodule.quotEquivOfEq _ _ (ker_fracInv Φ h)).length_eq

private theorem length_fracMod : Module.length O (Unit → FracMod O K) = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  have hd : (Matrix.of fun (_ _ : Unit) => ϖ ^ k).det = ϖ ^ k := by simp
  have := length_kernel_fraction_module_of_det_ne_zero (K := K) (Matrix.of fun (_ _ : Unit) => ϖ ^ k)
    (by rw [hd]; exact pow_ne_zero _ hϖ.ne_zero)
  rw [hd, hϖ.addVal_pow] at this
  rw [← this]
  exact Module.length_le_of_injective _ (Submodule.subtype_injective _)

theorem length_kernel_fraction_module_eq_addVal_det (Φ : Matrix n n O) :
    Module.length O (H1c Φ (FracMod O K)) = IsDiscreteValuationRing.addVal O Φ.det := by
  by_cases h : Φ.det = 0
  · rw [h, IsDiscreteValuationRing.addVal_zero, eq_top_iff, ← length_fracMod (O := O) (K := K)]
    obtain ⟨v, hv, hΦ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    have hK : algebraMap O K (v i) ≠ 0 := fun h0 =>
      hi (IsFractionRing.injective O K (by rw [h0, Pi.zero_apply, map_zero]))
    refine Module.length_le_of_surjective
      ((LinearMap.pi fun _ : Unit => LinearMap.proj i) ∘ₗ (H1c Φ (FracMod O K)).subtype) ?_
    intro t
    obtain ⟨z, hz⟩ := (1 : Submodule O K).mkQ_surjective (t ())
    refine ⟨⟨fun j => v j • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z), ?_⟩, ?_⟩
    · rw [H1c, LinearMap.mem_ker]
      funext a
      rw [coefMap_apply]
      simp only [smul_smul, ← Finset.sum_smul]
      have : ∑ j, Φ a j * v j = 0 := congrFun hΦ a
      rw [this, zero_smul, Pi.zero_apply]
    · funext u
      change v i • (1 : Submodule O K).mkQ ((algebraMap O K (v i))⁻¹ * z) = t ()
      rw [← map_smul, ← hz, Algebra.smul_def, mul_inv_cancel_left₀ hK]
  · exact length_kernel_fraction_module_of_det_ne_zero Φ h

end KStar.Selmer
end

