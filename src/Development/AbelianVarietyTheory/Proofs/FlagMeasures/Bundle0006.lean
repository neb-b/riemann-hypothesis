module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPowSmulMem
section
namespace GlobalTheory.PowSmulMem

theorem exists_pow_smul_mem {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V]
    {O : Subring E} {p : E} (hp : p ∈ O) (hO : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ' : Submodule O V) (hsp : Submodule.span E (Λ' : Set V) = ⊤) (v : V) :
    ∃ a : ℕ, ∀ b, a ≤ b → p ^ b • v ∈ Λ' := by
  have hv : v ∈ Submodule.span E (Λ' : Set V) := hsp ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun b _ => ?_⟩
    exact Λ'.smul_mem (⟨p ^ b, O.pow_mem hp b⟩ : O) hx
  | zero => exact ⟨0, fun b _ => by rw [smul_zero]; exact Λ'.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    refine ⟨max a c, fun b hb => ?_⟩
    rw [smul_add]
    exact Λ'.add_mem (ha b (le_trans (le_max_left _ _) hb)) (hc b (le_trans (le_max_right _ _) hb))
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hO e
    refine ⟨a + c, fun b hb => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
    have h : p ^ (a + c + d) • e • x = (p ^ c * e) • (p ^ (a + d) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [h]
    exact Λ'.smul_mem (⟨p ^ c * e, hc⟩ : O) (ha _ (Nat.le_add_right _ _))

theorem main : ∀ {E : Type} [inst : CommRing E] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module E V] {O : Subring E} {p : E}, p ∈ O → (∀ (e : E), ∃ (a : ℕ), p ^ a * e ∈ O) → ∀ (Λ Λ' : Submodule (↥O) V), Submodule.FG Λ → Submodule.span E (↑Λ' : Set V) = ⊤ → ∃ (a : ℕ), ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  intro E _ V _ _ O p hp hO Λ Λ' hfg hsp
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose f hf using exists_pow_smul_mem hp hO Λ' hsp
  refine ⟨s.sup f, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hf x _ (Finset.le_sup (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul e x _ hx =>
    have h : p ^ s.sup f • e • x = e • (p ^ s.sup f • x) := by
      change p ^ s.sup f • (e : E) • x = (e : E) • (p ^ s.sup f • x)
      exact smul_comm _ _ _
    rw [h]
    exact Λ'.smul_mem e hx

end GlobalTheory.PowSmulMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubmoduleSkewBlockFinrankLe
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

def skewOpsBlock (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Submodule ℝ (F →L[ℂ] F) where
  carrier := {M | ∀ x z, ⟪M x, z⟫_ℂ + ⟪x, M z⟫_ℂ = 0}
  zero_mem' := by intro x z; simp
  add_mem' := by
    intro a b ha hb x z
    have h1 := ha x z
    have h2 := hb x z
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha x z
    have h1 := ha x z
    have e : ∀ y, (c • a) y = (c : ℂ) • a y := fun y => by
      simp [Complex.coe_smul]
    simp only [e, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (c : ℂ) * h1

theorem finrank_skewOpsBlock_le (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    Module.finrank ℝ (skewOpsBlock F) ≤ Module.finrank ℂ F ^ 2 := by
  let J : (F →L[ℂ] F) →ₗ[ℝ] (F →L[ℂ] F) :=
    { toFun := fun M => Complex.I • M
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  have hJ : Function.Injective J := by
    intro a b h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hd : Disjoint (skewOpsBlock F) ((skewOpsBlock F).map J) := by
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : b = 0 := by
      ext x
      have h1 := ha x (b x)
      have h2 := hb x (b x)
      have e : ∀ y, J b y = Complex.I • b y := fun y => rfl
      simp only [e, inner_smul_left, inner_smul_right, Complex.conj_I] at h1
      have h3 : ⟪b x, b x⟫_ℂ = 0 := by
        linear_combination (Complex.I / 2) * h1 + (1 / 2 : ℂ) * h2 +
          ((⟪b x, b x⟫_ℂ - ⟪x, b (b x)⟫_ℂ) / 2) * Complex.I_mul_I
      simpa using h3
    rw [hb0, map_zero]
  haveI : FiniteDimensional ℝ (F →L[ℂ] F) := FiniteDimensional.complexToReal _
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [← (Submodule.equivMapOfInjective J hJ (skewOpsBlock F)).finrank_eq,
    finrank_real_of_complex] at h1
  have h2 : Module.finrank ℂ (F →L[ℂ] F) = Module.finrank ℂ F ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := F) (F' := F)).finrank_eq,
      Module.finrank_linearMap, sq]
  omega

theorem exists_submodule_skew_block_finrank_le (n : ℕ)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ Module.finrank ℂ E ^ 2 ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ x ∈ E, ∀ z ∈ E, ⟪T x, z⟫_ℂ + ⟪x, T z⟫_ℂ = 0) →
          E.starProjection ∘L T ∘L E.starProjection ∈ U := by
  let Φ : (E →L[ℂ] E) →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun a b => by ext1 x; rfl
      map_smul' := fun c a => by ext1 x; rfl }
  haveI : FiniteDimensional ℝ (E →L[ℂ] E) := FiniteDimensional.complexToReal _
  refine ⟨(skewOpsBlock E).map Φ,
    (Submodule.finrank_map_le Φ _).trans (finrank_skewOpsBlock_le E), ?_⟩
  intro T hT
  refine ⟨E.orthogonalProjection ∘L T ∘L E.subtypeL, ?_, ?_⟩
  · intro x z
    have := hT x x.2 z z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjection_eq_of_mem_left,
      Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact this
  · ext1 x; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularLiftOfUnimodularMod
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_add_mul_notMem_of_maximal_ge {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J : Ideal R) (hJ : J ≠ 0) (n x : R)
    (h : ∀ p : Ideal R, p.IsMaximal → J ≤ p → n ∈ p → x ∉ p) :
    ∃ s : R, ∀ p : Ideal R, p.IsMaximal → J ≤ p → x + n * s ∉ p := by
  classical
  haveI : Fintype {p : Ideal R // p ∣ J} := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  let ι := {p : Ideal R // p.IsMaximal ∧ J ≤ p}
  haveI : Finite ι := Finite.of_injective
    (fun p : ι => (⟨p.1, Ideal.dvd_iff_le.2 p.2.2⟩ : {p : Ideal R // p ∣ J}))
    (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hc : Pairwise fun i j : ι => IsCoprime i.1 j.1 := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne i.2.1 j.2.1 (fun e => hij (Subtype.ext e))
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective (I := fun i : ι => i.1) hc
    (fun i => Ideal.Quotient.mk i.1 (if x ∈ i.1 then 1 else 0))
  refine ⟨s, fun p hp hJp hmem => ?_⟩
  have h1 := Ideal.Quotient.eq.1 (hs ⟨p, hp, hJp⟩)
  by_cases hx : x ∈ p
  · simp only [hx, if_true] at h1
    have h2 : n * s ∈ p := by simpa using p.sub_mem hmem hx
    have h3 : n ∈ p := by
      have := p.sub_mem h2 (p.mul_mem_left n h1)
      have e : n * s - n * (s - 1) = n := by ring
      rwa [e] at this
    exact h p hp hJp h3 hx
  · simp only [hx, if_false, sub_zero] at h1
    apply hx
    simpa using p.sub_mem hmem (p.mul_mem_left n h1)

theorem exists_unimodular_lift_of_unimodular_mod :
    ∀ (F : Type) [Field F] [NumberField F] (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), b ≠ 0 → ∀ (n x₀ : 𝓞 F) (y₀ : F), n ≠ 0 → y₀ ∈ b → (∀ p : Ideal (𝓞 F), p.IsMaximal → n ∈ p → ¬ (x₀ ∈ p ∧ y₀ ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b)) → ∃ (s : 𝓞 F) (t : F), t ∈ b ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → ¬ (x₀ + n * s ∈ p ∧ y₀ + (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b) := by
  intro F _ _ b hb n x₀ y₀ hn hy₀ H
  have hnF : (n : F) ≠ 0 := by
    intro e
    exact hn (RingOfIntegers.ext e)
  obtain ⟨t, ht, hy⟩ : ∃ t : F, t ∈ b ∧ y₀ + (n : F) * t ≠ 0 := by
    by_cases h0 : y₀ = 0
    · obtain ⟨t, ht, ht0⟩ : ∃ t : F, t ∈ b ∧ t ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hb (FractionalIdeal.eq_zero_iff.2 hcon)
      exact ⟨t, ht, by rw [h0, zero_add]; exact mul_ne_zero hnF ht0⟩
    · exact ⟨0, b.zero_mem, by simpa using h0⟩
  set y := y₀ + (n : F) * t with hydef
  have hyb : y ∈ b := by
    have h1 : n • t ∈ (b : Submodule (𝓞 F) F) := Submodule.smul_mem _ n ht
    exact Submodule.add_mem (b : Submodule (𝓞 F) F) hy₀ h1
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y * b⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hb]
    exact mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 hyb) _
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJb : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b
      = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ hb, mul_one]
  have hJ0 : J ≠ 0 := by
    rintro rfl
    apply hy
    rw [← FractionalIdeal.spanSingleton_eq_zero_iff (S := nonZeroDivisors (𝓞 F)), ← hJb]
    simp
  have key : ∀ p : Ideal (𝓞 F),
      y ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b ↔ J ≤ p := by
    intro p
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← FractionalIdeal.coeIdeal_le_coeIdeal F]
    constructor
    · intro h
      have := mul_le_mul_left h b⁻¹
      rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, ← hJ] at this
    · intro h
      rw [← hJb]
      exact mul_le_mul_left h b
  obtain ⟨s, hs⟩ := exists_add_mul_notMem_of_maximal_ge J hJ0 n x₀ (by
    intro p hp hJp hnp hx
    refine H p hp hnp ⟨hx, ?_⟩
    have h1 := (key p).2 hJp
    have h2 : (n : F) * t ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hnp) ht
    have h3 := Submodule.sub_mem
      (((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * b : FractionalIdeal _ F) : Submodule (𝓞 F) F) h1 h2
    have e : y - (n : F) * t = y₀ := by rw [hydef]; ring
    rw [e] at h3
    exact h3)
  exact ⟨s, t, ht, fun p hp h => hs p hp ((key p).1 h.2) h.1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEq
section
open Matrix

namespace GlobalTheory

theorem conjTranspose_mul_mul_eq_of_form_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by
  have key : ∀ z w : Fin n → E, star z ⬝ᵥ ((γᴴ * J * γ) *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) := by
    intro z w
    rw [← h z w, star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  ext i j
  simpa [single_dotProduct, mulVec_single_one] using key (star (Pi.single i 1)) (Pi.single j 1)

theorem star_form_eq_of_hermitian {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by
  rw [star_dotProduct z (J *ᵥ w), star_star, star_mulVec, ← dotProduct_mulVec, hJ]

private lemma form_sub_smul_left {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (s : E) :
    star (z - s • u) ⬝ᵥ (J *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) - star s * (star u ⬝ᵥ (J *ᵥ w)) := by
  rw [star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma form_sub_smul_right {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z u w : Fin n → E) (t : E) :
    star z ⬝ᵥ (J *ᵥ (w - t • u)) = star z ⬝ᵥ (J *ᵥ w) - t * (star z ⬝ᵥ (J *ᵥ u)) := by
  rw [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

private lemma form_mulVec_eq_of_transvection {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (γ : Matrix (Fin n) (Fin n) E)
    (u : Fin n → E) (c : E)
    (hγ : ∀ v, γ *ᵥ v = v - (c * (star u ⬝ᵥ (J *ᵥ v))) • u)
    (hc : c + star c = star c * c * (star u ⬝ᵥ (J *ᵥ u))) (z w : Fin n → E) :
    star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w) := by
  have hzu := star_form_eq_of_hermitian J hJ u z
  rw [hγ z, hγ w, form_sub_smul_left, form_sub_smul_right J z u w,
    form_sub_smul_right J u u w, star_mul']
  linear_combination (c * (star u ⬝ᵥ (J *ᵥ w))) * hzu +
    (-(star (star u ⬝ᵥ (J *ᵥ z))) * (star u ⬝ᵥ (J *ᵥ w))) * hc

theorem exists_quasiReflection_mulVec_eq {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (x y : Fin n → E)
    (hxy : star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y))
    (h0 : star (x - y) ⬝ᵥ (J *ᵥ x) ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  have hγ : ∀ v, (1 - (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ • vecMulVec (x - y) (star (x - y) ᵥ* J)) *ᵥ v
      = v - ((star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ v))) • (x - y) := by
    intro v
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  have hsa : star (star (x - y) ⬝ᵥ (J *ᵥ x)) = star x ⬝ᵥ (J *ᵥ (x - y)) :=
    star_form_eq_of_hermitian J hJ (x - y) x
  have hsum : star (x - y) ⬝ᵥ (J *ᵥ x) + star (star (x - y) ⬝ᵥ (J *ᵥ x))
      = star (x - y) ⬝ᵥ (J *ᵥ (x - y)) := by
    rw [hsa]
    simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]
    linear_combination hxy
  have hs0 : star (star (x - y) ⬝ᵥ (J *ᵥ x)) ≠ 0 := (star_ne_zero).mpr h0
  have hc : (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ + star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
      = star (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹ * (star (x - y) ⬝ᵥ (J *ᵥ x))⁻¹
        * (star (x - y) ⬝ᵥ (J *ᵥ (x - y))) := by
    rw [star_inv₀, ← hsum]
    field_simp
    ring
  refine ⟨_, conjTranspose_mul_mul_eq_of_form_eq J _
    (form_mulVec_eq_of_transvection J hJ _ (x - y) _ hγ hc), ?_⟩
  rw [hγ, inv_mul_cancel₀ h0, one_smul, sub_sub_cancel]

theorem exists_unitary_mulVec_eq_of_form_eq :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  intro E _ _ _ n J hJ _ x y hxy hx
  by_cases h0 : star (x - y) ⬝ᵥ (J *ᵥ x) = 0
  · have hneg : star (-y) ⬝ᵥ (J *ᵥ (-y)) = star y ⬝ᵥ (J *ᵥ y) := by
      rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hyx : star y ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ (J *ᵥ x) := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at h0
      exact h0.symm
    have h1 : star (x - -y) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
      rw [sub_neg_eq_add, star_add, add_dotProduct, hyx, ← two_mul]
      exact mul_ne_zero two_ne_zero hx
    obtain ⟨γ, hγ, hγx⟩ := exists_quasiReflection_mulVec_eq J hJ x (-y) (hxy.trans hneg.symm) h1
    refine ⟨-γ, ?_, ?_⟩
    · rw [conjTranspose_neg, neg_mul, mul_neg, neg_mul, neg_neg, hγ]
    · rw [neg_mulVec, hγx, neg_neg]
  · exact exists_quasiReflection_mulVec_eq J hJ x y hxy h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLower
section
open Matrix Finset Real

namespace GlobalTheory

theorem one_add_add_sq_div_three_le_exp (u : ℝ) (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have h := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have h5 : |u| ^ 5 ≤ u ^ 4 := by
    rw [← h4, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hu
  have h6 : -1 ≤ u := (abs_le.mp hu).1
  have h7 : 0 ≤ u ^ 2 * (1 + u) := mul_nonneg (sq_nonneg u) (by linarith)
  have h8 : 0 ≤ u ^ 4 := by positivity
  nlinarith

theorem three_mul_div_four_le_log_one_add (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    3 * u / 4 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
  have : (1 + u)⁻¹ ≤ 1 - 3 * u / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith
  linarith

theorem exp_quadratic_lower_and_log_linear_lower :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) :=
  ⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAndNcardLeProdOfLevels
section
open Finset

namespace GlobalTheory

theorem card_le_prod_of_separated_levels {α β : Type} (S : Set α) (lv : β → ℕ)
    (r : β → α → α → Prop) (B : β → ℝ) (hr : ∀ b, Equivalence (r b)) (s : Finset β) :
    (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
      (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
      (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) →
    ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, (∀ b ∈ s, r b x y) → x = y) →
      (T.card : ℝ) ≤ ∏ b ∈ s, B b := by
  classical
  induction s using Finset.induction_on_max_value lv with
  | empty =>
    intro _ T _ hT
    have : T.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => hT x hx y hy (by simp)
    simpa using this
  | insert a s ha hmax ih =>
    intro hp T hTS hT
    have hps : ∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S →
        (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) →
        (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b := by
      intro b hb T' h1 h2 h3
      refine hp b (mem_insert_of_mem hb) T' h1 ?_ h3
      intro x hx y hy b' hb' hlt
      rcases mem_insert.1 hb' with rfl | hb'
      · exact absurd (hmax b hb) (by omega)
      · exact h2 x hx y hy b' hb' hlt
    have hBa : 0 ≤ B a := by
      simpa using hp a (mem_insert_self _ _) ∅ (by simp) (by simp) (by simp)
    rw [prod_insert ha]
    rcases T.eq_empty_or_nonempty with rfl | ⟨x0, -⟩
    · have := ih hps ∅ (by simp) (by simp)
      simp only [card_empty, Nat.cast_zero] at this ⊢
      positivity
    haveI : Nonempty α := ⟨x0⟩
    let q : α → Set α := fun x => {y | ∀ b ∈ s, r b x y}
    have hq : ∀ x y, q x = q y ↔ ∀ b ∈ s, r b x y := by
      intro x y
      constructor
      · intro h
        have : y ∈ q y := fun b _ => (hr b).refl y
        rw [← h] at this
        exact this
      · intro h
        ext z
        exact ⟨fun hz b hb => (hr b).trans ((hr b).symm (h b hb)) (hz b hb),
          fun hz b hb => (hr b).trans (h b hb) (hz b hb)⟩
    let ρ : α → α := fun x => Function.invFunOn q (↑T : Set α) (q x)
    have hρ : ∀ x ∈ T, ρ x ∈ T ∧ q (ρ x) = q x := fun x hx =>
      Function.invFunOn_pos (f := q) (s := (↑T : Set α)) ⟨x, hx, rfl⟩
    have him : ((T.image ρ).card : ℝ) ≤ ∏ b ∈ s, B b := by
      refine ih hps _ ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hz)
        exact hTS (hρ x hx).1
      · intro z hz w hw h
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
        have h' := (hq _ _).2 h
        rw [(hρ x hx).2, (hρ y hy).2] at h'
        simp only [ρ, h']
    have hfib : ∀ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ) ≤ B a := by
      intro z _
      have key : ∀ x ∈ T.filter (fun x => ρ x = z), ∀ y ∈ T.filter (fun x => ρ x = z),
          ∀ b ∈ s, r b x y := by
        intro x hx y hy
        obtain ⟨hx, hx'⟩ := mem_filter.1 hx
        obtain ⟨hy, hy'⟩ := mem_filter.1 hy
        rw [← hq, ← (hρ x hx).2, ← (hρ y hy).2, hx', hy']
      refine hp a (mem_insert_self _ _) _ ?_ ?_ ?_
      · intro x hx
        exact hTS (mem_filter.1 (mem_coe.1 hx)).1
      · intro x hx y hy b' hb' hlt
        rcases mem_insert.1 hb' with rfl | hb'
        · exact absurd hlt (lt_irrefl _)
        · exact key x hx y hy b' hb'
      · intro x hx y hy h
        refine hT x (mem_filter.1 hx).1 y (mem_filter.1 hy).1 ?_
        intro b hb
        rcases mem_insert.1 hb with rfl | hb
        · exact h
        · exact key x hx y hy b hb
    rw [Finset.card_eq_sum_card_image ρ T]
    push_cast
    calc ∑ z ∈ T.image ρ, ((T.filter (fun x => ρ x = z)).card : ℝ)
        ≤ ∑ _z ∈ T.image ρ, B a := sum_le_sum hfib
      _ = B a * ((T.image ρ).card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ B a * ∏ b ∈ s, B b := mul_le_mul_of_nonneg_left him hBa

theorem finite_and_ncard_le_prod_of_levels :
    ∀ (α β : Type) (S : Set α) (s : Finset β) (lv : β → ℕ) (r : β → α → α → Prop) (B : β → ℝ), (∀ b, Equivalence (r b)) → (∀ x ∈ S, ∀ y ∈ S, (∀ b ∈ s, r b x y) → x = y) → (∀ b ∈ s, ∀ T : Finset α, (↑T : Set α) ⊆ S → (∀ x ∈ T, ∀ y ∈ T, ∀ b' ∈ s, lv b' < lv b → r b' x y) → (∀ x ∈ T, ∀ y ∈ T, r b x y → x = y) → (T.card : ℝ) ≤ B b) → S.Finite ∧ ((S.ncard : ℕ) : ℝ) ≤ ∏ b ∈ s, B b := by
  intro α β S s lv r B hr hinj hp
  have h : ∀ T : Finset α, (↑T : Set α) ⊆ S → (T.card : ℝ) ≤ ∏ b ∈ s, B b := fun T hT =>
    card_le_prod_of_separated_levels S lv r B hr s hp T hT
      fun x hx y hy => hinj x (hT hx) y (hT hy)
  have hS : S.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (∏ b ∈ s, B b)
    obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := h T hT
    rw [hc] at this
    linarith
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hS]
  exact h _ (by simp)

end GlobalTheory
end

