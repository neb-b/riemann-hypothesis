module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Development.AbelianVarietyTheory.Definitions.HermitianLattices.ExistsZsmulMemOfIsLattice

@[expose] public section

noncomputable section

namespace GlobalTheory

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.FD hiding cc_cc cc_sub cc_mul cc_one cc_zero cc_eq_zero
open ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_forall_trace_mul {K : Type} [Field K] [NumberField K] {t : K}
    (h : ∀ a : K, Algebra.trace ℚ K (a * t) = 0) : t = 0 :=
  (traceForm_nondegenerate ℚ K).1 t fun a => by rw [Algebra.traceForm_apply, mul_comm]; exact h a

theorem herm_single_single (G : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
  rw [herm_single_right]; simp

theorem herm_injective {G G' : Matrix (Fin r) (Fin r) E} (h : ∀ x y, herm G x y = herm G' x y) :
    G = G' := by
  ext a b
  rw [← herm_single_single G, h, herm_single_single]

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ G *ᵥ fun b => cc (y b) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem herm_mulVec {s : ℕ} (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin s) E)
    (x y : Fin s → E) : herm G (γ *ᵥ x) (γ *ᵥ y) = herm (γᵀ * G * γ.map cc) x y := by
  have h : (fun b => cc ((γ *ᵥ y) b)) = γ.map cc *ᵥ fun b => cc (y b) := by
    funext b
    simp [mulVec, dotProduct, cc_sum]
  rw [herm_eq_dotProduct, herm_eq_dotProduct, h, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec x, vecMul_transpose]

def IsConjAdj (B : LinearMap.BilinForm ℚ (Fin r → E)) : Prop :=
  ∀ (a : E) (x y : Fin r → E), B (a • x) y = B x (cc a • y)

theorem EFf_smul_eq_trace (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    EFf ξ0 G (a • x) y = Algebra.trace ℚ E (a * (-ξ0 * herm G x y)) := by
  rw [EFf, herm_smul_left, mul_left_comm]

theorem traceFormBilin_isConjAdj (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) : IsConjAdj (traceFormBilin ξ0 G) :=
  EFf_smul_left ξ0 G

theorem EFf_swap {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : EFf ξ0 G y x = -EFf ξ0 G x y := by
  rw [EFf, EFf, ← trace_cc, cc_mul, cc_neg, hξ, herm_conj G hG, ← map_neg]
  congr 1; ring

theorem EFf_self {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : EFf ξ0 G x x = 0 := by
  have := EFf_swap hξ hG x x
  linarith

theorem traceFormBilin_isAlt {ξ0 : E} (hξ : cc ξ0 = -ξ0) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) : (traceFormBilin ξ0 G).IsAlt :=
  EFf_self hξ hG

theorem herm_eq_of_EFf_smul {s : ℕ} {ξ0 : E} (h0 : ξ0 ≠ 0) {G : Matrix (Fin r) (Fin r) E}
    {G' : Matrix (Fin s) (Fin s) E} {x y : Fin r → E} {x' y' : Fin s → E}
    (h : ∀ a : E, EFf ξ0 G (a • x) y = EFf ξ0 G' (a • x') y') : herm G x y = herm G' x' y' := by
  have : -ξ0 * herm G x y - -ξ0 * herm G' x' y' = 0 :=
    eq_zero_of_forall_trace_mul fun a => by
      rw [mul_sub, map_sub, ← EFf_smul_eq_trace, ← EFf_smul_eq_trace, h, sub_self]
  exact mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)

theorem traceFormBilin_injective {ξ0 : E} (h0 : ξ0 ≠ 0) :
    Function.Injective (traceFormBilin ξ0 : Matrix (Fin r) (Fin r) E → _) := fun G G' h =>
  herm_injective fun x y => herm_eq_of_EFf_smul h0 fun a => by
    rw [← traceFormBilin_apply, ← traceFormBilin_apply, h]

theorem traceFormBilin_isAlt_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    (G : Matrix (Fin r) (Fin r) E) : (traceFormBilin ξ0 G).IsAlt ↔ ∀ a b, cc (G a b) = G b a := by
  refine ⟨fun h a b => ?_, traceFormBilin_isAlt hξ⟩
  have : -ξ0 * G b a - -ξ0 * cc (G a b) = 0 :=
    eq_zero_of_forall_trace_mul fun t => by
      have h1 := h.neg_eq (t • Pi.single b 1) (Pi.single a 1)
      have h2 : EFf ξ0 G (Pi.single a 1) (t • Pi.single b 1) =
          -Algebra.trace ℚ E (t * (-ξ0 * cc (G a b))) := by
        rw [EFf, herm_smul_right, herm_single_single, ← trace_cc, ← map_neg]
        simp only [cc_mul, cc_neg, cc_cc, hξ]
        congr 1; ring
      rw [traceFormBilin_apply, traceFormBilin_apply, EFf_smul_eq_trace, herm_single_single, h2] at h1
      rw [mul_sub, map_sub, neg_inj.mp h1, sub_self]
  exact (mul_left_cancel₀ (neg_ne_zero.mpr h0) (sub_eq_zero.mp this)).symm

theorem forall_EFf_eq_zero_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E)
    (x : Fin r → E) : (∀ y, EFf ξ0 G x y = 0) ↔ ∀ y, herm G x y = 0 := by
  refine ⟨fun h y => ?_, fun h y => by simp [EFf, h]⟩
  have : -ξ0 * herm G x y = 0 :=
    eq_zero_of_forall_trace_mul fun a => by rw [← EFf_smul_eq_trace, EFf_smul_left, h]
  exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr h0)

theorem traceFormBilin_separatingLeft_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).SeparatingLeft ↔ G.det ≠ 0 := by
  constructor
  · intro h hd
    obtain ⟨v, hv, hvG⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    refine hv (h v ((forall_EFf_eq_zero_iff h0 G v).mpr fun y => ?_))
    rw [herm_eq_dotProduct, dotProduct_mulVec, hvG, zero_dotProduct]
  · intro hd v hv
    exact eq_zero_of_herm G hd v ((forall_EFf_eq_zero_iff h0 G v).mp hv)

theorem traceFormBilin_nondegenerate_iff {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    (traceFormBilin ξ0 G).Nondegenerate ↔ G.det ≠ 0 := by
  rw [← traceFormBilin_separatingLeft_iff h0]
  exact ⟨fun h => h.1, LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft⟩

def traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) : K :=
  ((Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)).symm f

theorem trace_mul_traceRep {K : Type} [Field K] [NumberField K] (f : Module.Dual ℚ K) (a : K) :
    Algebra.trace ℚ K (a * traceRep f) = f a := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

def skewGram (ξ0 : E) (B : LinearMap.BilinForm ℚ (Fin r → E)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b =>
    (-ξ0)⁻¹ * traceRep (B.flip (Pi.single b 1) ∘ₗ LinearMap.single ℚ (fun _ : Fin r => E) a)


omit [IsCMField E] in
theorem trace_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) (B : LinearMap.BilinForm ℚ (Fin r → E))
    (a b : Fin r) (t : E) :
    Algebra.trace ℚ E (t * (-ξ0 * skewGram ξ0 B a b)) = B (Pi.single a t) (Pi.single b 1) := by
  rw [skewGram, Matrix.of_apply, mul_inv_cancel_left₀ (neg_ne_zero.mpr h0), trace_mul_traceRep]
  rfl

theorem IsConjAdj.ext {B B' : LinearMap.BilinForm ℚ (Fin r → E)} (h : IsConjAdj B)
    (h' : IsConjAdj B')
    (hh : ∀ a b t, B (Pi.single a t) (Pi.single b 1) = B' (Pi.single a t) (Pi.single b 1)) :
    B = B' := by
  have key : ∀ a b t u, B (Pi.single a t) (Pi.single b u) = B' (Pi.single a t) (Pi.single b u) := by
    intro a b t u
    have hu : (Pi.single b u : Fin r → E) = cc (cc u) • Pi.single b 1 := by
      rw [cc_cc, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hu, ← h, ← h', ← Pi.single_smul, hh]
  refine LinearMap.pi_ext fun a t => LinearMap.pi_ext fun b u => key a b t u

theorem traceFormBilin_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) : traceFormBilin ξ0 (skewGram ξ0 B) = B := by
  refine (traceFormBilin_isConjAdj _ _).ext hB fun a b t => ?_
  have ht : (Pi.single a t : Fin r → E) = t • Pi.single a 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [← trace_skewGram h0 B, traceFormBilin_apply, ht, EFf_smul_eq_trace, herm_single_single]

theorem EFf_skewGram {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) (x y : Fin r → E) : EFf ξ0 (skewGram ξ0 B) x y = B x y := by
  rw [← traceFormBilin_apply, traceFormBilin_skewGram h0 hB]

theorem skewGram_traceFormBilin {ξ0 : E} (h0 : ξ0 ≠ 0) (G : Matrix (Fin r) (Fin r) E) :
    skewGram ξ0 (traceFormBilin ξ0 G) = G :=
  traceFormBilin_injective h0 (traceFormBilin_skewGram h0 (traceFormBilin_isConjAdj ξ0 G))

theorem skewGram_herm {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {B : LinearMap.BilinForm ℚ (Fin r → E)} (hB : IsConjAdj B) (halt : B.IsAlt) (a b : Fin r) :
    cc (skewGram ξ0 B a b) = skewGram ξ0 B b a :=
  (traceFormBilin_isAlt_iff h0 hξ _).mp (by rwa [traceFormBilin_skewGram h0 hB]) a b

theorem skewGram_det_ne_zero_iff {ξ0 : E} (h0 : ξ0 ≠ 0) {B : LinearMap.BilinForm ℚ (Fin r → E)}
    (hB : IsConjAdj B) : (skewGram ξ0 B).det ≠ 0 ↔ B.Nondegenerate := by
  rw [← traceFormBilin_nondegenerate_iff h0, traceFormBilin_skewGram h0 hB]


section Integral

variable {M M' : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup M'] [Module (𝓞 E) M']

def IsIntConjAdj (E : Type) [Field E] [NumberField E] [IsCMField E] {M : Type} [AddCommGroup M]
    [Module (𝓞 E) M] (β : LinearMap.BilinForm ℤ M) : Prop :=
  ∀ (a : 𝓞 E) (x y : M), β (a • x) y = β x (IsCMField.ringOfIntegersComplexConj E a • y)

theorem coe_ringOfIntegersComplexConj (a : 𝓞 E) :
    ((IsCMField.ringOfIntegersComplexConj E a : 𝓞 E) : E) = cc (a : E) :=
  IsCMField.coe_ringOfIntegersComplexConj E a

namespace IsLatticeEmb

variable {φ : M →ₗ[𝓞 E] (Fin r → E)}

theorem extend_isConjAdj (h : IsLatticeEmb φ) {β : LinearMap.BilinForm ℤ M}
    (hβ : IsIntConjAdj E β) : IsConjAdj (h.extend β) := by
  intro a v w
  obtain ⟨m, hm, x, hx⟩ := h.exists_zsmul v
  obtain ⟨n, hn, y, hy⟩ := h.exists_zsmul w
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hint⟩ := halg.exists_integral_multiple
  let α : 𝓞 E := ⟨k • a, hint⟩
  have hα : (α : E) = k • a := rfl
  have h1 : φ (α • x) = k • m • a • v := by
    rw [map_smul, ← algebraMap_smul E α, hx, smul_comm m a v, ← smul_assoc k]; rfl
  have h2 : φ (IsCMField.ringOfIntegersComplexConj E α • y) = k • n • cc a • w := by
    rw [map_smul, ← algebraMap_smul E (IsCMField.ringOfIntegersComplexConj E α), hy,
      smul_comm n (cc a) w, ← smul_assoc k]
    congr 1
    change ((IsCMField.ringOfIntegersComplexConj E α : 𝓞 E) : E) = _
    rw [coe_ringOfIntegersComplexConj, hα, zsmul_eq_mul, zsmul_eq_mul, cc_mul, cc_intCast]
  have h3 : h.extend β (φ (α • x)) (φ y) =
      h.extend β (φ x) (φ (IsCMField.ringOfIntegersComplexConj E α • y)) := by
    rw [extend_apply, extend_apply, hβ]
  simp only [h1, h2, hx, hy, map_zsmul, LinearMap.smul_apply] at h3
  rw [smul_comm k n] at h3
  exact smul_right_injective ℚ hm (smul_right_injective ℚ hk (smul_right_injective ℚ hn h3))

def gram (h : IsLatticeEmb φ) (ξ0 : E) (β : LinearMap.BilinForm ℤ M) : Matrix (Fin r) (Fin r) E :=
  skewGram ξ0 (h.extend β)

theorem EFf_gram (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    (hβ : IsIntConjAdj E β) (x y : M) : EFf ξ0 (h.gram ξ0 β) (φ x) (φ y) = β x y := by
  rw [gram, EFf_skewGram h0 (h.extend_isConjAdj hβ), extend_apply]

theorem eq_gram (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    G = h.gram ξ0 β := by
  have : h.extend β = traceFormBilin ξ0 G := h.bilin_ext fun x y => by rw [extend_apply, traceFormBilin_apply, hG]
  rw [gram, this, skewGram_traceFormBilin h0]

theorem gram_herm (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0)
    {β : LinearMap.BilinForm ℤ M} (hβ : IsIntConjAdj E β) (halt : ∀ x, β x x = 0) (a b : Fin r) :
    cc (h.gram ξ0 β a b) = h.gram ξ0 β b a :=
  skewGram_herm h0 hξ (h.extend_isConjAdj hβ) (h.extend_isAlt halt) a b

theorem gram_det_ne_zero_iff (h : IsLatticeEmb φ) {ξ0 : E} (h0 : ξ0 ≠ 0)
    {β : LinearMap.BilinForm ℤ M} (hβ : IsIntConjAdj E β) :
    (h.gram ξ0 β).det ≠ 0 ↔ Function.Injective β := by
  rw [gram, skewGram_det_ne_zero_iff h0 (h.extend_isConjAdj hβ), extend_nondegenerate_iff]

theorem EF_int_of_eq {ξ0 : E} {β : LinearMap.BilinForm ℤ M} {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ, ∃ k : ℤ, EFf ξ0 G x y = k := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact ⟨β x y, hG x y⟩

theorem EF_perf_iff (h : IsLatticeEmb φ) {ξ0 : E} {β : LinearMap.BilinForm ℤ M}
    {G : Matrix (Fin r) (Fin r) E} (hG : ∀ x y, EFf ξ0 G (φ x) (φ y) = β x y) :
    (∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
      (f y : ℚ) = EFf ξ0 G x y) ↔ Function.Surjective β := by
  let e := LinearEquiv.ofInjective φ h.1
  have he : ∀ x, ((e x : LinearMap.range φ) : Fin r → E) = φ x := fun x => rfl
  constructor
  · intro hp f
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hp (f.toAddMonoidHom.comp e.symm.toAddEquiv.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => ?_⟩
    have := hx (e y)
    rw [he, hG] at this
    simpa using this.symm
  · intro hs f
    obtain ⟨x, hx⟩ := hs (f.comp e.toAddEquiv.toAddMonoidHom).toIntLinearMap
    refine ⟨φ x, ⟨x, rfl⟩, fun y => ?_⟩
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [he, hG, hx]
    rfl

end IsLatticeEmb

def latticeEF (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k) : LinearMap.BilinForm ℤ Λ :=
  have key : ∀ x y : Λ, (((EFf ξ0 G x y).num : ℤ) : ℚ) = traceFormBilin ξ0 G x y := fun x y => by
    obtain ⟨k, hk⟩ := hint x x.2 y y.2
    rw [traceFormBilin_apply, hk, Rat.num_intCast]
  LinearMap.mk₂ ℤ (fun x y => (EFf ξ0 G x y).num)
    (fun x x' y => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add (f := _), LinearMap.add_apply]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        LinearMap.smul_apply, zsmul_eq_mul]))
    (fun x y y' => Int.cast_injective (α := ℚ) (by
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add (f := _)]))
    (fun n x y => Int.cast_injective (α := ℚ) (by
      rw [smul_eq_mul, Int.cast_mul, key, key, Submodule.coe_smul_of_tower, map_zsmul,
        zsmul_eq_mul]))

section LatticeEF

variable {ξ0 : E} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
  (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 G x y = k)

theorem latticeEF_apply (x y : Λ) : ((latticeEF ξ0 G Λ hint x y : ℤ) : ℚ) = EFf ξ0 G x y := by
  obtain ⟨k, hk⟩ := hint x x.2 y y.2
  change (((EFf ξ0 G x y).num : ℤ) : ℚ) = _
  rw [hk, Rat.num_intCast]

theorem latticeEF_isIntConjAdj : IsIntConjAdj E (latticeEF ξ0 G Λ hint) := fun a x y =>
  Int.cast_injective (α := ℚ) (by
    rw [latticeEF_apply, latticeEF_apply, Submodule.coe_smul, Submodule.coe_smul,
      ← algebraMap_smul E a, ← algebraMap_smul E (IsCMField.ringOfIntegersComplexConj E a),
      EFf_smul_left, ← coe_ringOfIntegersComplexConj])

theorem gram_latticeEF (hΛ : IsLattice Λ) (h0 : ξ0 ≠ 0) :
    (isLatticeEmb_subtype hΛ).gram ξ0 (latticeEF ξ0 G Λ hint) = G :=
  ((isLatticeEmb_subtype hΛ).eq_gram h0 fun x y => (latticeEF_apply hint x y).symm).symm

theorem latticeEF_bijective_iff (hΛ : IsLattice Λ) (h0 : ξ0 ≠ 0) :
    Function.Bijective (latticeEF ξ0 G Λ hint) ↔
      G.det ≠ 0 ∧ ∀ f : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (f y : ℚ) = EFf ξ0 G x y := by
  have h := isLatticeEmb_subtype hΛ
  have h1 := h.gram_det_ne_zero_iff h0 (latticeEF_isIntConjAdj hint)
  rw [gram_latticeEF hint hΛ h0] at h1
  have h2 := h.EF_perf_iff (ξ0 := ξ0) (G := G) fun x y => (latticeEF_apply hint x y).symm
  rw [Submodule.range_subtype] at h2
  rw [h1, h2]
  rfl

end LatticeEF

end Integral

section Datum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {H : Host E}

theorem host_bar_eq (H : Host E) (a : 𝓞 E) : H.bar a = IsCMField.ringOfIntegersComplexConj E a :=
  RingOfIntegers.ext (H.bar_eq a)

theorem datum_isIntConjAdj (D : Datum H) : IsIntConjAdj E D.EF := fun a x y => by
  rw [D.adj, host_bar_eq]

theorem datum_exists_isLatticeEmb (D : Datum H) :
    ∃ φ : D.La →ₗ[𝓞 E] (Fin (D.p + D.q) → E), IsLatticeEmb φ := by
  have := D.fin
  have := D.proj
  exact exists_isLatticeEmb D.rank

theorem datum_gram_spec (D : Datum H) {φ : D.La →ₗ[𝓞 E] (Fin r → E)} (h : IsLatticeEmb φ)
    {ξ0 : E} (h0 : ξ0 ≠ 0) (hξ : cc ξ0 = -ξ0) :
    (∀ a b, cc (h.gram ξ0 D.EF a b) = h.gram ξ0 D.EF b a) ∧ (h.gram ξ0 D.EF).det ≠ 0 ∧
      (∀ x y, EFf ξ0 (h.gram ξ0 D.EF) (φ x) (φ y) = D.EF x y) ∧
      (∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
        ∃ k : ℤ, EFf ξ0 (h.gram ξ0 D.EF) x y = k) ∧
      ∀ f : LinearMap.range φ →+ ℤ, ∃ x ∈ LinearMap.range φ, ∀ y : LinearMap.range φ,
        (f y : ℚ) = EFf ξ0 (h.gram ξ0 D.EF) x y :=
  have hβ := datum_isIntConjAdj D
  ⟨h.gram_herm h0 hξ hβ D.alt, (h.gram_det_ne_zero_iff h0 hβ).mpr D.unimod.1, h.EFf_gram h0 hβ,
    IsLatticeEmb.EF_int_of_eq (h.EFf_gram h0 hβ),
    (h.EF_perf_iff (h.EFf_gram h0 hβ)).mpr D.unimod.2⟩

section
variable (D : Datum H) {ξ0 : E}

end

end Datum

namespace SkewModel

namespace ConjDual

end ConjDual

end SkewModel

end GlobalTheory
