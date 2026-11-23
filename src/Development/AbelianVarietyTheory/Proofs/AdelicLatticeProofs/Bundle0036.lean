module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormalFormNonsquareAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLocalNonnormOfNonsquareAdicCompletion
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem exists_even_valuation_of_mul_sq_eq_norm {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (Δ y s p q : K)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hs : s ≠ 0) (hy : y ≠ 0)
    (h : y * s ^ 2 = p ^ 2 - Δ * q ^ 2) : ∃ n : ℤ, w y = WithZero.exp (2 * n) := by
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_self,
      mul_eq_zero, pow_eq_zero_iff] at h
    tauto
  obtain ⟨n, hn⟩ := hΔ p q hpq
  rw [← h, map_mul, map_pow] at hn
  have hws : w s = WithZero.exp (w s).log :=
    (WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hs)).symm
  rw [hws, ← WithZero.exp_nsmul] at hn
  refine ⟨n - (w s).log, ?_⟩
  have key : w y = WithZero.exp (2 * n) * WithZero.exp (-(2 • (w s).log)) := by
    rw [← hn, mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one]
  rw [key, ← WithZero.exp_add]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

open NumberField IsDedekindDomain in
open scoped WithZero in
private theorem not_norm_of_odd_valuation_of_norm_mul {K : Type} [Field K]
    (w : Valuation K (WithZero (Multiplicative ℤ))) (δ Δ y c d : K) (hδ : δ ≠ 0)
    (hΔ : _root_.GlobalTheory.QNorm.EvenNorms w Δ) (hy : y ≠ 0)
    (hodd : ∀ n : ℤ, w y ≠ WithZero.exp (2 * n)) (hc : y = c ^ 2 - δ * Δ * d ^ 2) :
    ¬ ∃ a b : K, y = a ^ 2 - δ * b ^ 2 := by
  rintro ⟨a, b, hab⟩
  have main : ∀ e : K, e ^ 2 = c ^ 2 → a + e ≠ 0 → False := by
    intro e he hs
    have hc2 : y = e ^ 2 - δ * Δ * d ^ 2 := by rw [he]; exact hc
    obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y (a + e) (a * e + y) (δ * b * d)
      hΔ hs hy (by linear_combination (e ^ 2 - y) * hab + δ * b ^ 2 * hc2)
    exact hodd n hn
  by_cases h1 : a + c = 0
  · by_cases h2 : a + -c = 0
    · have hca : c = -a := by linear_combination h1
      have hb : δ * b ^ 2 = δ * (Δ * d ^ 2) := by
        rw [hca] at hc
        linear_combination hab - hc
      have hb' : b ^ 2 = Δ * d ^ 2 := mul_left_cancel₀ hδ hb
      by_cases hd : d = 0
      · rw [hd] at hb'
        have hb0 : b = 0 := by simpa using hb'
        rw [hb0] at hab
        obtain ⟨n, hn⟩ := exists_even_valuation_of_mul_sq_eq_norm w Δ y 1 a 0 hΔ one_ne_zero hy
          (by rw [hab]; ring)
        exact hodd n hn
      · obtain ⟨n, hn⟩ := hΔ (b / d) 1 (Or.inr one_ne_zero)
        have hz : (b / d) ^ 2 - Δ * 1 ^ 2 = 0 := by
          rw [div_pow, hb']
          field_simp
          ring
        rw [hz, map_zero] at hn
        exact WithZero.exp_ne_zero hn.symm
    · exact main (-c) (by ring) h2
  · exact main c rfl h1


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.exists_local_nonnorm : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (δ : v.adicCompletion F), δ ≠ 0 → ¬ IsSquare δ →
    ∃ x : v.adicCompletion F, x ≠ 0 ∧ ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * b ^ 2 := by
  intro F _ _ v δ hδ hns
  obtain ⟨c, hc0, hcases⟩ := _root_.GlobalTheory.QNorm.exists_normal_form_of_not_isSquare F v δ hδ hns
  have hδ' : δ * c ^ 2 ≠ 0 := mul_ne_zero hδ (pow_ne_zero 2 hc0)
  suffices h : ∃ x : v.adicCompletion F, x ≠ 0 ∧
      ¬ ∃ a b : v.adicCompletion F, x = a ^ 2 - δ * c ^ 2 * b ^ 2 by
    obtain ⟨x, hx0, hx⟩ := h
    refine ⟨x, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    refine hx ⟨a, b / c, ?_⟩
    rw [hab]
    field_simp
  obtain ⟨Δ, hΔ, hΔ1, hΔ4⟩ := _root_.GlobalTheory.QNorm.exists_evenNorms_unit F v
  have hΔ0 : Δ ≠ 0 := by
    intro h
    rw [h, map_zero] at hΔ1
    exact zero_ne_one hΔ1
  rcases hcases with ⟨n, hn⟩ | ⟨h1, h4, n, hn⟩ | hE
  · refine ⟨-(δ * c ^ 2 * Δ), neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0),
      not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 0 1 hδ' hΔ
        (neg_ne_zero.mpr (mul_ne_zero hδ' hΔ0)) ?_ (by ring)⟩
    intro m hm
    rw [Valuation.map_neg, map_mul, hn, hΔ1, mul_one, WithZero.exp_inj] at hm
    omega
  · have hy : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ =
        -((δ * c ^ 2 - 1) + δ * c ^ 2 * (Δ - 1)) := by
      ring
    have hwy : Valued.v ((1 : v.adicCompletion F) - δ * c ^ 2 * Δ) =
        WithZero.exp (2 * n + 1) := by
      rw [hy, Valuation.map_neg, Valuation.map_add_eq_of_lt_left _
        (by rw [map_mul, h1, one_mul]; exact lt_of_le_of_lt hΔ4 h4), hn]
    have hy0 : (1 : v.adicCompletion F) - δ * c ^ 2 * Δ ≠ 0 := by
      intro h
      rw [h, map_zero] at hwy
      exact WithZero.exp_ne_zero hwy.symm
    refine ⟨_, hy0, not_norm_of_odd_valuation_of_norm_mul Valued.v (δ * c ^ 2) Δ _ 1 1 hδ' hΔ hy0 ?_
      (by ring)⟩
    intro m hm
    rw [hwy, WithZero.exp_inj] at hm
    omega
  · obtain ⟨⟨π, -, hπ⟩, -⟩ := _root_.GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives F v
    have hx0 : algebraMap F (v.adicCompletion F) π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    refine ⟨_, hx0, ?_⟩
    rintro ⟨a, b, hab⟩
    have hab' : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      rw [h.1, h.2] at hab
      apply hx0
      rw [hab]
      ring
    obtain ⟨m, hm⟩ := hE a b hab'
    rw [← hab, hπ, WithZero.exp_inj] at hm
    omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevel
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem ..)

theorem exists_nat_smul_map_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, (d : E) • φ v ∈ L := by
  classical
  choose d hd hdL using exists_nat_smul_mem_of_span L hL
  obtain ⟨S, hS⟩ := hfg
  refine ⟨∏ s ∈ S, d (φ s), Finset.prod_pos fun s _ => hd _, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul S _ (Finset.mem_coe.1 hx), Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul E (∏ s ∈ S.erase x, d (φ s))]
    exact L.toAddSubmonoid.nsmul_mem (hdL _) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    have h1 : φ (a • x) = (a : E) • φ x := φ.map_smul (a : E) x
    rw [h1, smul_comm]
    exact L.smul_mem a hx

theorem exists_refl_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    _root_.GlobalTheory.UnRep.normOne_approx F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspace
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_of_stable (ι : Type) [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (ι → ℂ))
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) :
    ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  classical

  obtain ⟨Wq, hWq⟩ : ∃ Wq : Submodule ℚ (ι → ℚ),
      ∀ q, q ∈ Wq ↔ (fun i => algebraMap ℚ ℂ (q i)) ∈ W := by
    refine ⟨{ carrier := {q | (fun i => algebraMap ℚ ℂ (q i)) ∈ W}
              add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun q => Iff.rfl⟩
    · intro a b ha hb
      have h : (fun i => algebraMap ℚ ℂ ((a + b) i))
          = (fun i => algebraMap ℚ ℂ (a i)) + (fun i => algebraMap ℚ ℂ (b i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((a + b) i)) ∈ W
      rw [h]; exact W.add_mem ha hb
    · show (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) ∈ W
      have h : (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) = 0 := by ext i; simp
      rw [h]; exact W.zero_mem
    · intro c q hq
      have h : (fun i => algebraMap ℚ ℂ ((c • q) i))
          = algebraMap ℚ ℂ c • (fun i => algebraMap ℚ ℂ (q i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((c • q) i)) ∈ W
      rw [h]; exact W.smul_mem _ hq

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Wq
  obtain ⟨f, hf1, hf2⟩ : ∃ f : (ι → ℚ) →ₗ[ℚ] (ι → ℚ), (∀ q, f q ∈ Wq) ∧ (∀ q ∈ Wq, f q = q) :=
    ⟨Wq.subtype ∘ₗ Wq.projectionOnto C hC, fun q => (Wq.projectionOnto C hC q).2,
      fun q hq => congrArg Subtype.val (Submodule.projectionOnto_apply_left hC ⟨q, hq⟩)⟩
  have hff : f ∘ₗ f = f := LinearMap.ext fun q => hf2 _ (hf1 q)

  have hstable := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational (ι → ℂ) ι (Pi.basisFun ℂ ι) W
    (fun σ w hw => ⟨fun i => σ (w i), hW σ w hw, fun k => by simp⟩)
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hff]

  have hA : ∀ q : ι → ℚ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => algebraMap ℚ ℂ (q i)) = fun i => algebraMap ℚ ℂ (f q i) := by
    intro q
    ext i
    rw [← LinearMap.toMatrix'_mulVec f q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

  have hB : ∀ v : ι → ℂ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v ∈ W := by
    intro v
    have hcol : ∀ j, (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) ∈ W := by
      intro j
      simp only [LinearMap.toMatrix'_apply]
      exact (hWq _).1 (hf1 _)
    have h : (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v
        = ∑ j, v j • (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcol j)
  intro v
  constructor
  · intro hv
    have hspan := hstable hv
    clear hv
    induction hspan using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨hwW, hq⟩ := hw
      choose q hq using hq
      have hw : w = fun i => algebraMap ℚ ℂ (q i) := by
        ext k
        rw [← Pi.basisFun_repr ℂ ι w k, hq k]
        exact (eq_ratCast (algebraMap ℚ ℂ) (q k)).symm
      have hqW : q ∈ Wq := (hWq q).2 (by rw [← hw]; exact hwW)
      rw [hw, hA, hf2 q hqW]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  · intro hv
    rw [← hv]
    exact hB v

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatProjectorOfAutStableMatrices
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatProj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def entryEquiv (ι : Type) : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) where
  toFun X := fun kl => X kl.1 kl.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_entry (w : Matrix ι ι ℂ) (k : ι × ι) :
    (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = w k.1 k.2 := by
  rw [Module.Basis.ofEquivFun_repr_apply]; rfl

noncomputable def castLin (ι : Type) : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℂ where
  toFun X := X.map (algebraMap ℚ ℂ)
  map_add' X Y := by ext i j; simp
  map_smul' q X := by ext i j; simp [Rat.smul_def]

noncomputable def linExtLin (c : ι × ι → ι × ι → ℚ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := linExt c X
  map_add' X Y := by ext i j; simp [linExt, mul_add, Finset.sum_add_distrib]
  map_smul' a X := by ext i j; simp [linExt, Finset.mul_sum, mul_left_comm]

theorem linExt_eq_sum (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (X : Matrix ι ι ℂ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) X =
      ∑ kl : ι × ι, X kl.1 kl.2 • castLin ι (p (single kl.1 kl.2 1)) := by
  ext i j
  simp [linExt, castLin, Matrix.sum_apply, mul_comm]

theorem linExt_cast (p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ) (Y : Matrix ι ι ℚ) :
    linExt (fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (castLin ι Y) = castLin ι (p Y) := by
  rw [linExt_eq_sum]
  have hY : Y = ∑ kl : ι × ι, Y kl.1 kl.2 • single kl.1 kl.2 (1 : ℚ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    rw [Fintype.sum_prod_type]
    simp [Matrix.smul_single]
  conv_rhs => rw [hY]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [map_smul, map_smul]
  ext i j
  simp [castLin, Rat.smul_def]

theorem exists_rat_projector : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Submodule ℂ (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ x ∈ E, x.map σ ∈ E) → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, linExt c X ∈ E) ∧ ∀ x ∈ E, linExt c x = x := by
  intro ι _ _ E hE
  let E₀ : Submodule ℚ (Matrix ι ι ℚ) := (E.restrictScalars ℚ).comap (castLin ι)
  obtain ⟨π, hπ⟩ : ∃ π : Matrix ι ι ℚ →ₗ[ℚ] E₀, ∀ x : E₀, π x = x := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective E₀.subtype E₀.ker_subtype
    exact ⟨g, fun x => LinearMap.congr_fun hg x⟩
  let p : Matrix ι ι ℚ →ₗ[ℚ] Matrix ι ι ℚ := E₀.subtype ∘ₗ π
  refine ⟨fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2, fun X => ?_, fun x hx => ?_⟩
  · rw [linExt_eq_sum]
    exact E.sum_mem fun kl _ => E.smul_mem _ (π (single kl.1 kl.2 1)).2
  · have hd := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational (Matrix ι ι ℂ) (ι × ι) (Module.Basis.ofEquivFun (entryEquiv ι)) E
      (fun σ w hw => ⟨w.map σ, hE σ w hw, fun k => by
        rw [repr_entry, repr_entry]; rfl⟩) hx
    have key : Set.EqOn (linExtLin fun ij kl => p (single kl.1 kl.2 1) ij.1 ij.2) (LinearMap.id (R := ℂ))
        {w | w ∈ E ∧ ∀ k, ∃ q : ℚ, (Module.Basis.ofEquivFun (entryEquiv ι)).repr w k = q} := by
      rintro w ⟨hw, hq⟩
      choose q hq using hq
      have hwq : w = castLin ι (Matrix.of fun i j => q (i, j)) := by
        ext i j
        have := hq (i, j)
        rw [repr_entry] at this
        simpa [castLin] using this
      have hmem : (Matrix.of fun i j => q (i, j)) ∈ E₀ := by
        change castLin ι _ ∈ E
        rw [← hwq]; exact hw
      have h1 : p (Matrix.of fun i j => q (i, j)) = Matrix.of fun i j => q (i, j) :=
        congrArg Subtype.val (hπ ⟨_, hmem⟩)
      have h2 := linExt_cast p (Matrix.of fun i j => q (i, j))
      rw [h1, ← hwq] at h2
      exact h2
    exact LinearMap.eqOn_span key hd

end GlobalTheory.ClassFin.RatProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummer
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem hilbert90_sUnits_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  classical
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE hadm hδ u hu hN
  obtain ⟨hfd, -, hgal, -, hgen, -⟩ := kummer_galois p F E ζ δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := (_root_.GlobalTheory.CNorm.kummer_basic p F E ζ δ θ σ hq).2.2.2.2.1 (u : E) hN
  obtain ⟨hact, htrans⟩ := galois_places_transitive F E
  rw [mem_sUnits] at hu
  have hval : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀, div_eq_one_iff_eq (by simpa only [ne_eq, map_eq_zero] using hy0)] at h1
    exact h1
  have hpow : ∀ (k : ℕ) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E ((σ ^ k) y) = w.valuation E y := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨w', hw', hv'⟩ := hact (σ ^ k) w
      have hw'' : w' ∉ SE := fun h => hw ((hSE w).2 (hw' ▸ (hSE w').1 h))
      rw [pow_succ, AlgEquiv.mul_apply, ← hv', hval w' hw'', hv', ih]
  have hall : ∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E (τ y) = w.valuation E y := by
    intro τ w hw
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hgen τ)
    exact hpow k w hw
  choose up hup using (places_over F E).2.1
  obtain ⟨T, -, hT⟩ := exists_superset_mem_sUnits E {Units.mk0 y hy0} ∅
  have hT' := (mem_sUnits E T _).1 (hT T subset_rfl _ (Finset.mem_singleton_self _))
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S (T.image fun w => w.under (𝓞 F))
    (fun v => -WithZero.log ((up v).valuation E y)) hadm.1 (by
      intro v hv
      have : up v ∉ T := fun h => hv (Finset.mem_image.2 ⟨_, h, hup v⟩)
      have h2 : (up v).valuation E y = 1 := hT' _ this
      simp [h2])
  have ha0 : algebraMap F E (a : F) ≠ 0 := by simp
  refine ⟨Units.mk0 (algebraMap F E a * y) (mul_ne_zero ha0 hy0), ?_, ?_⟩
  · rw [mem_sUnits]
    intro w hw
    have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
    have h3 : (up (w.under (𝓞 F))).valuation E y = w.valuation E y := by
      obtain ⟨τ, hτ⟩ := htrans w (up (w.under (𝓞 F))) (hup _)
      rw [hτ, hall τ w hw]
    have h4 : w.valuation E y ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hy0
    rw [Units.val_mk0, map_mul,
      _root_.GlobalTheory.CNorm.kummer_valuation_unramified p F E ζ δ θ σ hq w (hadm.2 _ hv) (hδ _ hv), ha _ hv]
    simp only [h3]
    rw [WithZero.exp_neg, WithZero.exp_log h4, inv_mul_cancel₀ h4]
  · rw [Units.val_mk0, map_mul, AlgEquiv.commutes, hy, mul_div_mul_left _ _ ha0]

end GlobalTheory.CNorm
end

