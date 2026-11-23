module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardInfinitePlaceLeQuadratic
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_real_eq_pos_add_tReal (F : Type) [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    Nat.card (F →+* ℝ) = Nat.card {φ : F →+* ℝ // 0 < φ δ} + tReal F δ := by
  classical
  have h := Set.ncard_add_ncard_compl {φ : F →+* ℝ | 0 < φ δ}
  have hc : {φ : F →+* ℝ | 0 < φ δ}ᶜ = {φ : F →+* ℝ | φ δ < 0} := by
    ext φ
    have : φ δ ≠ 0 := by simpa using hδ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun a => lt_of_le_of_ne a this, le_of_lt⟩
  rw [hc] at h
  rw [← h]
  rfl

theorem two_mul_card_pos_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (h : IsQuad δ θ σ) :
    2 * Nat.card {φ : F →+* ℝ // 0 < φ δ} ≤ Nat.card (E →+* ℝ) := by
  classical
  have hext := (_root_.GlobalTheory.QNorm.isQuad_galois_and_embedding F E δ θ σ h).2.2 ℝ
  have key : ∀ p : Bool × {φ : F →+* ℝ // 0 < φ δ}, ∃ ψ : E →+* ℝ,
      (∀ a : F, ψ (algebraMap F E a) = p.2.1 a) ∧ (0 < ψ θ ↔ p.1 = true) := by
    rintro ⟨b, φ, hφ⟩
    have hs : 0 < Real.sqrt (φ δ) := Real.sqrt_pos.mpr hφ
    cases b
    · obtain ⟨ψ, h1, h2⟩ := hext φ (-Real.sqrt (φ δ)) (by rw [neg_sq, Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simp only [Bool.false_eq_true, iff_false, not_lt]
      linarith
    · obtain ⟨ψ, h1, h2⟩ := hext φ (Real.sqrt (φ δ)) (by rw [Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simpa using hφ
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p q hpq
    refine Prod.ext ?_ (Subtype.ext (RingHom.ext fun a => ?_))
    · have := (hf2 p).symm.trans (hpq ▸ hf2 q)
      exact Bool.eq_iff_iff.mpr this
    · rw [← hf1 p a, ← hf1 q a, hpq]
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this

theorem two_mul_card_infinitePlace_le :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F)
      (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ →
      2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  intro F E _ _ _ _ _ δ θ σ h
  have hδ : δ ≠ 0 := fun h0 => h.nonsq (h0 ▸ IsSquare.zero)
  have h1 := card_real_eq_pos_add_tReal F δ hδ
  have h2 := two_mul_card_pos_le F E δ θ σ h
  rw [_root_.GlobalTheory.QNorm.card_ringHom_real_eq_nrRealPlaces] at h1 h2
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h4 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : Module.finrank F E = 2 := (_root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ h).2.2.2.2.2.2
  have h8 := Module.finrank_mul_finrank ℚ F E
  rw [h7] at h8
  omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflLaws

variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot (v x : Fin n → E) :
    _root_.GlobalTheory.UnRep.hermE c G v x = (G *ᵥ fun b => c (x b)) ⬝ᵥ v := by
  unfold _root_.GlobalTheory.UnRep.hermE
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec (x : Fin n → E) (u : E) (v : Fin n → E) :
    _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x := by
  unfold _root_.GlobalTheory.UnRep.refl
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  congr 1
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    _root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot]
  ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_add_smul_left' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G (v + t • x) y =
      _root_.GlobalTheory.UnRep.hermE c G v y + t * _root_.GlobalTheory.UnRep.hermE c G x y := by
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, dotProduct_add, dotProduct_smul,
    smul_eq_mul]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_conj_eq_swap_of_involutive_of_conj_symm (hinv : ∀ z : E, c (c z) = z) (hG : ∀ a b, c (G a b) = G b a)
    (a b : Fin n → E) :
    c (_root_.GlobalTheory.UnRep.hermE c G a b) = _root_.GlobalTheory.UnRep.hermE c G b a := by
  unfold _root_.GlobalTheory.UnRep.hermE
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hinv, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_add_smul_right' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G v (y + t • x) =
      _root_.GlobalTheory.UnRep.hermE c G v y + c t * _root_.GlobalTheory.UnRep.hermE c G v x := by
  have hfun : (fun b => c ((y + t • x) b)) = (fun b => c (y b)) + c t • fun b => c (x b) := by
    funext b
    simp [map_add (f := _), map_mul]
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, hfun, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
theorem _root_.GlobalTheory.UnRep.ReflLaws.refl_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E),
    _root_.GlobalTheory.UnRep.IsHermForm c G → ∀ x : Fin n → E,
    _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 →
    (∀ u v, _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x) ∧
    _root_.GlobalTheory.UnRep.refl c G x 1 = 1 ∧
    (∀ u u', _root_.GlobalTheory.UnRep.refl c G x u * _root_.GlobalTheory.UnRep.refl c G x u' =
      _root_.GlobalTheory.UnRep.refl c G x (u * u')) ∧
    ∀ u, u * c u = 1 → _root_.GlobalTheory.UnRep.IsUnE c G (_root_.GlobalTheory.UnRep.refl c G x u) := by
  intro F E _ _ _ _ _ c n G hG x hx
  obtain ⟨hinv, -, hsym, -⟩ := hG
  refine ⟨_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec c G x, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UnRep.refl
    simp
  · intro u u'
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
      hermE_add_smul_left']
    rw [add_assoc, ← add_smul]
    congr 2
    field_simp
    ring
  · intro u hu
    unfold _root_.GlobalTheory.UnRep.IsUnE
    intro v y
    have hxx : c (_root_.GlobalTheory.UnRep.hermE c G x x) = _root_.GlobalTheory.UnRep.hermE c G x x :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym x x
    have hyx : c (_root_.GlobalTheory.UnRep.hermE c G y x) = _root_.GlobalTheory.UnRep.hermE c G x y :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym y x
    simp only [_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec, hermE_add_smul_left', hermE_add_smul_right',
      map_div₀, map_mul, map_sub, map_one, hxx, hyx]
    field_simp
    linear_combination (_root_.GlobalTheory.UnRep.hermE c G v x * _root_.GlobalTheory.UnRep.hermE c G x y *
      1) * hu

end GlobalTheory.UnRep.ReflLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAway
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

theorem tvGen_adjust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ m ∈ TvGen (c : E →+* E) G, ∀ b : ℕ, 0 < b → ∀ N : ℕ, ∃ m' ∈ TvGen (c : E →+* E) G, ∃ k e : ℕ, k.Coprime b ∧ ∀ v ∈ L, (∃ w ∈ L, k • (m' *ᵥ v - m *ᵥ v) = b ^ N • w) ∧ b ^ e • (m' *ᵥ v) ∈ L ∧ b ^ e • (m'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG L hL hsp m hm b hb
  induction hm using Submonoid.closure_induction with
  | mem m hm =>
    intro N
    obtain ⟨x, t, hx, ht, rfl⟩ := hm
    obtain ⟨t', k, e, ht', hk, H⟩ := _root_.GlobalTheory.TvAdjust.exists_tv_adjust F E c n G hFE hG L hL hsp x t (b ^ (N + 1)) (by positivity) ht
    have hinv : (tv (c : E →+* E) G x t')⁻¹ = tv (c : E →+* E) G x (-t') := by
      apply Matrix.inv_eq_right_inv
      rw [(_root_.GlobalTheory.UTrans.Calc.calculus E n (c : E →+* E) G hG.invol hG.herm).2.2.1, hx]
      ext i j
      simp [tv]
    refine ⟨_, Submonoid.subset_closure ⟨x, t', hx, ht', rfl⟩, k, (N + 1) * e,
      (Nat.coprime_pow_right_iff (Nat.succ_pos N) _ _).1 hk, fun v hv => ?_⟩
    obtain ⟨⟨w, hw, h1⟩, h2, h3⟩ := H v hv
    refine ⟨⟨b • w, L.smul_of_tower_mem _ hw, ?_⟩, ?_, ?_⟩
    · rw [h1, smul_smul, pow_succ]
    · rwa [pow_mul]
    · rwa [pow_mul, hinv]
  | one =>
    intro N
    refine ⟨1, one_mem _, 1, 0, by simp, fun v hv => ⟨⟨0, zero_mem _, by simp⟩, ?_, ?_⟩⟩ <;> simpa using hv
  | mul m₁ m₂ _ _ ih₁ ih₂ =>
    intro N
    obtain ⟨p, -, k₀, e₀, hk₀, H₀⟩ := ih₁ 0
    have hden : ∀ v ∈ L, (k₀ * b ^ e₀) • (m₁ *ᵥ v) ∈ L := by
      intro v hv
      obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
      have : (k₀ * b ^ e₀) • (m₁ *ᵥ v) = k₀ • b ^ e₀ • (p *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
        rw [← h1]; module
      rw [this]
      exact sub_mem (L.smul_of_tower_mem _ h2) (L.smul_of_tower_mem _ (L.smul_of_tower_mem _ hw))
    obtain ⟨q₂, hq₂, k₂, e₂, hk₂, H₂⟩ := ih₂ (N + e₀)
    obtain ⟨q₁, hq₁, k₁, e₁, hk₁, H₁⟩ := ih₁ (N + e₂)
    refine ⟨q₁ * q₂, mul_mem hq₁ hq₂, k₀ * k₁ * k₂, e₁ + e₂,
      Nat.Coprime.mul_left (Nat.Coprime.mul_left hk₀ hk₁) hk₂, fun v hv => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨w₂, hw₂, a1⟩, a2, -⟩ := H₂ v hv
      obtain ⟨⟨w₁, hw₁, b1⟩, -, -⟩ := H₁ _ a2
      have hb' : ((b : E) ^ e₂) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hb.ne')
      have b2 : k₁ • (q₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (q₂ *ᵥ v)) = b ^ N • w₁ := by
        apply smul_right_injective (Fin n → E) hb'
        simp only [Matrix.mulVec_smul] at b1
        linear_combination (norm := module) b1
      have a3 : k₂ • (m₁ *ᵥ (q₂ *ᵥ v) - m₁ *ᵥ (m₂ *ᵥ v)) = b ^ (N + e₀) • (m₁ *ᵥ w₂) := by
        rw [← Matrix.mulVec_smul, ← a1, Matrix.mulVec_smul, Matrix.mulVec_sub]
      refine ⟨(k₀ * k₂) • w₁ + k₁ • (k₀ * b ^ e₀) • (m₁ *ᵥ w₂),
        add_mem (L.smul_of_tower_mem _ hw₁) (L.smul_of_tower_mem _ (hden _ hw₂)), ?_⟩
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      linear_combination (norm := module) (k₀ * k₂) • b2 + (k₀ * k₁) • a3
    · have := (H₁ _ (H₂ v hv).2.1).2.1
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec] at this
    · have := (H₂ _ (H₁ v hv).2.2).2.2
      rwa [Matrix.mulVec_smul, smul_smul, ← pow_add, Matrix.mulVec_mulVec, ← Matrix.mul_inv_rev, add_comm] at this

end GlobalTheory.UTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOne
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans

theorem IsU.transpose_mul_mul_map {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R}
    {G γ : Matrix (Fin n) (Fin n) R} (h : IsU σ G γ) : γᵀ * G * γ.map σ = G := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 : hf σ G (Pi.single a 1) (Pi.single b 1) = G a b := by
    simp [hf, Pi.single_apply, apply_ite σ]
  rw [h2] at h1
  rw [← h1]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem IsU.det_mul_conj_det {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : γ.det * σ γ.det = 1 := by
  have h1 := congrArg Matrix.det h.transpose_mul_mul_map
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (γ.map σ).det = σ γ.det := by
    rw [RingHom.map_det]; rfl
  rw [h2] at h1
  apply mul_left_cancel₀ hG
  linear_combination h1

theorem IsU.nonsing_inv {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : IsU σ G γ⁻¹ := by
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (h.det_mul_conj_det hG)
  intro x y
  rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem tvGen_normal : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∀ γ, IsU σ G γ → γ.det * σ γ.det = 1 ∧ IsU σ G γ⁻¹) ∧ (∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧ ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ ∧ ∃ m'' ∈ TvGen σ G, m * γ = γ * m'') := by
  intro E _ _ n σ G hG
  obtain ⟨-, -, hmul, hdet, hU, hconj, -, hUmul⟩ := _root_.GlobalTheory.UTrans.Calc.calculus E n σ G hG.invol hG.herm
  refine ⟨fun γ h => ⟨h.det_mul_conj_det hG.det_ne, h.nonsing_inv hG.det_ne⟩, ?_⟩
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ m.det = 1 ∧ m⁻¹ ∈ TvGen σ G ∧
      ∀ γ, IsU σ G γ → ∃ m' ∈ TvGen σ G, γ * m = m' * γ := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      refine ⟨hU x t (by rw [ht, hx]; simp), by rw [hdet, hx]; simp, ?_, ?_⟩
      · have h1 : tv σ G x t * tv σ G x (-t) = 1 := by
          rw [hmul, hx]
          ext a b
          simp [tv]
        rw [Matrix.inv_eq_right_inv h1]
        exact Submonoid.subset_closure ⟨x, -t, hx, by rw [map_neg]; linear_combination -ht, rfl⟩
      · intro γ hγ
        exact ⟨tv σ G (γ *ᵥ x) t, Submonoid.subset_closure ⟨_, t, by rw [hγ, hx], ht, rfl⟩,
          hconj γ x t hγ⟩
    | one =>
      refine ⟨fun x y => by simp, by simp, by rw [inv_one]; exact one_mem _, fun γ _ => ⟨1, one_mem _, by simp⟩⟩
    | mul a b _ _ ha hb =>
      obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
      refine ⟨hUmul _ _ ha1 hb1, by rw [Matrix.det_mul, ha2, hb2, one_mul], ?_, ?_⟩
      · rw [Matrix.mul_inv_rev]; exact mul_mem hb3 ha3
      · intro γ hγ
        obtain ⟨a', ha', ea⟩ := ha4 γ hγ
        obtain ⟨b', hb', eb⟩ := hb4 γ hγ
        exact ⟨a' * b', mul_mem ha' hb', by rw [← mul_assoc, ea, mul_assoc, eb, mul_assoc]⟩
  intro m hm
  obtain ⟨h1, h2, h3, h4⟩ := key m hm
  refine ⟨h1, h2, h3, fun γ hγ => ?_⟩
  obtain ⟨m', hm', e⟩ := h4 γ hγ
  obtain ⟨m'', hm'', e'⟩ := h4 γ⁻¹ (hγ.nonsing_inv hG.det_ne)
  have hu : IsUnit γ.det := IsUnit.of_mul_eq_one _ (hγ.det_mul_conj_det hG.det_ne)
  refine ⟨m', hm', e, m'', hm'', ?_⟩
  calc m * γ = γ * (γ⁻¹ * m) * γ := by
        rw [← mul_assoc, Matrix.mul_nonsing_inv _ hu, one_mul]
    _ = γ * m'' := by
        rw [e', mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hu, mul_one]

end GlobalTheory.UTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_map_of_basis {F L A B ι : Type} [CommRing F] [CommRing L] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra L B] [Fintype ι] [DecidableEq ι] (φ : F →+* L) (ψ : A →+* B)
    (hψ : ∀ c, ψ (algebraMap F A c) = algebraMap L B (φ c))
    (b : Module.Basis ι F A) (b' : Module.Basis ι L B) (hb : ∀ i, ψ (b i) = b' i) (y : A) :
    Algebra.norm L (ψ y) = φ (Algebra.norm F y) := by
  have hr : ∀ (x : A) (i : ι), b'.repr (ψ x) i = φ (b.repr x i) := by
    intro x i
    have h1 : ψ x = ∑ j, φ (b.repr x j) • b' j := by
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hψ, hb]
    rw [h1, b'.repr_sum_self]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem exists_basis_pow_root {L : Type} [Field L] {p : ℕ} (hp : 0 < p) (a : L) :
    ∃ b : Module.Basis (Fin p) L (AdjoinRoot (X ^ p - C a : L[X])),
      ∀ i, b i = AdjoinRoot.root (X ^ p - C a : L[X]) ^ (i : ℕ) := by
  have hne : (X ^ p - C a : L[X]) ≠ 0 := X_pow_sub_C_ne_zero hp a
  have hd : (AdjoinRoot.powerBasis hne).dim = p := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C _]
  refine ⟨(AdjoinRoot.powerBasis hne).basis.reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen]
  simp

theorem powSub_le_kNorm_and_kNorm_map : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  intro p hp
  constructor
  · intro F L _ _ φ δ x hx
    obtain ⟨r, hr⟩ := (mem_powSub p φ x).1 hx
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    obtain ⟨b, -⟩ := exists_basis_pow_root hp (φ δ)
    refine (mem_kNorm p φ δ x).2
      ⟨Units.map (algebraMap L (AdjoinRoot (X ^ p - C (φ δ) : L[X]))).toMonoidHom
        (Units.mk0 r hr0), ?_⟩
    change Algebra.norm L (algebraMap L _ r) = _
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, hr]
  · intro F L _ _ φ δ x hx
    obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ x).1 hx
    obtain ⟨b, hb⟩ := exists_basis_pow_root hp (RingHom.id F δ)
    obtain ⟨b', hb'⟩ := exists_basis_pow_root hp (φ δ)
    have hdv : (X ^ p - C (φ δ) : L[X]) ∣ (X ^ p - C (RingHom.id F δ) : F[X]).map φ := by
      simp
    let ψ := AdjoinRoot.map φ _ _ hdv
    refine (mem_kNorm p φ δ x).2 ⟨Units.map ψ.toMonoidHom y, ?_⟩
    change Algebra.norm L (ψ y) = _
    rw [norm_map_of_basis φ ψ (fun c => by simp [ψ]) b b'
      (fun i => by simp [hb, hb', ψ]) y, hy]
    rfl

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationEqOneOfNormOneOfNotMoved
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem intValuation_map_le_of_map_le {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (P : HeightOneSpectrum R) (h : P.asIdeal.map σ ≤ P.asIdeal) (a : R) :
    P.intValuation (σ a) ≤ P.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ) := P.intValuation_if_neg ha
  set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors
  have h2 : a ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem a k).1 h1.le
  rw [h1, P.intValuation_le_pow_iff_mem]
  have h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h k
  exact h3 (Ideal.mem_map_of_mem σ h2)

theorem valuation_eq_one_of_norm_one_of_not_moved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by
  intro F E _ _ _ _ _ c hc u P hu hP
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (c : E →+* E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E) := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [hσ, hσ, hc]
  have hle : P.asIdeal.map σ ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_contra hb
    exact hP ⟨a, ha, σ a, hσ a, hb⟩
  have hint : ∀ a, P.intValuation (σ a) = P.intValuation a := fun a => by
    apply le_antisymm (intValuation_map_le_of_map_le σ P hle a)
    have := intValuation_map_le_of_map_le σ P hle (σ a)
    rwa [hσσ] at this
  have hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E) := fun a => by
    rw [← hσ]
    change P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)
    rw [P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]
  have hcu : P.valuation E (c u) = P.valuation E u := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hval a) (hval b)
  have h2 : P.valuation E u ^ 2 = 1 := by
    have := congrArg (P.valuation E) hu
    rwa [map_mul, hcu, map_one, ← sq] at this
  exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2

end GlobalTheory.UnRep
end

