module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMkOfComp
section
namespace GlobalTheory.QuotientMapComposition

theorem map_mk'_of_comp {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (f : A →+* R) (F : LA →+* LR)
    (h : F.comp (algebraMap A LA) = (algebraMap R LR).comp f) (M : Submonoid A) [IsLocalization M LA]
    (N : Submonoid R) [IsLocalization N LR] (a : A) (m : M) (n : N) (hn : (n : R) = f m) :
    F (IsLocalization.mk' LA a m) = IsLocalization.mk' LR (f a) n := by
  have hx : ∀ x, F (algebraMap A LA x) = algebraMap R LR (f x) := fun x => RingHom.congr_fun h x
  rw [IsLocalization.eq_mk'_iff_mul_eq, hn, ← hx, ← hx, ← map_mul, IsLocalization.mk'_spec]

theorem main : ∀ {A R₀ A' B₀ : Type} [inst : CommRing A] [inst_1 : CommRing R₀] [inst_2 : CommRing A'] [inst_3 : CommRing B₀] (φ : A →+* R₀) (ψ : A →+* A') (α : R₀ →+* B₀) (κ : A' →+* B₀), RingHom.comp α φ = RingHom.comp κ ψ → (∀ (a : A), (φ : A → R₀) a = (0 : R₀) → (ψ : A → A') a = (0 : A') → a = (0 : A)) → (∀ (r : R₀) (c : A'), (α : R₀ → B₀) r = (κ : A' → B₀) c → ∃ (a : A), (φ : A → R₀) a = r ∧ (ψ : A → A') a = c) → ∀ (s : A) (LA LR LA' LB : Type) [inst_4 : CommRing LA] [inst_5 : CommRing LR] [inst_6 : CommRing LA'] [inst_7 : CommRing LB] [inst_8 : Algebra A LA] [inst_9 : Algebra R₀ LR] [inst_10 : Algebra A' LA'] [inst_11 : Algebra B₀ LB] [IsLocalization.Away s LA] [IsLocalization.Away ((φ : A → R₀) s) LR] [IsLocalization.Away ((ψ : A → A') s) LA'] [IsLocalization.Away ((α : R₀ → B₀) ((φ : A → R₀) s)) LB] (Φ : LA →+* LR) (Ψ : LA →+* LA') (Aα : LR →+* LB) (Kκ : LA' →+* LB), RingHom.comp Φ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap R₀ LR) φ → RingHom.comp Ψ (Algebra.algebraMap A LA) = RingHom.comp (Algebra.algebraMap A' LA') ψ → RingHom.comp Aα (Algebra.algebraMap R₀ LR) = RingHom.comp (Algebra.algebraMap B₀ LB) α → RingHom.comp Kκ (Algebra.algebraMap A' LA') = RingHom.comp (Algebra.algebraMap B₀ LB) κ → (∀ (t : LA), (Φ : LA → LR) t = (0 : LR) → (Ψ : LA → LA') t = (0 : LA') → t = (0 : LA)) ∧ ∀ (a : LR) (b : LA'), (Aα : LR → LB) a = (Kκ : LA' → LB) b → ∃ (t : LA), (Φ : LA → LR) t = a ∧ (Ψ : LA → LA') t = b := by
  intro A R₀ A' B₀ _ _ _ _ φ ψ α κ h0 hinj hsurj s LA LR LA' LB _ _ _ _ _ _ _ _ _ _ _ _ Φ Ψ Aα Kκ hΦ hΨ hA hK
  have hu : κ (ψ s) = α (φ s) := (RingHom.congr_fun h0 s).symm
  constructor
  · intro t ht1 ht2
    obtain ⟨⟨a, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) t
    rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a _ ⟨φ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht1
    rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a _ ⟨ψ s ^ n, n, rfl⟩ (by simp),
      IsLocalization.mk'_eq_zero_iff] at ht2
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := ht1
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := ht2
    change φ s ^ k * φ a = 0 at hk
    change ψ s ^ l * ψ a = 0 at hl
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨s ^ (k + l), k + l, rfl⟩, hinj _ ?_ ?_⟩
    · change φ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_right_comm, hk, zero_mul]
    · change ψ (s ^ (k + l) * a) = 0
      rw [map_mul, map_pow, pow_add, mul_assoc, hl, mul_zero]
  · intro a b hab
    obtain ⟨⟨r, _, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (φ s)) a
    obtain ⟨⟨c, _, m, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (ψ s)) b
    rw [map_mk'_of_comp α Aα hA (Submonoid.powers (φ s)) (Submonoid.powers (α (φ s))) r _
        ⟨α (φ s) ^ n, n, rfl⟩ (by simp),
      map_mk'_of_comp κ Kκ hK (Submonoid.powers (ψ s)) (Submonoid.powers (α (φ s))) c _
        ⟨α (φ s) ^ m, m, rfl⟩ (by simp [hu]),
      IsLocalization.mk'_eq_iff_eq, IsLocalization.eq_iff_exists (Submonoid.powers (α (φ s)))] at hab
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hab
    change α (φ s) ^ k * (α (φ s) ^ m * α r) = α (φ s) ^ k * (α (φ s) ^ n * κ c) at hk
    obtain ⟨a0, ha1, ha2⟩ := hsurj (φ s ^ (k + m) * r) (ψ s ^ (k + n) * c) (by
      rw [map_mul, map_pow, map_mul, map_pow, hu, pow_add, pow_add, mul_assoc, mul_assoc]; exact hk)
    refine ⟨IsLocalization.mk' LA a0 (⟨s ^ (n + k + m), n + k + m, rfl⟩ : Submonoid.powers s), ?_, ?_⟩
    · rw [map_mk'_of_comp φ Φ hΦ (Submonoid.powers s) (Submonoid.powers (φ s)) a0 _
        ⟨φ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change φ s ^ n * φ a0 = φ s ^ (n + k + m) * r
      rw [ha1]; ring
    · rw [map_mk'_of_comp ψ Ψ hΨ (Submonoid.powers s) (Submonoid.powers (ψ s)) a0 _
        ⟨ψ s ^ (n + k + m), _, rfl⟩ (by simp), IsLocalization.mk'_eq_iff_eq]
      congr 1
      change ψ s ^ m * ψ a0 = ψ s ^ (n + k + m) * c
      rw [ha2]; ring

end GlobalTheory.QuotientMapComposition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSubApply
section
namespace GlobalTheory.LinearMapDifferenceFormula

open AdicCompletion

theorem map_sub_apply {A : Type} [CommRing A] (J : Ideal A) {M P : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (h k : M →ₗ[A] P) (y : AdicCompletion J M) :
    AdicCompletion.map J (h - k) y = AdicCompletion.map J h y - AdicCompletion.map J k y := by
  induction y using AdicCompletion.induction_on with
  | h a =>
    ext n
    simp

theorem main : ∀ (A : Type) [inst : CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [inst_2 : AddCommGroup N] [inst_3 : Module A N] [inst_4 : AddCommGroup M] [inst_5 : Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → M →ₗ[A] M), Function.Injective (⇑f : N → M) → (∀ (x : M), x ∈ LinearMap.range f ↔ ∀ (σ : Γ), (g σ : M → M) x = x) → Function.Injective (⇑(AdicCompletion.map J f) : AdicCompletion J N → AdicCompletion J M) ∧ ∀ (y : AdicCompletion J M), y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ (σ : Γ), (AdicCompletion.map J (g σ) : AdicCompletion J M → AdicCompletion J M) y = y := by
  intro A _ _ J N M _ _ _ _ _ f Γ _ g hf hfix
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  refine ⟨AdicCompletion.map_injective J hf, ?_⟩

  let φ : M →ₗ[A] (Γ → M) := LinearMap.pi (fun σ => g σ - LinearMap.id)
  let ψ : M →ₗ[A] LinearMap.range φ := φ.rangeRestrict
  have hψs : Function.Surjective ψ := LinearMap.surjective_rangeRestrict φ
  have hφ0 : ∀ x, φ x = 0 ↔ ∀ σ, g σ x = x := by
    intro x
    simp only [φ, funext_iff, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Pi.zero_apply, sub_eq_zero]
  have hex : Function.Exact f ψ := by
    intro x
    have : ψ x = 0 ↔ φ x = 0 := by
      simp [ψ, Subtype.ext_iff]
    rw [this, hφ0, ← hfix]
    rfl
  have hE := AdicCompletion.map_exact (I := J) hf hex hψs
  have hinj : Function.Injective (AdicCompletion.map J (LinearMap.range φ).subtype) :=
    AdicCompletion.map_injective J (Submodule.injective_subtype _)
  have hcomp : (LinearMap.range φ).subtype ∘ₗ ψ = φ := by
    ext x; simp [ψ]
  intro y
  rw [LinearMap.mem_range, ← Set.mem_range, ← hE y]
  have h1 : AdicCompletion.map J ψ y = 0 ↔ AdicCompletion.map J φ y = 0 := by
    have e : AdicCompletion.map J φ y = AdicCompletion.map J (LinearMap.range φ).subtype (AdicCompletion.map J ψ y) := by
      rw [AdicCompletion.map_comp_apply, hcomp]
    rw [e]
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; exact hinj (by rw [h, _root_.map_zero])
  rw [h1]
  have hpi : AdicCompletion.map J φ y = 0 ↔ ∀ σ, AdicCompletion.map J (LinearMap.proj σ) (AdicCompletion.map J φ y) = 0 := by
    constructor
    · intro h σ; rw [h, _root_.map_zero]
    · intro h
      apply (AdicCompletion.piEquivOfFintype J (fun _ : Γ => M)).injective
      rw [_root_.map_zero, AdicCompletion.piEquivOfFintype_apply]
      funext σ
      exact h σ
  rw [hpi]
  refine forall_congr' fun σ => ?_
  rw [AdicCompletion.map_comp_apply]
  have : (LinearMap.proj σ : (Γ → M) →ₗ[A] M) ∘ₗ φ = g σ - LinearMap.id := by
    ext x; simp [φ]
  rw [this, map_sub_apply, AdicCompletion.map_id, LinearMap.id_apply, sub_eq_zero]

end GlobalTheory.LinearMapDifferenceFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqOfImDotProductMulVecStarEqOnSpan
section
open scoped Matrix

namespace GlobalTheory

theorem matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span :
    ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  intro g H H' S hS h
  set D := H - H' with hD
  have hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
    intro a ha b hb
    simp only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im)
      (by intro a a' b; simp [add_dotProduct])
      (by intro r a b; simp [smul_dotProduct])
      (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB : B = 0 := by
    apply LinearMap.ext_on hS
    intro a ha
    apply LinearMap.ext_on hS
    intro b hb
    simpa [B] using hS0 a ha b hb
  have hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0 := by
    intro a b
    have h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f a b) hB
      simpa [B] using this
    have h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f (Complex.I • a) b) hB
      simpa [B] using this
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im] at h2
    simp at h2
    exact Complex.ext h2 h1
  have hDz : D = 0 := by
    ext i j
    have := hall (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.star_single] using this
  exact sub_eq_zero.mp hDz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealLocalizationEqSpanOfReducedArtinianA
section
open IsLocalRing

namespace GlobalTheory

theorem exists_not_mem_mul_mem_span_of_reduced_artinian (R : Type) [CommRing R] (T : R)
    (hred : IsReduced (R ⧸ Ideal.span {T})) (hart : IsArtinianRing (R ⧸ Ideal.span {T}))
    (n : Ideal R) [n.IsPrime] (z : R) (hz : z ∈ n) :
    ∃ c : R, c ∉ n ∧ c * z ∈ Ideal.span {T} := by
  set x : R ⧸ Ideal.span {T} := Ideal.Quotient.mk _ z
  obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R ⧸ Ideal.span {T})
  simp only [smul_eq_mul, mul_one] at hy
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h0 : x * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨k + 1, ?_⟩
    have : x ^ k * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
    calc (x * (1 - x * Ideal.Quotient.mk _ w)) ^ (k + 1)
        = (x ^ k * (1 - x * Ideal.Quotient.mk _ w)) * (x * (1 - x * Ideal.Quotient.mk _ w) ^ k) := by rw [mul_pow, pow_succ, pow_succ]; ring
      _ = 0 := by rw [this, zero_mul]
  refine ⟨1 - z * w, ?_, ?_⟩
  · intro hc
    have : (1 : R) ∈ n := by
      have := n.add_mem hc (n.mul_mem_right w hz)
      simpa using this
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [x, mul_comm] using h0

theorem maximalIdeal_localization_eq_span_of_reduced_artinian :
    ∀ (R : Type) [CommRing R] (T : R), IsReduced (R ⧸ Ideal.span {T}) → IsArtinianRing (R ⧸ Ideal.span {T}) → ∀ (n : Ideal R) [n.IsPrime], T ∈ n → IsLocalRing.maximalIdeal (Localization.AtPrime n) = Ideal.span {algebraMap R (Localization.AtPrime n) T} := by
  intro R _ T hred hart n _ hT
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨c, hc, hcz⟩ := exists_not_mem_mul_mem_span_of_reduced_artinian R T hred hart n z hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hcz
    have hu : IsUnit (algebraMap R (Localization.AtPrime n) c) :=
      IsLocalization.map_units (Localization.AtPrime n) (⟨c, hc⟩ : n.primeCompl)
    rw [Ideal.mem_comap]
    have : algebraMap R (Localization.AtPrime n) z =
        (hu.unit⁻¹ : (Localization.AtPrime n)ˣ) * algebraMap R _ a * algebraMap R _ T := by
      rw [mul_assoc, ← map_mul, ha, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
section
namespace GlobalTheory

open IsLocalRing

theorem maxIdeal_pow_dvd_natCast_of_integers :
    ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type)
      [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A]
      [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A →
      ∃ N : ℕ, (p : A) ∣ a ^ N := by
  intro p hp C _ _ v O _ _ hv A _ _ _ _ a ha

  set J : Ideal O := (maximalIdeal A).comap (algebraMap O A) with hJdef
  haveI : J.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal A)

  have hJp : ∀ c ∈ J, ∃ k : ℕ, (p : O) ∣ c ^ k := by
    intro c hc
    have hlt : v (algebraMap O C c) < 1 := by
      refine lt_of_le_of_ne (hv.map_le_one c) ?_
      intro h1
      have hu : IsUnit c := hv.isUnit_of_one' h1
      have : IsUnit (algebraMap O A c) := hu.map _
      exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ hc this)
    have hp0 : 0 < v (algebraMap O C (p : O)) := by
      rw [map_natCast]
      exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 hp)
    obtain ⟨k, hk⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hlt
    refine ⟨k, hv.dvd_of_le ?_⟩
    rw [map_pow, map_pow]
    exact hk.le

  have hI : J.map (algebraMap O A) ≤ (Ideal.span {(p : A)}).radical := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨k, d, hd⟩ := hJp c hc
    refine ⟨k, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap O A d, ?_⟩
    rw [← map_pow, hd, map_mul, map_natCast]

  have ha' : a ∈ (J.map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    have hle : J ≤ Q.comap (algebraMap O A) := Ideal.map_le_iff_le_comap.1 hQ
    have hQc : Q.comap (algebraMap O A) = J :=
      ((inferInstance : J.IsMaximal).eq_of_le (Ideal.IsPrime.comap (algebraMap O A)).ne_top hle).symm
    haveI : (Q.comap (algebraMap O A)).IsMaximal := by rw [hQc]; infer_instance
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap O A) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) Q this
    rw [IsLocalRing.eq_maximalIdeal this]
    exact ha
  have h2 : a ∈ (Ideal.span {(p : A)}).radical := by
    have := Ideal.radical_mono hI ha'
    rwa [Ideal.radical_idem] at this
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, Ideal.mem_span_singleton.1 hN⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealSpanImageUniformizer
section
open IsLocalRing

namespace GlobalTheory

theorem eq_pow_mul_unit_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] (T : V) (hm : maximalIdeal V = Ideal.span {T}) (v : V) (hv : v ≠ 0) :
    ∃ (a : ℕ) (c : V), IsUnit c ∧ v = T ^ a * c := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have hex : ∃ n : ℕ, v ∉ Ideal.span {T ^ n} := by
    by_contra h
    push_neg at h
    apply hv
    have : v ∈ ⨅ n : ℕ, maximalIdeal V ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      rw [hm, Ideal.span_singleton_pow]
      exact h n
    rw [hK] at this
    exact (Ideal.mem_bot).mp this
  classical
  have hn₀ : v ∉ Ideal.span {T ^ Nat.find hex} := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : v ∈ Ideal.span {T ^ a} := by
    have := Nat.find_min hex (show a < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨a, c, ?_, by rw [← hc, mul_comm]⟩
  by_contra hcu
  have hcm : c ∈ maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hcu
  rw [hm] at hcm
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hcm
  apply hn₀
  rw [ha, Ideal.mem_span_singleton']
  exact ⟨d, by rw [← hc, ← hd, pow_succ]; ring⟩

theorem maximalIdeal_eq_span_map_of_fractions (V W : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [CommRing W] [IsLocalRing W] (φ : V →+* W) (T : V)
    (hm : IsLocalRing.maximalIdeal V = Ideal.span {T})
    (hTm : φ T ∈ IsLocalRing.maximalIdeal W) (hTn : φ T ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z : V, φ z ∈ nonZeroDivisors W ∧ φ z * w = φ x) :
    IsLocalRing.maximalIdeal W = Ideal.span {φ T} := by
  have cancel : ∀ (n : ℕ) (y : W), φ T ^ n * y = 0 → y = 0 := fun n y h =>
    (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hTn n)).mp h
  have surj : ∀ w : W, ∃ v : V, φ v = w := by
    intro w
    obtain ⟨x, z, hz, hzw⟩ := hfrac w
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      have h1 : (1 : W) = 0 :=
        (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp (zero_mul 1)
      exact one_ne_zero h1
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [hx, map_zero] at hzw
      rw [map_zero, eq_comm]
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp hzw
    obtain ⟨a, α, hα, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm x hx
    obtain ⟨c, β, hβ, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm z hz0
    obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
    simp only [map_mul, map_pow] at hzw
    rcases le_or_gt c a with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      refine ⟨βi * T ^ d * α, ?_⟩
      have h1 : φ β * w = φ T ^ d * φ α := by
        apply sub_eq_zero.mp
        apply cancel c
        linear_combination hzw
      have h2 : φ βi * φ β = 1 := by rw [← map_mul, mul_comm, hβi, map_one]
      calc φ (βi * T ^ d * α) = φ βi * (φ T ^ d * φ α) := by simp only [map_mul, map_pow]; ring
        _ = φ βi * (φ β * w) := by rw [h1]
        _ = w := by rw [← mul_assoc, h2, one_mul]
    · exfalso
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : φ T ^ (d + 1) * φ β * w = φ α := by
        apply sub_eq_zero.mp
        apply cancel a
        linear_combination hzw
      have hmem : φ T ^ (d + 1) * φ β * w ∈ maximalIdeal W := by
        rw [mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hTm _ (Nat.succ_pos d))
      rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      exact hmem (hα.map φ)
  ext w
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := surj w
    have hv : v ∈ maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
      exact hw (hu.map φ)
    rw [hm] at hv
    obtain ⟨v', rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [map_mul, Ideal.mem_span_singleton']
    exact ⟨φ v', rfl⟩
  · intro hw
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    exact Ideal.mul_mem_left _ _ hTm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHom
section
open NumberField

namespace GlobalTheory

theorem ringOfIntegers_ringHom_injective {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : 𝓞 E →+* 𝓞 K) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

theorem sum_log_norm_embeddings {K : Type} [Field K] [NumberField K] (y : K) :
    ∑ s : K →+* ℂ, Real.log ‖s y‖ = Real.log |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
  by_cases hy : y = 0
  · subst hy
    simp
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have h2 : ∏ s : K →+* ℂ, s y = ∏ s : K →ₐ[ℚ] ℂ, s y :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun s => rfl)
  rw [← Real.log_prod (fun s _ => by simpa using hy), ← norm_prod, h2, ← h]
  congr 1
  rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem mean_log_norm_embeddings_ringHom :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (σ : 𝓞 E →+* 𝓞 K) (x : 𝓞 E),
  (∑ s : K →+* ℂ, Real.log ‖s (σ x : K)‖) / Module.finrank ℚ K =
    Real.log |((Algebra.norm ℚ (x : E) : ℚ) : ℝ)| / Module.finrank ℚ E := by
  intro E K _ _ _ _ σ x
  have hinj : Function.Injective ((algebraMap (𝓞 K) K).comp σ) :=
    (RingOfIntegers.coe_injective).comp (ringOfIntegers_ringHom_injective σ)
  let τ : E →+* K := IsFractionRing.lift hinj
  have hτ : τ (x : E) = (σ x : K) := IsFractionRing.lift_algebraMap hinj x
  letI : Algebra E K := τ.toAlgebra
  haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  have hx : (σ x : K) = algebraMap E K (x : E) := hτ.symm
  rw [sum_log_norm_embeddings, hx, ← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow,
    ← Module.finrank_mul_finrank ℚ E K]
  have h1 : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank E K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  push_cast
  rw [abs_pow, Real.log_pow]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemIdentityComponentOfRational
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.mul_mem_identityComponent_of_rational : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  intro k _ G _ x y hx hy
  set T : G ⟶ G := (toUnit G ≫ x) * 𝟙 G with hT
  have hyT : y ≫ T = x * y := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
  have hηT : η[G] ≫ T = x := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
    have : (η[G] : 𝟙_ _ ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this, _root_.mul_one]
  have hsub := T.left.continuous.image_connectedComponent_subset ((η[G]).left (IsLocalRing.closedPoint k))
  have h1 : (x * y).left (IsLocalRing.closedPoint k) = T.left (y.left (IsLocalRing.closedPoint k)) := by
    rw [← hyT, Over.comp_left]
    exact Scheme.Hom.comp_apply y.left T.left _
  have h2 : T.left ((η[G]).left (IsLocalRing.closedPoint k)) = x.left (IsLocalRing.closedPoint k) := by
    rw [← hηT, Over.comp_left]
    exact (Scheme.Hom.comp_apply (η[G]).left T.left _).symm
  rw [h1, connectedComponent_eq hx]
  have := hsub ⟨_, hy, rfl⟩
  rwa [h2] at this
end

