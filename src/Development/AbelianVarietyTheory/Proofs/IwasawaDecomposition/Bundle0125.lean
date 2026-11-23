module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsNormModEqOneOfPrincipalRayClass
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayNorm

theorem int_norm_pos (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {x : 𝓞 K} (hx : x ≠ 0) :
    0 < Algebra.norm ℤ x := by
  classical
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx

  have fibre : ∀ w : InfinitePlace K,
      ∏ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ (x : K) =
        ((Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    intro w
    have hset : (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have key := InfinitePlace.mk_eq_iff (φ := φ) (ψ := w.embedding)
      rw [InfinitePlace.mk_embedding] at key
      rw [key]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [← h]; exact (star_star φ).symm
      · rintro (h | h)
        · exact Or.inl h
        · right; rw [h]; exact star_star w.embedding
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x : K)) =
      ((∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)]
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ (x : K)) _
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ (x : K))]
    push_cast
    exact Finset.prod_congr rfl (fun w _ => fibre w)
  have hpos : (0 : ℝ) < ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx')
  have hreal : ((Algebra.norm ℚ (x : K) : ℚ) : ℝ) =
      ∏ w : InfinitePlace K, Complex.normSq (w.embedding (x : K)) := by
    apply Complex.ofReal_injective
    rw [← hprod]
    simp
  have hq : (0 : ℚ) < Algebra.norm ℚ (x : K) := by
    have := hreal ▸ hpos
    exact_mod_cast this
  rw [← Algebra.coe_norm_int] at hq
  exact_mod_cast hq

theorem norm_cast_eq (K : Type) [Field K] [NumberField K] (p : ℕ) {x y : 𝓞 K}
    (h : x - y ∈ Ideal.span {(p : 𝓞 K)}) :
    ((Algebra.norm ℤ x : ℤ) : ZMod p) = ((Algebra.norm ℤ y : ℤ) : ZMod p) := by
  classical
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = y + (p : 𝓞 K) * z := by rw [mul_comm, hz]; ring
  let b := RingOfIntegers.basis K
  have h0 : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b (p : 𝓞 K)) = 0 := by
    rw [map_natCast, map_natCast]
    ext i j
    simp
  have hmat : (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b x) =
      (Int.castRingHom (ZMod p)).mapMatrix (Algebra.leftMulMatrix b y) := by
    rw [hx, map_add (f := _), map_mul, map_add (f := _), map_mul, h0, zero_mul, add_zero]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b]
  have e1 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b x)
  have e2 := RingHom.map_det (Int.castRingHom (ZMod p)) (Algebra.leftMulMatrix b y)
  simp only [eq_intCast] at e1 e2
  rw [e1, e2, hmat]

theorem absNorm_modEq_one : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (𝔮 : Ideal (𝓞 K)) (p : ℕ), 𝔮 ≤ Ideal.span {(p : 𝓞 K)} → ∀ (I : Ideal (𝓞 K)) (α β : 𝓞 K), RayPair 𝔮 α β → I * Ideal.span {β} = Ideal.span {α} → Ideal.absNorm I ≡ 1 [MOD p] := by
  intro K _ _ _ 𝔮 p h𝔮 I α β hR hI
  unfold GlobalTheory.NT.RayPair at hR
  obtain ⟨hα, hβ, -, hβq, hαβ, -⟩ := hR

  have hnorm : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β = Algebra.norm ℤ α := by
    have e := congrArg Ideal.absNorm hI
    rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at e
    have e' : ((Ideal.absNorm I * (Algebra.norm ℤ β).natAbs : ℕ) : ℤ) =
        ((Algebra.norm ℤ α).natAbs : ℤ) := by rw [e]
    push_cast at e'
    rwa [abs_of_pos (int_norm_pos K hβ), abs_of_pos (int_norm_pos K hα)] at e'

  have htop : Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} = ⊤ := by
    rw [Ideal.isCoprime_iff_sup_eq] at hβq
    exact eq_top_mono (sup_le_sup_left h𝔮 _) hβq
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ Ideal.span {(p : 𝓞 K)} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp h1
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have hu : β * u - 1 ∈ Ideal.span {(p : 𝓞 K)} := by
    have e : β * u - 1 = -c := by rw [← hac]; ring
    rw [e]; exact neg_mem hc
  have hinv := norm_cast_eq K p hu
  rw [map_mul, map_one] at hinv
  push_cast at hinv
  have hmod := norm_cast_eq K p (h𝔮 hαβ)
  have key : ((Ideal.absNorm I : ℕ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) =
      ((Algebra.norm ℤ β : ℤ) : ZMod p) := by
    have e := congrArg (fun t : ℤ => (t : ZMod p)) hnorm
    push_cast at e
    rw [e, hmod]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [Nat.cast_one]
  linear_combination (1 - ((Ideal.absNorm I : ℕ) : ZMod p)) * hinv +
    ((Algebra.norm ℤ u : ℤ) : ZMod p) * key

end GlobalTheory.Mem.RayNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharacterValueMemKummerField
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem absNorm_pow_eq_prod_sq {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (v : HeightOneSpectrum (𝓞 L)) (h : ℕ)
    (k : L) (hk : FractionalIdeal.spanSingleton (𝓞 L)⁰ k = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ h = (∏ i, ‖φ i k‖) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm k
  rw [← hφ.prod_comp] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) k ^ (InfinitePlace.mk (φ i)).mult = ‖φ i k‖ ^ 2 := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  simp_rw [h2] at h1
  have h3 := congrArg FractionalIdeal.absNorm hk
  rw [FractionalIdeal.absNorm_span_singleton, map_pow, FractionalIdeal.coeIdeal_absNorm] at h3
  rw [← Finset.prod_pow, h1, h3]
  simp

theorem valTw_mem_kummerField : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] [_root_.NumberField.IsTotallyComplex L] (φ₀ : L →+* ℂ) (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∀ (v : HeightOneSpectrum (𝓞 L)) (h : ℕ) (k : Lˣ), FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h → χ.inf k * χ.val v ^ h = 1 → χ.valTw ((r : ℝ) / 2) v ∈ kummerField φ₀ h := by
  intro L _ _ _ _ φ₀ I _ φ hφ χ n r hinf hev v h k hk hχ
  choose s hs using exists_aut φ₀
  choose m hm using hev
  have hkm : (k : L) ∈ powIdealElts L h := ⟨k.ne_zero, _, hk⟩
  have hsm : ∀ τ, s τ (k : L) ∈ powIdealElts L h := fun τ => map_mem_pow (s τ : L →+* L) hkm
  have hy : ∏ i, ((s (φ i) k ^ n i)⁻¹ * (s (φ i) k * s ((starRingEnd ℂ).comp (φ i)) k) ^ m i) ∈ powIdealElts L h :=
    prod_mem_pow _ _ fun i _ => mul_mem_pow (inv_mem_pow (zpow_mem_pow (hsm _) _))
      (zpow_mem_pow (mul_mem_pow (hsm _) (hsm _)) _)
  refine mem_kummerField φ₀ hy ?_
  have hp := congrArg (Units.val : ℂˣ → ℂ) hχ
  rw [Units.val_mul, hinf, Units.val_one, Units.val_pow_eq_pow_val] at hp
  have hN := absNorm_pow_eq_prod_sq φ hφ v h k hk
  have hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hreal : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ h = (∏ i, ‖φ i k‖) ^ (-r) := by
    have h0 : 0 ≤ ∏ i, ‖φ i k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _), hN, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hc : χ.valTw ((r : ℝ) / 2) v ^ h = ((χ.val v : ℂˣ) : ℂ) ^ h * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) := by
    unfold HChar.valTw
    rw [hpow, mul_pow, ← Complex.ofReal_pow, hreal, Finset.prod_zpow, Complex.ofReal_zpow, Complex.ofReal_prod]
  rw [hc, eq_inv_of_mul_eq_one_right hp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by simp
  rw [map_mul, map_inv₀, map_zpow₀, map_zpow₀, map_mul, ← hs, ← hs, RingHom.comp_apply, Complex.mul_conj', sq,
    mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]
  ring

end GlobalTheory.Mem.FieldsEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdFinrank
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ClassDvd

theorem classGroup_exists_integral_ideal_coprime {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R} (hm : m ≠ ⊥)
    (c : ClassGroup R) : ∃ I : (Ideal R)⁰, IsCoprime (I : Ideal R) m ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, ← Ideal.one_eq_top]; exact isCoprime_one_right, hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J) Ideal.mul_le_left
    (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, ?_, ?_⟩
  · rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact h1
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
    rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
    exact ⟨a, ha0, by rw [hM, mul_comm]⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

theorem exists_symbol [IsGalois K L] (hR : IsRay L 𝔮) (I : Ideal (𝓞 K)) :
    I ≠ ⊥ → IsCoprime I 𝔮 → ∃ σ : L ≃ₐ[K] L, ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ I hI =>
    intro _ _
    obtain rfl : I = 1 := by rw [Ideal.one_eq_top]; exact Ideal.isUnit_iff.1 hI
    exact ⟨1, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
  | h₃ I p hI0 hp ih =>
    intro _ hc
    obtain ⟨σ, hσ⟩ := ih hI0 hc.of_mul_left_right
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv : ¬ v.asIdeal ∣ 𝔮 := fun h => hp.not_isUnit (hc.of_mul_left_left.isUnit_of_dvd h)
    obtain ⟨τ, hτ⟩ := GlobalTheory.NT.exists_isFrob L v
    refine ⟨τ * σ, fun χ => ?_⟩
    have h1 := GlobalTheory.NT.Model.heckeIdeal_prime L χ v
    rw [heckeVal_of_unramIn L χ (hR.1 v hv) hτ] at h1
    rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hp.ne_zero hI0, hσ]
    change heckeIdeal L χ v.asIdeal * _ = _
    rw [h1]; simp

theorem classNumber_dvd_finrank : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRayField K L 𝔮 → classNumber K ∣ Module.finrank K L := by
  intro K L _ _ _ _ _ 𝔮 h𝔮 h
  have := h.1
  have hR : IsRay L 𝔮 := h.2
  let S : Submonoid ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { carrier := {x | ∃ I : (Ideal (𝓞 K))⁰, IsCoprime (I : Ideal (𝓞 K)) 𝔮 ∧ ClassGroup.mk0 I = x.2 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ x.1 : ℂˣ)}
      one_mem' := ⟨1, isCoprime_one_left, map_one _, fun χ => by
        rw [OneMemClass.coe_one, GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI, hIc, hx⟩ ⟨J, hJ, hJc, hy⟩
        refine ⟨I * J, hI.mul_left hJ, by rw [map_mul, hIc, hJc]; rfl, fun χ => ?_⟩
        rw [Submonoid.coe_mul, GlobalTheory.NT.Model.heckeIdeal_mul L χ (nonZeroDivisors.coe_ne_zero I)
          (nonZeroDivisors.coe_ne_zero J), hx, hy]; simp }
  let H : Subgroup ((L ≃ₐ[K] L) × ClassGroup (𝓞 K)) :=
    { S with
      inv_mem' := by
        intro x hx
        have : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        rw [this]
        exact S.pow_mem hx _ }
  have h1 : Function.Bijective ((MonoidHom.fst _ _).comp H.subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun σ => ?_⟩
    · rintro ⟨⟨σ, c⟩, I, hI, hIc, hx⟩ hσ
      obtain rfl : σ = 1 := hσ
      obtain ⟨α, β, hp, he⟩ := (hR.2.2 I (nonZeroDivisors.coe_ne_zero I) hI).1 fun χ => by simpa using hx χ
      have hc : ClassGroup.mk0 I = ClassGroup.mk0 1 :=
        ClassGroup.mk0_eq_mk0_iff.2 ⟨β, α, hp.2.1, hp.1, by simpa [mul_comm] using he⟩
      rw [map_one] at hc
      obtain rfl : c = 1 := hIc.symm.trans hc
      rfl
    · obtain ⟨I, hI0, hI, hx⟩ := RayDegree.exists_ideal hR σ
      let J : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
      exact ⟨⟨(σ, ClassGroup.mk0 J), J, hI, rfl, hx⟩, rfl⟩
  have h2 : Function.Surjective ((MonoidHom.snd _ _).comp H.subtype) := fun c => by
    obtain ⟨I, hI, hc⟩ := classGroup_exists_integral_ideal_coprime h𝔮 c
    obtain ⟨σ, hσ⟩ := exists_symbol hR I (nonZeroDivisors.coe_ne_zero I) hI
    exact ⟨⟨(σ, c), I, hI, hc, hσ⟩, rfl⟩
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_eq_of_bijective _ h1, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_surjective h2

end GlobalTheory.Mem.ClassDvd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTop
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField Pointwise

namespace GlobalTheory.Mem.FieldsEx

theorem isFrob_conj {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (τ : L ≃ₐ[K] L) :
    IsFrob L v (τ * σ * τ⁻¹) := by
  obtain ⟨P, hP, hl, h⟩ := (isFrob_iff L v σ).1 h
  exact (isFrob_iff L v _).2 ⟨τ • P, inferInstance, inferInstance, h.conj τ⟩

theorem isFrob_one_of_fix {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (F : IntermediateField K L)
    [NumberField F] (hF : ∀ x ∈ F, σ x = x) : IsFrob F v 1 := by
  obtain ⟨P, hP, hl, h⟩ := h
  refine ⟨P.under (𝓞 F), inferInstance, inferInstance, fun x => ?_⟩
  rw [Ideal.under_def, Ideal.mem_comap, one_smul, map_sub, map_pow]
  have h1 : σ • algebraMap (𝓞 F) (𝓞 L) x = algebraMap (𝓞 F) (𝓞 L) x :=
    RingOfIntegers.ext (hF _ (x : F).2)
  have := h (algebraMap (𝓞 F) (𝓞 L) x)
  rwa [h1] at this

theorem closure_frob_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ (F : Type) [Field F] [NumberField F] [Algebra K F],
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  intro K L _ _ _ _ _ _ S _ h
  set H := Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} with hH
  have hn : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hx⟩ := hx
      exact Subgroup.subset_closure ⟨v, hv, isFrob_conj hx g⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      convert this using 1
      group
    | inv x _ hx =>
      have := H.inv_mem hx
      convert this using 1
      group
  let F := IntermediateField.fixedField H
  have : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  have : NumberField F := NumberField.of_module_finite K F
  have h1 := h F fun v hv => by
    obtain ⟨σ, hσ⟩ := exists_isFrob L v
    exact isFrob_one_of_fix hσ F fun x hx =>
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.subset_closure ⟨v, hv, hσ⟩)
  refine eq_top_iff.2 fun τ _ => ?_
  rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h2 := τ.restrictNormal_commutes F ⟨x, hx⟩
  rw [h1 (τ.restrictNormal F)] at h2
  exact h2.symm

end GlobalTheory.Mem.FieldsEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingIdentity
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylReproducing

open Formalism.GradedWeylDivisibility GlobalTheory.WeylMinorDual

theorem rowAct_leadMinor (N h : ℕ) (hh : h ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh) =
      ∑ K : Fin h ↪o Fin N, C (eval x (initMinor ℚ (r := N) (n := N) (⇑K) hh)) *
        initMinor ℚ (r := N) (n := N) (⇑K) hh := by
  set A : Matrix (Fin h) (Fin N) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun p b => C (x (b, Fin.castLE hh p)) with hA
  set B : Matrix (Fin N) (Fin h) (MvPolynomial (Fin N × Fin N) ℚ) :=
    Matrix.of fun b q => X (b, Fin.castLE hh q) with hB
  have hM : rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (initMinor ℚ (r := N) (n := N) (Fin.castLE hh) hh)
      = (A * B).det := by
    unfold initMinor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [rowAct, Matrix.mul_apply, hA, hB]
  rw [hM, PI.IsoDerivBFintype.cauchyBinet]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  · rw [← Matrix.det_transpose (A.submatrix id K)]
    unfold initMinor
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p k
    simp [hA]

theorem rowAct_hw_expand (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (x : Fin N × Fin N → ℚ) :
    rowAct ℚ (Matrix.of fun a s : Fin N => x (a, s)).transpose (hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, C (eval x (colProd ℚ N Y hY J)) * colProd ℚ N Y hY J := by
  have hwEq : hw ℚ le_rfl (fun r : Fin N => Y.rowLen r) =
      bideterminant ℚ (r := N) (n := N) (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY)
        (fun c => Fin.castLE (colLen_le hY c)) := by
    rw [bidet_lead ℚ N (fun c : Fin (Y.rowLen 0) => Y.colLen c) (colLen_le hY) _ (fun c i => rfl), shapeDeg_colLen]
  rw [hwEq]
  unfold bideterminant
  rw [map_prod]
  simp_rw [rowAct_leadMinor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod]
  rfl

theorem reproducing (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ)
    (hh : h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r)) :
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) •
        GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti a b hab

  let L : MvPolynomial (Fin N × Fin N) ℚ →ₗ[ℚ] ℚ :=
    { toFun := fun g => fockQ g h
      map_add' := fun f f' => (fockQBilin _ f f' h 1).1
      map_smul' := fun c f => (fockQBilin _ f 0 h c).2 }
  apply MvPolynomial.funext
  intro x
  set z : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun a s : Fin N => x (a, s) with hz
  have hev : eval (idFrame ℚ N N) (rowAct ℚ z h) = eval x h := by
    have : (eval (idFrame ℚ N N)).comp (rowAct ℚ z).toRingHom = eval x := by
      refine MvPolynomial.ringHom_ext (fun a => by simp [rowAct]) fun v => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rowAct, aeval_X, eval_X,
        map_sum, map_mul, eval_C, idFrame]
      rw [Finset.sum_eq_single v.2]
      · simp [hz]
      · intro b _ hb
        simp [Fin.val_inj, hb]
      · simp
    exact congrArg (fun f => f h) this
  have key1 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) =
      ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, fockQ h (colProd ℚ N Y hY J) * eval x (colProd ℚ N Y hY J) := by
    rw [hz, rowAct_hw_expand, (fockQPos _ _ _).1]
    change L _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [C_mul', L.map_smul, smul_eq_mul, mul_comm]
    change fockQ _ h * _ = _
    rw [(fockQPos _ _ _).1]
  have key2 : fockQ h (rowAct ℚ z.transpose (hw ℚ le_rfl μ)) = eval x h * fockQ (hw ℚ le_rfl μ) (hw ℚ le_rfl μ) := by
    rw [← fock_space_row_action, (fockQPos _ _ _).1,
      fock_space_highest_weight N N le_rfl μ hanti _ (dualWeylRowStable ℚ N N μ z h hh), hev]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, smul_eval]
  simp only [smul_eval]
  rw [← key1, key2, mul_comm]

end GlobalTheory.WeylReproducing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisensteinStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frob_of_eisenstein_root : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  exact @GlobalTheory.TameRecip.exists_frob_fix_of_eisenstein
end

