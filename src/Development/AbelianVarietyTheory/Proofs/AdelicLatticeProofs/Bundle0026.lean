module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem tensor_repr_map {ι : Type} (b : Module.Basis ι F E) {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis K' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i =
      φ ((Algebra.TensorProduct.basis K b).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]

theorem tensor_norm_map [FiniteDimensional F E] {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) :
    Algebra.norm K' (Algebra.TensorProduct.map φ (AlgHom.id F E) y) = φ (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K' b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b)]
  rw [show (φ : K → K') = φ.toRingHom from rfl, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply]
  have h1 : (1 : K') ⊗ₜ[F] b j = Algebra.TensorProduct.map φ (AlgHom.id F E) ((1 : K) ⊗ₜ[F] b j) := by
    simp
  rw [h1, ← map_mul, tensor_repr_map b φ]
  rfl

theorem tensor_norm_one_tmul [FiniteDimensional F E] (K : Type) [CommRing K] [Algebra F K] (e : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.norm F e) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b), Algebra.norm_eq_matrix_det b,
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end

theorem tnorm_baseChange : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  intro F E _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro K K' _ _ _ _ φ x ⟨y, hy⟩
    refine ⟨Algebra.TensorProduct.map φ (AlgHom.id F E) y, ?_⟩
    rw [tensor_norm_map φ y, hy, AlgHom.commutes]
  · intro K _ _ e
    exact ⟨(1 : K) ⊗ₜ[F] e, tensor_norm_one_tmul K e⟩
  · rintro K _ _ x y hy0 ⟨a, ha⟩ ⟨c, hc⟩
    have hyK : algebraMap F K y ≠ 0 := (_root_.map_ne_zero _).mpr hy0
    have hu : IsUnit (Algebra.lmul K (K ⊗[F] E) c) := by
      rw [LinearMap.isUnit_iff_isUnit_det, ← Algebra.norm_apply, hc]
      exact hyK.isUnit
    obtain ⟨d, hd⟩ := ((Module.End.isUnit_iff _).mp hu).2 1
    have hd' : c * d = 1 := hd
    have hn : Algebra.norm K c * Algebra.norm K d = 1 := by
      rw [← map_mul, hd', map_one]
    refine ⟨a * d, ?_⟩
    rw [map_mul, ha, map_mul]
    rw [hc] at hn
    calc algebraMap F K x * algebraMap F K y * Algebra.norm K d
        = algebraMap F K x * (algebraMap F K y * Algebra.norm K d) := by ring
      _ = algebraMap F K x := by rw [hn, mul_one]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem IsKum.minpoly_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) : minpoly F θ = X ^ p - C δ := by
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime h.prime h.nonpow
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C δ h.prime.ne_zero)).symm
  simp [h.pow]

theorem IsKum.pow_apply {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, AlgEquiv.commutes, h.conj, pow_succ', map_mul]
    ring

theorem kummer_galois : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ IsGalois F E ∧ orderOf σ = p ∧ (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) ∧ Nonempty (E ≃ₐ[F] AdjoinRoot (X ^ p - C δ : F[X])) ∧ ∀ (L : Type) [Field L] [Algebra F L] (r : L), r ^ p = algebraMap F L δ → ∃ ψ : E →ₐ[F] L, ψ θ = r := by
  intro p F E _ _ _ _ ζ δ θ σ h
  have hp := h.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  have : NeZero p := ⟨hp0⟩
  have hirr : Irreducible (X ^ p - C δ) := X_pow_sub_C_irreducible_of_prime hp h.nonpow
  have hζ : (primitiveRoots p F).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr h.root⟩
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hθ0 : θ ≠ 0 := by
    intro h0
    have h1 := h.pow
    rw [h0, zero_pow hp0, eq_comm, map_eq_zero] at h1
    exact h.nonpow 0 (by rw [zero_pow hp0, h1])
  have hsplit : IsSplittingField F E (X ^ p - C δ) := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot (h.root.map_of_injective hinj) h.pow
    · rw [eq_top_iff, ← h.gen]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hp.pos δ)]
      simp [h.pow]
  have hfin : FiniteDimensional F E := IsSplittingField.finiteDimensional E (X ^ p - C δ)
  have hrank : Module.finrank F E = p :=
    finrank_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hgal : IsGalois F E := isGalois_of_isSplittingField_X_pow_sub_C (hζ := hζ) (H := hirr) (L := E)
  have hext : ∀ τ₁ τ₂ : E ≃ₐ[F] E, τ₁ θ = τ₂ θ → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top h.gen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hτ
  have hσp : σ ^ p = 1 :=
    hext _ _ (by rw [h.pow_apply, h.root.pow_eq_one, map_one, one_mul, AlgEquiv.one_apply])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hc := h.conj
    rw [h1, AlgEquiv.one_apply] at hc
    have hz : algebraMap F E ζ = 1 := mul_right_cancel₀ hθ0 (by rw [← hc, one_mul])
    exact h.root.ne_one hp.one_lt (hinj (by rw [hz, map_one]))
  have hord : orderOf σ = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime hσp hσ1
  have hall : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    have hτp : (τ θ) ^ p = algebraMap F E δ := by rw [← map_pow, h.pow, AlgEquiv.commutes]
    have hq : (τ θ / θ) ^ p = 1 := by
      rw [div_pow, hτp, ← h.pow, div_self (pow_ne_zero _ hθ0)]
    obtain ⟨i, -, hi⟩ := (h.root.map_of_injective hinj).eq_pow_of_pow_eq_one hq
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨i, hext _ _ ?_⟩
    rw [zpow_natCast, h.pow_apply, map_pow, hi, div_mul_cancel₀ _ hθ0]
  let e : AdjoinRoot (X ^ p - C δ : F[X]) ≃ₐ[F] E := adjoinRootXPowSubCEquiv hζ hirr h.pow
  refine ⟨hfin, hrank, hgal, hord, hall, ⟨e.symm⟩, ?_⟩
  intro L _ _ r hr
  refine ⟨(AdjoinRoot.liftAlgHom (X ^ p - C δ) (Algebra.ofId F L) r (by simp [hr])).comp
    e.symm.toAlgHom, ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, e, adjoinRootXPowSubCEquiv_symm_eq_root,
    AdjoinRoot.liftAlgHom_root]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormCoeffMinpolyLeOneOfNormLeOne
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem norm_coeff_minpoly_le_one_of_norm_le_one (K : Type) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) (h : ‖Algebra.norm K x‖ ≤ 1) (n : ℕ) :
    ‖(minpoly K x).coeff n‖ ≤ 1 := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖(minpoly K x).coeff 0‖ ≤ 1 := by
    rw [Algebra.norm_eq_norm_adjoin K x, ← IntermediateField.adjoin.powerBasis_gen hx,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, IntermediateField.adjoin.powerBasis_gen hx,
      IntermediateField.minpoly_gen, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Module.finrank_pos).ne').1 h
  have h1 : spectralNorm K L x ≤ 1 := by
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L x]
    exact Real.rpow_le_one (norm_nonneg _) h0 (by positivity)
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h1
  exact h1 n

theorem isIntegral_iff_valued_norm_le_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] [Algebra (v.adicCompletionIntegers F) L]
    [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L] (x : L) :
    IsIntegral (v.adicCompletionIntegers F) x ↔
      Valued.v (Algebra.norm (v.adicCompletion F) x) ≤ 1 := by
  constructor
  · intro h
    have h1 : IsIntegral (v.adicCompletionIntegers F) (Algebra.norm (v.adicCompletion F) x) :=
      Algebra.isIntegral_norm (v.adicCompletion F) h
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := v.adicCompletion F)).1 h1
    rw [← hy]
    exact y.2
  · intro h
    letI : NontriviallyNormedField (v.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰
    haveI : IsUltrametricDist (v.adicCompletion F) :=
      inferInstanceAs (@IsUltrametricDist (v.adicCompletion F)
        (Valued.toNormedField (v.adicCompletion F) ℤᵐ⁰).toDist)
    have hc : ∀ n, Valued.v ((minpoly (v.adicCompletion F) x).coeff n) ≤ 1 := fun n =>
      Valued.toNormedField.norm_le_one_iff.1
        (norm_coeff_minpoly_le_one_of_norm_le_one (v.adicCompletion F) L x
          (Valued.toNormedField.norm_le_one_iff.2 h) n)
    have hx : IsIntegral (v.adicCompletion F) x := Algebra.IsIntegral.isIntegral x
    have hl : minpoly (v.adicCompletion F) x ∈
        Polynomial.lifts (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (v.adicCompletion F), hq,
      minpoly.aeval]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormDifferenceIndexIdentity
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem herb_relIndex_map_range {A : Type} [CommGroup A] (f : A →* A) (H : Subgroup A) :
    (H.map f).relIndex f.range = (H ⊔ f.ker).index := by
  rw [← Subgroup.comap_map_eq, Subgroup.index_comap]

theorem herb_lattice {A : Type} [CommGroup A] (B C K : Subgroup A) (hCK : C ≤ K) :
    (C ⊔ B).index * Nat.card ↥(B ⊓ K) =
      (B ⊔ K).index * C.relIndex K * Nat.card ↥(C ⊓ B) := by
  have h1 : (C ⊔ B).relIndex (B ⊔ K) * (B ⊔ K).index = (C ⊔ B).index :=
    Subgroup.relIndex_mul_index (sup_le (hCK.trans le_sup_right) le_sup_left)
  have h2 : (C ⊔ B).relIndex (B ⊔ K) = (C ⊔ B ⊓ K).relIndex K := by
    have e : B ⊔ K = K ⊔ (C ⊔ B) := by
      apply le_antisymm
      · exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
      · exact sup_le le_sup_right (sup_le (hCK.trans le_sup_right) le_sup_left)
    rw [e, Subgroup.relIndex_sup_right, ← sup_inf_assoc_of_le B hCK, Subgroup.inf_relIndex_right]
  have h3 : C.relIndex (C ⊔ B ⊓ K) * (C ⊔ B ⊓ K).relIndex K = C.relIndex K :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hCK inf_le_right)
  have h4 : C.relIndex (C ⊔ B ⊓ K) = C.relIndex (B ⊓ K) := Subgroup.relIndex_sup_left _ _
  have h5 : Nat.card ↥(C ⊓ B) * C.relIndex (B ⊓ K) = Nat.card ↥(B ⊓ K) := by
    have e : C ⊓ (B ⊓ K) = C ⊓ B := by
      rw [inf_comm B K, ← inf_assoc, inf_eq_left.2 hCK]
    rw [← Subgroup.inf_relIndex_right C, e, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_bot_left]
    exact Subgroup.relIndex_mul_relIndex _ _ _ bot_le (e ▸ inf_le_right)
  rw [← h1, h2, ← h3, h4, ← h5]
  ring

theorem herb_nrm_apply_sigma {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ)
    (h : ∀ a, σ^[p] a = a) (a : A) : nrm σ p (σ a) = nrm σ p a := by
  have e1 := Finset.prod_range_succ (fun i => σ^[i] a) p
  have e2 := Finset.prod_range_succ' (fun i => σ^[i] a) p
  rw [e1] at e2
  simp only [h, Function.iterate_zero, id, Function.iterate_succ_apply] at e2
  rw [nrm_apply, nrm_apply]
  exact (mul_right_cancel e2).symm

theorem herb_nrm_of_fix {A : Type} [CommGroup A] (σ : A →* A) (p : ℕ) (b : A)
    (hb : b ∈ fix σ) : nrm σ p b = b ^ p := by
  rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed ((mem_fix σ b).1 hb) i)]
  simp

theorem herb_index_identity : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), (∀ a, σ^[p] a = a) → (nrm σ p).range.relIndex (fix σ) * ((dif σ).range.map (dif σ)).relIndex (dif σ).range * pTor p (fix σ) = pIdx p (fix σ) * (dif σ).range.relIndex (nrm σ p).ker * Nat.card ↥((dif σ).range ⊓ fix σ) := by
  intro p A _ σ h
  have hker : (dif σ).ker = fix σ := by
    ext a
    rw [MonoidHom.mem_ker, dif_apply, mem_fix, div_eq_one]
  have hCK : (dif σ).range ≤ (nrm σ p).ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, dif_apply, _root_.map_div, herb_nrm_apply_sigma σ p h, div_self']
  have hNB : (nrm σ p).range ≤ fix σ := by
    rintro _ ⟨a, rfl⟩
    rw [mem_fix, ← herb_nrm_apply_sigma σ p h a]
    conv_lhs => rw [herb_nrm_apply_sigma σ p h a]
    rw [nrm_apply, nrm_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Function.iterate_succ_apply σ i a, Function.iterate_succ_apply']
  have hpow : pows p (fix σ) = (fix σ).map (nrm σ p) := by
    ext x
    simp only [pows, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, herb_nrm_of_fix σ p b hb⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, (herb_nrm_of_fix σ p b hb).symm⟩
  have htor : pTor p (fix σ) = Nat.card ↥(fix σ ⊓ (nrm σ p).ker) := by
    unfold pTor
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    refine and_congr_right fun hx => ?_
    rw [herb_nrm_of_fix σ p x hx]
  have hidx : pIdx p (fix σ) =
      (fix σ ⊔ (nrm σ p).ker).index * (nrm σ p).range.relIndex (fix σ) := by
    unfold pIdx
    rw [hpow, ← herb_relIndex_map_range]
    exact (Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_le_range _ _) hNB).symm
  have hl := herb_lattice (fix σ) (dif σ).range (nrm σ p).ker hCK
  rw [herb_relIndex_map_range, hker, htor, hidx, mul_assoc, hl]
  ring

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCardLeIndexIInfOfPrime
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_card_le_index_iInf_of_prime :
    ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime →
      (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) →
      (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro p G ι _ _ K hp hpow hx hind
  classical
  choose x hx1 hx2 using hx
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ⧸ (⨅ i, K i)) := Nat.finite_of_card_ne_zero hind
  have hord : ∀ j, orderOf (QuotientGroup.mk' (K j) (x j)) = p := by
    intro j
    apply orderOf_eq_prime
    · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow j _
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hx1 j
  have hprod : ∀ (n : ι → Fin p) (j : ι),
      QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ)) = (QuotientGroup.mk' (K j) (x j)) ^ (n j : ℕ) := by
    intro n j
    rw [map_prod, Finset.prod_eq_single j]
    · rw [map_pow]
    · intro i _ hij
      rw [map_pow]
      have : QuotientGroup.mk' (K j) (x i) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx2 i j (Ne.symm hij)
      rw [this, one_pow]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let f : (ι → Fin p) → G ⧸ (⨅ i, K i) := fun n => QuotientGroup.mk (∏ i, x i ^ (n i : ℕ))
  have hf : Function.Injective f := by
    intro n m h
    have h1 := QuotientGroup.eq.1 h
    funext j
    have h2 := Subgroup.mem_iInf.1 h1 j
    have h3 : QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ))
        = QuotientGroup.mk' (K j) (∏ i, x i ^ (m i : ℕ)) := QuotientGroup.eq.2 h2
    rw [hprod, hprod] at h3
    apply Fin.ext
    refine pow_injOn_Iio_orderOf ?_ ?_ h3
    · rw [hord]; exact (n j).2
    · rw [hord]; exact (m j).2
  have := Nat.card_le_card_of_injective f hf
  simpa [Subgroup.index] using this

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionFiniteKerRange
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_pTor_ker_range_ne_zero :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'),
      pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 →
      pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  intro p A A' _ _ g h1 h2 h3
  unfold pIdx pTor pows at *
  refine ⟨?_, ?_, ?_⟩
  · set f : A →* A := powMonoidHom p with hf
    have hP : ((⊤ : Subgroup A).map f).relIndex g.ker ≠ 0 :=
      fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right le_top h0)
    have hBD : g.ker ≤ g.ker.comap f := by
      intro x hx
      exact g.ker.pow_mem hx p
    have hD : g.ker.relIndex (g.ker.comap f) ≠ 0 := by
      rw [Subgroup.relIndex_ker]
      have : Nat.card ((g.ker.comap f).map g) = Nat.card {x : A' // x ∈ g.range ∧ x ^ p = 1} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro x
        constructor
        · rintro ⟨a, ha, rfl⟩
          refine ⟨⟨a, rfl⟩, ?_⟩
          have : g (a ^ p) = 1 := ha
          rwa [map_pow] at this
        · rintro ⟨⟨a, rfl⟩, ha⟩
          refine ⟨a, ?_, rfl⟩
          change g (a ^ p) = 1
          rwa [map_pow]
      rw [this]
      exact h3
    have hQ : (g.ker.map f).relIndex ((g.ker.comap f).map f) ≠ 0 := by
      intro h0
      have hd := Subgroup.relIndex_map_map f g.ker (g.ker.comap f)
      have hk : f.ker ≤ g.ker.comap f := by
        intro x hx
        have : f x = 1 := hx
        change f x ∈ g.ker
        rw [this]
        exact one_mem _
      rw [h0, sup_eq_left.2 hk] at hd
      have hdv : (g.ker ⊔ f.ker).relIndex (g.ker.comap f) ∣ g.ker.relIndex (g.ker.comap f) :=
        Subgroup.relIndex_dvd_of_le_left _ le_sup_left
      rw [← hd] at hdv
      exact hD (Nat.eq_zero_of_zero_dvd hdv)
    have he : (g.ker.comap f).map f = ((⊤ : Subgroup A).map f) ⊓ g.ker := by
      rw [Subgroup.map_comap_eq, ← MonoidHom.range_eq_map]
    refine Subgroup.relIndex_ne_zero_trans hQ ?_
    rw [he, Subgroup.inf_relIndex_right]
    exact hP
  · have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero h2
    have : Finite {x : A // x ∈ g.ker ∧ x ^ p = 1} :=
      Finite.of_injective
        (fun x => (⟨x.1, Subgroup.mem_top _, x.2.2⟩ : {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1}))
        (fun x y h => Subtype.ext (congrArg (fun z => z.1) h))
    have : Nonempty {x : A // x ∈ g.ker ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow p⟩⟩
    exact Nat.card_pos.ne'
  · have he : g.range.map (powMonoidHom p) = ((⊤ : Subgroup A).map (powMonoidHom p)).map g := by
      ext x
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a ^ p, ⟨a, Subgroup.mem_top _, rfl⟩, by simp⟩
      · rintro ⟨_, ⟨a, -, rfl⟩, rfl⟩
        exact ⟨g a, ⟨a, rfl⟩, by simp⟩
    rw [he]
    intro h0
    have hd := Subgroup.relIndex_map_map g ((⊤ : Subgroup A).map (powMonoidHom p)) ⊤
    rw [← MonoidHom.range_eq_map g, h0, top_sup_eq] at hd
    have hdv : ((⊤ : Subgroup A).map (powMonoidHom p) ⊔ g.ker).relIndex ⊤ ∣
        ((⊤ : Subgroup A).map (powMonoidHom p)).relIndex ⊤ :=
      Subgroup.relIndex_dvd_of_le_left _ le_sup_left
    rw [← hd] at hdv
    exact h1 (Nat.eq_zero_of_zero_dvd hdv)

end GlobalTheory.CNorm
end

