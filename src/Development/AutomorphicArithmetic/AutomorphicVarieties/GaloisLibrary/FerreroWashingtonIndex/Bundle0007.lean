module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ClassGroupDivMemOfMulConjEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem quotient_mem_of_norm_eq_involution {M C : Type} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [Subsingleton Mˣ]
    [CommGroup C] (σ : M ≃* M) (hσ : ∀ x, σ (σ x) = x) (H : Subgroup C) (f : M → C)
    (hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b) (hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ H) (I : M) :
    I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun I => I ≠ 0 → ∀ J : M, J ≠ 0 → I * σ I = J * σ J → f I / f J ∈ H) I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx _ J _ hxJ
    rw [isUnit_iff_eq_one] at hx
    subst hx
    rw [map_one, mul_one] at hxJ
    have hJ1 : J = 1 := isUnit_iff_eq_one.mp (Units.mkOfMulEqOne J (σ J) hxJ.symm).isUnit
    subst hJ1
    rw [div_self']
    exact H.one_mem
  · intro a p ha hp ih _ J hJ hE
    have h0 : σ 0 = 0 := by
      have h := map_mul σ 0 (σ.symm 0)
      rwa [zero_mul, MulEquiv.apply_symm_apply, mul_zero] at h
    have hne : ∀ x : M, x ≠ 0 → σ x ≠ 0 := by
      intro x hx h
      apply hx
      rw [← hσ x, h, h0]
    have hp0 : p ≠ 0 := hp.ne_zero
    have hsp0 := hne p hp0
    have hd : p ∣ J * σ J := hE ▸ dvd_mul_of_dvd_left (dvd_mul_right p a) _
    rw [map_mul] at hE
    rcases hp.dvd_or_dvd hd with ⟨J₀, rfl⟩ | ⟨K₀, hK⟩
    · have hJ0 : J₀ ≠ 0 := right_ne_zero_of_mul hJ
      rw [map_mul] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (J₀ * σ J₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      rw [hf p a hp0 ha, hf p J₀ hp0 hJ0, mul_div_mul_left_eq_div]
      exact ih ha J₀ hJ0 e2
    · have hsJ := hne J hJ
      have hK0 : K₀ ≠ 0 := by
        rw [hK] at hsJ
        exact right_ne_zero_of_mul hsJ
      have hsK0 := hne K₀ hK0
      have hJ' : J = σ p * σ K₀ := by rw [← hσ J, hK, map_mul]
      rw [hK, hJ'] at hE
      have e1 : (p * σ p) * (a * σ a) = (p * σ p) * (K₀ * σ K₀) := by
        simpa only [mul_comm, mul_assoc, mul_left_comm] using hE
      have e2 := mul_left_cancel₀ (mul_ne_zero hp0 hsp0) e1
      have key := H.mul_mem (hH p hp0) (H.mul_mem (ih ha K₀ hK0 e2) (hH K₀ hK0))
      rw [div_mul_div_cancel, div_mul_div_comm] at key
      rw [hJ', hf p a hp0 ha, hf (σ p) (σ K₀) hsp0 hsK0]
      exact key

theorem UpperTheory.V.FW.classGroup_div_mem_of_mul_conj_eq :
    ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K) (I J : (Ideal (𝓞 K))⁰), (∀ x, τ (τ x) = x) → I * idMap τ I = J * idMap τ J → ClassGroup.mk0 I / ClassGroup.mk0 J ∈ difR (clMap τ) := by
  intro K _ _ τ I J hτ hIJ
  classical
  have hee : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv τ (RingOfIntegers.mapRingEquiv τ x) = x :=
    fun x => RingOfIntegers.ext (hτ x)
  have hmap : ∀ I : Ideal (𝓞 K), Ideal.map (RingOfIntegers.mapRingEquiv τ)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ) I) = I := by
    intro I
    show Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K) I) = I
    rw [Ideal.map_map]
    convert Ideal.map_id I
    exact RingHom.ext fun x => hee x
  let σ : Ideal (𝓞 K) ≃* Ideal (𝓞 K) :=
    { toFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      invFun := Ideal.map (RingOfIntegers.mapRingEquiv τ)
      left_inv := hmap
      right_inv := hmap
      map_mul' := Ideal.map_mul (RingOfIntegers.mapRingEquiv τ) }
  let f : Ideal (𝓞 K) → ClassGroup (𝓞 K) := fun a =>
    if h : a ∈ (Ideal (𝓞 K))⁰ then ClassGroup.mk0 ⟨a, h⟩ else 1
  have hfv : ∀ a (h : a ∈ (Ideal (𝓞 K))⁰), f a = ClassGroup.mk0 ⟨a, h⟩ := fun a h => dif_pos h
  have hf : ∀ a b, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b := by
    intro a b ha hb
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hb' := mem_nonZeroDivisors_of_ne_zero hb
    rw [hfv a ha', hfv b hb', hfv (a * b) (Submonoid.mul_mem _ ha' hb'), ← map_mul]
    rfl
  have hH : ∀ a, a ≠ 0 → f a / f (σ a) ∈ difR (clMap τ) := by
    intro a ha
    have ha' := mem_nonZeroDivisors_of_ne_zero ha
    have hs' : σ a ∈ (Ideal (𝓞 K))⁰ := (idMap τ ⟨a, ha'⟩).2
    rw [hfv a ha', hfv _ hs']
    refine ⟨ClassGroup.mk0 ⟨a, ha'⟩, ?_⟩
    rw [MonoidHom.div_apply, MonoidHom.id_apply, class_map_mk0]
    rfl
  have key := quotient_mem_of_norm_eq_involution σ (fun x => hmap x) (difR (clMap τ)) f hf hH (I : Ideal (𝓞 K))
    (nonZeroDivisors.coe_ne_zero I) J (nonZeroDivisors.coe_ne_zero J) (congrArg Subtype.val hIJ)
  rwa [hfv _ I.2, hfv _ J.2] at key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ConjEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.conjEq :
    ∀ (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L] [IsCMField L], (sg M L (-1)).toRingEquiv = cE L ∧ clA M L (-1) = clMap (cE L) := by
  intro M _ L _ _ _ _
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta M ℚ L) M :=
    IsCyclotomicExtension.zeta_spec M ℚ L
  set ζ := IsCyclotomicExtension.zeta M ℚ L
  have h1 : sg M L (-1) ζ = ζ⁻¹ := by
    rw [sg_apply M L _ hζ.pow_eq_one]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    simp
  have h2 : cE L ζ = ζ⁻¹ := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    refine eq_inv_of_mul_eq_one_left ?_
    apply φ.injective
    have hz : ‖φ ζ‖ = 1 := (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne M)
    rw [map_mul, map_one, cE]
    simp only [NumberField.IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj,
      AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [Complex.conj_mul', hz]
    simp
  have hc : sg M L (-1) = AlgEquiv.ofRingEquiv (f := cE L) (fun q => by simp) := by
    apply AlgEquiv.coe_algHom_injective
    apply (hζ.powerBasis ℚ).algHom_ext
    simp only [IsPrimitiveRoot.powerBasis_gen, AlgEquiv.coe_algHom]
    rw [h1]
    exact h2.symm
  have key : (sg M L (-1)).toRingEquiv = cE L := by
    rw [hc]
    ext x
    rfl
  refine ⟨key, ?_⟩
  rw [clA, ← map_inv, inv_neg_one, key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.embCyc :
    ∀ (N m M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {m} K K'] (L : Type) [Field L] [NumberField L] [Algebra K' L] [IsCyclotomicExtension {M} K' L], N ∣ M → m ∣ M → Nonempty (K →ₐ[ℚ] CyclotomicField N ℚ) → IsCyclotomicExtension {M} ℚ L := by
  intro N m M _ K _ _ _ K' _ _ _ _ L _ _ _ _ hNM hmM hφ
  obtain ⟨φ⟩ := hφ
  have hM0 : M ≠ 0 := NeZero.ne M
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM0 (zero_dvd_iff.mp hNM)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K' L (Set.mem_singleton M) hM0
  let F : Subalgebra ℚ L := Algebra.adjoin ℚ {ζ}
  have hroot : ∀ x : L, ∀ k : ℕ, k ∣ M → x ^ k = 1 → x ∈ F := by
    intro x k hk hx
    have hxM : x ^ M = 1 := by
      obtain ⟨j, hj⟩ := hk
      rw [hj, pow_mul, hx, one_pow]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hxM
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have hpN : IsPrimitiveRoot (ζ ^ (M / N)) N := by
    have := hζ.pow_of_dvd (p := M / N) ?_ (Nat.div_dvd_of_dvd hNM)
    · rwa [Nat.div_div_self hNM hM0] at this
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hNM) (Nat.pos_of_ne_zero hN0)).ne'
  have hsp : Polynomial.Splits ((Polynomial.X ^ N - 1 : Polynomial ℚ).map (algebraMap ℚ L)) := by
    simpa using Polynomial.X_pow_sub_one_splits hpN
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ (CyclotomicField N ℚ)
  let ψ : CyclotomicField N ℚ →ₐ[ℚ] L :=
    Polynomial.IsSplittingField.lift (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) hsp
  have h1 : ∀ y, ψ y ∈ F := by
    intro y
    have hy := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) y
    have hle : Algebra.adjoin ℚ {b : CyclotomicField N ℚ | ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}
        ≤ F.comap ψ := by
      rw [Algebra.adjoin_le_iff]
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hb
      exact hroot (ψ b) N hNM (by rw [← map_pow, hb, map_one])
    exact hle hy
  have h2 : ∀ k : K, algebraMap K' L (algebraMap K K' k) ∈ F := by
    intro k
    let e1 : K →ₐ[ℚ] L := ((algebraMap K' L).comp (algebraMap K K')).toRatAlgHom
    let e2 : K →ₐ[ℚ] L := ψ.comp φ
    let g := e2.equivFieldRange
    haveI := Normal.of_algEquiv g
    have hr := AlgHom.fieldRange_of_normal (e1.comp g.symm.toAlgHom)
    have hk : e1 k ∈ e2.fieldRange := by
      rw [← hr]
      exact AlgHom.mem_fieldRange.mpr ⟨g k, by simp⟩
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hk
    show e1 k ∈ F
    rw [← hy]
    exact h1 (φ y)
  have h3 : ∀ x : K', algebraMap K' L x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {m}) (A := K) x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ m hmM (by rw [← map_pow, hbn, map_one])
    | algebraMap k => exact h2 k
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  have h4 : ∀ x : L, x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {M}) (A := K') x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ M dvd_rfl hbn
    | algebraMap k => exact h3 k
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => Algebra.adjoin_mono ?_ (h4 x)⟩
  rintro _ rfl
  exact hζ.pow_eq_one
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.IneCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem iC_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem iC_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem iC_eta {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => iC_pow A (iC_one A hm hη) h i

private theorem iC_ine (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) (g : G F Ω)
    (hg : g ∈ Ine (F := F) A) (k : ℕ) (ζ : Ω) (hζ : ζ ^ l ^ k = 1) : g ζ = ζ := by
  have hm : l ^ k ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  have hv := iC_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).2 (natCast_mem A l)) (not_lt.1 hA)
  have hA' : ¬ A.valuation ((l ^ k : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]; exact lt_irrefl _
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine iC_eta A hm hA' (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, hv, div_one]; exact hg.2 ζ hv.le
  exact (div_eq_one_iff_eq h0).1 this

theorem UpperTheory.V.FW.ineCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) [IsCyclotomicExtension {l ^ n} F K] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 → Ine (F := F) A ≤ galOf F K Ω := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ n hc A hA g hg x
  have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := F) (B := K) x
  show g (algebraMap K Ω x) = algebraMap K Ω x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨m, hm, -, hy⟩ := hy
    obtain rfl : m = l ^ n := hm
    exact iC_ine F Ω l A hA g hg n _ (by rw [← map_pow, hy, map_one])
  | algebraMap r => rw [← IsScalarTower.algebraMap_apply]; exact g.commutes r
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RealGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem real_eq_one_of_nonneg_of_mul_self_eq_one (x : ℝ) (h0 : 0 ≤ x) (h : x * x = 1) : x = 1 := by
  nlinarith

theorem UpperTheory.V.FW.realGen :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (x : Cl K), Function.Surjective (IsCMField.unitsMulComplexConjInv K) → x ∈ minK (clMap (cE K)) → ∃ (I : (Ideal (𝓞 K))⁰) (a : 𝓞 K), ClassGroup.mk0 I = x ∧ a ≠ 0 ∧ cE K (a : K) = a ∧ (I * idMap (cE K) I).1 = Ideal.span {a} := by
  intro K _ _ _ x hsurj hx
  set σ := RingOfIntegers.mapRingEquiv (cE K) with hσdef
  have hσK : ∀ y : 𝓞 K, ((σ y : 𝓞 K) : K) = cE K (y : K) := fun y => rfl
  have hσσ : ∀ y : 𝓞 K, σ (σ y) = y := fun y => by
    apply RingOfIntegers.ext
    rw [hσK, hσK]
    exact IsCMField.complexConj_apply_apply K (y : K)
  have hw : ∀ (w : InfinitePlace K) (y : 𝓞 K), w (σ y : K) = w (y : K) := fun w y =>
    IsCMField.infinitePlace_complexConj K w (y : K)
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  set J := idMap (cE K) I with hJdef
  have hJ : (J : Ideal (𝓞 K)) = Ideal.map σ (I : Ideal (𝓞 K)) := rfl
  have hmapmap : ∀ A : Ideal (𝓞 K), Ideal.map σ (Ideal.map σ A) = A := by
    intro A
    show Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.map (σ : 𝓞 K →+* 𝓞 K) A) = A
    rw [Ideal.map_map]
    have : (σ : 𝓞 K →+* 𝓞 K).comp (σ : 𝓞 K →+* 𝓞 K) = RingHom.id _ :=
      RingHom.ext fun y => hσσ y
    rw [this, Ideal.map_id]
  have hJJ : Ideal.map σ (J : Ideal (𝓞 K)) = I := by
    rw [hJ, hmapmap]
  have hprin : Submodule.IsPrincipal ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) := by
    rw [← ClassGroup.mk0_eq_one_iff (I * J).2]
    have := hx
    simp only [minK, MonoidHom.mem_ker, MonoidHom.mul_apply, class_map_mk0, MonoidHom.id_apply] at this
    rw [← map_mul, mul_comm] at this
    exact this
  obtain ⟨b, hb⟩ := hprin
  have hb' : ((I * J : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = Ideal.span {b} := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hb'
    exact nonZeroDivisors.coe_ne_zero (I * J) hb'
  have hspan : Ideal.span {σ b} = Ideal.span {b} := by
    rw [← Set.image_singleton, ← Ideal.map_span, ← hb', Submonoid.coe_mul, Ideal.map_mul, ← hJ,
      hJJ, mul_comm]
  obtain ⟨t, ht⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hσt : σ (t : 𝓞 K) * t = 1 := by
    have h1 := congrArg σ ht
    rw [map_mul, hσσ] at h1
    have : b * (σ t * t) = b * 1 := by
      rw [← mul_assoc, h1, ht, mul_one]
    exact mul_left_cancel₀ hb0 this
  have htor : t⁻¹ ∈ Units.torsion K := by
    refine inv_mem ?_
    rw [Units.mem_torsion]
    intro w
    show w ((t : 𝓞 K) : K) = 1
    have hK : ((σ t : 𝓞 K) : K) * ((t : 𝓞 K) : K) = 1 := by
      exact_mod_cast congrArg (fun y : 𝓞 K => (y : K)) hσt
    have hprod := congrArg w hK
    rw [map_mul, map_one, hw] at hprod
    exact real_eq_one_of_nonneg_of_mul_self_eq_one _ (AbsoluteValue.nonneg _ _) hprod
  obtain ⟨v, hv⟩ := hsurj ⟨t⁻¹, htor⟩
  have hv2 : v * ((IsCMField.unitsComplexConj K) v)⁻¹ = t⁻¹ := by
    have hv1 := congrArg Subtype.val hv
    rw [IsCMField.unitsMulComplexConjInv_apply] at hv1
    exact hv1
  rw [mul_inv_eq_iff_eq_mul] at hv2
  have hv' : (v : 𝓞 K) = ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σ v := by
    have h3 := congrArg Units.val hv2
    rw [Units.val_mul] at h3
    exact h3
  have hσb : σ b = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    calc σ b = σ b * t * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = b * ((t⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [ht]
  refine ⟨I, b * v, rfl, mul_ne_zero hb0 v.ne_zero, ?_, ?_⟩
  · rw [← hσK]
    congr 1
    rw [map_mul, hσb, mul_assoc, ← hv']
  · rw [Ideal.span_singleton_mul_right_unit v.isUnit]
    exact hb'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RelCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem UpperTheory.V.FW.relCyc_compat {m N : ℕ} [NeZero m] [NeZero N] (h : m ∣ N) (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C]
    (i : K →ₐ[ℚ] C) (a : (ZMod N)ˣ) (x : K) :
    sg N C a (i x) = i (sg m K (ZMod.unitsMap h a) x) := by
  have hz := IsCyclotomicExtension.zeta_spec m ℚ K
  have key : ((sg N C a : C →ₐ[ℚ] C)).comp i = i.comp (sg m K (ZMod.unitsMap h a) : K →ₐ[ℚ] K) := by
    apply (hz.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    set z := IsCyclotomicExtension.zeta m ℚ K
    have h1 : z ^ m = 1 := hz.pow_eq_one
    have h2 : (i z) ^ m = 1 := by rw [← map_pow, h1, map_one]
    have h3 : (i z) ^ N = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, h2, one_pow]
    change sg N C a (i z) = i (sg m K (ZMod.unitsMap h a) z)
    rw [sg_apply N C a h3, sg_apply m K _ h1, map_pow]
    have : ((ZMod.unitsMap h a : (ZMod m)ˣ) : ZMod m).val = (a : ZMod N).val % m := by
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [this]
    exact pow_eq_pow_mod _ h2
  exact DFunLike.congr_fun key x

theorem UpperTheory.V.FW.relCyc :
    ∀ (l f e n : ℕ) [NeZero (f * l ^ n)] (h : f * l ^ e ∣ f * l ^ n) (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {f * l ^ e} ℚ F] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L], f.Coprime l → ∃ _ : Algebra F L, IsCyclotomicExtension {l ^ n} F L ∧ (∀ σ : Gal(L/F), ∃ t ∈ (ZMod.unitsMap h).ker, σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv) ∧ ∀ t ∈ (ZMod.unitsMap h).ker, ∃ σ : Gal(L/F), σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv := by
  intro l f e n _ h F _ _ _ L _ _ _ hfl
  have hM : 0 < f * l ^ n := NeZero.pos _
  have hM0 : 0 < f * l ^ e := Nat.pos_of_dvd_of_pos h hM
  haveI : NeZero (f * l ^ e) := ⟨hM0.ne'⟩
  have hf : 0 < f := Nat.pos_of_mul_pos_right hM
  have hln : 0 < l ^ n := Nat.pos_of_mul_pos_left hM
  haveI : NeZero (l ^ n) := ⟨hln.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec (f * l ^ n) ℚ L
  set ζ := IsCyclotomicExtension.zeta (f * l ^ n) ℚ L
  have hz := IsCyclotomicExtension.zeta_spec (f * l ^ e) ℚ F
  set z := IsCyclotomicExtension.zeta (f * l ^ e) ℚ F with hzdef
  obtain ⟨k, hk⟩ := id h
  have hk' : l ^ n = k * l ^ e := by
    apply Nat.eq_of_mul_eq_mul_left hf
    rw [hk]; ring
  obtain ⟨i, hi⟩ : ∃ i : F →ₐ[ℚ] L, i z = ζ ^ k := by
    have hξ : IsPrimitiveRoot (ζ ^ k) (f * l ^ e) := hζ.pow hM (by rw [hk, mul_comm])
    refine ⟨(hz.powerBasis ℚ).lift (ζ ^ k) ?_, ?_⟩
    · rw [IsPrimitiveRoot.powerBasis_gen, ← Polynomial.cyclotomic_eq_minpoly_rat hz hM0,
        Polynomial.cyclotomic_eq_minpoly_rat hξ hM0]
      exact minpoly.aeval ℚ _
    · exact (congrArg _ (IsPrimitiveRoot.powerBasis_gen ℚ hz).symm).trans ((hz.powerBasis ℚ).lift_gen (ζ ^ k) _)
  letI : Algebra F L := i.toRingHom.toAlgebra
  have hal : ∀ x, algebraMap F L x = i x := fun _ => rfl
  refine ⟨this, ?_, ?_, ?_⟩
  · have hη : IsPrimitiveRoot (ζ ^ f) (l ^ n) := hζ.pow hM rfl
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hη⟩, fun x => ?_⟩
    set A := Algebra.adjoin F {b : L | b ^ l ^ n = 1}
    have h1 : ζ ^ f ∈ A := Algebra.subset_adjoin hη.pow_eq_one
    have h2 : ζ ^ l ^ n ∈ A := by
      rw [hk', pow_mul, ← hi, ← hal]
      exact A.pow_mem (A.algebraMap_mem z) _
    have h3 : ζ ∈ A := by
      have hc : Nat.Coprime f (l ^ n) := hfl.pow_right n
      have hc' : Nat.Coprime (f + l ^ n) (f * l ^ n) :=
        Nat.Coprime.mul_right (by simpa using hc.symm) (by simpa using hc)
      obtain ⟨a, -, ha⟩ := (hζ.pow_of_coprime _ hc').eq_pow_of_pow_eq_one hζ.pow_eq_one
      rw [← ha, pow_add]
      exact A.pow_mem (A.mul_mem h1 h2) a
    have h4 : Algebra.adjoin ℚ {ζ} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    have h5 : x ∈ Algebra.adjoin ℚ {ζ} := h4 ▸ Algebra.mem_top
    have h6 : Algebra.adjoin ℚ {ζ} ≤ A.restrictScalars ℚ := Algebra.adjoin_le (by simpa using h3)
    exact h6 h5
  · intro σ
    obtain ⟨t, ht⟩ := (sg (f * l ^ n) L).surjective (σ.restrictScalars ℚ)
    refine ⟨t, ?_, by rw [ht]; rfl⟩
    rw [MonoidHom.mem_ker, ← map_eq_one_iff _ (sg (f * l ^ e) F).injective]
    ext y
    apply i.injective
    have := relCyc_compat h F L i t y
    rw [ht] at this
    exact this.symm.trans (σ.commutes y)
  · intro t ht
    refine ⟨{ (sg (f * l ^ n) L t).toRingEquiv with commutes' := fun y => ?_ }, rfl⟩
    have := relCyc_compat h F L i t y
    rw [MonoidHom.mem_ker.1 ht, map_one] at this
    exact this
end

