module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactor
section
open scoped TensorProduct

namespace GlobalTheory

theorem sqloc_present : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  intro k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha
  classical
  choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))
  choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))
  set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨p, hp⟩ := ha x
    refine ⟨MvPolynomial.rename Sum.inr p, ?_⟩
    rw [hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    exact hp
  obtain ⟨u, hu⟩ := hΨsurj e
  set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef
  have hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | j
    · simp [hΨ, hκdef, hy]
    · simp [hΨ, hκdef, hh]
  have hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F) := by
    intro F
    have := congrArg (fun f => f F) hκ
    simpa using this
  let G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k :=
    Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i))
      (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))
  have hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p := by
    intro p
    rw [hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]
  have hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j := by
    intro j
    rw [hκdef, MvPolynomial.aeval_X, Sum.elim_inr]
  have hg'ker : ∀ i, φ (g' i) = 0 := by
    intro i
    have : g' i ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa using this
  have hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0 := by
    intro i
    rw [hκF]
    rcases i with i | j
    · simp only [G, Sum.elim_inl, hκr, hg'ker]
    · simp only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]
  have hΨuG : ∀ i, Ψ (u * G i) = 0 := by
    intro i
    have hm : Ψ (G i) ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul, hu, ← hc]
    have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hidem.eq, sub_self]
    calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
      _ = 0 := by rw [h0, mul_zero]
  refine ⟨s, y, fun i => u * G i, hΨuG, ?_⟩
  rw [← hΨ]
  intro F hF
  rw [RingHom.mem_ker] at hF

  have hFG : F ∈ Ideal.span (Set.range G) := by
    have hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp
        ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G)) := by
      apply MvPolynomial.algHom_ext
      intro i
      rcases i with i | j
      · simp only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl,
          MvPolynomial.rename_X]
      · simp only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        rw [← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    have h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := congrArg (fun f => f F) hq
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← neg_sub, neg_mem_iff]
      exact Ideal.Quotient.eq.mp this
    have hmem : κ F ∈ Ideal.span (Set.range g') := by
      rw [← hker, RingHom.mem_ker, ← hκF, hF, map_zero]
    have h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    have := Ideal.add_mem _ h1 h2
    simpa using this
  have hsplit : F = u * F + (1 - u) * F := by ring
  rw [hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hFG
    refine (Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · apply Ideal.mul_mem_mul
    · rw [RingHom.mem_ker]
      simp [hu, he]
    · exact hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeGtDvdEval
section
namespace GlobalTheory.PrimeDivisorOfPolynomialValue

open Polynomial

theorem exists_eval_mul_ne (f : ℤ[X]) (hf : 0 < f.natDegree) (c a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, f.eval (a * k) ≠ c ∧ f.eval (a * k) ≠ -c := by

  have hdeg : 0 < (f.comp (C a * X)).natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]
    exact hf
  have hne : ∀ b : ℤ, f.comp (C a * X) - C b ≠ 0 := fun b h => by
    rw [sub_eq_zero] at h
    rw [h, natDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
    ((f.comp (C a * X) - C c).roots.toFinset ∪ (f.comp (C a * X) - C (-c)).roots.toFinset)
  refine ⟨k, fun e => hk (Finset.mem_union_left _ ?_), fun e => hk (Finset.mem_union_right _ ?_)⟩
  · rw [Multiset.mem_toFinset, mem_roots (hne c)]
    simp [e]
  · rw [Multiset.mem_toFinset, mem_roots (hne (-c))]
    simp [e]

theorem exists_prime_gt_dvd_eval :
    ∀ (f : Polynomial ℤ), (0 : ℕ) < Polynomial.natDegree f → ∀ (n : ℕ),
      ∃ (p : ℕ), Nat.Prime p ∧ n < p ∧ ∃ (x : ℤ), (↑p : ℤ) ∣ Polynomial.eval x f := by
  intro f hf n

  have of_root : ∀ x, f.eval x = 0 → ∃ p, Nat.Prime p ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
    intro x hx
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, hp, hnp, x, by rw [hx]; exact dvd_zero _⟩
  by_cases h0 : f.eval 0 = 0
  · exact of_root 0 h0
  have hfac : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  obtain ⟨k, hk1, hk2⟩ := exists_eval_mul_ne f hf (f.eval 0) _ (mul_ne_zero h0 hfac)
  by_cases hx : f.eval (f.eval 0 * n.factorial * k) = 0
  · exact of_root _ hx

  obtain ⟨q, hq⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * n.factorial * k) 0 f
  have hft : f.eval (f.eval 0 * n.factorial * k) = f.eval 0 * (1 + n.factorial * k * q) := by
    linear_combination hq
  have ht1 : (1 + (n.factorial : ℤ) * k * q) ≠ 1 := fun h => hk1 (by rw [hft, h, mul_one])
  have ht2 : (1 + (n.factorial : ℤ) * k * q) ≠ -1 := fun h => hk2 (by rw [hft, h, mul_neg_one])
  have hnat : (1 + (n.factorial : ℤ) * k * q).natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.1 h with h | h
    · exact ht1 (by simpa using h)
    · exact ht2 (by simpa using h)
  have hp := Nat.minFac_prime hnat
  have hpt : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (1 + (n.factorial : ℤ) * k * q) :=
    Int.ofNat_dvd_left.2 (Nat.minFac_dvd _)
  refine ⟨_, hp, ?_, _, by rw [hft]; exact dvd_mul_of_dvd_right hpt _⟩

  by_contra hle
  rw [not_lt] at hle
  have h3 : ((1 + (n.factorial : ℤ) * k * q).natAbs.minFac : ℤ) ∣ (n.factorial : ℤ) * k * q :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos hle)) _) _
  have h4 := dvd_sub hpt h3
  rw [add_sub_cancel_right] at h4
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.1 (by simpa using h4))

end GlobalTheory.PrimeDivisorOfPolynomialValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveAnnihilator
section
open NumberField Matrix

namespace GlobalTheory.PrimAnnih

theorem exists_unit_coeff {W V ι : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [AddCommGroup V] [Module W V] [NoZeroSMulDivisors W V] [Fintype ι] (u : ι → V) (w : ι → W)
    (hw : w ≠ 0) (h : ∑ i, w i • u i = 0) :
    ∃ v : ι → W, (∃ i, IsUnit (v i)) ∧ ∑ i, v i • u i = 0 := by
  classical
  let I : Ideal W := Ideal.span (Set.range w)
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdvd : ∀ i, c ∣ w i := fun i => by
    have : w i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [hc] at this
    exact Ideal.mem_span_singleton.1 this
  choose v hv using hdvd
  have hcI : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw; funext i; rw [hv i, zero_mul]; rfl
  have hsum : ∑ i, a i * v i = 1 := by
    apply mul_left_cancel₀ hc0
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv i]; ring
  refine ⟨v, ?_, ?_⟩
  · by_contra hnu
    push_neg at hnu
    have h1 : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu i))
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · have h2 : c • ∑ i, v i • u i = 0 := by
      rw [Finset.smul_sum, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← hv i]
    exact (smul_eq_zero.1 h2).resolve_left hc0

theorem exists_vecMul_eq_zero {W Ω ι κ : Type} [CommRing W] [IsDomain W] [Field Ω] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : W →+* Ω) (hf : Function.Injective f)
    (A : Matrix ι κ W) (x : ι → Ω) (hx : x ≠ 0) (h : x ᵥ* A.map f = 0) :
    ∃ w : ι → W, w ≠ 0 ∧ w ᵥ* A = 0 := by
  classical
  by_contra H
  push_neg at H
  let L := FractionRing W
  let g : L →+* Ω := IsFractionRing.lift hf
  have hg : ∀ r, g (algebraMap W L r) = f r := fun r => IsFractionRing.lift_algebraMap hf r
  let AL : Matrix ι κ L := A.map (algebraMap W L)
  have hker : LinearMap.ker AL.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    obtain ⟨⟨c, hc⟩, hint⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors W) Finset.univ l
    choose w hw using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
    have hl' : l ᵥ* AL = 0 := hl
    have h1 : w ᵥ* A = 0 := by
      funext j
      apply IsFractionRing.injective W L
      rw [RingHom.map_vecMul, Pi.zero_apply, map_zero]
      have e : (algebraMap W L ∘ w) = fun i => algebraMap W L c * l i := by
        funext i; simpa [Algebra.smul_def] using hw i
      rw [e]
      have := congrFun hl' j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this ⊢
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero, AL]
    have hw0 : w = 0 := by
      by_contra hw0; exact H w hw0 h1
    funext i
    have e1 := hw i
    rw [hw0, Pi.zero_apply, map_zero, Algebra.smul_def] at e1
    have hc0 : algebraMap W L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact (mul_eq_zero.1 e1.symm).resolve_left hc0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective AL.vecMulLinear hker
  let P := LinearMap.toMatrix' G
  have hP : AL * P.transpose = 1 := by
    ext i j
    have := congrArg (fun φ => φ (Pi.single i 1) j) hG
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← LinearMap.toMatrix'_mulVec G] at this
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (if i = j then (1:L) else 0) = (Pi.single i (1:L) : ι → L) j by simp [Pi.single_apply, eq_comm], ← this]
    simp [Matrix.mulVec, dotProduct, P, mul_comm, Matrix.vecMulLinear_apply]
  have hAf : AL.map g = A.map f := by ext i j; simp [AL, hg]
  have hP' : A.map f * (P.transpose.map g) = 1 := by
    rw [← hAf, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero g) (map_one g)]
  apply hx
  rw [← Matrix.vecMul_one x, ← hP', ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

end GlobalTheory.PrimAnnih

namespace GlobalTheory.PrimAnnih

theorem exists_extend (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω]
    (σ : 𝓞 F →+* Ω) : ∃ σ' : F →ₐ[ℚ] Ω, ∀ a : 𝓞 F, σ' (algebraMap (𝓞 F) F a) = σ a := by
  have hk : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [Ideal.under_def, RingHom.comap_ker, show σ.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom Ω from
      RingHom.ext_int _ _]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot σ).2 hk
  exact ⟨(IsFractionRing.lift hinj : F →+* Ω).toRatAlgHom,
    fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_primitive_annihilator : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  intro F _ _ W Ω _ _ _ _ _ _ f hf n M σ hσ ι _ b
  classical
  let b' : Module.Basis ι ℚ F := Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) F b
  have hb' : ∀ i, b' i = algebraMap (𝓞 F) F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) F b i
  obtain ⟨σ', hσ'⟩ := exists_extend F Ω σ
  have hcard : Fintype.card ι = Fintype.card (F →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b']
  let q := Fintype.equivOfCardEq hcard
  let P := Algebra.embeddingsMatrixReindex ℚ Ω b' q
  have hPij : ∀ i j, P i j = q j (b' i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b' q
    intro h0
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at hd
    exact Algebra.discr_not_zero_of_basis ℚ b' hd
  have inj : ∀ z : ι → Ω, (∀ τ : F →ₐ[ℚ] Ω, ∑ i, z i * τ (b' i) = 0) → z = 0 := by
    intro z hz
    refine Matrix.eq_zero_of_vecMul_eq_zero hP (funext fun j => ?_)
    simpa [Matrix.vecMul, dotProduct, hPij] using hz (q j)
  let y : ι → Ω := fun j => if q j = σ' then 1 else 0
  let x : ι → Ω := y ᵥ* P⁻¹
  have hx : ∀ τ, ∑ i, x i * τ (b' i) = if τ = σ' then 1 else 0 := by
    intro τ
    have h1 : x ᵥ* P = y := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP),
        Matrix.vecMul_one]
    have := congrFun h1 (q.symm τ)
    simpa [Matrix.vecMul, dotProduct, hPij, y] using this

  let Φ : 𝓞 F →+* Matrix (Fin n) (Fin n) Ω := f.mapMatrix.comp M
  have hΦ : ∀ a, Φ a = (M a).map f := fun a => rfl
  have hcoef : ∀ (a : 𝓞 F) j, ∑ i, x i * (b.repr (a * b i) j : Ω) = σ a * x j := by
    intro a
    have hrep : ∀ i (τ : F →ₐ[ℚ] Ω), ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) =
        τ (algebraMap (𝓞 F) F a) * τ (b' i) := by
      intro i τ
      have e := congrArg (fun t : 𝓞 F => τ (algebraMap (𝓞 F) F t)) (b.sum_repr (a * b i))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, map_mul, zsmul_eq_mul] at e
      simpa [hb'] using e
    have := inj (fun j => ∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) (fun τ => by
      have key : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) =
          τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
        calc ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j)
            = ∑ j, ∑ i, x i * ((b.repr (a * b i) j : Ω) * τ (b' j)) := by
              simp only [Finset.sum_mul, mul_assoc]
          _ = ∑ i, x i * ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) := by
              rw [Finset.sum_comm]; simp only [Finset.mul_sum]
          _ = ∑ i, x i * (τ (algebraMap (𝓞 F) F a) * τ (b' i)) := by simp only [hrep]
          _ = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) * τ (b' j) =
          ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) -
            σ a * ∑ j, x j * τ (b' j) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      rw [e2, key, hx]
      split_ifs with hτ
      · subst hτ; rw [hσ']; ring
      · ring)
    intro j
    exact sub_eq_zero.1 (congrFun this j)
  let N : Matrix (Fin n) (Fin n) Ω := ∑ i, x i • Φ (b i)
  have hN : ∀ a, Φ a * N = σ a • N := by
    intro a
    calc Φ a * N = ∑ i, x i • Φ (a * b i) := by
          simp only [N, Finset.mul_sum, Matrix.mul_smul, map_mul]
      _ = ∑ i, x i • ∑ j, (b.repr (a * b i) j : Ω) • Φ (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (a * b i)]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) • Φ (b j) := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
      _ = ∑ j, (σ a * x j) • Φ (b j) := by simp only [hcoef]
      _ = σ a • N := by simp only [N, Finset.smul_sum, smul_smul]
  have hN0 : N = 0 := by
    ext j k
    have := hσ (fun j => N j k) (fun a => by
      funext r
      have e := congrFun (congrFun (hN a) r) k
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ] using e)
    simpa using congrFun this j
  let A : Matrix ι (Fin n × Fin n) W := Matrix.of fun i p => M (b i) p.1 p.2
  have hx0 : x ≠ 0 := by
    intro h0
    have := hx σ'
    simp [h0] at this
  have hxA : x ᵥ* A.map f = 0 := by
    funext p
    have := congrFun (congrFun hN0 p.1) p.2
    simpa [Matrix.vecMul, dotProduct, A, N, hΦ, Matrix.sum_apply, mul_comm] using this
  obtain ⟨w, hw0, hwA⟩ := exists_vecMul_eq_zero f hf A x hx0 hxA
  haveI : NoZeroSMulDivisors W (Matrix (Fin n) (Fin n) W) :=
    inferInstanceAs (NoZeroSMulDivisors W (Fin n → Fin n → W))
  refine exists_unit_coeff (fun i => M (b i)) w hw0 ?_
  ext j k
  have := congrFun hwA (j, k)
  simpa [Matrix.vecMul, dotProduct, A, Matrix.sum_apply, mul_comm] using this

end GlobalTheory.PrimAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdealOfIdempotent
section
open Matrix

namespace GlobalTheory

theorem range_idempotent_projective {A : Type} [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A)
    (hP : P * P = P) : Module.Projective A (LinearMap.range P.mulVecLin) := by
  refine Module.Projective.of_split (LinearMap.range P.mulVecLin).subtype P.mulVecLin.rangeRestrict ?_
  ext ⟨v, w, rfl⟩ j
  simp [Matrix.mulVec_mulVec, hP]

theorem exists_rank_ideal_of_idempotent : ∀ (A : Type) [CommRing A] (I : Type) [Fintype I] (n : ℕ) (P : I → Matrix (Fin n) (Fin n) A),
    (∀ i, P i * P i = P i) → ∀ (m : ℕ), ∃ x : A, ∀ (T : Type) [CommRing T] (f : A →+* T),
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : I),
          Module.rankAtStalk (LinearMap.range (P i).mulVecLin)
            (⟨RingHom.ker (h.comp f), RingHom.ker_isPrime _⟩ : PrimeSpectrum A) = m) ↔ f x = 0) := by
  intro A _ I _ n P hP m
  let V : Set (PrimeSpectrum A) :=
    ⋂ i, {q | Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m}
  have hV : IsClopen V := by
    refine isClopen_iInter_of_finite fun i => ?_
    have := range_idempotent_projective n (P i) (hP i)
    have := Module.finitePresentation_of_projective A (LinearMap.range (P i).mulVecLin)
    exact (Module.isLocallyConstant_rankAtStalk (R := A)
      (M := LinearMap.range (P i).mulVecLin)).isClopen_fiber m
  obtain ⟨e, x, hmul, hadd, hVe⟩ := PrimeSpectrum.isClopen_iff_mul_add.mp hV
  refine ⟨x, fun T _ f => ?_⟩
  have hmem : ∀ q : PrimeSpectrum A, q ∈ V ↔ e ∉ q.asIdeal := by
    intro q; rw [hVe]; rfl
  have hmem' : ∀ q : PrimeSpectrum A, q ∈ V ↔ ∀ i, Module.rankAtStalk (LinearMap.range (P i).mulVecLin) q = m := by
    intro q; simp [V]
  constructor
  · intro H
    have hxx : f x * f x = f x := by
      have : x * x = x := by
        have h1 : x = x * (e + x) := by rw [hadd, mul_one]
        calc x * x = x * (e + x) - x * e := by ring
          _ = x := by rw [← h1, mul_comm x e, hmul, sub_zero]
      rw [← map_mul, this]
    have hnil : IsNilpotent (f x) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
      intro (Q : Ideal T) hQ
      haveI : Q.IsPrime := hQ
      let k := AlgebraicClosure (FractionRing (T ⧸ Q))
      let h : T →+* k := (algebraMap (FractionRing (T ⧸ Q)) k).comp
        ((algebraMap (T ⧸ Q) (FractionRing (T ⧸ Q))).comp (Ideal.Quotient.mk Q))
      have hker : RingHom.ker h = Q := by
        ext t
        simp only [h, RingHom.mem_ker, RingHom.comp_apply]
        rw [map_eq_zero_iff _ (algebraMap (FractionRing (T ⧸ Q)) k).injective,
          IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      have hq := (hmem _).mp ((hmem' _).mpr (H k h))
      have : e * x ∈ RingHom.ker (h.comp f) := by rw [hmul]; exact Ideal.zero_mem _
      rcases (RingHom.ker_isPrime (h.comp f)).mem_or_mem this with he | hx
      · exact absurd he hq
      · rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker] at hx
        exact hx
    obtain ⟨N, hN⟩ := hnil
    have : ∀ j : ℕ, f x ^ (j + 1) = f x := by
      intro j; induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, ih, hxx]
    rcases N with _ | N
    · simp at hN; exact (subsingleton_of_zero_eq_one hN.symm).elim _ _
    · rw [this] at hN; exact hN
  · intro hx k _ _ h i
    refine ((hmem' _).mp ?_) i
    rw [hmem]
    show e ∉ RingHom.ker (h.comp f)
    rw [RingHom.mem_ker, RingHom.comp_apply]
    have : f e = 1 := by
      have := congrArg f hadd
      rw [map_add (f := _), hx, add_zero, map_one] at this; exact this
    rw [this, map_one]; exact one_ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
section
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.PinchLift

def Glues {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z) : Prop :=
  ∀ (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
    (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
    ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b

end GlobalTheory.PinchLift
end

