module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.DiffAtOddSt
section
noncomputable section

open NumberField UniqueFactorizationMonoid

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

def DiffExpSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (ℓ a m : ℕ), ℓ.Prime → ¬ ℓ ∣ m →
    (discr E).natAbs = ℓ ^ a * m →
    ∀ P : Ideal (𝓞 E), P.IsPrime → (ℓ : 𝓞 E) ∈ P →
      (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E =
        a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Polynomial

section Split

variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]

def IsEigV (ρ : O →+* Module.End S M) (χ : O →+* K) (m : M) : Prop := ∀ a, ρ a m = algebraMap K S (χ a) • m

theorem pow_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (n : ℕ) : (f ^ n) m = x ^ n • m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hm, smul_smul, pow_succ]

theorem aeval_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : ℤ[X]) :
    aeval f P m = aeval x P • m := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, pow_eig f hm, smul_assoc]

theorem aevalS_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : S[X]) :
    aeval f P m = aeval x P • m := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, pow_eig f hm, smul_assoc]

def lagr (x : ι → K) (τ : ι) : K[X] := Lagrange.basis Finset.univ x τ

theorem X_sub_mul_lagr (x : ι → K) (hx : Function.Injective x) (τ : ι) :
    (X - C (x τ)) * lagr x τ = C (∏ τ' ∈ Finset.univ.erase τ, (x τ - x τ')⁻¹) * ∏ τ', (X - C (x τ')) := by
  unfold lagr
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib]
  rw [← map_prod, ← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (x τ')) (Finset.mem_univ τ)]
  ring

theorem sum_lagr (x : ι → K) (hx : Function.Injective x) [Nonempty ι] : ∑ τ, lagr x τ = 1 :=
  Lagrange.sum_basis hx.injOn Finset.univ_nonempty

theorem eval_lagr (x : ι → K) (hx : Function.Injective x) (τ τ' : ι) :
    (lagr x τ).eval (x τ') = if τ = τ' then 1 else 0 := by
  unfold lagr
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self hx.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ _)

end Split

section Split2

variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)

def proj (τ : ι) : Module.End S M := aeval (ρ α) ((lagr (fun τ => χ τ α) τ).map (algebraMap K S))

theorem sum_proj [Nonempty ι] (hα : Function.Injective fun τ => χ τ α) : ∑ τ, proj ρ χ α τ = 1 := by
  have h := sum_lagr (fun τ => χ τ α) hα
  calc ∑ τ, proj ρ χ α τ
      = aeval (ρ α) ((∑ τ, lagr (fun τ => χ τ α) τ).map (algebraMap K S)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [proj, Polynomial.map_sum, map_sum]
    _ = 1 := by rw [h, Polynomial.map_one, map_one]

theorem proj_eig_alpha (hα : Function.Injective fun τ => χ τ α) (f : ℤ[X]) (hf : aeval α f = 0)
    (hfs : f.map (Int.castRingHom K) = ∏ τ, (X - C (χ τ α))) (τ : ι) (m : M) :
    ρ α (proj ρ χ α τ m) = algebraMap K S (χ τ α) • proj ρ χ α τ m := by
  have hk := congrArg (Polynomial.map (algebraMap K S)) (X_sub_mul_lagr (fun τ => χ τ α) hα τ)
  rw [← hfs] at hk
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_map] at hk
  have hz : aeval (ρ α) (f.map ((algebraMap K S).comp (Int.castRingHom K))) = 0 := by
    rw [show (algebraMap K S).comp (Int.castRingHom K) = algebraMap ℤ S from RingHom.ext_int _ _,
      aeval_map_algebraMap]
    have e : aeval (ρ α) f = ρ (aeval α f) := aeval_algHom_apply ρ.toIntAlgHom α f
    rw [e, hf, map_zero]
  have h1 := congrArg (aeval (ρ α)) hk
  rw [map_mul, map_mul, hz, mul_zero, map_sub, aeval_X, aeval_C] at h1
  have h2 := congrArg (fun g : Module.End S M => g m) h1
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    LinearMap.zero_apply] at h2
  unfold proj
  exact sub_eq_zero.mp h2

theorem eig_of_alpha (hN : ∀ a : O, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : O) * a = aeval α g) (τ : ι) {m : M}
    (hm : ρ α m = algebraMap K S (χ τ α) • m) : IsEigV ρ (χ τ) m := by
  intro a
  obtain ⟨N, g, hN0, hg⟩ := hN a
  have h1 := aeval_eig (ρ α) hm g
  have hL : aeval (ρ α) g = ρ (aeval α g) := aeval_algHom_apply ρ.toIntAlgHom α g
  have hR : aeval (algebraMap K S (χ τ α)) g = algebraMap K S (χ τ (aeval α g)) :=
    aeval_algHom_apply ((algebraMap K S).comp (χ τ)).toIntAlgHom α g
  rw [hL, hR, ← hg, map_mul, map_mul, map_intCast, map_intCast, map_mul, map_intCast,
    Module.End.mul_apply, mul_smul] at h1
  have hNK : (N : K) ≠ 0 := Int.cast_ne_zero.mpr hN0

  have cancel : ∀ y : M, algebraMap K S ((N : K)⁻¹) • ((N : S) • y) = y := by
    intro y
    rw [smul_smul, ← map_intCast (algebraMap K S) N, ← map_mul, inv_mul_cancel₀ hNK, map_one, one_smul]
  have hE : ((N : Module.End S M) (ρ a m)) = (N : S) • ρ a m := by
    rw [Int.cast_smul_eq_zsmul S N (ρ a m)]
    simp
  rw [hE] at h1
  rw [← cancel (ρ a m), h1, cancel]

theorem proj_sum_eig (hα : Function.Injective fun τ => χ τ α) (mm : ι → M)
    (hmm : ∀ τ, IsEigV ρ (χ τ) (mm τ)) (τ : ι) : proj ρ χ α τ (∑ τ', mm τ') = mm τ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have key : ∀ τ', proj ρ χ α τ (mm τ') = if τ = τ' then mm τ' else 0 := by
    intro τ'
    have hm := hmm τ' α
    unfold proj
    rw [aevalS_eig (ρ α) hm, aeval_map_algebraMap, aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval,
      eval_lagr (fun τ => χ τ α) hα]
    split_ifs <;> simp
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Split2

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open Polynomial NumberField IntermediateField Module

theorem exists_sepElt {E : Type} [Field E] [NumberField E] {F : Type} [Field F] (j : F →+* ℂ)
    (χ : (E →+* ℂ) → (𝓞 E →+* F)) (hχ : ∀ τ a, j (χ τ a) = τ (a : E)) :
    ∃ α : 𝓞 E, Function.Injective (fun τ => χ τ α) ∧
      (∃ f : ℤ[X], aeval α f = 0 ∧ f.map (Int.castRingHom F) = ∏ τ, (X - C (χ τ α))) ∧
      ∀ a : 𝓞 E, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : 𝓞 E) * a = aeval α g := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ ({θ} : Finset E)
  have hint : IsIntegral ℤ (y • θ) := hyi θ (Finset.mem_singleton_self θ)
  let α : 𝓞 E := ⟨y • θ, hint⟩
  have hintα : IsIntegral ℤ ((α : 𝓞 E) : E) := hint
  have hαE : ((α : 𝓞 E) : E) = (y : E) * θ := by simp [α, zsmul_eq_mul]

  have htop : ℚ⟮((α : 𝓞 E) : E)⟯ = ⊤ := by
    rw [eq_top_iff, ← hθ, adjoin_simple_le_iff]
    have hy : (y : E) ≠ 0 := Int.cast_ne_zero.2 hy0
    have : θ = ((y : ℚ)⁻¹ : ℚ) • ((α : 𝓞 E) : E) := by
      rw [hαE, Rat.smul_def, ← mul_assoc, Rat.cast_inv, Rat.cast_intCast, inv_mul_cancel₀ hy, one_mul]
    rw [this]
    exact smul_mem _ (mem_adjoin_simple_self ℚ _)
  have hintQ : IsIntegral ℚ ((α : 𝓞 E) : E) := .of_finite ℚ _
  have hadj : Algebra.adjoin ℚ {((α : 𝓞 E) : E)} = ⊤ := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, htop]
    rfl
  have hinj : Function.Injective (fun τ => χ τ α) := by
    intro τ τ' h
    have h' : τ ((α : 𝓞 E) : E) = τ' ((α : 𝓞 E) : E) := by
      rw [← hχ, ← hχ]; exact congrArg j h
    have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by intro z hz; rw [Set.mem_singleton_iff.1 hz]; exact h')
    exact RingHom.ext fun z => congrArg (fun φ : E →ₐ[ℚ] ℂ => φ z) this
  have hinjE : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective (𝓞 E) E
  refine ⟨α, hinj, ⟨minpoly ℤ ((α : 𝓞 E) : E), ?_, ?_⟩, ?_⟩
  · apply hinjE
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact minpoly.aeval ℤ _
  · have hp : (∏ τ, (X - C (χ τ α))).Monic := Polynomial.monic_prod_X_sub_C _ _
    have hq : ((minpoly ℤ ((α : 𝓞 E) : E)).map (Int.castRingHom F)).Monic := (minpoly.monic hintα).map _
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq ?_ ?_
    · refine Finset.prod_dvd_of_coprime (fun τ _ τ' _ h => Polynomial.pairwise_coprime_X_sub_C hinj h)
        fun τ _ => Polynomial.dvd_iff_isRoot.2 ?_
      have hχa : aeval (χ τ α) (minpoly ℤ ((α : 𝓞 E) : E)) = χ τ (aeval α (minpoly ℤ ((α : 𝓞 E) : E))) :=
        Polynomial.aeval_algHom_apply (χ τ).toIntAlgHom α _
      have h0 : aeval α (minpoly ℤ ((α : 𝓞 E) : E)) = 0 := by
        apply hinjE
        rw [← Polynomial.aeval_algebraMap_apply, map_zero]
        exact minpoly.aeval ℤ _
      rw [Polynomial.IsRoot, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def, hχa, h0, map_zero]
    · rw [(minpoly.monic hintα).natDegree_map, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ,
        NumberField.Embeddings.card E ℂ, ← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hintQ,
        minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintα, (minpoly.monic hintα).natDegree_map]
  · intro a
    have ha : ((a : 𝓞 E) : E) ∈ Algebra.adjoin ℚ {((α : 𝓞 E) : E)} := by rw [hadj]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨r, hr⟩ := ha
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) r
    refine ⟨(b : ℤ), IsLocalization.integerNormalization (nonZeroDivisors ℤ) r,
      nonZeroDivisors.coe_ne_zero ⟨b, hb.1⟩, ?_⟩
    apply hinjE
    have hr' : aeval (algebraMap (𝓞 E) E α) r = algebraMap (𝓞 E) E a := hr
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap ℚ, hb.2, map_zsmul, hr', map_mul,
      map_intCast, zsmul_eq_mul]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
section
noncomputable section

open NumberField

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections


open scoped Classical in
open Classical in
def PlaceIdemSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (k : Type) [Field k] [Algebra V k] [IsFractionRing V k]
    (P : Ideal (𝓞 E)), P.IsPrime → P ≠ ⊥ →
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (a : Fin n → V), ∀ ψ : E →+* k,
      ∑ i, algebraMap V k (a i) * ψ (b i : E) =
        if (∀ x : 𝓞 E, x ∈ P ↔ ψ (x : E) ∈ algebraMap V k '' (IsLocalRing.maximalIdeal V : Set V)) then 1 else 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

