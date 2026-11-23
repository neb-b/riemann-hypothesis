module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegCA
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

theorem relIndex_eq_map_mul_ker {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) {A B : AddSubgroup G} (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * (A ⊓ f.ker).relIndex (B ⊓ f.ker) := by
  have hN : A ⊓ (B ⊓ f.ker) = A ⊓ f.ker := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]
  have hC : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      refine ⟨y, hy, z, ⟨?_, hz⟩, rfl⟩
      have := B.sub_mem hx (hAB hy)
      simpa using this
    · rintro ⟨y, hy, z, ⟨hzB, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, B.add_mem (hAB hy) hzB⟩
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ (B ⊓ f.ker)).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
      ← AddSubgroup.inf_relIndex_right, hC]
  have h2 : (A ⊓ f.ker).relIndex (B ⊓ f.ker) = A.relIndex (A ⊔ (B ⊓ f.ker)) := by
    rw [sup_comm A, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A (B ⊓ f.ker),
      hN]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hAB inf_le_left)).symm

def intVec (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_intVec {K : Type} [Field K] [NumberField K] {k : ℕ} {x : Fin k → K} :
    x ∈ intVec K k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 K) K) := by
  simp [intVec, Submodule.mem_pi]

theorem exists_section_of_image {K : Type} [Field K] [NumberField K] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (X : Submodule (𝓞 K) V) (f : V →ₗ[K] K) (hfg : (X.map (f.restrictScalars (𝓞 K))).FG)
    (h1 : (1 : Submodule (𝓞 K) K) ≤ X.map (f.restrictScalars (𝓞 K))) :
    ∃ v : V, f v = 1 ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • v ∈ X := by
  classical
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    ⟨X.map (f.restrictScalars (𝓞 K)), FractionalIdeal.isFractional_of_fg hfg⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hI0 : I ≠ 0 := by
    intro h
    have h1I : (1 : K) ∈ (I : Submodule (𝓞 K) K) := h1 hone
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1I
    exact one_ne_zero h1I
  have hII : (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI0, FractionalIdeal.coe_one]
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ u : V, f u = w ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • u ∈ X := by
    intro w hw
    refine Submodule.mul_induction_on hw (fun c hc d hd => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hc
      rw [LinearMap.restrictScalars_apply] at hfx
      refine ⟨d • x, ?_, fun t ht => ?_⟩
      · rw [map_smul, smul_eq_mul, hfx, mul_comm]
      · have htd : t * d ∈ (1 : Submodule (𝓞 K) K) := by
          rw [← hII]
          exact Submodule.mul_mem_mul (show t ∈ (I : Submodule (𝓞 K) K) from ht) hd
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp htd
        rw [smul_smul, ← hr, algebraMap_smul]
        exact X.smul_mem r hx
    · obtain ⟨u1, e1, h1'⟩ := ha
      obtain ⟨u2, e2, h2'⟩ := hb
      exact ⟨u1 + u2, by rw [map_add (f := _), e1, e2], fun t ht => by
        rw [smul_add]; exact X.add_mem (h1' t ht) (h2' t ht)⟩
  exact key 1 (by rw [hII]; exact hone)

theorem absNorm_mul_relIndex_one {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := ⟨C, FractionalIdeal.isFractional_of_fg hC⟩ with hIdef
  have hden := FractionalIdeal.den_mul_self_eq_num I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  set J : Ideal (𝓞 K) := I.num with hJ
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let ι : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  let μ : K →+ K := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)
  have hμ : Function.Injective μ := mul_right_injective₀ hdK
  have hsm : ∀ y : K, (I.den : 𝓞 K) • y = μ y := fun y => by
    rw [Algebra.smul_def]
    rfl
  have hone : AddSubgroup.map μ (1 : Submodule (𝓞 K) K).toAddSubgroup =
      AddSubgroup.map ι (Ideal.span {d}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨r * d, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
  have hCm : AddSubgroup.map μ C.toAddSubgroup = AddSubgroup.map ι J.toAddSubgroup := by
    ext x
    open Pointwise in
    have hx : x ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K)) ↔
        x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      exact Iff.rfl
    rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists] at hx
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx.mp ⟨y, hy, hsm y⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx.mpr ⟨z, hz, rfl⟩
      exact ⟨y, hy, by rw [← hsm]; exact hyx⟩
  have hidx : (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex J.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hμ, hone, hCm,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι]
  have hle : Ideal.span {d} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h1C : (1 : K) ∈ C := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hm : algebraMap (𝓞 K) K d ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      open Pointwise in
      show _ ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K))
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, h1C, by rw [hsm]; simp [μ]⟩
    obtain ⟨z, hz, hzd⟩ := Submodule.mem_map.mp hm
    have hzd' := hι hzd
    rw [hd, ← hzd']
    exact hz
  have htower := AddSubgroup.relIndex_mul_relIndex (Ideal.span {d}).toAddSubgroup
    J.toAddSubgroup ⊤ hle le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htower
  have hiJ : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, AddSubgroup.index_eq_card]
    rfl
  have hid : (Ideal.span {d}).toAddSubgroup.index = (Algebra.norm ℤ d).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      AddSubgroup.index_eq_card]
    rfl
  rw [hiJ, hid] at htower
  have hb : (Algebra.norm ℤ d).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact hd0 h
  have hbq : ((Algebra.norm ℤ d).natAbs : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcast : ((|Algebra.norm ℤ d| : ℤ) : ℚ) = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [hidx, FractionalIdeal.absNorm_eq, hcast, div_mul_eq_mul_div, div_eq_one_iff_eq hbq]
  rw [mul_comm] at htower
  exact_mod_cast htower

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

-- bundled from ReciprocityTheory.SemistableReduction.UnipotentA
section
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial Matrix

theorem unip_trace_aeval_zero {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Matrix.trace_one]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Matrix.trace_smul, hN (i + 1) (by omega) (by omega), smul_zero]

theorem unip_idem_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (E : Matrix (Fin r) (Fin r) K)
    (hE : E * E = E) (ht : E.trace = 0) : E = 0 := by
  set f := Matrix.toLin' E with hfdef
  have hf : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x
      exact LinearMap.mem_range_self f x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [hfdef, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hE]
  have htr : LinearMap.trace K _ f = E.trace := by
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin r)),
      LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']
  have h0 : ((Module.finrank K (LinearMap.range f) : ℕ) : K) = 0 := by
    rw [← hf.trace, htr, ht]
  have h1 : Module.finrank K (LinearMap.range f) = 0 := by exact_mod_cast h0
  have h2 : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp h1
  have h3 : f = 0 := LinearMap.range_eq_bot.mp h2
  exact Matrix.toLin'.injective (h3.trans (map_zero _).symm)

theorem unip_pow_card_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact Subsingleton.elim _ _
  have hint : IsIntegral K N := IsIntegral.of_finite K N
  set m := minpoly K N with hm
  have hmon : m.Monic := minpoly.monic hint
  have hm0 : aeval N m = 0 := minpoly.aeval K N
  have hmdeg : m.natDegree ≤ r := by
    have h2 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N)
      (Matrix.charpoly_monic N).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hrK : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmc : m.coeff 0 = 0 := by
    have h := unip_trace_aeval_zero N hN m hmdeg
    rw [hm0, Matrix.trace_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrK
  have hXm : X ∣ m := Polynomial.X_dvd_iff.mpr hmc
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd m hmon.ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set k := m.rootMultiplicity 0 with hkdef
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hq
    exact hXq (hq ▸ hXm)
  have hcop : IsCoprime (X ^ k) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hXq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨P, hP⟩ : ∃ P : K[X], P = u * X ^ k := ⟨_, rfl⟩
  have hPP : aeval N P * aeval N P = aeval N P := by
    have hsub : P - 1 = -(v * q) := by rw [hP, ← huv]; ring
    have hfac : P * P - P = -(u * v) * m := by
      calc P * P - P = P * (P - 1) := by ring
        _ = -(u * v) * (X ^ k * q) := by rw [hsub, hP]; ring
        _ = -(u * v) * m := by rw [← hq]
    have h := congrArg (aeval N) hfac
    rw [map_sub, map_mul, map_mul, hm0, mul_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨P', hP'⟩ : ∃ P' : K[X], P' = P %ₘ m := ⟨_, rfl⟩
  have hdiv : P' + m * (P /ₘ m) = P := by
    rw [hP']
    first
      | exact Polynomial.modByMonic_add_div P hmon
      | exact Polynomial.modByMonic_add_div P m
  have hPeq : aeval N P' = aeval N P := by
    have h := congrArg (aeval N) hdiv
    rw [map_add (f := _), map_mul, hm0, zero_mul, add_zero] at h
    exact h
  have hP'deg : P'.natDegree ≤ r := by
    rw [hP']
    refine le_trans ?_ hmdeg
    first
      | exact Polynomial.natDegree_modByMonic_le P hmon
      | exact Polynomial.natDegree_modByMonic_le P m
  have hP'0 : P'.coeff 0 = 0 := by
    have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hdiv
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, hmc, zero_mul, add_zero] at h
    rw [h, hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have htr : (aeval N P).trace = 0 := by
    rw [← hPeq, unip_trace_aeval_zero N hN P' hP'deg, hP'0, zero_mul]
  have hE : aeval N P = 0 := unip_idem_eq_zero _ hPP htr
  have hmP : m ∣ P := minpoly.dvd K N hE
  have hqu : q ∣ u := by
    rw [hq, hP, mul_comm u] at hmP
    exact (mul_dvd_mul_iff_left (pow_ne_zero k Polynomial.X_ne_zero)).mp hmP
  have hq1 : IsUnit q := by
    apply isUnit_of_dvd_one
    rw [← huv]
    exact (dvd_mul_of_dvd_left hqu _).add (dvd_mul_left q v)
  have hNk : N ^ k = 0 := by
    have h := hm0
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h
    exact ((hq1.map (aeval N)).mul_left_eq_zero).mp h
  have hkm : k ≤ m.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hmon.ne_zero
    rwa [Polynomial.natDegree_X_pow] at h
  exact pow_eq_zero_of_le (le_trans hkm hmdeg) hNk

end ReciprocityTheory.MultiplicativeHeights
end

