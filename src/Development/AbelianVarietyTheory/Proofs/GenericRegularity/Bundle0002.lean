module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEigenProjectorRingOfIntegers
section
open NumberField

namespace GlobalTheory

open NumberField Matrix in
open Polynomial in
private theorem aeval_mulVec_of_eigenvector {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (μ : K) (x : Fin n → R) (hx : M *ᵥ x = algebraMap K R μ • x)
    (p : K[X]) : (aeval M p) *ᵥ x = algebraMap K R (p.eval μ) • x := by
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ x = algebraMap K R (μ ^ k) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hx, smul_smul, pow_succ',
        map_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_eq_sum_range, Matrix.sum_mulVec, eval_eq_sum_range, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.smul_mulVec, hpow, map_mul, mul_smul, algebraMap_smul]


open NumberField Matrix in
open Polynomial in
theorem _root_.GlobalTheory.exists_eigen_projector_ringOfIntegers : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K)), Function.Injective emb → ∀ τ : E →+* ℂ, ∃ (m : ℕ) (a : Fin m → 𝓞 E) (κ : Fin m → K), ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap K R (κ k) • ρ (a k)) = algebraMap K R (emb τ (b : E)) • ∑ k, algebraMap K R (κ k) • ρ (a k)) ∧ ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap K R (emb τ (b : E)) • x) → (∑ k, algebraMap K R (κ k) • ρ (a k)).mulVec x = x := by
  intro E K _ _ _ emb hemb τ
  classical
  haveI : CharZero K := ⟨fun a b h => by
    have : (emb τ) (a : E) = (emb τ) (b : E) := by simpa using h
    exact Nat.cast_injective ((emb τ).injective this)⟩
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨y, hy0, hyint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic α0)).exists_integral_multiple
  let θ : 𝓞 E := ⟨y • α0, hyint⟩
  have hθ : (θ : E) = y • α0 := rfl
  have hadj : Algebra.adjoin ℚ {α0} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α0), hα0, IntermediateField.top_toSubalgebra]

  have hsep : ∀ σ σ' : E →+* K, σ θ = σ' θ → σ = σ' := by
    intro σ σ' h
    rw [hθ, map_zsmul, map_zsmul] at h
    have h' : σ α0 = σ' α0 := smul_right_injective K (by exact_mod_cast hy0) h
    have := AlgHom.ext_of_adjoin_eq_top (φ₁ := σ.toRatAlgHom) (φ₂ := σ'.toRatAlgHom) hadj
      (by rintro _ rfl; exact h')
    ext z
    exact congrArg (fun φ : E →ₐ[ℚ] K => φ z) this
  have hpoly : ∀ b : 𝓞 E, ∃ D : ℤ, D ≠ 0 ∧ ∃ h : ℤ[X], (D : 𝓞 E) * b = aeval θ h := by
    intro b
    have hb : (b : E) ∈ Algebra.adjoin ℚ {α0} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨p, hp⟩ := hb
    obtain ⟨c, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X))
    refine ⟨c, nonZeroDivisors.ne_zero hc.1, IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (p.comp (C ((y : ℚ)⁻¹) * X)), ?_⟩
    have hy' : (y : E) ≠ 0 := by exact_mod_cast hy0
    have hθα : aeval (θ : E) (C ((y : ℚ)⁻¹) * X) = α0 := by
      rw [hθ, zsmul_eq_mul]
      simp only [map_mul, aeval_C, aeval_X, map_inv₀, map_intCast]
      field_simp
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply]
    have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
    rw [hθc, ← aeval_map_algebraMap ℚ, hc.2, map_zsmul, aeval_comp, hθα]
    have hp' : aeval α0 p = (b : E) := hp
    rw [hp', zsmul_eq_mul, map_mul, map_intCast]
  have hθint : IsIntegral ℤ (θ : E) := hyint
  have hfmon : (minpoly ℤ (θ : E)).Monic := minpoly.monic hθint
  have hθc : algebraMap (𝓞 E) E θ = (θ : E) := rfl
  have hf0 : aeval θ (minpoly ℤ (θ : E)) = 0 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← aeval_algebraMap_apply, map_zero, hθc]
    exact minpoly.aeval ℤ (θ : E)
  let σ : (E →+* ℂ) → K := fun τ' => emb τ' (θ : E)
  have hσinj : Function.Injective σ := fun τ1 τ2 h => hemb (hsep _ _ h)
  let P : K[X] := ∏ τ' : E →+* ℂ, (X - C (σ τ'))
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hPdeg : P.natDegree = Fintype.card (E →+* ℂ) := by
    simp only [P]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  have hfK : (minpoly ℤ (θ : E)).map (algebraMap ℤ K) = P := by
    refine eq_of_monic_of_dvd_of_natDegree_le hPmon (hfmon.map _) ?_ ?_
    · apply Finset.prod_dvd_of_coprime
      · exact (pairwise_coprime_X_sub_C hσinj).set_pairwise _
      · intro τ' _
        rw [dvd_iff_isRoot, IsRoot, eval_map_algebraMap,
          show σ τ' = (emb τ').toIntAlgHom (θ : E) from rfl, aeval_algHom_apply, minpoly.aeval,
          map_zero]
    · rw [hPdeg, hfmon.natDegree_map, NumberField.Embeddings.card E ℂ,
        ← hfmon.natDegree_map (algebraMap ℤ ℚ),
        ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθint]
      exact minpoly.natDegree_le _
  have hPρ : ∀ (R : Type) [CommRing R] [Algebra K R] (n : ℕ)
      (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R), aeval (ρ θ) P = 0 := by
    intro R _ _ n ρ
    rw [← hfK, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply, hf0,
      map_zero]
  let c : K := (∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ'))⁻¹
  let G : K[X] := C c * ∏ τ' ∈ Finset.univ.erase τ, (X - C (σ τ'))
  have hprod_ne : ∏ τ' ∈ Finset.univ.erase τ, (σ τ - σ τ') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ' h => sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h) (hσinj e).symm
  have hGev : G.eval (σ τ) = 1 := by
    simp only [G, c, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact inv_mul_cancel₀ hprod_ne
  have hXG : (X - C (σ τ)) * G = C c * P := by
    simp only [G, P]
    rw [← Finset.mul_prod_erase Finset.univ (fun τ' => X - C (σ τ')) (Finset.mem_univ τ)]
    ring
  clear_value G c P
  refine ⟨G.natDegree + 1, fun k => θ ^ (k : ℕ), fun k => G.coeff k, ?_⟩
  intro R _ _ n ρ
  have hsum : ∑ k : Fin (G.natDegree + 1), algebraMap K R (G.coeff k) • ρ (θ ^ (k : ℕ)) =
      aeval (ρ θ) G := by
    rw [aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, algebraMap_smul]
  rw [hsum]
  have hsmul : ∀ (k : K) (M : Matrix (Fin n) (Fin n) R),
      algebraMap K (Matrix (Fin n) (Fin n) R) k * M = algebraMap K R k • M := by
    intro k M
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, algebraMap_smul]
  refine ⟨fun b => ?_, fun x hx => ?_⟩
  · obtain ⟨D, hD, h, hh⟩ := hpoly b
    set hK := h.map (algebraMap ℤ K) with hKdef
    set r := hK.eval (σ τ) with hrdef
    have hr : r = (D : K) * emb τ (b : E) := by
      rw [hrdef, hKdef, eval_map_algebraMap,
        show σ τ = ((emb τ).comp (algebraMap (𝓞 E) E)).toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    have hq := (mul_divByMonic_eq_iff_isRoot (p := hK - C r) (a := σ τ)).2
      (by rw [IsRoot, eval_sub, eval_C, hrdef, sub_self])
    have hkey : hK * G = C r * G + C c * ((hK - C r) /ₘ (X - C (σ τ))) * P := by
      calc hK * G = C r * G + ((X - C (σ τ)) * ((hK - C r) /ₘ (X - C (σ τ)))) * G := by
            rw [hq]; ring
        _ = C r * G + ((hK - C r) /ₘ (X - C (σ τ))) * ((X - C (σ τ)) * G) := by ring
        _ = _ := by rw [hXG]; ring
    have hev := congrArg (aeval (ρ θ)) hkey
    rw [map_add (f := _), map_mul, map_mul, map_mul, hPρ R n ρ, mul_zero, add_zero, aeval_C] at hev
    have hρh : aeval (ρ θ) hK = algebraMap K _ (D : K) * ρ b := by
      rw [hKdef, aeval_map_algebraMap, show ρ θ = ρ.toIntAlgHom θ from rfl, aeval_algHom_apply,
        ← hh]
      simp
    rw [hρh, hr, map_mul, mul_assoc, mul_assoc] at hev
    have hu : IsUnit (algebraMap K (Matrix (Fin n) (Fin n) R) (D : K)) :=
      (IsUnit.mk0 _ (by exact_mod_cast hD)).map _
    rw [hu.mul_left_cancel hev, hsmul]
  · rw [aeval_mulVec_of_eigenvector (ρ θ) (σ τ) x (hx θ) G, hGev, map_one, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
section
namespace GlobalTheory

open Matrix

theorem exists_pivot_entry {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ}
    (w : Fin n → L) (hw : w ≠ 0) : ∃ k, w k ≠ 0 ∧ ∀ i, w i / w k ∈ W := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    exact hw (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i => W.valuation (w i)) ⟨j, Finset.mem_univ j⟩
  have hwk : w k ≠ 0 := by
    intro h0
    have hle := hk j (Finset.mem_univ j)
    rw [h0, map_zero] at hle
    exact hj ((Valuation.zero_iff _).1 (le_antisymm hle zero_le))
  refine ⟨k, hwk, fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ i)) zero_le

private theorem exists_pivot_unipotent_mul_triangular {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ} :
    ∀ (r : ℕ) (g : Matrix (Fin n) (Fin r) L), LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro r
  induction r with
  | zero =>
    intro g _
    refine ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    ext _ j
    exact Fin.elim0 j
  | succ r ih =>
    intro g hg
    let cols' : Fin r → Fin n → L := fun i a => g a i.castSucc
    let g' : Matrix (Fin n) (Fin r) L := Matrix.of fun a i => cols' i a
    let x : Fin n → L := fun a => g a (Fin.last r)
    have hsplit : (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) = fun i a => g a i := by
      funext i a
      cases i using Fin.lastCases with
      | last => simp [x]
      | cast i => simp [cols']
    have hg2 : LinearIndependent L (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) := by
      rw [hsplit]
      exact hg
    rw [linearIndependent_finSnoc] at hg2
    obtain ⟨hg'ind, hxspan⟩ := hg2
    obtain ⟨ι', u', b', hu'W, hu'zero, hu'one, hb'tri, hb'diag, hgub⟩ := ih g' hg'ind
    have hb'det : IsUnit b'.det := by
      rw [Matrix.det_of_isUpperTriangular hb'tri]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hb'diag i).isUnit
    let M : Matrix (Fin r) (Fin r) L := Matrix.of fun l i => u' (ι' l) i
    have hMtri : M.BlockTriangular OrderDual.toDual := by
      intro l i hli
      simpa [M] using hu'zero l i (OrderDual.toDual_lt_toDual.1 hli)
    have hMdet : IsUnit M.det := by
      rw [Matrix.det_of_isLowerTriangular M hMtri]
      simp [M, hu'one]
    let c : Fin r → L := M⁻¹ *ᵥ (fun l => x (ι' l))
    let v : Fin n → L := x - u' *ᵥ c
    have hvpiv : ∀ l, v (ι' l) = 0 := by
      intro l
      have h1 : (u' *ᵥ c) (ι' l) = (M *ᵥ c) l := rfl
      have h2 : M *ᵥ c = fun l => x (ι' l) := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMdet, Matrix.one_mulVec]
      show x (ι' l) - (u' *ᵥ c) (ι' l) = 0
      rw [h1, h2, sub_self]
    have hv0 : v ≠ 0 := by
      intro h0
      apply hxspan
      have hxv : x - u' *ᵥ c = 0 := h0
      have hu' : u' = g' * b'⁻¹ := by
        rw [hgub]
        exact (Matrix.mul_nonsing_inv_cancel_right (B := u') (h := hb'det)).symm
      have hxe : x = g' *ᵥ (b'⁻¹ *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, ← hu']
        exact sub_eq_zero.1 hxv
      have hmem := LinearMap.mem_range_self g'.mulVecLin (b'⁻¹ *ᵥ c)
      rw [Matrix.range_mulVecLin] at hmem
      rw [hxe]
      exact hmem
    obtain ⟨k, hvk, hkW⟩ := exists_pivot_entry W v hv0
    have hk : ∀ l, ι' l ≠ k := fun l hl => hvk (hl ▸ hvpiv l)
    let ιf : Fin (r + 1) → Fin n := Fin.lastCases (motive := fun _ => Fin n) k (fun i => ι' i)
    have hιf : Function.Injective ιf := by
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij.symm (hk j)
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij (hk i)
        | cast j =>
          simp only [ιf, Fin.lastCases_castSucc] at hij
          rw [ι'.injective hij]
    let u : Matrix (Fin n) (Fin (r + 1)) L :=
      Matrix.of fun a => Fin.snoc (α := fun _ => L) (u' a) (v a / v k)
    let b : Matrix (Fin (r + 1)) (Fin (r + 1)) L := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) (v k) (fun i' => c i') i)
        (fun j' => Fin.lastCases (motive := fun _ => L) 0 (fun i' => b' i' j') i) j
    refine ⟨⟨ιf, hιf⟩, u, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a j
      cases j using Fin.lastCases with
      | last => simpa [u] using hkW a
      | cast j => simpa [u] using hu'W a j
    · intro i j hij
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_last]
          rw [hvpiv i, zero_div]
        | cast j =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_castSucc]
          exact hu'zero i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_last,
          Fin.snoc_last]
        exact div_self hvk
      | cast i =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
          Fin.snoc_castSucc]
        exact hu'one i
    · intro i j hji
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j => simp [b]
      | cast i =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (not_lt.2 (Fin.le_last _))
        | cast j =>
          simp only [b, Matrix.of_apply, Fin.lastCases_castSucc]
          exact hb'tri (Fin.castSucc_lt_castSucc_iff.1 hji)
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [b] using hvk
      | cast i => simpa [b] using hb'diag i
    · ext a j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      cases j using Fin.lastCases with
      | last =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        rw [div_mul_cancel₀ _ hvk]
        show x a = _ + (x a - (u' *ᵥ c) a)
        simp only [Matrix.mulVec, dotProduct]
        ring
      | cast j =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.lastCases_last,
          Fin.lastCases_castSucc, mul_zero, add_zero]
        have hentry := congrFun (congrFun hgub a) j
        simpa [g', cols', Matrix.mul_apply] using hentry

theorem exists_integral_pivot_decomposition :
    ∀ (L : Type) [Field L] (W : ValuationSubring L) (n r : ℕ) (g : Matrix (Fin n) (Fin r) L),
      LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro L _ W n r g hg
  exact exists_pivot_unipotent_mul_triangular W r g hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
section
open TensorProduct

namespace GlobalTheory

theorem flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro m ⟨⟨r, hr⟩, hm⟩
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hmul : algebraMap O A r * m = 0 := by rw [← Algebra.smul_def]; exact hm
  exact (mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)

theorem one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  have key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by
  obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI
  have hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B) :=
    Ideal.map_le_iff_le_comap.mp (hm.trans hIN)
  letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (B ⧸ N)))
  let f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    (Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))
  let g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    ((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)
  refine ⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩
  · rw [RingHom.mem_ker]
    have h0 : IsLocalRing.residue O' a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]
  · rw [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mk N b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]

theorem exists_integral_point_of_complete_case :
    (∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B] (M : Ideal B), M.IsMaximal → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ M → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V := by
  intro H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he
  haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'
  haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB
  obtain ⟨M, hM, hM1, hM2⟩ := exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI
  obtain ⟨P, hPmin, hPM⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)
  haveI : P.IsPrime := hPmin.isPrime
  haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0 := ha
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha')
      hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)
  haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj
  haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P)
      (Ideal.Quotient.mkₐ_surjective O' P)
  have hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_
    intro htop
    have h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, hm1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have hmP : m - 1 ∈ P := Ideal.Quotient.eq.mp (by rw [hm1, map_one])
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))
  have hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤
      M.map (Ideal.Quotient.mk P) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)
  have he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0 := by
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)
  obtain ⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩ :=
    H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'
  refine ⟨V, i₁, i₂, i₃, i₄, i₅,
    φ.toRingHom.comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩
  · ext o
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) =
        algebraMap O' (O' ⊗[O] B) (algebraMap O O' o) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]
    exact φ.commutes _
  · intro x hx
    exact hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))

end GlobalTheory
end

