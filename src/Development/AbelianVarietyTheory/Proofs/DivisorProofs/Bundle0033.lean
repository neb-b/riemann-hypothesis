module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetN
section
open Matrix

namespace GlobalTheory
namespace IwasawaLowerTri

variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F]

lemma permMatrix_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix V).map (algebraMap V F) = σ.permMatrix F := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma permMatrix_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (σ.permMatrix F * A) i j = A (σ i) j := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

lemma isUnit_det_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsUnit (σ.permMatrix V).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma exists_max_val {n : ℕ} (c : Fin (n+1) → F) :
    ∃ i0, ∀ i, ValuationRing.valuation V F (c i) ≤ ValuationRing.valuation V F (c i0) := by
  obtain ⟨i0, -, h⟩ := Finset.exists_max_image Finset.univ (fun i => ValuationRing.valuation V F (c i)) Finset.univ_nonempty
  exact ⟨i0, fun i => h i (Finset.mem_univ _)⟩

lemma integral_of_val_le (x y : F) (hy : y ≠ 0)
    (h : ValuationRing.valuation V F x ≤ ValuationRing.valuation V F y) :
    ∃ q : V, algebraMap V F q = x / y := by
  rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_div]
  have : ValuationRing.valuation V F y ≠ 0 := by simpa using hy
  exact (div_le_one₀ (zero_lt_iff.mpr this)).mpr h

lemma clear_last_column {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) V, IsUnit P.det ∧
      ∀ i : Fin n, (P.map (algebraMap V F) * A) i.castSucc (Fin.last n) = 0 := by
  by_cases hz : ∀ i, A i (Fin.last n) = 0
  · refine ⟨1, by simp, fun i => ?_⟩
    simp [hz]
  push_neg at hz
  obtain ⟨i1, hi1⟩ := hz
  obtain ⟨i0, hmax⟩ := exists_max_val V F (fun i => A i (Fin.last n))
  have h0 : A i0 (Fin.last n) ≠ 0 := by
    intro h
    have := hmax i1
    simp only [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi1 this
  have hq : ∀ i, ∃ q : V, algebraMap V F q = A i (Fin.last n) / A i0 (Fin.last n) :=
    fun i => integral_of_val_le V F _ _ h0 (hmax i)
  choose q hq using hq
  set σ : Equiv.Perm (Fin (n+1)) := Equiv.swap i0 (Fin.last n) with hσ
  let E : Matrix (Fin (n+1)) (Fin (n+1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = Fin.last n then -q (σ i) else 0
  refine ⟨E * σ.permMatrix V, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ (isUnit_det_permMatrix V σ)
    rw [Matrix.det_of_upperTriangular]
    · simp [E]
    · intro a b hab
      have hne : a ≠ b := ne_of_gt hab
      have hb : b ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hab (Fin.le_last a))
      simp [E, hne, hb]
  · rw [Matrix.map_mul, Matrix.mul_assoc, permMatrix_map, Matrix.mul_apply,
      Fintype.sum_eq_add i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne]
    · simp only [permMatrix_mul_apply, E, Matrix.map_apply, Matrix.of_apply, if_true,
        (Fin.castSucc_lt_last i).ne, if_false, map_one, map_neg, hq]
      have : σ (Fin.last n) = i0 := by simp [hσ]
      rw [this]
      field_simp
      ring
    · intro x hx
      simp [E, Matrix.map_apply, Ne.symm hx.1, hx.2]

def blockExt {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : Matrix (Fin (n+1)) (Fin (n+1)) V :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks k 0 0 (1 : Matrix (Fin 1) (Fin 1) V))

lemma blockExt_det {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : (blockExt V k).det = k.det := by
  simp [blockExt, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma blockExt_cc {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a b : Fin n) :
    blockExt V k a.castSucc b.castSucc = k a b := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_cl {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a : Fin n) :
    blockExt V k a.castSucc (Fin.last n) = 0 := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_mul_apply {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (A : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (a : Fin n) (j : Fin (n+1)) :
    ((blockExt V k).map (algebraMap V F) * A) a.castSucc j =
      (k.map (algebraMap V F) * A.submatrix Fin.castSucc id) a j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply, blockExt_cc, blockExt_cl,
    map_zero, zero_mul, add_zero, Matrix.submatrix_apply, id]

theorem iwasawa_lowerTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧
      ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  induction n with
  | zero => exact ⟨1, by simp, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨P, hP, hPA⟩ := clear_last_column V F A
    set A' := P.map (algebraMap V F) * A with hA'
    obtain ⟨k', hk', hk'A⟩ := ih (A'.submatrix Fin.castSucc Fin.castSucc)
    refine ⟨blockExt V k' * P, ?_, fun i j hij => ?_⟩
    · rw [Matrix.det_mul, blockExt_det]
      exact hk'.mul hP
    · rw [Matrix.map_mul, Matrix.mul_assoc, ← hA']
      obtain ⟨a, rfl⟩ : ∃ a : Fin n, a.castSucc = i :=
        Fin.exists_castSucc_eq.mpr (ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j)))
      rw [blockExt_mul_apply]
      induction j using Fin.lastCases with
      | last =>
        rw [Matrix.mul_apply]
        simp only [Matrix.submatrix_apply, id, hPA, mul_zero, Finset.sum_const_zero]
      | cast b =>
        have := hk'A a b (Fin.castSucc_lt_castSucc_iff.mp hij)
        simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
end IwasawaLowerTri
end GlobalTheory

theorem GlobalTheory.iwasawa_lowerTriangular_of_det :
    ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 :=
  fun V F _ _ _ _ _ _ n A _ => GlobalTheory.IwasawaLowerTri.iwasawa_lowerTriangular V F n A
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPosDefHermitian
section
open Matrix

noncomputable section
namespace GlobalTheory.CompactAvg
open MeasureTheory

theorem exists_invariant_posDef_hermitian {n : ℕ} (H : Subgroup (GL (Fin n) ℂ))
    (hH : IsCompact (H : Set (GL (Fin n) ℂ))) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let m : H → Matrix (Fin n) (Fin n) ℂ := fun g => (((g⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)

  let f : H → (Fin n → Fin n → ℂ) := fun g => ((m g)ᴴ * m g : Matrix (Fin n) (Fin n) ℂ)
  have hf : Continuous f := hm.matrix_conjTranspose.matrix_mul hm
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.of (∫ g, f g ∂μ)

  have hinv : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ * h = P₀ := by
    intro h hh
    let M : Matrix (Fin n) (Fin n) ℂ := h
    let Lₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
      { toFun := fun A => (Mᴴ * Matrix.of A * M : Matrix (Fin n) (Fin n) ℂ)
        map_add' := fun A B => by
          show Mᴴ * Matrix.of (A + B) * M = Mᴴ * Matrix.of A * M + Mᴴ * Matrix.of B * M
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c A => by
          show Mᴴ * Matrix.of (c • A) * M = c • (Mᴴ * Matrix.of A * M)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul] }
    let L := LinearMap.toContinuousLinearMap Lₗ
    have e1 : L (∫ g, f g ∂μ) = ∫ g, L (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm L hfi).symm
    have e2 : ∀ g : H, L (f g) = f ((⟨h, hh⟩ : H)⁻¹ * g) := by
      intro g
      have hq : m ((⟨h, hh⟩ : H)⁻¹ * g) = m g * M := by
        show (((((⟨h, hh⟩ : H)⁻¹ * g)⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = m g * M
        rw [_root_.mul_inv_rev, inv_inv]
        rfl
      show Mᴴ * ((m g)ᴴ * m g) * M = (m _)ᴴ * m _
      rw [hq, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e3 : ∫ g, f ((⟨h, hh⟩ : H)⁻¹ * g) ∂μ = ∫ g, f g ∂μ := integral_mul_left_eq_self f _
    show L (∫ g, f g ∂μ) = ∫ g, f g ∂μ
    rw [e1]; simp_rw [e2]; exact e3

  have hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P₀ *ᵥ x).re := by
    intro x hx
    let ℓₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun A => star x ⬝ᵥ Matrix.of A *ᵥ x
        map_add' := fun A B => by
          show star x ⬝ᵥ Matrix.of (A + B) *ᵥ x = star x ⬝ᵥ Matrix.of A *ᵥ x + star x ⬝ᵥ Matrix.of B *ᵥ x
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c A => by
          show star x ⬝ᵥ Matrix.of (c • A) *ᵥ x = c • (star x ⬝ᵥ Matrix.of A *ᵥ x)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.smul_mulVec, dotProduct_smul] }
    let ℓ := LinearMap.toContinuousLinearMap ℓₗ
    have e1 : ℓ (∫ g, f g ∂μ) = ∫ g, ℓ (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm ℓ hfi).symm
    have hℓi : Integrable (fun g => ℓ (f g)) μ := ℓ.integrable_comp hfi
    have e2 : (star x ⬝ᵥ P₀ *ᵥ x).re = ∫ g, RCLike.re (ℓ (f g)) ∂μ := by
      rw [integral_re hℓi, ← e1]; rfl
    have e3 : ∀ g : H, RCLike.re (ℓ (f g)) = ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      show (star x ⬝ᵥ ((m g)ᴴ * m g) *ᵥ x).re = _
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.star_def, Complex.mul_re]
    have hnz : ∀ g : H, m g *ᵥ x ≠ 0 := by
      intro g h0
      have : (((g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * m g) *ᵥ x = x := by
        simp [m]
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at this
      exact hx this.symm
    have e4 : ∀ g : H, 0 < ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (hnz g)
      have hi' : 0 < ‖(m g *ᵥ x) i‖ ^ 2 := by
        have : 0 < ‖(m g *ᵥ x) i‖ := norm_pos_iff.2 hi
        positivity
      exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i => ‖(m g *ᵥ x) i‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i))
    rw [e2]
    simp_rw [e3]
    have hgi : Integrable (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) μ :=
      (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_pos_iff_support_of_nonneg (fun g => (e4 g).le) hgi]
    have hs : Function.support (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) = Set.univ :=
      Set.eq_univ_of_forall fun g => (e4 g).ne'
    rw [hs]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  refine ⟨P₀ + P₀ᴴ, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian, add_comm]
  · intro x hx
    have hc : star x ⬝ᵥ P₀ᴴ *ᵥ x = star (star x ⬝ᵥ P₀ *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_dotProduct]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hc]
    have := hpos x hx
    simp only [Complex.star_def, Complex.conj_re]
    linarith
  · intro g hg
    have h1 := hinv g hg
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ᴴ * g = P₀ᴴ := by
      conv_rhs => rw [← h1]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]

end GlobalTheory.CompactAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomial
section
open Polynomial

namespace GlobalTheory

noncomputable def awayLiftAlgHom {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) : Localization.Away P →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers P) (f := f)
    (by rintro ⟨_, n, rfl⟩; simpa using h.pow n)

theorem awayLiftAlgHom_algebraMap {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by
  simp [awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem aeval_reverse_mul_pow_of_mul_eq_one {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x y : B) (h : x * y = 1) (P : k[X]) :
    aeval y P.reverse * x ^ P.natDegree = aeval x P := by
  letI : Invertible x := invertibleOfRightInverse x y h
  have hinv : (⅟x : B) = y := invOf_eq_right_inv h
  have := eval₂_reverse_mul_pow (algebraMap k B) x P
  rw [hinv] at this
  simpa [aeval_def] using this

theorem algebraMap_eq_aeval_X {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
  have : (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun this p

theorem localizationAway_inv_coordinate (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  classical
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  refine ⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩

  set C := Localization.Away (X * P)
  set u : C := IsLocalization.Away.invSelf (X * P)
  have hu : algebraMap k[X] C (X * P) * u = 1 := IsLocalization.Away.mul_invSelf _
  set xC : C := algebraMap k[X] C X
  set xi : C := algebraMap k[X] C P * u
  have hxC : xC * xi = 1 := by rw [← hu, map_mul]; ring
  have hPC : IsUnit (algebraMap k[X] C P) :=
    isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩
  have hxi : IsUnit xi := isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩
  have hτ : IsUnit (aeval xi (X * P.reverse)) := by
    rw [map_mul, aeval_X]
    refine hxi.mul ?_
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P
    rw [← algebraMap_eq_aeval_X] at key
    exact isUnit_of_mul_isUnit_left (key ▸ hPC)
  let τ := awayLiftAlgHom (X * P.reverse) (aeval xi) hτ

  set B := Localization.Away (X * P.reverse)
  set v : B := IsLocalization.Away.invSelf (X * P.reverse)
  have hv : algebraMap k[X] B (X * P.reverse) * v = 1 := IsLocalization.Away.mul_invSelf _
  set yB : B := algebraMap k[X] B X
  set yi : B := algebraMap k[X] B P.reverse * v
  have hyB : yB * yi = 1 := by rw [← hv, map_mul]; ring
  have hrevB : IsUnit (algebraMap k[X] B P.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩
  have hyi : IsUnit yi := isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩
  have hσ : IsUnit (aeval yi P) := by
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P
    rw [← algebraMap_eq_aeval_X] at key
    rw [← key]
    exact hrevB.mul (hyi.pow _)
  let σ := awayLiftAlgHom P (aeval yi) hσ
  have hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q :=
    awayLiftAlgHom_algebraMap _ _ _
  have hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q :=
    awayLiftAlgHom_algebraMap _ _ _
  refine ⟨σ, τ, ?_, ?_⟩
  · have hτyi : τ yi = xC := by
      have h1 : τ yB * τ yi = 1 := by rw [← map_mul, hyB, map_one]
      have h2 : τ yB = xi := by rw [hτalg, aeval_X]
      rw [h2] at h1
      calc τ yi = τ yi * (xC * xi) := by rw [hxC, mul_one]
        _ = xC * (xi * τ yi) := by ring
        _ = xC := by rw [h1, mul_one]
    have hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) =
        IsScalarTower.toAlgHom k k[X] C := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [hσalg, aeval_X, hτyi]
    exact RingHom.ext fun p => DFunLike.congr_fun hext p
  · exact RingHom.ext fun p => hτalg p

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgClosedEmbeddingsOfFamily
section
namespace GlobalTheory

open MvPolynomial

theorem exists_isAlgClosed_embeddings_of_family :
    ∀ (F : Type) [Field F] (I : Type) (k : I → Type) [∀ i, Field (k i)] (f : ∀ i, F →+* k i),
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (g : ∀ i, k i →+* L) (h : F →+* L),
        ∀ i, (g i).comp (f i) = h := by
  intro F _ I k _ f
  let K := FractionRing (MvPolynomial (Σ i, k i) F)
  let Ω := AlgebraicClosure K
  have key : ∀ i, ∃ g : k i →+* Ω, g.comp (f i) = algebraMap F Ω := by
    intro i
    letI : Algebra F (k i) := (f i).toAlgebra
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F (k i)
    let x : (Σ i, k i) → Ω := fun j => algebraMap K Ω (algebraMap (MvPolynomial (Σ i, k i) F) K (X j))
    have hx : AlgebraicIndependent F x := by
      have h0 := MvPolynomial.algebraicIndependent_X (Σ i, k i) F
      have h1 : Function.Injective (IsScalarTower.toAlgHom F (MvPolynomial (Σ i, k i) F) K) :=
        IsFractionRing.injective _ _
      have h2 : Function.Injective (IsScalarTower.toAlgHom F K Ω) :=
        (algebraMap K Ω).injective
      have := (h0.map' h1).map' h2
      exact this
    have hv : AlgebraicIndependent F (fun b : s => x ⟨i, b.1⟩) :=
      hx.comp (fun b : s => (⟨i, b.1⟩ : Σ i, k i)) (by
        intro a b hab
        exact Subtype.ext (by simpa using hab))
    let φ0 : IntermediateField.adjoin F (Set.range ((↑) : s → k i)) →ₐ[F] Ω :=
      (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
    have halg := hs.isAlgebraic_field
    obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' φ0
      (fun (y : k i) => ⟨(Algebra.IsAlgebraic.isAlgebraic
        (R := IntermediateField.adjoin F (Set.range ((↑) : s → k i))) y).isIntegral,
        IsAlgClosed.splits _⟩)
    refine ⟨φ.toRingHom, ?_⟩
    ext y
    exact φ.commutes y
  choose g hg using key
  exact ⟨Ω, inferInstance, inferInstance, g, algebraMap F Ω, hg⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind
section
namespace GlobalTheory

namespace FracAlgDedekind

open Order

theorem ringKrullDim_le_of_isIntegral {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact LTSeries.length_le_krullDim L

theorem exists_finite_inj_polynomial (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (hB : ¬ IsField B) :
    ∃ f : Polynomial k →+* B, Function.Injective f ∧ f.Finite := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  have hle := ringKrullDim_le_of_isIntegral (A := MvPolynomial (Fin s) k) (R := B) hg
  have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hB1 : ringKrullDim B ≤ 1 := Ring.krullDimLE_iff.1 inferInstance
  rw [hdim] at hle
  have hs1 : s ≤ 1 := by exact_mod_cast hle.trans hB1
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : Algebra.IsIntegral k (MvPolynomial (Fin 0) k) :=
      Algebra.IsIntegral.of_surjective (Algebra.ofId k (MvPolynomial (Fin 0) k))
        (MvPolynomial.C_surjective (Fin 0))
    have : Algebra.IsIntegral k B := Algebra.IsIntegral.trans (MvPolynomial (Fin 0) k)
    exact hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).1
      (Field.toIsField k))
  obtain rfl : s = 1 := by omega
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    MvPolynomial.uniqueAlgEquiv k (Fin 1)
  refine ⟨g.toRingHom.comp e.symm.toRingEquiv.toRingHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem exists_isAlgebraic_ratFunc : ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
    ∃ _ : Algebra (RatFunc k) (FractionRing B), Algebra.IsAlgebraic (RatFunc k) (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  obtain ⟨f, hf, hfin⟩ := exists_finite_inj_polynomial k B hB
  letI : Algebra (Polynomial k) B := f.toAlgebra
  have : Module.Finite (Polynomial k) B := hfin
  have hφ : Function.Injective (algebraMap (Polynomial k) (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial k) B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hf
  letI alg : Algebra (RatFunc k) (FractionRing B) := (IsFractionRing.lift hφ (K := RatFunc k)).toAlgebra
  have : IsScalarTower (Polynomial k) (RatFunc k) (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq fun p => (IsFractionRing.lift_algebraMap hφ p).symm
  have : FaithfulSMul (Polynomial k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : Algebra.IsAlgebraic B (FractionRing B) :=
    IsLocalization.isAlgebraic (FractionRing B) (nonZeroDivisors B)
  have : Algebra.IsAlgebraic (Polynomial k) (FractionRing B) :=
    Algebra.IsAlgebraic.trans (Polynomial k) B (FractionRing B)
  exact ⟨alg, Algebra.IsAlgebraic.extendScalars (R := Polynomial k) (RatFunc.algebraMap_injective k)⟩

end FracAlgDedekind

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdjoinRootOfSeparable
section
namespace GlobalTheory.ReducedAdjoinRootSeparable

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by
  have h1 : IsRadical f := isRadical_iff_squarefree_or_zero.2 (Or.inl hf.squarefree)
  have h2 : (Ideal.span {f}).IsRadical := isRadical_iff_span_singleton.1 h1
  exact (Ideal.isRadical_iff_quotient_reduced _).1 h2

end GlobalTheory.ReducedAdjoinRootSeparable
end

