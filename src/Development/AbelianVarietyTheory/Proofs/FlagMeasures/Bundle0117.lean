module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumns
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory

theorem uJ_col_sum {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h)
    (j : Fin n) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖h i j‖ ^ 2 = if ε j then (1 : ℝ) else -1 := by
  have h1 := congrFun (congrFun hh j) j
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  apply Complex.ofReal_injective
  push_cast
  have : ((if ε j then (1 : ℝ) else -1 : ℝ) : ℂ) = if ε j then (1 : ℂ) else -1 := by
    split_ifs <;> simp
  rw [this, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((‖h i j‖ : ℝ) : ℂ) ^ 2 = star (h i j) * h i j := by
    rw [Complex.star_def, Complex.conj_mul']
  rw [h2]
  split_ifs <;> simp

theorem uJ_conjTranspose {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) : inUJ ε hᴴ := by
  have h1 := (uJInv n ε h hh).1
  have hJ : Jm ε * Jm ε = 1 := by
    simp only [Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  unfold inUJ
  rw [Matrix.conjTranspose_conjTranspose]
  calc h * Jm ε * hᴴ = h * (Jm ε * hᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem hs_le_of_cols (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) :
    hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  set e : Fin n → ℝ := fun i => if ε i then (1 : ℝ) else -1 with he
  set σ : ℝ := if s then (1 : ℝ) else -1 with hσ
  have hc : ∀ j, ∑ i, e i * ‖h i j‖ ^ 2 = e j := uJ_col_sum ε h hh
  have hr : ∀ i, ∑ j, e j * ‖h i j‖ ^ 2 = e i := fun i => by
    have := uJ_col_sum ε hᴴ (uJ_conjTranspose ε h hh) i
    simpa only [Matrix.conjTranspose_apply, norm_star] using this
  have hee : ∀ i, e i * e i = 1 := fun i => by
    simp only [he]; split_ifs <;> simp
  have A : ∑ i, ∑ j, e i * (e j * ‖h i j‖ ^ 2) = n := by
    simp only [← Finset.mul_sum, hr, hee]
    simp
  have B : ∑ i, ∑ j, e j * ‖h i j‖ ^ 2 = ∑ i, ∑ j, e i * ‖h i j‖ ^ 2 := by
    rw [Finset.sum_comm (f := fun i j => e i * ‖h i j‖ ^ 2)]
    simp only [hr, hc]
  have C : ∑ i, ∑ j, (‖h i j‖ ^ 2 - e i * (e j * ‖h i j‖ ^ 2) + σ * (e j * ‖h i j‖ ^ 2)
      - σ * (e i * ‖h i j‖ ^ 2)) ≤ ∑ i, ∑ j, 4 * (if ε j = s then ‖h i j‖ ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ ‖h i j‖ ^ 2 := by positivity
    simp only [he, hσ]
    cases ε i <;> cases ε j <;> cases s <;> simp <;> linarith
  have D : ∑ i, ∑ j, σ * (e j * ‖h i j‖ ^ 2) = ∑ i, ∑ j, σ * (e i * ‖h i j‖ ^ 2) := by
    have := congrArg (σ * ·) B
    simpa only [Finset.mul_sum] using this
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at C
  rw [A, D] at C
  simp only [Finset.sum_filter, Finset.mul_sum, hs]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspace
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagInv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem map_Xflag_le (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) ≤ Xflag F j := by
  show (F.fl.Xa j).map (a : S.V →ₗ[E] S.V) ≤ F.fl.Xa j
  rw [Submodule.map_le_iff_le_comap]
  unfold Formalism.MainNotions.S.FlagG.Xa
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq] at hi
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
  have hb := h (Fin.castSucc i)
  have hf : frame F (Fin.castSucc i) = F.fl.e i := by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  rw [hf] at hb
  have hmono : Xflag F (Fin.castSucc i).val ≤ F.fl.Xa j := by
    show F.fl.Xa i.val ≤ F.fl.Xa j
    unfold Formalism.MainNotions.S.FlagG.Xa
    apply Submodule.span_mono
    apply Set.image_mono
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    omega
  have he : F.fl.e i ∈ F.fl.Xa j := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have := Submodule.add_mem _ (hmono hb) he
  unfold Formalism.MainNotions.S.FlagG.Xa at this
  simpa using this

theorem map_Xflag_eq (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) = Xflag F j := by
  haveI : FiniteDimensional E (Xflag F j) := by
    show FiniteDimensional E (Submodule.span E (F.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite E (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq (map_Xflag_le F a h j) (LinearEquiv.finrank_map_eq a _)

theorem symm_mem_Xflag (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) {x : S.V}
    (hx : x ∈ Xflag F j) : a.symm x ∈ Xflag F j := by
  rw [← map_Xflag_eq F a h j] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem inv_moves : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  intro E _ _ _ S r T F a h b
  have hm := symm_mem_Xflag F a h b.val (h b)
  have key : a⁻¹ (frame F b) - frame F b = -(a.symm (a (frame F b) - frame F b)) := by
    show a.symm (frame F b) - frame F b = _
    simp [map_sub]
  rw [key]
  exact Submodule.neg_mem _ hm

end GlobalTheory.FlagInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCTypeWConj
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable {k : ℕ}

theorem lowK_allPos (lam : Fin k → ℝ) (a : Fin k) :
    Formalism.QuantumDeterminants.lowK (allPos k) lam a = lam a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ k := a.2
  simp only [allPos, Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show k - 1 - (a : ℕ) = k - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem lowK_neg_rev (u : Fin k → ℝ) :
    Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) = fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
  funext a
  rw [lowK_allPos, lowK_allPos, Fin.val_rev, Nat.cast_sub a.2]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

end GlobalTheory.ConjTypeW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSquareCardOfInvolution
section
set_option autoImplicit false

namespace GlobalTheory.InertSquareNorm

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

theorem isSquare_card_of_involution {k : Type} [Field k] [Finite k] (s : k ≃+* k)
    (hs : ∀ x, s (s x) = x) (h1 : ∃ x, s x ≠ x) : IsSquare (Nat.card k) := by
  classical
  have hs2 : s ^ 2 = 1 := by
    ext x
    simp [pow_two, hs]
  have hs1 : s ≠ 1 := by
    obtain ⟨x, hx⟩ := h1
    intro h
    exact hx (by rw [h]; rfl)
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1

  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k))
    (fun a b h => RingEquiv.ext (congrFun h))
  haveI : Fintype (Subgroup.zpowers s) := Fintype.ofFinite _
  haveI : FaithfulSMul (Subgroup.zpowers s) k :=
    ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩
  have hcardG : Fintype.card (Subgroup.zpowers s) = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_zpowers s).trans hord
  have hfin : Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k = 2 :=
    (FixedPoints.finrank_eq_card (Subgroup.zpowers s) k).trans hcardG
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers s) k) := Fintype.ofFinite _
  have hk : Fintype.card k = Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k) ^
      Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k :=
    Module.card_eq_pow_finrank
  refine ⟨Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k), ?_⟩
  rw [Nat.card_eq_fintype_card, hk, hfin, pow_two]

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal) := by
  intro E _ _ _ hE P hP
  classical

  let c : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hc : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (c x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hcc : ∀ x : 𝓞 E, c (c x) = x := fun x => RingOfIntegers.ext (by simp [c])

  have hle : P.asIdeal ≤ P.asIdeal.comap c := by
    intro x hx
    rw [Ideal.mem_comap, ← hP]
    exact Ideal.subset_span ⟨x, hx, hc x⟩
  haveI hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let sb : (𝓞 E ⧸ P.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) := Ideal.quotientMap P.asIdeal c hle
  have hsb_mk : ∀ x : 𝓞 E, sb (Ideal.Quotient.mk P.asIdeal x) = Ideal.Quotient.mk P.asIdeal (c x) :=
    fun x => Ideal.quotientMap_mk
  have hsb : ∀ y, sb (sb y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hsb_mk, hsb_mk, hcc]
  let s : (𝓞 E ⧸ P.asIdeal) ≃+* (𝓞 E ⧸ P.asIdeal) :=
    { sb with invFun := sb, left_inv := hsb, right_inv := hsb }
  have hN : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hN]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P.asIdeal P.isMaximal
  have htc : t = c θ := FaithfulSMul.algebraMap_injective (𝓞 E) E (ht.trans (hc θ).symm)
  rw [hN]
  refine isSquare_card_of_involution s hsb ⟨Ideal.Quotient.mk P.asIdeal θ, fun h => hθ ?_⟩
  have h2 : Ideal.Quotient.mk P.asIdeal θ = Ideal.Quotient.mk P.asIdeal t := by
    rw [htc, ← hsb_mk]
    exact h.symm
  exact Ideal.Quotient.eq.mp h2

end GlobalTheory.InertSquareNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerProdCountMulDensityLeTwo
section
open GlobalTheory.Count Finset

namespace GlobalTheory.Count

theorem layerProd_mul_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G H : ℝ → ℝ) :
    layerProd n f j τ G * layerProd n f j τ H = layerProd n f j τ (fun la => G la * H la) := by
  simp only [layerProd, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem layerProd_const_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (c : ℝ) :
    layerProd n f j τ (fun _ => c) = c ^ (∑ i, ∑ k ∈ univ.filter (fun k => i < k),
      (2 * j i * j k * f + 2 * j i * j k * f) + ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f)) := by
  simp only [layerProd, ← pow_add, Finset.prod_pow_eq_pow_sum]

private theorem layerProd_exponent_le_three_mul_sum_mul (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (hn : 2 * ∑ i, j i ≤ n) :
    ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) +
      ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f) ≤ 3 * (∑ i, j i) * n * f := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, j i := ⟨_, rfl⟩
  rw [← hS] at hn ⊢
  have h1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ S * S := by
    calc ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ ∑ i, ∑ k, j i * j k :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = S * S := by rw [hS, Finset.sum_mul_sum]
  have h2 : ∑ i, j i ^ 2 ≤ S * S := by
    calc ∑ i, j i ^ 2 ≤ ∑ i, j i * S := Finset.sum_le_sum fun i _ => by
          rw [sq, hS]
          exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      _ = S * S := by rw [← Finset.sum_mul, hS]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * S + m := ⟨n - 2 * S, by omega⟩
  have hm : 2 * S + m - 2 * S = m := by omega
  have e1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) =
      4 * f * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, (2 * j i * m * f + j i ^ 2 * f) = 2 * m * f * S + f * ∑ i, j i ^ 2 := by
    rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm, e1, e2]
  nlinarith [Nat.mul_le_mul_left f h1, Nat.mul_le_mul_left f h2, Nat.zero_le (S * m * f)]

theorem layerProd_le_exp (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hn : 2 * ∑ i, j i ≤ n) (hτ : StrictMono τ) (h01 : ∀ i, 0 < τ i ∧ τ i < 1)
    (hG : ∀ la, 0 < la → la < 1 → 0 ≤ G la ∧ G la ≤ Real.exp x) :
    layerProd n f j τ G ≤ Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * x) := by
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => (h01 i).2
  have hb : ∀ la, 0 < la → la < 1 → ∀ e : ℕ, 0 ≤ G la ^ e ∧ G la ^ e ≤ Real.exp x ^ e :=
    fun la h0 h1 e => ⟨pow_nonneg (hG la h0 h1).1 e, pow_le_pow_left₀ (hG la h0 h1).1 (hG la h0 h1).2 e⟩
  have hr : ∀ i k, i < k → 0 < τ i / τ k ∧ τ i / τ k < 1 :=
    fun i k hik => ⟨div_pos (hpos i) (hpos k), (div_lt_one (hpos k)).2 (hτ hik)⟩
  have hp : ∀ i k, 0 < τ i * τ k ∧ τ i * τ k < 1 := fun i k =>
    ⟨mul_pos (hpos i) (hpos k), by nlinarith [hpos i, hpos k, hlt i, hlt k]⟩
  have hs : ∀ i, 0 < τ i ^ 2 ∧ τ i ^ 2 < 1 := fun i => ⟨pow_pos (hpos i) 2, by nlinarith [hpos i, hlt i]⟩
  have hex : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have key : layerProd n f j τ G ≤ layerProd n f j τ (fun _ => Real.exp x) := by
    simp only [layerProd]
    apply mul_le_mul
    · apply Finset.prod_le_prod₀
      · intro i _
        apply Finset.prod_nonneg
        intro k hk
        have hik := (Finset.mem_filter.1 hk).2
        exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
      · intro i _
        apply Finset.prod_le_prod₀
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_le_mul (hb _ (hr i k hik).1 (hr i k hik).2 _).2 (hb _ (hp i k).1 (hp i k).2 _).2
            (hb _ (hp i k).1 (hp i k).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
      · intro i _
        exact mul_le_mul (hb _ (hpos i) (hlt i) _).2 (hb _ (hs i).1 (hs i).2 _).2
          (hb _ (hs i).1 (hs i).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_nonneg
      intro i _
      exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      positivity
  refine key.trans ?_
  rw [layerProd_const_eq_pow, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_right _ hx
  exact_mod_cast layerProd_exponent_le_three_mul_sum_mul n f j hn

private theorem mul_prod_mul_le_prod_of_le_one {a : ℕ} (X : ℝ) (u v : Fin a → ℝ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    X * ∏ i, u i * v i ≤ ∏ i, u i := by
  rw [Finset.prod_mul_distrib]
  have hA : 0 ≤ ∏ i, u i := Finset.prod_nonneg fun i _ => hu i
  have hB0 : 0 ≤ ∏ i, v i := Finset.prod_nonneg fun i _ => hv0 i
  have hB1 : ∏ i, v i ≤ 1 := Finset.prod_le_one₀ (fun i _ => hv0 i) (fun i _ => hv1 i)
  calc X * ((∏ i, u i) * ∏ i, v i) ≤ 1 * ((∏ i, u i) * ∏ i, v i) :=
        mul_le_mul_of_nonneg_right hX1 (mul_nonneg hA hB0)
    _ ≤ ∏ i, u i := by rw [one_mul]; exact mul_le_of_le_one_right hA hB1

theorem layerProd_count_mul_density_le_two :
    ∀ (n f q a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (de : ℝ), ∑ i, j i ≤ q → 2 * q ≤ n → StrictMono τ →
      (∀ i, 0 < τ i ∧ τ i < 1 / 2) → 0 ≤ de → de * q * n * f ≤ 1 / 100 →
      layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ (fun la => la) ≤ 2 ∧
      layerProd n f j τ (fun la => la) ≤ ∏ i, τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) := by
  intro n f q a j τ de hq hqn hτ h01 hde hsmall
  have hS2 : 2 * ∑ i, j i ≤ n := by omega
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => by linarith [(h01 i).2]
  constructor
  · rw [layerProd_mul_layerProd]
    have hb := layerProd_le_exp n f j τ (fun la => (1 + 12 * de / la) * la) (12 * de) (by positivity)
      hS2 hτ (fun i => ⟨hpos i, hlt i⟩) (fun la h0 h1 => by
        show 0 ≤ (1 + 12 * de / la) * la ∧ (1 + 12 * de / la) * la ≤ Real.exp (12 * de)
        rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul]
        exact ⟨by linarith, by linarith [Real.add_one_le_exp (12 * de)]⟩)
    refine hb.trans ?_
    have hnat : 3 * (∑ i, j i) * n * f ≤ 3 * q * n * f := by gcongr
    have hcast : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) ≤ 3 * q * n * f := by exact_mod_cast hnat
    have hexp : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ 36 / 100 := by
      calc ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ (3 * q * n * f : ℝ) * (12 * de) :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
        _ = 36 * (de * q * n * f) := by ring
        _ ≤ 36 / 100 := by linarith
    calc Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de)) ≤ Real.exp (36 / 100) :=
          Real.exp_le_exp.2 hexp
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  · unfold layerProd
    refine mul_prod_mul_le_prod_of_le_one _ (fun i => τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f))
      (fun i => (τ i ^ 2) ^ (j i ^ 2 * f)) ?_ ?_ (fun i => pow_nonneg (hpos i).le _)
      (fun i => pow_nonneg (pow_pos (hpos i) 2).le _) ?_
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
    · apply Finset.prod_le_one₀
      · intro i _
        apply Finset.prod_nonneg
        intro k _
        exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
      · intro i _
        apply Finset.prod_le_one₀
        · intro k _
          exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          have hq1 : τ i / τ k ≤ 1 := ((div_lt_one (hpos k)).2 (hτ hik)).le
          have hp1 : τ i * τ k ≤ 1 := by nlinarith [hpos i, hpos k, hlt i, hlt k]
          exact mul_le_one₀ (pow_le_one₀ (div_pos (hpos i) (hpos k)).le hq1)
            (pow_nonneg (mul_pos (hpos i) (hpos k)).le _) (pow_le_one₀ (mul_pos (hpos i) (hpos k)).le hp1)
    · intro i
      have : τ i ^ 2 ≤ 1 := by nlinarith [hpos i, hlt i]
      exact pow_le_one₀ (pow_pos (hpos i) 2).le this

end GlobalTheory.Count
end

