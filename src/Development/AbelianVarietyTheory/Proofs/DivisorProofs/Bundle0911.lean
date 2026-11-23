module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogPeriodFamily
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem GlobalTheory.AbsLattice.exists_unit_of_conj_stable : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by

  intro A B _ _ j Λ R r e h0 h1 hadd hneg hmul hR0 hR1 hRadd hRneg hRmul hrep hmem hE hden hsq X hX
  rcases r with _ | n
  · have hall : ∀ a : A, a = 0 := fun a => by
      obtain ⟨β, hβ, -⟩ := hrep a
      simpa using hβ
    have key : ∀ a : A, a ∈ Λ := fun a => by rw [hall a]; exact h0
    exact ⟨1, key _, key _⟩
  ·
    have hL : ∀ ρ ∈ R, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (j ρ * x) ∈ Λ := by
      intro ρ hρ x hx
      have : (X : A) * (j ρ * x) = ((X : A) * j ρ * ↑X⁻¹) * ((X : A) * x) := by
        simp [mul_assoc]
      rw [this]; exact hmul _ (hX ρ hρ) _ hx
    have hRt : ∀ μ ∈ Λ, ∀ x : A, (X : A) * x ∈ Λ → (X : A) * (x * μ) ∈ Λ := by
      intro μ hμ x hx
      rw [← mul_assoc]; exact hmul _ hx _ hμ
    have hS : ∀ (N : ℕ) (f : Fin N → A), (∀ k, (X : A) * f k ∈ Λ) → (X : A) * ∑ k, f k ∈ Λ := by
      intro N f hf
      rw [Finset.mul_sum]
      exact Finset.sum_induction _ (· ∈ Λ) (fun a b ha hb => hadd a ha b hb) h0 (fun k _ => hf k)
    have hsingle : ∀ b : B, ∑ i'', j ((Pi.single (0 : Fin (n+1)) b : Fin (n+1) → B) i'') * e i'' = j b * e 0 := by
      intro b
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, map_zero, zero_mul]
      · simp
    have hsingleR : ∀ b : B, j b * e 0 ∈ Λ ↔ b ∈ R := by
      intro b
      rw [← hsingle, hmem]
      constructor
      · intro h; simpa using h 0
      · intro hb i
        by_cases hi : i = 0
        · subst hi; simpa using hb
        · rw [Pi.single_eq_of_ne hi]; exact hR0
    have he0 : e 0 ∈ Λ := by
      have := (hsingleR 1).2 hR1
      rwa [map_one, one_mul] at this

    have hA : ∀ β : Fin (n+1) → B, (X : A) * (∑ i, j (β i) * e i) ∈ Λ →
        ∀ i', (X : A) * (j (β i') * e 0) ∈ Λ := by
      intro β hx i'
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE 0 i'
      rw [← hf β]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hx))

    have hB : ∀ b : B, (X : A) * (j b * e 0) ∈ Λ → ∀ i, (X : A) * (j b * e i) ∈ Λ := by
      intro b hb i
      obtain ⟨N, ρ, μ, hρ, hμ, hf⟩ := hE i 0
      have h := hf (Pi.single 0 b)
      rw [hsingle, Pi.single_eq_same] at h
      rw [← h]
      exact hS N _ (fun k => hRt (μ k) (hμ k) _ (hL _ (hρ k) _ hb))
    have hsum : ∀ β : Fin (n+1) → B, (∀ i, (X : A) * (j (β i) * e 0) ∈ Λ) →
        (X : A) * (∑ i, j (β i) * e i) ∈ Λ :=
      fun β hβ => hS _ _ (fun i => hB _ (hβ i) i)
    have hRint : ∀ z : ℤ, (z : B) ∈ R := by
      intro z
      induction z using Int.induction_on with
      | zero => simpa using hR0
      | succ i ih => rw [Int.cast_add, Int.cast_one]; exact hRadd _ ih _ hR1
      | pred i ih =>
        have : ((-(i : ℤ) - 1 : ℤ) : B) = ((-(i : ℤ) : ℤ) : B) + -1 := by push_cast; ring
        rw [this]; exact hRadd _ ih _ (hRneg _ hR1)
    obtain ⟨D₁, hD₁, hD₁m⟩ := hden (X : A)
    obtain ⟨D₂, hD₂, hD₂m⟩ := hden (↑X⁻¹ : A)
    have hDR : ∀ ρ ∈ R, (X : A) * (j (ρ * D₁) * e 0) ∈ Λ := by
      intro ρ hρ
      rw [map_mul, map_intCast, mul_assoc]
      apply hL ρ hρ
      rw [← mul_assoc, ← (Int.cast_commute D₁ (X : A)).eq]
      exact hmul _ hD₁m _ he0
    have hDI : ∀ β : B, (X : A) * (j β * e 0) ∈ Λ → β * D₂ ∈ R := by
      intro β hβ
      rw [← hsingleR]
      have : j (β * D₂) * e 0 = ((D₂ : A) * ↑X⁻¹) * ((X : A) * (j β * e 0)) := by
        rw [map_mul, map_intCast, ← (Int.cast_commute D₂ (j β)).eq, mul_assoc, mul_assoc,
          Units.inv_mul_cancel_left]
      rw [this]; exact hmul _ hD₂m _ hβ
    obtain ⟨m, hm⟩ := hsq {β | (X : A) * (j β * e 0) ∈ Λ}
      (by show (X : A) * (j 0 * e 0) ∈ Λ; simpa using h0)
      (fun x hx y hy => by
        show (X : A) * (j (x + y) * e 0) ∈ Λ
        rw [map_add (f := _), add_mul, mul_add]; exact hadd _ hx _ hy)
      (fun ρ hρ x hx => by
        show (X : A) * (j (ρ * x) * e 0) ∈ Λ
        rw [map_mul, mul_assoc]; exact hL ρ hρ _ hx)
      ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂,
        fun x hx => by
          show (X : A) * (j (((D₁ * D₂ : ℤ) : B) * x) * e 0) ∈ Λ
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₂ : B) * (x * D₁) := by push_cast; ring
          rw [this, map_mul, mul_assoc]
          exact hL _ (hRint D₂) _ (hDR x hx),
        fun x hx => by
          have : ((D₁ * D₂ : ℤ) : B) * x = (D₁ : B) * (x * D₂) := by push_cast; ring
          rw [this]
          exact hRmul _ (hRint D₁) _ (hDI x hx)⟩
    refine ⟨m, ?_, ?_⟩
    · obtain ⟨γ, hγ, -⟩ := hrep 1
      have hγR : ∀ i, γ i ∈ R := (hmem γ).1 (hγ ▸ h1)
      have hjm : j (m : B) = ∑ i, j ((m : B) * γ i) * e i := by
        conv_lhs => rw [← mul_one (j (m : B)), hγ]
        rw [Finset.mul_sum]
        simp only [map_mul, mul_assoc]
      rw [hjm]
      exact hsum _ (fun i => (hm _).2 ⟨γ i, hγR i, rfl⟩)
    · obtain ⟨β, hβ, -⟩ := hrep (↑X⁻¹ : A)
      have hXinv : (X : A) * (∑ i, j (β i) * e i) ∈ Λ := by
        rw [← hβ, Units.mul_inv]; exact h1
      have hc : ∀ i, ∃ ρ ∈ R, β i = (m : B) * ρ := fun i => (hm _).1 (hA β hXinv i)
      choose ρ hρR hρeq using hc
      have : j (↑m⁻¹ : B) * (↑X⁻¹ : A) = ∑ i, j (ρ i) * e i := by
        rw [hβ, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← mul_assoc, ← map_mul, hρeq, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact (hmem ρ).2 hρR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClass
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_nsmul_sub_eff : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  intro R _ Y f _ H m s M hH hM hs
  have hD : (dual M).IsLB := isLB_dual hM
  obtain ⟨t₀, ht⟩ := exists_sec_tw_ne_zero R Y f H m s (dual M) hH hD hs
  refine ⟨(max t₀ 0).toNat, ?_⟩
  have hc : t₀ ≤ ((max t₀ 0).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (le_max_right _ _)]; exact le_max_left _ _
  obtain ⟨σ, i, hσ⟩ := ht _ hc
  have key := eff_of_sec _ (isLB_tw hD hH _) σ i hσ
  have e : cls (tw (dual M) H ((max t₀ 0).toNat : ℤ)) (isLB_tw hD hH _) =
      cls (dual M) hD - cls (pw H (-((max t₀ 0).toNat : ℤ))) (isLB_pw hH _) :=
    cls_div hD (isLB_pw hH _) (isLB_tw hD hH _)
  rw [e, cls_pw hH, cls_dual hM hD, neg_zsmul, natCast_zsmul] at key
  convert key using 1
  abel
end GlobalTheory.EffBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOne
section
open Matrix GlobalTheory.LKTrip

namespace GlobalTheory.HermitianMajorantIdentities

theorem mul_vecMulVec_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    A * vecMulVec u v * B = vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_vecMulVec {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec u (star u) *ᵥ x = (star x ⬝ᵥ u) * (star u ⬝ᵥ x) := by
  rw [vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]

theorem herm_swap {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ H *ᵥ x = star (star x ⬝ᵥ H *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]

end GlobalTheory.HermitianMajorantIdentities

namespace GlobalTheory


open GlobalTheory.HermitianMajorantIdentities in
theorem exists_posDef_majorant_of_sigPosH_eq_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  intro n H hH hdet hsig z hz
  set a : ℝ := (star z ⬝ᵥ H *ᵥ z).re with ha
  have hzz : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := by
    have h := herm_swap hH z z
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  set u : Fin n → ℂ := H *ᵥ z with hu
  have hux : ∀ x, star u ⬝ᵥ x = star z ⬝ᵥ H *ᵥ x := by
    intro x; rw [hu, star_mulVec, hH.eq, ← dotProduct_mulVec]
  refine ⟨((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hH.eq, conjTranspose_vecMulVec, star_star]
    simp [Complex.star_def]
  · intro x hx
    set q := star z ⬝ᵥ H *ᵥ x with hq
    set t : ℂ := q / (a : ℂ) with ht
    set x' := x - t • z with hx'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hzx' : star z ⬝ᵥ H *ᵥ x' = 0 := by
      rw [hx', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hzz, ← hq, ht, smul_eq_mul]
      field_simp; ring
    have hx'z : star x' ⬝ᵥ H *ᵥ z = 0 := by
      rw [herm_swap hH z x', hzx', star_zero]
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have hxe : x = t • z + x' := by rw [hx']; abel
    have hxx : star x ⬝ᵥ H *ᵥ x = star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x' := by
      conv_lhs => rw [hxe]
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzx', hx'z, hzz']
      ring
    have hxz : star x ⬝ᵥ H *ᵥ z = star q := herm_swap hH z x
    have hP : star x ⬝ᵥ (((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H) *ᵥ x
        = ((2 / a : ℝ) : ℂ) * (star q * q) - (star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x') := by
      rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, form_vecMulVec, hux, hxx,
        smul_eq_mul]
      rw [show star x ⬝ᵥ u = star q from hxz]
    have hqt : q = t * (a : ℂ) := by rw [ht]; field_simp
    have hnt : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hP, hqt, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e1 : ((starRingEnd ℂ) t * (a : ℂ) * (t * (a : ℂ))) = ((Complex.normSq t * a * a : ℝ) : ℂ) := by
      rw [← Complex.star_def, show star t * (a:ℂ) * (t * (a:ℂ)) = (star t * t) * ((a * a : ℝ) : ℂ) by push_cast; ring, hnt]
      push_cast; ring
    rw [e1, ← Complex.star_def, hnt]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul]
    have hapos : 0 < a := hz
    by_cases h0 : x' = 0
    · have htne : t ≠ 0 := by
        intro ht0
        apply hx
        rw [hxe, h0, ht0, zero_smul, add_zero]
      have hnpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr htne
      rw [h0]
      simp only [star_zero, zero_dotProduct, Complex.zero_re, add_zero]
      field_simp
      nlinarith [mul_pos hnpos hapos]
    · have hneg := re_form_neg_of_orth_of_sigPosH_eq_one H hH hdet hsig z x' hz hzx' h0
      have hn0 : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
      have : 2 / a * (Complex.normSq t * a * a) - Complex.normSq t * a = Complex.normSq t * a := by
        field_simp; ring
      nlinarith [mul_nonneg hn0 hapos.le]
  · intro Y s c hs hY hYz
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hA : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = (s : ℂ) * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hY,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hB : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = star c * (star z ⬝ᵥ H *ᵥ (Y *ᵥ x)) := by
      intro x
      rw [hYz, star_smul, smul_dotProduct, smul_eq_mul]
    have hsc : (s : ℂ) = star c * c := by
      have h1 := (hA z).symm.trans (hB z)
      rw [hYz, mulVec_smul, dotProduct_smul, smul_eq_mul, hzz'] at h1
      have h2 : ((s : ℂ) - star c * c) * (a : ℂ) = 0 := by rw [sub_mul, h1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha0)
    have hc0 : star c ≠ 0 := by
      intro h0
      have : (s : ℂ) = 0 := by rw [hsc, h0, zero_mul]
      exact hs.ne' (by exact_mod_cast this)
    have hrow : ∀ x, star z ⬝ᵥ H *ᵥ (Y *ᵥ x) = c * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      have h1 := (hA x).symm.trans (hB x)
      rw [hsc, mul_assoc] at h1
      exact (mul_left_cancel₀ hc0 h1).symm
    have hrowv : star u ᵥ* Y = c • star u := by
      funext j
      have h1 : (star u ᵥ* Y) ⬝ᵥ Pi.single j 1 = (c • star u) ⬝ᵥ Pi.single j 1 := by
        rw [← dotProduct_mulVec, hux, hrow, smul_dotProduct, hux, smul_eq_mul]
      simpa [dotProduct_single] using h1
    have hcolv : Yᴴ *ᵥ u = star c • u := by
      have h1 := congrArg star hrowv
      rw [star_vecMul, star_star, star_smul, star_star] at h1
      exact h1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hcolv,
      hrowv, hY]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hsc]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOneStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  first | exact @GlobalTheory.exists_prime_eq_span_of_coheight_le_one | exact GlobalTheory.exists_prime_eq_span_of_coheight_le_one | (intros; apply GlobalTheory.exists_prime_eq_span_of_coheight_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAwayStatement
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p → ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.ratDen_pow_of_intAfP) | (exact GlobalTheory.ratDen_pow_of_intAfP) | (intros; apply GlobalTheory.ratDen_pow_of_intAfP  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAway
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecBGenerating
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic

namespace GlobalTheory.Mum

theorem exists_secB_generating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (α : D.X),
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (n : ℕ) (b : Fin n → D.SecB k α), ⨆ j, nonzeroLocus (b j) = ⊤ := by
  intro R _ _ _ D α
  have hL := D.P.isLB
  have := D.P.isAb.proper
  have hA : IsAmpleLB D.P.L := (relAmple_iff_isAmpleLB_of_isAffine D.P.A hL).1 D.P.ample
  have hN : ∀ k, (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)).IsLB := fun k => LB.isLB_linComb hL _ _
  obtain ⟨k₀, hk⟩ := eventually_atTop.1 (hA.eventually_isGenerated_tens_lbPow (hN 0))
  refine ⟨k₀, fun k h => ?_⟩
  have hP := isLB_lbPow hL k
  have hT := isLB_tens (hN 0) hP
  refine (hk k h).of_lbIso (hN k) (iso_of_chart hT ⟨fun j => (j, fun _ => j 0), fun _ _ hj => ⟨hj, ?_⟩, ?_⟩)
  · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  · intro y p q hp hq
    set_option maxHeartbeats 200000 in
    refine (gm_linComb D.P.L (D.famφB α) (DegPre.famε k) (𝟙 _) y p q hp hq).trans ?_
    refine ((gm_tens (LB.LinComb D.P.L (D.famφB α) (DegPre.famε 0)) (lbPow D.P.L k) (𝟙 _) y (p, fun _ => p 0) (q, fun _ => q 0) ⟨hp, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0⟩ ⟨hq, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0⟩).trans ?_).symm
    refine (congrArg₂ (· * ·) (gm_linComb D.P.L (D.famφB α) (DegPre.famε 0) (𝟙 _) y p q hp hq) (gm_linComb D.P.L (fun _ : PUnit => 𝟙 _) (fun _ => (k : ℤ)) (𝟙 _) y (fun _ => p 0) (fun _ => q 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hp 0) (Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hq 0))).trans ?_
    simp only [Fin.prod_univ_four, Fintype.prod_unique, DegPre.famφB, DegPre.famε, Matrix.cons_val, Category.id_comp, zpow_sub, zpow_one]
    simp only [Nat.cast_zero, zpow_zero, one_mul]
    ac_rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroChartOfEffectiveClass
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem exists_sec_of_eff {X : Scheme.{0}} (N : LB X) (hN : N.IsLB) (h : Eff (cls N hN)) :
    ∃ (σ : LB.Sec N) (j : N.ι), σ.f j ≠ 0 := by
  obtain ⟨N', hN', hc, σ, j, hj⟩ := h
  obtain ⟨w, hw⟩ := (cls_eq_iff hN' hN).1 hc
  let e : LB.Sec N' ≃ₗ[Γ(X, ⊤)] LB.Sec N :=
    (SecOn.topEquiv N').symm ≪≫ₗ SecOn.congr hN' hN w hw ⊤ ≪≫ₗ SecOn.topEquiv N
  have hσ : σ ≠ 0 := fun h0 => hj (by rw [h0]; rfl)
  have he : e σ ≠ 0 := by
    intro h0
    exact hσ (e.injective (h0.trans (map_zero e).symm))
  by_contra hne
  push_neg at hne
  exact he (HighTwist.sec_eq_zero _ (hne (e σ)))

end GlobalTheory.EffBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryLiftDetOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_supported_unitary_lift_detOne : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D}, Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 → ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧ (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  first | exact @GlobalTheory.ParahoricLiftDet.exists_local_lift_det | exact GlobalTheory.ParahoricLiftDet.exists_local_lift_det | (intros; apply GlobalTheory.ParahoricLiftDet.exists_local_lift_det <;> assumption)
end

