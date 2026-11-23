module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOperatorParametricExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianSplitUnitaryLowerBlockInvertible
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

section Transverse

variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem transv_kills (c : k →+* k) (S A C : Matrix ν ν k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu : A *ᵥ u = 0) (w : ν → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

def transvRankOne (S : Matrix ν ν k) (j : ν) : Matrix ν ν k :=
  Matrix.of fun a b => if a = j then S b j else 0

theorem transvRankOne_adm (c : k →+* k) (S : Matrix ν ν k) (hS : Sᵀ = -S.map c) (j : ν) :
    (transvRankOne S j)ᵀ * S + S * (transvRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, transvRankOne, h3, h1]

theorem transvRankOne_mulVec (S : Matrix ν ν k) (j : ν) (v : ν → k) :
    transvRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [transvRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [transvRankOne, mulVec, dotProduct, h]

theorem transv_step (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (A C : Matrix ν ν k)
    (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : ν, (∀ w, (A + transvRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + transvRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : ν → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := transv_kills c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, transvRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

theorem transv_iso_update (c : k →+* k) (S A C X : Matrix ν ν k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem skewAdmissibleMatrix_add (c : k →+* k) (S X Y : Matrix ν ν k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

theorem transv_field (c : k →+* k) (S : Matrix ν ν k) (hSu : IsUnit S.det) (hS : Sᵀ = -S.map c)
    (A C : Matrix ν ν k) (hinj : ∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  suffices H : ∀ m : ℕ, ∀ A : Matrix ν ν k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : ν → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix ν ν k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := transv_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := transvRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + transvRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : ν → k, (A + transvRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + transvRankOne S j * C) (by omega) hinj'
        (transv_iso_update c S A C _ hX1 hiso)
      refine ⟨transvRankOne S j + X2, skewAdmissibleMatrix_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end Transverse

end GlobalTheory.KSp

namespace GlobalTheory.KSp

theorem exists_herm_transverse : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  have hδ : δ ≠ 0 := hE.unit.ne_zero
  set M := mat c g with hMdef
  set cc := M.toBlocks₂₁
  set dd := M.toBlocks₂₂
  have hU := (mem_UG_iff c _).mp g.2
  change M * stdJ ν E * (M.map c)ᵀ = stdJ ν E at hU
  have key : cc * (dd.map c)ᵀ = dd * (cc.map c)ᵀ := by
    have h := congrArg Matrix.toBlocks₂₂ hU
    rw [← fromBlocks_toBlocks M] at h
    simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul] at h
    have h' : cc * (dd.map c)ᵀ + -(dd * (cc.map c)ᵀ) = 0 := by rw [← h]; abel
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h')

  set S : Matrix ν ν E := δ • (1 : Matrix ν ν E)
  have hcδ : c δ = -δ := hE.anti
  have hSu : IsUnit S.det := by
    rw [isUnit_iff_ne_zero]; simp [S, Matrix.det_smul, hδ]
  have hS : Sᵀ = -S.map (c : E →+* E) := by
    ext i j; by_cases h : i = j <;> simp [S, Matrix.one_apply, h, hcδ, eq_comm]
  have hmapC : (δ • ddᵀ).map (c : E →+* E) = (-δ) • (dd.map c)ᵀ := by
    ext i j; simp [hcδ]
  have hiso : (ccᵀ)ᵀ * S * (δ • ddᵀ).map (c : E →+* E) + (δ • ddᵀ)ᵀ * S * (ccᵀ).map (c : E →+* E) = 0 := by
    rw [hmapC]
    have e1 : (ccᵀ).map (c : E →+* E) = (cc.map c)ᵀ := rfl
    rw [e1]
    simp only [S, transpose_transpose, transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, key]
    rw [← add_smul]; simp
  have hinj : ∀ u : ν → E, ccᵀ *ᵥ u = 0 → (δ • ddᵀ) *ᵥ u = 0 → u = 0 := by
    intro u h1 h2
    rw [mulVec_transpose] at h1
    rw [smul_mulVec, mulVec_transpose, smul_eq_zero] at h2
    have h2' : u ᵥ* dd = 0 := h2.resolve_left hδ
    have hw : (Sum.elim 0 u : ν ⊕ ν → E) ᵥ* M = 0 := by
      rw [← fromBlocks_toBlocks M]
      funext i
      rcases i with i | i
      · have := congrFun h1 i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, cc] using this
      · have := congrFun h2' i
        simpa [vecMul, dotProduct, fromBlocks, Fintype.sum_sum_type, dd] using this
    have hinv : M * ((g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = 1 := by
      change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
      rw [mul_inv_cancel]; rfl
    have hw0 : (Sum.elim 0 u : ν ⊕ ν → E) = 0 := by
      rw [← vecMul_one (Sum.elim 0 u : ν ⊕ ν → E), ← hinv, ← vecMul_vecMul, hw, zero_vecMul]
    funext i
    simpa using congrFun hw0 (Sum.inr i)
  obtain ⟨X, hX, hdet⟩ := transv_field (c : E →+* E) S hSu hS ccᵀ (δ • ddᵀ) hinj hiso
  refine ⟨δ • Xᵀ, ?_, ?_⟩
  · have hX' : δ • Xᵀ + δ • X.map (c : E →+* E) = 0 := by
      simpa [S, Matrix.mul_smul, Matrix.smul_mul] using hX
    rw [← smul_add, smul_eq_zero] at hX'
    have hX'' : X.map (c : E →+* E) = -Xᵀ := eq_neg_of_add_eq_zero_right (hX'.resolve_left hδ)
    have e : (δ • Xᵀ).map c = (-δ) • (X.map (c : E →+* E))ᵀ := by ext i j; simp [hcδ]
    rw [e, hX'']
    simp
  · have e : (ccᵀ + X * (δ • ddᵀ))ᵀ = cc + dd * (δ • Xᵀ) := by
      simp [transpose_add, transpose_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [← e, det_transpose]
    exact (isUnit_iff_ne_zero).mp hdet

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelations
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem groupChunk_extend {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by
  classical

  have key : ∀ g u w, C u → C (g * u) → C w → C (g * w) → C (u⁻¹ * w) →
      f (g * u) * (f u)⁻¹ = f (g * w) * (f w)⁻¹ := by
    intro g u w hu hgu hw hgw huw
    have h1 : f w = f u * f (u⁻¹ * w) := by
      have h := hmul u (u⁻¹ * w) hu huw (by rwa [mul_inv_cancel_left])
      rwa [mul_inv_cancel_left] at h
    have h2 : f (g * w) = f (g * u) * f (u⁻¹ * w) := by
      have h := hmul (g * u) (u⁻¹ * w) hgu huw (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at h
    rw [h1, h2]
    group
  choose u₀ hu₀ using fun g : G => hgen {1, g}
  have hu₀1 : ∀ g, C (u₀ g) := fun g => by simpa using hu₀ g 1 (by simp)
  have hu₀g : ∀ g, C (g * u₀ g) := fun g => hu₀ g g (by simp)
  let φ : G → H := fun g => f (g * u₀ g) * (f (u₀ g))⁻¹
  have hφ : ∀ g u, C u → C (g * u) → φ g = f (g * u) * (f u)⁻¹ := by
    intro g u hu hgu
    obtain ⟨w, hw⟩ := hgen {1, g, u⁻¹, (u₀ g)⁻¹}
    have hw1 : C w := by simpa using hw 1 (by simp)
    have hwg : C (g * w) := hw g (by simp)
    have hwu : C (u⁻¹ * w) := hw u⁻¹ (by simp)
    have hwu₀ : C ((u₀ g)⁻¹ * w) := hw (u₀ g)⁻¹ (by simp)
    rw [key g u w hu hgu hw1 hwg hwu]
    exact key g (u₀ g) w (hu₀1 g) (hu₀g g) hw1 hwg hwu₀
  refine ⟨MonoidHom.mk' φ ?_, fun g u hu hgu => hφ g u hu hgu⟩
  intro g h
  obtain ⟨w, hw⟩ := hgen {1, h, g * h}
  have hw1 : C w := by simpa using hw 1 (by simp)
  have hwh : C (h * w) := hw h (by simp)
  have hwgh : C (g * h * w) := hw (g * h) (by simp)
  rw [hφ (g * h) w hw1 hwgh, hφ h w hw1 hwh, hφ g (h * w) hwh (by rwa [← mul_assoc]),
    ← mul_assoc g h w]
  group

theorem bigCell_hom : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  classical
  intro G H _ _ P w ρ W ha hb hc
  let C : G → Prop := fun g => ∃ p₁ p₂ : P, g = p₁ * w * p₂

  have hwd : ∀ p₁ p₂ q₁ q₂ : P, (p₁ : G) * w * p₂ = q₁ * w * q₂ →
      ρ p₁ * W * ρ p₂ = ρ q₁ * W * ρ q₂ := by
    intro p₁ p₂ q₁ q₂ h
    have h' : w * ((p₂ * q₂⁻¹ : P) : G) = ((p₁⁻¹ * q₁ : P) : G) * w := by
      push_cast
      calc w * ((p₂ : G) * (q₂ : G)⁻¹)
          = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂) * (q₂ : G)⁻¹ := by group
        _ = (p₁ : G)⁻¹ * ((q₁ : G) * w * q₂) * (q₂ : G)⁻¹ := by rw [h]
        _ = (p₁ : G)⁻¹ * q₁ * w := by group
    have h'' := ha _ _ h'
    rw [map_mul, map_mul, map_inv, map_inv] at h''
    calc ρ p₁ * W * ρ p₂ = ρ p₁ * (W * (ρ p₂ * (ρ q₂)⁻¹)) * ρ q₂ := by group
      _ = ρ p₁ * ((ρ p₁)⁻¹ * ρ q₁ * W) * ρ q₂ := by rw [h'']
      _ = ρ q₁ * W * ρ q₂ := by group
  let f : G → H := fun g => if h : C g then ρ h.choose * W * ρ h.choose_spec.choose else 1
  have hf : ∀ p₁ p₂ : P, f (p₁ * w * p₂) = ρ p₁ * W * ρ p₂ := by
    intro p₁ p₂
    have hC : C (p₁ * w * p₂) := ⟨p₁, p₂, rfl⟩
    dsimp only [f]
    rw [dite_eq_left hC]
    exact hwd _ _ _ _ hC.choose_spec.choose_spec.symm
  have hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y := by
    rintro x y ⟨p₁, p₂, rfl⟩ ⟨q₁, q₂, rfl⟩ ⟨r₁, r₂, hr⟩
    have hin : ∃ a b : P, w * ((p₂ * q₁ : P) : G) * w = a * w * b :=
      ⟨p₁⁻¹ * r₁, r₂ * q₂⁻¹, by
        push_cast
        calc w * ((p₂ : G) * q₁) * w
            = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)) * (q₂ : G)⁻¹ := by group
          _ = (p₁ : G)⁻¹ * ((r₁ : G) * w * r₂) * (q₂ : G)⁻¹ := by rw [hr]
          _ = (p₁ : G)⁻¹ * r₁ * w * ((r₂ : G) * (q₂ : G)⁻¹) := by group⟩
    obtain ⟨a, b, hab, hW⟩ := hb _ hin
    rw [map_mul] at hW
    have hxy : (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂) = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by
      calc (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)
          = (p₁ : G) * (w * ((p₂ * q₁ : P) : G) * w) * q₂ := by push_cast; group
        _ = (p₁ : G) * ((a : G) * w * b) * q₂ := by rw [hab]
        _ = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by push_cast; group
    rw [hxy, hf, hf, hf, map_mul, map_mul]
    calc ρ p₁ * ρ a * W * (ρ b * ρ q₂) = ρ p₁ * (ρ a * W * ρ b) * ρ q₂ := by group
      _ = ρ p₁ * (W * (ρ p₂ * ρ q₁) * W) * ρ q₂ := by rw [hW]
      _ = ρ p₁ * W * ρ p₂ * (ρ q₁ * W * ρ q₂) := by group
  obtain ⟨Φ, hΦ⟩ := groupChunk_extend C f hmul hc
  refine ⟨Φ, fun p => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hc {1}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    have e1 : (p : G) * u = ((p * a : P) : G) * w * b := by
      rw [hab]
      push_cast
      group
    rw [hΦ p u ⟨a, b, hab⟩ ⟨p * a, b, e1⟩, e1, hab, hf, hf, map_mul]
    group
  · obtain ⟨u, hu⟩ := hc {1, w}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    obtain ⟨c, d, hcd⟩ := hu w (by simp)
    have hin : ∃ p₁ p₂ : P, w * (a : G) * w = p₁ * w * p₂ :=
      ⟨c, d * b⁻¹, by
        calc w * (a : G) * w = w * u * (b : G)⁻¹ := by rw [hab]; group
          _ = (c : G) * w * d * (b : G)⁻¹ := by rw [hcd]
          _ = (c : G) * w * ((d * b⁻¹ : P) : G) := by push_cast; group⟩
    obtain ⟨r₁, r₂, hr, hW⟩ := hb a hin
    have e1 : w * u = (r₁ : G) * w * ((r₂ * b : P) : G) := by
      rw [hab]
      push_cast
      calc w * ((a : G) * w * b) = w * a * w * b := by group
        _ = (r₁ : G) * w * ((r₂ : G) * b) := by rw [hr]; group
    rw [hΦ w u ⟨a, b, hab⟩ ⟨c, d, hcd⟩, e1, hab, hf, hf, map_mul]
    calc ρ r₁ * W * (ρ r₂ * ρ b) * (ρ a * W * ρ b)⁻¹ = (ρ r₁ * W * ρ r₂) * (ρ a * W)⁻¹ := by group
      _ = (W * ρ a * W) * (ρ a * W)⁻¹ := by rw [hW]
      _ = W := by group

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlat
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory

theorem unit_splits_of_projective_faithfullyFlat :
    ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  intro R D _ _ _ _ hP hF
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hP
  let ev : (D →ₗ[R] R) →ₗ[R] R :=
    { toFun := fun τ => τ 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  by_cases hI : LinearMap.range ev = ⊤
  · obtain ⟨τ, hτ⟩ := LinearMap.mem_range.mp (hI ▸ Submodule.mem_top : (1 : R) ∈ LinearMap.range ev)
    exact ⟨τ, hτ⟩
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal (LinearMap.range ev) hI
  exfalso
  have hcoord : ∀ x : D, s 1 x ∈ m := fun x =>
    hIm (LinearMap.mem_range.mpr ⟨Finsupp.lapply x ∘ₗ s, rfl⟩)
  have h1 : (1 : D) ∈ m • (⊤ : Submodule R D) := by
    have : Finsupp.linearCombination R id (s 1) = (1 : D) := LinearMap.congr_fun hs 1
    rw [← this, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (hcoord x) Submodule.mem_top
  have hmul : ∀ d : D, ∀ y ∈ m • (⊤ : Submodule R D), d * y ∈ m • (⊤ : Submodule R D) := by
    intro d y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr n _
      rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro x z hx hz
      rw [mul_add]; exact Submodule.add_mem _ hx hz
  apply Module.FaithfullyFlat.submodule_ne_top (M := D) hm
  rw [eq_top_iff]
  intro d _
  simpa using hmul d 1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibreStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (exact GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPolynomialMemPrimeLocalization
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → P ≠ ⊥ → ∃ g : Polynomial T, g ≠ 0 ∧ algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P := by
  first | (exact @GlobalTheory.genFibre_prime_meets_polynomial) | (exact GlobalTheory.genFibre_prime_meets_polynomial) | (intros; apply GlobalTheory.genFibre_prime_meets_polynomial  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgreeStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  first | exact @GlobalTheory.SecGlue.exists_pair_lift_comb | exact GlobalTheory.SecGlue.exists_pair_lift_comb | (intros; apply GlobalTheory.SecGlue.exists_pair_lift_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOriginStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.OriginResidue.residue_origin) | (exact GlobalTheory.OriginResidue.residue_origin) | (intros; apply GlobalTheory.OriginResidue.residue_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOperatorParametricExtensionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_operator_parametric_extension : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V') (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  first | exact @GlobalTheory.SchwartzFstOp.exists_tensorId | exact GlobalTheory.SchwartzFstOp.exists_tensorId | (intros; apply GlobalTheory.SchwartzFstOp.exists_tensorId <;> assumption)
end

