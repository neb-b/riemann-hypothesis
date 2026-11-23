module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LintegralMulRight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem aLin_mulVec_of_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = hermC τ.1 X.Gm w (FD.col (mat x₂ τ) a) := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_pos h, hermC, FD.col, mat, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem aLin_mulVec_of_not_lt (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (w : Fin r → ℂ) {a : Fin r}
    (h : ¬ (a : ℕ) < X.p0) :
    (aLin X x₁ x₂ τ *ᵥ w) a = ((mat x₁ τ)⁻¹ *ᵥ w) a := by
  simp only [aLin, mulVec, dotProduct, of_apply, if_neg h]

variable {X}

theorem pos_of_upper {x₁ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (x₂ : Frame X.Ψ r) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    0 < (hermC τ.1 X.Gm w w).re := by
  set c := (mat x₁ τ)⁻¹ *ᵥ w with hc
  have hu : IsUnit (mat x₁ τ).det := isUnit_iff_ne_zero.2 (h₁ τ).1
  have hcw : mat x₁ τ *ᵥ c = w := by rw [hc, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hc0 : ∀ a : Fin r, ¬ (a : ℕ) < X.p0 → c a = 0 := fun a ha => by
    rw [hc, ← aLin_mulVec_of_not_lt X x₁ x₂ τ w ha, h a ha]
  have hsum : w = ∑ a : Fin X.p0, c (Fin.castLE X.p0_le a) • X.colP x₁ τ a := by
    rw [← hcw, Data.mulVec_eq_sum_col]
    symm
    refine Finset.sum_of_injOn (Fin.castLE X.p0_le) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun i _ hi => ?_) (fun _ _ => rfl)
    rw [hc0 i, zero_smul]
    intro hlt
    exact hi ⟨⟨i, hlt⟩, by simp, rfl⟩
  have hne : (fun a : Fin X.p0 => c (Fin.castLE X.p0_le a)) ≠ 0 := by
    intro h0
    apply hw
    rw [hsum]
    exact Finset.sum_eq_zero fun a _ => by rw [congrFun h0 a, Pi.zero_apply, zero_smul]
  have := quad_re_pos (X.gramPos_posDef h₁ τ) hne
  rw [hsum, hermC_quad]
  exact this

theorem neg_of_lower (x₁ : Frame X.Ψ r) {x₂ : Frame X.Ψ r} (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {w : Fin r → ℂ} (hw : w ≠ 0)
    (h : ∀ a : Fin r, (a : ℕ) < X.p0 → (aLin X x₁ x₂ τ *ᵥ w) a = 0) :
    (hermC τ.1 X.Gm w w).re < 0 :=
  X.neg_of_perp h₂ τ hw fun b => by
    have hb : ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 := b.2
    rw [Data.colP, ← aLin_mulVec_of_lt X x₁ x₂ τ w hb, h _ hb]

theorem det_aLin_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aLin X x₁ x₂ τ).det ≠ 0 := by
  intro h
  obtain ⟨w, hw, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have a := pos_of_upper h₁ x₂ τ hw fun a _ => congrFun h0 a
  have b := neg_of_lower x₁ h₂ τ hw fun a _ => congrFun h0 a
  linarith


variable (X) in
theorem aLin_swap (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) :
    aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  ext a c
  simp only [aLin, aAnti, map_apply, of_apply]
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, ← emb_cc, X.Gm_herm]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [Complex.conj_conj]

theorem det_aAnti_ne_zero {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ) :
    (aAnti X x₁ x₂ τ).det ≠ 0 := by
  intro h
  apply det_aLin_ne_zero h₂ h₁ τ
  rw [aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

theorem re_hermC_invol_neg {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) (τ : X.Ψ)
    {d : Fin r → ℂ} (hd : d ≠ 0) :
    (hermC τ.1 X.Gm (((aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ) *ᵥ d) d).re
      < 0 := by
  set A := aLin X x₁ x₂ τ with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_aLin_ne_zero h₁ h₂ τ)
  set y := A *ᵥ d with hy
  set yp : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then y a else 0 with hyp
  set ym : Fin r → ℂ := fun a => if (a : ℕ) < X.p0 then 0 else y a with hym
  set d₁ := A⁻¹ *ᵥ yp with hd₁
  set d₂ := A⁻¹ *ᵥ ym with hd₂
  have e₁ : A *ᵥ d₁ = yp := by rw [hd₁, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e₂ : A *ᵥ d₂ = ym := by rw [hd₂, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hsum : d = d₁ + d₂ := by
    have : yp + ym = y := by
      funext a; simp only [hyp, hym, Pi.add_apply]; split_ifs <;> simp
    rw [hd₁, hd₂, ← mulVec_add, this, hy, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  have hS : (A⁻¹ * Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * A) *ᵥ d
      = d₂ - d₁ := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hd₁, hd₂, ← mulVec_sub, ← hy]
    congr 1
    funext a
    simp [Matrix.mulVec_diagonal, hyp, hym, sgn]
    split_ifs <;> simp
  have p₁ : d₁ ≠ 0 → 0 < (hermC τ.1 X.Gm d₁ d₁).re := fun h =>
    pos_of_upper h₁ x₂ τ h fun a ha => by rw [← hA, e₁]; simp only [hyp, if_neg ha]
  have p₂ : d₂ ≠ 0 → (hermC τ.1 X.Gm d₂ d₂).re < 0 := fun h =>
    neg_of_lower x₁ h₂ τ h fun a ha => by rw [← hA, e₂]; simp only [hym, if_pos ha]
  have hc : (hermC τ.1 X.Gm d₁ d₂).re = (hermC τ.1 X.Gm d₂ d₁).re := by
    rw [← hermC_conj τ.1 X.Gm_herm d₁ d₂, Complex.conj_re]
  have key : (hermC τ.1 X.Gm (d₂ - d₁) (d₁ + d₂)).re =
      (hermC τ.1 X.Gm d₂ d₂).re - (hermC τ.1 X.Gm d₁ d₁).re := by
    rw [hermC_sub_left, hermC_add_right, hermC_add_right]
    simp only [Complex.sub_re, Complex.add_re, hc]
    ring
  rw [hS]
  rw [← hsum] at key
  rw [key]
  by_cases z₁ : d₁ = 0
  · have z₂ : d₂ ≠ 0 := fun z₂ => hd (by rw [hsum, z₁, z₂, add_zero])
    have := p₂ z₂
    rw [z₁, hermC_zero_left, Complex.zero_re]
    linarith
  · have := p₁ z₁
    by_cases z₂ : d₂ = 0
    · rw [z₂, hermC_zero_left, Complex.zero_re]
      linarith
    · have := p₂ z₂
      linarith

theorem posDef_imH {N : ℕ} {Z : Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ v : Fin N → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ Z *ᵥ v).im) : (imH Z).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · unfold imH
    rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose,
      ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp
  · have e : star v ⬝ᵥ Zᴴ *ᵥ v = conj (star v ⬝ᵥ Z *ᵥ v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Complex.star_def, map_sum,
        map_mul, Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have : star v ⬝ᵥ imH Z *ᵥ v = ((star v ⬝ᵥ Z *ᵥ v).im : ℂ) := by
      unfold imH
      rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, e, Complex.sub_conj,
        smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact_mod_cast h v hv


variable (X) in
theorem re_kappa (τ : E →+* ℂ) : (τ X.κ0).re = 0 := by
  have h : conj (τ X.ξ0) = -τ X.ξ0 := by rw [← emb_cc, X.ξ0_im, map_neg]
  have h' := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at h'
  have h0 : (τ X.ξ0).re = 0 := by linarith
  rcases X.κ0_xi with e | e <;> simp [e, h0, map_ofNat]

theorem dblZ_mem {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom) :
    dblZ X x₁ x₂ ∈ Hn X.Ψ r := by
  intro τ
  refine posDef_imH fun v hv => ?_
  have hd : star v ≠ 0 := by simpa using hv
  have h := re_hermC_invol_neg h₁ h₂ τ hd
  set S := (aLin X x₁ x₂ τ)⁻¹ *
      Matrix.diagonal (fun a : Fin r => (-(sgn X.p0 a : ℝ) : ℂ)) * aLin X x₁ x₂ τ with hS
  have e : star v ⬝ᵥ dblZ X x₁ x₂ τ *ᵥ v =
      τ.1 X.κ0 / 4 * hermC τ.1 X.Gm (S *ᵥ star v) (star v) := by
    unfold dblZ
    rw [← hS, smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose]
    congr 1
    simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [e, Complex.mul_im]
  have k₁ : (τ.1 X.κ0 / 4).re = 0 := by simp [re_kappa X τ.1]
  have k₂ : (τ.1 X.κ0 / 4).im < 0 := by
    have := X.κ0_sign τ
    simp only [Complex.div_ofNat_im]
    linarith
  rw [k₁, zero_mul, zero_add]
  exact mul_pos_of_neg_of_neg k₂ h

end GlobalTheory.SW.DblPoint

namespace GlobalTheory.SW

theorem dblZ_mem_Hn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj :=
  fun _ _ _ _ _ X x₁ h₁ x₂ h₂ => ⟨X.cmType, DblPoint.dblZ_mem h₁ h₂, fun τ =>
    ⟨DblPoint.det_aLin_ne_zero h₁ h₂ τ, DblPoint.det_aAnti_ne_zero h₁ h₂ τ,
      DblPoint.aLin_swap X x₁ x₂ τ⟩⟩

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetDoubledCoordinatesToRationalCoords
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblDet

noncomputable section

def shuffle {T : Type} {r g : ℕ} (p0 : ℕ) (idx : Fin g ≃ T × Fin r) :
    (Fin g ⊕ Fin g → ℂ) ≃ₗ[ℂ] (T → Fin r → ℂ) × (T → Fin r → ℂ) where
  toFun v := (fun τ a => if (a : ℕ) < p0 then v (Sum.inl (idx.symm (τ, a))) else
      v (Sum.inr (idx.symm (τ, a))),
    fun τ a => if (a : ℕ) < p0 then v (Sum.inr (idx.symm (τ, a))) else
      v (Sum.inl (idx.symm (τ, a))))
  invFun u := Sum.elim
    (fun i => if ((idx i).2 : ℕ) < p0 then u.1 (idx i).1 (idx i).2 else u.2 (idx i).1 (idx i).2)
    (fun i => if ((idx i).2 : ℕ) < p0 then u.2 (idx i).1 (idx i).2 else u.1 (idx i).1 (idx i).2)
  map_add' v w := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]
  map_smul' c v := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]
  left_inv v := by
    funext i
    rcases i with i | i <;> by_cases h : ((idx i).2 : ℕ) < p0 <;> simp [h]
  right_inv u := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]

def blocks {T : Type} {r : ℕ} (A A' : T → Matrix (Fin r) (Fin r) ℂ) :
    ((T → Fin r → ℂ) × (T → Fin r → ℂ)) →ₗ[ℂ] ((T → Fin r → ℂ) × (T → Fin r → ℂ)) :=
  LinearMap.prodMap
    (LinearMap.pi fun τ => (Matrix.toLin' (A τ)).comp (LinearMap.proj τ))
    (LinearMap.pi fun τ => (Matrix.toLin' (A' τ)).comp (LinearMap.proj τ))

def coordMap {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    ((X.Ψ → Fin r → ℂ) × (X.Ψ → Fin r → ℂ)) →ₗ[ℂ] (QI E r → ℂ) where
  toFun u p := ∑ τ : X.Ψ,
    (τ.1 (Module.finBasis ℚ E p.2) * ((-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ u.1 τ)) p.1 +
      ((τ.1 X.κ0 / 2) • (u.2 τ ᵥ* X.Gm.map τ.1)) p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))
  map_add' u v := by
    funext p
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, Matrix.add_vecMul,
      ← Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun τ _ => by ring
  map_smul' c u := by
    funext p
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul,
      Matrix.smul_vecMul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring

end

end GlobalTheory.SW.DblDet

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
theorem _root_.GlobalTheory.SW.det_dbl_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : ℕ) (idx : Fin g ≃ X.Ψ × Fin r) (e : (Fin g ⊕ Fin g) ≃ _root_.GlobalTheory.SW.QI E r), ∃ c : ℂ, ∀ x₁ x₂ : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ∃ L : Matrix (_root_.GlobalTheory.SW.QI E r) (Fin g ⊕ Fin g) ℂ, (L.submatrix e id).det = c * ∏ τ : X.Ψ, ((_root_.GlobalTheory.SW.aLin X x₁ x₂ τ).det * (_root_.GlobalTheory.SW.aAnti X x₁ x₂ τ).det)⁻¹ ∧ ∀ (n : ℕ) (z₁ w : Fin n → Fin g → ℂ) (k : Fin n), _root_.GlobalTheory.SW.zetaOf X.Ψ (_root_.GlobalTheory.SW.dblz X idx x₁ x₂ z₁ w) (_root_.GlobalTheory.SW.dblz' X idx x₁ x₂ z₁ w) k = L *ᵥ Sum.elim (z₁ k) (w k) := by
  intro E _ _ _ r X g idx e
  set S := _root_.GlobalTheory.SW.DblDet.shuffle X.p0 idx
  refine ⟨LinearMap.det (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ
    (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)), fun x₁ x₂ => ?_⟩
  set B := _root_.GlobalTheory.SW.DblDet.blocks (fun τ => (_root_.GlobalTheory.SW.aAnti X x₁ x₂ τ)⁻¹)
    (fun τ => (_root_.GlobalTheory.SW.aLin X x₁ x₂ τ)⁻¹)
  refine ⟨LinearMap.toMatrix' (_root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
    (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)), ?_, ?_⟩
  · have hsub : (LinearMap.toMatrix' (_root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
        (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _))).submatrix e id =
        LinearMap.toMatrix' (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
          (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) := by
      ext i j
      simp [LinearMap.toMatrix'_apply, LinearMap.funLeft_apply]
    have hsplit : LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
        (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _) =
        (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ
          (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) ∘ₗ
        ((S.symm : _ →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ)) ∘ₗ B ∘ₗ
          (S.symm.symm : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) := by
      refine LinearMap.ext fun v => ?_
      simp
    rw [hsub, LinearMap.det_toMatrix', hsplit, LinearMap.det_comp, LinearMap.det_conj]
    congr 1
    simp only [B, _root_.GlobalTheory.SW.DblDet.blocks, LinearMap.det_prodMap, LinearMap.det_pi,
      LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_inv, mul_comm]
  · intro n z₁ w k
    rw [LinearMap.toMatrix'_mulVec]
    funext p
    simp [_root_.GlobalTheory.SW.zetaOf, _root_.GlobalTheory.SW.dblz,
      _root_.GlobalTheory.SW.dblz', _root_.GlobalTheory.SW.DblDet.coordMap, B, _root_.GlobalTheory.SW.DblDet.blocks, S,
      _root_.GlobalTheory.SW.DblDet.shuffle]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFamilyInvariantOfFockInner
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem sum_mul_conj_orthonormalBasis {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Fintype ι] (b b' : OrthonormalBasis ι ℂ V) (l l' : V →ₗ[ℂ] ℂ) :
    ∑ j, l (b j) * conj (l' (b j)) = ∑ j, l (b' j) * conj (l' (b' j)) := by
  have := FiniteDimensional.complete ℂ V
  have h (l : V →ₗ[ℂ] ℂ) : ∃ a : V, ∀ v, l v = inner ℂ a v :=
    ⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap l), fun v => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨a, ha⟩ := h l
  obtain ⟨a', ha'⟩ := h l'
  simp only [ha, ha', inner_conj_symm, OrthonormalBasis.sum_inner_mul_inner]

theorem exists_family_invariant_of_fockInner {σ : Type} (W : Submodule ℂ (MvPolynomial σ ℂ))
    [FiniteDimensional ℂ W] (hW : W ≠ ⊥) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial σ ℂ), (∀ j, P j ∈ W) ∧ (∃ j, P j ≠ 0) ∧
      ∀ f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ, (∀ Q ∈ W, f Q ∈ W) →
        (∀ Q Q', MvPoly.fockInner (f Q) (f Q') = MvPoly.fockInner Q Q') →
        ∀ l l' : MvPolynomial σ ℂ →ₗ[ℂ] ℂ,
          ∑ j, l (f (P j)) * conj (l' (f (P j))) = ∑ j, l (P j) * conj (l' (P j)) := by
  let cr : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => MvPoly.fockInner (y : MvPolynomial σ ℂ) x
      conj_inner_symm := fun x y => MvPoly.fockInner_conj_symm _ _
      re_inner_nonneg := fun x => by
        rw [MvPoly.fockInner_self, RCLike.ofReal_re]; exact MvPoly.fockNormSq_nonneg _
      add_left := fun x y z => MvPoly.fockInner_add_right _ _ _
      smul_left := fun x y r => MvPoly.fockInner_smul_right _ _ _
      definite := fun x hx => by
        rw [MvPoly.fockInner_self] at hx
        exact Subtype.ext (MvPoly.fockNormSq_eq_zero.mp (RCLike.ofReal_eq_zero.mp hx)) }
  letI : NormedAddCommGroup W := cr.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore cr.toCore
  let b := stdOrthonormalBasis ℂ W
  have hpos : 0 < Module.finrank ℂ W := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]; exact hW
  refine ⟨_, fun j => b j, fun j => (b j).2, ⟨⟨0, hpos⟩, fun e => ?_⟩, fun f hf hi l l' => ?_⟩
  · exact b.orthonormal.ne_zero _ (Subtype.ext e)
  · let U : W →ₗᵢ[ℂ] W := (f.restrict hf).isometryOfInner fun x y => hi _ _
    exact sum_mul_conj_orthonormalBasis (b.map (U.toLinearIsometryEquiv rfl)) b
      (l ∘ₗ W.subtype) (l' ∘ₗ W.subtype)

theorem exists_invFam_rowHighest : ∀ (T : Type) [Fintype T] [DecidableEq T] (p q n : ℕ)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ), p + q ≤ n →
    ∃ (m : ℕ) (P : Fin m → Harm.Poly ℂ T p q (Fin n)), (∀ j, P j ∈ Harm.rowHighest ℂ c c') ∧
      (∃ j, P j ≠ 0) ∧ InvFam P := by
  intro T _ _ p q n c c' h
  obtain ⟨m, P, h₁, h₂, h₃⟩ := exists_family_invariant_of_fockInner
    (Harm.rowHighest (κ := Fin n) ℂ c c') (Harm.rowHighest_ne_bot h c c')
  refine ⟨m, P, h₁, h₂, fun u hu z w => ?_⟩
  have hs : star u * u = 1 := funext fun t => Units.ext (Matrix.mem_unitaryGroup_iff'.mp (hu t))
  refine h₃ (Harm.colActHom u).toLinearMap (fun Q hQ => Harm.colAct_mem_rowHighest u hQ)
    (fun Q Q' => ?_) (MvPolynomial.aeval z).toLinearMap (MvPolynomial.aeval w).toLinearMap
  change MvPoly.fockInner (Harm.colAct ℂ T p q (Fin n) u Q) (Harm.colAct ℂ T p q (Fin n) u Q') = _
  rw [Harm.fockInner_colAct, ← AlgEquiv.mul_apply, ← map_mul, hs, map_one, AlgEquiv.one_apply]

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Imports
section
namespace GlobalTheory.CommonDenominatorExistence

theorem exists_common_denominator {E : Type} [Field E] [NumberField E] {r : ℕ}
    {L : GlobalTheory.SW.Lt E r} (hL : Submodule.FG L) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ v ∈ L, ∀ (a : Fin r), ∃ (c : NumberField.RingOfIntegers E),
        (↑c : E) = (↑d : E) * v a := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin r → E) × Fin r =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let d : NumberField.RingOfIntegers E := ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin r)), ((z p).2 : _)
  refine ⟨d, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, a) ∈ s ×ˢ (Finset.univ : Finset (Fin r)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩)
    refine ⟨e * (z (g, a)).1, ?_⟩
    have h := hz (g, a)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show d = ((z (g, a)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    obtain ⟨c2, h2⟩ := hy a
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro a
    obtain ⟨c1, h1⟩ := hx a
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableOnMinorFin
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.MinorInt

theorem integrableOn_minor_fin : ∀ (p q n : ℕ), 2 * (p + q) ≤ n → ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn (fun y : (Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ) * (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)) a b‖ < δ₀} volume := by
  intro p q n hn
  convert integrableOn_minor (Fin p) (Fin q) n (by simpa using hn)

end GlobalTheory.MinorInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LactMulFrame
section
namespace GlobalTheory.LeftActionFrameMul

open ReciprocityTheory.ChartRestriction.G.FD

theorem lact_mul_frame {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (γ' γ : GL (Fin r) E) (x : Frame Ψ r) : lact (γ' * γ) x = lact γ' (lact γ x) := by
  funext τ

  show ((γ' * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

end GlobalTheory.LeftActionFrameMul
end

