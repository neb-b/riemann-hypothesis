module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegerSmallAtPlaces
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFamilyBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicSplit
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PKTransitive
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Matrix
open scoped ComplexOrder

noncomputable section

theorem KTransitive.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : IsotropicSplit.Statement ι) (h₂ : EigenReflectionMaps.Statement ι)
    (h₃ : PhaseOnMinus.Statement ι) (_h₄ : EigenspacesOrthogonal.Statement ι) :
    KTransitive.Statement ι := by
  intro H P hmaj z z' hz hz' hzH hz'H
  obtain ⟨ha, hb, hab⟩ := h₁ H P hmaj z hzH
  obtain ⟨ha', hb', hab'⟩ := h₁ H P hmaj z' hz'H
  have hsplit : ∀ w : ι → ℂ, plusPart H P w + minusPart H P w = w := by
    intro w; ext i; simp only [plusPart, minusPart, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]; ring
  have hPpos := hmaj.1
  have hne : ∀ w : ι → ℂ, w ≠ 0 →
      star (plusPart H P w) ⬝ᵥ (P *ᵥ plusPart H P w) =
        star (minusPart H P w) ⬝ᵥ (P *ᵥ minusPart H P w) → plusPart H P w ≠ 0 := by
    intro w hw heq h0
    apply hw
    rw [h0] at heq
    simp only [star_zero, zero_dotProduct] at heq
    have hm : minusPart H P w = 0 := by
      by_contra hm
      exact (hPpos.dotProduct_mulVec_pos hm).ne heq
    rw [← hsplit w, h0, hm, add_zero]
  set a := plusPart H P z with ha_def
  set b := minusPart H P z with hb_def
  set a' := plusPart H P z' with ha'_def
  set b' := minusPart H P z' with hb'_def
  have ha0 : a ≠ 0 := hne z hz hab
  have ha'0 : a' ≠ 0 := hne z' hz' hab'
  have hp := hPpos.dotProduct_mulVec_pos ha0
  have hq := hPpos.dotProduct_mulVec_pos ha'0
  set p := star a ⬝ᵥ (P *ᵥ a) with hp_def
  set q := star a' ⬝ᵥ (P *ᵥ a') with hq_def
  obtain ⟨hpr, hpi⟩ := Complex.lt_def.mp hp
  obtain ⟨hqr, hqi⟩ := Complex.lt_def.mp hq
  simp only [Complex.zero_re, Complex.zero_im] at hpr hpi hqr hqi
  set t : ℝ := Real.sqrt (p.re / q.re) with ht_def
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hpr hqr)
  have htt : t * t = p.re / q.re := Real.mul_self_sqrt (div_nonneg hpr.le hqr.le)
  have ht2 : (t : ℂ) * t * q = p := by
    have key : t * t * q.re = p.re := by rw [htt, div_mul_cancel₀ _ hqr.ne']
    apply Complex.ext
    · simp [Complex.mul_re, ← hqi, key]
    · simp [Complex.mul_im, ← hqi, ← hpi]
  have hscale : ∀ v : ι → ℂ, star ((t : ℂ) • v) ⬝ᵥ (P *ᵥ ((t : ℂ) • v)) =
      (t : ℂ) * t * (star v ⬝ᵥ (P *ᵥ v)) := by
    intro v
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  have hA1 : majInvolution H P *ᵥ ((t : ℂ) • a') = (1 : ℂ) • ((t : ℂ) • a') := by
    rw [mulVec_smul, ha', one_smul]
  have hAm : majInvolution H P *ᵥ ((t : ℂ) • b') = (-1 : ℂ) • ((t : ℂ) • b') := by
    rw [mulVec_smul, hb', neg_one_smul, smul_neg]
  obtain ⟨α, hα, Rp, hRpP, hRpH, hRpa, hRpfix⟩ := h₂ H P hmaj 1 (Or.inl rfl) a ((t : ℂ) • a')
    (by rw [ha, one_smul]) hA1 (by rw [hscale, ht2])
  obtain ⟨β, hβ, Rm, hRmP, hRmH, hRmb, hRmfix⟩ := h₂ H P hmaj (-1) (Or.inr rfl) b ((t : ℂ) • b')
    (by rw [hb, neg_one_smul]) hAm (by rw [hscale, ← hab', ht2, hab])
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact zero_ne_one hβ
  have hc : ‖α / β‖ = 1 := by rw [norm_div, hα, hβ, div_one]
  obtain ⟨hDP, hDH, hDplus, hDminus⟩ := h₃ H P hmaj (α / β) hc
  set D := phaseOnMinus H P (α / β) with hD_def
  set M := D * Rm * Rp with hM_def
  have hunit : ∀ X : Matrix ι ι ℂ, Dᴴ * X * D = X → Rmᴴ * X * Rm = X → Rpᴴ * X * Rp = X →
      Mᴴ * X * M = X := by
    intro X h1 h2 h3
    have e : Mᴴ * X * M = Rpᴴ * (Rmᴴ * (Dᴴ * X * D) * Rm) * Rp := by
      simp only [hM_def, conjTranspose_mul, Matrix.mul_assoc]
    rw [e, h1, h2, h3]
  have hMH : Mᴴ * H * M = H := hunit H hDH hRmH hRpH
  have hMP : Mᴴ * P * M = P := hunit P hDP hRmP hRpP
  have hct : ∀ X : Matrix ι ι ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i j; simp [conjTranspose_apply]
  have hRma : Rm *ᵥ a = a := hRmfix a (by rw [ha, neg_neg, one_smul])
  have hMz : M *ᵥ ((t : ℂ) • z') = α • z := by
    have hz'2 : (t : ℂ) • z' = (t : ℂ) • a' + (t : ℂ) • b' := by rw [← smul_add, hsplit z']
    rw [hz'2, hM_def, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_add, hRpa, hRpfix _ hAm,
      mulVec_add, mulVec_smul, hRma, hRmb, mulVec_add, mulVec_smul, mulVec_smul, hDplus a ha,
      hDminus b hb, smul_smul, mul_div_cancel₀ _ hβ0, ← smul_add, hsplit z]
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hdet : IsUnit M.det := isUnit_det_of_unitary (starRingEnd ℂ) hmaj.2.2.1 (by rw [hct]; exact hMH)
  refine ⟨nonsingInvUnit M hdet, ?_, ?_, (t : ℂ)⁻¹ * α, ?_⟩
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * H * M = H
    rw [hct]; exact hMH
  · rw [mem_unitaryGroupMatrix]
    show (M.map (starRingEnd ℂ))ᵀ * P * M = P
    rw [hct]; exact hMP
  · show M *ᵥ z' = ((t : ℂ)⁻¹ * α) • z
    rw [mulVec_smul] at hMz
    rw [mul_smul, ← hMz, smul_smul, inv_mul_cancel₀ htc, one_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticeOrbitsFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem isIsotropicLine_span_singleton (h : HermitianForm F E W) {x : W} (hx : x ≠ 0)
    (hxx : h.toSesq x x = 0) : IsIsotropicLine h (Submodule.span E {x}) := by
  refine ⟨finrank_span_singleton hx, ?_⟩
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hb
  simp only [map_smul, LinearMap.map_smulₛₗ₂, hxx, smul_zero]

theorem LatticeOrbitsFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by
  intro D
  obtain ⟨M⟩ := h₂
  obtain ⟨S₁, hS₁, K, -, hK⟩ := h₁ M D 1 one_pos
  obtain ⟨S₂, hS₂, hP⟩ := h₄ D
  refine ⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩
  intro La hLa
  by_cases hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1
  · obtain ⟨x, hxL, hx0, hxlt⟩ := hshort
    have hxx : h.toSesq x x = 0 := h₃ M D La 1 x hLa hxL hxlt
    obtain ⟨p, hp, g, hg, -⟩ := hP La (Submodule.span E {x}) hLa
      (isIsotropicLine_span_singleton h hx0 hxx)
    exact ⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩
  · push Not at hshort
    obtain ⟨γ, hγ, -⟩ := hK La 1 hLa hshort
    exact ⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenSq
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem LenSq.re_nonneg {P : Matrix ι ι ℂ} (hP : P.PosDef) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re :=
  (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LenSq.proof (h : HermitianForm F E W) (v : Basis ι E W) : LenSq.Statement h v := by
  intro M y
  have hw : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
    LenSq.re_nonneg (M.posDef w) (y w)
  refine ⟨hw, ?_⟩
  unfold Majorant.len
  exact Real.sq_sqrt (Finset.sum_nonneg fun w _ => hw w)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineCoeffsFG
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

noncomputable section

variable {E : Type*} [Field E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineCoeffsFG.proof : LineCoeffsFG.Statement (E := E) W := by
  intro La x hLa hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hf : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have h : a • x = b • x := hab
    exact smul_left_injective E hx h
  have hS : La.toIntSubmodule.FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]
    simpa using hLa
  have hle : (lineCoeffs (E := E) La x).toIntSubmodule.map f.toIntLinearMap ≤
      La.toIntSubmodule := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hN : (lineCoeffs (E := E) La x).toIntSubmodule.FG :=
    Submodule.fg_of_fg_map_injective _ hf (hS.of_le hle)
  rw [Submodule.fg_iff_addSubgroup_fg] at hN
  simpa using hN

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexCoeffs
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

variable (E : Type*) [Field E] [NumberField E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexCoeffs.proof : LineIndexCoeffs.Statement (E := E) W := by
  intro La x hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hfa : ∀ a : E, f a = a • x := fun a => rfl
  have hf : Function.Injective f := by
    intro a b hab
    rw [hfa, hfa] at hab
    exact smul_left_injective E hx hab
  have h1 : (intSubgroup E).map f = ringMultiples E x := by
    rw [intSubgroup, ringMultiples, AddMonoidHom.range_comp]
  have hrange : f.range = (Submodule.span E {x}).toAddSubgroup := by
    ext y
    simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
      hfa]
  have h2 : (lineCoeffs La x).map f = La ⊓ (Submodule.span E {x}).toAddSubgroup := by
    rw [lineCoeffs, AddSubgroup.map_comap_eq, hrange, inf_comm]
  unfold lineIndex
  rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

theorem majorant_mul_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) : H * P⁻¹ * H = P := by
  obtain ⟨hP, -, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  calc H * P⁻¹ * H = (P * H⁻¹ * P) * P⁻¹ * H := by rw [hPHP]
    _ = P * H⁻¹ * (P * P⁻¹) * H := by simp only [Matrix.mul_assoc]
    _ = P := by
      rw [Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

theorem MajorantBound.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MajorantBound.Statement ι := by
  intro H P hM z
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set w := P⁻¹ *ᵥ (H *ᵥ z) with hw
  have h1 : P *ᵥ w = H *ᵥ z := by
    rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star w ⬝ᵥ (P *ᵥ w) = star z ⬝ᵥ (P *ᵥ z) := by
    rw [h1, hw, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) z w
  have e1 : (inner ℂ z w : ℂ) = star z ⬝ᵥ (H *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star z = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ w z : ℂ) = star (star z ⬝ᵥ (H *ᵥ z)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) w z).symm
  have e3 : (inner ℂ z z : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ z) ⬝ᵥ star z = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ w w : ℂ) = star z ⬝ᵥ (P *ᵥ z) := by
    change (P *ᵥ w) ⬝ᵥ star w = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  have hnn : 0 ≤ (star z ⬝ᵥ (P *ᵥ z)).re := hP.posSemidef.re_dotProduct_nonneg z
  have hn : 0 ≤ ‖star z ⬝ᵥ (H *ᵥ z)‖ := norm_nonneg _
  simp only [RCLike.re_to_complex] at cs
  nlinarith

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortVectorIsotropic
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ShortVectorIsotropic.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by
  intro M D La g x hLa hx hlen
  apply h₆ _ (hLa.integral x hx x hx)
  intro w
  set y := vecAt v x
  set z := invApply g y
  have hP : IsMajorantOf (gramAt h v w) (M.P w) :=
    ⟨M.posDef w, (h₂ w).1, (h₂ w).2, M.siegel w⟩
  obtain ⟨hnn, hsq⟩ := h₅ M z
  have hlen0 : 0 ≤ M.len z := Real.sqrt_nonneg _
  have hsq1 : M.len z ^ 2 < 1 := by nlinarith
  have hterm : (star (z w) ⬝ᵥ (M.P w *ᵥ z w)).re ≤ M.len z ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun w' => (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re)
      (fun w' _ => hnn w') (Finset.mem_univ w)
  have hform : w.embedding (h.toSesq x x) = star (z w) ⬝ᵥ (gramAt h v w *ᵥ z w) := by
    rw [h₁ w x x, h₃ g y y w]
  rw [← InfinitePlace.norm_embedding_eq, hform]
  exact lt_of_le_of_lt ((h₄ _ _ hP (z w)).trans hterm) hsq1

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

