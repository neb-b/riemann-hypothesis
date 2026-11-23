module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.DimAddCardFlagVar
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim


open NumberField in
theorem _root_.GlobalTheory.FlagDim.card_pairs_lt (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ (j : Fin n) × Fin j :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]


open NumberField in
theorem _root_.GlobalTheory.FlagDim.dim_add_card_flagVar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), Dw.dim + Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have hcard : Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 := by
    show Nat.card ((τ : E →+* ℂ) × {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}) = _
    rw [Nat.card_sigma]
    simp only [_root_.GlobalTheory.FlagDim.card_pairs_lt]
  have hdim : Dw.dim = Module.finrank ℚ E / 2 * Dw.p * Dw.q := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim; rfl
  have hall : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hcm : (Finset.univ.filter fun τ : E →+* ℂ => τ H.rt = H.rt0).card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, _root_.GlobalTheory.PeriodCoord.card_cmType]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ H.rt = H.rt0)
  obtain ⟨k, hk⟩ : Even (Module.finrank ℚ E) := by
    rw [IsTotallyComplex.finrank]; exact even_two_mul _
  rw [Finset.card_univ, hall] at hsplit
  have hk2 : Module.finrank ℚ E / 2 = k := by omega
  have hnot : (Finset.univ.filter fun τ : E →+* ℂ => ¬ τ H.rt = H.rt0).card = k := by omega
  have hterm : ∀ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 =
      if τ H.rt = H.rt0 then Dw.p * (Dw.p - 1) / 2 else Dw.q * (Dw.q - 1) / 2 := by
    intro τ; unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult; split_ifs <;> rfl
  rw [hcard, hdim, Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hcm, hnot, hk2]
  ring

end GlobalTheory.FlagDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameSign

private theorem hermC_emb_eq_map_herm' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (Gm : Matrix (Fin r) (Fin r) E) (v w : Fin r → E) :
    hermC τ Gm (Data.emb τ v) (Data.emb τ w) = τ (herm Gm v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, cc, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]

private theorem re_emb' {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) (ξ : E)
    (hξ : cc ξ = -ξ) : (τ ξ).re = 0 := by
  have h1 : τ (cc ξ) = τ (-ξ) := by rw [hξ]
  rw [cc, IsCMField.complexEmbedding_complexConj, map_neg] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.conj_re, Complex.neg_re] at h2
  linarith

private theorem im_hermForm_diagonal_eq_sum {g : ℕ} (c : Fin g → ℝ) (z w : Fin g → ℂ) :
    (hermForm (Matrix.diagonal fun k => ((c k : ℝ) : ℂ)) z w).im =
      ∑ k, c k * (z k * (starRingEnd ℂ) (w k)).im := by
  simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Complex.im_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.im_ofReal_mul]

theorem im_hermForm_signed {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (q : ℕ) (ξ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (idx : Fin g ≃ Ψ × Fin r)
    (hξ : cc ξ = -ξ) (x : Frame Ψ r)
    (hx : ∀ τ : Ψ, gram τ.1 Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ))
    (P : (Fin r → E) → Fin g → ℂ)
    (hP : ∀ v k, P v k = if ((idx k).2 : ℕ) < q then
      hermC (idx k).1.1 Gm (col (mat x (idx k).1) (idx k).2) (Data.emb (idx k).1.1 v)
      else ((mat x (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 v) (idx k).2) (v w : Fin r → E) :
    (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) (P v) (P w)).im =
      ((Algebra.trace ℚ E (ξ * herm Gm v w) : ℚ) : ℝ) := by
  classical
  rw [im_hermForm_diagonal_eq_sum (fun k => 2 * ((idx k).1.1 ξ).im), ← Equiv.sum_comp idx.symm, Fintype.sum_prod_type,
    GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hΨ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hsum := GlobalTheory.UnitFrame.im_sum_periods q τ.1 Gm (mat x τ) (hx τ) (Data.emb τ.1 v) (Data.emb τ.1 w)
  simp only [hP, Equiv.apply_symm_apply]
  rw [← Finset.mul_sum, ← Complex.im_sum, hsum, hermC_emb_eq_map_herm', map_mul, Complex.mul_re, re_emb' τ.1 ξ hξ]
  ring

theorem pos_of_pullback_pos {g : ℕ} (d : Fin g → ℝ) (h : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (hermForm (Matrix.diagonal fun k => ((d k : ℝ) : ℂ)) (h *ᵥ z) (h *ᵥ z)).re) (j : Fin g) :
    0 < d j := by
  have hinj : Function.Injective (Matrix.mulVecLin h) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    by_contra hne
    have hp := hpos z hne
    rw [Matrix.mulVecLin_apply] at hz
    rw [hz] at hp
    simp [hermForm] at hp
  obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (Pi.single j 1)
  rw [Matrix.mulVecLin_apply] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    have h1 := congrFun hz j
    simp at h1
  have hp := hpos z hz0
  rw [hz] at hp
  simpa [hermForm, Matrix.mulVec_diagonal, Pi.single_apply] using hp

theorem im_neg_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → ∀ x ∈ X.dom, ∀ P : D.La →+ (Fin g → ℂ), (∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) → IsPeriod D (fun j => relab c σ (e j).1) P → r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0 := by
  intro E _ _ _ H Dw l c σ g e D r X φ hgood hr hp0 hΨ hEF x hx P hP hper hr0 τ hτ
  classical

  have hrtE : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (fun z : 𝓞 E => (z : E)) H.5
  have hrt : ∀ τ' : E →+* ℂ, relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
    intro τ'
    have hs : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hrtE, H.12]
      simp
    have hv : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    have hz : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hgood
    have hz0 : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · have he : (⟨τ' (H.rt : E), c.conj τ' _⟩ : c.F) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hz0.symm)
      rw [hv, he, hz]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · have he : (⟨τ' (H.rt : E), c.conj τ' _⟩ : c.F) = -IntermediateField.inclusion c.le (baseKA l).ρ := by
        apply Subtype.ext
        show τ' (H.rt : E) = ((-IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
        rw [h, IntermediateField.coe_neg, hz0]
      rw [hv, he, map_neg, hz, h]
  have hρinj : Function.Injective (relab c σ) := by
    intro τ1 τ2 h12
    ext a
    have h : σ ⟨τ1 a, c.conj τ1 a⟩ = σ ⟨τ2 a, c.conj τ2 a⟩ := congrArg (fun ρ' : E →+* ℂ => ρ' a) h12
    exact congrArg Subtype.val (σ.injective h)
  have hρ : Function.Bijective (relab c σ) := Finite.injective_iff_bijective.mp hρinj
  have hmult : ∀ τ' : E →+* ℂ, Dw.mult τ' = if τ' (H.rt : E) = H.rt0 then Dw.p else Dw.q := fun _ => rfl
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hρ Dw.mult
    (fun τ' h => by rw [hmult, if_pos ((hrt τ').1 ((hΨ _).1 h))])
    (fun τ' h => by rw [hmult, if_neg (fun h' => h ((hΨ _).2 ((hrt τ').2 h')))])
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ k,
      (relab c σ (e k).1 ∈ X.Ψ ∧ (idx k).1.1 = relab c σ (e k).1 ∧ ((idx k).2 : ℕ) = Dw.q + (e k).2) ∨
      (relab c σ (e k).1 ∉ X.Ψ ∧ (idx k).1.1 = ComplexEmbedding.conjugate (relab c σ (e k).1) ∧
        ((idx k).2 : ℕ) = Dw.q - 1 - (e k).2 ∧ ((e k).2 : ℕ) < Dw.q) :=
    ⟨e.trans f, fun k => hf (e k)⟩

  have hPa : ∀ a k, P a k = if ((idx k).2 : ℕ) < Dw.q then
      hermC (idx k).1.1 X.Gm (col (mat x (idx k).1) (idx k).2) (Data.emb (idx k).1.1 (φ a : Fin r → E))
      else ((mat x (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 (φ a : Fin r → E)) (idx k).2 := by
    intro a k
    rw [hP a k]
    unfold perFr
    rcases hidx k with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · have hi : X.p0 + ((e k).2 : ℕ) < r := by rw [hp0, ← h3]; exact (idx k).2.isLt
      have hk1 : (idx k).1 = ⟨relab c σ (e k).1, h1⟩ := Subtype.ext h2
      have hk2 : (idx k).2 = ⟨X.p0 + (e k).2, hi⟩ :=
        Fin.ext (show ((idx k).2 : ℕ) = X.p0 + (e k).2 by rw [hp0]; exact h3)
      have hnot : ¬ (((idx k).2 : ℕ) < Dw.q) := by rw [h3]; omega
      rw [dite_eq_left h1, dite_eq_left hi, if_neg hnot, hk1, hk2]
    · have hc : conjEmb (relab c σ (e k).1) ∈ X.Ψ := by
        have h5 := (idx k).1.2
        rw [h2] at h5
        exact h5
      have hj : X.p0 - 1 - ((e k).2 : ℕ) < r := by rw [hp0, ← h3]; exact (idx k).2.isLt
      have hk1 : (idx k).1 = ⟨conjEmb (relab c σ (e k).1), hc⟩ := Subtype.ext h2
      have hk2 : (idx k).2 = ⟨X.p0 - 1 - (e k).2, hj⟩ :=
        Fin.ext (show ((idx k).2 : ℕ) = X.p0 - 1 - (e k).2 by rw [hp0]; exact h3)
      have hlt : ((idx k).2 : ℕ) < Dw.q := by rw [h3]; omega
      rw [dite_eq_right h1, dite_eq_left hc, dite_eq_left hj, if_pos hlt, hk1, hk2]

  obtain ⟨x₀, b, hb, hon, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  rw [hp0] at hon
  have hξ' : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  let Q : (Fin r → E) → Fin g → ℂ := fun v k => if ((idx k).2 : ℕ) < Dw.q then
      hermC (idx k).1.1 X.Gm (col (mat (rmul x b) (idx k).1) (idx k).2) (Data.emb (idx k).1.1 v)
      else ((mat (rmul x b) (idx k).1)⁻¹ *ᵥ Data.emb (idx k).1.1 v) (idx k).2
  have hform : ∀ a a', (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ))
      (Q (φ a)) (Q (φ a'))).im = ((D.EF a a' : ℤ) : ℝ) := by
    intro a a'
    rw [im_hermForm_signed Dw.q (-X.ξ0) X.Gm X.Ψ X.cmType idx hξ' (rmul x b) hon Q (fun v k => rfl),
      ← hEF a a', Rat.cast_intCast]
  have hmove : ∀ a, Q (φ a) = GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ P a := fun a =>
    GlobalTheory.PerBor.moveMat_mulVec Dw.q idx hb X.Gm x (φ a : Fin r → E) (P a) (Q (φ a)) (hPa a) (fun k => rfl)
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper

  have hHm : Hm = (GlobalTheory.PerBor.moveMat Dw.q idx b)ᵀ *
      ((Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ)) *
        (GlobalTheory.PerBor.moveMat Dw.q idx b).map (starRingEnd ℂ)) := by
    apply GlobalTheory.UnitDet.eq_of_im_hermForm_eq (Set.range P) hspan
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hIm, ← GlobalTheory.UnitDet.hermForm_mulVec, ← hmove, ← hmove, hform]
  have hpos' : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 (-X.ξ0)).im : ℝ) : ℂ))
        (GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ z) (GlobalTheory.PerBor.moveMat Dw.q idx b *ᵥ z)).re := by
    intro z hz
    rw [GlobalTheory.UnitDet.hermForm_mulVec, ← hHm]
    exact hpos z hz
  have hr0' : 0 < r := Nat.pos_of_ne_zero hr0
  have h1 : (idx (idx.symm (⟨τ, hτ⟩, ⟨0, hr0'⟩))).1.1 = τ := by rw [Equiv.apply_symm_apply]
  have key : 0 < 2 * ((idx (idx.symm (⟨τ, hτ⟩, ⟨0, hr0'⟩))).1.1 (-X.ξ0)).im :=
    pos_of_pullback_pos (fun k => 2 * ((idx k).1.1 (-X.ξ0)).im) (GlobalTheory.PerBor.moveMat Dw.q idx b) hpos' _
  rw [h1, map_neg, Complex.neg_im] at key
  linarith

end GlobalTheory.FrameSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IntegralityTrivialValuationsOfNormalAffineCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.ChartInt

open IsLocalRing Formalism.L2.PjFree

section Values
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem vV_nonneg (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by
  have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
    intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w
  have h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0 := valV_ne_zero hw'
  have h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_le_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vV
  omega

theorem vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V) (algebraMap V _ u) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing V)
      (IsDiscreteValuationRing.maximalIdeal V)).2 hu
  unfold vV valV
  rw [h1, WithZero.log_one, neg_zero]

theorem mem_of_vV_nonneg (y : FractionRing V) (hy : y ≠ 0) (h : 0 ≤ vV V y) :
    ∃ w : V, algebraMap V (FractionRing V) w = y := by
  have h0 : valV V y ≠ 0 := valV_ne_zero hy
  have hle : valV V y ≤ 1 := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]
    unfold vV at h
    omega
  obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V)
    (K := FractionRing V) y (fun v => by
      have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
        have hm : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
        ext1
        exact IsLocalRing.eq_maximalIdeal hm
      rw [hv]
      exact hle)
  exact ⟨w, hw⟩

theorem nval_nonneg (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by
  by_cases hw : w = 0
  · rw [hw, map_zero, nval_zero]
    exact le_top
  · have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
      intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
    rw [nval_of_ne hw']
    exact EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))

theorem nval_unit (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (maximalIdeal V).zero_mem)
  have hu' : algebraMap V (FractionRing V) u ≠ 0 := by
    intro h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  rw [nval_of_ne hu', vV_unit u hu]
  simp

theorem ne_zero_map {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  intro h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])

variable {A : Type} [CommRing A] [IsDomain A]

theorem chval_eq (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a b : A)
    (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a) (hb : φ b ≠ 0) :
    r = nval V e (algebraMap V (FractionRing V) (φ a)) - nval V e (algebraMap V (FractionRing V) (φ b)) := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have has : a * s = x * b := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul, ← hab, ← hfs]
    ring
  have hφ : φ a * φ s = φ x * φ b := by rw [← map_mul, ← map_mul, has]
  by_cases ha : φ a = 0
  · have hx : φ x = 0 := by
      rw [ha, zero_mul] at hφ
      exact (mul_eq_zero.1 hφ.symm).resolve_right hb
    rw [ha, hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), nval_of_ne (ne_zero_map hb),
      EReal.top_sub_coe, EReal.top_sub_coe]
  · have hx : φ x ≠ 0 := by
      intro hx
      rw [hx, zero_mul] at hφ
      exact mul_ne_zero ha hs hφ
    have hv := congrArg (vV V) (congrArg (algebraMap V (FractionRing V)) hφ)
    rw [map_mul, map_mul, vV_mul (ne_zero_map ha) (ne_zero_map hs),
      vV_mul (ne_zero_map hx) (ne_zero_map hb)] at hv
    rw [nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb), nval_of_ne (ne_zero_map hx),
      nval_of_ne (ne_zero_map hs), ← EReal.coe_sub, ← EReal.coe_sub, div_sub_div_same, div_sub_div_same]
    congr 2
    have : ((vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) : ℝ) -
        (vV V (algebraMap V (FractionRing V) (φ s)) : ℤ) =
        ((vV V (algebraMap V (FractionRing V) (φ a)) : ℤ) : ℝ) - (vV V (algebraMap V (FractionRing V) (φ b)) : ℤ) := by
      have : (vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) - vV V (algebraMap V (FractionRing V) (φ s)) =
          vV V (algebraMap V (FractionRing V) (φ a)) - vV V (algebraMap V (FractionRing V) (φ b)) := by omega
      exact_mod_cast this
    exact this

theorem chval_div (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by
  by_cases ha : φ a = 0
  · exact ⟨0, by rw [ha, zero_mul]⟩
  rw [chval_eq φ e f r h a b hab hb, nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb),
    ← EReal.coe_sub, EReal.coe_nonneg, div_sub_div_same] at hr
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hle : (vV V (algebraMap V (FractionRing V) (φ b)) : ℝ) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    have := (div_nonneg_iff.1 hr)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  have hle' : vV V (algebraMap V (FractionRing V) (φ b)) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    exact_mod_cast hle
  set y := algebraMap V (FractionRing V) (φ a) / algebraMap V (FractionRing V) (φ b)
  have hy0 : y ≠ 0 := div_ne_zero (ne_zero_map ha) (ne_zero_map hb)
  have hyv : vV V y + vV V (algebraMap V (FractionRing V) (φ b)) = vV V (algebraMap V (FractionRing V) (φ a)) := by
    rw [← vV_mul hy0 (ne_zero_map hb), div_mul_cancel₀ _ (ne_zero_map hb)]
  obtain ⟨w, hw⟩ := mem_of_vV_nonneg y hy0 (by omega)
  refine ⟨w, IsFractionRing.injective V (FractionRing V) ?_⟩
  rw [map_mul, hw, div_mul_cancel₀ _ (ne_zero_map hb)]

theorem chval_nonneg (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a s : A)
    (hfs : f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) (hs : φ s ∉ maximalIdeal V) :
    0 ≤ r := by
  have hs0 : φ s ≠ 0 := fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)
  rw [chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]
  exact nval_nonneg e _

end Values

section Charts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transfer {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (j : S.J) (g : FractionRing (S.A j)) (x : S.A j) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
      [Module.Finite S.O V] (φ : S.A j →ₐ[S.O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal (S.A j)) [qq.IsPrime]
    (hqq : qq ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    ∃ a s : S.A j, s ∉ qq ∧ g * algebraMap (S.A j) (FractionRing (S.A j)) s =
      algebraMap (S.A j) (FractionRing (S.A j)) a := by
  refine Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq
  obtain ⟨e, r, he, hr, hr0⟩ := hpts V φ hφx
  exact chval_div φ.toRingHom e he g r hr hr0 a b hab hb

theorem nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by
  obtain ⟨a', s', hs', hfs'⟩ := transfer S j (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom e (S.ch j F) rr hch a' s' hfs' hs'

theorem nonneg_at_all_points {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by
  intro v hv
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, -, hmap, hChV⟩ := S.cover v hv
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  refine nonneg_at S hF h0 j x hxE hx0 V φ e (v F) (hChV a n F hF) ?_
  rw [sup_eq_left.2 hmap]
  exact (Ideal.IsPrime.ne_top inferInstance)

theorem nonneg_at_trivial {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  refine nonneg_at S hF h0 j x hxE hx0 V φ 1 (q F) (hChV a n F hF) ?_
  have hm : maximalIdeal S.O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
  exact hcen ϖ hϖ

theorem qpt_mem_trivSet (q : QPt Xo c) : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => h u.isUnit)

end Charts

end GlobalTheory.Reg.ChartInt

namespace GlobalTheory

theorem integrality_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c hS C hC
  refine ⟨?_, ?_⟩
  · rintro a n f hf ⟨la, h0⟩ q
    obtain ⟨S, hQ⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_trivial S hQ (hC a n hf) h0 _ (GlobalTheory.Reg.ChartInt.qpt_mem_trivSet q)
  · intro a n f hf la h0
    obtain ⟨S, -⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_all_points S (hC a n hf) h0

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_fg_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), KapFG Xo c ∧ KapTrdeg Xo c Dw.dim := by
  intro E _ _ _ H Dw l Xo c
  have hs : SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have h := fun Z : Comp Xo c =>
    GlobalTheory.residueField_genericPoint_fg_trdeg_of_smoothOfRelativeDimension c.F (Xo.XF c) strK Dw.dim hs Z.1 Z.2
  exact ⟨fun Z => (h Z).1, fun Z => (h Z).2⟩

end GlobalTheory.Reg
end

