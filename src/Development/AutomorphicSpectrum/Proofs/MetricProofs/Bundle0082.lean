module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsDualflag
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesValueAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) {i : Fin N} : stepCols N j i ≠ ∅ := by
  intro e
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have h0 : N - j < N := by omega
    have : (⟨N - j, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at this
    simp at this
  · have h0 : 0 < N := by have := i.2; omega
    have : (⟨0, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at this
    simp at this

theorem img_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F h hb hF' hF hG' hG hh hyp p k hp
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hp
  obtain ⟨a, ha, hz⟩ := hyp p k' hk'
  have hCB := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (stepCols_ne_empty M.j_le)
  have hdelta : ∀ I' J, IsStepRows N j p.2 I' → IsStepRows N j p.2 J →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
        valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z) = if I' = J then 1 else 0 := by
    intro I' J hI hJ
    have hu' := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ I').2
    have hu := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ J).1
    have e1 := (reg_sum hb Finset.univ (fun m' : ι' k' => F'.u' I' ⟨k', m'⟩ * F'.u ⟨k', m'⟩ J)
      fun m' _ => (reg_mul hb (hu' m') (hu m')).1).2
    rw [hF'.2.2.1 p k' hk' I' J hI hJ] at e1
    rw [Finset.sum_congr rfl fun m' _ => ((reg_mul hb (hu' m') (hu m')).2).symm, ← e1]
    split_ifs
    · exact map_one (regVal M'.x hb)
    · exact map_zero (regVal M'.x hb)
  have hread : ∀ I', IsStepRows N j p.2 I' →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * minorIJ (h p.1) I' (stepCols N j p.2) := by
    intro I' hI
    have e1 : ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * ∑ J, (∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
          valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z)) * minorIJ (h p.1) J (stepCols N j p.2) := by
      simp_rw [hz, plk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m' _ => ?_
      ring
    rw [e1]
    congr 1
    rw [Finset.sum_eq_single I']
    · rw [hdelta I' I' hI hI, if_pos rfl, one_mul]
    · intro J _ hne
      by_cases hJ : IsStepRows N j p.2 J
      · rw [hdelta I' J hI hJ, if_neg hne.symm, zero_mul]
      · rw [hoff J hJ, mul_zero]
    · simp
  refine ⟨a, ha, fun m => ?_⟩
  rw [img_step Cv F' F z hp hk' m]
  unfold stepCoord plk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hCB.1, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j p.2 I'
  · rw [if_pos hI, hread I' hI]; ring
  · rw [if_neg hI, hoff I' hI, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactor
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

section Unit

variable {R : Type} [CommRing R] {N : ℕ}

def unitCols (I' C : Finset (Fin N)) (e : I'.card = C.card) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun a b => ∑ s : Fin C.card,
    if a = I'.orderEmbOfFin e s ∧ b = C.orderEmbOfFin rfl s then 1 else 0

theorem unitCols_col (I' C : Finset (Fin N)) (e : I'.card = C.card) (a : Fin N) (t : Fin C.card) :
    (unitCols I' C e : Matrix (Fin N) (Fin N) R) a (C.orderEmbOfFin rfl t) =
      if a = I'.orderEmbOfFin e t then 1 else 0 := by
  simp only [unitCols, Matrix.of_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    rw [if_neg]
    rintro ⟨_, h⟩
    exact hs ((C.orderEmbOfFin rfl).injective h).symm
  · simp

theorem minor_unitCols (I' C J : Finset (Fin N)) (e : I'.card = C.card) :
    minorIJ (unitCols I' C e : Matrix (Fin N) (Fin N) R) J C = if J = I' then 1 else 0 := by
  by_cases hJ : J = I'
  · subst hJ
    rw [if_pos rfl, minorIJ, dite_eq_left e]
    have : (unitCols J C e : Matrix (Fin N) (Fin N) R).submatrix (J.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, unitCols_col, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  · rw [if_neg hJ, minorIJ]
    split_ifs with e'
    · have hns : ¬ J ⊆ I' := fun hs => hJ (Finset.eq_of_subset_of_card_le hs (by rw [e, e']))
      obtain ⟨a, haJ, haI⟩ := Finset.not_subset.1 hns
      have hr : a ∈ Set.range (J.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]; exact haJ
      obtain ⟨s, rfl⟩ := hr
      refine Matrix.det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply, unitCols_col, if_neg]
      intro h
      exact haI (h ▸ Finset.orderEmbOfFin_mem _ _ _)
    · rfl

theorem unitCols_blockDiag {j : ℕ} (I' C : Finset (Fin N)) (e : I'.card = C.card)
    (hs : ∀ a ∈ I', ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) :
    IsBlockDiag j (unitCols I' C e : Matrix (Fin N) (Fin N) R) := fun a b h => by
  simp only [unitCols, Matrix.of_apply]
  refine Finset.sum_eq_zero fun s _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h (hs _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _))

theorem stepRows_same_side {j : ℕ} {i : Fin N} {I' : Finset (Fin N)} (h : IsStepRows N j i I') :
    ∀ a ∈ I', ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have h2 := h.2 ha
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  split_ifs at h2 hb with c
  · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega
  · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    omega

theorem minorIJ_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  rw [minorIJ, dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp only [detFac, minorIJ_one_self, ite_self, mul_one]

end Unit

theorem detFac_ne_zero {Ω : Type} [Field Ω] {N j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) Ω}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  intro h0
  have hu : IsUnit T.det := hd.isUnit
  have h := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main Ω N j i hj).2.2.2 T T⁻¹ hT (hT.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu, detFac_one, h0, zero_mul] at h
  exact one_ne_zero h

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg


open FrameChange in
theorem plucker_change_of_frame : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ ρ : M.Ω, ρ ≠ 0 ∧ ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' → ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F₁ F₂ h₁ h₂ c₁ c₂ p k hp
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hd₁ := detFac_ne_zero hj p.2 hT₁.1 hT₁.2
  have hd₂ := detFac_ne_zero hj p.2 hT₂.1 hT₂.2
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hA₂ : (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₂ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  refine ⟨detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') /
    (detFac j p.2 (F₂.T p.1) * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k'),
    div_ne_zero (mul_ne_zero hd₁ hA₂) (mul_ne_zero hd₂ hA₁), fun m I' hI' => ?_⟩
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hd₂ hA₁)]
  linear_combination (-detFac j p.2 (F₂.T p.1)) * e1 + detFac j p.2 (F₁.T p.1) * e2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormulaStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → IsNormalScheme Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTermStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_leading_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuationStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_minor_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBoundStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_order_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

theorem values_adapted {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R : Subring Φ) {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (C₀ : Matrix (Fin r) (Fin n) Ω) (z : Ω)
    (u U Rm Rm' : Matrix (Fin r) (Fin r) Φ) (F : Matrix (Fin n) (Fin r) Φ)
    (hF : F = A.map i * u) (hu : u * U = T.map i * Rm) (hRm : ∀ a b, Rm a b ∈ R) (hRm' : ∀ a b, Rm' a b ∈ R)
    (hR : Rm * Rm' = 1) (hB : ∀ a b, i ((A * T) a b / z) ∈ R) (hC₀ : ∀ a b, i (C₀ a b) ∈ R)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / z) = if a = b then 1 else 0) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (F * U) a b / i z ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((F * U) k b / i z) = if a = b then 1 else 0 := by
  set B : Matrix (Fin n) (Fin r) Ω := Matrix.of fun a b => (A * T) a b / z with hBdef
  have hFU : F * U = (A * T).map i * Rm := by
    rw [hF, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, Matrix.map_mul]
  have hval : ∀ a b, (F * U) a b / i z = (B.map i * Rm) a b := by
    intro a b
    rw [hFU, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.map_apply, hBdef, Matrix.of_apply, map_div₀]
    ring
  have hCB : C₀ * B = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv a b
  have hRm2 : Rm' * Rm = 1 := mul_eq_one_comm.1 hR
  refine ⟨Rm' * C₀.map i, fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hval, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hB a k) (hRm k b)
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hRm' a k) (hC₀ k b)
  · have h1 : (Rm' * C₀.map i) * (B.map i * Rm) = 1 := by
      have h2 : C₀.map i * B.map i = 1 := by
        rw [← Matrix.map_mul, hCB]
        exact Matrix.map_one _ (map_zero i) (map_one i)
      calc (Rm' * C₀.map i) * (B.map i * Rm) = Rm' * (C₀.map i * B.map i) * Rm := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hRm2]
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    simpa only [hval] using h3

theorem colFrame_semi {Ω Φ E F : Type} [Field Ω] [Field Φ] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Φ F]
    {i : Ω →+* Φ} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ} (e : Fin r → E)
    (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame e T k)) = colFrame (fun a => j (e a)) (T.map i) := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [colFrame, map_sum, hj, Matrix.map_apply]

theorem isFrameAt_of_map {X : Scheme.{0}} {Ω E E' : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω E'] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (f : E →ₗ[Ω] E') (hf : Function.Injective f) {r : ℕ}
    (b : Fin r → E) (p : Cpt ξ) (h : (L.map f).IsFrameAt (fun k => f (b k)) p) : L.IsFrameAt b p := by
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have h2 : (L p).map (f.restrictScalars (regAt ξ p)) =
      (Submodule.span (regAt ξ p) (Set.range b)).map (f.restrictScalars (regAt ξ p)) := by
    have : (Set.range fun k => f (b k)) = (f.restrictScalars (regAt ξ p)) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [Submodule.map_span, ← this]
    exact h.2
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf h2

end Pure

section Main

theorem adapted_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hch
  obtain ⟨T, C₀, -, hfr, hreg, hC₀r, hinv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀)
    (LL 𝔐 (.inl τ)) (m (.inl τ)) (rk (CMType H) D.p D.q (.inl τ)) (n (.inl τ)) (VV 𝔐 (.inl τ)) (φ (.inl τ))
    (cc 𝔐 bW bO (.inl τ)) (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hch
  let e : Fin (rk (CMType H) D.p D.q (.inl τ)) → 𝔐.Li := fun a => (bW τ a : 𝔐.Li)
  have hfrV : (𝔐.V (.inl τ)).IsFrameAt (colFrame e T) ⟨pr p'.1, hp⟩ := by
    refine isFrameAt_of_map _ (inW 𝔐) (GenBases.inW_injective 𝔐) _ _ ?_
    have h : (fun k => inW 𝔐 (colFrame e T k)) = colFrame (cc 𝔐 bW bO (.inl τ)) T := by
      funext k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [colFrame, map_sum, map_smul]
      rfl
    rw [h]
    exact hfr
  have hE := hO.2.2.2.1
  have hpull := FlagPull.pull_isFrameAt hO.1 hE p' hp hfrV
  rw [← hV (.inl τ), colFrame_semi hE.1] at hpull
  have he : LinearIndependent Ω e :=
    (bW τ).linearIndependent.map' (𝔐.Vgen (.inl τ)).subtype (Submodule.ker_subtype _)
  have hw := hE.2 _ e he
  have hb : Fl.b (.inl τ) = colFrame (fun a => j (e a)) (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) := by
    funext k
    rw [hC.1 τ k, DetG.wBlock_gMat]
    rfl
  have hflag := Fl.sub (.inl τ)
  rw [hb] at hflag
  obtain ⟨U, Rm, Rm', hU, hRm, hRm', hR, hu, hgen⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inl τ))
    (rk (CMType H) D.p D.q (.inl τ)) (fun a => j (e a)) _ (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) p' hw
    (by rw [DetG.det_genU]; exact isUnit_one) hpull hflag
  obtain ⟨C, h1, h2, h3⟩ := values_adapted (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) (regAt 𝔐'.ξ p')
    (aOf 𝔐 bW bO φ (.inl τ)) T C₀ (seg x₀ c₁ ^ m (.inl τ)) _ U Rm Rm' (fMat (aOf 𝔐 bW bO φ) (.inl τ)) rfl hu hRm hRm' hR
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hreg a b))
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hC₀r a b)) hinv
  refine ⟨U, C, hU, h1, h2, h3, fun l => ?_⟩
  rw [hb]
  exact hgen l

end Main

end GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterionStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_unit_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptLatticeBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem flags_dual_of_flags_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x) (τ : CMType H) (X' : Scheme.{0}) (G : Type) [Field G] [Algebra Ω G] (ξ' : Spec (CommRingCat.of G) ⟶ X') (pr : X' ⟶ 𝔐.X) (Li' : Type) [AddCommGroup Li'] [Module G Li'] (j : 𝔐.Li →+ Li') (bO : Module.Basis (Fin D.q) Ω (Module.Dual Ω (𝔐.Vgen (.inr τ)))) (v : Fin D.q → 𝔐.Vgen (.inr τ)) (u : Matrix (Fin D.q) (Fin D.q) G), IsExtOver (algebraMap Ω G) j → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ pr (algebraMap Ω G) → (∀ a b, bO a (v b) = if a = b then 1 else 0) → (∀ a, u a a = 1) → (∀ a b, a < b → u a b = 0) → ((omBundle 𝔐 τ).pull ξ' pr (TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1 (bO l)) → ((𝔐.V (.inr τ)).pull ξ' pr j).IsFlagVBOn Set.univ (fun k => colFrame (fun a => j (v a)) uᵀ⁻¹ k.rev) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_dualflag

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptMorphismCompat
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem GlobalTheory.CompanionTheory.Ar.FlagPull.field_of_hodgeOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_field
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.InChartIffOfDominates
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' :=
  @PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates
end

