module

public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
section
open Finset
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

section block

variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)

noncomputable def qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) (c : γ → ℂ) : ℂ :=
  ∑ x ∈ Y, ∑ y ∈ Y, conj (c x) * k x y * c y

def blockK (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) : α ⊕ β → α ⊕ β → ℂ :=
  fun x y => match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q

theorem blockPSD_iff (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) :
    KB.BlockPSD Y₁ Y₂ a w b ↔ TB.PSDOn (Y₁.disjSum Y₂) (blockK a w b) := by
  unfold KB.BlockPSD blockK
  exact Iff.rfl

theorem qf_block (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) (c : α ⊕ β → ℂ) :
    (qf (Y₁.disjSum Y₂) (blockK a w b) c).re =
      (qf Y₁ a (fun p => c (.inl p))).re + (qf Y₂ b (fun q => c (.inr q))).re +
        2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)).re := by
  have hconj : (∑ x ∈ Y₂, ∑ y ∈ Y₁, conj (c (.inr x)) * conj (w y x) * c (.inl y)) =
      conj (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)) := by
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [qf, Finset.sum_disjSum, blockK, Finset.sum_add_distrib]
  rw [hconj]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem psd_iff_qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) :
    TB.PSDOn Y k ↔ (∀ x ∈ Y, ∀ y ∈ Y, k y x = conj (k x y)) ∧ ∀ c, 0 ≤ (qf Y k c).re := by
  classical
  have hqf : ∀ c : γ → ℂ, qf Y k c = ∑ i : Y, ∑ j : Y, conj (c i) * k i j * c j := by
    intro c
    unfold qf
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have hsum : ∀ x : Y →₀ ℂ,
      (x.sum fun i xi => x.sum fun j xj => star xi * Matrix.of (fun x y : Y => k x y) i j * xj) =
        ∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j := by
    intro x
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    rfl
  unfold TB.PSDOn Matrix.PosSemidef
  constructor
  · rintro ⟨hH, hpos⟩
    refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
    · have h1 := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
      exact h1.symm
    · have h2 := hpos (Finsupp.equivFunOnFinite.symm fun i : Y => c i)
      rw [hsum] at h2
      rw [hqf]
      simpa using (Complex.le_def.mp h2).1
  · rintro ⟨hh, hq⟩
    refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
    · simp only [Matrix.of_apply]
      rw [hh j j.2 i i.2]
      rfl
    · rw [hsum]
      have hre := hq (fun g => if h : g ∈ Y then x ⟨g, h⟩ else 0)
      rw [hqf] at hre
      have hc : ∀ i : Y, (if h : (i : γ) ∈ Y then x ⟨i, h⟩ else 0) = x i := fun i => by simp
      simp only [hc] at hre
      have him : (∑ i : Y, ∑ j : Y, conj (x i) * k i j * x j).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hh i i.2 j j.2, Complex.conj_conj]
        ring
      exact Complex.le_def.mpr ⟨by simpa using hre, by rw [Complex.zero_im, him]⟩

theorem block_quad {a : α → α → ℂ} {w : α → β → ℂ} {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b)
    (c : α → ℂ) (d : β → ℂ) :
    0 ≤ (qf Y₁ a c).re + (qf Y₂ b d).re + 2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c p) * w p q * d q).re := by
  have h1 := ((psd_iff_qf _ _).1 ((blockPSD_iff Y₁ Y₂ a w b).1 h)).2 (Sum.elim c d)
  rw [qf_block] at h1
  simpa using h1

end block

theorem cross_le {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A * B) (hx : 0 ≤ x) : 2 * x ≤ A + B := by
  have hAB : 0 ≤ A + B := by linarith
  by_contra hc
  push_neg at hc
  nlinarith [sq_nonneg (A - B), mul_nonneg hAB hx]

theorem block_of_cauchy_schwarz : KB.BlockOfCS := by
  intro α β Y₁ Y₂ a w b ha hb hcs
  have ha' := (psd_iff_qf Y₁ a).1 ha
  have hb' := (psd_iff_qf Y₂ b).1 hb
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rcases x with p | q <;> rcases y with p' | q'
    · simpa [blockK] using ha'.1 p (by simpa using hx) p' (by simpa using hy)
    · simp [blockK]
    · simp [blockK]
    · simpa [blockK] using hb'.1 q (by simpa using hx) q' (by simpa using hy)
  · rw [qf_block]
    set X := ∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q) with hX
    have hA := ha'.2 (fun p => c (.inl p))
    have hB := hb'.2 (fun q => c (.inr q))
    have h1 := hcs (fun p => conj (c (.inl p))) (fun q => conj (c (.inr q)))
    have eX : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * conj (conj (c (.inr q))) * w p q) = X := by
      rw [hX]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.conj_conj]
      ring
    have eA : (∑ p ∈ Y₁, ∑ p' ∈ Y₁, conj (c (.inl p)) * conj (conj (c (.inl p'))) * a p p') =
        qf Y₁ a (fun p => c (.inl p)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have eB : (∑ q ∈ Y₂, ∑ q' ∈ Y₂, conj (c (.inr q)) * conj (conj (c (.inr q'))) * b q q') =
        qf Y₂ b (fun q => c (.inr q)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eX, eA, eB] at h1
    have hx := cross_le hA hB h1 (norm_nonneg X)
    have hre : -‖X‖ ≤ X.re := by
      have h2 := Complex.normSq_eq_norm_sq X
      rw [Complex.normSq_apply] at h2
      nlinarith [sq_nonneg X.im, norm_nonneg X]
    linarith

theorem blockPSD_mul {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a a' : α → α → ℂ} {w w' : α → β → ℂ}
    {b b' : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) (h' : KB.BlockPSD Y₁ Y₂ a' w' b') :
    KB.BlockPSD Y₁ Y₂ (fun p q => a p q * a' p q) (fun p q => w p q * w' p q) (fun p q => b p q * b' p q) := by
  rw [blockPSD_iff] at *
  refine Jx7.psd_congr ?_ (Jx7.psd_mul h h')
  intro x _ y _
  rcases x with p | q <;> rcases y with p' | q' <;> simp [blockK, map_mul]

theorem blockPSD_ones {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β) :
    KB.BlockPSD Y₁ Y₂ (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) := by
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · cases x <;> cases y <;> simp [blockK]
  · have hq : qf (Y₁.disjSum Y₂) (blockK (fun _ _ => (1 : ℂ)) (fun _ _ => 1) (fun _ _ => 1)) c =
        conj (∑ x ∈ Y₁.disjSum Y₂, c x) * ∑ x ∈ Y₁.disjSum Y₂, c x := by
      unfold qf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> simp [blockK]
    rw [hq, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_nonneg]

theorem blockPSD_prod {α β ι : Type} {Y₁ : Finset α} {Y₂ : Finset β} (s : Finset ι) (a : ι → α → α → ℂ)
    (w : ι → α → β → ℂ) (b : ι → β → β → ℂ) (h : ∀ v ∈ s, KB.BlockPSD Y₁ Y₂ (a v) (w v) (b v)) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ∏ v ∈ s, a v p q) (fun p q => ∏ v ∈ s, w v p q)
      (fun p q => ∏ v ∈ s, b v p q) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using blockPSD_ones Y₁ Y₂
  · intro v t hv ih h
    simp only [Finset.prod_insert hv]
    exact blockPSD_mul (h v (Finset.mem_insert_self v t)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

theorem block_cross_le {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a : α → α → ℂ} {w : α → β → ℂ}
    {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) :
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q‖ ≤ ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re) / 2 := by
  have key : ∀ u v : ℂ, 0 ≤ Complex.normSq u * (∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re +
      Complex.normSq v * (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re +
      2 * (conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q).re := by
    intro u v
    have h1 := block_quad Y₁ Y₂ h (fun _ => u) (fun _ => v)
    have e1 : qf Y₁ a (fun _ => u) = conj u * u * ∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e2 : qf Y₂ b (fun _ => v) = conj v * v * ∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e3 : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj u * w p q * v) = conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e1, e2, e3, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h1
    exact h1
  set S := ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q with hS
  by_cases h0 : S = 0
  · have k1 := key 1 (-1)
    rw [h0] at k1
    simp at k1
    rw [h0, norm_zero]
    simp only [Complex.re_sum]
    linarith
  · have hn : 0 < ‖S‖ := norm_pos_iff.mpr h0
    have k2 := key S (-(‖S‖ : ℂ))
    have hns : Complex.normSq S = ‖S‖ ^ 2 := Complex.normSq_eq_norm_sq S
    have hnr : Complex.normSq (-(‖S‖ : ℂ)) = ‖S‖ ^ 2 := by
      rw [Complex.normSq_neg, Complex.normSq_ofReal]
      ring
    have hcr : (conj S * -(‖S‖ : ℂ) * S).re = -(‖S‖ ^ 3) := by
      have e : conj S * -(‖S‖ : ℂ) * S = -((‖S‖ : ℂ) * (Complex.normSq S : ℂ)) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [e, hns, Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      ring
    rw [hns, hnr, hcr] at k2
    nlinarith [mul_pos hn hn, k2]

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CellSmoothness
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

end Formalism.FourierDecayAlt.P.CellSmoothness
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_wordSum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))⟩
  | cons cw L ih =>
    intro hL
    have h1 : B.InCC A m (fun g => cw.1 • B.Rw cw.2 F g) := by
      have hw := hL cw (by simp)
      have h0 : B.InCC A (m + cw.2.length) F :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (by omega) hF
      obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (fun X hX => (hw.1 X hX).1) h0
      exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 hc⟩
    have h2 := ih (fun cw' hcw' => hL cw' (List.mem_cons_of_mem cw hcw'))
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨c₁ + c₂, ?_⟩
    simpa [List.map_cons, List.sum_cons] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ hc₂

theorem coefficient_vector_in_L2_class : CVInCC := by
  intro k r E _ _ A m F Y s hF
  obtain ⟨L, hLw, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) F := by
    obtain ⟨c, hc⟩ := hF
    exact Formalism.FourierDecayAlt.P.B5.ckOn_mono (by exact_mod_cast Nat.le_add_left _ _) hc.1
  obtain ⟨c, hc⟩ := inCC_wordSum hF L hLw
  refine ⟨_, Formalism.FourierDecayAlt.P.Qx8.CCle_congr (f := fun g => s • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum) ?_
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s hc)⟩
  intro g hg
  rw [Pi.smul_apply, hCV E (B.GV k r) F hck g hg hg]

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVLocal
section
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem rw_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (B.Mat k r)}
    (hU : IsOpen U) {f₁ f₂ : B.Mat k r → E} (he : ∀ x ∈ U, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f₁ x = B.Rw w f₂ x
  | [], _, x, hx, hxG => he x hx hxG
  | X :: w, hw, x, hx, hxG => by
    show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x
    exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp))
      (rw_congr hU he w (fun Y hY => hw Y (by simp [hY])))

theorem coefficient_vector_locality : CVLocal := by
  intro k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  rw [hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  rw [rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem om_sub' {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  obtain ⟨hG, hD, hGf⟩ := hg
  refine ⟨⟨hG, fun a ha => by simp at ha⟩, hGf, fun a => hD _ (by show (a : ℕ) + 1 ≤ r; omega)⟩

theorem stab_fix_gq {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : (Fin r → ℂ) × ℂ) {p : Q.Mx k r × Q.Mx k r} (hp : p ∈ NF.Stab k r z z' μsec q.2) :
    p.1 * bigCell k r q.1 (μsec q.2) * p.2 = bigCell k r q.1 (μsec q.2) := by
  obtain ⟨h1, -, h3⟩ := hp
  obtain ⟨-, hsub, hcomm⟩ := Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts k r
  have hc := hcomm q.1 p.1 (hsub z h1)
  have hf := (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r q.1 (μsec q.2)).1
  have h3' : p.1 * B2.embWb k r (μsec q.2) * p.2 = B2.embWb k r (μsec q.2) := h3
  rw [hf]
  calc p.1 * (bigCell k r q.1 1 * B2.embWb k r (μsec q.2)) * p.2
      = (p.1 * bigCell k r q.1 1) * B2.embWb k r (μsec q.2) * p.2 := by simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * (p.1 * B2.embWb k r (μsec q.2) * p.2) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * B2.embWb k r (μsec q.2) := by rw [h3']

theorem fibre_membership_holds : FibMem := by
  unfold FibMem
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hP J hJ q hq
  simp only [NF.Fib, Set.mem_setOf_eq]
  intro p hp
  have hdom : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    obtain ⟨hq1, hq2⟩ := hq
    refine ⟨hq1, ?_⟩
    rw [hP.2.2.2.1, hP.2.2.2.2.1]
    exact hq2
  have hg := om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hdom)
  have hfix := stab_fix_gq (T v).base.μsec q hp
  have hJe := hJ.2.2.2 (B.gq (T v).base q) ⟨hg.1, hg.2⟩ p.1 hp.1 p.2 hp.2.1
  exact hJe.symm.trans (congrArg J hfix)

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem class_lower_decay_holds : JDCCLower := by
  intro k r Wp Wq _ _ _ _ _ _ Θ d A hd hG F hF hFA
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hΦck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word F) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) T.word_lie x (by simpa [wL] using hx))
    simpa using hF
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  refine ⟨?_, fun m => ?_⟩
  · rw [hop]
    clear hop
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (ap T.coef (B.Rw T.word F)) :=
        Pr.ck hO hcov ⟨(hG T (by simp)).1, hΦck T (by simp), fun g _ hg => by simp at hg⟩
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hΦck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · rw [hop]
    refine InCC_opsum Θ (fun T => ap T.coef (B.Rw T.word F)) ?_
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ : B.InCC (A - d + d) m (B.Rw T.word F) := by
      rw [sub_add_cancel]; exact InCC_Rw T.word_lie (hFA _)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hc (fun g _ hg => by simp at hg)⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

