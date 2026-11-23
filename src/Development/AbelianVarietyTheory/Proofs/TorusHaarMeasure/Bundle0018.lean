module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.PointwiseNormConstantSection
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MajInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section copy
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)

omit [NumberField E] [IsCMField E] in
theorem col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = Data.emb τ (P *ᵥ Pi.single k 1) := by
  funext i
  simp [ReciprocityTheory.ChartRestriction.G.FD.col, Data.emb]

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply]
  have hc : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.col (γ.map τ * Y) c = (γ.map τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
    intro c; funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab X hγ]

end copy

theorem exists_colP_rmul_eq_sum {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    ∃ L : Fin X.p0 → ℂ, X.colP (rmul x b) τ a = ∑ c, L c • X.colP x τ c := by
  classical
  refine ⟨fun c => b τ (Fin.castLE X.p0_le c) (Fin.castLE X.p0_le a), ?_⟩
  funext k
  have e1 : X.colP (rmul x b) τ a k = ∑ j, x τ k j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) k (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show b τ _ _ * x τ k _ = _
    rw [mul_comm]

theorem maj_rmul {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul x b) τ v = X.maj x τ v := by
  have h := MajorantConjugateTransfer.maj_transfer X hx (OrthogonalFrameDomain.rmul_mem_dom X hx hb) τ 1 1 (by simp) (by simp)
    (fun c => ?_) (fun a => ?_) v
  · simpa using h
  · have := exists_colP_rmul_eq_sum X (rmul x b) (ExtFPf.invF_mem X hb) τ c
    rw [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF] at this
    simpa using this
  · simpa using exists_colP_rmul_eq_sum X x hb τ a

theorem gram_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_stab X hγ.1 τ.1 (mat x τ)

theorem lact_mem_dom {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul, show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    refine mul_ne_zero ?_ (hx τ).1
    have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).det) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    exact (hu.map τ.1).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact X hγ]

theorem maj_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj (lact γ x) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) =
      X.maj x τ v := by
  have hc : ∀ c, col (mat (lact γ x) τ) c =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ col (mat x τ) c := by
    intro c; funext i
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) i c = _
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold Data.maj Data.posPart Data.gramPos
  simp only [hc, gram_lact X hγ, hermC_stab X hγ.1]

end GlobalTheory.MajInv

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem maj_lact_rmul :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) := by
  intro r X γ hγ x hx b hb
  refine ⟨MajInv.lact_mem_dom X hγ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), fun τ v => ?_⟩
  rw [MajInv.maj_lact X hγ, MajInv.maj_rmul X hx hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinStatementOf
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoincareAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_chi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h := congrArg norm (hpow γ hγ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem cpt_lact {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)
  simp only [mat, lact, cpt, rmul]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ))
    (Matrix.of (nmat X z τ))

theorem dom_of_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : lact γ x ∈ X.dom) : x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have h := (hx τ).1
    rw [e1, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [OntoS.gram_lact X hγ] at this

theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

theorem phla_lact {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) : phla X la (lact γ x) = phla X la x := by
  unfold phla Data.nfac dmin
  simp only [OntoS.gram_lact X hγ]

theorem poin_mul {r : ℕ} (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ)
    (hg : X.IsSec la' g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  have h1 : X.χ la' γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la' γ.2]; exact one_ne_zero
  have h2 : X.χ la γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la γ.2]; exact one_ne_zero
  simp only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  field_simp

theorem poinStatement_of :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (κ : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ), IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) → (PoinStatement (E := E)) := by
  intro hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF
  obtain ⟨κ, hκ⟩ := hκ r X x0 ho hPD bb hbb
  obtain ⟨hs, hb⟩ := hbdd r X la κ P hP hκ.2.2.2.2.1
    (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)
  refine ⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_,
    fun la' g hg x hx => poin_mul X la la' P g hg hx⟩
  obtain ⟨C, hC⟩ := hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1
  obtain ⟨K, hK, hKs⟩ := hκ.2.2.2.2.1
  refine ⟨C * K.toReal, fun x hx hxo => ?_⟩
  set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS
  have hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤
      ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) := by
    intro γ
    rw [← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
    refine (hC _ (isOrth_lact X γ.2 hxo)).trans ?_
    rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]
    gcongr
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_
    rw [cpt_lact] at hd ⊢
    have hd' := dom_of_lact X γ.2 hd
    rw [phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']
    exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))
  calc ENNReal.ofReal ‖poin X la P x‖
      = ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := ofReal_norm _
    _ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' γ : X.Γ, ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal C * S * K := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact hKs x hx
    _ = ENNReal.ofReal (C * K.toReal) * S := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]

end GlobalTheory.PoincareAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumMultiLtSucc
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.JetsPure

open Filter Asymptotics

open MeasureTheory Topology Filter Asymptotics in
open scoped ContDiff ENNReal Matrix in
theorem _root_.GlobalTheory.JetsPure.monomial_isBigO {n D : ℕ} (σ : Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hσ : ∀ k, DifferentiableAt ℂ (σ k) 0) (h0 : ∀ k, σ k 0 = 0) (α : Fin D → ℕ) :
    (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (∑ q, α q) := by
  have h1 : ∀ q, σ q =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ‖z‖ := by
    intro q
    have h := (hσ q).hasFDerivAt.isBigO_sub.norm_right
    simpa only [h0 q, sub_zero] using h
  have h2 : (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ q, ‖z‖ ^ α q :=
    IsBigO.finsetProd fun q _ => (h1 q).pow (α q)
  simpa only [Finset.prod_pow_eq_pow_sum] using h2


open MeasureTheory Topology Filter Asymptotics in
open scoped ContDiff ENNReal Matrix in
theorem _root_.GlobalTheory.JetsPure.main : ∀ (J I : Type) [Fintype I] (D T a : ℕ),
    a ≤ T + 1 → ∀ (n : J → ℕ) (e : ∀ p, Fin (n p) ≃ Fin D)
    (f w0 : ∀ p, _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ) (s : ∀ p, Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ)
    (t : ∀ p, I → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ),
    (∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), DifferentiableAt ℂ (f p) z ∧
      DifferentiableAt ℂ (w0 p) z ∧
      (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) →
    (∀ p, w0 p 0 ≠ 0 ∧ (∀ k, s p k 0 = 0) ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) 0).det
        ≠ 0) →
    (∀ v : J → ℂ, ∃ u : I → ℂ, ∀ p, ∑ k, u k * t p k 0 = v p) →
    ∃ cc : (Fin D → ℕ) → I → ℂ, ∀ p, (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
      cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) =O[𝓝 0]
        fun z => ‖z‖ ^ a := by
  intro J I _ D T a haT n e f w0 s t hdiff hnz hsurj
  induction a with
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have hf : ContinuousAt (f p) 0 := (hdiff p).self_of_nhds.1.continuousAt
    simpa using hf.tendsto.isBigO_one ℝ
  | succ a ih =>
    obtain ⟨cc, hcc⟩ := ih (by omega)
    have haT' : a ≤ T := by omega
    have hw0c : ∀ p, ContinuousAt (w0 p) 0 := fun p =>
      (hdiff p).self_of_nhds.2.1.continuousAt
    have hev : ∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), (DifferentiableAt ℂ (f p) z ∧
        DifferentiableAt ℂ (w0 p) z ∧ (∀ k, DifferentiableAt ℂ (s p k) z) ∧
        ∀ k, DifferentiableAt ℂ (t p k) z) ∧ w0 p z ≠ 0 :=
      fun p => (hdiff p).and ((hw0c p).eventually_ne (hnz p).1)
    have htaylor : ∀ p, ∃ b : (Fin (n p) → ℕ) → ℂ, (fun z => (f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
        cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) -
        ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b β * ∏ k, (s p (e p k) z / w0 p z) ^ β k)
          =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro p
      obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.mp (hev p)
      have hζ : DifferentiableOn ℂ
          (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        apply differentiableAt_euclidean.mpr
        intro k
        obtain ⟨⟨-, hw, hs, -⟩, hw0⟩ := hU z hz
        have hsk := hs (e p k)
        fun_prop (disch := assumption)
      have hg : DifferentiableOn ℂ (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        obtain ⟨⟨hf, hw, hs, ht⟩, -⟩ := hU z hz
        fun_prop
      obtain ⟨b, hb⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates (a := a) _
        (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U 0 hUo h0U
        hg hζ (by simp [(hnz p).2.1]; rfl) (hnz p).2.2 (by simpa only [sub_zero] using hcc p)
      exact ⟨b, by simpa only [WithLp.ofLp_toLp, sub_zero] using hb⟩
    choose b hb using htaylor
    choose u hu using fun α : Fin D → ℕ => hsurj fun p => b p (α ∘ e p) / w0 p 0 ^ T
    refine ⟨fun α => if ∑ q, α q < a then cc α else u α, fun p => ?_⟩
    have hsplit : _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1) = _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a ∪ Finset.Nat.antidiagonalTuple D a := by
      ext α
      simp only [Finset.mem_union, _root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff, Finset.Nat.mem_antidiagonalTuple]
      omega
    have hdisj : Disjoint (_root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a) (Finset.Nat.antidiagonalTuple D a) := by
      rw [Finset.disjoint_left]
      intro α h1 h2
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff] at h1
      rw [Finset.Nat.mem_antidiagonalTuple] at h2
      omega
    have hreidx : ∀ z, ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a,
        b p β * ∏ k, (s p (e p k) z / w0 p z) ^ β k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q := by
      intro z
      symm
      refine Finset.sum_nbij' (fun α => α ∘ e p) (fun β => β ∘ (e p).symm) ?_ ?_ ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
        rw [← hα]
        exact Equiv.sum_comp (e p) α
      · intro β hβ
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
        rw [← hβ]
        exact Equiv.sum_comp (e p).symm β
      · intro α _
        ext q
        simp
      · intro β _
        ext k
        simp
      · intro α _
        simp only [Function.comp_apply]
        rw [Equiv.prod_comp (e p) (fun q => (s p q z / w0 p z) ^ α q)]
    have hsum_split : ∀ z, ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1), ∑ k,
        (if ∑ q, α q < a then cc α else u α) k * (∏ q, s p q z ^ α q) *
          w0 p z ^ (T - ∑ q, α q) * t p k z =
        ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z +
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ k,
          u α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z := by
      intro z
      rw [hsplit, Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_pos (_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff.mp hα)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_neg (by rw [Finset.Nat.mem_antidiagonalTuple.mp hα]; exact lt_irrefl a)]
    have hR : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, (fun z => ∑ k, u α k *
        (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z -
        b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro α hα
      have hsum : ∑ q, α q = a := Finset.Nat.mem_antidiagonalTuple.mp hα
      obtain ⟨-, hw, hs, ht⟩ := (hdiff p).self_of_nhds
      have hH0 : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = b p (α ∘ e p) := by
        have hw : w0 p 0 ^ T ≠ 0 := pow_ne_zero _ (hnz p).1
        have h : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = w0 p 0 ^ T * ∑ k, u α k * t p k 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h, hu α p]
        field_simp
      have hHd : DifferentiableAt ℂ (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z)) 0 := by
        fun_prop
      have hHO : (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z) -
          ∑ k, u α k * (w0 p 0 ^ T * t p k 0)) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p) => ‖z‖ := by
        simpa only [sub_zero] using hHd.hasFDerivAt.isBigO_sub.norm_right
      have hmono := _root_.GlobalTheory.JetsPure.monomial_isBigO (fun q z => s p q z / w0 p z)
        (fun q => by
          have hsq := hs q
          have hw00 := (hnz p).1
          fun_prop (disch := assumption)) (fun q => by simp [(hnz p).2.1]) α
      rw [hsum] at hmono
      refine (hmono.mul hHO).congr' ?_ (Eventually.of_forall fun z => by ring)
      filter_upwards [(hw0c p).eventually_ne (hnz p).1] with z hz
      rw [hH0]
      have hP : ∏ q, s p q z ^ α q = (∏ q, (s p q z / w0 p z) ^ α q) * w0 p z ^ a := by
        rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
      have hW : w0 p z ^ a * w0 p z ^ (T - a) = w0 p z ^ T := by
        rw [← pow_add, Nat.add_sub_cancel' haT']
      rw [hsum, hP, mul_sub, Finset.mul_sum, ← hW]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    refine ((hb p).sub (IsBigO.sum hR)).congr' (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    clear hdiff hnz hsurj ih hcc hev hsplit hdisj hR hw0c hb hu
    beta_reduce
    rw [hsum_split z, hreidx z, Finset.sum_apply, Finset.sum_sub_distrib]
    ring

end GlobalTheory.JetsPure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFramesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, IsOrth X x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  first | exact @GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | exact GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | (intros; apply GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames <;> assumption)
end

