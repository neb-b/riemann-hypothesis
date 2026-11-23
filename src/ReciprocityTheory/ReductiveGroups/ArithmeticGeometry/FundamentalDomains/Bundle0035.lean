module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlagSpanBounds
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma span_le_of_upper (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hcol : col (M * N) (Fin.castLE hp a) = ∑ j : Fin r, N j (Fin.castLE hp a) • col M j := by
    funext i
    simp only [col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  show col (M * N) (Fin.castLE hp a) ∈ Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a))
  rw [hcol]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : (j : ℕ) < p
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, congrArg (col M) (Fin.ext rfl)⟩)
  · have hlt : Fin.castLE hp a < j := Fin.lt_iff_val_lt_val.mpr (by show (a : ℕ) < j; omega)
    have h0 : N j (Fin.castLE hp a) = 0 := hN hlt
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

variable (X : Data E r)

lemma sameFlag_rmul (z : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : X.SameFlag z (rmul z b) := by
  unfold Data.SameFlag
  unfold Bor at hb
  rw [Set.mem_setOf_eq] at hb
  intro τ
  obtain ⟨hdet, htri⟩ := hb τ
  have hmul : mat (rmul z b) τ = mat z τ * mat b τ := by
    first
    | rfl
    | (unfold rmul mat; rfl)
    | (ext i j; simp [rmul, mat, Matrix.mul_apply])
  have hT : (mat b τ).BlockTriangular id := fun a c h => by
    first
    | exact htri a c h
    | (simp only [mat]; exact htri a c h)
  haveI : Invertible (mat b τ).det := invertibleOfNonzero hdet
  haveI : Invertible (mat b τ) := Matrix.invertibleOfDetInvertible _
  apply le_antisymm
  · have hinv : mat z τ = mat (rmul z b) τ * (mat b τ)⁻¹ := by
      rw [hmul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]
    rw [hinv]
    exact span_le_of_upper _ _ _ _ (Matrix.blockTriangular_inv_of_blockTriangular hT)
  · rw [hmul]
    exact span_le_of_upper _ _ _ _ hT

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · subst hv
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hx τ hv).le

end

end ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramMatrixExistence
section
namespace ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sub_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u w v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (u - a • w) v = hermC τ G u v - a * hermC τ G w v := by
  unfold hermC
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma hermC_smul_left_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u v : Fin r → ℂ) (a : ℂ) :
    hermC τ G (a • u) v = a * hermC τ G u v := by
  have h := hermC_sub_smul_left τ G 0 u v (-a)
  have h0 : hermC τ G 0 v = 0 := by simp [hermC]
  simpa [h0] using h

private lemma hermC_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (a : Fin n → ℂ) (g : Fin n → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ j, a j • g j) w = ∑ j, a j * hermC τ G (g j) w := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma hermC_sum_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ}
    (u : Fin r → ℂ) (b : Fin n → ℂ) (g : Fin n → Fin r → ℂ) :
    hermC τ G u (∑ l, b l • g l) = ∑ l, conj (b l) * hermC τ G u (g l) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma herm_eq_hermC_emb_emb (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    τ (herm G x y) = hermC τ G (Data.emb τ x) (Data.emb τ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]

private lemma emb_sum_smul' (τ : E →+* ℂ) {n : ℕ} (c : Fin n → E) (β : Fin n → Fin r → E) :
    Data.emb τ (∑ k, c k • β k) = ∑ k, τ (c k) • Data.emb τ (β k) := by
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Data.emb, Finset.sum_apply, map_sum, map_mul]

theorem Q_exists (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (β : Fin (r - 2) → Fin r → E) (hβξ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hli : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
      ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) :
    ∃ Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ, (∀ τ, (Q τ).det ≠ 0) ∧
      (∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
        ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
          (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c')) ∧
      (∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
        ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k) := by
  classical
  have hξξ : herm X.Gm ξ ξ = 0 := hξ.2.1
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := by
    intro τ h
    apply hξ0
    funext a
    have h1 := congrFun h a
    simp only [Data.emb, Pi.zero_apply, map_eq_zero] at h1
    simpa using h1
  have hHf : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := by
    intro τ
    rw [Data.Hf_self X.toData hz]
    exact_mod_cast (Data.maj_pos X.toData hz τ (he0 τ)).ne'
  have hperp : ∀ (τ : X.Ψ) (y : Fin r → E), herm X.Gm y ξ = 0 →
      hermC τ.1 X.Gm (Data.emb τ.1 y) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [← herm_eq_hermC_emb_emb, hy, map_zero]
  have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 :=
    fun τ => hperp τ ξ hξξ
  have huc : ∀ (τ : X.Ψ) (v : Fin r → E),
      X.ucomp z0 ξ (X.embV v) τ = uc X.toData z0 ξ τ (Data.emb τ.1 v) := fun τ v => rfl
  have hmem : ∀ (τ : X.Ψ) (v : Fin r → ℂ), hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      uc X.toData z0 ξ τ v ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ v hv
    set e := Data.emb τ.1 ξ with he
    set t := X.Hf z0 τ v e / X.Hf z0 τ e e with ht
    have hu : uc X.toData z0 ξ τ v = v - t • e := rfl
    have h1 : hermC τ.1 X.Gm (uc X.toData z0 ξ τ v) e = 0 := by
      rw [hu, hermC_sub_smul_left, hv, hee τ]
      ring
    have h2 : X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0 := by
      have hl : (2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e) =
          ((2 : ℂ) • X.ppos z0 τ v - v) - t • ((2 : ℂ) • X.ppos z0 τ e - e) := by
        rw [ReciprocityTheory.ChartRestriction.G.FD.OrthogonalComplementLines.ppos_sub X.toData, Data.ppos_smul_eq]
        module
      have hd : X.Hf z0 τ (uc X.toData z0 ξ τ v) e =
          X.Hf z0 τ v e - t * X.Hf z0 τ e e := by
        rw [hu]
        show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos z0 τ (v - t • e) - (v - t • e)) e = _
        rw [hl, hermC_sub_smul_left]
        rfl
      rw [hd, ht, div_mul_cancel₀ _ (hHf τ), sub_self]
    have h3 : hermC τ.1 X.Gm (X.Jt z0 τ (uc X.toData z0 ξ τ v)) e = 0 := by
      show hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ (uc X.toData z0 ξ τ v) -
        uc X.toData z0 ξ τ v)) e = 0
      rw [hermC_smul_left_mul]
      change I * X.Hf z0 τ (uc X.toData z0 ξ τ v) e = 0
      rw [h2, mul_zero]
    exact (hf τ).2.2.2.2 _ h1 h3
  have hcoord : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ∈ Submodule.span ℂ (Set.range (f τ)) →
      w = ∑ j : Fin (r - 2), ((if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) * hermC τ.1 X.Gm w (f τ j)) • f τ j := by
    intro τ w hw
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hermC_sum_smul_left]
    simp_rw [(hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> ring
  let Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ := fun τ => Matrix.of fun j k =>
    (if (j : ℕ) < X.p0 - 1 then (1 : ℂ) else -1) *
      hermC τ.1 X.Gm (uc X.toData z0 ξ τ (Data.emb τ.1 (β k))) (f τ j)
  have hb : ∀ (τ : X.Ψ) (k : Fin (r - 2)),
      uc X.toData z0 ξ τ (Data.emb τ.1 (β k)) = ∑ j, Q τ j k • f τ j := by
    intro τ k
    exact hcoord τ _ (hmem τ _ (hperp τ _ (hβξ k)))
  have hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k := by
    intro τ c
    rw [huc, emb_sum_smul', uc_comb (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) hz]
    simp_rw [hb τ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, ReciprocityTheory.MultiplicativeHeights.embVec, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hp : ∀ (τ : X.Ψ) (c : Fin (r - 2) → E),
      hermC τ.1 X.Gm (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 ξ) = 0 := by
    intro τ c
    rw [emb_sum_smul', hermC_sum_smul_left]
    simp [hperp τ _ (hβξ _)]
  have hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 ((Sform X β).h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c)
        (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c') := by
    intro τ c c'
    rw [Sform_h, herm_eq_hermC_emb_emb, ← uc_perp (X := X.toData) (z0 := z0) (ξ := ξ) (τ := τ) (hee τ)
      (Data.emb τ.1 (∑ k, c k • β k)) (Data.emb τ.1 (∑ k, c' k • β k)) (hp τ c) (hp τ c'),
      ← huc, ← huc, hQf, hQf, hermC_sum_smul_left]
    simp_rw [hermC_sum_smul_right, (hf τ).2.2.1]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  refine ⟨Q, ?_, hSQ, hQf⟩
  intro τ hdet
  apply detG_ne (X := X) (ξ := ξ) (β := β) hξ hβξ hli hspan
  have hmap : τ.1.mapMatrix (Sform X β).G = (Q τ)ᴴ *
      Matrix.diagonal (fun k : Fin (r - 2) => ReciprocityTheory.MultiplicativeHeights.sgn (X.p0 - 1) k) * Q τ := by
    ext a b
    have h := hSQ τ (Pi.single a 1) (Pi.single b 1)
    have hh : (Sform X β).h (Pi.single a 1) (Pi.single b 1) = (Sform X β).G a b := by
      simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h, Pi.single_apply, apply_ite, ite_mul, mul_ite]
    have hs : ∀ a : Fin (r - 2), ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (Pi.single a (1 : E)) = Pi.single a 1 := by
      intro a
      funext i
      by_cases hi : i = a
      · subst hi; simp [ReciprocityTheory.MultiplicativeHeights.embVec]
      · simp [ReciprocityTheory.MultiplicativeHeights.embVec, hi]
    rw [hh, hs, hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h]
    simp [ReciprocityTheory.MultiplicativeHeights.jForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdm := RingHom.map_det τ.1 (Sform X β).G
  rw [hmap, Matrix.det_mul, Matrix.det_mul, hdet, mul_zero] at hdm
  exact (map_eq_zero τ.1).1 hdm

end

end ReciprocityTheory.ChartRestriction.G.FD.GramMatrixExistence
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMaxHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem nonvanishingNearHalfMax_holds : NonvanishingNearHalfMax (E := E) := by
  unfold NonvanishingNearHalfMax
  intro r X la P z0 x0 w hSec hz0 hx0o ⟨b, hb, hx0⟩ hmax hpos hw hw1 hr Z hZ hPZ
  have hx0d : x0 ∈ X.dom := by rw [hx0]; exact OrthogonalFrameDomain.rmul_mem_dom (X := X) hz0 hb
  have hpx : X.pnorm la P x0 = X.pnorm la P z0 := by
    rw [hx0]; exact FrameDegreeData.pnorm_rmul (X := X) la P hSec.2.1 z0 hz0 b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun y => rfl
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
  have hw0 : w ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hwr : 0 < w * r := by nlinarith
  have hwr1 : 1 ≤ w * r := by nlinarith
  have hsq : Real.sqrt (w * r) ^ 2 = w * r := Real.sq_sqrt hwr.le
  have hs1 : 1 ≤ Real.sqrt (w * r) := by nlinarith [Real.sqrt_nonneg (w * r)]
  set ρ := frameRadius w r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, frameRadius]; positivity
  have hρle : ρ ≤ 1 / 10 := by
    rw [hρdef, frameRadius]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hρsq : 4 * w * r * ρ ^ 2 = 1 / 25 := by
    rw [hρdef, frameRadius, div_pow, mul_pow, hsq]
    field_simp
    ring
  have hM0 : 0 < ‖P x0‖ := by
    have h1 : 0 < X.pnorm la P x0 := hpx ▸ hpos
    rw [hpn] at h1
    rcases (norm_nonneg (P x0)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h1
      exact absurd h1 (lt_irrefl 0)
  have hzt : ∀ t : ℂ, ‖t‖ < 5 → X.zN (t • Z) ≤ ρ := fun t ht =>
    (OrthogonalFrameDomain.zN_smul_le (X := X) t Z).trans (by nlinarith [OrthogonalFrameDomain.zN_nonneg (X := X) Z, norm_nonneg t])
  have hdom : ∀ t : ℂ, ‖t‖ < 5 → X.xZ x0 (t • Z) ∈ X.dom := fun t ht =>
    OrthonormalChartBounds.xZ_mem_dom (X := X) hx0d hx0o (lt_of_le_of_lt (hzt t ht) (by linarith))
  have hbound : ∀ t : ℂ, ‖t‖ < 5 → ‖P (X.xZ x0 (t • Z))‖ < 3 * ‖P x0‖ := by
    intro t ht
    have hyd := hdom t ht
    have hny := BoundedSectionAlgebra.nfac_pos (X := X) hyd la
    have hnx := BoundedSectionAlgebra.nfac_pos (X := X) hx0d la
    have hlog := OrthonormalChartBounds.nfac_xZ (X := X) hx0d hx0o hρpos hρle (hzt t ht) la w hw
    have hz2 : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 25 := by
      rw [← hρsq]
      have hwr4 : 0 ≤ 4 * w * r := by nlinarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (OrthogonalFrameDomain.zN_nonneg (X := X) _) (hzt t ht) 2) hwr4
    have hlow : Real.log (X.nfac la x0) - 1 / 25 ≤ Real.log (X.nfac la (X.xZ x0 (t • Z))) := by
      have := (abs_le.mp (hlog.trans hz2)).1
      linarith
    have hexp : X.nfac la x0 * Real.exp (-(1 / 25)) ≤ X.nfac la (X.xZ x0 (t • Z)) := by
      rw [← Real.exp_log hnx, ← Real.exp_log hny, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpy : X.pnorm la P (X.xZ x0 (t • Z)) ≤ 2 * X.pnorm la P x0 := by
      rw [hpx]; exact hmax _ hyd
    rw [hpn, hpn] at hpy
    have h1 : ‖P (X.xZ x0 (t • Z))‖ * (X.nfac la x0 * Real.exp (-(1 / 25))) ≤
        2 * (‖P x0‖ * X.nfac la x0) :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hpy
    have h2 : ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) ≤ 2 * ‖P x0‖ := by
      have h3 : (‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25))) * X.nfac la x0 ≤
          (2 * ‖P x0‖) * X.nfac la x0 := by nlinarith
      exact le_of_mul_le_mul_right h3 hnx
    have hE : Real.exp (-(1 / 25)) * Real.exp (1 / 25) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : ‖P (X.xZ x0 (t • Z))‖ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) := by
      calc ‖P (X.xZ x0 (t • Z))‖
          = ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) * Real.exp (1 / 25) := by
            rw [mul_assoc, hE, mul_one]
        _ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have he := OrthogonalFrameDomain.exp_small
    nlinarith [mul_lt_mul_of_pos_left he hM0]
  have h5 : ∀ s ∈ Metric.ball (1 : ℂ) 4, ‖s‖ < 5 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 5 := by rw [norm_one]; linarith
  set g : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hg
  have hg1 : g 1 = 0 := by simp only [hg, one_smul]; exact hPZ
  have hg0 : g 0 = P x0 := by simp only [hg, zero_smul, (OrthogonalFrameDomain.xZ_zero (X := X))]
  have hgd : DifferentiableOn ℂ g (Metric.ball 1 4) := by
    intro t ht
    have hin : DifferentiableAt ℂ (fun s : ℂ => X.xZ x0 (s • Z)) t :=
      (OrthogonalFrameDomain.xZ_diff (X := X) x0).differentiableAt.comp t (differentiableAt_id.smul_const Z)
    exact (hSec.1 _ (hdom t (h5 t ht))).comp t hin.differentiableWithinAt
      (fun s hs => hdom s (h5 s hs))
  have hmaps : Set.MapsTo g (Metric.ball 1 4) (Metric.closedBall (g 1) (3 * ‖P x0‖)) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm, hg1, sub_zero]
    exact (hbound s (h5 s hs)).le
  have hd : dist (0 : ℂ) 1 = 1 := by simp [dist_eq_norm]
  have h0 : (0 : ℂ) ∈ Metric.ball (1 : ℂ) 4 := by rw [Metric.mem_ball, hd]; norm_num
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps h0
  rw [hg0, hg1, dist_zero_right, hd, mul_one] at hS
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

