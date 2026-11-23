module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorEqSmulComponent
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem pointNorm_eq_norm_mul (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    X.pnorm la G z = ‖G z‖ * X.pnorm la (fun _ => (1 : ℂ)) z := by
  simp only [Data.pnorm, norm_one, one_mul]

theorem pointNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.pnorm la G z := by
  unfold Data.pnorm
  refine mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem hatNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.hatN la G z := by
  unfold Data.hatN
  refine Real.sSup_nonneg fun t ht => ?_
  obtain ⟨x', -, -, rfl⟩ := ht
  exact X.pointNorm_nonneg la G x'

end Data

theorem epsilonZero_spec {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 ∧
    ∀ ε, 0 < ε → ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w →
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * ((4 * fdeg E : ℕ) : ℝ)) +
        ((4 * fdeg E : ℕ) : ℝ) + 2 <
        (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) := by
  have hf1 : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  have hd0 : 0 < dE E := field_discr_constant_pos
  have hg0 : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC0 : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  generalize hK : (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) = K2
  have hK1 : 1 ≤ K2 := by
    rw [← hK]
    have : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by positivity
    linarith
  have hN : ((4 * fdeg E : ℕ) : ℝ) = 4 * (fdeg E : ℝ) := by push_cast; ring
  generalize hR : w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * K2 * ((4 * fdeg E : ℕ) : ℝ)) +
      ((4 * fdeg E : ℕ) : ℝ) + 2 = R2
  have hR0 : 0 < R2 := by
    rw [← hR, hN]
    have : 0 ≤ 4 * (fdeg E : ℝ) * Real.log (2 * K2 * (4 * (fdeg E : ℝ))) :=
      mul_nonneg (by linarith) (Real.log_nonneg (by nlinarith))
    linarith
  generalize hB : (X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 = B
  have hB0 : 0 < B := by rw [← hB]; positivity
  have heq : flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w = min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) := by
    rw [← hB, ← hR, ← hK, hN]
    simp only [flowEpsilonBound]
    rw [← rootDiscriminant_eq_rpow]
  rw [heq]
  refine ⟨lt_min one_pos (div_pos (by positivity) (mul_pos hB0 hR0)), min_le_left _ _, fun ε hε hεlt => ?_⟩
  have hle : min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) ≤ (fdeg E : ℝ) ^ 2 / (B * R2) := min_le_right _ _
  have h1 := (le_div_iff₀ (mul_pos hB0 hR0)).1 (le_of_lt (lt_of_lt_of_le hεlt hle))
  rw [lt_div_iff₀ (mul_pos hB0 hε)]
  have hε' : ε * (B * R2) < (fdeg E : ℝ) ^ 2 := by
    have h2 := (lt_div_iff₀ (mul_pos hB0 hR0)).1 (lt_of_lt_of_le hεlt hle)
    exact h2
  calc R2 * (B * ε) = ε * (B * R2) := by ring
    _ < (fdeg E : ℝ) ^ 2 := hε'

set_option maxHeartbeats 1000000 in
theorem unipotent_vector_eq_smul_component {r : ℕ} (X : DataX E r) (z0 : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) (K : ℂ)
    (a : X.Ψ → Fin 2 → ℂ) (ha : a τ = ![-(K * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K / (X.NC : ℂ)]) :
    X.uvec ![ξ, (X.NC : E) • x] a τ = K • X.ucomp z0 ξ (X.embV x) τ := by
  have hNCc : (X.NC : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  rw [X.toData.orthogonal_component_apply]
  funext j
  simp only [Data.uvec, ha, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Data.emb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_natCast]
  generalize X.Hf z0 τ (fun a => τ.1 (x a)) (fun a => τ.1 (ξ a)) /
    X.Hf z0 τ (fun a => τ.1 (ξ a)) (fun a => τ.1 (ξ a)) = q
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem short_vector_setting_exists {r : ℕ} (X : DataX E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {ξ : Fin r → E}
    {ν : X.Ψ → ℝ} {c1 w : ℝ} {z0 : Frame X.Ψ r} (hH : ShortVectorHypotheses X la P ξ ν c1 w z0) {x : Fin r → E}
    (hxL : x ∈ X.L') (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    ∃ a, IsotropicFlowSetting X la P ξ ν c1 w z0 x a := by
  have hξ0 : ξ ≠ 0 := hH.2.2.1.2.2
  have hune : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0 := X.toData.orthogonal_component_ne_zero z0 hξ0 hxE
  obtain ⟨K, hK⟩ : ∃ K : X.Ψ → ℂ, ∀ τ,
      K τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨fun τ => ![-(K τ * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K τ / (X.NC : ℂ)],
    hH, hxL, hxξ, hxx, hxE, hune, fun τ => ?_⟩
  rw [← hK τ]
  exact unipotent_vector_eq_smul_component X z0 ξ x τ (K τ) _ rfl

theorem isotropic_pair_in_lattice {r : ℕ} (X : DataX E r) {ξ x : Fin r → E} (hiso : X.IsIso ξ) (hxL : x ∈ X.L')
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] ∧ ∀ i, ![ξ, (X.NC : E) • x] i ∈ X.Λ := by
  have hξ0 : ξ ≠ 0 := hiso.2.2
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ, HermitianTraceFormVanishing.cc_zero]
  refine ⟨⟨fun i k => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases k <;>
      simp [hiso.2.1, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hxξ, hξx, hxx]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNCE : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
      have htN : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNCE
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]; exact eq_neg_of_add_eq_zero_right hst
      apply hxE (-(s / (t * (X.NC : E))))
      calc x = (t * (X.NC : E))⁻¹ • ((t * (X.NC : E)) • x) := by
            rw [smul_smul, inv_mul_cancel₀ htN, one_smul]
        _ = -(s / (t * (X.NC : E))) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · fin_cases i
    · exact hiso.1
    · exact X.NC_sub x hxL

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnitaryComplementMoveOfIsotropic
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma ppos_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma ppos_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.ppos x τ 0 = 0 := by
  have := ppos_smul X x τ 0 0
  simpa using this

lemma ppos_selfadj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hA := gramPos_det_ne X hx τ
  have hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v) := fun v v' =>
    hC_symm τ.1 X.Gm X.Gm_herm v' v

  have hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) →
      hermC τ.1 X.Gm (X.ppos x τ v) y = 0 := by
    intro y v hy
    unfold ppos
    rw [hC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hC_smul_left, hsymm, hy a, map_zero, mul_zero]
  have h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0 :=
    hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)
  have h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0 :=
    hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]
  have e1 : hermC τ.1 X.Gm (X.ppos x τ u) w =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : w = X.ppos x τ w + (w - X.ppos x τ w) := by abel
    conv_lhs => rw [this]
    rw [hC_add_right, h1, add_zero]
  have e2 : hermC τ.1 X.Gm u (X.ppos x τ w) =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : u = X.ppos x τ u + (u - X.ppos x τ u) := by abel
    conv_lhs => rw [this]
    rw [hC_add_left, h2, add_zero]
  rw [e1, e2]

lemma Hf_eq (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
  have hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w := by
    have := hC_smul_right τ.1 X.Gm (-1) u w
    simpa using this
  calc X.Hf x τ u w = 2 * hermC τ.1 X.Gm u (X.ppos x τ w) - hermC τ.1 X.Gm u w := by
        simp only [Hf]; rw [hC_sub_left, hC_smul_left, ppos_selfadj X hx]
    _ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
        rw [sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]
        ring

section unitary

variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)

include hg

lemma gram_unitary : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

lemma ppos_unitary (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.ppos (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g v) = Matrix.mulVec g (X.ppos x τ v) := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = Matrix.mulVec g (col (mat x τ) a) := by
    intro a; exact col_mul g (mat x τ) a
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    simp only [gramPos]
    rw [show mat (X.lmulC (fun _ => g) x) τ = g * mat x τ from rfl, gram_unitary X x τ g hg]
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a
  have hpx : X.ppos x τ v = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hsum : Matrix.mulVec g (X.ppos x τ v) =
      ∑ a, α a • col (mat (X.lmulC (fun _ => g) x) τ) (Fin.castLE X.p0_le a) := by
    rw [hpx, mulVec_lin]; simp only [hcol]
  rw [hsum]
  apply ppos_eq_of X _ τ (by rw [hgram]; exact gramPos_det_ne X hx τ)
  intro b
  rw [← hsum, hcol, ← Matrix.mulVec_sub, hg]
  exact ppos_orth X x τ (gramPos_det_ne X hx τ) v b

end unitary

theorem unitaryComplementMove_of_isotropic : UnitaryComplementMove (E := E) := by
  intro r X ξ hξ x hx h1 hu hfix _hU
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := fun τ => by
    rw [← emb_herm, hξ.2.1, map_zero]
  set x' := X.lmulC h1 x with hx'
  have hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True := fun _ => Or.inr trivial

  have hmat : ∀ τ, mat x' τ = h1 τ * mat x τ := fun τ => rfl
  have hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ) := fun τ => by
    rw [hmat]; exact gram_unitary X x τ (h1 τ) (hu τ)

  have hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 1) (fun _ => 0)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero,
      sub_zero, add_zero] at h
    exact h
  have hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) =
      (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 0) (fun _ => -I)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h
    have e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      rw [smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by
        linear_combination (-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by
        linear_combination (-1 : ℂ) * Complex.I_mul_I, one_smul]
    rw [e1] at h
    exact h

  have hdom : x' ∈ X.dom := by
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · rw [hmat, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0

      have hrad : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by rw [← hu τ v w, hv]; simp [hermC]
      have hG : (Matrix.map X.Gm τ.1).det ≠ 0 := by
        have h := RingHom.map_det τ.1 X.Gm
        rw [show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl] at h
        rw [← h]; exact (map_ne_zero _).mpr X.Gm_det
      by_contra hne
      apply hG
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hne, ?_⟩
      funext b
      have := hrad (Pi.single b 1)
      simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply] using this
    · have : dmin X.Gm x' τ i = dmin X.Gm x τ i := by
        simp only [dmin]; rw [hgramτ]
      rw [this]; exact (hx τ).2 i
  refine ⟨hdom, ?_, ?_, ?_⟩
  ·
    intro u _
    funext τ
    have hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)
      rw [hfe τ] at hp
      rw [show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]
      rw [← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]
    simp only [aproj, lineV]
    rw [Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]
  · intro τ

    have hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ) := by
      have hgp : X.gramPos x' τ = X.gramPos x τ := by simp only [gramPos]; rw [hgramτ]
      simp only [posPart]
      rw [hgp]
      have hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) =
          hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a)) := by
        intro a
        rw [hmat, col_mul]
        conv_lhs => rw [← hfe τ]
        rw [hu τ]
      simp only [hc]
    simp only [maj, hpp]
  · intro u _
    funext τ
    simp only [Jz, applyV]
    have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)
    rw [show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) =
      X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Data

theorem unitaryComplementMove : UnitaryComplementMove (E := E) := Data.unitaryComplementMove_of_isotropic

end ReciprocityTheory.ChartRestriction.G.FD
end

