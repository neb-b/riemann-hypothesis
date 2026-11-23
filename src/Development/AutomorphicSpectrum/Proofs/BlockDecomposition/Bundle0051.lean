module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLaw
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEis

def cosMul {G : Type} [Group G] (P Γ : Subgroup G) (γ : Γ) : Cos P Γ ≃ Cos P Γ where
  toFun := Quotient.map (· * γ) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ) (y * γ)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  invFun := Quotient.map (· * γ⁻¹) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ⁻¹) (y * γ⁻¹)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]

theorem rep_mk {G : Type} [Group G] {P Γ : Subgroup G} (x : Γ) :
    ∃ δ : G, δ ∈ Γ ∧ δ ∈ P ∧ rep (Quotient.mk _ x : Cos P Γ) = δ * x := by
  have h : QuotientGroup.rightRel (P.subgroupOf Γ) (Quotient.out (Quotient.mk _ x : Cos P Γ)) x :=
    Quotient.mk_out (s := QuotientGroup.rightRel (P.subgroupOf Γ)) x
  rw [QuotientGroup.rightRel_apply] at h
  refine ⟨((x * (Quotient.out (Quotient.mk _ x : Cos P Γ))⁻¹)⁻¹ : Γ), Subtype.property _, ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.mp (inv_mem h))
  · simp [rep]

theorem tsum_rep_mul {G : Type} [Group G] {X : Type} [AddCommMonoid X] [TopologicalSpace X]
    {P Γ : Subgroup G} (F : G → X) (hF : ∀ δ ∈ Γ, δ ∈ P → ∀ x, F (δ * x) = F x) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ∑' q : Cos P Γ, F (rep q * (γ * g)) = ∑' q : Cos P Γ, F (rep q * g) := by
  rw [← Equiv.tsum_eq (cosMul P Γ ⟨γ, hγ⟩) (fun q : Cos P Γ => F (rep q * g))]
  refine tsum_congr fun q => ?_
  have hq : cosMul P Γ ⟨γ, hγ⟩ q = Quotient.mk _ (Quotient.out q * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨δ, h1, h2, h3⟩ := rep_mk (P := P) (Quotient.out q * (⟨γ, hγ⟩ : Γ))
  rw [hq, h3, mul_assoc δ, hF δ h1 h2]
  simp [rep, mul_assoc]

theorem norm_le_of_strip {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X}
    (hf : Differentiable ℂ f) {a b B C : ℝ} (hab : a < b)
    (hB : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ B) (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C) {z : ℂ} (h1 : a ≤ z.re) (h2 : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb h1 h2
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  refine Asymptotics.IsBigO.of_bound B ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
  have := hB w hw.1.le hw.2.le
  simpa using this

theorem entire_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] {f g : ℂ → X}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (R : ℝ) (h : ∀ z : ℂ, R < z.re → f z = g z) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  refine hfa.eq_of_eventuallyEq hga (z₀ := ((R + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {z : ℂ | R < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | R < z.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with z hz using h z hz

theorem bound_left {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hB hq]

theorem bound_right {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    B * q * n ≤ (A + B) * (p + q) * n := by
  refine mul_le_mul_of_nonneg_right ?_ hn
  nlinarith [mul_nonneg hA hq, mul_nonneg hB hp, mul_nonneg hA hp]

section Sec

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}

theorem sec_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) {δ : G} (h1 : δ ∈ Γ) (h2 : δ ∈ P) (x : G) :
    sec K P c ρ (δ * x) w = sec K P c ρ x w := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have e := h w hw (δ * p) (mul_mem h2 hp) ⟨k, hk⟩
  have e' := h w hw p hp ⟨k, hk⟩
  simp only at e e'
  rw [← mul_assoc, e, e', hP.ch.mul δ h2 p hp, hP.ch.rat δ h1 h2, one_mul]

theorem sec_right (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hw : w ∈ secSp K P c ρ) (x : G) (k : K) :
    sec K P c ρ (x * k) w = ρ k⁻¹ (sec K P c ρ x w) := by
  obtain ⟨p, hp, k', hk', rfl⟩ := hP.iwa x
  have e := h w hw p hp (⟨k', hk'⟩ * k)
  have e' := h w hw p hp ⟨k', hk'⟩
  simp only at e'
  have e2 : p * k' * (k : G) = p * (((⟨k', hk'⟩ : K) * k : K) : G) := by simp [mul_assoc]
  rw [e2, e, e', map_smul, mul_inv_rev, map_mul]
  rfl

theorem eis_mul_left (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    eis Γ K P c ρ (fun x => z * η x) (γ * g) w = eis Γ K P c ρ (fun x => z * η x) g w := by
  unfold eis
  refine tsum_rep_mul (fun x => Complex.exp (z * η x) • sec K P c ρ x w) ?_ hγ g
  intro δ h1 h2 x
  simp only [sec_left hP h hw h1 h2 x, hη.left δ h2 x, hη.rat δ h1 h2, zero_add]

theorem norm_term_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ} {Λ : G → ℂ}
    (hΛ : ∀ x, (Λ x).re = l x) (x : G) (w : W) :
    ‖Complex.exp (Λ x) • sec K P c ρ x w‖ ≤ M * ‖w‖ * Real.exp (l x) := by
  rw [norm_smul, Complex.norm_exp, hΛ, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb x w) (Real.exp_pos _).le

theorem summable_term [CompleteSpace W] {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    Summable fun q : Cos P Γ => Complex.exp (Λ (rep q * g)) • sec K P c ρ (rep q * g) w :=
  Summable.of_norm_bounded ((hl g).mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem norm_eis_le {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖) {l : G → ℝ}
    (hl : Conv Γ P l) {Λ : G → ℂ} (hΛ : ∀ x, (Λ x).re = l x) (g : G) (w : W) :
    ‖eis Γ K P c ρ Λ g w‖ ≤ M * ‖w‖ * pos Γ P l g :=
  tsum_of_norm_bounded ((hl g).hasSum.mul_left (M * ‖w‖)) fun q => norm_term_le hb hΛ _ w

theorem pos_nonneg (l : G → ℝ) (g : G) : 0 ≤ pos Γ P l g :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem eis_mul_right [CompleteSpace W] (hP : IsPar Γ K P c)
    (h : ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w)
    {M : ℝ} (hb : ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖)
    (hη : IsHt Γ K P η) (hw : w ∈ secSp K P c ρ) (z : ℂ) (hc : Conv Γ P fun g => z.re * η g) (g : G) (k : K) :
    eis Γ K P c ρ (fun x => z * η x) (g * k) w = ρ k⁻¹ (eis Γ K P c ρ (fun x => z * η x) g w) := by
  have hs := summable_term (Γ := Γ) (l := fun g => z.re * η g) (Λ := fun x => z * η x) hb hc
    (by intro x; simp) g w
  unfold eis
  rw [(ρ k⁻¹).map_tsum hs]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc]
  beta_reduce
  rw [hη.right _ k k.2, sec_right hP h hw, map_smul]

end Sec

theorem wallLaw_of_secLaw : SecLaw → WallLaw := by
  intro hS
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ P P' c η η' β L R D Op H hP hP' hη hη' hβ hW
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨h1, -, Ms, hb⟩ := hS G W K ρ hK hρ Γ P c hP
  obtain ⟨-, -, Ms', hb'⟩ := hS G W K ρ hK hρ Γ P' c hP'
  have hdiff : ∀ (g : G) (w : L), Differentiable ℂ fun z => H z g w := fun g w =>
    (hW.hol g).clm_apply (differentiable_const _)
  refine ⟨?_, ?_, ?_⟩
  · intro z γ hγ g
    refine ContinuousLinearMap.ext fun w => ?_
    have e : (fun z => H z (γ * g) w) = fun z => H z g w := by
      refine entire_eq (hdiff _ w) (hdiff _ w) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_left hP h1 hη (hW.le w.2) z hγ g]
    exact congrFun e z
  · intro z g k w
    have e : (fun z => H z (g * k) w) = fun z => ρ k⁻¹ (H z g w) := by
      refine entire_eq (hdiff _ w) ((ρ k⁻¹).differentiable.comp (hdiff g w)) R fun z hz => ?_
      rw [hW.eqR z hz, hW.eqR z hz, eis_mul_right hP h1 hb hη (hW.le w.2) z (hW.convR _ hz) g k, map_smul]
    exact congrFun e z
  · intro a b ha hb₀
    obtain ⟨MD, hD⟩ := hW.dEnt.2 a a
    obtain ⟨MO, hO⟩ := hW.op.2 b b hb₀
    refine ⟨|MD| * |Ms| + |Ms'| * |MO|, ?_⟩
    intro z hz1 hz2 g
    have hab : b < a := by linarith [hW.pos]
    obtain ⟨U, hU, B, hB⟩ := hW.bdd b a g
    have hg : g ∈ U := mem_of_mem_nhds hU
    have hp := pos_nonneg (Γ := Γ) (P := P) (fun x => a * η x) g
    have hq := pos_nonneg (Γ := Γ) (P := P') (fun x => β x - b * η' x) g
    have hA : 0 ≤ |MD| * |Ms| := by positivity
    have hB' : 0 ≤ |Ms'| * |MO| := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    refine norm_le_of_strip (f := fun z => H z g w) (B := B * ‖w‖) (hdiff g w) hab ?_ ?_ ?_ hz1 hz2
    · intro u hu1 hu2
      exact ((H u g).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB u hu1 hu2 g hg) (norm_nonneg _))
    · intro u hu
      have hO' := hO u hu.ge hu.le
      have hu' : u.re < -R := by rw [hu]; exact hb₀
      have e2 := norm_eis_le (Γ := Γ) hb' (l := fun x => β x - b * η' x) (hW.convL b hb₀)
        (Λ := fun x => (β x : ℂ) - u * η' x) (by intro x; simp [hu]) g (Op u w : W)
      have e3 : ‖(Op u w : W)‖ ≤ |MO| * ‖w‖ := by
        have : ‖(Op u w : W)‖ = ‖Op u w‖ := rfl
        rw [this]
        exact ((Op u).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hO'.trans (le_abs_self _)) (norm_nonneg _))
      show ‖H u g w‖ ≤ _
      rw [hW.eqL u hu' g w]
      calc _ ≤ Ms' * ‖(Op u w : W)‖ * _ := e2
        _ ≤ |Ms'| * (|MO| * ‖w‖) * _ := by
            refine mul_le_mul_of_nonneg_right ?_ hq
            exact mul_le_mul (le_abs_self _) e3 (norm_nonneg _) (abs_nonneg _)
        _ = |Ms'| * |MO| * _ * ‖w‖ := by ring
        _ ≤ _ := bound_right hA hB' hp hq (norm_nonneg _)
    · intro u hu
      have hD' := hD u hu.ge hu.le
      have hu' : R < u.re := by rw [hu]; exact ha
      have e2 := norm_eis_le (Γ := Γ) hb (l := fun x => a * η x) (hW.convR a ha)
        (Λ := fun x => u * η x) (by intro x; simp [hu]) g (w : W)
      show ‖H u g w‖ ≤ _
      rw [hW.eqR u hu' g w, norm_smul]
      calc _ ≤ |MD| * (|Ms| * ‖w‖ * _) := by
            refine mul_le_mul (hD'.trans (le_abs_self _)) (e2.trans ?_) (norm_nonneg _) (abs_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ hp
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = |MD| * |Ms| * _ * ‖w‖ := by
            have : ‖w‖ = ‖(w : W)‖ := rfl
            ring
        _ ≤ _ := bound_left hA hB' hp hq (norm_nonneg _)

end GlobalTheory.CompanionTheory.RgEis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
section
noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Wedge

variable {ι κ κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem gram_det_nonneg (A : Matrix ι κ ℂ) : 0 ≤ (Aᴴ * A).det := by
  exact (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg

theorem gram_det_im (A : Matrix ι κ ℂ) : (Aᴴ * A).det.im = 0 := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).2.symm

theorem nI_nonneg (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  exact (Complex.nonneg_iff.1 (gram_det_nonneg A)).1

theorem nI_ne_zero_iff_det (A : Matrix ι κ ℂ) : nI A ≠ 0 ↔ (Aᴴ * A).det ≠ 0 := by
  have him := gram_det_im A
  show (Aᴴ * A).det.re ≠ 0 ↔ _
  constructor
  · intro h h0
    apply h
    rw [h0, Complex.zero_re]
  · intro h h0
    apply h
    exact Complex.ext (by rw [h0, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem gram_det_ne_zero_iff (A : Matrix ι κ ℂ) :
    (Aᴴ * A).det ≠ 0 ↔ LinearIndependent ℂ Aᵀ := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit,
    ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_conjTranspose_mul_self,
    LinearMap.ker_eq_bot, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_iff

theorem nI_submatrix (e : κ' ≃ κ) (A : Matrix ι κ ℂ) : nI (A.submatrix id e) = nI A := by
  show ((A.submatrix id e)ᴴ * A.submatrix id e).det.re = (Aᴴ * A).det.re
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul Aᴴ A (⇑e) id (⇑e) Function.bijective_id,
    Matrix.det_submatrix_equiv_self]

theorem nI_fromCols_of_orth (B : Matrix ι κ ℂ) (D : Matrix ι κ' ℂ) (h : Bᴴ * D = 0) :
    nI (fromCols B D) = nI B * nI D := by
  have h' : Dᴴ * B = 0 := by
    have h2 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at h2
    exact h2
  show ((fromCols B D)ᴴ * fromCols B D).det.re = (Bᴴ * B).det.re * (Dᴴ * D).det.re
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols, h, h',
    Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, gram_det_im B, gram_det_im D, mul_zero, sub_zero]

theorem exists_proj (B : Matrix ι κ ℂ) (hB : LinearIndependent ℂ Bᵀ) :
    ∃ Y : Matrix κ ι ℂ, Y * B = 1 ∧ (B * Y)ᴴ = B * Y := by
  have hu : IsUnit (Bᴴ * B).det := isUnit_iff_ne_zero.2 ((gram_det_ne_zero_iff B).2 hB)
  have hG : (Bᴴ * B)ᴴ = Bᴴ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine ⟨(Bᴴ * B)⁻¹ * Bᴴ, ?_, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hG, Matrix.mul_assoc]

theorem commGroup_mul_mul_eq_mul_inv_mul_mul_mul [DecidableEq ι] (hD : DetMono) (hM : MulI) (B : Matrix ι κ ℂ) (Y : Matrix κ ι ℂ)
    (hYB : Y * B = 1) (hQ : (B * Y)ᴴ = B * Y) (C : Matrix ι κ' ℂ) :
    nI (fromCols B C) = nI B * nI ((1 - B * Y) * C) ∧ nI ((1 - B * Y) * C) ≤ nI C ∧
      (1 - B * Y) * B = 0 := by
  have hPP : B * Y * (B * Y) = B * Y := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYB, Matrix.one_mul]
  have hQB : (1 - B * Y) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYB, Matrix.mul_one, sub_self]
  have hQh : (1 - B * Y)ᴴ = 1 - B * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQ]
  have hQQ : (1 - B * Y) * (1 - B * Y) = 1 - B * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hPh : (B * Y)ᴴ * (B * Y) = B * Y := by
    rw [hQ, hPP]
  refine ⟨?_, ?_, hQB⟩
  · have hcols : fromCols B C = (fromCols B ((1 - B * Y) * C) : Matrix ι (κ ⊕ κ') ℂ) *
        (fromBlocks (1 : Matrix κ κ ℂ) (Y * C) (0 : Matrix κ' κ ℂ) (1 : Matrix κ' κ' ℂ)) := by
      rw [Matrix.fromCols_mul_fromBlocks]
      congr 1
      · rw [Matrix.mul_one, Matrix.mul_zero, add_zero]
      · rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
        abel
    have horth : Bᴴ * ((1 - B * Y) * C) = 0 := by
      rw [← Matrix.mul_assoc, ← hQh, ← Matrix.conjTranspose_mul, hQB, Matrix.conjTranspose_zero,
        Matrix.zero_mul]
    rw [hcols, (hM ι ι (κ ⊕ κ') (fromCols B ((1 - B * Y) * C))).2.1, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, Matrix.det_one, mul_one, norm_one, one_pow, mul_one, nI_fromCols_of_orth B _ horth]
  · have hX : ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = Cᴴ * ((1 - B * Y) * C) := by
      rw [Matrix.conjTranspose_mul, hQh, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - B * Y), hQQ]
    have hYX : Cᴴ * C - ((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C) = (B * Y * C)ᴴ * (B * Y * C) := by
      rw [hX, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (B * Y)ᴴ, hPh,
        Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, sub_sub_cancel]
    exact hD κ' (((1 - B * Y) * C)ᴴ * ((1 - B * Y) * C)) (Cᴴ * C)
      (Matrix.posSemidef_conjTranspose_mul_self _)
      (by rw [hYX]; exact Matrix.posSemidef_conjTranspose_mul_self _)

theorem wedgeI_of_detMono_mulI : DetMono → MulI → WedgeI := by
  intro hD hM ι _ _
  refine ⟨fun κ _ _ A => nI_nonneg A, fun κ _ _ A => (nI_ne_zero_iff_det A).trans (gram_det_ne_zero_iff A),
    fun κ κ' _ _ _ _ e A => nI_submatrix e A, fun κ _ _ B hB => ?_⟩
  obtain ⟨Y, hYB, hQ⟩ := exists_proj B hB
  exact ⟨Y, fun κ' _ _ C => commGroup_mul_mul_eq_mul_inv_mul_mul_mul hD hM B Y hYB hQ C⟩

end GlobalTheory.CompanionTheory.Wedge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.WedgeNorm

theorem wedge_fromCols_le {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {N : Fam K ι}
    (h : IsWedge N) (κ κ' : Type) [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (X : Matrix ι κ K) (Z : Matrix ι κ' K) :
    N (κ ⊕ κ') (fromCols X Z) ≤ N κ X * N κ' Z := by
  by_cases hX : LinearIndependent K Xᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ X hX
    obtain ⟨h1, h2, -⟩ := hY κ' Z
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (h.nonneg κ X)
  · have h0 : N (κ ⊕ κ') (fromCols X Z) = 0 := by
      by_contra hne
      have hli := (h.ne_zero _ _).1 hne
      apply hX
      have hc := hli.comp Sum.inl Sum.inl_injective
      have he : (((fromCols X Z)ᵀ : (κ ⊕ κ') → ι → K) ∘ Sum.inl) = (Xᵀ : κ → ι → K) := by
        funext i j
        rfl
      rwa [he] at hc
    rw [h0]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

theorem wedgeSub : WedgeSub := by
  intro K ι _ _ _ N h κ₀ κ₁ κ₂ _ _ _ _ _ _ B A C
  by_cases hB : LinearIndependent K Bᵀ
  · obtain ⟨Y, hY⟩ := h.quot κ₀ B hB
    obtain ⟨h1, -, -⟩ := hY (κ₁ ⊕ κ₂) (fromCols A C)
    obtain ⟨h2, -, -⟩ := hY κ₁ A
    obtain ⟨h3, -, -⟩ := hY κ₂ C
    rw [h1, h2, h3, Matrix.mul_fromCols]
    have hle := wedge_fromCols_le h κ₁ κ₂ ((1 - B * Y) * A) ((1 - B * Y) * C)
    have hn := h.nonneg κ₀ B
    calc N κ₀ B * N (κ₁ ⊕ κ₂) (fromCols ((1 - B * Y) * A) ((1 - B * Y) * C)) * N κ₀ B
        ≤ N κ₀ B * (N κ₁ ((1 - B * Y) * A) * N κ₂ ((1 - B * Y) * C)) * N κ₀ B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hn) hn
      _ = N κ₀ B * N κ₁ ((1 - B * Y) * A) * (N κ₀ B * N κ₂ ((1 - B * Y) * C)) := by ring
  · have h0 : N κ₀ B = 0 := by
      by_contra hne
      exact hB ((h.ne_zero _ _).1 hne)
    rw [h0, mul_zero]
    exact mul_nonneg (h.nonneg _ _) (h.nonneg _ _)

end GlobalTheory.CompanionTheory.WedgeNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProduct
section
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem prod_prod_symm_eq_diag_mul_prs_sq {n : ℕ} (g : Fin n → Fin n → ℂ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b, g a b = (∏ a, g a a) * (∏ p ∈ prs n, g p.1 p.2) ^ 2 := by
  have h1 : ∏ a, ∏ b, g a b = ∏ p : Fin n × Fin n, g p.1 p.2 :=
    (Fintype.prod_prod_type' (f := g)).symm
  have hd : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => p.1 = p.2),
      g p.1 p.2 = ∏ a, g a a := by
    refine Finset.prod_nbij' (fun p => p.1) (fun a => (a, a)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro a _; simp
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      ext <;> simp [this]
    · intro a _; rfl
    · intro p hp
      have : p.1 = p.2 := (mem_filter.mp hp).2
      simp [← this]
  have ho : ∏ p ∈ (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2).filter (fun p => ¬ p.1 = p.2),
      g p.1 p.2 = ∏ p ∈ prs n, g p.1 p.2 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp only [prs, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hp.1) (Ne.symm hp.2)
    · intro p hp
      have hlt : p.1 < p.2 := by simpa [prs] using hp
      simp only [mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap]
      exact ⟨not_lt.mpr hlt.le, hlt.ne'⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simpa using hg p.1 p.2
  rw [h1, ← Finset.prod_filter_mul_prod_filter_not univ (fun p : Fin n × Fin n => p.1 < p.2),
    ← Finset.prod_filter_mul_prod_filter_not (univ.filter fun p : Fin n × Fin n => ¬ p.1 < p.2)
      (fun p => p.1 = p.2), hd, ho]
  change (∏ p ∈ prs n, g p.1 p.2) * _ = _
  ring

theorem prod_one_add_div_mul_prod_pow {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a ≠ 0) :
    (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1)
      = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  have hZ : (∏ a, z a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hz a
  have h1 : ∏ a, ∏ b, (1 + z a / z b) = (∏ a, ∏ b, (z a + z b)) / (∏ a, z a) ^ n := by
    have hterm : ∀ a b, 1 + z a / z b = (z a + z b) / z b := by
      intro a b
      field_simp [hz b]
      ring
    simp only [hterm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have h2 : ∏ a, ∏ b, (z a + z b) = 2 ^ n * (∏ a, z a) * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
    rw [prod_prod_symm_eq_diag_mul_prs_sq (fun a b => z a + z b) (fun a b => add_comm _ _)]
    have : ∏ a, (z a + z a) = 2 ^ n * ∏ a, z a := by
      simp only [← two_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [this]
  have h3 : (∏ a, z a) * (∏ a, z a) ^ (n - 1) = (∏ a, z a) ^ n := by
    rcases n with _ | m
    · simp
    · simp [pow_succ, mul_comm]
  rw [h1, h2]
  field_simp
  rw [mul_comm (∏ a, z a), ← h3]
  ring

end GlobalTheory.CompanionTheory.CoefId
end

