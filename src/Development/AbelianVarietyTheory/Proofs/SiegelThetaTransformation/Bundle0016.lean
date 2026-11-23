module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSIntertwines
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem im_quad_eq_re_imH (M : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    (star x ⬝ᵥ M *ᵥ x).im = (star x ⬝ᵥ imH M *ᵥ x).re := by
  have hq : star x ⬝ᵥ Mᴴ *ᵥ x = star (star x ⬝ᵥ M *ᵥ x) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, dotProduct_mulVec]
  unfold imH
  rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hq, smul_eq_mul]
  generalize star x ⬝ᵥ M *ᵥ x = q
  rw [Complex.star_def, Complex.sub_conj,
    show ((2 * q.im : ℝ) : ℂ) * I = (2 * I) * (q.im : ℂ) by push_cast; ring,
    inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero I_ne_zero), Complex.ofReal_re]

theorem imH_add_I_smul (Z P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) :
    imH (Z + I • P) = imH Z + P := by
  unfold imH
  rw [conjTranspose_add, conjTranspose_smul, hP.eq]
  have e : Z + I • P - (Zᴴ + star I • P) = (Z - Zᴴ) + (2 * I) • P := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def,
      Complex.conj_I]
    ring
  rw [e, smul_add, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

theorem imH_mul_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian) :
    imH (C * (C * Z + D)ᴴ) = -(C * imH Z * Cᴴ) := by
  have hDC : D * Cᴴ = C * Dᴴ := by
    have e := h.eq
    rwa [conjTranspose_mul, conjTranspose_conjTranspose] at e
  have e : C * (C * Z + D)ᴴ - (C * (C * Z + D)ᴴ)ᴴ = -(C * (Z - Zᴴ) * Cᴴ) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_add, conjTranspose_mul,
      Matrix.add_mul (C * Z) D Cᴴ, hDC]
    noncomm_ring
  unfold imH
  rw [e, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem im_quad_denom (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (x : Fin N → ℂ) :
    (star x ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ x)).im =
      -(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re := by
  have e : star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x) = star x ⬝ᵥ (C * imH Z * Cᴴ) *ᵥ x := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [e, mulVec_mulVec, im_quad_eq_re_imH, imH_mul_denom C D Z h, neg_mulVec, dotProduct_neg,
    Complex.neg_re]

theorem det_denom_ne_zero (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) : (C * Z + D).det ≠ 0 := by
  intro hdet
  have h0 : ((C * Z + D)ᴴ).det = 0 := by rw [det_conjTranspose, hdet, star_zero]
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
  have h1 := im_quad_denom C D Z h x
  rw [hx, mulVec_zero, dotProduct_zero, Complex.zero_im] at h1
  have hCx : Cᴴ *ᵥ x = 0 := by
    by_contra hne
    have h2 := (Complex.pos_iff.mp (hZ.dotProduct_mulVec_pos hne)).1
    linarith
  have hDx : Dᴴ *ᵥ x = 0 := by
    rw [conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec, hCx, mulVec_zero,
      zero_add] at hx
    exact hx
  have h3 := hp.dotProduct_mulVec_pos hx0
  rw [add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hCx, hDx, mulVec_zero, mulVec_zero, add_zero,
    dotProduct_zero] at h3
  exact lt_irrefl _ h3

theorem norm_det_denom_le_rank_one (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hp : (C * Cᴴ + D * Dᴴ).PosDef) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • vecMulVec v (star v)) + D).det‖ := by
  have hW := det_denom_ne_zero C D Z h hp hZ
  have hWh : IsUnit ((C * Z + D)ᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  obtain ⟨y, rfl⟩ : ∃ y, (C * Z + D)ᴴ *ᵥ y = v :=
    ⟨((C * Z + D)ᴴ)⁻¹ *ᵥ v, by rw [mulVec_mulVec, mul_nonsing_inv (A := (C * Z + D)ᴴ) hWh, one_mulVec]⟩
  have hstar : star ((C * Z + D)ᴴ *ᵥ y) = star y ᵥ* (C * Z + D) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  have e1 : I • vecMulVec (C *ᵥ ((C * Z + D)ᴴ *ᵥ y)) (star y ᵥ* (C * Z + D)) =
      vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y) * (C * Z + D) := by
    rw [vecMulVec_mul]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have key : C * (Z + I • vecMulVec ((C * Z + D)ᴴ *ᵥ y) (star ((C * Z + D)ᴴ *ᵥ y))) + D =
      (1 + vecMulVec (I • (C *ᵥ ((C * Z + D)ᴴ *ᵥ y))) (star y)) * (C * Z + D) := by
    rw [hstar, Matrix.mul_add C, Matrix.mul_smul C, mul_vecMulVec C, e1,
      Matrix.add_mul (1 : Matrix (Fin N) (Fin N) ℂ), Matrix.one_mul]
    abel
  have hs : (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y)).im ≤ 0 := by
    rw [im_quad_denom C D Z h y]
    have h0 := (Complex.nonneg_iff.mp (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ y))).1
    linarith
  have hone : 1 ≤ ‖1 + I * (star y ⬝ᵥ C *ᵥ ((C * Z + D)ᴴ *ᵥ y))‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    linarith
  rw [key, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hone

private theorem exists_eq_sum_vecMulVec_star {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.PosSemidef) :
    ∃ w : Fin N → Fin N → ℂ, P = ∑ k, vecMulVec (w k) (star (w k)) := by
  refine ⟨fun k i => (Real.sqrt (hP.1.eigenvalues k) : ℂ) *
    (hP.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k, ?_⟩
  have hspec := hP.1.spectral_theorem
  ext i j
  conv_lhs => rw [hspec]
  rw [Unitary.conjStarAlgAut_apply, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, vecMulVec_apply, Pi.star_apply, star_mul', Function.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) * (Real.sqrt (hP.1.eigenvalues k) : ℂ) =
      (RCLike.ofReal (hP.1.eigenvalues k) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg k)]
    rfl
  have hs : star ((Real.sqrt (hP.1.eigenvalues k) : ℝ) : ℂ) = (Real.sqrt (hP.1.eigenvalues k) : ℂ) :=
    Complex.conj_ofReal _
  rw [Matrix.star_apply, hs, ← hsq]
  ring

theorem norm_det_denom_mono :
    ∀ (N : ℕ) (C D Z P : Matrix (Fin N) (Fin N) ℂ), (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z).PosDef → P.PosSemidef → (C * Z + D).det ≠ 0 ∧ ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • P) + D).det‖ := by
  intro N C D Z P h hp hZ hP
  refine ⟨det_denom_ne_zero C D Z h hp hZ, ?_⟩
  obtain ⟨w, rfl⟩ := exists_eq_sum_vecMulVec_star P hP
  have gen : ∀ s : Finset (Fin N),
      (imH (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k)))).PosDef ∧
        ‖(C * Z + D).det‖ ≤ ‖(C * (Z + I • ∑ k ∈ s, vecMulVec (w k) (star (w k))) + D).det‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, smul_zero, add_zero]
      exact ⟨hZ, le_rfl⟩
    | insert k s hk ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [Finset.sum_insert hk, add_comm (vecMulVec _ _) _, smul_add, ← add_assoc]
      refine ⟨?_, ?_⟩
      · rw [imH_add_I_smul _ _ (posSemidef_vecMulVec_self_star (w k)).isHermitian]
        exact ih1.add_posSemidef (posSemidef_vecMulVec_self_star (w k))
      · exact ih2.trans (norm_det_denom_le_rank_one C D _ h hp ih1 (w k))
  exact (gen Finset.univ).2

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransform
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.WeilPV

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem trans_unique {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (h1 : IsSB ψ) (h2 : IsSB ψ') (t1 : TransS σ φ ψ)
    (t2 : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' h1 h2 _ hs fun ζ => ?_
  have e1 := t1 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e2 := t2 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e := e1.trans e2.symm
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
    Matrix.vecMul_one] at e
  exact e


omit [DecidableEq ι] in
theorem thS_smul (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem trans_smul {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} {φ ψ : Matrix κ ι ℚ → ℂ} (c : ℂ)
    (t : TransS σ φ ψ) : TransS σ (c • φ) (c • ψ) := fun τ hτ ζ => by
  rw [thS_smul, thS_smul, t τ hτ ζ]; ring


omit [DecidableEq ι] in
theorem sb_smul (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem vac_trans {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : ∃ A ε, VacS A ε φ) :
    ∃ A ε, VacS A ε ψ := by
  obtain ⟨A, ε, h⟩ := h
  obtain ⟨T, hom, hT⟩ := GlobalTheory.Phase.transS_intertwines κ ι σ hσ
  have mem : ∀ y, y ∈ A.map T.toAddMonoidHom ↔ T.symm y ∈ A := fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun hy => ⟨_, hy, by simp⟩⟩
  have hom' : ∀ y y', om (T.symm y) (T.symm y') = om y y' := fun y y' => by
    rw [← hom]; simp
  refine ⟨A.map T.toAddMonoidHom, fun y => ε (T.symm y), ?_, ?_, ?_, ?_, ?_, hψ, ?_⟩
  · obtain ⟨S, hS⟩ := h.fg
    classical
    let e := A.equivMapOfInjective T.toAddMonoidHom T.injective
    refine ⟨S.image e, ?_⟩
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ AddSubsemigroup.closure (S : Set A) := by rw [hS]; trivial
    induction hx using AddSubsemigroup.closure_induction with
    | mem x hx =>
        apply AddSubsemigroup.subset_closure
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using AddSubsemigroup.add_mem _ (ihx (by trivial)) (ihy (by trivial))
  · intro y
    rw [mem, h.dual]
    constructor
    · intro H y' hy'
      rw [← hom']; exact H _ ((mem _).1 hy')
    · intro H y' hy'
      have := H (T y') ((mem _).2 (by simpa using hy'))
      rw [← hom'] at this
      simpa using this
  · intro y hy; exact h.norm _ ((mem _).1 hy)
  · intro y hy y' hy'
    rw [map_add (f := _), h.semi _ ((mem _).1 hy) _ ((mem _).1 hy'), hom']
  · obtain ⟨m, hm, H⟩ := h.ord
    exact ⟨m, hm, fun y hy => by rw [map_nsmul]; exact H _ ((mem _).1 hy)⟩
  · intro y hy
    have t1 := trans_smul (ε (T.symm y)) (hT φ ψ h.sb hψ t (T.symm y))
    rw [h.fix _ ((mem _).1 hy), T.apply_symm_apply] at t1
    exact trans_unique hσ (sb_smul _ (GlobalTheory.SW.heisS_laws _ _ _ _ ψ hψ).1) hψ t1 t


omit [DecidableEq ι] in
theorem pv_sb {φ : Matrix κ ι ℚ → ℂ} (h : PV φ) : IsSB φ := by
  obtain ⟨⟨_, _, h⟩, -⟩ := h
  exact h.sb

theorem pv_parabolic (he : Even (Fintype.card κ)) {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (h0 : σ.toBlocks₂₁ = 0)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans hσ hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := _root_.GlobalTheory.Phase.ParabValues.values_parabolic κ ι he σ hσ h0 φ ψ (pv_sb h) hψ t y
  rw [e]; exact hu.mul (h.2 _)

theorem pv_J (he : Even (Fintype.card κ))
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS (Matrix.J ι ℚ) φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans (SymplecticGroup.J_mem ι ℚ) hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.Phase.val_trans_J κ ι he φ ψ (pv_sb h) hψ t y
  rw [e]
  exact hu.mul (_root_.GlobalTheory.Phase.ph_haar_of_shape κ ι _
    ((GlobalTheory.Phase.shape_conj_chr_mul κ ι φ ((GlobalTheory.Phase.VacShape.vacuum_shape κ ι φ).2.1 h)).2.1 y'))

theorem pv_mul (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by
  intro φ ψ hψ t h
  obtain ⟨w, hw⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ he hσ
  obtain ⟨w', hw'⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ' he hσ'
  obtain ⟨s1, t1, -⟩ := hw φ (pv_sb h)
  obtain ⟨s2, t2, -⟩ := hw' (w φ) s1
  have t3 := GlobalTheory.SW.transS_comp κ ι σ σ' hσ hσ' _ _ _ t1 t2
  rw [trans_unique (mul_mem hσ' hσ) hψ s2 t t3]
  exact H' _ _ s2 t2 (H _ _ s1 t1 h)

theorem pv_of_transS : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  intro κ ι _ _ _ he σ hσ
  obtain ⟨p₁, h1, p₂, h2, p₃, h3, z1, z2, z3, rfl⟩ :=
    GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ := SymplecticGroup.J_mem ι ℚ
  have P : ∀ p ∈ Matrix.symplecticGroup ι ℚ, p.toBlocks₂₁ = 0 →
      ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS p φ ψ → PV φ → PV ψ :=
    fun p hp z φ ψ hψ t h => pv_parabolic he hp z hψ t h
  have Q : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (Matrix.J ι ℚ) φ ψ → PV φ → PV ψ :=
    fun φ ψ hψ t h => pv_J he hψ t h
  have a := mul_mem h1 hJ
  have b := mul_mem a h2
  have c := mul_mem b hJ
  exact pv_mul he h3 c (P _ h3 z3) (pv_mul he hJ b Q (pv_mul he h2 a (P _ h2 z2)
    (pv_mul he hJ h1 Q (P _ h1 z1))))

end GlobalTheory.Phase.WeilPV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableExpNegTraceTotallyPositiveHermitian
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PosSum

theorem norm_entry_le_trace {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (i j : Fin N) : ‖A i j‖ ≤ A.trace.re := by
  have hd : ∀ k, 0 ≤ (A k k).re := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).1
  have hi : ∀ k, (A k k).im = 0 := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).2.symm
  have ht : ∀ k, (A k k).re ≤ A.trace.re := fun k => by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.single_le_sum (f := fun k => (A k k).re) (fun k _ => hd k) (Finset.mem_univ k)
  have h2 := (Complex.nonneg_iff.1 (hA.submatrix ![i, j]).det_nonneg).1
  have hji : A j i = conj (A i j) := by
    have := hA.1.apply j i
    simpa using this.symm
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hji,
    Complex.mul_conj, Complex.sub_re, Complex.mul_re, hi, Complex.ofReal_re, mul_zero, sub_zero,
    Matrix.cons_val_fin_one] at h2
  have h0 : 0 ≤ A.trace.re := (hd i).trans (ht i)
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [Complex.sq_norm, sq]
  have := mul_le_mul (ht i) (ht j) (hd j) h0
  linarith

theorem exists_repr_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem house_le_of_isType {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ τ ∈ Ψ, ‖τ x‖ ≤ B) : house x ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun τ => ?_
  change ‖τ x‖ ≤ B
  by_cases hτ : τ ∈ Ψ
  · exact h τ hτ
  · have := h _ (not_not.1 fun h' => hτ ((hΨ τ).2 h'))
    simpa using this

end GlobalTheory.SW.PosSum


open GlobalTheory.SW.PosSum in
theorem GlobalTheory.SW.summable_exp_neg_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  intro E _ _ _ Ψ hΨ N c δ hc hδ
  obtain ⟨C, hC, hb⟩ := exists_repr_le E
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let K : ℝ := Fintype.card ι * (C * c) + 1
  have hK : 0 < K := by positivity
  let m : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
      ∀ τ : Ψ, (T.map τ.1).PosSemidef} → ι → ℤ := fun T q =>
    (RingOfIntegers.basis E).repr ⟨_, T.2.2.1 q.1 q.2.1⟩ q.2.2
  have hm : Function.Injective m := by
    intro T T' h
    ext a b
    have : (⟨_, T.2.2.1 a b⟩ : 𝓞 E) = ⟨_, T'.2.2.1 a b⟩ :=
      (RingOfIntegers.basis E).ext_elem fun j => congrFun h (a, b, j)
    have h2 : (c : E) * T.1 a b = c * T'.1 a b := congrArg Subtype.val this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hc.ne') h2
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun T => ?_)
    ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (div_pos hδ hK)).comp_injective hm)
  set S := ∑ τ : Ψ, (T.1.map τ.1).trace.re with hS
  have h0 : ∀ τ : Ψ, 0 ≤ (T.1.map τ.1).trace.re := fun τ =>
    (Complex.nonneg_iff.1 (T.2.2.2 τ).trace_nonneg).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => h0 τ
  have hq : ∀ q, |(m T q : ℝ)| ≤ C * c * S := fun q => by
    refine (hb _ _).trans ?_
    change C * house ((c : E) * T.1 q.1 q.2.1) ≤ _
    rw [house_nat_mul, mul_assoc]
    gcongr
    refine house_le_of_isType hΨ hS0 fun τ hτ => ?_
    exact (norm_entry_le_trace (T.2.2.2 ⟨τ, hτ⟩) q.1 q.2.1).trans
      (Finset.single_le_sum (fun τ _ => h0 τ) (Finset.mem_univ (⟨τ, hτ⟩ : Ψ)))
  have hs : ∑ q, |(m T q : ℝ)| ≤ K * S := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun q _ => hq q).trans ?_
    simp only [Finset.card_univ, nsmul_eq_mul, K]
    nlinarith
  simp only [Function.comp_apply]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  calc δ / K * ∑ q, |(m T q : ℝ)| ≤ δ / K * (K * S) := by gcongr
    _ = δ * S := by field_simp
end

