module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledIsotropicStructureGeneral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropic
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_botSpan (g : M2 E r) (v : Fin r ⊕ Fin r → E) :
    v ∈ botSpan g ↔ ∃ c : Fin r → E, Sum.elim 0 c ᵥ* g = v := by
  rw [botSpan, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => Eq.congr_left ?_
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply]

theorem pair_vecMul (A B : M2 E r) (u v : Fin r ⊕ Fin r → E) :
    ((u ᵥ* A) ᵥ* B) ⬝ᵥ (fun j => cc ((v ᵥ* A) j)) = (u ᵥ* (A * B * ccT A)) ⬝ᵥ fun j => cc (v j) := by
  have e : (fun j => cc ((v ᵥ* A) j)) = ccT A *ᵥ fun j => cc (v j) := by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecMul, mulVec, dotProduct, cc, ccT, map_sum, map_mul, transpose_apply, map_apply,
      mul_comm]
  rw [e, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]

theorem iso_of_mem {g : M2 E r} (hg : g ∈ UU E r) {u v : Fin r ⊕ Fin r → E}
    (hu : u ∈ botSpan g) (hv : v ∈ botSpan g) :
    (u ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc (v j)) = 0 := by
  obtain ⟨c, rfl⟩ := (mem_botSpan _ _).1 hu
  obtain ⟨d, rfl⟩ := (mem_botSpan _ _).1 hv
  have h : ccT (ccT g) * Matrix.J (Fin r) E * ccT g = Matrix.J (Fin r) E :=
    (HAct.group_part hg).2.2.1
  rw [HAct.ccT_ccT] at h
  rw [pair_vecMul, h, Matrix.J, vecMul_fromBlocks]
  simp [dotProduct, cc]

theorem finrank_botSpan {g : M2 E r} (hg : g ∈ UU E r) : Module.finrank E (botSpan g) = r := by
  have h : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (HAct.group_part hg).1
  have hl := (Matrix.linearIndependent_rows_iff_isUnit.2 h).comp _
    (Sum.inr_injective (α := Fin r) (β := Fin r))
  have := finrank_span_eq_card hl
  rw [Fintype.card_fin] at this
  exact this

variable (X : Data E r)

theorem isUnit_dblT : IsUnit (dblT X) :=
  IsUnit.of_mul_eq_one_right _ (DblPair.dblT_left X)

theorem pair_dblT (x y x' y' : Fin r → E) :
    ((Sum.elim x y ᵥ* dblT X) ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc ((Sum.elim x' y' ᵥ* dblT X) j)) =
      X.κ0 / 2 * (herm X.Gm x x' - herm X.Gm y y') := by
  rw [pair_vecMul, DblPair.dblT_form, vecMul_fromBlocks]
  have e : ∀ x y : Fin r → E, herm X.Gm x y = ∑ b, (x ᵥ* X.Gm) b * cc (y b) := fun x y => by
    rw [herm, Finset.sum_comm]
    simp only [vecMul, dotProduct, Finset.sum_mul]
  simp [dotProduct, e, vecMul_neg, vecMul_smul, mul_add, Finset.mul_sum, mul_assoc, sub_eq_add_neg]

theorem mem_iota (γ : GL (Fin r) E) (x y : Fin r → E) :
    Sum.elim x y ᵥ* dblT X ∈ botSpan (iota X 1 γ) ↔ y = (γ⁻¹).1 *ᵥ x := by
  have hinj : Function.Injective fun v => v ᵥ* dblT X :=
    Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X)
  have hk : (2 * (X.κ0 / 4)) ≠ 0 := by simp [DblPair.kappa_ne X]
  have key : ∀ c : Fin r → E, Sum.elim 0 c ᵥ* iota X 1 γ =
      Sum.elim (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))
        ((γ⁻¹).1 *ᵥ (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))) ᵥ* dblT X := fun c => by
    rw [iota, Matrix.inv_eq_left_inv (DblPair.dblT_left X), ← vecMul_vecMul, ← vecMul_vecMul,
      vecMul_fromBlocks, vecMul_fromBlocks]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_vecMul, vecMul_zero, zero_add, add_zero,
      inv_one, Units.val_one, transpose_one, vecMul_one, vecMul_transpose]
  rw [mem_botSpan]
  constructor
  · rintro ⟨c, hc⟩
    rw [key] at hc
    have h := hinj hc
    have h1 := congrArg (· ∘ Sum.inl) h
    have h2 := congrArg (· ∘ Sum.inr) h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h1 h2
    rw [← h2, h1]
  · rintro rfl
    refine ⟨x ᵥ* ((2 * (X.κ0 / 4)) • X.Gm), ?_⟩
    rw [key, vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk,
      mul_nonsing_inv _ (Ne.isUnit X.Gm_det), one_smul, vecMul_one]

noncomputable def coord : ((Fin r → E) × (Fin r → E)) ≃ₗ[E] (Fin r ⊕ Fin r → E) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) E E).symm.trans
    (LinearEquiv.ofBijective (dblT X).vecMulLinear
      ⟨Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X),
        Matrix.vecMul_surjective_iff_isUnit.2 (isUnit_dblT X)⟩)

theorem coord_apply (p : (Fin r → E) × (Fin r → E)) :
    coord X p = Sum.elim p.1 p.2 ᵥ* dblT X := rfl

end GlobalTheory.SW.DblLag


open GlobalTheory.SW.DblLag in
theorem GlobalTheory.SW.lag_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  intro E _ _ _ r X
  refine ⟨fun γ γ' _ _ h => ?_, ?_⟩
  · refine inv_injective (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_)))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mem_iota X, ← h, mem_iota]
  rintro ⟨U, g, hg, rfl⟩
  set I := (botSpan g).comap (coord X).toLinearMap with hI
  have hm : ∀ p, p ∈ I ↔ Sum.elim p.1 p.2 ᵥ* dblT X ∈ botSpan g := fun p => Iff.rfl
  have hiso : ∀ p ∈ I, ∀ q ∈ I, herm X.Gm p.1 q.1 - herm X.Gm p.2 q.2 = 0 := fun p hp q hq => by
    have := iso_of_mem hg ((hm p).1 hp) ((hm q).1 hq)
    rw [pair_dblT] at this
    exact (mul_eq_zero.1 this).resolve_left (by simp [DblPair.kappa_ne X])
  have hd : Module.finrank E I = r := by
    rw [hI, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, finrank_botSpan hg]
  obtain ⟨a1, -, -, -, -, -, a2, -⟩ :=
    (doubled_isotropic_structure X.Gm X.Gm_herm X.Gm_det).1 I hiso hd
  by_cases h0 : DoubledSpace.left I = ⊥
  · obtain ⟨δ, ⟨d1, d2⟩, -⟩ := a2.1 h0
    refine Or.inl ⟨δ⁻¹, fun x y => ?_, ?_⟩
    · rw [← d1, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
    · ext v
      obtain ⟨⟨x, y⟩, rfl⟩ := (coord X).surjective v
      rw [coord_apply, mem_iota, inv_inv, ← d2, hm]
  · obtain ⟨ξ, hξ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Or.inr ⟨ξ, hne, a1 ξ hξ ξ hξ, (hm (ξ, 0)).1 hξ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemImageConjugate
section
open Matrix Complex NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

namespace GlobalTheory.Ker.ConjDatum

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (ComplexEmbedding.conjugate τ) G (P.map (starRingEnd ℂ)) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G P).map (starRingEnd ℂ) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, ComplexEmbedding.conjugate_coe_eq, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Ker.ConjDatum.det_map_ne {M : Matrix (Fin r) (Fin r) ℂ} (h : M.det ≠ 0) :
    (M.map (starRingEnd ℂ)).det ≠ 0 := by
  have hdet : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [hdet]
  exact (map_ne_zero _).2 h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.mem_image_conjugate (Ψ : Finset (E →+* ℂ)) (τ : E →+* ℂ) :
    τ ∈ Ψ.image ComplexEmbedding.conjugate ↔ ComplexEmbedding.conjugate τ ∈ Ψ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rwa [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice]
  · exact fun h => ⟨_, h, _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice τ⟩

def cpl (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Ψ.image ComplexEmbedding.conjugate :=
  ⟨ComplexEmbedding.conjugate τ.1, Finset.mem_image_of_mem _ τ.2⟩

def cfr (Ψ : Finset (E →+* ℂ)) (x : Frame (Ψ.image ComplexEmbedding.conjugate) r) : Frame Ψ r :=
  fun τ a b => conj (x (cpl Ψ τ) a b)

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_GG (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (p : ℕ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG _ G p) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G p := by
  intro τ
  obtain ⟨hdet, hpos⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
    ext a b
    rfl
  have hgram : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) G (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ : E →+* ℂ) G
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))).map (starRingEnd ℂ) := by
    rw [hmat]
    have h := _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (ComplexEmbedding.conjugate (τ : E →+* ℂ)) G
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))
    rw [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice] at h
    exact h
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · have h := hpos i
    have hminor : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ i =
        starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ) i) := by
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, hgram, ← Matrix.submatrix_map]
      rw [RingHom.map_det]
      rfl
    rw [hminor, Complex.conj_re]
    exact h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_Bor (Ψ : Finset (E →+* ℂ))
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor _ r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  obtain ⟨hdet, htri⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  refine ⟨?_, fun a c hca => ?_⟩
  · have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
      ext a b
      rfl
    rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, htri a c hca]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_rmul (Ψ : Finset (E →+* ℂ))
    (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ b) := by
  funext τ a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_lact (Ψ : Finset (E →+* ℂ)) (γ : GL (Fin r) E)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) := by
  funext τ a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum,
    _root_.GlobalTheory.Ker.ConjDatum.cpl, ComplexEmbedding.conjugate_coe_eq]

def conjData (X : Data E r) : Data E r where
  Ψ := X.Ψ.image ComplexEmbedding.conjugate
  cmType τ := by
    rw [mem_image_conjugate, mem_image_conjugate]
    exact X.cmType _
  Gm := X.Gm
  Gm_herm := X.Gm_herm
  Gm_det := X.Gm_det
  p0 := X.p0
  p0_le := X.p0_le
  signature τ := by
    obtain ⟨P, h1, h2⟩ := X.signature ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    refine ⟨P.map (starRingEnd ℂ), det_map_ne h1, ?_⟩
    have h4 := gram_conjugate (ComplexEmbedding.conjugate τ.1) X.Gm P
    rw [conjugate_twice] at h4
    rw [h4, h2]
    ext a b
    by_cases h : a = b <;> simp [Matrix.diagonal, h]
  Λ := X.Λ
  Λ_fg := X.Λ_fg
  Λ_span := X.Λ_span
  den := X.den
  den_ne := X.den_ne
  Λ_int := X.Λ_int
  Γ := X.Γ
  Γ_stab := X.Γ_stab
  Γ_index := X.Γ_index
  Γ_free γ hγ x hx b hb h := by
    refine X.Γ_free γ hγ _ (cfr_mem_GG _ _ _ hx) _ (cfr_mem_Bor _ hb) ?_
    rw [← cfr_lact, h, cfr_rmul]
  χ _ _ := 1
  χ_mul := by simp
  χ_add := by simp
  χ_fin _ := ⟨1, one_pos, by simp⟩
  ξ0 := X.ξ0
  ξ0_im := X.ξ0_im
  ξ0_ne := X.ξ0_ne
  κ0 := -X.κ0
  κ0_xi := by
    rcases X.κ0_xi with h | h
    · right; rw [h]
    · left; rw [h, neg_neg]
  κ0_sign τ := by
    have := X.κ0_sign ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  m := X.m
  m_pos := X.m_pos
  transv ξ hξ h0 s hs hi := by
    obtain ⟨γ, h1, h2⟩ := X.transv ξ hξ h0 (-s) (by unfold cc at hs ⊢; rw [map_neg, hs]) hi.neg
    refine ⟨γ, h1, ?_⟩
    rw [h2]
    congr 1
    ring

end

end GlobalTheory.Ker.ConjDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.Dict

theorem isHolFam_fibrePoint {S : Scheme.{0}} (G : Over S) [GrpObj G] {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (ex : (Fin g → ℂ) → (Over.mk x0 ⟶ G)) (hol : IsHolTo Set.univ (fun z => (ex z).left)) :
    IsHolFam (fun z => (vtfQ G (ex z)).left) := by
  have hol' : IsHolFam (fun z => (ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and] using hol U f
  have he : ∀ z, (ex z).left ≫ G.hom = x0 := fun z => Over.w (ex z)
  have h := isHolFam_vtfLift G.hom x0 (fun z => (ex z).left) he hol'
  let σ : pullback G.hom x0 ⟶ (Over.mk x0 ⊗ G).left := (pullbackSymmetry G.hom x0).hom
  have hσ : ∀ z, vtfLift G.hom x0 (fun z => (ex z).left) he z ≫ σ = (vtfQ G (ex z)).left := fun z => by
    refine vtf_pt_uniq G (ex z) _ ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_snd G.hom x0)).trans
        (pullback.lift_fst _ _ _))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_fst G.hom x0)).trans
        (pullback.lift_snd _ _ _))
  intro U f
  have h2 := h (σ ⁻¹ᵁ U) ((σ.app U).hom f)
  simp only [← hσ]
  exact ⟨h2.1, h2.2.congr fun z _ => (valAt'_comp _ σ U f).symm⟩

theorem hx_add_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (z a w : Fin g → ℂ) (t : ℂ) :
    hx X bas idx x (z + t • a) w = hx X bas idx x z w + t * hx X bas idx x a w := by
  simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem reads_existsUnique_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))), (∃! θ, A.Reads k F θ) ∧ ∀ θ, A.Reads k F θ → Differentiable ℂ θ ∧ ∀ v ∈ L, (A.χ v)⁻¹ ^ k • fock X bas idx x k (pv X idx x v) θ = θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A _ _ _ k F
  have hcov : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (A.ex z).left cpt ∈ (⨆ i, Xo.univ.t.PP.L.U i) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, top_le_of_mem hj⟩
  have hrd : ∀ θ, A.Reads k F θ → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * A.fr j z ^ (k : ℤ) := fun θ h j z hj =>
    h j z _ (vtfQ_snd _ _) (vtfQ_fst _ _) hj
  have hne : ∀ j z (m : ℤ), ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A.fr j z ^ m ≠ 0 :=
    fun j z m hj => zpow_ne_zero m (A.fr_ne j z hj)
  refine ⟨?_, fun θ h => ⟨fun z => ?_, fun v hv => ?_⟩⟩
  · choose ch hch using hcov
    refine ⟨fun z => valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => ch z)) (F.f (fun _ => ch z)) /
        A.fr (ch z) z ^ (k : ℤ), ?_, fun θ h => ?_⟩
    · intro j z pt h1 h2 hj
      obtain rfl := vtf_pt_uniq Xo.univ.t.G (A.ex z) pt h1 h2
      exact vtf_read Xo.univ.t.G Xo.univ.t.PP.L F (A.ex z) (fun j => A.fr j z) (fun j j' => A.fr_g j j' z)
        (ch z) j (hch z) hj _ (div_mul_cancel₀ _ (hne _ _ _ (hch z))).symm
    · funext z
      rw [hrd θ h _ z (hch z), mul_div_cancel_right₀ _ (hne _ _ _ (hch z))]
  · obtain ⟨j, hj⟩ := hcov z
    have ho : IsOpen {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      simpa only [Set.mem_univ, true_and] using (A.hol (Xo.univ.t.PP.L.U j) 0).1
    have hn := ho.mem_nhds hj
    have hd := (isHolFam_fibrePoint Xo.univ.t.G A.ex A.hol _ (F.f (fun _ => j))).2.mono
      (fun w (hw : w ∈ {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) =>
        vtf_chart Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (A.ex w) (fun _ => j) hw)
    have hq := (hd.differentiableAt hn).mul (((A.fr_hol j).differentiableAt hn).zpow (m := -(k : ℤ))
      (Or.inl (A.fr_ne j z hj)))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    have h1 := hrd θ h j w hw
    refine Eq.trans ?_ (congrArg (· * A.fr j w ^ (-(k : ℤ))) h1.symm)
    rw [_root_.zpow_neg, mul_inv_cancel_right₀ (hne _ _ _ hw)]
  · funext z
    obtain ⟨j, hj⟩ := hcov z
    have hex : A.ex (z + pv X idx x v) = A.ex z := by
      rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
    have hj' : ⊤ ≤ (A.ex (z + pv X idx x v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
      rw [hex]; exact hj
    have h2 := hrd θ h j _ hj'
    rw [hex, hrd θ h j z hj, A.fr_per v hv j z hj, mul_zpow, ← _root_.mul_assoc] at h2
    have h3 := mul_right_cancel₀ (hne _ _ _ hj') h2
    have hχ : A.χ v ≠ 0 := fun h0 => by simpa [h0] using A.χ_norm v hv
    simp only [Pi.smul_apply, fock, smul_eq_mul]
    rw [← h3, hx_add_smul, zpow_natCast, mul_pow, ← Complex.exp_nat_mul]
    set a := hx X bas idx x z (pv X idx x v)
    set b := hx X bas idx x (pv X idx x v) (pv X idx x v)
    have h4 : cexp (-((k : ℂ) * Real.pi * (a + 1 / 2 * b))) * cexp (k * (Real.pi * a + Real.pi / 2 * b)) = 1 := by
      rw [← Complex.exp_add]
      refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
      ring
    have h5 : (A.χ v)⁻¹ ^ k * A.χ v ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hχ, one_pow]
    linear_combination (θ z * ((A.χ v)⁻¹ ^ k * A.χ v ^ k)) * h4 + θ z * h5

end GlobalTheory.Dict
end

