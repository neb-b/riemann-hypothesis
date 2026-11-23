module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
section
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q m : ℕ}

abbrev Low (m : ℕ) : Type := {s : Fin m × Fin m // s.2 < s.1}

def uni (y : Low m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => if h : b < a then y ⟨(a, b), h⟩ else if a = b then 1 else 0

def dens (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : ℝ :=
  ∏ i : Fin m, ‖lminor ((uni y)ᴴ * A * uni y) i.castSucc‖ ^ (-2 : ℤ)

def IsBlockSL2Embedding (e : Fin r ≃ Fin p ⊕ Fin q) : Prop :=
  (∀ a, (e.symm (Sum.inl a) : ℕ) = q + a) ∧ ∀ a, (e.symm (Sum.inr a) : ℕ) = a

def toMat (v : Fin p × Fin q → ℂ) : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun a b => v (a, b)

def glue (e : Fin r ≃ Fin p ⊕ Fin q) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : Low r → ℂ :=
  fun s => fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) (e s.1.1) (e s.1.2)

def base (e : Fin r ≃ Fin p ⊕ Fin q) (y : Low r → ℂ) : Fin p × Fin q → ℂ := vecOf (moeb (reindex e e (uni y)) 0)

def shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * A * fromBlocks 1 Z 0 1

def schur (H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₂₁

def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ)

theorem isBlockOrderedSumEquiv_trueIndex {r j : ℕ} (h : j ≤ r) : IsBlockSL2Embedding (idx h) := ⟨idx_symm_inl h, idx_symm_inr h⟩

theorem IsBlockSL2Embedding.card {e : Fin r ≃ Fin p ⊕ Fin q} (_ : IsBlockSL2Embedding e) : r = p + q := by
  simpa using Fintype.card_congr e

theorem exists_isBlockOrderedSumEquiv (p q : ℕ) : ∃ e : Fin (p + q) ≃ Fin p ⊕ Fin q, IsBlockSL2Embedding e :=
  ⟨((finCongr (add_comm p q)).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _), by
    constructor <;> intro a <;> simp [add_comm]⟩

@[simp] theorem toMat_vecOf (Z : Matrix (Fin p) (Fin q) ℂ) : toMat (vecOf Z) = Z := rfl

@[simp] theorem vecOf_toMat (v : Fin p × Fin q → ℂ) : vecOf (toMat v) = v := rfl

theorem det_uni (y : Low m → ℂ) : (uni y).det = 1 := by
  rw [det_of_lowerTriangular]
  · simp [uni]
  · intro a b h
    have h' : a < b := h
    simp [uni, not_lt_of_gt h', h'.ne]

theorem uni_eq_of_entries {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (y : Low r → ℂ) (y1 : Low q → ℂ) (y2 : Low p → ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) (h : ∀ s : Low r, y s = fromBlocks (uni y2) Y 0 (uni y1) (e s.1.1) (e s.1.2)) :
    reindex e e (uni y) = fromBlocks (uni y2) Y 0 (uni y1) := by
  ext a b
  rw [reindex_apply, submatrix_apply]
  by_cases hab : e.symm b < e.symm a
  · simp only [uni, of_apply, dif_pos hab]
    rw [h]; simp [uni]
  · simp only [uni, of_apply, dif_neg hab, EmbeddingLike.apply_eq_iff_eq]
    rw [Fin.lt_def] at hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]
    · have := b.2; omega
    · simp
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]

theorem reindex_uni_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e (uni (glue e w)) = fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) :=
  uni_eq_of_entries he _ _ _ _ fun _ => rfl

theorem base_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : base e (glue e w) = w.1 := by
  rw [base, reindex_uni_glue he, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    mul_nonsing_inv_cancel_right _ _ (by rw [det_uni]; exact isUnit_one), vecOf_toMat]

theorem glue_surjective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Surjective (glue e) := by
  intro y
  set M := reindex e e (uni y) with hM
  let y1 : Low q → ℂ := fun s => M (.inr s.1.1) (.inr s.1.2)
  refine ⟨(vecOf (M.toBlocks₁₂ * (uni y1)⁻¹), y1, fun s => M (.inl s.1.1) (.inl s.1.2)), funext fun s => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨b, rfl⟩ := e.symm.surjective b
  have hy : y ⟨(e.symm a, e.symm b), hab⟩ = M a b := by
    have hab' : e.symm b < e.symm a := hab
    simp only [hM, reindex_apply, submatrix_apply, uni, of_apply, dif_pos hab']
  rw [hy]
  simp only [glue, toMat_vecOf, Equiv.apply_symm_apply]
  rw [nonsing_inv_mul_cancel_right _ _ (by rw [det_uni]; exact isUnit_one)]
  replace hab : (e.symm b : ℕ) < e.symm a := hab
  rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
  · have : b < a := by rw [Fin.lt_def]; omega
    simp [uni, this]
  · rfl
  · have := a.2; omega
  · have : b < a := hab
    simp [uni, this, y1]

theorem continuous_uni : Continuous (uni : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) := by
  refine continuous_matrix fun a b => ?_
  simp only [uni, of_apply]
  split_ifs <;> fun_prop

theorem continuous_toMat : Continuous (toMat : (Fin p × Fin q → ℂ) → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_matrix fun a b => continuous_apply (a, b)

theorem continuous_glue (e : Fin r ≃ Fin p ⊕ Fin q) : Continuous (glue e) := by
  refine continuous_pi fun s => ?_
  have h1 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.1 :=
    continuous_uni.comp (by fun_prop)
  have h2 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.2 :=
    continuous_uni.comp (by fun_prop)
  exact (h2.matrix_fromBlocks ((continuous_toMat.comp continuous_fst).matrix_mul h1) continuous_const h1).matrix_elem _ _

theorem measurable_dens (A : Matrix (Fin m) (Fin m) ℂ) : Measurable (dens A) := by
  refine Finset.measurable_prod _ fun i _ => Measurable.pow_const (Continuous.measurable (Continuous.norm ?_)) _
  exact (((continuous_uni.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_uni).matrix_submatrix _ _).matrix_det

theorem dens_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : 0 ≤ dens A y :=
  Finset.prod_nonneg fun _ _ => zpow_nonneg (norm_nonneg _) _

theorem measurable_moeb_zero {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {g : α → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : Continuous g) (a : Fin p) (b : Fin q) :
    Measurable fun x => moeb (g x) 0 a b := by
  have h2 : Continuous fun x => (g x).toBlocks₂₂ := continuous_matrix fun _ _ => hg.matrix_elem _ _
  simp only [moeb_zero, Matrix.mul_apply, inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun c _ => (hg.matrix_elem (.inl a) (.inr c)).measurable.mul
    (h2.matrix_det.measurable.inv.mul (h2.matrix_adjugate.matrix_elem _ _).measurable)

theorem measurable_base (e : Fin r ≃ Fin p ⊕ Fin q) : Measurable (base e) :=
  Measurable.of_eval fun s => measurable_moeb_zero (continuous_uni.matrix_submatrix _ _) s.1 s.2

theorem det_shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).det = A.det := by
  simp [shear, det_conjTranspose, det_fromBlocks_zero₂₁]

theorem posDef_shear {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).PosDef :=
  hA.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2
    (by simp [det_fromBlocks_zero₂₁])))

theorem det_eq_mul_schur {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUnit H.toBlocks₂₂.det) :
    H.det = H.toBlocks₂₂.det * (schur H).det := by
  letI := invertibleOfIsUnitDet _ h
  conv_lhs => rw [← fromBlocks_toBlocks H, det_fromBlocks₂₂]
  rw [schur, invOf_eq_nonsing_inv]

theorem posDef_blocks {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : H.PosDef) :
    H.toBlocks₁₁.PosDef ∧ H.toBlocks₂₂.PosDef ∧ (schur H).PosDef := by
  have h1 : H.toBlocks₁₁.PosDef := h.submatrix Sum.inl_injective
  have h2 : H.toBlocks₂₂.PosDef := h.submatrix Sum.inr_injective
  refine ⟨h1, h2, ?_⟩
  letI := invertibleOfIsUnitDet _ h2.det_pos.ne'.isUnit
  have e : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ := by
    ext a b
    exact (h.1.apply _ _).symm
  have h3 := h.posSemidef
  rw [← fromBlocks_toBlocks H, e, PosDef.fromBlocks₂₂ _ _ h2, ← e] at h3
  refine h3.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)
  have h4 := h.det_pos.ne'
  rw [det_eq_mul_schur h2.det_pos.ne'.isUnit] at h4
  exact (right_ne_zero_of_mul h4).isUnit

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type}
  (ι : Tau → X.Ψ)

def coords (z : V (nd X)) : Tau → Low r → ℂ := fun t s => z (Fintype.equivFin (Ent X) ⟨ι t, s⟩)

def proj (z : V (nd X)) : Tau × Fin j × Fin (r - j) → ℂ := flat (domPt X hj ι (cpt X (x0F X) z))

theorem mat_nmat (z : V (nd X)) (t : Tau) : mat (nmat X z) (ι t) = uni (coords X ι z t) := rfl

theorem measurable_domPt : Measurable fun x : Frame X.Ψ r => flat (domPt X hj ι x) :=
  Measurable.of_eval fun s => measurable_moeb_zero
    ((continuous_const.matrix_mul (KU.cont_mat X (ι s.1))).matrix_submatrix _ _) s.2.1 s.2.2

theorem measurable_proj : Measurable (proj X hj ι) := (measurable_domPt X hj ι).comp (KU.cont_cpt X _).measurable

theorem proj_eq (z : V (nd X)) (t : Tau) (s : Fin j × Fin (r - j)) :
    proj X hj ι z (t, s) = base (idx hj) (coords X ι z t) s := by
  have e : frameCo X hj (cpt X (x0F X) z) (ι t) = reindex (idx hj) (idx hj) (uni (coords X ι z t)) := by
    rw [frameCo, ← mat_nmat]
    congr 1
    exact nonsing_inv_mul_cancel_left _ _ (det_x0F X (ι t)).isUnit
  simp only [proj, flat, domPt, base, vecOf, e]

theorem dmin_cpt (z : V (nd X)) (t : Tau) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X (x0F X) z) (ι t) i =
      lminor ((uni (coords X ι z t))ᴴ * sgnMat r X.p0 * uni (coords X ι z t)) i := by
  have h0 := congrArg transpose (isOrth_x0F X (ι t))
  rw [gram_eq_mul, diagonal_transpose] at h0
  have h1 := gram_eq_mul (ι t).1 X.Gm (mat (cpt X (x0F X) z) (ι t))
  have e : mat (cpt X (x0F X) z) (ι t) = mat (x0F X) (ι t) * uni (coords X ι z t) := rfl
  rw [sgnMat, ← h0, dmin, lminor, ← det_transpose, transpose_submatrix, h1, e, lminor]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end Data

end GlobalTheory.FlagFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntryHypOfTrueColumnChoices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem kerEntHyp_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → KerEntHyp Pl O Bs Y (I.tw l l0 Z) := fun I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8 =>
  ⟨_root_.GlobalTheory.KerVal.prTC_val I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, _root_.GlobalTheory.KerLatS.kerEntHyp_latS I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, _root_.GlobalTheory.Mem.Col2.TC.kerEnt_latT I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8, GlobalTheory.T.kernelEntries_form_true_chains I h1 h2 l Z l0 Y O Pl Bs h3 h4 h5 h6 h7 h8⟩

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsFormBaseChangeCrd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

namespace GlobalTheory

theorem ksForm_baseChange_crd {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']
    (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n')
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', GlobalTheory.Mem.R3.Rw.CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK))
    (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, GlobalTheory.Mem.R3.Rw.CrdOver ι x x')
    (h : ∃ (m : ℕ) (b : Fin m → (Fin n → LL)), (∀ i, b i ∈ WK) ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK ∧ LinearIndependent LL b ∧
        Submodule.span LL (Set.range b) = ⊤) :
    ∃ (m : ℕ) (b : Fin m → (Fin n' → LL')), (∀ i, b i ∈ WK') ∧ LinearIndependent Ks b ∧
        Submodule.span Ks (Set.range b) = WK' ∧ LinearIndependent LL' b ∧
        Submodule.span LL' (Set.range b) = ⊤ := by
  subst hn
  have hc : ∀ x : Fin n → LL, GlobalTheory.Mem.R3.Rw.CrdOver ι x (fun k => ι (x k)) :=
    fun x => ⟨rfl, fun k k' hk => by rw [Fin.ext hk]⟩
  refine GlobalTheory.ksForm_baseChange ι hι WK WK' (fun x => (hmem x _ (hc x)).symm) ?_ h
  intro x' hx'
  obtain ⟨x, -, hx⟩ := honto x' hx'
  have he : x' = fun k => ι (x k) := funext fun k => hx k k rfl
  subst he
  exact ⟨x, (hmem x _ (hc x)).1 hx', rfl⟩

end GlobalTheory


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.ksForm_moved : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ i : Fin (w'.st Z').toD7.R.m, (R'.FW i).IsKsForm := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hcore hlaws Xg tr R' hR hmu ι hι i
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  rcases core' with ⟨⟨⟨H', l', c'⟩⟩⟩
  obtain ⟨hH, hl, hc, -⟩ := hcore
  have hH' := eq_of_heq hH
  subst hH'
  have hl' := eq_of_heq hl
  subst hl'
  have hc' := eq_of_heq hc
  subst hc'
  obtain ⟨-, -, -, -, -, hnW, -, -, -, -, -, -, hcol, -⟩ := hR
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hι'⟩ := hcol i i rfl
  obtain ⟨-, ⟨hmem, honto⟩, -⟩ := hι' ι hι
  have hn : z.R.nW i = R'.nW i := congrFun (eq_of_heq hnW).symm i
  have halg2 : ∀ y : ↥z.core.Q.c.F, ι (algebraMap _ _ y) = @algebraMap _ _ _ _ alg' y := by
    intro y
    apply (w'.st Z').toD7.what₂.embLL.injective
    rw [hι]
    exact (z.alg_eq y).trans (halg y).symm
  exact GlobalTheory.ksForm_baseChange_crd ι halg2 hn (z.R.FW i).WK (R'.FW i).WK hmem honto (z.geo.fw.ks i)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsJEnl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Ext

theorem lawsJ_enl : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      Formalism.L2.Pj.LawsJ core' := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hH hL Xg tr R' hRS hmu ι hι
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hH
  obtain ⟨P'⟩ := B'
  dsimp only at hPre
  subst hPre
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := core'
  have e1 : H = z.core.Q.H := eq_of_heq h1; subst e1
  have e2 : l = z.core.Q.l := eq_of_heq h2; subst e2
  have e3 : c = z.core.Q.c := eq_of_heq h3; subst e3
  have e4 : Dw = z.core.Q.Dw := eq_of_heq h4; subst e4
  have e5 : Xo = z.core.Q.Xo := eq_of_heq h5; subst e5
  have e6 : U = z.core.U := eq_of_heq h6; subst e6
  have e7 : V = z.core.V := eq_of_heq h7; subst e7
  have e8 : dict = z.core.dict := eq_of_heq h8; subst e8
  have e9 : mu = z.core.mu := eq_of_heq h9; subst e9
  have e10 : Kf = z.core.Kf := eq_of_heq h10; subst e10
  have e11 : cE = z.core.cE := eq_of_heq h11; subst e11
  have e12 : chiW = z.core.chiW := eq_of_heq h12; subst e12
  have e13 : x₀ = z.core.x₀ := eq_of_heq h13; subst e13
  have e14 : iota = z.core.iota := eq_of_heq h14; subst e14
  have hz := z.geo.fw.laws
  constructor
  case toLawsM => exact hL.toLawsM
  case cUnit => exact (by with_unfolding_all exact (hz.cUnit :))
  case muVal => exact (by with_unfolding_all exact (hz.muVal :))
  case muConj => exact (by with_unfolding_all exact (hz.muConj :))
  case intAll => exact (by with_unfolding_all exact (hz.intAll :))
  case modelW => exact (by with_unfolding_all exact (hz.modelW :))
  case familyUniformisationBasePointOrthogonal => exact (by with_unfolding_all exact (hz.familyUniformisationBasePointOrthogonal :))
  case kfHalf => exact (by with_unfolding_all exact (hz.kfHalf :))
  case adPin => exact (by with_unfolding_all exact (hz.adPin :))

end GlobalTheory.Mem.R3.Ext
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Up

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T₀ D.R.m}

theorem exists_mjHTie_of_eq (F : Face3 D A3) (Xd : DivX D) {X X' : Cx.CxData A3.fam3.amb3} (e : X' = X)
    (jW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (jW0 : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (hj : HEq jW jW0)
    (eW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (h1 : ∀ (i : Fin D.R.m) x, Xd.jM ((i : ℕ) + 1) (eW i x) = jW i x)
    (h2 : ∀ i : Fin D.R.m, HLatTie (Xd.MjH ((i : ℕ) + 1)) ((A3.indefDown (X'.data F.cr false)).M i)
      ((A3.indefDown (X'.data F.cr false)).XW i) (eW i)) :
    ∃ J, MjHTie D A3.A Xd (A3.indefDown (X.data F.cr false)) jW0 J := by
  subst e
  cases hj
  exact ⟨⟨eW⟩, ⟨h1, h2⟩⟩

end GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.Up.mjAre_back : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  intro K B f T w Z hX Wt p0 r S' N h r'
  obtain ⟨z', hold', Y', Z', tix⟩ := r'
  intro hz
  change z' = _ at hz
  subst z'
  intro hj Y hY
  letI : Algebra (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).core.Q.c.F
      (w.st (SRe.upL Z S' N h)).toD7.what₂.LL :=
    (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).alg
  change HEq Z'.jW r.Z.jW at hj
  change MjAre Z' Y at hY
  obtain ⟨J', t'⟩ := hY
  have e := toCx3_eq (Up.refUp Z S' N h).to (iK := r.z.alg) r.z.R r.z.F
  with_unfolding_all
    exact exists_mjHTie_of_eq r.z.F (divBack Y) e.symm Z'.jW r.Z.jW hj J'.eW t'.j_eq t'.hlat

end
end

