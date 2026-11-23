module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmatrixMulLower
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.ChernCalc
open scoped Matrix ComplexOrder

namespace GlobalTheory.LeadingMinorPositivity

section Lin

variable {s : ℕ}

theorem submatrix_mul_lower {κ : Type} (T : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0)
    (M : Matrix (Fin s) κ ℂ) (j : ℕ) :
    (T * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id =
      T.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id := by
  ext a b
  change ∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp)
    (fun l => T a l * M l b)]
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra h
  refine hl ?_
  rw [hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]

theorem leadMinor_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (j : ℕ) :
    leadMinor (T * G * Tᴴ) j =
      ((∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < j, ‖T a a‖ ^ 2 : ℝ) : ℂ) * leadMinor G j := by
  let v : {a : Fin s // (a : ℕ) < j} → Fin s := Subtype.val
  have h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ := by
    have := submatrix_mul_lower T hT (G.submatrix v id)ᴴ j
    have h2 := (congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)
    refine Eq.trans ?_ (h2.trans ?_)
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rfl
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
      rfl
  have h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ) := by
    have := submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j
    rw [← h1, Matrix.mul_assoc]
    exact this
  have h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a) :=
    Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab
  unfold leadMinor
  change ((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4,
    Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]
  congr 1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

theorem leadMinor_re_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re :=
  (Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1

theorem grD_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (i : Fin s) : 0 < grD G i :=
  div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)

theorem grD_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (hd : ∀ a, T a a ≠ 0) (i : Fin s) :
    grD (T * G * Tᴴ) i = ‖T i i‖ ^ 2 * grD G i := by
  have e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))
  rw [grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e,
    Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]

theorem diag_mul_lower {K : Type} [Field K] (S T : Matrix (Fin s) (Fin s) K) (hS : ∀ a b, a < b → S a b = 0)
    (hT : ∀ a b, a < b → T a b = 0) (i : Fin s) : (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hT l i h, mul_zero]
  · rw [hS i l h, zero_mul]

end Lin

theorem green_frame_indep (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H)
    (B : Mat m X.Fn) (hB : B ∈ E.S (genericPoint X.X)) (y : GlobalTheory.CxPts X.str σ)
    (A : Mat m X.Fn) (hA : A ∈ E.S (under y)) (A' : Mat m X.Fn) (hA' : A' ∈ E.S (under y))
    (x : Root m) (f : X.Fn) (hu : UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f)) :
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
      -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  obtain ⟨τ, i⟩ := x
  have hT := (Fr.mem_iff hA).1 hA'
  have hS := (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hV := hT.map_of (ratVal · y) ψ hψ τ
  have hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0 := fun a b h => hV.2.2.2 a b a.2 h
  have hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0 := by
    have h := hV.2.1
    rw [Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
    rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
  have e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i := by
    rw [e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h)
      (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]
  have hu0 := ratVal_ne_zero hu
  have hur : RegAt (under y) ((B * A'⁻¹) τ i i / f) := by
    by_contra h
    exact hu0 (dif_neg h)
  have ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0 := hd i
  have hg := (grD_pos (hH.posDef y A hA τ) i).ne'
  have e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i := by
    rw [hH.trans y A hA A' hA' τ]
    exact grD_conj _ _ hlow hd i
  have n1 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
  have n2 := pow_ne_zero 2 (norm_ne_zero_iff.2 ht)
  dsimp only at n1 ⊢
  rw [e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2,
    Real.log_mul n2 hg]
  ring

end GlobalTheory.LeadingMinorPositivity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBiextensionHypPullbackOfGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.QHypPull

theorem sq_comm {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) {X : Scheme.{0}} (u' : X ⟶ (A' ⊗ A').left)
    (u : X ⟶ (A ⊗ A).left)
    (h1 : u' ≫ (fst A' A').left ≫ φ = u ≫ (fst A A).left) (h2 : u' ≫ (snd A' A').left ≫ φ = u ≫ (snd A A).left) :
    u' ≫ φ₂ = u := by
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, h1]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, h2]

end GlobalTheory.ActFin.QHypPull


open GlobalTheory.ActFin.QHypPull in
theorem GlobalTheory.ActFin.qHyp_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) := by
  intro S S' f A _ _ A' _ φ φ₂ Q h hs hQ
  obtain ⟨hA, hL, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, hsym, hD⟩ := hQ
  haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback S S' A A' f φ h
  have hone : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    rw [GlobalTheory.FlatModel.LiftW.one_left_comp_of_isGrpPullback h A', GlobalTheory.FlatModel.LiftW.one_left_eq,
      GlobalTheory.FlatModel.LiftW.one_left_eq, ← Category.assoc, h.1.w]
    rfl
  have fl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (fst A' A').left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl : ∀ {T : Over S'} (a b : T ⟶ A'), (lift a b).left ≫ (snd A' A').left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have fl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (fst A A).left = a.left := fun a b => by
    rw [← Over.comp_left, lift_fst]
  have sl' : ∀ {T : Over S} (a b : T ⟶ A), (lift a b).left ≫ (snd A A).left = b.left := fun a b => by
    rw [← Over.comp_left, lift_snd]
  have e₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, hone, Category.assoc, fl'])
      (by rw [← Category.assoc, sl, Category.assoc, sl']; rfl)
  have e₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl']; rfl)
      (by rw [← Category.assoc, sl, hone, Category.assoc, sl'])
  have e₃ : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left :=
    sq_comm hs _ _ (by rw [← Category.assoc, fl, Category.assoc, fl', hs.2])
      (by rw [← Category.assoc, sl, Category.assoc, sl', hs.1])
  haveI := hA.proper
  refine ⟨⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
    MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩,
    pull_isLB hL φ₂, ?_, ?_, ?_, ?_⟩
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (1 : A' ⟶ A') (𝟙 A')).left)
      (fun _ => (lift (1 : A ⟶ A) (𝟙 A)).left) (fun _ => 1) φ (fun _ => e₁)) t₁ ht₁
  · exact gen_chartPull (chartPullLinComb Q φ₂ (fun _ : PUnit => (lift (𝟙 A') (1 : A' ⟶ A')).left)
      (fun _ => (lift (𝟙 A) (1 : A ⟶ A)).left) (fun _ => 1) φ (fun _ => e₂)) t₂ ht₂
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q φ₂ φ₂ rfl) (chartPullLinComb Q φ₂
      (fun _ : PUnit => (lift (snd A' A') (fst A' A')).left) (fun _ => (lift (snd A A) (fst A A)).left)
      (fun _ => 1) φ₂ (fun _ => e₃)) hsym
  · exact GlobalTheory.DiagAmpleBC.relAmple_diag_pull S S' A hA Q hL hD f A' φ φ₂ h.1 hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCoordinatesO1FactorialPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdSym

open GlobalTheory.Points GlobalTheory.ProjSpace

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem div_mem_O {o : Type} [CommRing o] {M : RatModel k Ω} {n : ℕ} {h : M.Z ⟶ PSpace o n}
    {c : Fin (n + 1) → Ω} (hc : PCrd (M.pt ≫ h) c) {a : Fin (n + 1)} {z : M.Z}
    (hz : z ∈ h ⁻¹ᵁ ProjSpace.chart o n a) : c a ≠ 0 ∧ ∀ b, c b / c a ∈ M.O z := by
  have hW : ⊤ ≤ M.pt ⁻¹ᵁ (h ⁻¹ᵁ ProjSpace.chart o n a) := M.top_le_preimage_pt ⟨z, hz⟩
  obtain ⟨h0, hv⟩ := _root_.GlobalTheory.UMin.CrdChart.pCrd_chart o Ω n (M.pt ≫ h) c a hc (le_preimage_comp M.pt h le_rfl hW)
  refine ⟨h0, fun b => ?_⟩
  have e : valF M.pt (h ⁻¹ᵁ ProjSpace.chart o n a) (ProjSpace.pullRatio h _ a le_rfl b) = c b / c a :=
    (Points.valR_appLE M.pt h le_rfl hW _).trans (hv b)
  exact e ▸ M.valF_mem_O hz _

theorem valR_pullO1_g {L : Type} [Field L] {X : Scheme.{0}} {o : Type} [CommRing o] {r : ℕ} (y0 : Sp L ⟶ X)
    (π : X ⟶ PSpace o r) {t : Fin (r + 1) → L} (ht : PCrd (y0 ≫ π) t) (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ y0 ⁻¹ᵁ (((ProjSpace.O1 o r).pull π).U i ⊓ ((ProjSpace.O1 o r).pull π).U j)) :
    valR y0 _ (((ProjSpace.O1 o r).pull π).g i j).val = t (j PUnit.unit) / t (i PUnit.unit) := by
  have h1 : ⊤ ≤ (y0 ≫ π) ⁻¹ᵁ (ProjSpace.chart o r (i PUnit.unit) ⊓ ProjSpace.chart o r (j PUnit.unit)) :=
    le_preimage_comp y0 π (inf_le_inf (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) i PUnit.unit)
      (LB.wchart_le (ProjSpace.O1 o r) (fun _ => π) j PUnit.unit)) h
  refine (TuplePoint.valR_linComb_g y0 (ProjSpace.O1 o r) π 1 i j h).trans ((zpow_one _).trans ?_)
  refine (valR_res (y0 ≫ π) inf_le_left h1 (ProjSpace.ratio o r (i PUnit.unit) (j PUnit.unit))).trans ?_
  exact (_root_.GlobalTheory.UMin.CrdChart.pCrd_chart o L r (y0 ≫ π) t _ ht (le_preimage_mono _ inf_le_left h1)).2 _


open Classical in
def unitOf (M : RatModel k Ω) (U : M.Z.Opens) (x : Ω) (hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z) :
    Γ(M.Z, U)ˣ :=
  if hU : (U : Set M.Z).Nonempty then
    Units.map (M.sectionsEquiv U hU).symm.toMonoidHom
      ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩, ⟨x⁻¹, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.2⟩,
        Subtype.ext (mul_inv_cancel₀ (hx _ hU.some_mem).1), Subtype.ext (inv_mul_cancel₀ (hx _ hU.some_mem).1)⟩
  else 1

theorem valR_unitOf {M : RatModel k Ω} {U : M.Z.Opens} {x : Ω} {hx : ∀ z ∈ U, x ≠ 0 ∧ x ∈ M.O z ∧ x⁻¹ ∈ M.O z}
    (h : ⊤ ≤ M.pt ⁻¹ᵁ U) : valR M.pt U (unitOf M U x hx).val = x := by
  have hU : (U : Set M.Z).Nonempty := ⟨_, h (x := IsLocalRing.closedPoint Ω) trivial⟩
  rw [unitOf, dite_eq_left hU]
  have := M.coe_sectionsEquiv U hU ((M.sectionsEquiv U hU).symm ⟨x, RatModel.mem_ringOn.2 fun z hz => (hx z hz).2.1⟩)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UMin.CrdSym
end

namespace GlobalTheory.UMin.CrdSym
open GlobalTheory.Points GlobalTheory.ProjSpace

theorem lbIso_symTup : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (h : M.Z ⟶ PSpace k n) (g : M.Z ⟶ PSpace o n) (c : Fin (n + 1) → Ω), PCrd (M.pt ≫ h) c → PCrd (M.pt ≫ g) (symTup c) → LBIso ((ProjSpace.O1 o n).pull g) (lbPow ((ProjSpace.O1 k n).pull h) (n + 1).factorial) := by
  intro k Ω o _ _ _ _ M n h g c hc he
  set D := (n + 1).factorial
  set L := (ProjSpace.O1 o n).pull g
  set L' := lbPow ((ProjSpace.O1 k n).pull h) D
  have h2 : ∀ a : L'.ι, L'.U a ≤ ((ProjSpace.O1 k n).pull h).U (a PUnit.unit) := fun a =>
    LB.wchart_le ((ProjSpace.O1 k n).pull h) (fun _ => 𝟙 M.Z) a PUnit.unit
  have hL' : ∀ a : L'.ι, L'.U a ≤ h ⁻¹ᵁ ProjSpace.chart k n (a PUnit.unit PUnit.unit) := fun a =>
    (h2 a).trans (LB.wchart_le (ProjSpace.O1 k n) (fun _ => h) _ PUnit.unit)
  have hL : ∀ j : L.ι, L.U j ≤ g ⁻¹ᵁ ProjSpace.chart o n (j PUnit.unit) := fun j =>
    LB.wchart_le (ProjSpace.O1 o n) (fun _ => g) j PUnit.unit
  let x : L'.ι × L.ι → Ω := fun p => symTup c (p.2 PUnit.unit) / c (p.1 PUnit.unit PUnit.unit) ^ D
  have hx : ∀ p : L'.ι × L.ι, ∀ z ∈ (LB.div L' L).U p, x p ≠ 0 ∧ x p ∈ M.O z ∧ (x p)⁻¹ ∈ M.O z := by
    rintro ⟨a, j⟩ z ⟨hza, hzj⟩
    obtain ⟨h1, h3⟩ := div_mem_O hc (hL' a hza)
    obtain ⟨h4, h5⟩ := div_mem_O he (hL j hzj)
    exact _root_.GlobalTheory.UMin.symTup_div_pow_isUnit_of_dvd k Ω (M.O z) (n + 1) c _ _ h1 h3 h4 h5
  have nzh : ∀ a : L'.ι, ⊤ ≤ M.pt ⁻¹ᵁ L'.U a → c (a PUnit.unit PUnit.unit) ≠ 0 := fun a ha =>
    (_root_.GlobalTheory.UMin.CrdChart.pCrd_chart k Ω n (M.pt ≫ h) c _ hc (le_preimage_comp M.pt h (hL' a) ha)).1
  have nzg : ∀ j : L.ι, ⊤ ≤ M.pt ⁻¹ᵁ L.U j → symTup c (j PUnit.unit) ≠ 0 := fun j hj =>
    (_root_.GlobalTheory.UMin.CrdChart.pCrd_chart o Ω n (M.pt ≫ g) (symTup c) _ he (le_preimage_comp M.pt g (hL j) hj)).1
  let w : LB.Iso L L' := ⟨fun p => unitOf M ((LB.div L' L).U p) (x p) (hx p)⟩
  refine ⟨w, ?_⟩
  rintro ⟨a, j⟩ ⟨a', j'⟩
  refine Units.ext (TuplePoint.ext_of_dense M.pt fun hW => ?_)
  have ha := le_preimage_mono M.pt inf_le_left hW
  have hb := le_preimage_mono M.pt inf_le_right hW
  have hk : ⊤ ≤ M.pt ⁻¹ᵁ (L'.U a ⊓ L'.U a') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) hW
  have hj : ⊤ ≤ M.pt ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_preimage_mono M.pt (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) hW
  have e1 := TuplePoint.valR_linComb_g M.pt ((ProjSpace.O1 k n).pull h) (𝟙 M.Z) D a a' hk
  rw [Category.comp_id, valR_pullO1_g M.pt h hc _ _ (le_preimage_mono M.pt (inf_le_inf (h2 a) (h2 a')) hk),
    zpow_natCast] at e1
  have e2 := valR_pullO1_g M.pt g he j j' hj
  have n1 := nzh a (le_preimage_mono M.pt inf_le_left ha)
  have n2 := nzh a' (le_preimage_mono M.pt inf_le_left hb)
  have n3 := nzg j (le_preimage_mono M.pt inf_le_right ha)
  have n4 := nzg j' (le_preimage_mono M.pt inf_le_right hb)
  refine (TuplePoint.valR_res_unit M.pt _ hW _).trans ((valR_unitOf (hx := hx (a, j)) ha).trans (Eq.symm ?_))
  refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
  have eg : valR M.pt _ ((LB.div L' L).g (a, j) (a', j')).val =
      (c (a' PUnit.unit PUnit.unit) / c (a PUnit.unit PUnit.unit)) ^ D *
        (symTup c (j' PUnit.unit) / symTup c (j PUnit.unit))⁻¹ := by
    refine (TuplePoint.valR_mul_unit M.pt hW _ _).trans ?_
    exact congrArg₂ (· * ·) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e1)
      ((TuplePoint.valR_inv_unit M.pt hW _).trans (congrArg (·⁻¹) ((TuplePoint.valR_res_unit M.pt _ hW _).trans e2)))
  rw [eg, TuplePoint.valR_res_unit M.pt _ hW, valR_unitOf (hx := hx (a', j')) hb]
  simp only [x]
  rw [div_pow]
  field_simp

end GlobalTheory.UMin.CrdSym
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_level_over_cyclotomic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  first | (exact @GlobalTheory.HTSympCover.exists_galoisCover) | (exact GlobalTheory.HTSympCover.exists_galoisCover) | (intros; apply GlobalTheory.HTSympCover.exists_galoisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := _root_.GlobalTheory.TInj.PerUnit.monomial_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := _root_.GlobalTheory.TInj.coneval V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := _root_.GlobalTheory.TInj.coneSum_eq ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.scalar_tens | exact GlobalTheory.Mum.TensPol.scalar_tens | (intros; apply GlobalTheory.Mum.TensPol.scalar_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSqStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {φ : V n → V n} {w : V n}, ContDiffAt ℂ 2 φ w → DifferentiableAt ℝ ρ (φ w) → MContDiffAt 2 G₀ (φ w) → IsUnit (G₀ (φ w)).det → MContDiffAt 2 G₁ (φ w) → IsUnit (G₁ (φ w)).det → corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * corrC ρ G₀ G₁ (φ w) := by
  first | exact @GlobalTheory.GoodTop.corrC_comp_holo | exact GlobalTheory.GoodTop.corrC_comp_holo | (intros; apply GlobalTheory.GoodTop.corrC_comp_holo <;> assumption)
end

