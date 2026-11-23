module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedNormalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_shifted_normalisation (k : ℕ) (g : GtPtF D F) (z : D.X) (b' : TF (R := R) F ⟶ D.P.A)
    (hb : b' = g.b * cP D _ z)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b') (DegPre.lineε k)), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J := by
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      have a₁ : ∀ χ, jFK (R := R) F ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ => (Category.assoc _ _ _).symm
      have a₂ : jFK (R := R) F ≫ (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left :=
        (Category.assoc _ _ _).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, hb, mul_comm g.b]
      show h (cP D _ z * g.b).left ^ ((k : ℤ) * (-1 : ℤ)) * h (cP D _ z).left ^ ((k : ℤ) * (1 : ℤ)) *
        h g.b.left ^ ((k : ℤ) * (1 : ℤ)) * h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * (-1 : ℤ)) * _ *
        (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h g.b.left ^ (-(k : ℤ))) =
        h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h (cP D _ z * g.b).left ^ (-(k : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (g.s z) k)
      (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi z) k)
        (GeneratorPullback.powGen D.P.L _ _ D.rigK k)) (jFK (R := R) F))) w)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (g.isGen z) k)
      (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (powGen_isGen _ _ _ _ (D.psi_gen z) k)
        (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) k)) _)) hw)
  refine ⟨w', hw', fun Z r x J hJ => ?_⟩
  refine (hv Z r x J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) ((val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (UUA.val_powGen' _ _ _ _ _) (UUA.val_powGen' _ _ _ _ _)))))) rfl))

theorem phi_value_shift (hG : GlobalFnsSt) (k : ℕ) (g h g' : GtPtF D F) (z : D.X)
    (hι : GtPtF.IsIota z h) (ha : GtPtF.IsAdd g h g')
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g'.b) (DegPre.lineε k)))
    (hw' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (x : Z) (J), Good D.P.L x J →
        val w' r x J = val (g.s z) r x J ^ k * (val (D.psi z) (r ≫ jFK (R := R) F) x J ^ k *
          val D.rigK (r ≫ jFK (R := R) F) x J ^ k) * val w r x J)
    (s : Fam D F k) (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (x : T.left) (J)
    (hJ : Good D.P.L x J) :
    sval (s.s (α + k • z)) (ρ ≫ DegPre.trPt D F g.b).left x J *
      (uVal D F k (α + k • z) g.b ρ x J *
        val (LB.mulGen D.P.L _ _ _ _ (g.s (α + k • z)) w) (ρ ≫ fst _ _).left x J).val =
    sval (s.s α) (ρ ≫ DegPre.trPt D F g'.b).left x J *
      (uVal D F k α g'.b ρ x J * val (LB.mulGen D.P.L _ _ _ _ (g'.s α) w') (ρ ≫ fst _ _).left x J).val := by
  have C : IsCub (th D x J) := isCub_cubV D.cub hJ
  have hh : h.b = cP D _ z := hι.1
  have hb : g'.b = g.b * cP D _ z := ha.1.trans (congrArg (g.b * ·) hh)
  obtain ⟨⟨u, hu, hc⟩, hv'⟩ := gen_fe (D := D) (F := F) hG k z α
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe z α u hu hc) _ (ρ ≫ DegPre.trPt D F g.b).left x J hJ
  have htr : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.trPt D F (cP D _ z) = ρ ≫ DegPre.trPt D F g'.b := by
    rw [hb, Category.assoc]
    refine congrArg (ρ ≫ ·) ?_
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, tr_fst, tr_fst]
    · have e₁ : (DegPre.trPt D F g.b ≫ DegPre.trPt D F (cP D _ z)) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [Category.assoc, tr_pr, MonObj.comp_mul, tr_pr, ← Category.assoc, tr_fst]
      have e₂ : DegPre.trPt D F (g.b * cP D _ z) ≫ DegPre.prB D F =
          DegPre.prB D F * (fst _ _ ≫ g.b) * (fst _ _ ≫ cP D _ z) := by
        rw [tr_pr, MonObj.comp_mul, _root_.mul_assoc]
      exact e₁.trans e₂.symm
  have hf : (ρ ≫ DegPre.trPt D F g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, Category.assoc]
  rw [hv' u hu hc _ (ρ ≫ DegPre.trPt D F g.b) x J hJ, trF_eq, ← Over.comp_left, htr, hf] at e
  rw [e, _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) rfl (congrArg Units.val ?_)
  have u1 : uVal D F k α (cP D _ z) (ρ ≫ DegPre.trPt D F g.b) x J =
      hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F g.b), hf, comp_cP]; rfl
  have u2 : uVal D F k (α + k • z) g.b ρ x J =
      hv (th D x J) k (cP D T α * cP D T z ^ k) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, cPoint_nsmul, ← Category.assoc ρ]; rfl
  have u3 : uVal D F k α g'.b ρ x J =
      hv (th D x J) k (cP D T α) (cP D T z * ((ρ ≫ fst _ _) ≫ g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc ρ, hb, MonObj.comp_mul, comp_cP, mul_comm (cP D T z)]; rfl
  have hvc := UUA.hv_comp C k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) (ρ ≫ DegPre.prB D F)
  have h8 : hv (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) =
      cubN (th D x J) k (cP D T α) (cP D T z) ((ρ ≫ fst _ _) ≫ g.b) *
        (th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z))⁻¹ := rfl
  have t1 := gt_nsmul (ρ ≫ fst _ _) hJ g α z k
  have t2 : val (g'.s α) (ρ ≫ fst _ _).left x J * th D x J (cP D T α) ((ρ ≫ fst _ _) ≫ g.b) (cP D T z) =
      val (g.s α) (ρ ≫ fst _ _).left x J * val (D.tau z α) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) x J := by
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D.cub (ρ ≫ fst _ _) hJ _ _ _))).symm.trans
      ((val_corr hJ (ha.2 α) (ρ ≫ fst _ _).left).trans (val_mul hJ _ _ _))
    have e₂ : (ρ ≫ fst _ _) ≫ DegPre.cF D F α = cP D T α := comp_cP D _ α
    have e₃ : (ρ ≫ fst _ _) ≫ h.b = cP D T z := by rw [hh, comp_cP]
    rw [e₂, e₃] at e'
    exact e'.trans (congrArg₂ (· * ·) rfl ((val_corr hJ (hι.2 α) _).trans (val_pull hJ _ _ _)))
  rw [u1, u2, u3, val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen', val_mul hJ, val_mul hJ, hw' _ _ x J hJ]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg Additive.ofMul h8
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 ⊢
  linear_combination (norm := abel) a1 + a2 + a3 - a4

end

theorem phiRel_of_qkEquiv : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, QkPt.Equiv D.toPre F p p' → ∀ w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen → ∃ w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p'.g.b) (DegPre.lineε k)), w'.IsGen ∧ ∀ s t : Fam D.toPre F k, PhiRel D.toPre F k p w s t ↔ PhiRel D.toPre F k p' w' s t := by
  intro hL V _ _ _ D F _ _ k _ p p' ⟨z, hy, h, hι, ha⟩ w hw
  have hG := hL.globalFns
  obtain ⟨w', hw', hv⟩ := exists_shifted_normalisation k p.g z p'.g.b
    (ha.1.trans (congrArg (p.g.b * ·) hι.1)) w hw
  refine ⟨w', hw', fun s t => ?_⟩
  rw [phiRel_iff hG p w hw, phiRel_iff hG p' w' hw']
  constructor
  · intro H α β hβ T ρ x J hJ
    rw [← phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H (α + k • z) β (by rw [← hβ, hy]; abel) T ρ x J hJ
  · intro H α β hβ T ρ x J hJ
    obtain ⟨α, rfl⟩ : ∃ α', α' + k • z = α := ⟨α - k • z, sub_add_cancel _ _⟩
    rw [phi_value_shift hG k p.g h p'.g z hι ha w w' hv s α T ρ x J hJ]
    exact H α β (by rw [← hβ, hy]; abel) T ρ x J hJ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormSubRight
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgNorm

open Formalism.FourierDecayAlt.P.Dx2.DF

section form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem form_add_left (u v w : Fin m → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem form_add_right (u v w : Fin m → ℂ) : herm H w (u + v) = herm H w u + herm H w v := by
  simp only [herm, star_add, add_dotProduct]

theorem form_sub_left (u v w : Fin m → ℂ) : herm H (u - v) w = herm H u w - herm H v w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem form_sub_right (u v w : Fin m → ℂ) : herm H w (u - v) = herm H w u - herm H w v := by
  simp only [herm, star_sub, sub_dotProduct]

theorem form_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H w (c • u) = star c * herm H w u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

end form

variable {k r : ℕ}

theorem inWb_Wb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (Wb v) := by
  intro i hi
  show (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) = 0
  rw [if_neg (by omega)]

theorem split_of_free {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v := by
  funext i
  have hval : ∀ a : Fin r, (eI k r a).val = a.val := fun a => rfl
  have hsum : (∑ a : Fin r, v (eI k r a) • ee k r a) i = if i.val < r then v i else 0 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, ee, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · have hi : i = eI k r ⟨i.val, h⟩ := Fin.ext (hval ⟨i.val, h⟩).symm
      rw [Finset.sum_eq_single ⟨i.val, h⟩]
      · rw [if_pos hi, ← hi]
      · intro b _ hb
        rw [if_neg]
        intro hib
        apply hb
        apply Fin.ext
        show b.val = i.val
        rw [hib, hval]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hib
      apply h
      rw [hib, hval]
      exact b.isLt
  rw [Pi.add_apply, hsum]
  show v i = (if i.val < r then v i else 0) + (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0)
  have hlt := i.isLt
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos ⟨by omega, h2⟩]
    · rw [if_neg (by omega)]
      have hi : i = esI k r ⟨2 * r + k - i.val, by omega⟩ :=
        Fin.ext (by show i.val = 2 * r + k - (2 * r + k - i.val); omega)
      rw [hi]
      exact hv _

theorem form_Wb_right {v w : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (hw : inWb k r w) :
    herm (Hpk k r) (Wb v) w = herm (Hpk k r) v w := by
  conv_rhs => rw [split_of_free hv]
  rw [form_add_left, herm_sum_left]
  simp only [form_smul_left, h_ee_w hw, mul_zero, Finset.sum_const_zero, zero_add]

theorem form_Wb_self {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    herm (Hpk k r) (Wb v) (Wb v) = herm (Hpk k r) v v := by
  rw [form_Wb_right hv (inWb_Wb v)]
  have hs := split_of_free hv
  calc herm (Hpk k r) v (Wb v)
      = herm (Hpk k r) v ((∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v) := by
        rw [form_add_right, herm_sum_right]
        simp [form_smul_right, herm_ee, hv]
    _ = herm (Hpk k r) v v := by rw [← hs]

theorem mul_adj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact mul_eq_one_comm.mp hl

theorem adj_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r) = Dmin k r z z' g ⟨r, by omega⟩ := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have hs : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hs, one_mul]
  rfl

theorem det_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).det = Dmin k r z z' g (Fin.last (r + 1)) := by
  show _ = Matrix.det ((Zhat k r z z' g).submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl))
  rw [Fin.castLE_rfl, Matrix.submatrix_id_id]

private theorem herm_adjoint_mulVec_eq (g : Mx k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ x) y = herm (Hpk k r) x (g *ᵥ y) := by
  unfold herm
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.one_mul,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem omg_norm : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g : Mx k r), inWb k r z → 0 < Tz k r z →
    inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) →
    inWb k r (GlobalTheory.WigSh.omg k r z z' g) ∧ herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) z' = 0 ∧
      (herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) (GlobalTheory.WigSh.omg k r z z' g)).re = Gf k r z z' g / Tz k r z' := by
  intro k r z z' g hz _ hz' hT' hg
  have hTne : (Tz k r z' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hss : herm (Hpk k r) z' z' = -((Tz k r z' : ℝ) : ℂ) := herm_self_alt
  have hsz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := herm_self_alt
  have hs0 : herm (Hpk k r) z' z' ≠ 0 := by rw [hss]; exact neg_ne_zero.mpr hTne
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * r + k + 1) → ℂ,
      u = ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * r + k + 1) → ℂ, v = (Hpk k r * gᴴ * Hpk k r) *ᵥ u := ⟨_, rfl⟩
  have homg : GlobalTheory.WigSh.omg k r z z' g = Formalism.FourierDecayAlt.D.prW k r z' v := by
    rw [hv, hu]; rfl
  have hkey : ∀ b : Fin (r + 1), herm (Hpk k r) v (fvec k r z' b) =
      star ((Zhat k r z z' g).det * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.last r) b) := by
    intro b
    have hsym : ∀ a, herm (Hpk k r) (fvec k r z a) (g *ᵥ fvec k r z' b) = star (Zhat k r z z' g a b) := by
      intro a
      rw [herm_symm']
      rfl
    rw [hv, herm_adjoint_mulVec_eq, hu, herm_sum_left]
    simp only [form_smul_left, hsym, ← star_mul', ← star_sum]
    rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hfree : ∀ a : Fin r, v (esI k r a) = 0 := by
    intro a
    rw [← herm_ee v a, ← fvec_cs z' a, hkey, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', mul_zero,
      star_zero]
  have hlast : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w (Fin.last r) = w := by
    intro w
    simp [fvec]
  have hvz' : herm (Hpk k r) v z' = star (Zhat k r z z' g).det := by
    have h := hkey (Fin.last r)
    rw [hlast, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hWv : herm (Hpk k r) (Wb v) z' = star (Zhat k r z z' g).det := by
    rw [form_Wb_right hfree hz', hvz']
  have hWW : herm (Hpk k r) (Wb v) (Wb v) =
      star ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z z := by
    rw [form_Wb_self hfree, hv, herm_adjoint_mulVec_eq, mulVec_mulVec, mul_adj hg, one_mulVec, hu,
      Fin.sum_univ_castSucc]
    simp only [fvec_cs, hlast]
    simp [herm_sum_left, herm_sum_right, form_add_left, form_add_right, form_smul_left, form_smul_right,
      h_ee_w hz, h_w_ee hz]
    ring
  rw [homg, prW_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, inWb_Wb v i hi, hz' i hi, smul_zero, sub_zero]
  · rw [form_sub_left, form_smul_left, div_mul_cancel₀ _ hs0, sub_self]
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, herm_symm' (Wb v) z', hWv, hWW, hss, hsz]
    unfold Gf
    rw [← det_last, ← adj_last]
    set d := (Zhat k r z z' g).det
    set A := (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)
    have hT'0 : Tz k r z' ≠ 0 := hT'.ne'
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.div_im, Complex.neg_im,
      Complex.normSq_neg, Complex.normSq_ofReal]
    field_simp
    ring

end GlobalTheory.WigSh.OmgNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.FrameExpansion

open Matrix in
private lemma herm_mulVec_invariant {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w := by
  simp only [_root_.Formalism.QuantumDeterminants.herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hH]

open Matrix in
private lemma inWb_of_coords_eq_zero {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ a, v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0) (h2 : ∀ a, v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0) : _root_.Formalism.QuantumDeterminants.inWb k r v := by
  intro i hi
  rcases hi with hi | hi
  · have e : _root_.Formalism.QuantumDeterminants.eI k r ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← e]; exact h1 _
  · have e : _root_.Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i, by omega⟩ = i :=
      Fin.ext (show 2 * r + k - (2 * r + k - (i : ℕ)) = i by omega)
    rw [← e]; exact h2 _

open Matrix in
private lemma herm_bvec_esI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) = v (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_eI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0 :=
  hv _ (Or.inl (show (a : ℕ) < r from a.2))

open Matrix in
private lemma herm_bvec_eI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) = v (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_esI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0 :=
  hv _ (Or.inr (show r + k < 2 * r + k - (a : ℕ) by have := a.2; omega))


open Matrix in
theorem _root_.GlobalTheory.FrameExpansion.frame_expansion_uw_group :
    ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B → (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → w = ∑ c, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w (B c) • B c) ∧ ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → _root_.Formalism.QuantumDeterminants.inWb k r (h *ᵥ w) ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ w) z = 0) ∧ (∀ v w, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w) ∧ h⁻¹ ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 ∧ ∀ h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, h * h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  intro k r z B hz hT hB
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  refine ⟨fun w hw hwz => _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz, ?_⟩
  intro h hh
  have hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r := hh.1
  have hinv := herm_mulVec_invariant hH
  have hfz : h *ᵥ z = z := hh.2.2
  have hdet : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  refine ⟨fun w hw hwz => ⟨?_, ?_⟩, hinv, _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh, mul_nonsing_inv h hdet,
    nonsing_inv_mul h hdet, fun h' hh' => _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh hh'⟩
  · apply inWb_of_coords_eq_zero
    · intro a
      rw [← herm_bvec_esI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).2, hinv, herm_bvec_esI_jet_harmonics]
      exact coord_eI_eq_zero_of_inWb hw a
    · intro a
      rw [← herm_bvec_eI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).1, hinv, herm_bvec_eI_jet_harmonics]
      exact coord_esI_eq_zero_of_inWb hw a
  · rw [← hfz, hinv, hwz]

end GlobalTheory.FrameExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCommMonObjOfDominant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtComm

theorem isCommMonObj_of_dominant {S S' : Scheme.{0}} {f : S' ⟶ S} [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    [Flat A.hom] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
    [IsCommMonObj A'] : IsCommMonObj A := by
  have := ExtUnique.flat_tensorObj A A
  have key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A),
      t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A] := fun T t => by
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [lift_braiding_hom_assoc]
    exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
      ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))
  refine ⟨?_⟩
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_
  exact congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f))
    (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))

end GlobalTheory.SplitExtComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RightOperatorDualMemOfInfiniteStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightOperatorDual_mem_of_infinite : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite → (∀ y ∈ S, rhv d y ∈ K) → ∀ y : ℂ, rhv d y ∈ K := by
  first | exact @GlobalTheory.RhvPoly.rhv_mem_of_infinite | exact GlobalTheory.RhvPoly.rhv_mem_of_infinite | (intros; apply GlobalTheory.RhvPoly.rhv_mem_of_infinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end

