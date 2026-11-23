module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1775
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditions
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesDefiniteLiftIndex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq


open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in
theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem archOne_congr {X X' : Data E r} (hX : X = X') {L Fp : Wt X.Ψ r} {L' Fp' : Wt X'.Ψ r} {T : ℕ}
    (hL : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, L ⟨τ, h1⟩ a = L' ⟨τ, h2⟩ a)
    (hF : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, Fp ⟨τ, h1⟩ a = Fp' ⟨τ, h2⟩ a) (h : ArchOne X' L' Fp' T) :
    ArchOne X L Fp T := by
  subst hX
  have e1 : L = L' := funext fun τ => funext fun a => hL τ.1 τ.2 τ.2 a
  have e2 : Fp = Fp' := funext fun τ => funext fun a => hF τ.1 τ.2 τ.2 a
  subst e1 e2
  exact h

theorem archOn_of_comps {U C K : Type} [Group U] [MulAction U C] [Nonempty C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r)
    (X : K → Data E r) (e : C ≃ K) (hX : ∀ c, (M.comp c).toData = X (e c)) (lK lL lF : ∀ k, Wt (X k).Ψ r) (T n : ℕ)
    (hn : n = M.dimY)
    (hka : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = lK (e c) ⟨τ, h2⟩ a)
    (hsum : ∀ k, lK k = lF k + T • lL k)
    (hLi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lL k ⟨τ, h⟩ a = lL k' ⟨τ, h'⟩ a)
    (hFi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lF k ⟨τ, h⟩ a = lF k' ⟨τ, h'⟩ a)
    (hW : ∀ k, GapsGe (X k).p0 (lL k) 1 ∧ PairGe (lL k) (1.9 * T) ∧
      GapsGe (X k).p0 (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 0 ∧ PairGe (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 1)
    (hA : ∀ k, ArchOne (X k) (lL k) (lF k) T) : ArchOn M ka T := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hΨ : ∀ c, (X (e c)).Ψ = M.Ψ := fun c => (congrArg Data.Ψ (hX c)).symm.trans (M.comp_Ψ c)
  have hp : ∀ c, (X (e c)).p0 = M.p0 := fun c => (congrArg Data.p0 (hX c)).symm.trans (M.comp_basePoint c)
  have mem : ∀ c τ, τ ∈ M.Ψ → τ ∈ (X (e c)).Ψ := fun c τ h => (hΨ c).symm ▸ h
  let L : Wt M.Ψ r := fun τ a => lL (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  let Fp : Wt M.Ψ r := fun τ a => lF (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  have hW0 := hW (e c0)
  rw [hp c0, hn] at hW0
  obtain ⟨w1, w2, w3, w4⟩ := hW0
  refine ⟨L, Fp, ?_, fun τ a b h1 h2 => w1 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w2 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun τ a b h1 h2 => w3 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w4 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun c => ?_⟩
  · funext τ a
    rw [hka c0 τ.1 τ.2 (mem c0 τ.1 τ.2) a, hsum]
    rfl
  · refine archOne_congr (hX c) (fun τ h1 h2 a => ?_) (fun τ h1 h2 a => ?_) (hA (e c))
    · exact hLi (e c0) (e c) τ _ h2 a
    · exact hFi (e c0) (e c) τ _ h2 a

end Model

section Run

theorem row_pair {r p q : ℕ} (hpq : p + q = r) (Dm nL nF : ℤ) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) = r - 1)
    (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L b) -
      (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L a) := by
  have hq1 : q ≤ (b : ℕ) := by omega
  have hq2 : ¬ q ≤ (a : ℕ) := by omega
  have e1 : (a : ℤ) = 0 := by omega
  have e2 : (b : ℤ) = r - 1 := by omega
  have e3 : (r : ℤ) = p + q := by omega
  rw [hL a, hL b, hF a, hF b, e1, e2]
  simp only [if_pos hq1, if_neg hq2]
  rw [show (b : ℕ) - q = p - 1 by omega, show q - 1 - (a : ℕ) = q - 1 by omega]
  nlinarith

theorem expand_weight {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (F L : Wt Ψ r)
    (n : ℕ) (τ : Ψ) (c : Fin r) :
    (F - kLog Ψ r - (n + 2) • L) τ c = F τ c - (2 * (c : ℤ) - ((r : ℤ) - 1)) - ((n : ℤ) + 2) * L τ c := by
  show F τ c - kLog Ψ r τ c - ((n + 2) • L τ c) = _
  rw [nsmul_eq_mul]
  simp only [kLog]
  push_cast
  ring


set_option maxHeartbeats 1000000 in
theorem run_weight_arch (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hP : FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0) (hjm : j < D.R.m)
    (k : (T.U j T.σ₀).Comp) :
    GapsGe ((T.U j T.σ₀).X k).p0 (laR T j wL k) 1 ∧ PairGe (laR T j wL k) (1.9 * Tn) ∧
      GapsGe ((T.U j T.σ₀).X k).p0
        (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 0 ∧
      PairGe (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 1 := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : 0 < (D.R.sigW j).2 := by show 0 < D.R.m - j; omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    show D.R.k + j - 1 + (D.R.m - j) = D.R.k + D.R.m - 1; omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := GlobalTheory.RunWeightDom.block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    have bM := GlobalTheory.RunWeightDom.block hq (ka.aM (tt τ)) (wL.aM (tt τ)) (wF.aM (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      0 (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' (Int.natCast_nonneg _)
      (fun i hi => by have := g2 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM (tt τ) i : ℝ) := by have := h7 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.2 (tt τ) i; rwa [hTp, ← sub_zero (ka.aM (tt τ) i : ℤ)] at this) (hF.2.2 (tt τ))
    rw [hn] at bP
    exact And.intro (GlobalTheory.RunWeightDom.row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) _ _ _ _ (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      bM.1 bM.2.1 bM.2.2.1 bM.2.2.2)
      (row_pair hpq (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
        (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
        (laR T j wL k τ) (laR T j wF k τ) (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.2.2.2 bM.2.2.2)
  rw [← hp0] at key hq
  have hq' : ((T.U j T.σ₀).X k).p0 < D.R.r := by omega
  have e : ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (c : Fin D.R.r),
      (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) τ c =
        laR T j wF k τ c - (2 * (c : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ c := by
    intro τ c
    exact expand_weight _ _ _ τ c
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, fun τ a b hab hb => ?_, fun τ a b ha hb => ?_⟩
  · obtain ⟨⟨k1, k2, -, -, -⟩, -⟩ := key τ
    have hab' : (a : ℕ) < b := by omega
    by_cases hc : (b : ℕ) < ((T.U j T.σ₀).X k).p0
    · have := k1 a b hab' hc; omega
    · have := k2 a b (by omega) hab'; omega
  · obtain ⟨⟨-, -, -, k4, -⟩, -⟩ := key τ
    have := k4 a b (by omega) (by omega)
    have h' : (19 : ℝ) * Tn ≤ 10 * ((laR T j wL k τ b - laR T j wL k τ a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · obtain ⟨⟨-, -, k3, -, -⟩, -⟩ := key τ
    have := k3 a b hab hb
    rw [e τ a, e τ b]
    linarith
  · obtain ⟨-, k5⟩ := key τ
    have := k5 a b ha hb hp hq
    rw [e τ a, e τ b]
    have h1 : (1 : ℤ) ≤ (laR T j wF k τ b - (2 * (b : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ b) -
      (laR T j wF k τ a - (2 * (a : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ a) := this
    exact_mod_cast h1

theorem archOne_of_run (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hpar : ParOK T EX p j) (hpg : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hC : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus)
    (hjm : j < D.R.m) :
    ∀ k : (T.U j T.σ₀).Comp, ArchOne ((T.U j T.σ₀).X k) (GlobalTheory.Shares.laR T j wL k) (GlobalTheory.Shares.laR T j wF k) Tn := by
  obtain ⟨G, hG⟩ := GlobalTheory.RunJoin.exists_genOK D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar.orient hpg
  obtain ⟨i, et, he⟩ := GlobalTheory.EtaBoundForm.exists_etaOK D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpg hjm
  let G' := FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  have hG' : GenOK h j hj large₂ G' _ _ := genOK_refill h j hj large₂ G _ _ hG G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  obtain ⟨A⟩ := GlobalTheory.RunJoin.archAt_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ nus hpar hpg hC hjm G' hG' he
  obtain ⟨t, -, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj _ wL wF G'.w Tn _ A
  intro k
  exact ⟨A.Xa k, A.hL k, A.hF k, A.hT k, A.mar k, ⟨Fl.Fl k⟩⟩

end Run

section Point

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Point

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

variable {X Y : Scheme.{0}} (L : LB X) {k k' : ℕ}

abbrev secChart (i : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) i

def SecRatioEq (u v : Y ⟶ X) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k') : Prop :=
  ∀ i i' : Fin 1 → L.ι,
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₁.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₂.f i')) =
    (Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
        ((u.app (secChart L i)).hom (s₂.f i)) *
      (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
        ((v.app (secChart L i')).hom (t₁.f i'))

def SecCoNonzero (u v : Y ⟶ X) (s : H0 L k) (t : H0 L k') : Prop :=
  ∃ (y : Y) (i i' : Fin 1 → L.ι), y ∈ Y.basicOpen ((u.app (secChart L i)).hom (s.f i)) ∧
    y ∈ Y.basicOpen ((v.app (secChart L i')).hom (t.f i'))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMonoOfHeightNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem selfInter_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hC k _ Y _ p D hX A B α β hle hnef hα hβ
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![A, B]).1
  have hpos := _root_.GlobalTheory.HSNef.mixed_diff_nonneg hC k Y p D hX A B Φ hΦ hle
  have hmono := GlobalTheory.monotone_form_along_segment D Φ fun x y => hpos x y (hnef x y)
  have hd := ((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1
  have h0 : Φ (MvPolynomial.X 0 ^ (D + 1)) = α := HermLB.IsSelfInter.unique hX (hd 0) hα
  have h1 : Φ (MvPolynomial.X 1 ^ (D + 1)) = β := HermLB.IsSelfInter.unique hX (hd 1) hβ
  rw [← h0, ← h1]
  exact hmono

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegMin

theorem exists_semiAbelian_idempotent_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  intro S G _ _ hG e he hee
  obtain ⟨H, hgrp, _, i, r, hH, hi, hr, hir, hri⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image S G hG e he hee
  exact ⟨H, hgrp, i, r, hi, hr, hir, hri, hH⟩

end GlobalTheory.SiegMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genericEnd_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  intro R _ _ _ hR G _ _ hG f hf
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  haveI := hN
  haveI := hIC
  haveI := hf
  obtain ⟨g, ⟨hg, hg'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG f
  exact ⟨g, hg, hg'⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocalInj

theorem base_to_stalk_injective : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, Function.Injective ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) := by
  intro R' _ _ _ _ G₁ _ _ hG x
  haveI : Smooth G₁.hom := hG.smooth
  haveI : Flat G₁.hom := inferInstance

  have hst : Function.Injective (G₁.hom.stalkMap x).hom := by
    have h := Flat.stalkMap G₁.hom x
    letI := (G₁.hom.stalkMap x).hom.toAlgebra
    haveI : Module.Flat ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x) := h
    have : IsLocalHom (algebraMap ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (G₁.hom.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp R').presheaf.stalk (G₁.hom x))
      (B := G₁.left.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)

  have hgerm : Function.Injective ((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom := by
    have hU := isAffineOpen_top (Sp R')
    let _ := (Sp R').presheaf.algebra_section_stalk (U := ⊤) ⟨G₁.hom x, trivial⟩
    have := hU.isLocalization_stalk ⟨G₁.hom x, trivial⟩
    haveI : IsDomain Γ(Sp R', ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance
    exact IsLocalization.injective (M := (hU.primeIdealOf ⟨G₁.hom x, trivial⟩).asIdeal.primeCompl)
      (S := (Sp R').presheaf.stalk ((⟨G₁.hom x, trivial⟩ : (⊤ : (Sp R').Opens)) : Sp R'))
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hiso : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).1
  have e : ⇑((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) =
      ⇑(G₁.hom.stalkMap x).hom ∘ ⇑((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom ∘
        ⇑(Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom := by
    funext a
    exact (Scheme.Hom.germ_stalkMap_apply G₁.hom ⊤ x trivial _).symm
  rw [e]
  exact hst.comp (hgerm.comp hiso)

end GlobalTheory.Mum.LocalInj
end

