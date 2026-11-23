module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameDenseZ


open Formalism.L2.LamCM GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT in
theorem exists_poly_div_det_secZ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    (e : Ix Dw → ℤ) (F : Rul Xo c) (hF : F ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S)
      (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)),
      (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, hWD, -⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := GlobalTheory.LamT.RatFn.exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [evR_frMap hWD F hF.1 k u (hT _ u) z' hm]
  exact hk

end GlobalTheory.FrameDenseZ

namespace GlobalTheory.FrameDenseZ


open Formalism.L2.LamCM in
theorem exists_frame_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] (m : B → ℕ)
    (P : MvPolynomial (FrVar m) K) (hP : P ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr P Y ≠ 0 := by
  classical
  have hD : ∀ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 := by
    intro b h
    have := GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly (K := K) m b (fun _ => 1)
    rw [h] at this
    simp [evalFr] at this
  have hQ : P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b ≠ 0 :=
    mul_ne_zero hP (Finset.prod_ne_zero_iff.2 fun b _ => hD b)
  obtain ⟨v, hv⟩ : ∃ v : FrVar m → K,
      MvPolynomial.eval v (P * ∏ b, GlobalTheory.LamT.FieldPoly.blockDetPoly K m b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hQ (MvPolynomial.funext fun x => by simp only [h x, map_zero])
  let Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => v ⟨b, (j, i)⟩
  have hY : ∀ R : MvPolynomial (FrVar m) K, evalFr R Y = MvPolynomial.eval v R := fun R => rfl
  rw [map_mul, map_prod] at hv
  refine ⟨Y, fun b => ?_, ?_⟩
  · rw [← GlobalTheory.LamT.FieldPoly.evalFr_blockDetPoly m b Y, hY]
    exact (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hv)) b (Finset.mem_univ b)
  · rw [hY]
    exact left_ne_zero_of_mul hv

theorem exists_frame_evR_ne_zero_of_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K]
    (y : FrPt Xo c K) (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ)
    (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 →
    ∃ y' : FrPt Xo c K, y'.x = y.x ∧ evR Xo c F y' ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y e F hF σ σ₁ w hw hne
  classical
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_secZ E H Dw l Xo c K y e F hF
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hP0 : P ≠ 0 := by
    intro hP0
    haveI : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ :=
      (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e' : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e'
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    have hb : FrBor t z1 z2 := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
      ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩
    have hv := hP _ σ₁ z z1 (fun b => (g b).transpose)
      (fun b => by rw [Matrix.det_transpose]; exact hg b) hz
      (by simpa only [Matrix.transpose_transpose] using h1)
    rw [hP0, map_zero] at hv
    have hz1 : evR Xo c F z1 = 0 := by
      have hdet : (∏ b, ((g b).transpose).det) ^ N ≠ 0 :=
        pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun b _ => by
          rw [Matrix.det_transpose]; exact (hg b).ne_zero)
      have h00 : Formalism.L2.LamCM.evalFr (0 : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) (CAt σ))
          (fun b => (g b).transpose) = 0 := by simp [Formalism.L2.LamCM.evalFr]
      rw [h00] at hv
      exact (mul_eq_zero.1 hv).resolve_left hdet
    apply hne
    rw [GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF (CAt σ) t z1 z2 hb, hz1, mul_zero]
  obtain ⟨Y, hYd, hYv⟩ := exists_frame_evalFr_ne_zero Dw.mult P hP0
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hYd b).isUnit)
  refine ⟨y', hy'.1, fun h0 => hYv ?_⟩
  have hv := hP K (AlgHom.id c.F K) y y' Y (fun b => (hYd b).isUnit)
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K K (AlgHom.id c.F K) y).2.1 hy'
  rw [h0, mul_zero, show (AlgHom.id c.F K).toRingHom = RingHom.id K from rfl, MvPolynomial.map_id] at hv
  exact hv.symm

end GlobalTheory.FrameDenseZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefFromBlocks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl.BlockPos

theorem exists_neg_mul_le {n : Type} [Fintype n] (S : Matrix n n ℝ) :
    ∃ C : ℝ, ∀ x : n → ℝ, -(C * (x ⬝ᵥ x)) ≤ x ⬝ᵥ S *ᵥ x := by
  refine ⟨∑ i, ∑ j, |S i j|, fun x => ?_⟩
  have h : ∀ i, x i * x i ≤ x ⬝ᵥ x := fun i =>
    Finset.single_le_sum (f := fun i => x i * x i) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib, mulVec, dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hi := h i
  have hj := h j
  rw [dotProduct] at hi hj
  rcases abs_cases (S i j) with ⟨e, p⟩ | ⟨e, p⟩ <;> rw [e]
  · nlinarith [mul_nonneg p (sq_nonneg (x i + x j)), mul_le_mul_of_nonneg_left hi p, mul_le_mul_of_nonneg_left hj p]
  · have p' : 0 ≤ -S i j := by linarith
    nlinarith [mul_nonneg p' (sq_nonneg (x i - x j)), mul_le_mul_of_nonneg_left hi p', mul_le_mul_of_nonneg_left hj p']

theorem exists_posDef_fromBlocks {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Y : Matrix m m ℝ} (hY : Y.PosDef) (P : Matrix m n ℝ) {Q B : Matrix n n ℝ} (hQ : Q.IsHermitian) (hB : B.PosDef) :
    ∃ T : ℝ, ∀ t : ℝ, T < t → (fromBlocks Y P Pᴴ (Q + t • B)).PosDef := by
  obtain ⟨c, hc, hcB⟩ := posDef_exists_mul_dotProduct_le hB
  obtain ⟨C, hC⟩ := exists_neg_mul_le (Q - Pᴴ * Y⁻¹ * P)
  have : Invertible Y := (isUnit_iff_isUnit_det Y).mpr (hY.det_pos.ne').isUnit |>.invertible
  refine ⟨max 0 (C / c), fun t ht => ?_⟩
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  have htC : C < t * c := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt ht)
  have hH : (Q + t • B).IsHermitian := hQ.add (hB.smul ht0).1
  refine PosDef.of_dotProduct_mulVec_pos (hY.1.fromBlocks rfl hH) fun x hx => ?_
  rw [← Sum.elim_comp_inl_inr x, dotProduct_mulVec, schur_complement_eq₁₁ P _ _ _ hY.1, ← dotProduct_mulVec,
    ← dotProduct_mulVec]
  by_cases h2 : x ∘ Sum.inr = 0
  · have h1 : x ∘ Sum.inl ≠ 0 := fun h1 => hx (by rw [← Sum.elim_comp_inl_inr x, h1, h2]; simp)
    simpa [h2] using hY.dotProduct_mulVec_pos h1
  · refine add_pos_of_nonneg_of_pos (hY.posSemidef.dotProduct_mulVec_nonneg _) ?_
    have e : Q + t • B - Pᴴ * Y⁻¹ * P = (Q - Pᴴ * Y⁻¹ * P) + t • B := by abel
    rw [e, star_trivial, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
    have a1 := hC (x ∘ Sum.inr)
    have a2 := mul_le_mul_of_nonneg_left (hcB (x ∘ Sum.inr)) ht0.le
    have a3 : 0 < (x ∘ Sum.inr) ⬝ᵥ (x ∘ Sum.inr) := by
      simpa using (dotProduct_star_self_pos_iff (v := x ∘ Sum.inr)).mpr h2
    nlinarith [mul_pos (sub_pos.mpr htC) a3]

theorem full_posDef : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ) (β : N.Form k), ∃ T : ℝ, ∀ w : ℂ, T < w.im →
    (w • bmat bX β).IsSymm ∧ (d.full σ (w • bmat bX β)).IsSymm ∧
      ((d.full σ (w • bmat bX β)).map Complex.im).PosDef := by
  intro N g' r g bX d σ k β
  have hB := (ClassMin.realExtension_posDef_iff _ bX).mp (ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos)
  have hQ : (d.t22.map Complex.im).IsHermitian := by
    ext i j
    simp [d.toricPeriodBlock_isSymm.apply i j]
  obtain ⟨T, hT⟩ := exists_posDef_fromBlocks d.pos (d.t12.map Complex.im) hQ hB
  refine ⟨T, fun w hw => ?_⟩
  have hs : (w • bmat bX β).IsSymm := by
    ext i j
    simp [bmat, β.symm (bX j) (bX i)]
  refine ⟨hs, (IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hs)).submatrix σ, ?_⟩
  convert (hT w.im hw).submatrix σ.injective using 1
  ext i j
  simp only [CD.full, map_apply, submatrix_apply]
  rcases σ i with a | a <;> rcases σ j with b | b <;> simp [bmat, ClassMin.polar_ofIntBilin β.symm]

end GlobalTheory.MBLow.Cl.BlockPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTangentLiftOfModelTangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TanLiftPull

theorem toUnit_left_eq {S : Scheme.{0}} (A : Over S) (f : A ⟶ 𝟙_ (Over S)) : f.left = A.hom := by
  simpa using Over.w f

theorem one_left_eq {S : Scheme.{0}} (A : Over S) (G : Over S) [GrpObj G] :
    (1 : A ⟶ G).left = A.hom ≫ η[G].left := by
  rw [← toUnit_left_eq A (toUnit A)]
  rfl

theorem exists_isTan_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), ∃ w : epsOver V V ⟶ G.G, IsTan w ∧ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ v
  have hpb : IsPullback ψ.φ G.G.hom Y.t.G.hom x := ψ.cart.1
  have hsq : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ Y.t.G.hom = (epsOver V V).hom ≫ x := by
    rw [Over.w]; rfl
  have hfa : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) = 𝟙 _ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of V)
    ext a
    simp
  refine ⟨Over.homMk (hpb.lift _ _ hsq) (hpb.lift_snd _ _ _), ?_, (hpb.lift_fst _ _ _).symm⟩
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ hpb.lift _ _ hsq = (1 : ptOver V V ⟶ G.G).left
  apply hpb.hom_ext
  · rw [Category.assoc, hpb.lift_fst]
    have h1 := congrArg (fun f => f.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
    simp only [smT_left] at h1
    have key : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (epsMul (0 : V)) =
        spMap (TrivSqZeroExt.fstHom V V V).toRingHom := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext <;> simp [epsMul]
    have hunit : η[G.G].left ≫ ψ.φ = x ≫ η[Y.t.G].left := by
      have h := ψ.cm.e_comm
      rw [ψ.base] at h
      exact h
    rw [← key, Category.assoc, h1, one_left_eq, one_left_eq, Category.assoc, hunit]
    simp only [Over.mk_hom, ← Category.assoc, hfa]
    simp [spMap]
  · rw [Category.assoc, hpb.lift_snd, Over.w]
    simp only [Over.mk_hom]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end GlobalTheory.TanLiftPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowEval

noncomputable def absConv (u : ℂ) : Subring (PowerSeries ℂ) where
  carrier := {Φ | Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖}
  zero_mem' := by simp
  one_mem' := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp [PowerSeries.coeff_one, Finset.notMem_singleton.1 hn]
  add_mem' := by
    intro f g hf hg
    refine (Summable.add hf hg).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    rw [map_add (f := _), add_mul]
    exact norm_add_le _ _
  neg_mem' := by
    intro f hf
    simpa [map_neg, neg_mul, norm_neg] using hf
  mul_mem' := by
    intro f g hf hg
    have e : ∀ n, PowerSeries.coeff n (f * g) * u ^ n = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * u ^ kl.1) * (PowerSeries.coeff kl.2 g * u ^ kl.2) := fun n => by
      rw [PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl h => ?_
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
      ring
    show Summable fun n => ‖PowerSeries.coeff n (f * g) * u ^ n‖
    simp only [e]
    exact summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => PowerSeries.coeff n f * u ^ n) (g := fun n => PowerSeries.coeff n g * u ^ n) hf hg

noncomputable def evalAt (u : ℂ) : absConv u →+* ℂ where
  toFun Φ := ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
    simp
  map_zero' := by simp
  map_add' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    simp only [Subring.coe_add, map_add (f := _), add_mul]
    exact hf.of_norm.tsum_add hg.of_norm
  map_mul' := by
    intro f g
    have hf : Summable fun n => ‖PowerSeries.coeff n (f : PowerSeries ℂ) * u ^ n‖ := f.2
    have hg : Summable fun n => ‖PowerSeries.coeff n (g : PowerSeries ℂ) * u ^ n‖ := g.2
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
    refine tsum_congr fun n => ?_
    simp only [Subring.coe_mul]
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl h => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 h, pow_add]
    ring

theorem countable_closure {A : Type} [CommRing A] (S : Set A) (hS : S.Countable) :
    Countable (Subring.closure S) := by
  have : Countable S := hS.to_subtype
  have : Countable (MvPolynomial S ℤ) :=
    (MvPolynomial.basisMonomials S ℤ).repr.injective.countable
  let φ : MvPolynomial S ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) Subtype.val
  have hle : Subring.closure S ≤ φ.range := Subring.closure_le.2 fun s hs =>
    ⟨MvPolynomial.X ⟨s, hs⟩, by simp [φ]⟩
  have hc : (φ.range : Set A).Countable := by
    rw [RingHom.coe_range]; exact Set.countable_range _
  exact (hc.mono hle).to_subtype

theorem radius_ge (ε : ℝ) (Φ : PowerSeries ℂ)
    (h : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) :
    ENNReal.ofReal ε ≤ (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrε : (r : ℝ) < ε := by
    rw [← ENNReal.ofReal_coe_nnreal] at hr
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
  refine FormalMultilinearSeries.le_radius_of_summable _ ?_
  have hs := h (r : ℂ) (by exact_mod_cast hr0) (by simpa using hrε)
  refine hs.congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow]
  simp

end GlobalTheory.PowEval


open GlobalTheory.PowEval in
theorem GlobalTheory.exists_injective_evalAt_closure : ∀ (ε : ℝ) (S : Set (PowerSeries ℂ)), 0 < ε → S.Countable → (∀ Φ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖) → ∃ (u : ℂ) (i : Subring.closure S →+* ℂ), u ≠ 0 ∧ ‖u‖ < ε ∧ Function.Injective i ∧ ∀ Φ : Subring.closure S, i Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries ℂ) * u ^ n := by
  intro ε S hε hS h
  have : Countable (Subring.closure S) := countable_closure S hS
  let p : PowerSeries ℂ → FormalMultilinearSeries ℂ ℂ ℂ := fun Φ =>
    FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n Φ
  have hsum : ∀ (Φ : PowerSeries ℂ) (u : ℂ), (p Φ).sum u = ∑' n, PowerSeries.coeff n Φ * u ^ n := by
    intro Φ u
    show FormalMultilinearSeries.ofScalarsSum _ u = _
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    simp [smul_eq_mul]
  have hcl : ∀ Φ ∈ Subring.closure S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      Summable fun n => ‖PowerSeries.coeff n Φ * u ^ n‖ := by
    intro Φ hΦ u hu0 hu
    have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hu
    exact hle hΦ
  have hrad : ∀ Φ ∈ Subring.closure S, ENNReal.ofReal ε ≤ (p Φ).radius := fun Φ hΦ =>
    radius_ge ε Φ (hcl Φ hΦ)
  have hpos : ∀ Φ ∈ Subring.closure S, 0 < (p Φ).radius := fun Φ hΦ =>
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) (hrad Φ hΦ)
  have hball : ∀ Φ ∈ Subring.closure S, Metric.ball (0 : ℂ) ε ⊆ Metric.eball 0 (p Φ).radius := by
    intro Φ hΦ
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball (hrad Φ hΦ)
  let J := Option {Φ : Subring.closure S // Φ ≠ 0}
  let f : J → ℂ → ℂ := fun i => match i with
    | none => id
    | some Φ => (p (Φ.1 : PowerSeries ℂ)).sum
  have han : ∀ i, AnalyticOnNhd ℂ (f i) (Metric.ball 0 ε) := by
    intro i
    cases i with
    | none => exact analyticOnNhd_id
    | some Φ =>
      exact ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).analyticOnNhd.mono (hball _ Φ.1.2)
  have hnz : ∀ i, ∃ x ∈ Metric.ball (0 : ℂ) ε, f i x ≠ 0 := by
    intro i
    cases i with
    | none =>
      refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · show ((ε / 2 : ℝ) : ℂ) ≠ 0
        exact_mod_cast (by linarith : ε / 2 ≠ 0)
    | some Φ =>
      by_contra hcon
      push Not at hcon
      have hev : (p (Φ.1 : PowerSeries ℂ)).sum =ᶠ[nhds 0] 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy
        exact hcon y hy
      have h0 := ((p _).hasFPowerSeriesOnBall (hpos _ Φ.1.2)).hasFPowerSeriesAt.eq_zero_of_eventually hev
      apply Φ.2
      apply Subtype.ext
      ext n
      have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n) h0
      simpa using (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := fun n => PowerSeries.coeff n (Φ.1 : PowerSeries ℂ)) n).1 this
  obtain ⟨u, hu, hx⟩ := GlobalTheory.exists_forall_ne_zero_of_countable_analytic ℂ (Metric.ball 0 ε)
    Metric.isOpen_ball (convex_ball 0 ε).isPreconnected (Metric.nonempty_ball.2 hε) J f han hnz
  have hu0 : u ≠ 0 := hx none
  have hun : ‖u‖ < ε := mem_ball_zero_iff.1 hu
  have hle : Subring.closure S ≤ absConv u := Subring.closure_le.2 fun Ψ hΨ => h Ψ hΨ u hu0 hun
  let i : Subring.closure S →+* ℂ := (evalAt u).comp (Subring.inclusion hle)
  refine ⟨u, i, hu0, hun, ?_, fun Φ => rfl⟩
  refine (injective_iff_map_eq_zero i).2 fun Φ hΦ => ?_
  by_contra hne
  apply hx (some ⟨Φ, hne⟩)
  show (p (Φ : PowerSeries ℂ)).sum u = 0
  rw [hsum]
  exact hΦ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring <;> assumption)
end

