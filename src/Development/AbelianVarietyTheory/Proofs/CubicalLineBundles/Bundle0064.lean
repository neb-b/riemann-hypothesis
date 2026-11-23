module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.abelian₂ Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.FD (Data DataX Frame LamBasis fdeg)
open GlobalTheory.SecTransport GlobalTheory.SecTieEx

namespace GlobalTheory.FramedCMPointCompare

section Bundles

variable {X X' Y : Scheme.{0}}

end Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} {c : Coeff l}

section Letters

variable [StarRing (𝓞 E)] {nΨ n' : ℕ}

variable {o : LamObj c nΨ n'}

end Letters

section Data

variable {Dw : Datum H} {Xo : Moduli Dw l}

end Data

variable {D : D7}

theorem fdeg_host (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

end GlobalTheory.FramedCMPointCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFramedPointOfLieEigenbasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem exists_frPt_of_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (e : (Σ b : E →+* ℂ, Fin (Dw.mult b)) ≃ Fin Φ.T.g) (U : Matrix (Fin Φ.T.g) (Fin Φ.T.g) K) (w : Fin Φ.T.g → (epsR K ⟶ Φ.T.t.G)), x ≫ Xo.s = sOf c K → U.det ≠ 0 → (∀ k, IsLieComb (U k) Φ.v (w k)) → (∀ τ i, IsEigAt c τ ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ)) → ∃ y : FrPt Xo c K, y.x = x ∧ SecTie Φ.m Φ.th y.s ∧ ∀ τ i, y.u τ i = (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo c K _ _ x Φ e U w hx hU hw heig
  have hb : IsLieBasis w :=
    ((GlobalTheory.LieComb.lieComb_algebra K Φ.T.t.G Φ.T.g Φ.v Φ.basis.1).2.2.2.2 U w Φ.basis hw).2 hU.isUnit
  have ht : TanBasis x (fun i => (w i).left ≫ Φ.m.φ) :=
    ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo K x Φ.T.t.G Φ.m.φ Φ.m.cart).2 _ w).1 hb
  have htan : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsTanAt x ((w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) :=
    fun τ i => ht.1 (e ⟨τ, i⟩)
  have hbas := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c K x
    (fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ) Φ.T.g e.symm htan heig).2 (by
      have : (fun j => (w (e ⟨(e.symm j).1, (e.symm j).2⟩)).left ≫ Φ.m.φ) = fun i => (w i).left ≫ Φ.m.φ :=
        funext fun j => congrArg (fun k => (w k).left ≫ Φ.m.φ) (e.apply_symm_apply j)
      exact this ▸ ht)
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x Φ.T.t Φ.m
  obtain ⟨s, hs⟩ := h1 Φ.th
  have hgen : SecGen x s := GlobalTheory.Frames.secGen_of_secNZ GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo K x s
    ((h3 Φ.th s hs).2.2 Φ.th_ne)
  exact ⟨⟨x, hx, fun τ i => (w (e ⟨τ, i⟩)).left ≫ Φ.m.φ, htan, heig, hbas, s, hgen⟩, rfl, hs, fun _ _ => rfl⟩

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem evR_frChg_mul_triangular (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (F : Rul Xo c) (hF : F ∈ sec Xo c a n) (z z' : FrPt Xo c K)
    (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (hT : ∀ b, (T b).BlockTriangular id)
    (hd : ∀ b, (T b).det ≠ 0) (h : FrChg (fun b => (T b).transpose) 1 z z') :
    evR Xo c F z' = (∏ b, ∏ i, T b i i ^ a (b, i)) * evR Xo c F z := by
  have hne : ∀ b i, T b i i ≠ 0 := by
    intro b i
    have h1 := hd b
    rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
  have hb : FrBor t z z' := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z z' z').1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
    exact hT τ hij
  have hw := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 K inferInstance a n F hF
    t z z' hb
  rw [hw]
  congr 1
  simp only [wchar, Fintype.prod_option, Fintype.prod_sigma, t, Formalism.L2.Pj.ex, Units.val_one, one_pow, _root_.one_mul,
    Units.val_mk0]

theorem exists_isFrPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∃ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ _ y a n F hF
  obtain ⟨P, N, hP⟩ := GlobalTheory.LamT.RatFn.exists_poly_div_det E H Dw l Xo c K y a n F hF
  have hrefl : FrMap (AlgHom.id c.F K) y y := GlobalTheory.Frames.frMapUniq_refl y
  have hPK : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr P Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rwa [h2] at h1
  obtain ⟨G, hG⟩ := GlobalTheory.LamT.evalFr_eq_prod_det_pow_mul K (E →+* ℂ) Dw.mult P (fun b i => a (b, i)) N (by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hPK z₁ X hX h₁
    have e₂ := hPK z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := evR_frChg_mul_triangular E H Dw l Xo c K a n F hF z₁ z₂ T hTtri hTd h₂
    have p₁ : (∏ b', ∏ i, T b' i i ^ a (b', i)) = ∏ i, t i i ^ a (b, i) := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [hup, ← e₂, ← e₁, e₃, p₁, p₂]
    simp only [pow_add, Finset.prod_mul_distrib, mul_pow, Finset.prod_pow]
    ring)
  refine ⟨G, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  have h1 := hP S φ z z' Y hY hz hz'
  rw [hG S φ.toRingHom Y] at h1
  have hu : IsUnit ((∏ b, (Y b).det) ^ N) := (IsUnit.prod_univ_iff.2 hY).pow N
  exact hu.mul_left_cancel h1

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMetricDataCmPointComplexEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMMetric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem exists_fibre {K : Type} [Field K] (σ : K →+* ℂ) {x x₀ : Sp K ⟶ Xo.X} (hx : x₀ = x) (Φ : FibKey Xo K x)
    (s : LB.Sec (PPx x₀)) (hs : SecTie Φ.m Φ.th s) (x' : Sp ℂ ⟶ Xo.X) (s' : LB.Sec (PPx x')) (hg : SecGen x' s')
    (hx' : x' = spMap σ ≫ x₀) (hb : SecBC σ 1 x₀ x' s s') (hpq : 1 ≤ Dw.p + Dw.q) :
    ∃ Φ' : FibKey Xo ℂ x', SecTie Φ'.m Φ'.th s' ∧ KeyPB Φ'.key Φ.key σ ∧
      ∀ (e : Φ'.T.g = Φ.T.g) (cf : Fin Φ.T.g → K) (w : epsR K ⟶ Φ.T.t.G), IsLieComb cf Φ.v w →
        ∃ w' : epsR ℂ ⟶ Φ'.T.t.G, IsLieComb (fun i => σ (cf i)) (fun i => Φ'.v (i.cast e.symm)) w' ∧
          w'.left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap σ) ≫ w.left ≫ Φ.m.φ := by
  subst hx
  obtain ⟨Φ₀⟩ := nonempty_fibKey E H Dw l Xo ℂ x' hpq
  obtain ⟨-, t2, t3⟩ := GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ x' Φ₀.T.t Φ₀.m
  obtain ⟨th, hth⟩ := t2 s'
  have hne := (t3 th s' hth).2.1 (secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hg)
  obtain ⟨e, v', hv', hK, hv⟩ := GlobalTheory.LamT.fibKey_keyPB E H Dw l Xo K ℂ σ x₀ x' Φ { Φ₀ with th := th, th_ne := hne } s s' hx' hs hth hb
  refine ⟨{ Φ₀ with th := th, th_ne := hne, v := v', basis := hv' }, hth, hK, fun _ cf w hw => ?_⟩
  have hp := Φ.m.cart.1
  have hc : IsGrpPullback Φ₀.T.t.G Xo.univ.t.G (spMap σ ≫ x₀) Φ₀.m.φ := hx' ▸ Φ₀.m.cart
  have w₁ : Φ₀.m.φ ≫ Xo.univ.t.G.hom = (Φ₀.T.t.G.hom ≫ spMap σ) ≫ x₀ := by rw [hc.1.w, Category.assoc]
  have hF : hp.lift _ _ w₁ ≫ Φ.m.φ = Φ₀.m.φ := hp.lift_fst _ _ _
  have hψ : IsGrpPullback Φ₀.T.t.G Φ.T.t.G (spMap σ) (hp.lift _ _ w₁) :=
    Φ.m.cart.cancel (by rw [hF]; exact hc) (hp.lift_snd _ _ _)
  generalize hp.lift _ _ w₁ = ψ at hF hψ
  have hov : ∀ j : Fin Φ.T.g, IsVecOver σ ψ (Φ.v j) (v' (j.cast e.symm)) := fun j => by
    obtain ⟨a, ha, -⟩ := existsUnique_isVecOver hψ.1 (Φ.v j)
    have : v' (j.cast e.symm) = a := by
      refine Over.OverMorphism.ext (hc.1.hom_ext ?_ ((Over.w _).trans (Over.w a).symm))
      refine (hv _).trans ?_
      rw [← hF, ← Category.assoc a.left, ha, Category.assoc]
      rfl
    rw [this]; exact ha
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hψ.1 w
  refine ⟨w', (lieComb_baseChange K ℂ σ _ _ ψ hψ _ Φ.v w cf _ w' hov hw).1 hw', ?_⟩
  show w'.left ≫ Φ₀.m.φ = _
  rw [← hF, ← Category.assoc, hw', Category.assoc]
  rfl

theorem exists_unif_of_eq (x : KeyIn ℂ) {g : ℕ} (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)) (N : ℝ)
    (h : u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal) :
    ∃ (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ)
      (Fd : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal := by
  subst hg
  exact ⟨u, Hm, χ, θ, Fd, h⟩

theorem exists_unif {K : Type} [Field K] [NumberField K] {x : KeyIn K} {T abelian₂ : MLine K} {σ : K →+* ℂ}
    (h : KeyArchAt x T abelian₂ σ) (x' : KeyIn ℂ) (hx : KeyPB x' x σ) :
    ∃ (u : HolUnif x'.P.A x'.P.L x'.P.g) (Hm : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x'.P.g → ℂ) → ℂ) (Fd : Set (Fin x'.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x'.rig ∧ u.IsFn x'.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      T.n σ ^ 2 = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal := by
  obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hK, hA, hR, hF, -, hD, hN, -⟩ := h
  have hI := GlobalTheory.KeyCancel.keyPB_id_of_keyPB K ℂ σ x x' xσ hx hK
  have hg : x'.P.g = xσ.P.g := by
    obtain ⟨_, _, _, hg, _⟩ := hI
    exact hg
  obtain ⟨u', χ', θ', Fd', a, b, c, d, e, -⟩ := GlobalTheory.KeyTransport.uniformisation_transport xσ x' hI hg _ u Hm χ θ Fd ⟨hA, hR, hF, hD⟩
  exact exists_unif_of_eq x' hg.symm u' _ χ' θ' Fd' _ ⟨a, b, c, d, hN.trans e.symm⟩

theorem form_eq_gram {K : Type} [Field K] [NumberField K] {n : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (s : K →+* ℂ)
    (a b : Fin n → K) :
    star (ReciprocityTheory.MultiplicativeHeights.embVec s a) ⬝ᵥ (h.gram s (fun i => Pi.single i 1)).mulVec (ReciprocityTheory.MultiplicativeHeights.embVec s b) =
      h.form s a b := by
  rw [LieMetric.form_eq_sum_sum, Finset.sum_comm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
    ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_isMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (σ : z.K →+* ℂ) (yσ : FrPt Xo c (CAt (σ.comp (algebraMap c.F z.K)))), FrMap (embAlg σ) z.y yσ → ∃ Hm : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) ℂ, Hm.PosDef ∧ z.LamL.n σ = Real.sqrt Hm.det.re ∧ (∀ j, ReciprocityTheory.MultiplicativeHeights.hq Hm (ReciprocityTheory.MultiplicativeHeights.embVec σ (z.U j)) ≤ (La * (z.ℓ j).n σ) ^ 2) ∧ IsMetric yσ (z.Tl.n σ ^ 2) (gramBlock z.e z.U Hm σ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz σ yσ hy
  obtain ⟨hG, hL, -, hx, hs, hu⟩ := hz
  have hU := GlobalTheory.thetaUnifAV_all
  have hLaw : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hfib : LamF.IsFibreOf z.B.pol z.Φ.key (LamF.gmap z.K) z.m'.φ := hG.2.2.2.1
  have hp : IsPolFibre (algebraMap (𝓞 z.K) z.K) z.B.pol z.Φ.key.P z.m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib
  obtain ⟨h, Hh⟩ := (LieMetric.exists_unique_isHerm hU hLaw z.K z.B.pol
    (GenFib.mk z.Φ.key.P z.m'.φ hp z.Φ.key.v z.Φ.key.basis)).1
  obtain ⟨a₁, a₂⟩ := LamF.gram_stdBasis_posDef_and_hq z.K z.Φ.T.g h σ
  obtain ⟨b₁, b₂⟩ := LamF.lamLen_of_isHerm hU hLaw E H l c _ _ f z.obj La hG z.letters hL hp h Hh σ
  refine ⟨h.gram σ (fun i => Pi.single i 1), a₁, b₁, fun j => (a₂ _).trans_le (b₂ j), ?_⟩
  have hpq : 1 ≤ Dw.p + Dw.q := by
    have e : z.Φ.T.g = f * (Dw.p + Dw.q) := hG.2.2.2.2.2.2.2.2.1
    have := z.Φ.g_pos
    rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | h0
    · rw [h0] at e; omega
    · exact h0
  have harch : KeyArchAt z.Φ.key z.Tl z.LamL σ := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 σ
  obtain ⟨y₁, y₂, pm, y₃, y₄, y₅⟩ := hy
  have hb : GlobalTheory.Frames.SecBC σ 1 z.y.x yσ.x z.y.s yσ.s := ⟨pm, y₃, y₄, fun i hi => by
    have e₁ : scal z.y.x 1 i = 1 := by simp only [scal, Out.liftFun, map_one]
    rw [e₁, _root_.one_mul]
    exact y₅ i hi⟩
  obtain ⟨Φ', ht, hK, hc⟩ := exists_fibre σ hx z.Φ z.y.s hs yσ.x yσ.s yσ.gen y₁ hb hpq
  obtain ⟨u, Hm, χ, θ, Fd, hA, hR, hF, hD, hN⟩ := exists_unif harch Φ'.key hK
  obtain ⟨ψ, e, hψ, hv⟩ := KeyFibre.exists_isPolFibre_of_keyPB _ _ σ _ _ hK
  obtain ⟨-, -, -, -, t1, -, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Φ'.key.P _ u Hm χ hA
  have key : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), ∃ (w₀ : epsR z.K ⟶ z.Φ.T.t.G) (w : epsR ℂ ⟶ Φ'.key.P.A)
      (W : Fin Φ'.key.P.g → ℂ), IsLieComb (z.U (z.e ⟨b, i⟩)) z.Φ.v w₀ ∧ IsVecOver σ ψ w₀ w ∧
      w.left ≫ Φ'.m.φ = yσ.u b i ∧ u.IsDiff W w := fun b i => by
    obtain ⟨w₀, l₀, c₀⟩ := hL.2.2.1 (z.e ⟨b, i⟩)
    obtain ⟨w₁, l₁, c₁⟩ := hu b i
    have e₀ : w₀ = w₁ := by
      refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w w₁).symm))
      unfold LamF.LamLetters.IsLetter at l₀ l₁
      cases hs : z.src (z.e ⟨b, i⟩) with
      | inl q =>
        simp only [hs] at l₀ l₁
        exact l₀.trans l₁.symm
      | inr q =>
        simp only [hs] at l₀ l₁
        exact l₀.trans l₁.symm
    subst e₀
    obtain ⟨w, hw, hw'⟩ := hc e _ w₀ c₀
    have ho : IsVecOver σ ψ w₀ w :=
      (lieComb_baseChange z.K ℂ σ _ _ ψ hψ.2.1 _ z.Φ.v w₀ _ _ w (fun j => hv (j.cast e.symm)) c₀).2 hw
    obtain ⟨W, hW, -⟩ := t1 w (ho.isTangent hψ.2.1 (Reg.isTangent_of_isLieComb z.Φ.basis.1 c₀))
    refine ⟨w₀, w, W, c₀, ho, hw'.trans ?_, hW⟩
    rw [y₂, c₁]
    rfl
  choose w₀ w W k₁ k₂ k₃ k₄ using key
  refine ⟨Φ', u, Hm, χ, θ, Fd, w, W, ht, hA, hR, hF, hD, hN, fun b i => ⟨k₃ b i, k₄ b i⟩, fun b i k => ?_⟩
  refine (form_eq_gram h σ _ _).trans ?_
  exact LieMetric.form_eq_pi_mul_hermForm hU hLaw z.K z.B.pol _ h Hh σ Φ'.key.P ψ u Hm χ hψ hA _ _ _ _ _ _ _ _
    (k₁ b i) (k₁ b k) (k₂ b i) (k₂ b k) (k₄ b i) (k₄ b k)

end GlobalTheory.LamT.CMMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_integral_generator_principal_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → ∃ a : T.Frˣ, ∀ (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (y' : FrPt Xo c T.Fr), FrChg g (a : T.Fr) y y' → SecInt T m1 m2 y'.s := by
  first | exact @GlobalTheory.LamT.LocSec.exists_unit_secInt | exact GlobalTheory.LamT.LocSec.exists_unit_secInt | (intros; apply GlobalTheory.LamT.LocSec.exists_unit_secInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_change_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y y' : FrPt Xo c (CAt σ)) (N : ℝ) (Gr Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) (a : ℂ), a ≠ 0 → FrChg (S := CAt σ) (fun b => (Y b).transpose) a y y' → IsMetric y N Gr → IsMetric y' (‖a‖ ^ 2 * N) (fun b => (Y b).conjTranspose * Gr b * Y b) := by
  first | exact @GlobalTheory.MetricChange.isMetric_frChg | exact GlobalTheory.MetricChange.isMetric_frChg | (intros; apply GlobalTheory.MetricChange.isMetric_frChg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonnegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | exact GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg | (intros; apply GlobalTheory.LamT.evR_mem_range_of_valSet_nonneg <;> assumption)
end

