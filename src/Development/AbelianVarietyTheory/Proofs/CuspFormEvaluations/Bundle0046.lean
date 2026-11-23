module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightVariableFormula
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionPolynomialExpressionCoeffFieldExtensio
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

set_option autoImplicit false

namespace GlobalTheory.FieldBC

theorem totalDegree_map_inj {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (P : MvPolynomial σ R) :
    (MvPolynomial.map f P).totalDegree = P.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective P hf]

theorem polyNab_fieldBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F : Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree ∧ ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support, algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) * ∏ b, nabBC hle nab y k (F b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab (y.res hle h) k (F b) (colOf m b) := by
  intro E _ _ _ H Dw l Xo c c' hle nab n P S _ inst _ h y k F
  have hinj : Function.Injective (incF c c' hle) := (incF c c' hle).injective
  refine ⟨totalDegree_map_inj _ hinj P, ?_⟩
  have e : inst = GlobalTheory.FieldBC.resAlg hle S := Algebra.algebra_ext _ _ (fun a => (h a).symm)
  subst e
  rw [MvPolynomial.support_map_of_injective P hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_map]
  rfl

end GlobalTheory.FieldBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VSetup

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hcc : ∀ x : E, φ (cc x) = conj (φ x) := fun x => by
    simp [cc, IsCMField.complexEmbedding_complexConj]
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
    simpa using this
  have htw : 2 * (H.w0 : E) = 1 + H.rt := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  have hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg φ hrt
  have hzc : conj (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz' : conj z ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hz]; simp
    have h1 : (conj z - z) * (conj z + z) = 0 := by
      linear_combination hz' - hz
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      have him : z.im = 0 := by
        have := congrArg Complex.im h
        simp at this
        linarith
      have hre := congrArg Complex.re hz
      simp [sq, him] at hre
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [mul_self_nonneg z.re]
    · linear_combination h
  have hw : 2 * φ (H.w0 : E) = 1 + φ (H.rt : E) := by
    have := congrArg φ htw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  have hwc : 2 * conj (φ (H.w0 : E)) = 1 + conj (φ (H.rt : E)) := by
    have := congrArg conj hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  apply φ.injective
  rw [map_add (f := _), map_one, hcc]
  linear_combination (hw + hwc + hzc) / 2

theorem exists_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU hr a n hD k x hx
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := by unfold Dom at hD; exact hD.2
  have hrpq : r = Dw.p + Dw.q := by unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.1
  have hXk : (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0 := by
    unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.2.1 k
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hSD, hMk, -⟩ := _root_.GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hG hU hr W k
  obtain ⟨Dc, hDe, -⟩ := _root_.GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n (U.X k) a W.e hG hrpq hXk.1 hXk.2 hSD hD
  have hper : ∀ y v j, pv (U.X k) Dc.idx y v j = Formalism.L2.PjFree.perFr (U.X k) y v (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2 := by
    intro y v j; rw [← hDe]; exact Dc.per_eq y v j
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = Formalism.L2.PjFree.relab c σ (W.e j).1 := by
    intro j; rw [← hDe]; exact Dc.ty_eq j
  obtain ⟨A, hAm, θ, hAr, hM1⟩ :=
    GlobalTheory.T.analyticFibre_unitFrame_uniformisation E H Dw l Xo c σ r U hG hU hr W k Dc.bas Dc.idx Dc.sympl hper hty x hx
  have hθ := _root_.GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A
    Dc.sympl x.2 hSD θ hAr
  have hw : (H.w0 : E) + cc (H.w0 : E) = 1 := hostHalfRoot_add_conj_eq_one H
  have hint : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD 1
    (stdL E n) (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD v hv x.1 x.2 θ hθ
  have hg : W.g = fdeg E * r := by
    have hc := Fintype.card_congr Dc.idx
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
      ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi] at hc
    exact hc
  exact ⟨W, Dc, A, θ, v, κ, hDe, hg, hw, hSD, hMk, hAm, hAr, hθ, hM1, hv, hκ⟩

end GlobalTheory.Dict.VSetup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab := by
  intro hL E _ _ _ H Dw l Xo c
  classical
  letI : StarRing (𝓞 E) := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hC := _root_.GlobalTheory.ChartRing.exists_chartAt_with_germs hL E H Dw l Xo c hs
  choose C _hT hg using hC
  choose g hg using hg
  let val : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (k : ℤ),
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S :=
    fun S _ _ _ y k => match k with
      | Int.ofNat k => fun F α =>
          (C S y).B.nabVal S (C S y).h H.w0 k (g S y k F) (C S y).uvec (MvPolynomial.monomial α 1)
      | Int.negSucc _ => fun _ _ => 0
  let nab : NabV Xo c := fun {S} _ _ y k F α =>
    if h : Nonempty (Algebra ℚ S) then @val S _ _ h.some y k F α else 0
  refine ⟨inferInstance, nab, hs, ?_⟩
  intro S _ _ iQ y
  refine ⟨C S y, fun k F => ⟨_, hg S y k F⟩, ?_⟩
  intro k F f hf α
  have hne : Nonempty (Algebra ℚ S) := ⟨iQ⟩
  have h1 : nab y k F α = @val S _ _ hne.some y k F α := dif_pos hne
  have h2 : hne.some = iQ := Subsingleton.elim _ _
  refine h1.trans ?_
  rw [h2, isGermFun_holds E H Dw l Xo c S y _ _ _ _ _ k F f _ hf (hg S y k F)]

end GlobalTheory.CanonConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomialsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_integral_basis_harmonicPolynomials : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ (R : ℕ) (b : Fin R → MvPolynomial (LtN Dw n) c.F), (∀ i, b i ∈ harmA (Dw := Dw) c a n) ∧ (∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) ∧ R ≤ Module.finrank ℚ c.F * (1 + DF Dw a) ^ (FD.fdeg E * (Dw.p + Dw.q) * n) ∧ ∀ i (σ : c.F →+* ℂ), l1At σ (b i) ≤ Real.exp (140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a + 2 * FD.fdeg E * (Dw.p + Dw.q : ℕ) * n * L + 4 * Real.log (Module.finrank ℚ c.F) + Real.log |((NumberField.discr c.F : ℤ) : ℝ)| / Module.finrank ℚ c.F) := by
  first | exact @GlobalTheory.HarmBasis.exists_reduced_basis_harmA | exact GlobalTheory.HarmBasis.exists_reduced_basis_harmA | (intros; apply GlobalTheory.HarmBasis.exists_reduced_basis_harmA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfIntegralGeneratorTraceEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem complexConj_rt_eq_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  set u := φ (H.rt : E) with hu
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have him' : u.re * u.im = 0 := by linarith
  have hu0 : u.re = 0 := by
    rcases mul_eq_zero.1 him' with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg u.re]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply Complex.ext
  all_goals simp
  all_goals (rw [← hu]; linarith)

theorem halfIntegralGenerator_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  apply RingOfIntegers.coe_injective
  have h1 := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h1
  have h2 := congrArg (IsCMField.complexConj E) h1
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h2
  have hr : IsCMField.complexConj E (algebraMap (𝓞 E) E H.rt) = -(algebraMap (𝓞 E) E H.rt) :=
    complexConj_rt_eq_neg H
  have hb : algebraMap (𝓞 E) E (H.bar H.w0) = IsCMField.complexConj E (algebraMap (𝓞 E) E H.w0) :=
    H.bar_eq _
  rw [map_add (f := _), map_one]
  linear_combination (h1 + h2) / 2 + hb + hr / 2

theorem univ_finset_fin_two : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

theorem chi_sum_two {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp, univ_finset_fin_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, add_assoc]

theorem chi_prod_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.prod_comp, univ_finset_fin_two,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply, _root_.mul_assoc]

theorem chi_eq_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 ∧ Φ.χ a = Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ a ha
  obtain ⟨⟨wP, hP⟩, hrd⟩ := _root_.GlobalTheory.AnVal.PrimRd.prim_reading E H Dw l Xo c y g ty el Φ
  have hlat : ∀ b ∈ Φ.lat, tyAct ty H.w0 b ∈ Φ.lat := by
    intro b hb
    have := Xo.univ.t.act.hom H.w0
    rw [← Φ.e_ker, Φ.lin, (Φ.e_ker b).2 hb, MonObj.one_comp]
  have hw := hlat a ha
  have htr : ∀ w : Fin g → ℂ, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    have h1 : (H.w0 : E) + ((H.bar H.w0 : 𝓞 E) : E) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) (halfIntegralGenerator_trace_eq_one H)
    funext k
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), h1, map_one, _root_.one_mul]
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛ : ∀ k z, Λ k z = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) k := by
    intro k z
    rcases k with k | I
    · rfl
    · simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
  have hT := _root_.GlobalTheory.AnVal.genRd_const _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr _ _ _ _ wP hP.1 g
    (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol
    (fun z k => by rw [hΛ]; exact (hrd wP hP z).1 k) Φ.span
    (fun gm hgm => ⟨fun z => by simp only [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => by
      rw [hΛ]
      rcases k with k | I
      · exact hgm
      · show psumL 2 g I ![gm, tyAct ty H.w0 gm] ∈ Φ.lat
        simp only [psumL, LinearMap.sum_apply, LinearMap.proj_apply]
        refine AddSubgroup.sum_mem _ fun i _ => ?_
        fin_cases i
        · exact hgm
        · exact hlat gm hgm⟩)
    (fun z w => by
      rw [Fintype.sum_sum_type, Fin.sum_univ_one, chi_sum_two]
      simp [Λ, psumL, cε]
      have hz := semichar_herm_add_left Φ.Hm z (tyAct ty H.w0 z) (w + tyAct ty H.w0 w)
      have hz1 := semichar_herm_add_right Φ.Hm z w (tyAct ty H.w0 w)
      have hz2 := semichar_herm_add_right Φ.Hm (tyAct ty H.w0 z) w (tyAct ty H.w0 w)
      have h0 := semichar_herm_zero_left Φ.Hm (0 : Fin g → ℂ)
      have hadj := Φ.adj H.w0 z w
      have hs := semichar_herm_add_right Φ.Hm z (tyAct ty H.w0 w) (tyAct ty (H.bar H.w0) w)
      rw [htr] at hs
      linear_combination (-1 : ℂ) * hz - hz1 - hz2 - h0 - hadj + hs)
  have hprod := hT.2 a ha
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, chi_prod_two] at hprod
  simp [Λ, psumL, cε] at hprod
  rw [Φ.toAnFr.χ_zero, Φ.toAnFr.χ_add ha hw] at hprod
  have ha0 := Φ.toAnFr.χ_ne_zero ha
  have hw0 := Φ.toAnFr.χ_ne_zero hw
  have hX := Complex.exp_ne_zero (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ))
  have key : Φ.χ a * (Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)))⁻¹ = 1 := by
    rw [← hprod]
    field_simp
    try ring
  have hχ := (mul_inv_eq_one₀ hX).1 key
  obtain ⟨k, hk⟩ := Φ.toAnFr.herm_im_int ha hw
  refine ⟨?_, hχ⟩
  rw [hχ, hk, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast
  ring

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HodgeWeightDominanceCondition
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Classical Matrix

theorem det_gen_ne_zero {K : Type} [Field K] {Ix : Type} {n : ℕ} (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)) h
  rw [RingHom.map_det] at h2
  have : (MvPolynomial.eval (fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)).mapMatrix
      (gen K n t) = 1 := by
    ext1 i j
    simp [gen]
  rw [this] at h2
  simp at h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero t)

theorem cof_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∃ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ (∀ F ∈ VV c.F lam, ∃! P, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧ cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) c.F), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ F ∈ VV c.F lam, cof Dw pl c.F n P = detFac Dw pl c.F a s lam * F → cof Dw pl c.F n (letAct Dw pl c.F g P) = (∏ t, ((g t : Matrix (Fin n) (Fin n) c.F).det) ^ (-(s t))) • (detFac Dw pl c.F a s lam * actP lam g F) := by
  first
  | exact @_root_.GlobalTheory.WeightOrderLemmas.main
  | exact _root_.GlobalTheory.WeightOrderLemmas.main
  | (apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightOrderLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightOrderLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightOrderLemmas.main ..)

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortSeriesValueTwistedEqConjugateValue
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

theorem colSum_eq_of_isNab (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab nab' : NabV Xo c) (h : IsNab Xo c nab) (h' : IsNab Xo c nab') {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : ℤ) (k : ℕ) (hK : K = (k : ℤ))
    (G : Fin n → LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
  subst hK
  exact GlobalTheory.NabUniqCompare.thExprUniqSt_iff_top.1 (Formalism.MainNotions.ModuliIntegralCharts.H1.thExprUniq_of_chartIndep2 hC) E H Dw l Xo c
    nab nab' h h' S y k n G P
    ⟨(GlobalTheory.NabUniqCompare.isHarmonic_iff_cmType c P).2 hP.1, hP.2.1, a, hP.2.2⟩

theorem coeffAutFixesCMConjugatesAndBase_symm {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {l : Level H} {c : Coeff l} {ta : c.F ≃+* c.F} (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => (ta.symm_apply_eq).2 (h.emb τ a).symm, fun a => (ta.symm_apply_eq).2 (h.base a).symm⟩

theorem algebraMap_tw_symm {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (x : K) :
    (algebraMap K (Tw ta.symm S) (ta x)).val = algebraMap K S x := by
  change algebraMap K S (ta.symm (ta x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem shortValAt_conj : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  intro hC E _ _ _ H Dw l Xo c ta h _ nab hnab n a P hP w Λ b N S _ _ y v hv
  obtain ⟨S', i1, i2, φ, y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, hv⟩ := hv
  have h' : Fixes c ta.symm := coeffAutFixesCMConjugatesAndBase_symm h
  have hnab' := GlobalTheory.GalTw.isNab_twist E H Dw l Xo c ta.symm h' nab hnab
  let φ' : S →ₐ[c.F] Tw ta.symm S' :=
    { toRingHom := φ.toRingHom
      commutes' := fun x => by
        have := φ.commutes (ta.symm x)
        change φ (algebraMap c.F S (ta (ta.symm x))) = _ at this
        rw [RingEquiv.apply_symm_apply] at this
        exact this }
  have hinj : Function.Injective (ta : c.F →+* c.F) := ta.injective
  have hsupp : (MvPolynomial.map (ta : c.F →+* c.F) P).support = P.support :=
    MvPolynomial.support_map_of_injective P hinj
  have hdeg : (MvPolynomial.map (ta : c.F →+* c.F) P).totalDegree = P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsupp]
  refine ⟨Tw ta.symm S', inferInstance, inferInstance, φ', twPt h' y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, ?_⟩
  have e1 : (ta b)⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹ = ta (b⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) := by
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  rw [hsupp, hdeg, e1]
  refine hv.trans ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine finsum_congr fun q => ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (colSum_eq_of_isNab hC Xo c _ _ hnab hnab' a P hP S' y' _ (N ^ 2) (Nat.cast_pow N 2).symm (F q i)).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  exact congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm rfl

end GlobalTheory.GalTw
end

