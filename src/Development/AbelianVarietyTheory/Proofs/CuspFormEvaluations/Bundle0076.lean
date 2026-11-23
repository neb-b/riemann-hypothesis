module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0031
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0030
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0023
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspReadingsLinearIndependent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem cusp_readings_linearIndependent : ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt := by
  set_option synthInstance.maxHeartbeats 200000 in
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt
  intro D T h j hj ka σ hσ m f hf
  have hlin := hf.map' (T.C j ka).subtype (T.C j ka).ker_subtype
  have hmem : ∀ i, (f i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun i =>
    Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n (f i).2
  have hU := h.unf j hj σ hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have key := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
    (wtA ka) ka.n).1 m (fun i => (f i : T.R j)) hmem hlin
  simp only [Formalism.L2.PjFree.rdU_ofPj] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartFree

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped ComplexConjugate
open Matrix

theorem embeddings_differ_on_integer {E : Type} [Field E] [NumberField E] (τ τ' : E →+* ℂ) (h : τ ≠ τ') :
    ∃ a : 𝓞 E, τ (a : E) ≠ τ' (a : E) := by
  by_contra hall
  push Not at hall
  apply h
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [map_div₀]
  rw [show (algebraMap (𝓞 E) E a) = (a : E) from rfl, show (algebraMap (𝓞 E) E b) = (b : E) from rfl,
    hall a, hall b]

theorem balanced_pairs_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ} (A : 𝓞 E → Matrix (Fin d) (Fin d) S)
    (uvec : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin d), ∑ j, A a i j * uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * uvec ℓ i)
    (M : Fin d → Fin d → S) (hbal : ∀ a, (A a).transpose * Matrix.of M = Matrix.of M * A (H.bar a))
    (ℓ ℓ' : Lt1 Dw) (hne : ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j ≠ 0) :
    ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  by_contra hc
  have hσ : ℓ.1 ≠ ComplexEmbedding.conjugate ℓ'.1 := by
    intro h
    apply hc
    rw [h]
    show ℓ'.1 = star (star ℓ'.1)
    rw [star_star]
  obtain ⟨a, ha⟩ := embeddings_differ_on_integer _ _ hσ
  have hmv : ∀ (b : 𝓞 E) (ℓ₀ : Lt1 Dw), A b *ᵥ uvec ℓ₀ = algebraMap c.F S (embK c ℓ₀.1 b) • uvec ℓ₀ := by
    intro b ℓ₀
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact heig b ℓ₀ i
  set B := uvec ℓ ⬝ᵥ (Matrix.of M *ᵥ uvec ℓ') with hB
  have hBe : B = ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j := by
    rw [hB]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) S => uvec ℓ ⬝ᵥ (N *ᵥ uvec ℓ')) (hbal a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hmv,
    hmv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← hB] at h1
  have key : (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) * B = 0 := by
    rw [sub_mul, h1, sub_self]
  have hu : IsUnit (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) := by
    rw [← map_sub]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    apply ha
    have h2 := congrArg (fun x : c.F => (x : ℂ)) (sub_eq_zero.1 h0)
    simp only [embK_coe] at h2
    rw [h2, H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  exact hne (hBe ▸ (hu.mul_right_eq_zero).1 key)

theorem twist_on_eigenDirections (hFix : FrTruncFixSt) (hLE : LinEigSt) : FrTruncFixBSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
  obtain ⟨e', hfr, hrig, cc, hT, h0, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hs S y C
  exact ⟨e', hfr, hrig, cc, hT, h0, hsym, fun m ℓ ℓ' hne => balanced_pairs_conjugate c (fun a => dLin (C.B.A.act a)) C.uvec
    (fun a ℓ i => hLE E H Dw l Xo c S y C a ℓ i) (cc m) (hbal m) ℓ ℓ' hne, hu⟩

theorem eigenDirections : LinEigSt := GlobalTheory.EigDir.linEig_holds

theorem chartIndep_of_globalFns (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  have hAct := expActOf_of eigenDirections
  chartIndep2_verb
    (chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) (killAddVal_of fun _ _ _ _ H => psiCover_holds H))
    (twist_on_eigenDirections (frTruncFix_of frRatio_holds) eigenDirections) germFix_holds (harmInv_of hAct)

theorem chartIndep : ChartIndepSt2 :=
  chartIndep_of_globalFns GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.ChartFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom
section
noncomputable section

namespace GlobalTheory.FiniteOrderRule

open Formalism.L2.Pj

theorem eq_zero_of_forall_algHom {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R]
    [Algebra.FiniteType K R] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (x : R)
    (h : ∀ φ : R →ₐ[K] Ω, φ x = 0) : x = 0 := by
  have hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hb : (⊥ : Ideal R).jacobson = ⊥ := hJ.out (Ideal.isRadical_bot)
  rw [← Ideal.mem_bot, ← hb, Ideal.jacobson, Ideal.mem_sInf]
  rintro J ⟨-, hM⟩
  letI := Ideal.Quotient.field J
  haveI : Module.Finite K (R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ J)
  let ψ : (R ⧸ J) →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h0 := h (ψ.comp (Ideal.Quotient.mkₐ K J))
  have h1 : Ideal.Quotient.mk J x = 0 := by
    apply ψ.toRingHom.injective
    rw [map_zero]
    exact h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem pow_eq_one_of_complex {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR)
    (hB : ∀ (S : Type) [CommRing S] [Algebra K S] (T : Type) [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
      (y : pts S), ∃ z : pts T, mapR φ y z)
    (σ : K →+* ℂ) (f : Rules pts) (hf : IsNatural pts mapR f) (k : ℕ)
    (h : ∀ y : pts (CAt σ), evalAt pts mapR f y ^ k = 1) (p : TRing K) (y : pts p.R) : f p y ^ k = 1 := by
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  rw [← sub_eq_zero]
  letI : Algebra K ℂ := σ.toAlgebra
  refine eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ ?_
  intro φ
  let φ' : p.R →ₐ[K] CAt σ := φ
  obtain ⟨z, hz⟩ := hB p.R (CAt σ) φ' y
  have hT : FromTest pts mapR z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evalAt at h0
  rw [dite_eq_left hT, ← hW f hf (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  show φ' _ = 0
  rw [map_sub, map_pow, h0, map_one, sub_self]

theorem evalAt_pow_eq_one {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (f : Rules pts) (k : ℕ) (h : ∀ (p : TRing K) (y : pts p.R), f p y ^ k = 1)
    {S : Type} [CommRing S] [Algebra K S] (y : pts S) (hT : FromTest pts mapR y) :
    evalAt pts mapR f y ^ k = 1 := by
  unfold evalAt
  rw [dite_eq_left hT, ← map_pow, h, map_one]

end GlobalTheory.FiniteOrderRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.FiniteOrderRule.unitC_of_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → UnitC d := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet hC A y
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hk : Nat.card Cls ≠ 0 := Nat.card_pos.ne'
  have h1 := GlobalTheory.FiniteOrderRule.pow_eq_one_of_complex (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) (GlobalTheory.Frames.algebraic_laws hS E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
    (fun S _ _ T _ _ φ y => GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw d.l₂ d.Xo₂ d.c₂ S T φ y)
    d.c₂.F.val.toRingHom d.cδ hC.1.1 (Nat.card Cls) (fun z => by
      have h2 := hC.2 z
      unfold evR at h2
      rw [h2, if_neg Bool.false_ne_true, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one,
        Units.val_one, map_one])
  have h3 := @GlobalTheory.FiniteOrderRule.evalAt_pow_eq_one d.c₂.F _ (fun S _ _ => FrPt d.Xo₂ d.c₂ S)
    (fun φ y z => FrMap φ y z) d.cδ (Nat.card Cls) h1 ℂ _ A y
    (@GlobalTheory.Frames.allTest_of_secBaseChange hS E _ _ _ H Dw d.l₂ d.Xo₂ d.c₂ ℂ _ inferInstance A y)
  exact Complex.norm_eq_one_of_pow_eq_one h3 hk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvRSumSmulFin
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory

theorem evR_sum_smul_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {ι : Type} (s : Finset ι) (t : ι → c.F) (f : ι → Rul Xo c)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (∑ i ∈ s, t i • f i) y = ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y := by
  classical
  have hL : ∑ i ∈ s, t i • f i = ∑ j : Fin s.card, t (s.equivFin.symm j) • f (s.equivFin.symm j) := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => t i • f i)).symm
  have hR : ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y =
      ∑ j : Fin s.card, algebraMap c.F S (t (s.equivFin.symm j)) * evR Xo c (f (s.equivFin.symm j)) y := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => algebraMap c.F S (t i) * evR Xo c (f i) y)).symm
  rw [hL, hR]
  exact Formalism.L2.Pj.evR_sum_smul y (fun j => t (s.equivFin.symm j)) (fun j => f (s.equivFin.symm j))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
theorem _root_.GlobalTheory.FieldBC.exists_emb_ext {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (hle : c.F ≤ c'.F) (σ : c.F →+* ℂ) :
    ∃ σ' : c'.F →+* ℂ, σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle) = σ := by
  letI : Algebra c.F c'.F := (_root_.Formalism.L2.Pj.incF c c' hle).toAlgebra
  letI : Algebra c.F ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ c'.F := Algebra.IsAlgebraic.of_finite ℚ c'.F
  haveI : Algebra.IsAlgebraic c.F c'.F := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let τ : c'.F →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨τ.toRingHom, ?_⟩
  ext x
  exact τ.commutes x


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
theorem _root_.GlobalTheory.FieldBC.rulBC_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
    (hle : c.F ≤ c'.F) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ)
    (n : ℕ), ∀ f ∈ _root_.Formalism.L2.Pj.sec Xo c a n,
    (∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f) ∧
    (_root_.GlobalTheory.FieldBC.rulBC hle f ∈ _root_.Formalism.L2.Pj.cusp Xo c' (_root_.Formalism.L2.Pj.unfBC hle U) a n ↔ f ∈ _root_.Formalism.L2.Pj.cusp Xo c U a n) := by
  intro E _ _ _ H Dw l Xo c c' hle r U a n f hf
  obtain ⟨hsec, hval⟩ := (_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf
  have hread : ∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f := by
    intro σ'
    have hbc : _root_.Formalism.L2.Pj.IsBC hle (_root_.GlobalTheory.FieldBC.rulBC hle f) ![1] ![f] := by
      unfold _root_.Formalism.L2.Pj.IsBC
      intro S _ _ _ h y
      simp [hval S h y]
    rw [_root_.Formalism.L2.Pj.rdU_unfBC hle U σ' hbc, Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero, map_one]
    exact one_smul ℂ _
  refine ⟨hread, ?_⟩
  rw [_root_.Formalism.L2.Pj.mem_cusp, _root_.Formalism.L2.Pj.mem_cusp]
  constructor
  · rintro ⟨-, hcusp⟩
    refine ⟨hf, fun σ hσ => ?_⟩
    obtain ⟨σ', rfl⟩ := _root_.GlobalTheory.FieldBC.exists_emb_ext hle σ
    have hmem := hcusp σ' (_root_.Formalism.L2.Pj.goodEmb_ext hle hσ rfl)
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC] at hmem
    exact hmem
  · rintro ⟨-, hcusp⟩
    refine ⟨hsec, fun σ' hσ' => ?_⟩
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC]
    exact hcusp _ (by unfold _root_.Formalism.L2.Pj.GoodEmb at hσ' ⊢; exact hσ')

end GlobalTheory.FieldBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsInBasisSharesInContain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_inBasis_shares_inContain : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (G₀ : GlobalFamilyData (recPlusN h j hj n) ka wL wF) (Tn : ℕ) (CR c : ℝ) (S : Scal n.base), addL wF wL Tn = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn → Nonempty (ArchAt h j G₀.w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → LatAt n.base j ka → (∃ β : ℝ, ShortG (recPlusN h j hj n) ((recPlusN h j hj n).wF0 wL wF) ((recPlusN h j hj n).Thc S.s0 ((recPlusN h j hj n).wF0 wL wF)) β) → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → ∃ (del : ℕ) (th' : Fin del → n.base.Cusp j wF), (∀ i, th' i ∈ Sh) ∧ ∀ rz alz th0 zc rq th iet et, (∀ la, InBasis (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la) ∧ ShareRd (D := D) (j := j) Tn del ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) S Tn ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoP (D := D) (j := j) Tn (WeightFamilies.rhoP n.base CR Tn c j ka) ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ∀ la, InContainMR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la S CR Tn c := by
  intro D T h j hj n ka wL wF G₀ Tn CR c S hka hd2 hT hArch hRd hMgg hLat hShort Sh hSh

  obtain ⟨R, t, δ, xs, hgen, hA⟩ :=
    _root_.GlobalTheory.Shares.exists_anFacts_record D T h j hj n G₀.N ka wL wF G₀.w Tn CR c hka hArch hRd hMgg
      (_root_.GlobalTheory.MaxCuspRecord.tieMaxCusp D T h j hj ka CR (Tn : ℝ) c)

  obtain ⟨θ, hθS, hθ⟩ :=
    exists_valueBasis_in_spanning D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn _ δ xs hA Sh hSh
  refine ⟨δ, θ, hθS, ?_⟩
  intro rz alz th0 zc rq th iet et
  have hdT : WeightFamilies.dimY D j < Tn := by nlinarith
  have hd0 : 0 < WeightFamilies.dimY D j := by omega

  have hA' : AnFacts R (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et).w t ka wF Tn
      (WeightFamilies.MggK n.base CR Tn c j ka) xs := hA
  have hB : ∀ la, InBasis (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) la := fun la =>
    (_root_.GlobalTheory.Shares.inBasis_iff_vals D n.base _ j (recPlusN h j hj n) ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hgen hA' hka la).2 ⟨hθ, rfl⟩

  obtain ⟨β, Sg, hSg, hspan, -⟩ := hShort
  have hle := Submodule.span_mono (R := n.base.KO) hSg
  rw [hspan] at hle
  have hTop := top_le_iff.mp hle
  obtain ⟨la₀⟩ := nonempty_heightOneSpectrum_ringOfIntegers n.base.KO
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · exact shareRd_of_inBasis D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hdT hd0 hLat ⟨la₀, hB la₀⟩
  · exact shareRhoR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hd2 hT hLat S
  · exact shareRhoP_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn CR c δ xs hA hd2 hT hLat
  · intro la
    exact Contain.inContainMR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn CR c δ xs hgen hA' hka hdT.le S hTop la (hB la)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetMaxAtGoodEmb
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_net_max_at_goodEmb : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ NN : Finset (FPt (T.U j σ).X), NN.Nonempty ∧ (∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∃ p ∈ NN, supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) P ≤ 4 * ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w) w.n p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h hG large₂ j hj w hw hL hrn hf σ hσ

  have hne0 : Nonempty (T.U j σ).Comp := ⟨(T.dict j σ 1).1⟩
  obtain ⟨-, hlrd, hd, hcc, hlf, -, -, -, hn⟩ := id hw
  obtain ⟨-, -, -, -, -, hfdeg, hdE, -, hfr, hf1, -, -, -⟩ := _root_.GlobalTheory.HostClear.host_clear D large₂.sc.L hL hlrd hd hcc
  obtain ⟨e, M, wg, hM1, hMl, hwg, hwgl, -, hk⟩ := _root_.GlobalTheory.CuspDataBounds.cusp_data_bounds D T h hG large₂ j hj w hw hL hrn σ hσ
  have hcard := _root_.GlobalTheory.RunIn.log_card_comp_le D T h large₂ j hj w hw hL hrn hf σ hσ
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by linarith
  have hr1 : 1 ≤ D.R.r := le_trans hf1 hfr
  have hF1 : (1 : ℝ) ≤ (fdeg D.host.E : ℝ) := by rw [hfdeg]; exact_mod_cast hf1
  have hZ : Zb D large₂ = (fdeg D.host.E : ℝ) * D.R.r * large₂.sc.L := by rw [hfdeg]; rfl

  have hlogr : Real.log (D.R.r : ℝ) ≤ large₂.sc.L := by
    refine le_trans (Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrn)) hn
  have hlogf : Real.log (fdeg D.host.E : ℝ) ≤ 2 * large₂.sc.L := by rw [hfdeg]; exact hlf
  obtain ⟨NN, hne, hP, hlog⟩ :=
    GlobalTheory.NetMax.exists_net_all_components_max D.host.E D.R.r (T.U j σ).Comp (fun k => (e k).toX)
      (laU (T.U j σ) (wtA w) w.n) M wg large₂.sc.L hr1 hL1 hM1 hwg (fun k => (hk k).1) (fun k => (hk k).2.1)
      hlogf hlogr hMl hwgl hdE
      (fun k => ⟨(hk k).2.2.1, le_trans (hk k).2.2.2.1 (by nlinarith),
        le_trans (hk k).2.2.2.2.1 (by nlinarith), le_trans (hk k).2.2.2.2.2.1 (by nlinarith)⟩)
      (by rw [← hZ]; exact hcard)
  refine ⟨NN, hne, hP, ?_⟩
  rw [hZ]
  exact hlog

end GlobalTheory.RunIn
end

