module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def rulEv (U : Unf Xo c σ r)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) :
    Rul Xo c →+* ((Σ k : U.Comp, (U.X k).dom) → ℂ) where
  toFun f y := rdU U f y.1 y.2.1
  map_zero' := by funext y; rw [map_zero]; rfl
  map_add' f g := by funext y; rw [map_add (f := _)]; rfl
  map_mul' f g := by funext y; rw [rdU_mul]; rfl
  map_one' := by
    funext y
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom U 1 y.1 y.2]
    have e : evR Xo c 1 (U.un y.1 y.2) = 1 := evalAt_one _ _ _ (hT y.1 y.2)
    rw [e]
    rfl

end Ev

def sumParts (R M : Type) [CommRing R] [AddCommMonoid M] :
    AddMonoidAlgebra R M →+* R :=
  (AddMonoidAlgebra.lift R R M 1).toRingHom

theorem sumParts_single (R M : Type) [CommRing R] [AddCommMonoid M] (m : M) (f : R) :
    sumParts R M (AddMonoidAlgebra.single m f) = f := by
  simp [sumParts]

theorem sumParts_smul (K R M : Type) [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (a : K)
    (x : AddMonoidAlgebra R M) : sumParts R M (a • x) = a • sumParts R M x := by
  rw [← algebraMap_smul R a x, ← algebraMap_smul R a (sumParts R M x)]
  exact map_smul (AddMonoidAlgebra.lift R R M 1) _ _


set_option synthInstance.maxHeartbeats 200000 in
theorem exists_isRdgU : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  intro D T h j hj n
  have hT := h.unTest j hj T.σ₀ T.good_σ₀
  have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
  let ev : AddMonoidAlgebra (T.R j) (Deg D j) →+* (DomPt T j → ℂ) :=
    (rulEv (T.U j T.σ₀) hT).comp (sumParts (T.R j) (Deg D j))
  have hev : ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (y : DomPt T j),
      ev (incG deg (cutR T.C j) u F) y = rdR h j F y.1 y.2.1 := by
    intro u F y
    show rulEv (T.U j T.σ₀) hT (sumParts (T.R j) (Deg D j) (AddMonoidAlgebra.single (deg u) F.1)) y = _
    rw [sumParts_single]
    rfl
  have hsm : ∀ (a : T.Q.c.F) (F : AddMonoidAlgebra (T.R j) (Deg D j)), ev (a • F) = T.σ₀ a • ev F := by
    intro a F
    funext y
    show rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) (a • F)) y.1 y.2.1 =
      T.σ₀ a • rdU (T.U j T.σ₀) (sumParts (T.R j) (Deg D j) F) y.1 y.2.1
    rw [sumParts_smul, map_smulₛₗ]
    rfl
  have hind : ∀ (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → cutR T.C j u),
      LinearIndependent T.Q.c.F F → LinearIndependent ℂ fun i => ev (incG deg (cutR T.C j) u (F i)) := by
    intro u m F hF
    have hb := hF.map' (cutR T.C j u).subtype (Submodule.ker_subtype _)
    have hs : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n := fun i =>
      cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA u) u.n (cutR_le T.C j u (F i).2)
    have hli : LinearIndependent ℂ (fun i => rdU (T.U j T.σ₀) (F i).1) :=
      (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ T.σ₀ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀))
        ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) (wtA u) u.n).1 m (fun i => (F i).1) hs hb
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg
    refine hli g ?_
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
    · have h1 := congrFun hg ⟨k, ⟨x, hx⟩⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun z => g i * z) (hev u (F i) ⟨k, ⟨x, hx⟩⟩).symm
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : rdU (T.U j T.σ₀) (F i).1 k x = 0 := dif_neg hx
      rw [this, mul_zero]
  exact ⟨⟨DomPt T j, T.σ₀, ev, hsm, hind⟩, Equiv.refl _, fun _ => rfl, hev⟩

end GlobalTheory.Shares
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomial
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.ShortValueLinear

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.IsHomogeneous (∑ σ : T, ∑ i : Fin (r σ), a σ i) := by
  classical
  intro m hm
  have hmS : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
  have key : ∀ (σ : T) (i : Fin (r σ)), a σ (i : ℕ) = ∑ b, m ⟨σ, (i, b)⟩ :=
    fun σ i => (hP m hmS σ i).symm
  simp only [key]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fintype.sum_prod_type _

theorem sum_support_eq_constr {ι F S : Type} [Field F] [CommRing S] [Algebra F S]
    (G : (ι →₀ ℕ) → S) (P : MvPolynomial ι F) :
    ∑ m ∈ P.support, algebraMap F S (P.coeff m) * G m =
      (MvPolynomial.basisMonomials ι F).constr F G P := by
  classical
  rw [Module.Basis.constr_apply, Finsupp.sum]
  refine Finset.sum_congr ?_ fun μ _ => ?_
  · ext μ
    simp [MvPolynomial.basisMonomials]
  · simp [MvPolynomial.basisMonomials, Algebra.smul_def]

theorem formula_linear {ι F S Qt J : Type} [Field F] [CommRing S] [Algebra F S] [Finite Qt] [Fintype J]
    (k N : F) (w : Qt → F) (G : Qt → J → (ι →₀ ℕ) → S) (d m : ℕ) (cf : Fin m → F)
    (Q : Fin m → MvPolynomial ι F) (hQ : ∀ i, (Q i).IsHomogeneous d) :
    algebraMap F S (k * (N ^ (∑ i, cf i • Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (∑ i, cf i • Q i).support,
          algebraMap F S ((∑ i, cf i • Q i).coeff μ) * G q j μ =
      ∑ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (Q i).support,
          algebraMap F S ((Q i).coeff μ) * G q j μ) := by
  classical
  have := Fintype.ofFinite Qt
  set B := MvPolynomial.basisMonomials ι F
  have hsum : ∀ (P : MvPolynomial ι F) (q : Qt) (j : J),
      ∑ μ ∈ P.support, algebraMap F S (P.coeff μ) * G q j μ = B.constr F (G q j) P :=
    fun P q j => sum_support_eq_constr (G q j) P
  simp only [hsum, finsum_eq_sum_of_fintype]
  have hpre : ∀ P : MvPolynomial ι F, P.IsHomogeneous d →
      algebraMap F S (k * (N ^ P.totalDegree)⁻¹) *
          ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P =
        algebraMap F S (k * (N ^ d)⁻¹) * ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P := by
    intro P hP
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [hP.totalDegree hP0]
  have hQs : (∑ i, cf i • Q i).IsHomogeneous d := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hQ i))
  have hR : ∀ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) =
      algebraMap F S (cf i) * (algebraMap F S (k * (N ^ d)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) :=
    fun i => by rw [hpre _ (hQ i)]
  have hlin : ∀ (q : Qt) (j : J), B.constr F (G q j) (∑ i, cf i • Q i) =
      ∑ i, algebraMap F S (cf i) * B.constr F (G q j) (Q i) := by
    intro q j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
  rw [hpre _ hQs]
  simp only [hR]
  simp only [hlin, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.ShortValueLinear

namespace GlobalTheory

theorem shortThetaValue_linear : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hL a w β m cf Q hQ S _ _ y v u hv hu
  classical
  have : Finite (LevQ Dw l) := GlobalTheory.ShortValue.finite_levelQuotient Dw l
  have hEU := fun i => GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l
    Xo c nab hnab n Λ N hU hT hL a (Q i) (hQ i) w β
  have hRow : ∀ i, RowDeg Dw.mult n c.F (fun τ j => a (τ, j)) (Q i) := by
    intro i
    have h := hQ i
    unfold HHa at h
    simp only [Set.mem_setOf_eq] at h
    exact h.2.2
  have hQd := fun i => GlobalTheory.ShortValueLinear.isHomogeneous_of_rowDeg (hRow i)
  unfold ShortValAt at hv
  obtain ⟨S', _i1, _i2, φ, y', z, tp, F, hff, hfr, hz, hgeo, htp, huu, hφv⟩ := hv
  have hnat : ∀ i, φ (u i) = algebraMap c.F S' (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ (Q i).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S' (w q) *
        ∑ j, ∑ μ ∈ (Q i).support, algebraMap c.F S' ((Q i).coeff μ) *
          ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b) := by
    intro i
    refine (hEU i).2 S S' φ y y' hfr (u i) _ (hu i) ?_
    unfold ShortValAt
    exact ⟨S', _i1, _i2, AlgHom.id c.F S', y', z, tp, F,
      RingHom.FaithfullyFlat.of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩,
      GlobalTheory.Frames.frMapUniq_refl y', hz, hgeo, htp, huu, rfl⟩
  have hlin := GlobalTheory.ShortValueLinear.formula_linear (S := S')
    (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹) (N : c.F) w
    (fun q j μ => ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b)) _ m cf Q hQd
  apply RingHom.FaithfullyFlat.injective hff
  change φ v = φ (∑ i, algebraMap c.F S (cf i) * u i)
  rw [hφv]
  refine hlin.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul φ, AlgHom.commutes, hnat i]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory

theorem thetaRule_exists_and_eval : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → (∃ f : Rul Xo c, IsThRule Xo c nab xx P f ∧ f ∈ sec Xo c a n) ∧ ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ (k : Type) [Field k] [Algebra c.F k] (y : FrPt Xo c k), ThValAt Xo c nab y xx P (evR Xo c f y) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hn a n xx P hP
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hT := GlobalTheory.thValTot_of_chartIndep hL hC E H Dw l Xo c nab hn
  refine ⟨?_, fun f hf k _ _ y => ?_⟩
  · obtain ⟨f, hf, -⟩ := existsUnique_thRule Xo c nab hT xx hP
    exact ⟨f, hf, GlobalTheory.thetaRule_mem_sec hL hC E H Dw l Xo c nab hn a n f ⟨xx, P, hP, hf⟩⟩
  · have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c k y
    obtain ⟨w, hw, -⟩ := hT k y a n xx P hP
    have e : evR Xo c f y = w := by
      unfold evR Formalism.L2.Pj.evalAt
      rw [dite_eq_left h]
      exact GlobalTheory.thetaValue_natural hL hC E H Dw l Xo c nab hn _ _ _ _ y
        h.choose_spec.choose_spec.choose_spec a n xx P hP _ _ (hf _ _) hw
    rw [e]
    exact hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruence
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem monomial_degree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) {m : LtN Dw n →₀ ℕ} (hm : m ∈ P.support) :
    (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  have hrow := hP.1.2.2 m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hrow τ i

theorem totalDegree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  unfold MvPolynomial.totalDegree
  refine le_antisymm (Finset.sup_le fun m hm => (monomial_degree_of_mem_harm hP hm).le) ?_
  rw [← monomial_degree_of_mem_harm hP hm0]
  exact Finset.le_sup (f := fun s : LtN Dw n →₀ ℕ => s.sum fun _ e => e) hm0

theorem thExpr_eq_sum_superset (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (U : Finset (LtN Dw n →₀ ℕ))
    (hU : P.support ⊆ U) :
    thExpr Xo c nab y P F = algebraMap c.F S (((l.M : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)))⁻¹) *
      ∑ m ∈ U, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b) := by
  unfold thExpr
  rw [Finset.sum_subset hU (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul])]
  by_cases h0 : P = 0
  · subst h0; simp
  · rw [totalDegree_of_mem_harm hP h0]

theorem thExpr_linear (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P) :
    thExpr Xo c nab y P F = ∑ i, algebraMap c.F S (cf i) * thExpr Xo c nab y (Q i) F := by
  classical
  set U := P.support ∪ Finset.univ.biUnion fun i => (Q i).support
  have hQU : ∀ i, (Q i).support ⊆ U := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (Q i).support) (Finset.mem_univ i)).trans Finset.subset_union_right
  rw [thExpr_eq_sum_superset nab y F hP U Finset.subset_union_left]
  simp only [fun i => thExpr_eq_sum_superset nab y F (hQ i) U (hQU i)]
  subst hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem thValAt_linear (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P)
    {S : Type} [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) {v : S} (hv : ThValAt Xo c nab y0 x P v)
    (vi : Fin N → S) (hvi : ∀ i, ThValAt Xo c nab y0 x (Q i) (vi i)) :
    v = ∑ i, algebraMap c.F S (cf i) * vi i := by
  obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hv
  have hrefl : FrMap (AlgHom.id c.F S') y' y' :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S' S' (AlgHom.id c.F S') y').2.1
  have e1 : ∀ i, φ (vi i) = thExpr Xo c nab y' (Q i) F := fun i =>
    GlobalTheory.thetaValue_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hnab S S' φ y0 y' hmap a n x (Q i) (hQ i)
      _ _ (hvi i) ⟨S', inferInstance, inferInstance, AlgHom.id c.F S', y', F,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, hrefl, hV, rfl⟩
  apply hff.injective
  show φ v = φ (∑ i, algebraMap c.F S (cf i) * vi i)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [he, thExpr_linear nab y' F cf Q hQ hP hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, AlgHom.commutes, e1 i]

theorem levPt_eq_of_sub_mem {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {u u' : Dw.La}
    (h : u - u' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : levPt Xo x0 u = levPt Xo x0 u' := by
  have e : Xo.univ.eta u = Xo.univ.eta u' := by
    have h1 := Xo.univ.eta_add (u - u') u'
    rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
    exact h1
  unfold levPt
  rw [e]

end Lin

theorem isThRule_linear_and_congr : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab a n
  refine ⟨fun x m cf Q f g hQ hP hf hg => ?_, fun x x' P f hx hf p y => ?_⟩
  · funext p y
    rw [thValAt_linear hC nab hnab x cf Q hQ hP rfl y (hf p y) (fun i => g i p y) (fun i => hg i p y)]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def (cf i) (g i p y)).symm
  · obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hf p y
    exact ⟨S', inferInstance, inferInstance, φ, y', F, hff, hmap,
      fun b => levPt_eq_of_sub_mem (Xo := Xo) y'.x (hx b) ▸ hV b, he⟩

end GlobalTheory.ThetaRule
end
end

