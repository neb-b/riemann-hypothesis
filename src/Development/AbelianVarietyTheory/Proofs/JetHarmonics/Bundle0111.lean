module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyRecursionStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_recursion : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.Moment.moment_first_length | exact GlobalTheory.Moment.moment_first_length | (intros; apply GlobalTheory.Moment.moment_first_length <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
section
noncomputable section

namespace GlobalTheory.ShortMove

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

def Marked {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (l : Level H)
    (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (mk : Dw.La → (Fin r → D.host.E)) (h : GA D V) : Prop :=
  (Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V h : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V h, finVec V (mk a ∘ Fin.cast hr) - (finHom V h).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
def FormPlus {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y)))

end GlobalTheory.ShortMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValues
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Transfer

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer GlobalTheory.PowGerm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem dLin_id : dLin (pt R (n := 1) d 0) = 1 := by
  classical
  ext i j
  simp only [dLin, pt, coeff_X, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero e)).symm

theorem law_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.G.F = B'.G.F := funext fun i => ((Related.refl B).law i).trans (h.law i).symm

theorem act_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.A.act = B'.A.act := funext fun a => ((Related.refl B).act a).trans (h.act a).symm

theorem const_diagSer {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d} (h : Related B B' φ φi ε) (w0 : O) :
    constantCoeff (diagSer B' w0 ε) = 1 := by
  have h1 := congrArg constantCoeff h.ax1
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_one] at h1
  unfold diagSer
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0))), h1]

theorem exists_inv_pow {σ : Type} (s : MvPowerSeries σ R) (hs : constantCoeff s = 1) (q : ℕ) :
    ∃ un : MvPowerSeries σ R, constantCoeff un = 1 ∧ un * s ^ q = 1 := by
  have hu : IsUnit (s ^ q) := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hs ▸ isUnit_one)).pow q
  obtain ⟨un, hun⟩ := hu.exists_left_inv
  refine ⟨un, ?_, hun⟩
  have := congrArg constantCoeff hun
  rwa [map_mul, map_pow, hs, one_pow, mul_one, map_one] at this

theorem const_gauge {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d}
    (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h1 := congrArg constantCoeff hh.ax1
  rwa [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_zero] at h1

theorem exists_gauge {B B' : FB R d O} {ε : PS R 2 d} (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ : PS k 2 d) (hh : B.IsCanonGauge k h₀) :
    ∃ h' : PS k 2 d, B₂.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ m = f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B₂.nabVal k h' w0 m f' u P = B.nabVal k h₀ w0 m f u P := by
  obtain ⟨h', hh', hv⟩ := GlobalTheory.JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.2.2.2.1 R d O B B' _ _ ε hr k h₀ hh
  refine ⟨h', (hG h').1 hh', fun w0 m f f' hf Λ _ u P => ?_⟩
  have e : (fun i => FB.toK k (pt R (n := 1) d 0 i)) = pt k (n := 1) d 0 := by
    funext i
    simp [pt]
  have h1 := hv w0 m f f' (by rw [e, gt_ev_pt_self]; exact hf) Λ u P
  rw [dLin_id, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [Matrix.one_mulVec] at h1
  rw [← h1]
  unfold FB.nabVal FB.hL
  rw [hF, hA]

theorem eig_map {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) (a : O) (u : Fin d → R) (s : R)
    (h : (dAct R B a).mulVec u = s • u) :
    (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • fun i => algebraMap R k (u i) := by
  funext i
  have h1 := congrArg (algebraMap R k) (congrFun h i)
  simpa [Matrix.mulVec, dotProduct, dAct, FB.actK, coeff_map] using h1

theorem value_eq [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] {B B' : FB R d O} {ε : PS R 2 d}
    (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ h : PS k 2 d) (hh₀ : B.IsCanonGauge k h₀)
    (hh : B₂.IsCanonGauge k h) {T : Type} [Fintype T] (r : T → ℕ) (cc : T → T) (σ : T → O →+* k)
    (hcc : ∀ τ, cc (cc τ) = τ) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu : ∀ l a, (dAct k B₂ a).mulVec (u l) = σ l.1 a • u l) {n : ℕ}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : ∀ (τ : T) (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
        (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0)
    (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (hf : ∀ b, f' b * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ q = f b)
    {Ix : Type} [Fintype Ix] (e : (Σ τ : T, Fin (r τ)) × Fin n → Ix) (cp : Ix → Fin n) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu' : ∀ p, u' (e p) = u p.1) :
    Formalism.L2.Pj.nabValN B₂ k h w0 q (boxSer f') cp u' (MvPolynomial.rename e Q) =
      ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h₀ w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  obtain ⟨h', hh', hval⟩ := exists_gauge hr B₂ hF hA hG h₀ hh₀
  rw [nabValN_boxSer R' d O B₂ k h w0 (const_gauge hh) q n f' _ Ix e cp u u' hcp hu' Q,
    canonGauge_independence_harmonic R' d O k B₂ h h' hh hh' T r cc (fun _ => True) σ hcc (fun _ => Or.inl trivial)
      hσ hsep u hu n Q (fun τ _ => hQ τ) w0 q f']
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b _ => hval w0 q (f b) (f' b) (hf b) _ u (MvPolynomial.monomial (colM mo b) 1)]

end GlobalTheory.Transfer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory


set_option maxHeartbeats 400000 in
theorem transfer_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  intro L1 L2 L4 TW E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hFr P tors ϖ hϖ Q hQ F _ _ _ _ _ _ v hv
  letI := io.toAlgebra
  haveI := T.cpl
  obtain ⟨BT, e1, e2, e3, e4, e5, e6, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hF, hA, hG, hcan⟩ := e7 F
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hrel, hgerm⟩ := _root_.GlobalTheory.ChartLink.link L1 L2 L4 TW E H T.V T.cpl C.I.G P tors ϖ hϖ
    Q hQ F v hv (chD C.ch) BT C.tgT C.xT C.eT C.wPT (by rw [e1, e2]; exact C.chartT)
    (by rw [e1, e2, e3, e4, e5, e6]; exact C.frameT) C.primT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) hFr τ hτ
    (by rw [e2]; exact hEL)
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, (Transfer.law_eq hrel).trans e1, (Transfer.act_eq hrel).trans e2, ?_⟩
  intro g g' π hg hg' hπ n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hon s s' t f hcol
  obtain ⟨un, hun1, hun⟩ := Transfer.exists_inv_pow _ (Transfer.const_diagSer hrel H.w0) (g' * g)
  have hf : ∀ b, (f b * MvPowerSeries.map (algebraMap T.V F) un) *
      MvPowerSeries.map (algebraMap T.V F) (diagSer BT H.w0 ε) ^ (g' * g) = f b := fun b => by
    rw [_root_.mul_assoc, ← map_pow, ← map_mul, hun, map_one, _root_.mul_one]
  choose σ hσ1 hσ2 using fun b => hgerm (g' * g) (t b) (f b) _ (hcol b).2.2.2 (hf b)
  choose p xx w ζ t₀ h1 h2 h3 h4 h5 h6 h7 using fun b => (hcol b).2.2.1
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', hbox, -⟩ := _root_.GlobalTheory.boxTup_of_columns L1 L2 L4 TW E H Dw l Xo c T io y C P ϖ hϖ Q hQ F v
    g g' π hg hg' hπ τ hτ hEL n D' A' G' pD pA pG U' PU oD' hxe hon s s' t₀ t p w ζ xx σ
    (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un)
    (fun b => ⟨(hcol b).1, (hcol b).2.1, h3 b, h4 b, h5 b, h1 b, h2 b, h6 b, h7 b, hσ1 b, hσ2 b⟩)
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', _, un, hbox, hun1, rfl, ?_⟩
  intro h₀ hh₀ rk hrk Pp hPp
  have huv : ∀ ℓ i, algebraMap T.Fr F (C.ch.uvec ℓ i) = algebraMap T.V F (C.uvecT ℓ i) := fun ℓ i => by
    rw [C.gen.1.2.2.2.2.2.2 ℓ i, ← IsScalarTower.algebraMap_apply]
  refine Transfer.value_eq hrel C.ch.B hF hA hG h₀ _ hh₀ hcan rk ComplexEmbedding.conjugate
    (fun τ => (algebraMap T.Fr F).comp (io.comp (embK c τ))) (fun τ => ComplexEmbedding.involutive_conjugate E τ) ?_ ?_
    (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) ?_ Pp hPp
    H.w0 (g' * g) f _ hf
    (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n))
    (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    (fun _ => rfl) (fun p => funext fun i => huv _ i)
  · intro τ a
    have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    exact congrArg (fun z => algebraMap T.Fr F (io z)) h
  · intro τ τ' hne
    obtain ⟨a, ha⟩ := EigDir.embK_sep c τ τ' hne
    refine ⟨a, ?_⟩
    simp only [RingHom.comp_apply]
    rw [← map_sub, ← map_sub]
    exact ((isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)).map io).map _
  · intro ℓ a
    have h := Transfer.eig_map (k := F) C.ch.B a _ _
      (eigDirSt E H Dw l Xo c T io y C a ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩)
    have e : (fun i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i)) =
        fun i => algebraMap T.V F (C.uvecT ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i) := funext fun i => huv _ i
    exact e ▸ h

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverSquare

open FrameLift OverMove

theorem rel_square {A A₂ Y Y' Y₂ Y₂' : Scheme.{0}} {L : LB A} {L₂ : LB A₂} (hL : L.IsLB) (hL₂ : L₂.IsLB)
    {φ φ' : A₂ ⟶ A} {ν : A ⟶ A} {ν₂ : A₂ ⟶ A₂} (hφ : ν₂ ≫ φ' = φ ≫ ν)
    {w₀ : LB.Iso L₂ (L.pull φ)} {w' : LB.Iso L₂ (L.pull φ')} {w : LB.Iso L (L.pull ν)} {w₂ : LB.Iso L₂ (L₂.pull ν₂)}
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ A₂) (z : Z) i k j l, ν (φ (f z)) ∈ L.U i → φ (f z) ∈ L.U k →
      ν₂ (f z) ∈ L₂.U j → f z ∈ L₂.U l →
      gw w (f ≫ φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂) z i j * gw w₂ f z j l)
    {q : Y ⟶ A} {q' : Y' ⟶ A} {q₂ : Y₂ ⟶ A₂} {q₂' : Y₂' ⟶ A₂} {p : Y₂ ⟶ Y} {p' : Y₂' ⟶ Y'} {pm : Y ⟶ Y'}
    {pm₂ : Y₂ ⟶ Y₂'} {σ : Y₂' ⟶ Y₂} (hσ : σ ≫ pm₂ = 𝟙 _) (hp : p ≫ q = q₂ ≫ φ) (h₂ : pm₂ ≫ q₂' = q₂ ≫ ν₂)
    (sq : pm₂ ≫ p' = p ≫ pm) {s : LB.Sec (LOne L q)} {s' : LB.Sec (LOne L q')} {s₂ : LB.Sec (LOne L₂ q₂)}
    {s₂' : LB.Sec (LOne L₂ q₂')} (H₀ : Rel w₀ p s₂ s) (H : Rel w pm s s') (H₂ : Rel w₂ pm₂ s₂ s₂') :
    Rel w' p' s₂' s' := by
  intro Z r z i j hi hj
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Z ⟶ Y₂, r = r₀ ≫ pm₂ := ⟨r ≫ σ, by rw [Category.assoc, hσ, Category.comp_id]⟩
  obtain ⟨k, hk⟩ := exists_chart hL (φ (q₂ (r₀ z)))
  obtain ⟨l, hl⟩ := exists_chart hL₂ (q₂ (r₀ z))
  have e₂ : q₂' (pm₂ (r₀ z)) = ν₂ (q₂ (r₀ z)) := pt_eq h₂ (r₀ z)
  have e₁ : q (p (r₀ z)) = φ (q₂ (r₀ z)) := pt_eq hp (r₀ z)
  have e₀ : φ' (ν₂ (q₂ (r₀ z))) = ν (φ (q₂ (r₀ z))) := pt_eq hφ (q₂ (r₀ z))
  have hj' : ν₂ (q₂ (r₀ z)) ∈ L₂.U j := e₂ ▸ (show q₂' (pm₂ (r₀ z)) ∈ L₂.U j from hj)
  have hi' : ν (φ (q₂ (r₀ z))) ∈ L.U i := by
    have : φ' (q₂' (pm₂ (r₀ z))) ∈ L.U i := hi
    rwa [e₂, e₀] at this
  have a := H Z (r₀ ≫ p) z i k (by show ν (q (p (r₀ z))) ∈ _; rw [e₁]; exact hi')
    (by show q (p (r₀ z)) ∈ _; rw [e₁]; exact hk)
  have b := H₀ Z r₀ z k l hk hl
  have c := H₂ Z r₀ z j l hj' hl
  have e := hw Z (r₀ ≫ q₂) z i k j l hi' hk hj' hl
  rw [Category.assoc r₀ pm₂ p', sq, ← Category.assoc r₀ p pm, a, b, c, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul, Category.assoc r₀ p q, hp, ← Category.assoc r₀ q₂ φ, e,
    Category.assoc r₀ pm₂ q₂', h₂, Category.assoc r₀ q₂ ν₂]

theorem gw_square {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ⟶ S₂}
    (hu : Function.Surjective t₂.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂)
    (hr : ρ₂ ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t.PP.L (t.PP.L.pull ν.φ)} {w₂ : LB.Iso t₂.PP.L (t₂.PP.L.pull ν₂.φ)}
    (h₀ : OverMove.RigIso m w₀) (h' : OverMove.RigIso m' w') (h : OverMove.RigIso ν w) (h₂ : OverMove.RigIso ν₂ w₂)
    (Z : Scheme.{0}) (f : Z ⟶ t₂.G.left) (z : Z) (i k : t.PP.L.ι) (j l : t₂.PP.L.ι)
    (hi : ν.φ (m.φ (f z)) ∈ t.PP.L.U i) (hk : m.φ (f z) ∈ t.PP.L.U k) (hj : ν₂.φ (f z) ∈ t₂.PP.L.U j)
    (hl : f z ∈ t₂.PP.L.U l) :
    gw w (f ≫ m.φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂.φ) z i j * gw w₂ f z j l := by
  obtain ⟨a, Ta⟩ := exists_comp t.PP.isLB w w₀ h.1 h₀.1 t.PP.isLB t₂.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w' w₂ h'.1 h₂.1 t.PP.isLB t₂.PP.isLB
  have ga := Ta.pgen_comp t.PP.isLB h.1 h₀.1
  have ra := Ta.pmaps_comp t.PP.isLB (fun _ => m.cm.e_comm) h.2 h₀.2
  have gb := Tb.pgen_comp t₂.PP.isLB h'.1 h₂.1
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => ν₂.cm.e_comm) h'.2 h₂.2
  have e := gw_eq_of_pmaps (S := S₂) (S₀ := S) t.PP.isLB t₂.PP.isLB t₂.G.hom (eSec t₂.G) (Over.w η[t₂.G]) hu
    hφ.symm ga gb (h₁ := m.cm.e ≫ ν.cm.e) (h₂ := ν₂.cm.e ≫ m'.cm.e)
    (by rw [m.base, m'.base, ν.base, ν₂.base]; exact hr.symm) ra rb f z i l
  have hi' : m'.φ (ν₂.φ (f z)) ∈ t.PP.L.U i :=
    (congrArg (· ∈ t.PP.L.U i) (pt_eq hφ (f z))).mpr hi
  exact (Ta Z f z i k l hi hk hl).symm.trans (e.trans (Tb Z f z i j l hi' hj hl))

end OverSquare


open FrameLift OverMove OverSquare in
theorem frOver_of_square_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  intro E _ _ _ H Dw l Xo c n d ρ ν ρ₂ ν₂ r' m' hr hφ S _ _ _ y y' y₂ y₂' h hy hy₂
  obtain ⟨e, hu, w₀, p, hw₀, p₁, p₂, H₀⟩ := (frOver_iff d _ _).1 h
  obtain ⟨ex, eu, pm, w, a₁, a₂, hw, H₁⟩ := MoveCalc.frMove_iff_carry.1 hy
  obtain ⟨ex₂, eu₂, pm₂, w₂, b₁, b₂, hw₂, H₂⟩ := MoveCalc.frMove_iff_carry.1 hy₂
  obtain ⟨w', g', r₁', -⟩ := m'.lin
  have e' : y₂'.x ≫ r' = y'.x := by rw [ex₂, ex, Category.assoc, hr, ← Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso m' e'
  obtain ⟨σ, hσ⟩ := MoveCalc.exists_section ν₂ ex₂ b₁ b₂
  have sq : pm₂ ≫ p' = p ≫ pm := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, p₁', ← Category.assoc, b₂, Category.assoc, hφ, Category.assoc, a₂, ← Category.assoc p, p₁,
        Category.assoc]
    · rw [Category.assoc, p₂', b₁, Category.assoc, a₁, p₂]
  have hs : Function.Surjective d.Xo₂.univ.t.G.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _
    ⟨d.Xo₂.univ.t.semi.comm, d.Xo₂.univ.t.semi.smooth, d.Xo₂.univ.proper, d.Xo₂.univ.t.semi.geomConnected⟩).2
  refine (frOver_iff { d with r := r', m := m' } y₂' y').2 ⟨e', fun τ i => ?_, w', p', ⟨g', r₁'⟩, p₁', p₂', ?_⟩
  · show y₂'.u τ i ≫ m'.φ = y'.u τ i
    rw [eu₂, eu, Category.assoc, hφ, ← Category.assoc, hu]
  · exact rel_square Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hφ
      (gw_square hs d.m m' ν ν₂ hr hφ (rigIso_of d.m hw₀.1 hw₀.2) (rigIso_of m' g' r₁') (rigIso_of ν hw.1 hw.2.1)
        (rigIso_of ν₂ hw₂.1 hw₂.2.1)) hσ p₁ b₂ sq H₀ H₁ H₂

end GlobalTheory
end
end

