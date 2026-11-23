module

public import Mathlib
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0002
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

private theorem exp_real_smul_mem_UJset_of_inG {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (hX : X.conjTranspose * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X)).conjTranspose * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  set Y : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hYdef
  have hHX : H * X = -(X.conjTranspose * H) := eq_neg_of_add_eq_zero_right hX
  have hY : SemiconjBy H Y (-Y.conjTranspose) := by
    show H * Y = -Y.conjTranspose * H
    rw [hYdef, Matrix.mul_smul, hHX, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.neg_mul, Matrix.smul_mul, smul_neg]
  have key : NormedSpace.exp (-(-Y.conjTranspose)) * H * NormedSpace.exp Y = H := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
    letI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
    exact hY.exp_neg_mul_mul_exp_eq_self
  rwa [neg_neg, Matrix.exp_conjTranspose] at key

private theorem mul_mem_UH_Hpk' {k r : ℕ} {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r := by
  have hg' : g.conjTranspose * Hpk k r * g = Hpk k r := hg
  have hh' : h.conjTranspose * Hpk k r * h = Hpk k r := hh
  show (g * h).conjTranspose * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul, show h.conjTranspose * g.conjTranspose * Hpk k r * (g * h) = h.conjTranspose * (g.conjTranspose * Hpk k r * g) * h by
    simp only [Matrix.mul_assoc], hg', hh']

private theorem exp_smul_mem_UJset' {k r : ℕ} {X : B.Mat k r} (hX : B.inLie k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r :=
  exp_real_smul_mem_UJset_of_inG (Hpk k r) X hX t

private theorem rdV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, RdV X f g = RdV X f' g := by
  intro g hg
  simp only [RdV]
  congr 1
  funext t
  exact h _ (mul_mem_UH_Hpk' hg (exp_smul_mem_UJset' hX t))

private theorem ldV_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : B.Mat k r} (hX : B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.LdV X f g = B.LdV X f' g := by
  intro g hg
  simp only [B.LdV]
  congr 1
  funext t
  have hneg : -((t : ℂ) • X) = ((-t : ℝ) : ℂ) • X := by rw [Complex.ofReal_neg, neg_smul]
  rw [hneg]
  exact h _ (mul_mem_UH_Hpk' (exp_smul_mem_UJset' hX (-t)) hg)

private theorem rw_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {f f' : B.Mat k r → E}
    (h : ∀ g ∈ B.GV k r, f g = f' g) : ∀ g ∈ B.GV k r, B.Rw v f g = B.Rw v f' g := by
  induction v with
  | nil => exact h
  | cons X v ih =>
    exact rdV_congr_on_GV (hv X List.mem_cons_self) (ih fun Y hY => hv Y (List.mem_cons_of_mem X hY))

private theorem dLR_congr_on_GV {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X)
    {f f' : B.Mat k r → E} (h : ∀ g ∈ B.GV k r, f g = f' g) :
    ∀ g ∈ B.GV k r, B.dLR u v f g = B.dLR u v f' g := by
  induction u with
  | nil => exact rw_congr_on_GV v hv h
  | cons X u ih =>
    exact ldV_congr_on_GV (hu X List.mem_cons_self) (ih fun Y hY => hu Y (List.mem_cons_of_mem X hY))

theorem ckOn_inCC_congr_on_group : ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (F F' : B.Mat k r → E), (∀ g ∈ B.GV k r, F g = F' g) → (B.CkOn ⊤ (B.GV k r) F → B.CkOn ⊤ (B.GV k r) F') ∧ ∀ m : ℕ, B.InCC A m F → B.InCC A m F' := by
  intro k r E _ _ A F F' h
  have hck : ∀ m : ℕ∞, B.CkOn m (B.GV k r) F → B.CkOn m (B.GV k r) F' := by
    intro m hF g₀ hg₀
    obtain ⟨U, f', hU, hg₀U, hf', hfU⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hg₀U, hf', fun g hgU hgG => (h g hgG).symm.trans (hfU g hgU hgG)⟩
  refine ⟨hck ⊤, fun m hF => ?_⟩
  unfold B.InCC B.CCle at hF ⊢
  obtain ⟨c, hc1, hc2⟩ := hF
  refine ⟨c, hck _ hc1, fun u v hu hv hlen g hg => ?_⟩
  rw [← dLR_congr_on_GV u v (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1) h g hg]
  exact hc2 u v hu hv hlen g hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth
section
noncomputable section

namespace GlobalTheory.SideCompare

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  first
  | (rename_i h_5 h_6; revert k r μG μS ν h_5 h_6 hS hq; exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas)
  | exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | (apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas ..)

theorem muS_ne_zero {k r : ℕ} {μW μN : Measure (Mt k r)} [SFinite μN] (hW : μW ≠ 0) (hN : μN ≠ 0) :
    muS μW μN ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero] at *
  unfold muS
  rw [Measure.map_apply SideNormalisedGap.measurable_mulP MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  exact mul_ne_zero hW hN

section Side

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
  (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
  (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r))

end Side

section Decay

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Decay

end GlobalTheory.SideCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EhInvEntry
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Matrix in
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.ThetaLeast


open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in
theorem nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by
  set ψ := algebraMap S S' with hψ
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S S') (B.G.F i)
    ext e
    simp [coeff_map, hψ]
  have eA : mapP ψ (B.actK S w0) = B.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S S') (B.A.act w0 i)
    ext e
    simp [coeff_map, hψ]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

theorem smul_mem_HHa {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_lift_integers (K : Type) [Field K] [NumberField K] (V L : Type) [CommRing V] [IsDomain V]
    [IsIntegrallyClosed V] [Field L] [Algebra V L] [IsFractionRing V L] (io : K →+* L) :
    ∃ φ : 𝓞 K →+* V, ∀ x : 𝓞 K, algebraMap V L (φ x) = io (x : K) := by
  have h : ∀ x : 𝓞 K, ∃ z : V, algebraMap V L z = io (x : K) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      (IsIntegral.tower_top (R := ℤ) (map_isIntegral_int io x.isIntegral_coe))
  choose g hg using h
  have inj := IsFractionRing.injective V L
  refine ⟨⟨⟨⟨g, inj ?_⟩, fun x y => inj ?_⟩, inj ?_, fun x y => inj ?_⟩, hg⟩ <;> simp [hg]

theorem exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift_integers K T.V T.Fr io
  let p : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal T.V).comap φ
  haveI hp : p.IsPrime := Ideal.comap_isPrime _ _
  have hS : p.primeCompl ≤ nonZeroDivisors (𝓞 K) := p.primeCompl_le_nonZeroDivisors
  let V := Localization.subalgebra.ofField K p.primeCompl hS
  haveI : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V p
  haveI : IsDedekindDomain V := IsLocalization.isDedekindDomain (𝓞 K) hS V
  haveI : IsPrincipalIdealRing V :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 3 1).1 ‹IsDedekindDomain V›
  have hu : ∀ s : p.primeCompl, IsUnit (φ s) := fun s => by
    by_contra hn
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  have hV : ∀ x : V, io (algebraMap V K x) ∈ (algebraMap T.V T.Fr).range := by
    rintro ⟨x, a, s, hs, rfl⟩
    obtain ⟨u, hu'⟩ := hu ⟨s, hs⟩
    refine ⟨φ a * (u⁻¹ : T.Vˣ), ?_⟩
    change _ = io (algebraMap _ K a * (algebraMap _ K s)⁻¹)
    rw [map_mul, map_mul, map_inv₀, map_units_inv, hu', hφ, hφ]
  obtain ⟨s, c, Q, hc, hQ, hsum⟩ := GlobalTheory.exists_integral_combination_of_mem_HaO Ty r n V K T.Fr io _ hV cc isX a P hP
  have hden : ∀ j, ∃ b : p.primeCompl, ∀ m, (((b : 𝓞 K) : K) • Q j).coeff m ∈ (integralClosure ℤ K).toSubring := by
    intro j
    choose g hg using (hQ j).2
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Q j).support g
    refine ⟨b, fun m => ?_⟩
    by_cases hm : m ∈ (Q j).support
    · obtain ⟨z, hz⟩ := hb m hm
      have : (((b : 𝓞 K) : K) • Q j).coeff m = (z : K) := by
        rw [MvPolynomial.coeff_smul, ← hg m]
        have := congrArg (algebraMap V K) hz
        rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] at this
        exact this.symm
      rw [this]
      exact z.isIntegral_coe
    · rw [MvPolynomial.coeff_smul, MvPolynomial.notMem_support_iff.1 hm, smul_zero]
      exact Subring.zero_mem _
  choose b hb using hden
  choose c' hc' using hc
  choose u hu' using hu
  refine ⟨s, fun j => c' j * ((u (b j))⁻¹ : T.Vˣ), fun j => ((b j : 𝓞 K) : K) • Q j,
    fun j => ⟨smul_mem_HHa _ (hQ j).1, hb j⟩, ?_⟩
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : io ((b j : 𝓞 K) : K) ≠ 0 := by
    rw [← hφ, ← hu']
    exact ((u (b j)).isUnit.map _).ne_zero
  beta_reduce
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map io), MvPolynomial.map_C, ← mul_assoc,
    ← map_mul, map_mul (algebraMap T.V T.Fr), map_units_inv, hu', hφ, hc', mul_assoc, inv_mul_cancel₀ h0, mul_one]

theorem totalDegree_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (T : CDVR) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) T.Fr} (hP : P ∈ FFV (Dw := Dw) T a n) :
    P.totalDegree ≤ DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  exact Finset.sup_le fun m' hm' => (key m' hm').le

theorem val_algebraMap_nonneg (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ)) (x : T.V) :
    0 ≤ v (algebraMap T.Fr F (algebraMap T.V T.Fr x)) := by
  by_cases hx : algebraMap T.V T.Fr x = 0
  · rw [hx, map_zero, AddValuation.map_zero]; exact le_top
  · rw [hv _ hx]
    exact_mod_cast GlobalTheory.vV_algebraMap_nonneg_dvr T x

theorem nval_le_of_val (T : CDVR) {F : Type} [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ))
    (hv : ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ))
    {x z : T.Fr} (hx : x ≠ 0) {ε : F} (hε : 0 ≤ v ε) {ρ : ℚ} (hρ : v (ε * algebraMap T.Fr F z) = (ρ : WithTop ℚ))
    {δ : ℝ} (hle : (ρ : ℝ) ≤ ((vV T.V x : ℤ) : ℚ) + δ) (e : ℕ) :
    nval T.V e z ≤ nval T.V e x + ((δ / e : ℝ) : EReal) := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, AddValuation.map_zero] at hρ
    exact WithTop.top_ne_coe hρ
  rw [AddValuation.map_mul, hv z hz] at hρ
  have h1 : (((vV T.V z : ℤ) : ℚ) : WithTop ℚ) ≤ (ρ : WithTop ℚ) := hρ ▸ le_add_of_nonneg_left hε
  have h2 : ((vV T.V z : ℤ) : ℚ) ≤ ρ := WithTop.coe_le_coe.1 h1
  have h3 : ((vV T.V z : ℤ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h2
  rw [nval_of_ne hz, nval_of_ne hx, ← EReal.coe_add, EReal.coe_le_coe_iff, ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg e)
  rw [Rat.cast_intCast] at hle
  linarith

theorem le_iInf_add_coe {ι : Sort*} {X : EReal} {g : ι → EReal} {δ : ℝ} (h : ∀ i, X ≤ g i + (δ : EReal)) :
    X ≤ (⨅ i, g i) + (δ : EReal) := by
  rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))]
  exact le_iInf fun i =>
    (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot δ)) (Or.inl (EReal.coe_ne_top δ))).2 (h i)

end GlobalTheory.ThetaLeast
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepOnePlusDet
section
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace BranchingSupport.TensInh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem lenA_eq_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) :
    lenA k r z g a = Formalism.MainNotions.S.lA k r z g a := by
  classical
  let Lm : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    { toFun := fun v => WithLp.toLp 2 (g⁻¹ *ᵥ v)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ
    (Set.range fun b : {b : Fin r // b.val < a.val} => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1))
  have hlt : ∀ b : Fin (r + 1), b < a → b.val < r :=
    fun b hb => Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ a.2)
  have hfv : ∀ (b : Fin (r + 1)) (hb : b < a),
      Formalism.QuantumDeterminants.fvec k r z b = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r ⟨b.val, hlt b hb⟩) := by
    intro b hb
    have hbr : b.val < r := hlt b hb
    simp [Formalism.QuantumDeterminants.fvec, hbr]
  have hspan : Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) = S.map Lm := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨_, ⟨⟨⟨b.val, hlt b hb⟩, hb⟩, rfl⟩, ?_⟩
      exact (congrArg (fun v => (WithLp.toLp 2 (g⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))
        (hfv b hb)).symm
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨b.val, by have := b.2; omega⟩, hb, ?_⟩
      show WithLp.toLp 2 (g⁻¹ *ᵥ _) = _
      rw [hfv _ hb]
      rfl
  have hd : ∀ y, dist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
      (WithLp.toLp 2 (g⁻¹ *ᵥ y)) = Formalism.MainNotions.S.eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y)) := by
    intro y
    rw [EuclideanSpace.dist_eq]
    simp [Formalism.MainNotions.S.eucl, Matrix.mulVec_sub, Complex.normSq_eq_norm_sq, dist_eq_norm]
  unfold lenA Formalism.MainNotions.S.lA
  rw [hspan, Metric.infDist_eq_iInf, ← sInf_range]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hd y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Lm y, y, hy, rfl⟩, hd y⟩

end BranchingSupport.TensInh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReducedWignerCoefficientLowering
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem reducedWigner_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + (n : ℂ))).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hE hEt hOm M v hv
  set m : Fin (n + 1) → ℂ := shf β L with hm
  have hcap : ∀ w v, qdet E w v = (∏ j, (w + m j)) • v := fun w v => hH.cap w v
  have hrel := tensor_dual_standard_rel V n E Et Om hH.gl hE hEt hOm
  obtain ⟨K, hK1, hK2⟩ := lastComatrixRow_inverts_dual V n E Om m hH.gl hcap hOm
  have hinj : Function.Injective m := by
    intro i j hij
    have h1 : ((L i : ℤ) : ℂ) = ((L j : ℤ) : ℂ) := by
      simpa [hm, shf] using hij
    exact hH.anti.injective (by exact_mod_cast h1)
  let ev : PiLp 2 (fun _ : Fin (n + 1) => V) →ₗ[ℂ] V :=
    { toFun := fun x => x (Fin.last n)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  let q : ℂ → ℂ := fun u => ∏ j, (u + shf β M j)
  have hq : Continuous q := by
    exact continuous_finsetProd _ (fun j _ => continuous_id.add continuous_const)
  have hKy : ∀ u, K u (PiLp.single 2 (Fin.last n) v) = q u • v := by
    intro u
    rw [hK2]
    exact (mem_CapSp.mp hv) u
  have hres := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    m (n : ℂ) Om ev K q (PiLp.single 2 (Fin.last n) v) v l hinj hrel.2.2.1
    (splitCasimir_eigenvalue_dual V n E Et Om m hH.gl hE hcap hEt hOm)
    (fun u x => hK1 u x) hq hKy
  have hev : m l + (n : ℂ) = β + L l + (n : ℂ) := by simp [hm, shf]
  rw [hev] at hres
  change ev _ = _
  rw [hres]
  congr 1
  simp only [q, hm, shf, WigSh.wM]
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    ring
  · apply Finset.prod_congr rfl
    intro j _
    ring

end GlobalTheory
end

