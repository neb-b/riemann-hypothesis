module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBound
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelHeight
open GlobalTheory.HolDict.ShortVec (intRing finPr)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (finCoord)

theorem openSub (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
      (∀ i j k, a i j k ∈ intRing D.host.F) →
      (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
        Module.finBasis D.host.F D.host.E k : WO V W) ∈ U :=
  _root_.GlobalTheory.OpenSubAdele.exists_nat_mul_mem_openAddSubgroup D V W U hU

theorem eq_sum_of_infPart (D : D7) (z : AE D) (hz : infPart D z = 0) :
    z = ∑ k, pairA D.host.F 0 (finCoord D (finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k :=
  _root_.GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero D z hz

theorem exists_denom_mul (D : D7) : ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ k, (e₁ : Af D.host.F) * finCoord D a k ∈ intRing D.host.F) →
    (∀ k, (e₂ : Af D.host.F) * finCoord D b k ∈ intRing D.host.F) →
    ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * finCoord D (a * b) k ∈ intRing D.host.F :=
  _root_.GlobalTheory.CoordDenom.finCoord_mul_denom D

theorem exists_denom_integral (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x →
    ∀ k, (d : Af D.host.F) * finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ intRing D.host.F :=
  _root_.GlobalTheory.DenInt.exists_den D

theorem infPart_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) : (finLift z).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] z i j := rfl
  simp only [finLift, Matrix.map_apply, Matrix.zero_apply]
  rw [h1, TensorProduct.zero_tmul]

theorem finPr_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) :
    (finLift z).map (finPr D) = z.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  ext i j
  rfl

theorem tmul_natCast_mul {D : D7} (N : ℕ) (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finPr_Y {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (N : ℕ)
    (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) : WO V W).map (finPr D) =
      ((N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e)) *
        P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have e1 : ((N : D.host.E) • x).map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j
    exact tmul_natCast_mul N (x i j)
  have e2 : (P.map (incA D)).map (finPr D) = P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j; rfl
  rw [Matrix.map_mul, finPr_finLift, e1, e2]

theorem finPr_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W).map (finPr D) =
      Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * Y.map (finPr D) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem infPart_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (z : Matrix (Fin W.rank) (Fin r) D.host.E)
    (g : GA D V) (h : GA D W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) (HMul.hMul (finLift z) (P.map (incA D)) : WO V W))
      (Formalism.L2.Theta.mt V g) : WO V W).map (infPart D) = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, infPart_finLift]
  simp

theorem actO_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    actO V W g h (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W) = Y := by
  have e1 : Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [actO, ← Matrix.mul_assoc]
  rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

theorem entry_of_map_eq {m n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Matrix (Fin m) (Fin n) R)
    (c : S) (w : Matrix (Fin m) (Fin n) S) (h : u.map f = c • w) (i : Fin m) (j : Fin n) : f (u i j) = c * w i j := by
  have := congrFun (congrFun h i) j
  simpa using this

theorem openSubY (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U := by
  obtain ⟨M₀, hM₀, hsub⟩ := openSub D V W U hU
  refine ⟨M₀, hM₀, fun y hy hc => ?_⟩
  choose b hb hbe using hc
  convert hsub b hb using 1
  ext i j
  rw [Matrix.of_apply, eq_sum_of_infPart D (y i j) (by simpa using congrFun (congrFun hy i) j)]
  exact Finset.sum_congr rfl fun k _ => by rw [hbe]

def Den (D : D7) (e : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  ∀ k, (e : Af D.host.F) * finCoord D z k ∈ intRing D.host.F

theorem den_sum {D : D7} {e : ℕ} {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ i ∈ s, Den D e (f i)) : Den D e (∑ i ∈ s, f i) := fun k => by
  unfold finCoord
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  exact (intRing D.host.F).sum_mem fun i hi => h i hi k

theorem den_matMul {D : D7} {c : ℕ} (hc : ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
      Den D e₁ a → Den D e₂ b → Den D (c * e₁ * e₂) (a * b)) {m n p : ℕ} {e₁ e₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (B : Matrix (Fin n) (Fin p) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hA : ∀ i j, Den D e₁ (A i j)) (hB : ∀ i j, Den D e₂ (B i j)) : ∀ i j, Den D (c * e₁ * e₂) ((A * B) i j) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact den_sum _ _ fun l _ => hc e₁ e₂ _ _ (hA i l) (hB l j)

theorem finCoord_natCast_mul (D : D7) (N : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k) :
    finCoord D ((N : Af D.host.F ⊗[D.host.F] D.host.E) * z) k = (N : Af D.host.F) * finCoord D z k := by
  unfold finCoord
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem exists_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (U : AddSubgroup (WO V W))
    {M₀ : ℕ} (hsub : ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U)
    (D' : ℕ) (g : GA D V) (h : GA D W) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    (hden : ∀ i j, Den D D' ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) i j)) :
    ∃ u ∈ U, u.map (infPart D) = 0 ∧
      actO V W g h u = HMul.hMul (finLift (((M₀ * D' : ℕ) : D.host.E) • x)) (P.map (incA D)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M₀ * D' := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨wf, hwf⟩ : ∃ wf : Matrix (Fin W.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E),
    wf = Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := ⟨_, rfl⟩
  rw [← hwf] at hden
  obtain ⟨Y, hY⟩ : ∃ Y : WO V W, Y = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : WO V W, u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) := ⟨_, rfl⟩
  have hinf : u.map (infPart D) = 0 := by
    rw [hu, hY]; exact infPart_u P _ g h
  have hfin : u.map (finPr D) = (N : Af D.host.F ⊗[D.host.F] D.host.E) • wf := by
    rw [hu, finPr_u, hY, finPr_Y, hwf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨u, ?_, hinf, ?_⟩
  · refine hsub u hinf fun i j k => ⟨_, hden i j k, ?_⟩
    rw [entry_of_map_eq (finPr D) u _ wf hfin i j, finCoord_natCast_mul, hN, Nat.cast_mul, mul_assoc]
  · rw [hu, actO_u]
    exact hY

theorem levelheight : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ,
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W),
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧
    ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U,
      u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  intro D V W r P
  refine ⟨1, fun U hU => ?_⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨CV, hCV, hcV⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨CW, hCW, hcW⟩ := GlobalTheory.Grow.height_comparison W hθ
  obtain ⟨M₀, hM₀, hsub⟩ := openSubY D V W U hU
  obtain ⟨c, hc0, hc⟩ := exists_denom_mul D
  obtain ⟨dx, hdx, hx⟩ := exists_denom_integral D
  obtain ⟨dP, hdP, hP⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (intRing D.host.F)
    (fun q : Fin r × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] P q.1 q.2.1) q.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  set nV := ⌈CV⌉₊ with hnV
  set nW := ⌈CW⌉₊ with hnW
  have hnV0 : 0 < nV := Nat.ceil_pos.2 hCV
  have hnW0 : 0 < nW := Nat.ceil_pos.2 hCW
  refine ⟨M₀ * c ^ 3 * dx * dP * nW * nV, by positivity, fun g h => ?_⟩
  obtain ⟨dh, hdh0, hdhH, hdh⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := W) h⁻¹
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  set D' := c * (c * (c * dh * dx) * dP) * dg with hD'
  refine ⟨M₀ * D', by positivity, ?_, fun x hxi => ?_⟩
  ·
    have h1 : (dh : ℝ) ≤ nW * GlobalTheory.Grow.height W h := by
      have := (hcW h⁻¹).1
      rw [GlobalTheory.Grow.height_inv] at this
      exact hdhH.trans (this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _)
        (GlobalTheory.Grow.height_pos W h).le))
    have h2 : (dg : ℝ) ≤ nV * GlobalTheory.Grow.height V g :=
      hdgH.trans ((hcV g).1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (GlobalTheory.Grow.height_pos V g).le))
    rw [pow_one, hD']
    push_cast
    have hpos : (0 : ℝ) ≤ M₀ * c ^ 3 * dx * dP := by positivity
    calc (M₀ : ℝ) * (c * (c * (c * dh * dx) * dP) * dg) = (M₀ * c ^ 3 * dx * dP) * (dh * dg) := by ring
      _ ≤ (M₀ * c ^ 3 * dx * dP) * ((nW * GlobalTheory.Grow.height W h) * (nV * GlobalTheory.Grow.height V g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (mul_nonneg (by positivity) (GlobalTheory.Grow.height_pos W h).le)) hpos
      _ = _ := by ring
  · exact exists_u P U hsub _ g h x (by
      rw [hD']
      refine den_matMul hc _ _ (den_matMul hc _ _ (den_matMul hc _ _ (fun i j => hdh i j) ?_) ?_) (fun i j => hdg i j)
      · intro i j; exact hx _ (hxi i j)
      · intro i j k; exact hP (i, j, k))
end GlobalTheory.LevelHeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTrivialBoundInertPlaceUnitarisableSpherica
section
noncomputable section

namespace GlobalTheory.SatBoundInert

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

theorem norm_form_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hpos : ∀ v, v ≠ 0 → 0 < (B v v).re) (u v : V)
    (h : B u u = B v v) : ‖B u v‖ ≤ (B v v).re := by
  have hnn : ∀ z, 0 ≤ (B z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hpos z hz).le
  by_cases h0 : B u v = 0
  · rw [h0, norm_zero]; exact hnn v
  have hn : (‖B u v‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h0)
  have hz := hnn (u - (B u v / (‖B u v‖ : ℂ)) • v)
  have e : B (u - (B u v / (‖B u v‖ : ℂ)) • v) (u - (B u v / (‖B u v‖ : ℂ)) • v) =
      B u u - starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v - (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) +
        (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B v v := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul]
    rw [hsym u v]
    ring
  have h1 : starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) * B u v = ‖B u v‖ := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have h2 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v) = ‖B u v‖ := by
    rw [div_mul_eq_mul_div, Complex.mul_conj', sq]
    field_simp
  have h3 : (B u v / (‖B u v‖ : ℂ)) * starRingEnd ℂ (B u v / (‖B u v‖ : ℂ)) = 1 := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', sq]
    field_simp
  rw [e, h1, h2, h3, h] at hz
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, one_mul] at hz
  linarith

theorem satakeBoundInert : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.SatakeBoundInert := by
  intro L _ _ _ ϖ σ q n hU V _ _ π α _ hun hsat
  obtain ⟨B, hsym, hpos, hinv⟩ := hun
  obtain ⟨x, hx⟩ := hsat.exists_vec
  have hxx : B x x ≠ 0 := fun h => by
    have := hpos x hx.1
    rw [h] at this
    simp at this
  let c : ℂ := (B x x)⁻¹
  let l : V →ₗ[ℂ] ℂ :=
    { toFun := fun y => B y x * c
      map_add' := fun a b => by simp [add_mul]
      map_smul' := fun a y => by simp [mul_assoc] }
  have hl : ∀ k ∈ KU σ n, ∀ y, l (π k y) = l y := fun k hk y => by
    show B (π k y) x * c = B y x * c
    conv_lhs => rw [← GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk]
    rw [hinv]
  have h1 : l x = 1 := mul_inv_cancel₀ hxx
  have hz := GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.isZonal_of_isSatVecU hU hx l hl h1
  have hϖ : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  refine _root_.GlobalTheory.ZonalBound.trivialBound_of_bounded GlobalTheory.InertZeta.unramDoublingInert L (Units.mk0 ϖ hϖ) σ q n hU α _ hz ⟨(B x x).re * ‖c‖, fun g => ?_⟩
  show ‖B (π g x) x * c‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_form_le B hsym hpos _ _ (hinv g x x)) (norm_nonneg _)

end GlobalTheory.SatBoundInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticRestrictionIsotropicPartEqPairing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}

private theorem sum_comm_three_reverse {M ι κ μ : Type*} [AddCommMonoid M] [Fintype ι] [Fintype κ] [Fintype μ]
    (f : ι → κ → μ → M) : ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k :=
  calc ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, f i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D)).transpose * (T.gram).map (incA D) * x) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (sum_comm_three_reverse _).trans ?_
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring

theorem halfPair_eq_trace (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) :
    halfPair W a t = Matrix.trace ((a.map (cA D)).transpose * (W.gram).map (incA D) * t) := by
  unfold halfPair
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem map_cA_isoMat_transpose (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Matrix.transpose (((adj D C * V.gram).map (incA D)).map (cA D)) = (V.gram * C).map (incA D) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  congr 1
  simp only [Matrix.mul_apply, star_sum, star_mul', adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    GlobalTheory.BesselCompare.sig_eq, star_star, GlobalTheory.DualPairCheck.gram_star]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sympl_restEmb_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  intro D V V' W r C B _ K hK a t
  have hG : IsUnit V.gram.det := GlobalTheory.LatVac.gram_det_isUnit V
  have h1 : K * V.gram⁻¹ * (V.gram * C) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul, hK]
  have key : K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D) = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  suffices h : hO V W (restEmb V W K t) (isoPart V W C a) = halfPair W a t by
    unfold symplO halfSympl
    rw [h]
  have e1 : (isoPart V W C a).map (cA D) = a.map (cA D) * ((adj D C * V.gram).map (incA D)).map (cA D) := by
    unfold isoPart
    exact Matrix.map_mul
  have e2 : restEmb V W K t = (t : Matrix (Fin W.rank) (Fin r) (AE D)) * K.map (incA D) := rfl
  rw [hO_eq_trace, halfPair_eq_trace, e1, Matrix.transpose_mul, map_cA_isoMat_transpose, e2]
  calc _ = Matrix.trace ((K.map (incA D) * (V.gram⁻¹).map (incA D) * (V.gram * C).map (incA D)) *
        ((a.map (cA D)).transpose * (W.gram).map (incA D) * t)) := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm (K.map (incA D))]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key, Matrix.one_mul]

end GlobalTheory.HalfAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridRowZeroVerticesAgreeWeilData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem lattice_heq_of_eq_hermitianSpaceWithLattice_mk {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)}
    (e : x = ⟨s, l⟩) : HEq l x.lat := by subst e; rfl

theorem nodeAgree_grid0_of_weil_over : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW j hj
  rcases Nat.lt_or_ge j D.R.m with h | h
  · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
    have e : G'.node (.grid 0 j) = ⟨Yc D j, R.ΛY j⟩ := colY_lt R.toLevCh h
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, (hW.cartY j h).symm, (hW.onbY j h).symm⟩
  · obtain rfl : j = D.R.m := le_antisymm hj h
    rw [← nodeX_eq_chainVertexAtRowZero_top R]
    have e : G'.node (.grid 0 D.R.m) = ⟨D.sp.X', R.ΛX⟩ := colY_m R.toLevCh
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, hW.cartX.symm, hW.onbX.symm⟩

end GlobalTheory.GridJoin
end
end

