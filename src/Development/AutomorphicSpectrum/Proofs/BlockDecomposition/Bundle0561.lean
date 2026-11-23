module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0536
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliser
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

theorem linearIndependent_mulVec_unit {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact_unitary {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec_unit (g : GL (Fin M) E) hX

theorem gact_inv_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : gact σ w⁻¹ (e0 E M) = e0 E M := by
  conv_lhs => rw [← hw]
  exact gact_inv_gact σ w _

theorem gact_zero_of_first {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (w : UJ (σ : E →+* E) (hypOne J))
    {X : Fin (n + 1) → Fin (M + 2) → E} (hX : X 0 = e0 E M 0) :
    gact σ w X 0 = gact σ w (e0 E M) 0 := by
  change ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X 0 =
    ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ e0 E M 0
  rw [hX]

theorem gact_mem_framesOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) {X : Fin (n + 1) → Fin (M + 2) → E}
    (hX : X ∈ framesOne σ J n) : gact σ w X ∈ framesOne σ J n := by
  refine ⟨⟨linearIndependent_gact_unitary σ w hX.1.1, ?_⟩, ?_⟩
  · rw [gramE_gact]; exact hX.1.2
  · rw [gact_zero_of_first σ w hX.2, hw]

def framesOneEquiv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (n : ℕ) {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : framesOne σ J n ≃ framesOne σ J n where
  toFun X := ⟨gact σ w X.1, gact_mem_framesOne σ hw X.2⟩
  invFun X := ⟨gact σ w⁻¹ X.1, gact_mem_framesOne σ (gact_inv_e0 σ hw) X.2⟩
  left_inv X := Subtype.ext (gact_inv_gact σ w X.1)
  right_inv X := Subtype.ext (gact_gact_inv σ w X.1)

theorem tsum_gact_framesOne (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J))
    (hw : gact σ w (e0 E M) = e0 E M) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞) :
    ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 :=
  (framesOneEquiv σ n hw).tsum_eq (fun X => f X.1)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrame
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_add_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J x (y + z) = hE σ J x y + hE σ J x z := by
  simp [hE, hform, mul_add, Finset.sum_add_distrib]

theorem hE_add_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y z : Fin M → E) :
    hE σ J (x + y) z = hE σ J x z + hE σ J y z := by
  simp [hE, hform, add_mul, Finset.sum_add_distrib]

theorem hE_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J x (c • y) = c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : E)
    (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by
  simp only [hE, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul,
    AlgHom.coe_toRingHom, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_herm (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (y z : Fin M → E) : σ (hE σ J y z) = hE σ J z y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem exists_partner [CharZero E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {N : ℕ}
    (K : Matrix (Fin N) (Fin N) E) (hK : IsHermND σ K) (x : Fin N → E) (hx0 : x ≠ 0)
    (hxx : hE σ K x x = 0) : ∃ y, hE σ K x y = 1 ∧ hE σ K y y = 0 := by
  have hherm := hE_herm σ hσ K hK.1
  have hex : ∃ y₀, hE σ K x y₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hv : Matrix.vecMul (fun i => σ (x i)) K = 0 := by
      funext j
      have := hall (Pi.single j 1)
      simpa [hE, hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hz : (fun i => σ (x i)) = 0 := by
      have hu : IsUnit K := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hK.2)
      exact (Matrix.vecMul_injective_of_isUnit hu) (by simpa using hv)
    apply hx0
    funext i
    have h := congrArg σ (congrFun hz i)
    simpa [hσ] using h
  obtain ⟨y₀, hy₀⟩ := hex
  obtain ⟨y₁, hxy₁⟩ : ∃ y₁, hE σ K x y₁ = 1 :=
    ⟨(hE σ K x y₀)⁻¹ • y₀, by rw [hE_smul_right]; exact inv_mul_cancel₀ hy₀⟩
  have hy₁x : hE σ K y₁ x = 1 := by rw [← hherm, hxy₁, map_one]
  obtain ⟨q, hq⟩ : ∃ q, q = hE σ K y₁ y₁ := ⟨_, rfl⟩
  have hqs : σ q = q := by rw [hq]; exact hherm _ _
  obtain ⟨y, hy⟩ : ∃ y : Fin N → E, y = y₁ + (-(q / 2)) • x := ⟨_, rfl⟩
  have hxy : hE σ K x y = 1 := by
    rw [hy, hE_add_right, hE_smul_right, hxy₁, hxx]; simp
  have hyy : hE σ K y y = 0 := by
    have hs2 : σ (-(q / 2)) = -(q / 2) := by
      rw [map_neg, map_div₀, hqs, map_ofNat]
    rw [hy, hE_add_right, hE_add_left, hE_add_left, hE_smul_right, hE_smul_right, hE_smul_left,
      hE_smul_left, hs2, hy₁x, hxy₁, hxx, ← hq]
    field_simp
    ring
  exact ⟨y, hxy, hyy⟩

theorem gramE_pair (σ : E →ₐ[F] E) {N : ℕ} (K : Matrix (Fin N) (Fin N) E) (u v : Fin N → E)
    (h1 : hE σ K u u = 0) (h2 : hE σ K u v = 1) (h3 : hE σ K v u = 1) (h4 : hE σ K v v = 0) :
    gramE σ K ![u, v] = !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gramE, h1, h2, h3, h4]

theorem hE_hypOne_basis (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 1 fun _ => 0) = 0 ∧
    hE σ (hypOne J) (Fin.cons 1 fun _ => 0) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 1 fun _ => 0) = 1 ∧
    hE σ (hypOne J) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) (Fin.cons 0 (Fin.cons 1 fun _ => 0)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [hE, hform, Fin.sum_univ_succ, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one]

end Alg

theorem exists_unitary_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  intro F E _ _ _ _ _ σ hCM M J hJ q hq
  obtain ⟨hσ, -⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hCM
  have hK := isHermND_hypOne σ hJ
  obtain ⟨hli, hg⟩ := hq
  have hx0 : q 0 ≠ 0 := hli.ne_zero 0
  have hxx : hE σ (hypOne J) (q 0) (q 0) = 0 := congrFun (congrFun hg 0) 0
  obtain ⟨y, hxy, hyy⟩ := exists_partner σ hσ (hypOne J) hK (q 0) hx0 hxx
  have hyx : hE σ (hypOne J) y (q 0) = 1 := by
    rw [← hE_herm σ hσ _ hK.1, hxy, map_one]
  obtain ⟨b1, b2, b3, b4⟩ := hE_hypOne_basis σ J
  have hX := gramE_pair σ (hypOne J) (q 0) y hxx hxy hyx hyy
  have hY := gramE_pair σ (hypOne J) _ _ b1 b2 b3 b4
  obtain ⟨g, hgU, hgX⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittE.witt_tuple F E σ hCM (M + 2) (hypOne J) hK 2 _ _ (hX.trans hY.symm)
    (by rw [hX]; simp [Matrix.det_fin_two_of])
  refine ⟨⟨g, hgU⟩, ?_⟩
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  exact hgX 0

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependentStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_set_compact_linearly_independent : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentities
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem sand {k l a b c : ℕ} (G : Mx D k k) (x : Mx D k l) (u : Mx D l a) (y : Mx D k b) (v : Mx D b c) :
    adj (x ⬝ u) ⬝ (G ⬝ (y ⬝ v)) = adj u ⬝ ((adj x ⬝ (G ⬝ y)) ⬝ v) := by
  simp only [adj_mul, Matrix.mul_assoc]

theorem gram_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) :
    adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h) = rat (gramQ W x₀) := by
  have hu := mt_unitary W h⁻¹
  have hr : adj (rat x₀) ⬝ (gA W ⬝ rat x₀) = rat (gramQ W x₀) :=
    gram_rat W (a := x₀) (b := x₀) (c := gramQ W x₀) (by
      show x₀ᴴ * W.gram * x₀ = x₀ᴴ * (W.gram * x₀)
      rw [Matrix.mul_assoc])
  have e : adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h)
      = adj (rat x₀) ⬝ ((adj (mt W h⁻¹) ⬝ (gA W ⬝ mt W h⁻¹)) ⬝ rat x₀) :=
    sand (gA W) (mt W h⁻¹) (rat x₀) (mt W h⁻¹) (rat x₀)
  rw [e, hu, hr]

theorem frame_perp (d : HypDec B W t) {a c : ℕ} (u : Mx D t a) (w : Mx D W.rank a) (v : Mx D t c) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
  rw [adj_add, Matrix.add_mul, sand, sand, d.gram_XX, d.gram_0X]
  simp

theorem frame_gram (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ u + d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
  have h1 := frame_perp d u w u
  have h2 : adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
    rw [adj_add, Matrix.add_mul, sand, sand, d.wittDecomp_gram_X_anisotropic, d.gram_00]
    simp
  rw [Matrix.mul_add, Matrix.mul_add, h1, h2, zero_add]

theorem pair_gram (d : HypDec B W t) (b₀ : HermE D W.rank) (hdet : b₀.1.det ≠ 0) (ξ : Mx D B.rank W.rank) (v : Mx D t t)
    (y : Mx D W.rank t) (hg : adj ξ ⬝ (gA B ⬝ ξ) = rat b₀.1) (hp : adj ξ ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0) :
    yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y ∧ qv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = 0 := by
  have h2 : adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = rat b₀.1 ⬝ y := by
    rw [Matrix.mul_add, Matrix.mul_add, hp, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj ξ), hg]
  have hinv : rat b₀.1⁻¹ ⬝ rat b₀.1 = (1 : Mx D W.rank W.rank) := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), rat_one]
  have h3 : yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y := by
    show rat b₀.1⁻¹ ⬝ (adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v))) = y
    rw [h2, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hxξ : adj (d.jX ⬝ v) ⬝ (gA B ⬝ ξ) = 0 := by
    have := gram_swap B hp
    rwa [adj_zero] at this
  have hxx : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
    rw [sand, d.gram_XX]
    simp
  have hq : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hxx, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj (d.jX ⬝ v)),
      hxξ, Matrix.zero_mul]
  have h4 : ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v) = adj y ⬝ (rat b₀.1 ⬝ y) := by
    show adj (ξ ⬝ y + d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = _
    rw [adj_add, Matrix.add_mul, hq, add_zero, adj_mul ξ y, Matrix.mul_assoc, h2]
  refine ⟨h3, ?_⟩
  show ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v)
    - pr b₀ (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) = 0
  rw [h3, h4]
  exact sub_eq_zero.2 rfl

theorem zp_eq : ZpEq := by
  intro D n t B W d hn b₀ hdet x₀ hx p
  have hg : adj (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1) ⬝ (gA B ⬝ (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1)) = rat b₀.1 := by
    rw [frame_gram, gram_ww, hx]
  have hp := frame_perp d (c1 hn p.2.1) (ww W x₀ p.1) (c2 hn p.2.1)
  obtain ⟨h3, h5⟩ := pair_gram d b₀ hdet _ (c2 hn p.2.1) p.2.2 hg hp
  exact ⟨hg, h3, h5⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}

theorem hasSatake_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (α : Fin n → ℂˣ)
    (hx : IsSatVecGL w π x (Finset.univ.val.map α)) : GlobalTheory.SmGL.HasSatake π α := by
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  have hq : IsSubquot π (psGL (w.adicCompletion E) α) :=
    GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
      hx.1 y hy hy0 fun f hf => by
        obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
        exact ⟨c, e1, ht f hf c e2⟩
  have hs : IsSpherical π (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩
  exact ⟨hπ.2, hs, (GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff _ _ π α).1 hq⟩

end GlobalTheory.CompanionTheory.SatComp


end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HtRightTranslate

theorem height_mul_le : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H →
    (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  rintro D n H hH ⟨C₀, hC₀, hcov⟩ C hC
  have hcont : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
  have hpos : ∀ g, 0 < (H g : ℝ) := fun g => by exact_mod_cast hH.2.1 g
  have hF : Continuous fun p : G D n × G D n => (H (p.1 * p.2) : ℝ) / (H p.1 : ℝ) :=
    (hcont.comp (continuous_fst.mul continuous_snd)).div (hcont.comp continuous_fst)
      fun p => (hpos p.1).ne'
  obtain ⟨M, hM⟩ := (hC₀.prod hC).bddAbove_image hF.continuousOn
  refine ⟨max M 1, le_max_right _ _, fun c hc x => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := hcov x
  have hb : (H (k * c) : ℝ) / (H k : ℝ) ≤ max M 1 :=
    (hM ⟨(k, c), ⟨hk, hc⟩, rfl⟩).trans (le_max_left _ _)
  have hb' : (H (k * c) : ℝ) ≤ max M 1 * (H k : ℝ) := (div_le_iff₀ (hpos k)).1 hb
  have hl := hH.2.2 q hq (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  rw [mul_assoc, hl (k * c), hl k]
  push_cast
  have hd : (0 : ℝ) ≤ (absA D (Matrix.GeneralLinearGroup.det (HeightExists.leviBlock (D := D) (n := n) ⟨q, hq⟩)) : ℝ) :=
    NNReal.coe_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hb' hd]

end GlobalTheory.CompanionTheory.HtRightTranslate
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSectionSmoothComposition
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.CxSmooth

private theorem analyticAt_of_differentiableOn_open {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h U) {c : Fin n → ℂ} (hc : c ∈ U) :
    AnalyticAt ℂ h c := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have hd : ∀ ζ ∈ Metric.closedBall c r, DifferentiableAt ℂ h ζ :=
    fun ζ hζ => hh.differentiableAt (hU.mem_nhds (hrU hζ))
  have hA : AnalyticAt ℂ (fun w => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ *
      ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd (ReciprocityTheory.AnForm.Osgood.kern c r w)) c :=
    analyticAt_const.mul
      (((ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd).analyticAt _).comp
        (ReciprocityTheory.AnForm.Osgood.kern_analyticAt c hr))
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)
  refine hA.congr ?_
  filter_upwards [Metric.ball_mem_nhds c hr] with w hw
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hr hd hw]
  exact inv_mul_cancel_left₀ h2 (h w)

theorem analyticAt_of_differentiableOn {ι : Type} [Fintype ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : ι → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  classical
  let e := Fintype.equivFin ι
  let φ : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)
  let ψ : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)
  have hφψ : ∀ w, φ (ψ w) = w := fun w => funext fun i => by simp [φ, ψ]
  have hmem : ψ z ∈ φ ⁻¹' U := by
    rw [Set.mem_preimage, hφψ]
    exact hz
  have hA := analyticAt_of_differentiableOn_open (hU.preimage φ.continuous)
    (hf.comp φ.differentiableOn (Set.mapsTo_preimage φ U)) hmem
  have hB := hA.comp (ψ.analyticAt z)
  have heq : (f ∘ ⇑φ) ∘ ⇑ψ = f := funext fun w => by simp only [Function.comp_apply, hφψ]
  rwa [heq] at hB

theorem contDiffAt_comp_of_cInfAt : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} [Fintype ι]
  {T : Set (ι → ℂ)} {s : (ι → ℂ) → CxPts p σ} {f : CxPts p σ → ℝ} {z₀ : ι → ℂ}, IsOpen T → ContinuousOn s T →
  (∀ (W : Y.Opens) (g : Γ(Y, W)), DifferentiableOn ℂ (CxPts.ev p σ W g ∘ s) (T ∩ s ⁻¹' ptsIn p σ W)) →
  z₀ ∈ T → CInfAt f (s z₀) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ s) z₀ := by
  intro k _ Y p σ ι _ T s f z₀ hT hs hd hz h
  obtain ⟨W, ι', _, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hN : IsOpen (T ∩ s ⁻¹' ptsIn p σ W) := hs.isOpen_inter_preimage hT (isOpen_ptsIn W)
  have hzN : z₀ ∈ T ∩ s ⁻¹' ptsIn p σ W := ⟨hz, hyW⟩
  have hG : AnalyticAt ℂ (fun z a => ev p σ W (g a) (s z)) z₀ :=
    analyticAt_pi_iff.2 fun a => analyticAt_of_differentiableOn hN (hd W (g a)) hzN
  have hcont : ContinuousAt s z₀ := hs.continuousAt (hT.mem_nhds hz)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ fun z a => ev p σ W (g a) (s z)) z₀ :=
    (hF.contDiffAt (hO.mem_nhds hmem)).comp z₀ (hG.contDiffAt.restrict_scalars ℝ)
  exact h1.congr_of_eventuallyEq (hev.comp_tendsto hcont)

end GlobalTheory.CompanionTheory.CxSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_sum_nondegenerate_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hypOne_isHermND_and_e0_mem <;> assumption)
end

