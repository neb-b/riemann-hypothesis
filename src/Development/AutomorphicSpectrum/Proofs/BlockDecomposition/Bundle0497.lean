module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBound
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCount

theorem exists_cone_lower (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ l : ℝ, 0 < l ∧ ∀ t ∈ cone r c, ∀ i, l ≤ t i := by
  set c' : ℝ := min c 1 with hc'
  have h0 : 0 < c' := lt_min hc one_pos
  have h1 : c' ≤ 1 := min_le_right _ _
  have h2 : c' ≤ c := min_le_left _ _
  have key : ∀ t ∈ cone r c, ∀ (m : ℕ) (i : Fin r), i.val + m + 1 = r → c' ^ (m + 1) ≤ t i := by
    intro t ht m
    induction m with
    | zero =>
      intro i hi
      simpa using h2.trans (ht.2.2 i (by omega))
    | succ m ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have a1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have a2 := ht.2.1 i ⟨i.val + 1, hj⟩ rfl
      have a3 : 0 < t ⟨i.val + 1, hj⟩ := ht.1 _
      calc c' ^ (m + 1 + 1) = c' * c' ^ (m + 1) := by ring
        _ ≤ c' * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ c * t ⟨i.val + 1, hj⟩ := by gcongr
        _ ≤ t i := a2
  refine ⟨c' ^ r, by positivity, fun t ht i => ?_⟩
  have hi := i.2
  obtain ⟨m, hm⟩ : ∃ m, i.val + m + 1 = r := ⟨r - i.val - 1, by omega⟩
  exact (pow_le_pow_of_le_one h0.le h1 (by omega)).trans (key t ht m i hm)

theorem le_prod_max {r : ℕ} (t : Fin r → ℝ) (i : Fin r) : max (t i) 1 ≤ ∏ k, max (t k) 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod₀ fun v _ => le_max_right _ _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem eq_of_act (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ)
    (hX : M * X.map τ = X.map τ * diagonal u) (hY : M * Y.map τ = Y.map τ * diagonal v)
    (hZ : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) :
    M = X.map τ * diagonal u * (Formalism.UG.cT (σ : E →+* E) Y * J).map τ +
      Y.map τ * diagonal v * (Formalism.UG.cT (σ : E →+* E) X * J).map τ +
      (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ := by
  set Ax := Formalism.UG.cT (σ : E →+* E) X * J with hAx
  set Ay := Formalism.UG.cT (σ : E →+* E) Y * J with hAy
  have xx : Ax * X = 0 := hW.xx
  have xy : Ax * Y = 1 := hW.xy
  have yy : Ay * Y = 0 := hW.yy
  have yx : Ay * X = 1 := by
    have e := congrArg (Formalism.UG.cT (σ : E →+* E)) hW.xy
    have cc : ∀ Z : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) Z) = Z :=
      fun Z => Matrix.ext fun i j => sigma_sigma h _
    have hJ' : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ', Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
  set P := 1 - X * Ay - Y * Ax with hP
  have hxP : Ax * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, xx, xy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hyP : Ay * P = 0 := by
    simp only [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, yx, yy, Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hMP : M * P.map τ = P.map τ := by
    ext i j
    have e := hZ (fun a => P a j) (funext fun k => congrFun (congrFun hxP k) j) (funext fun k => congrFun (congrFun hyP k) j)
    exact congrFun e i
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = X.map τ * Ay.map τ + Y.map τ * Ax.map τ + P.map τ := by
    have : (1 : Matrix (Fin n) (Fin n) E) = X * Ay + Y * Ax + P := by simp [hP]
    have e := congrArg (fun A : Matrix (Fin n) (Fin n) E => A.map τ) this
    simpa [Matrix.map_add (f := _), Matrix.map_mul, Matrix.map_one] using e
  calc M = M * 1 := (Matrix.mul_one _).symm
    _ = _ := by
      rw [h1, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hX, hY, hMP]

theorem exists_entry_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Matrix (Fin n) (Fin n) ℂ) (u v : Fin r → ℂ) (S : ℝ), 1 ≤ S → (∀ k, ‖u k‖ ≤ S) →
      (∀ k, ‖v k‖ ≤ S) → M * X.map τ = X.map τ * diagonal u → M * Y.map τ = Y.map τ * diagonal v →
      (∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
        M *ᵥ (fun i => τ (z i)) = fun i => τ (z i)) → ∀ i j, ‖M i j‖ ≤ c * S := by
  set A := X.map τ
  set A' := Y.map τ
  set B := (Formalism.UG.cT (σ : E →+* E) Y * J).map τ
  set B' := (Formalism.UG.cT (σ : E →+* E) X * J).map τ
  set Q := (1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)).map τ
  let f : Fin n → Fin n → ℝ := fun i j => ∑ k, ‖A i k‖ * ‖B k j‖ + ∑ k, ‖A' i k‖ * ‖B' k j‖ + ‖Q i j‖
  have hf : ∀ i j, 0 ≤ f i j := fun i j => by positivity
  refine ⟨∑ i, ∑ j, f i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hf i j,
    fun M u v S hS hu hv hX hY hZ i j => ?_⟩
  have hd : ∀ (P : Matrix (Fin n) (Fin r) ℂ) (R : Matrix (Fin r) (Fin n) ℂ) (d : Fin r → ℂ), (∀ k, ‖d k‖ ≤ S) →
      ‖(P * diagonal d * R) i j‖ ≤ (∑ k, ‖P i k‖ * ‖R k j‖) * S := fun P R d hd => by
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [Matrix.mul_diagonal, norm_mul, norm_mul]
    have := hd k
    calc ‖P i k‖ * ‖d k‖ * ‖R k j‖ ≤ ‖P i k‖ * S * ‖R k j‖ := by gcongr
      _ = _ := by ring
  have e := eq_of_act h hJ hW τ M u v hX hY hZ
  have h1 : ‖M i j‖ ≤ f i j * S := by
    rw [e, Matrix.add_apply, Matrix.add_apply]
    refine (norm_add₃_le).trans ?_
    have := hd A B u hu
    have := hd A' B' v hv
    have hq : ‖Q i j‖ ≤ ‖Q i j‖ * S := le_mul_of_one_le_right (norm_nonneg _) hS
    simp only [f, add_mul]
    linarith
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hf i j) (Finset.mem_univ i))
  exact Finset.single_le_sum (fun j _ => hf i j) (Finset.mem_univ j)

theorem exists_torus_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J) (S : ℝ), (∀ k, 0 < t k) → 1 ≤ S → (∀ k, t k ≤ S) →
      (∀ k, (t k)⁻¹ ≤ S) → IsTorusElt σ J X Y t a → ∀ i j,
        ‖archMat σ J τ (projArch σ J w a) i j‖ ≤ c * S ∧ ‖archMat σ J τ (projArch σ J w a⁻¹) i j‖ ≤ c * S := by
  obtain ⟨c, hc, hb⟩ := exists_entry_bound h hJ hW τ.1
  refine ⟨c, hc, fun t a S ht hS h1 h2 ha i j => ?_⟩
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  set M := archMat σ J τ (projArch σ J w a) with hM
  set M' := archMat σ J τ (projArch σ J w a⁻¹) with hM'
  have hMM : M' * M = 1 := by
    rw [hM, hM', ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hn : ∀ k, ‖(t k : ℂ)‖ ≤ S := fun k => by
    rw [Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h1 k
  have hn' : ∀ k, ‖(t k : ℂ)⁻¹‖ ≤ S := fun k => by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (ht k).le]; exact h2 k
  have hD : diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => mul_inv_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hD' : diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun k => inv_mul_cancel₀ (by exact_mod_cast (ht k).ne'))
  have hX' : M' * X.map τ.1 = X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
    calc M' * X.map τ.1 = M' * (X.map τ.1 * (diagonal (fun i => (t i : ℂ)) * diagonal (fun i => (t i : ℂ)⁻¹))) := by
          rw [hD, Matrix.mul_one]
      _ = (M' * M) * X.map τ.1 * diagonal (fun i => (t i : ℂ)⁻¹) := by
          rw [Matrix.mul_assoc M', hX]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hY' : M' * Y.map τ.1 = Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
    calc M' * Y.map τ.1 = M' * (Y.map τ.1 * (diagonal (fun i => (t i : ℂ)⁻¹) * diagonal (fun i => (t i : ℂ)))) := by
          rw [hD', Matrix.mul_one]
      _ = (M' * M) * Y.map τ.1 * diagonal (fun i => (t i : ℂ)) := by
          rw [Matrix.mul_assoc M', hY]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hMM, Matrix.one_mul]
  have hZ' : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M' *ᵥ (fun i => τ.1 (z i)) = fun i => τ.1 (z i) := fun z z1 z2 => by
    conv_lhs => rw [← hZ z z1 z2]
    rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  exact ⟨hb M _ _ S hS hn hn' hX hY hZ i j, hb M' _ _ S hS hn' hn hX' hY' hZ' i j⟩

theorem torus_count : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ c : ℝ, 0 < c → ∀ C : Set (GA D V), IsCompact C →
    ∃ (A : ℕ) (B : ℝ), ∀ t ∈ cone r c, ∀ a : GA D V, IsTorusElt D.sp.cm.sig V.gram X Y t a →
      {δ : GF V | a⁻¹ * rat V δ * a ∈ C}.Finite ∧
      (({δ : GF V | a⁻¹ * rat V δ * a ∈ C}.ncard : ℕ) : ℝ) ≤ B * (∏ i, max (t i) 1) ^ A := by
  intro D V r X Y hW c hc C hC
  obtain ⟨hcm, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  let θ : Formalism.IndefR.Datum.InfFam D := fun ρ => infProj (embOverOf D ρ)
  have hθ : IsInfFam θ := isInfFam_infProj D
  obtain ⟨N, hN⟩ := GlobalTheory.RatCount.ncard_rational_le D θ V hθ C hC
  obtain ⟨C₀, hC₀⟩ := hN 1
  obtain ⟨l, hl, hlow⟩ := exists_cone_lower r hc
  choose cb hcb0 hcb using fun ρ => exists_torus_bound hcm (hJ V) hW (embOverOf D ρ)
  set K : ℝ := ∑ ρ, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (cb ρ + cb ρ) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun ρ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (hcb0 ρ) (hcb0 ρ)
  set L : ℝ := max 1 l⁻¹ with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  refine ⟨N, |C₀| * (K * L) ^ N, fun t ht a ha => ?_⟩
  set T : ℝ := ∏ i, max (t i) 1 with hT
  have hT1 : 1 ≤ T := Finset.one_le_prod₀ fun v _ => le_max_right _ _
  have hS1 : 1 ≤ L * T := one_le_mul_of_one_le_of_one_le hL1 hT1
  have hs1 : ∀ k, t k ≤ L * T := fun k =>
    ((le_max_left _ _).trans (le_prod_max t k)).trans (le_mul_of_one_le_left (by linarith) hL1)
  have hs2 : ∀ k, (t k)⁻¹ ≤ L * T := fun k =>
    ((inv_anti₀ hl (hlow t ht k)).trans (le_max_right _ _)).trans (le_mul_of_one_le_right (by linarith) hT1)
  have hnorm : Formalism.L2.Theta.normInf θ V a ≤ K * (L * T) := by
    unfold Formalism.L2.Theta.normInf
    rw [hK, Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hb := hcb ρ t a (L * T) ht.1 hS1 hs1 hs2 ha i j
    have e : ∀ g : GA D V, Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) g =
        archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) g) := fun g =>
      infMat_infProj V.gram hcm (embOverOf D ρ) g
    rw [e, e, add_mul]
    exact add_le_add hb.1 hb.2
  have h0 := GlobalTheory.RatCount.normInf_nonneg θ V a
  have hsub : rat V '' {δ : GF V | a⁻¹ * rat V δ * a ∈ C} ⊆
      {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o} := by
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨?_, _, hδ, by group⟩
    exact (range_ratEmb D.sp.cm.sig V.gram).le ⟨δ, rfl⟩
  obtain ⟨hf, hcard⟩ := hC₀ a ha.1 a
  have hinj : Function.Injective (rat V) := ratEmb_injective _ _
  refine ⟨Set.Finite.of_finite_image (hf.subset hsub) hinj.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective _ hinj]
  calc _ ≤ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ C, γ * a = 1 * a * o}.ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub hf
    _ ≤ _ := by simpa using hcard
    _ ≤ |C₀| * Formalism.L2.Theta.normInf θ V a ^ N := by gcongr; exact le_abs_self _
    _ ≤ |C₀| * (K * (L * T)) ^ N := by gcongr
    _ = _ := by rw [mul_assoc, mul_pow, mul_pow]; ring

end GlobalTheory.CompanionTheory.TorusCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
namespace GlobalTheory.CompanionTheory.GrCech

theorem capO_affine {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) (n : ℕ)
    (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

theorem inU_capO {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have h := _root_.GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (γ := γ) (p := p) (q := q) (κ := κ) (fun a => U (i a)) Finset.univ T
  simpa [capO] using h

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  refine propext ⟨fun h => ⟨(h 0).1, capO U i, rfl, (inU_capO U i T).2 fun a => ?_⟩, ?_⟩
  · obtain ⟨-, V, hV, hT⟩ := h a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact hT
  · rintro ⟨hq, V, hV, hT⟩ a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, _, rfl, (inU_capO U i T).1 hT a⟩

end GlobalTheory.CompanionTheory.GrCech

namespace GlobalTheory.CompanionTheory.GrCech

theorem inU_mono {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {V W : X.Opens} (h : V ≤ W) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) : InU W T :=
  fun x hx => h (hT hx)

theorem vb_cech (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (r : ℕ) (hr : r < s) :
    Nonempty (VB (fun W : X.Opens => strV q W) U.U (CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r)) := by
  classical
  have isF : ∀ Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), IsFil (sP Q) (sFil Q) :=
    fun Q => _root_.GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  choose ω hω using fun α => _root_.GlobalTheory.CompanionTheory.GrCech.Omega.basis hLoc hPoly l s hb q (U.c α) r hr
  have hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), capT (fun α => St (TF l s) {U.U α}) i T → InU (capO U.U i) T := by
    intro n i T h
    rw [capT_eq] at h
    obtain ⟨-, V, hV, hT⟩ := h
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a)} := fun i a T h => h a
  have hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := by
    intro α β
    have h := U.inter {α, β} ⟨α, by simp⟩
    have e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β := by
      rw [Finset.iInf_insert, Finset.iInf_singleton]
    rwa [e] at h
  have hl2 : ∀ {V W : X.Opens} (h : V ≤ W), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} ≤ St (TF l s) {W} := by
    rintro V W h T ⟨hq, V', hV, hT⟩
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, W, rfl, inU_mono h hT⟩
  have hq2 : ∀ {V : X.Opens} (T), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} T → InU V T := by
    rintro V T ⟨hq, V', hV, hT⟩
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hg0 := fun α β (k' : Idx r (U.d β)) => (hω α (U.U α ⊓ U.U β) (hpair α β) inf_le_left _ rfl (hl2 inf_le_left) (isF _) hq2
    ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists
  choose g' hg' using hg0
  refine GlobalTheory.T.cover_cup_action_basis (fun W => strV q W) _ U.U _ r (fun α => Idx r (U.d α))
    (fun i => fHom (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k)
    ?_ ?_ ?_ ?_ ?_
  · intro n i a h
    exact hω (i a) (capO U.U i) (capO_affine U n i) (capO_le U.U i a) _ (capT_eq _ _ i) (hle i a) (isF _) (hT i) h
  · intro n i c h
    exact fAct_str (isF _) (hT i) r c h
  · intro n i j f h
    exact res_fAct (isF _) (hT _) r (isF _) (hT i) (capO_comp U.U i j.succAbove) _ f h
  · intro n i j a k
    exact res_res _ _ _ r _
  · intro n i a a' k'
    have hle2 : capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a) ⊓ U.U (i a')} := by
      intro T h
      exact ⟨(h a).1, _, rfl, le_preimage_inf (pt T) (hq2 T (hle i a T h)) (hq2 T (hle i a' T h))⟩
    have h1 := congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [res_res, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (res_fAct (isF _) hq2 r (isF _) (hT i) (le_inf (capO_le U.U i a) (capO_le U.U i a')) hle2 _ _).trans ?_
    change fAct _ _ r _ _ = fAct _ _ r _ _
    rw [res_res]

theorem main_nl (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ) :
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r).cx.H p) := by
  obtain ⟨V⟩ := vb_cech hLoc hPoly l s hb q U r hr
  exact _root_.GlobalTheory.CompanionTheory.VBGlue.finite_H_cx q U.U U.cover (capO_affine U) _ V p


set_option maxHeartbeats 1000000 in
theorem main_thm : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  intro hLoc hPoly _ _ O _ _ l s hb X q _ U r hr p
  exact main_nl hLoc hPoly l s hb q U r hr p

end GlobalTheory.CompanionTheory.GrCech
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add (f := _), hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add (f := _)]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjectiveStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)),
  ∃ f : XS τ σ, (∀ x ∈ Cl k i t, evX f x = 0) ∧ eO ψ f = (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.onto <;> assumption)
end

