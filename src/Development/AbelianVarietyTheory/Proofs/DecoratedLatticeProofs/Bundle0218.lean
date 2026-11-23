module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMaximalCompactUnnComponentStandardCartanIn
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CartanPt

variable {R : Type} [CommRing R] {n : ℕ}

theorem block_matrix_map {S : Type} [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4; rw [← Matrix.fromBlocks_map]; rfl

theorem blkJ_mul : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  have h : Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]
  rw [h]
  change -((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = _
  rw [Matrix.submatrix_one_equiv]

theorem blkJ_transpose : (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0)ᵀ = -blk4 0 1 (-1) 0 := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.transpose_neg]
  change _ = (-(Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)).submatrix _ _
  rw [Matrix.fromBlocks_neg, neg_zero, neg_neg]

theorem blkJ_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero f), Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

def mixJ (n : ℕ) (a j : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  a • (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) + j • blk4 0 1 (-1) 0

theorem mixJ_mul (a j a' j' : R) :
    mixJ n a j * mixJ n a' j' = mixJ n (a * a' - j * j') (a * j' + j * a') := by
  simp only [mixJ, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, blkJ_mul]
  module

theorem mixJ_one : mixJ n (1 : R) 0 = 1 := by simp [mixJ]

theorem mixJ_J : mixJ n (0 : R) 1 = blk4 0 1 (-1) 0 := by simp [mixJ]

theorem mixJ_map {S : Type} [CommRing S] (f : R →+* S) (a j : R) :
    (mixJ n a j).map f = mixJ n (f a) (f j) := by
  unfold mixJ
  rw [← blkJ_map f, ← Matrix.map_one f (map_zero f) (map_one f)]
  ext p q
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]

theorem mixJ_transpose (a j : R) : (mixJ n a j)ᵀ = mixJ n a (-j) := by
  simp [mixJ, Matrix.transpose_add, Matrix.transpose_smul, blkJ_transpose]

theorem cT_mixJ (σ : R →+* R) (a j : R) : Formalism.UG.cT σ (mixJ n a j) = mixJ n (σ a) (-σ j) := by
  rw [Formalism.UG.cT, mixJ_map, mixJ_transpose]

theorem phase (A B t : ℂ) (hB : B ≠ 0) (h1 : A * B * conj B = t) (h2 : A * conj A = 4) :
    A * (1 / 2) = t / (‖t‖ : ℂ) := by
  have hA : ‖A‖ = 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖A‖ ^ 2 = 2 ^ 2 := by
      have : ‖A‖ ^ 2 = 4 := by exact_mod_cast h2
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h3
  have hn : (‖B‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hB
  have ht : ‖t‖ = 2 * ‖B‖ ^ 2 := by
    rw [← h1, norm_mul, norm_mul, Complex.norm_conj, hA]; ring
  rw [ht, ← h1, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

theorem four_iff {S : Type} [CommRing S] (f : R →+* S) (z : R) : f (z - 4) = 0 ↔ f z = 4 := by
  rw [map_sub, map_ofNat, sub_eq_zero]

theorem four_left {S : Type} [CommRing S] (f : R →+* S) {e : R} (z : R) (h : f e = 0) : f (e * (z - 4)) = 0 := by
  rw [map_mul, h, zero_mul]

theorem four_right {S : Type} [CommRing S] (f : R →+* S) (e : R) {z : R} (h : f z = 4) : f (e * (z - 4)) = 0 := by
  rw [map_mul, (four_iff f z).2 h, mul_zero]

theorem alg_phase (c : R →+* R) (hc : ∀ z, c (c z) = z) {e h m : R} {u ε : Rˣ} (he : e * e = e) (hce : c e = e)
    (hε : (ε : R) * u * c u = m) (hm : c m = -m) (hh : 2 * h = 1) (h4 : e * (ε * c ε - 4) = 0) :
    e * (e * ε * h) = e * ε * h ∧ (e * ε * h) * (e * ε * h) = -e ∧ c (e * ε * h) = -(e * ε * h) := by
  have hcε : c ε = -(ε : R) := by
    rw [← hε, map_mul, map_mul, hc] at hm
    have hu : IsUnit ((u : R) * c u) := u.isUnit.mul (u.isUnit.map c)
    refine hu.mul_right_cancel ?_
    linear_combination hm
  have hch : c h = h := by
    have := congrArg c hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination h * this - c h * hh
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ((ε : R) * h) * he
  · linear_combination ((ε : R) ^ 2 * h ^ 2) * he + (e * ε * h ^ 2) * hcε - h ^ 2 * h4 - e * (2 * h + 1) * hh
  · rw [map_mul, map_mul, hce, hcε, hch]; ring

theorem cx_phase (c : R →+* R) (φ : R →+* ℂ) (hφ : ∀ z, φ (c z) = conj (φ z)) {e h m : R} {u ε : Rˣ} (he : φ e = 1)
    (hε : (ε : R) * u * c u = m) (hh : 2 * h = 1) (h4 : φ (ε * c ε) = 4) :
    φ (e * ε * h) = φ m / (‖φ m‖ : ℂ) := by
  have e1 : φ h = 1 / 2 := by
    have := congrArg φ hh
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination (1 / 2) * this
  rw [map_mul, map_mul, he, one_mul, e1]
  refine phase _ (φ u) _ (u.isUnit.map φ).ne_zero ?_ ?_
  · rw [← hφ, ← map_mul, ← map_mul, hε]
  · rw [← hφ, ← map_mul, h4]

theorem mixJ_real (φ : R →+* ℂ) {e j : R} (he : φ e = 1) :
    (mixJ n (1 - e) j).map φ = φ j • blk4 0 1 (-1) 0 := by
  rw [mixJ_map, map_sub, map_one, he, sub_self, mixJ, zero_smul, zero_add]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

omit [NumberField F] [NumberField E] in
theorem sigR_sigR (A : Type) [CommRing A] [Algebra F A] (hσ : ∀ x, σ (σ x) = x) (z : A ⊗[F] E) :
    sigR A σ (sigR A σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

omit [NumberField E] in
theorem sigR_compInf (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    sigR w.Completion σ (compInf F E w z) = compInf F E w (sigR (AF F) σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField F] [NumberField E] in
theorem incl_half [CharZero E] (A : Type) [CommRing A] [Algebra F A] : 2 * inclR (F := F) (E := E) A (1 / 2) = 1 := by
  rw [← map_ofNat (inclR (F := F) (E := E) A) 2, ← map_mul]
  norm_num

theorem exists_point (n : ℕ) {e j : AF F ⊗[F] E} (hee : e * e = e) (hej : e * j = j) (hjj : j * j = -e)
    (hce : sigR (AF F) σ e = e) (hcj : sigR (AF F) σ j = -j) (hef : ∀ v, compFin F E v e = 0) :
    ∃ k ∈ levelAll σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) (stdLattice E (n + n)) 1,
      (AdelicU.matHom _ σ _ k).1 = mixJ n (1 - e) j := by
  have hkk : mixJ n (1 - e) j * mixJ n (1 - e) j = 1 := by
    rw [mixJ_mul, ← mixJ_one]
    congr 1
    · linear_combination hee - hjj
    · linear_combination (-2) * hej
  have hcT : Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) = mixJ n (1 - e) j := by
    rw [cT_mixJ, map_sub, map_one, hce, hcj, neg_neg]
  let kU : GL (Fin (n + n)) (AF F ⊗[F] E) := ⟨mixJ n (1 - e) j, mixJ n (1 - e) j, hkk, hkk⟩
  have hmem : kU ∈ HR (AF F) σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := by
    change Formalism.UG.cT (sigR (AF F) σ) (mixJ n (1 - e) j) * (blk4 0 1 (-1) 0).map (inclR (AF F)) * mixJ n (1 - e) j =
      (blk4 0 1 (-1) 0).map (inclR (AF F))
    rw [hcT, blkJ_map, ← mixJ_J, mixJ_mul, mixJ_mul]
    congr 1
    · linear_combination 2 * hej
    · linear_combination hee - hjj
  let k : GAd σ (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0) := (⟨kU, hmem⟩ : HR (AF F) σ _)
  refine ⟨k, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, rfl⟩
  · have h : (AdelicU.matHom _ σ _ (proj σ _ v k)).1 = 1 := by
      change (mixJ n (1 - e) j).map (compFin F E v) = 1
      rw [mixJ_map, map_sub, map_one, hef, sub_zero, ← hej, map_mul, hef, zero_mul, mixJ_one]
    refine mem_stabLoc.2 fun y => ?_
    rw [h, Matrix.one_mulVec]
  · rw [mem_stabArch, map_one, inv_one, one_mul, mul_one]
    change Formalism.UG.cT (sigR w.Completion σ) ((mixJ n (1 - e) j).map (compInf F E w)) * 1 *
      (mixJ n (1 - e) j).map (compInf F E w) = 1
    rw [Matrix.mul_one]
    nth_rewrite 1 [mixJ_map]
    rw [cT_mixJ, sigR_compInf, sigR_compInf, hcj, map_neg, neg_neg, map_sub (sigR (AF F) σ), map_one, hce,
      ← mixJ_map, ← Matrix.map_mul, hkk, Matrix.map_one _ (map_zero _) (map_one _)]

end Adelic

theorem real_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (z : AE D)
    (hz : ∀ w, compInf D.host.F D.host.E w z = 4) (τ : D.what₂.Tau) : ((θ τ).comp (infPart D)) z = 4 :=
  (four_iff ((θ τ).comp (infPart D)) z).1
    (((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (z - 4)).1
      (fun w => (four_iff (compInf D.host.F D.host.E w) z).2 (hz w)) τ)

theorem idem_four (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) {e z : AE D} (he : finPart D e = 0)
    (hz : ∀ τ, ((θ τ).comp (infPart D)) z = 4) : e * (z - 4) = 0 :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 _
    (fun τ => four_right ((θ τ).comp (infPart D)) e (hz τ)) (four_left (finPart D) z he)

theorem cA_skew (D : D7) (μ : D.host.E) (hμ : IsSkew μ) : cA D (incA D μ) = -incA D μ :=
  (show cA D (incA D μ) = incA D (star μ) from rfl).trans ((congrArg (incA D) hμ.2).trans ((incA D).map_neg μ))

theorem cA_cA (D : D7) (z : AE D) : cA D (cA D z) = z := sigR_sigR D.sp.cm.sig _ (fun x => star_star x) z

theorem exists_phase_adele (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (μ : D.host.E) (hμ : IsSkew μ) :
    ∃ e j : AE D, e * e = e ∧ e * j = j ∧ j * j = -e ∧ cA D e = e ∧ cA D j = -j ∧
      (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ τ, ((θ τ).comp (infPart D)) e = 1) ∧
      ∀ τ, ((θ τ).comp (infPart D)) j = tauE D τ μ / (‖tauE D τ μ‖ : ℂ) := by
  obtain ⟨e, hee, hce, hef, -, hfp, hip⟩ := GlobalTheory.StdUnn.realIdem_exists D
  obtain ⟨-, L2, L3, -⟩ := GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  obtain ⟨u, ε, hεu, -, hε4⟩ := GlobalTheory.StdUnn.exists_scal_real D μ hμ 1
  have h4 := real_four D θ hθ _ hε4
  have hh : 2 * incA D (1 / 2) = 1 := incl_half _
  have h := alg_phase (cA D) (cA_cA D) hee hce hεu (cA_skew D μ hμ) hh (idem_four D θ hθ hfp h4)
  have he1 : ∀ τ, ((θ τ).comp (infPart D)) e = 1 := fun τ => (congrArg (θ τ) hip).trans (θ τ).map_one
  refine ⟨e, _, hee, h.1, h.2.1, hce, h.2.2, hef, he1, fun τ => ?_⟩
  have h2 : ((θ τ).comp (infPart D)) (incA D μ) = tauE D τ μ := L3 μ τ
  exact (cx_phase (cA D) ((θ τ).comp (infPart D)) (fun z => L2 z τ) (he1 τ) hεu hh (h4 τ)).trans
    (congrArg (fun t : ℂ => t / (‖t‖ : ℂ)) h2)

theorem exists_mem_K_compAt_eq_stdInv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (n : ℕ) (μ : D.host.E), IsSkew μ →
    ∃ k ∈ K D n, ∀ τ, compAt θ τ (mat k) = stdInv n μ τ := by
  intro D θ hθ n μ hμ
  obtain ⟨e, j, hee, hej, hjj, hce, hcj, hef, he1, hj⟩ := exists_phase_adele D θ hθ μ hμ
  obtain ⟨k, hk, hmat⟩ := exists_point D.sp.cm.sig n hee hej hjj hce hcj hef
  refine ⟨k, hk, fun τ => ?_⟩
  have h0 : mat (D := D) (n := n) k = mixJ n (1 - e) j := hmat
  have h1 : compAt θ τ (mixJ n (1 - e) j) = (mixJ n (1 - e) j).map ((θ τ).comp (infPart D)) := rfl
  rw [h0, h1, mixJ_real _ (he1 τ), hj]
  rfl

end GlobalTheory.CartanPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CenFockWt

theorem central_wt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  intro D ψ θ hθ S T x y hx hy k hk
  classical
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  have hvth : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CenterVac.exists_center_char D ψ θ hθ S T x y hx hy k hk
  set ζ : GA D S → D.what₂.Tau → ℂ := fun z τ =>
    if h : 0 < S.rank then compAt θ τ (Formalism.L2.Theta.mt S z) ⟨0, h⟩ ⟨0, h⟩ else 1 with hζdef
  set μ : GA D S → D.what₂.Tau → ℂ := fun z τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ z τ)⁻¹ else ζ z τ with hμdef
  set deg : D.what₂.Tau → (FVar D T.rank S.rank →₀ ℕ) → ℕ := fun τ α => ∑ v ∈ α.support with v.1 = τ, α v with hdeg
  have hζ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ,
      ‖ζ z τ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ z τ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
    intro z hz hzc τ
    obtain ⟨ζ', h1, h2⟩ := _root_.GlobalTheory.CenterScalar.center_scalar D θ hθ S x hx z hz hzc τ
    by_cases h : 0 < S.rank
    · have e : ζ z τ = ζ' := by
        simp only [hζdef, dif_pos h, h2, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      rw [e]; exact ⟨h1, h2⟩
    · have e : ζ z τ = 1 := by simp only [hζdef, dif_neg h]
      refine ⟨by rw [e, norm_one], ?_⟩
      ext i
      exact absurd i.2 (by omega)
  have hμ : ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ, ‖μ z τ‖ = 1 := by
    intro z hz hzc τ
    simp only [hμdef]
    split_ifs
    · rw [norm_inv, (hζ z hz hzc τ).1, inv_one]
    · exact (hζ z hz hzc τ).1
  have hT1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have comb_smul : ∀ (cc : WO S T →₀ ℂ) (a : ℂ) (g : WO S T → ℂ), comb ψ S T cc (a • g) = a • comb ψ S T cc g := by
    intro cc a g
    unfold comb
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have : heisO ψ S T u (a • g) = a • heisO ψ S T u g := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, smul_comm]
  refine ⟨fun α z => c z * ∏ τ, μ z τ ^ deg τ α, ?_, ?_⟩
  · intro α z hz hzc
    refine ⟨?_, ?_⟩
    · rw [norm_mul, (hc z hz hzc).1, one_mul, norm_prod]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [norm_pow, hμ z hz hzc τ, one_pow]
    · intro cc hcc
      set F := pureTensorO ψ θ S T x.s y.s x.B y.B with hF
      have hcomb : ∀ g, comb ψ S T cc g = ∑ i : Fin cc.support.card,
          cc (cc.support.equivFin.symm i) • heisO ψ S T (cc.support.equivFin.symm i) g := by
        intro g
        unfold comb
        rw [← Finset.sum_coe_sort]
        exact (Equiv.sum_comp cc.support.equivFin.symm (fun u => cc u • heisO ψ S T u g)).symm
      have key1 : ∀ g, IsThetaFunO ψ S T g → ∀ P, F (comb ψ S T cc g) P = comb ψ S T cc (F g P) := by
        intro g hg P
        rw [hcomb, hcomb]
        exact (_root_.GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hstd hθ x.s y.s x.B y.B g hg cc.support.card _ _
          (fun i => hcc _ (Finset.coe_mem _)) P).1.symm
      have hop := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B (fun τ => ζ z τ • x.B τ)
        y.s y.s y.B y.B z 1
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [(hζ z hz hzc τ).2, Matrix.smul_mul, Matrix.one_mul])
        (fun τ => by rw [hT1, Matrix.one_mul]) k.vac hvth (MvPolynomial.monomial α 1)
      rw [key1 k.vac hvth, _root_.GlobalTheory.SeeSaw.RealComm.om_comb D ψ S T χS χT k.om hW z hz cc hcc _ hop.1, hop.2, (hc z hz hzc).2,
        GlobalTheory.FiniteFock.pureTensorO_smul,
        _root_.GlobalTheory.FockScal.pureTensorO_scal D ψ θ hstd hθ S T x y hx hy k.vac hvth (ζ z) (fun τ => (hζ z hz hzc τ).1) α,
        smul_smul, comb_smul]
  · intro χ
    by_cases hne : ∃ α₀, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → c z * ∏ τ, μ z τ ^ deg τ α₀ = χ z
    · obtain ⟨α₀, hα₀⟩ := hne
      refine (_root_.GlobalTheory.finite_monomials_of_placeDegree D T.rank S.rank (fun τ => deg τ α₀)).subset fun α hα τ => ?_
      show deg τ α = deg τ α₀
      by_cases hr : 0 < S.rank ∧ 0 < T.rank
      · obtain ⟨z, hz, hzc, h1, h2⟩ := _root_.GlobalTheory.CentralUnit.exists_central_of_norm_one D θ hθ S τ (Complex.exp Complex.I) (by simpa using Complex.norm_exp_ofReal_mul_I 1)
        have e := (hα z hz hzc).trans (hα₀ z hz hzc).symm
        have hc0 : c z ≠ 0 := by
          intro h0
          have := (hc z hz hzc).1
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        have e2 := mul_left_cancel₀ hc0 e
        have hζρ : ∀ ρ, ρ ≠ τ → ζ z ρ = 1 := by
          intro ρ hρ
          simp only [hζdef, dif_pos hr.1, h2 ρ hρ, Matrix.one_apply_eq]
        have hζτ : ζ z τ = Complex.exp Complex.I := by
          simp only [hζdef, dif_pos hr.1, h1, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        have hμρ : ∀ ρ, ρ ≠ τ → μ z ρ = 1 := by
          intro ρ hρ
          simp only [hμdef, hζρ ρ hρ, inv_one, ite_self]
        rw [Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp),
          Finset.prod_eq_single τ (fun ρ _ hρ => by rw [hμρ ρ hρ, one_pow]) (by simp)] at e2
        exact GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv _ _ (μ z τ) (by
          simp only [hμdef, hζτ]
          split_ifs
          exacts [Or.inr rfl, Or.inl rfl]) e2
      · have hE : IsEmpty (FVar D T.rank S.rank) :=
          ⟨fun v => hr ⟨by have := v.2.2.2; omega, by have := v.2.1.2; omega⟩⟩
        simp only [hdeg, Finset.eq_empty_of_isEmpty α.support, Finset.eq_empty_of_isEmpty α₀.support,
          Finset.filter_empty, Finset.sum_empty]
    · refine Set.Finite.subset Set.finite_empty fun α hα => hne ⟨α, hα⟩

end GlobalTheory.CenFockWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.JacUnimod

theorem jacGrp_rightInv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ ρ d μ hμ
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V₀
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  obtain ⟨hlc, hsc, hbor, hcount⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨ν, 𝓝, hνH, h𝓝, h𝓝1⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  have hnorm := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d
  have hp := GlobalTheory.JacProj.exists_continuous_proj D V V₀ ρ d
  have hc := GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D V V₀ ρ d ν hνH
  let μ₀ : Measure (GA D V₀) := Measure.haar
  have hμ₀ : μ₀.IsHaarMeasure := inferInstance
  haveI := hνH
  haveI : μ₀.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V₀ μ₀ hμ₀
  haveI : ν.IsMulRightInvariant := GlobalTheory.SemiHaar.rightInv_of_fd _ ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed hnorm hp μ₀ ν hμ₀ hνH hc
  obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed hnorm hp
    μ₀ ν hμ₀ hνH hc
  have hH : (semiMeas (flagN d) d.emb0 μ₀ ν).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) d.emb0 hNc d.continuous_embed hnorm μ₀ ν
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) d.emb0 hnorm d.continuous_embed hp
  haveI : LocallyCompactSpace (jacGrp d) := e.symm.isClosedEmbedding.locallyCompactSpace
  let κ : Measure (jacGrp d) := semiMeas (flagN d) d.emb0 μ₀ ν
  haveI hκH : κ.IsHaarMeasure := hH
  haveI hκR : κ.IsMulRightInvariant := hR
  have hk := Measure.isMulLeftInvariant_eq_smul μ κ
  rw [hk]
  infer_instance

end GlobalTheory.JacUnimod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphSmooth

open GlobalTheory.SiegelSet (IsRealLine lineDer)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem isRealLine_oneP (hθ : IsInfFam θ) (V : HSp D) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  refine ⟨placeOf D τ, embOverOf D τ, X, hX, fun t => ?_⟩
  obtain ⟨x, hx⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  refine ⟨x, ?_, ?_⟩
  · rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl x]
  · rw [GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), hx]

theorem mem_smFun_of_isSm (hθ : IsInfFam θ) {f : GA D V → ℂ} (h : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f) :
    f ∈ SmFun θ V :=
  fun k τs Xs hX g => h k (fun i => oneP θ V (τs i) (Xs i)) (fun i => isRealLine_oneP hθ V (hX i)) g

def derSpan (V : HSp D) (f : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {g | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧ g = l.foldr lineDer f}

theorem derSpan_le (hθ : IsInfFam θ) {f : GA D V → ℂ} (hf : f ∈ SmFun θ V) : derSpan V f ≤ SmFun θ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    obtain ⟨p, hp, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    exact GlobalTheory.Mem.AutSpace.Rder_mem (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) hp

end GlobalTheory.SphSmooth

end
end

