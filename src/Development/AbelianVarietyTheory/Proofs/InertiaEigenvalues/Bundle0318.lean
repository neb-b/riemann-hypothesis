module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContCoreTied
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundCont

theorem contCore_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.contCore (P.PD K) :=
  fun _ _ _ AI T K => contCore_of_tied AI T K

end GlobalTheory.FundCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCochainOfDeRhamCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

open Formalism Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.FundCont Filter Topology

namespace GlobalTheory.ContDR

theorem cont_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  intro l _ P AI T K V _ _ _ _ _ ρ hρ k x β hβ x' f hf
  have hV : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have key : ∀ φ : V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : V ⊗[ℚ_[l]] P.R.BdR) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T b ((hV φ).comp ((hβ i).smul continuous_const))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add (f := _)]
        exact ih.add AI ih'
    have h2 : ∀ y : V ⊗[ℚ_[l]] P.R.BdR, LatCont AI fun g => Φ (actVdR (P.PD K) ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVdR (P.PD K) ρ g (v ⊗ₜ b)) =
            qB P (φ (ρ g v)) * P.actQdR (g : GQ l) b := by
          intro g
          rw [← P.PD_actdR K g b, ← hΦ]
          rfl
        simp only [e]
        exact latCont_orbit AI T b ((hV φ).comp (hρ v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add (f := _)]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVdR (P.PD K) ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  let b := Module.finBasis ℚ_[l] V
  have : f = fun g => ∑ j, b.coord j (f g) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact continuous_finsetSum _ fun j _ => (key (b.coord j)).smul continuous_const

end GlobalTheory.ContDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopolo
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_orbit_twTop :
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l}
      (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T),
      letI := twTop T b
      Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  intro l _ P AI K LL T d b y

  letI := zlMod T
  haveI := zlTower T
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  haveI hWr : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) :=
    GlobalTheory.WeakTop.continuous_padicInt_witt (zlW l (Cb l))
  have ha : Continuous fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2 :=
    GlobalTheory.WeakTop.continuous_map_witt (fun g : GQ l => (autCb l (AI.actT g)).toRingHom)
      (continuous_autCb_cbTop AI)
  haveI := LL.2
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hρ : ∀ i j, Continuous fun g : ↥(GK K) => b.repr (T.actT g (b j)) i := fun i j =>
    hemb.continuous_iff.2 (GlobalTheory.Cyc.continuous_coord_lat hc T b (b j) i)
  have h2 : ∀ w : WCb l, Continuous fun g : ↥(GK K) => (AI.actWCbHom (g : GQ l)).toAlgHom w := fun w =>
    Continuous.comp (g := fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2)
      (f := fun g : ↥(GK K) => ((g : GQ l), w)) ha (continuous_subtype_val.prodMk continuous_const)
  have hs : ∀ i, Continuous fun g : ↥(GK K) => ∑ j, algebraMap ℤ_[l] (WCb l) (b.repr (T.actT g (b j)) i) *
      (AI.actWCbHom (g : GQ l)).toAlgHom (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b y j) := fun i =>
    continuous_finsetSum _ fun j _ => (hW.comp (hρ i j)).mul (h2 _)
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  refine (hs i).congr fun g => ?_
  exact (GlobalTheory.WeakTop.coords_map b _ _ y i).symm

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTailStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M), (∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U) → (∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) → Continuous Φ := by
  first | exact @GlobalTheory.WeakClosed.continuous_of_tail | exact GlobalTheory.WeakClosed.continuous_of_tail | (intros; apply GlobalTheory.WeakClosed.continuous_of_tail <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_tmul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  first | exact @GlobalTheory.WeakClosed.continuous_one_tmul | exact GlobalTheory.WeakClosed.continuous_one_tmul | (intros; apply GlobalTheory.WeakClosed.continuous_one_tmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_padicInt_smul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  first | exact @GlobalTheory.WeakClosed.continuous_zl_smul | exact GlobalTheory.WeakClosed.continuous_zl_smul | (intros; apply GlobalTheory.WeakClosed.continuous_zl_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFilteredStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_comparison_isFiltered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.DRFil.deRham_filtered | exact GlobalTheory.DRFil.deRham_filtered | (intros; apply GlobalTheory.DRFil.deRham_filtered <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := _root_.GlobalTheory.PMon.bdR_tied l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact _root_.GlobalTheory.PMon.FrameOne.frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecWOfMatrixStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decW_of_matrix_criterion : ∀ (S : Sit) (E : S.Comparison₂), (∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) S.W.EE), (∀ y : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (y i) = y i) → ∃ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) ∧ ∀ i, ∃ e, y i - (∑ k, E.ioE (Pm i k) * S.φR (z k) - z i) = E.ioE e) ∧ (∀ z : Fin d → S.RW, (∀ i, ∀ g ∈ Hker S, S.gR g (z i) = z i) → (∀ i, ∃ e, ∑ k, E.ioE (Pm i k) * S.φR (z k) - z i = E.ioE e) → ∀ i, ∃ e, z i = E.ioE e)) → DecW S E := by
  first | exact @GlobalTheory.DecomplRed.decW_of_matrix | exact GlobalTheory.DecomplRed.decW_of_matrix | (intros; apply GlobalTheory.DecomplRed.decW_of_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAbove
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.JumpWin

theorem finset_of_rat (F : Finset ℚ) (n N : ℕ) (P : ℤ → Prop) (hF : F.card ≤ n)
    (hP : ∀ a, P a → (a : ℚ) ∈ F ∧ -(N : ℤ) ≤ a ∧ a ≤ N) :
    ∃ U : Finset ℤ, U.card ≤ n ∧ (∀ u ∈ U, -(N : ℤ) ≤ u ∧ u ≤ N) ∧ ∀ a, P a → a ∈ U := by
  classical
  refine ⟨(F.image fun q => ⌊q⌋).filter (fun u => -(N : ℤ) ≤ u ∧ u ≤ N), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hF)
  · intro u hu
    exact (Finset.mem_filter.1 hu).2
  · intro a ha
    obtain ⟨h1, h2⟩ := hP a ha
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a : ℚ), h1, Int.floor_intCast a⟩, h2⟩

variable {D : D7}

open AdmissibleParameterJ

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up <;> simp only [JW, cloudT, lowT, JJ, Jp, Jm, reflS, Bool.false_eq_true, if_true, if_false,
    Set.mem_union, Set.mem_setOf_eq] at hq ⊢ <;> tauto

theorem exists_finset_JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) :
    ∃ F : Finset ℚ, F.card ≤ D.R.r ∧ ∀ q ∈ JW D up j ρ, q ∈ F := by
  classical
  let cl : Finset ℚ := Finset.univ.image (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)
  let lw : Finset ℚ := Finset.univ.image (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)
  have hcard : (cl ∪ lw).card ≤ D.R.r := by
    have h1 : cl.card ≤ D.R.k - 1 := Finset.card_image_le.trans (by simp)
    have h2 : lw.card ≤ D.R.m := Finset.card_image_le.trans (by simp)
    have hk := D.R.m_add_three_le_k
    have : (cl ∪ lw).card ≤ cl.card + lw.card := Finset.card_union_le _ _
    simp only [Ranks.r]
    omega
  have hmem : ∀ q, q ∈ cloudJ D j ρ ∪ lowJ D j ρ → q ∈ cl ∪ lw := by
    intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
  cases up
  · refine ⟨(cl ∪ lw).image (AdmissibleParameterJ.refl D), Finset.card_image_le.trans hcard, ?_⟩
    intro q hq
    have hq' : AdmissibleParameterJ.refl D q ∈ cloudJ D j ρ ∪ lowJ D j ρ := by
      simpa only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
        Set.mem_setOf_eq] using hq
    refine Finset.mem_image.2 ⟨AdmissibleParameterJ.refl D q, hmem _ hq', ?_⟩
    simp only [AdmissibleParameterJ.refl]; ring
  · refine ⟨cl ∪ lw, hcard, ?_⟩
    intro q hq
    exact hmem q (by simpa only [JW, cloudT, lowT, if_true] using hq)

theorem zero_not_mem_JW (L : SizeData₂ D) (hc : jcCondition L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hj2 ρ
  cases up
  · intro h
    simp only [JW, cloudT, lowT, reflS, Bool.false_eq_true, if_false, Set.mem_union,
      Set.mem_setOf_eq] at h
    have ht : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
    rcases h with h | h
    · have := hcl _ h
      simp only [AdmissibleParameterJ.refl] at this
      linarith
    · rcases hlow _ h with ⟨-, h'⟩ | ⟨h', -⟩
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
      · simp only [AdmissibleParameterJ.refl] at h'
        linarith
  · simpa only [JW, cloudT, lowT, if_true] using h0

theorem natAbs_le_of_mem_JJ (L : SizeData₂ D) (he : JumpAbsoluteBound L) (up : Bool) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    a.natAbs ≤ ⌊2 * L.sc.b⌋₊ := by
  have h1 := he.1 j hj1 hj2 ρ up _ ha
  have h2 : |((a : ℚ) : ℝ)| ≤ 2 * L.sc.b := by
    have := he.2.1; have := he.2.2.2; linarith
  apply Nat.le_floor
  have : ((a.natAbs : ℕ) : ℝ) = |((a : ℚ) : ℝ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [this]; exact h2

end GlobalTheory.JumpWin


open GlobalTheory.JumpWin AdmissibleParameterJ in
theorem GlobalTheory.jumps_WpO_T2O_window : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → AdmissibleParameterJ.DualCloudSizes L → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1), ∀ M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i), (M = WpO D.nd i ρ π ∨ M = T2O D.nd i ρ π) → (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -((⌊2 * L.sc.b⌋₊ + 1 : ℕ) : ℤ) ≤ u ∧ u ≤ (⌊2 * L.sc.b⌋₊ + 1 : ℕ)) ∧ ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧ ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0 := by
  intro D L ep hA _hb hc he hf i r ρ π hr hπ hdec w hw C τ M hM
  classical
  obtain ⟨g, ρ', -, -, hT⟩ := hA i r hr w hw C τ
  have hj := D.nd.j_range i
  have hW := hT ρ π hπ hdec
  generalize decide (TypeU D ep g) = up at hW
  obtain ⟨F, hFc, hFm⟩ := exists_finset_JW up (D.nd.j i) ρ'
  rcases hM with rfl | rfl
  · refine ⟨finset_of_rat F D.R.r (⌊2 * L.sc.b⌋₊ + 1) _ hFc ?_, ?_⟩
    · intro a ha
      have hq := ((hW a).1).1 ha
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' a (JW_sub_JJ up _ ρ' hq)
      refine ⟨hFm _ hq, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).1).1 h0
      exact zero_not_mem_JW L hc up _ hj.1 hj.2 ρ' (by simpa using this)
  · refine ⟨finset_of_rat (F.image fun q => -q - 1) D.R.r (⌊2 * L.sc.b⌋₊ + 1) _
      (Finset.card_image_le.trans hFc) ?_, ?_⟩
    · intro a ha
      have hq : -(a : ℚ) - 1 ∈ JW D up (D.nd.j i) ρ' := ((hW a).2.2.1).1 ha
      have hq' : (((-a - 1 : ℤ)) : ℚ) ∈ JW D up (D.nd.j i) ρ' := by push_cast; exact hq
      have hn := natAbs_le_of_mem_JJ L he up _ hj.1 hj.2 ρ' _ (JW_sub_JJ up _ ρ' hq')
      refine ⟨Finset.mem_image.2 ⟨_, hFm _ hq, by ring⟩, ?_, ?_⟩ <;> push_cast <;> omega
    · intro h0
      have := ((hW 0).2.2.1).1 h0
      exact (hf _ hj.1 hj.2 ρ').2.2.1 up (by simpa using this)

end
end

