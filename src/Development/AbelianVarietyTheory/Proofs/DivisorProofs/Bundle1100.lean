module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapLocRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0134
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantWachModuleBasisOfNonnegJumps
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachFrame

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f) {T : LocLat G Qp LL O} {n : ℕ}

theorem γD_smulA (g : W.Gam) (a : LetA O f) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem coe_eq_sum (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (y : ↥(W.N T)) :
    (y : W.DD T) = ∑ m, b.repr y m • (b m : W.DD T) := by
  have h1 := congrArg Subtype.val (b.sum_repr y)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
  exact h1.symm

theorem coord_fixed (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (δ : W.Gam) (hδ : δ ∈ W.DelF) (hy : W.γD T δ (y : W.DD T) = y) (m : Fin n) :
    W.γA δ (b.repr y m) = b.repr y m := by
  have e : ∑ m, W.γA δ (b.repr y m) • b m = y := by
    apply Subtype.ext
    have h1 : W.γD T δ (y : W.DD T) = ∑ m, W.γA δ (b.repr y m) • (b m : W.DD T) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [coe_eq_sum W b y, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [γD_smulA, (hb m).2 δ hδ]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact h1.symm.trans hy
  have h2 := congrFun (b.repr_sum_self fun m => W.γA δ (b.repr y m)) m
  rw [e] at h2
  exact h2.symm

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

theorem exists_inc (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (y : ↥(W.N T)) (hy : ∀ δ ∈ W.DelF, W.γD T δ (y : W.DD T) = y) (m : Fin n) (i : ZMod f) :
    ∃ z, inc l O z = b.repr y m i :=
  hI _ fun δ hδ => congrFun (coord_fixed W b hb y δ hδ (hy δ hδ) m) i

theorem exists_phi_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hφ : ∀ x ∈ W.N T, W.φD T x ∈ W.N T) :
    ∃ Pm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.φD T (b k : W.DD T) =
      ∑ m, (fun i => inc l O (Pm i m k) : LetA O f) • (b m : W.DD T) := by
  have h : ∀ i m k, ∃ z, inc l O z = b.repr ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩ m i := fun i m k =>
    exists_inc W l hI b hb _ (fun δ hδ => by
      change W.γD T δ (W.φD T (b k : W.DD T)) = W.φD T (b k : W.DD T)
      rw [← W.φγ_comm, (hb k).2 δ hδ]) m i
  choose Pm hPm using h
  refine ⟨fun i => Matrix.of (Pm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.φD T (b k : W.DD T), hφ _ (b k).2⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hPm i m k).symm

theorem exists_gam_matrix (hI : ∀ a : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ y, inc l O y = a)
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (γ : W.Gam) :
    ∃ Dm : ZMod f → Matrix (Fin n) (Fin n) O⟦X⟧, ∀ k, W.γD T γ (b k : W.DD T) =
      ∑ m, (fun i => inc l O ((1 + (X : O⟦X⟧) • Dm i) m k) : LetA O f) • (b m : W.DD T) := by
  have hγ : ∀ k, W.γD T γ (b k : W.DD T) ∈ W.N T := fun k => W.N_Γ T γ _ (b k).2
  have h : ∀ i m k, ∃ d : O⟦X⟧, inc l O ((1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k + X * d) =
      b.repr ⟨W.γD T γ (b k : W.DD T), hγ k⟩ m i := by
    intro i m k
    obtain ⟨z, hz⟩ := exists_inc W l hI b hb ⟨W.γD T γ (b k : W.DD T), hγ k⟩ (fun δ hδ => by
      change W.γD T δ (W.γD T γ (b k : W.DD T)) = W.γD T γ (b k : W.DD T)
      rw [← W.γD_mul, mul_comm, W.γD_mul, (hb k).2 δ hδ]) m i
    obtain ⟨y, hy, e⟩ := W.N_π T γ _ (b k).2
    have e1 : (⟨W.γD T γ (b k : W.DD T), hγ k⟩ : ↥(W.N T)) = b k + (letπ : LetA O f) • (⟨y, hy⟩ : ↥(W.N T)) :=
      Subtype.ext (eq_add_of_sub_eq' e)
    have e2 : constantCoeff (z - (1 : Matrix (Fin n) (Fin n) O⟦X⟧) m k) = 0 := by
      rw [map_sub, ← (pi0Subst_laws_hold l O).2.2.2.2.2.1 z, hz, e1, map_add (f := _), map_smul, b.repr_self]
      by_cases hmk : m = k
      · subst hmk
        simp [letπ]
      · simp [letπ, hmk, Finsupp.single_eq_of_ne hmk]
    obtain ⟨d, hd⟩ := X_dvd_iff.2 e2
    exact ⟨d, by rw [← hd, add_sub_cancel, hz]⟩
  choose Dm hDm using h
  refine ⟨fun i => Matrix.of (Dm i), fun k => ?_⟩
  refine (coe_eq_sum W b ⟨W.γD T γ (b k : W.DD T), hγ k⟩).trans (Finset.sum_congr rfl fun m _ => ?_)
  congr 1
  funext i
  exact (hDm i m k).symm

theorem mem_of_letters (x : W.DD T) (h : ∀ i, (letE i : LetA O f) • x ∈ W.N T) : x ∈ W.N T := by
  haveI := GlobalTheory.WachLettersCompare.neZero_letters W
  have e : (∑ i, letE i : LetA O f) = 1 := Finset.univ_sum_single (1 : LetA O f)
  rw [← one_smul (LetA O f) x, ← e, Finset.sum_smul]
  exact Submodule.sum_mem _ fun i _ => h i

theorem phi_mem (hH : GlobalTheory.WachUse.Heights W) (U : ZMod f → Multiset ℤ)
    (hU : GlobalTheory.AdmLoc.CrysWith PD W.emb T.ρ U) (hpos : ∀ i, ∀ u ∈ U i, 0 ≤ u) :
    ∀ x ∈ W.N T, W.φD T x ∈ W.N T := by
  intro x hx
  refine mem_of_letters W _ fun i => ?_
  have := (hH T U (fun _ => 0) (fun i => ((U i).map Int.toNat).sum) hU (fun i u hu => ?_) i).1 x hx
  · simpa using this
  · refine ⟨by simpa using hpos i u hu, ?_⟩
    have h1 : u.toNat ≤ ((U i).map Int.toNat).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hu)
    exact (Int.self_le_toNat u).trans (by exact_mod_cast h1)

end Generic

theorem exists_rem {l : ℕ} [Fact l.Prime] (LL : FinExt l) (g : (↥(OL LL))⟦X⟧) :
    ∃ a : ↥(OL LL), (X - C (l : ↥(OL LL))) ∣ g - C a := by
  obtain ⟨_, hc, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨g₁, a, e⟩ := (linear_division_holds ↥(OL LL) (maximalIdeal ↥(OL LL)) (l : ↥(OL LL))
    ((mem_maximalIdeal _).2 hl)).1 g
  exact ⟨a, g₁, by rw [e, add_sub_cancel_right]⟩

theorem exists_frame : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n : ℕ), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u) → Module.finrank ↥(OL LL) ↥T.L.T = n → ∀ γ : ((HW l).W K 1 LL hA.2.2).Gam, ∃ (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N := by
  intro D HW F Cm l _ K LL hA T U n hU hpos hn γ
  have hR := _root_.GlobalTheory.WachPlace.ringFacts_of_caseA (HW l) K LL hA
  have hJ := (GlobalTheory.HeightsClauseCompare.heights_iff D HW F Cm).2
    ⟨GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm, GlobalTheory.NL.SandJumps.main D HW F Cm⟩
  have hH := GlobalTheory.WachUse.HeightsProof.heights_of_caseA (D.locA l) (HW l) (F l) (Cm l) ⟨D.locT l⟩
    ((GlobalTheory.HeightsFromJumpsCompare.heightsFromJumps_iff l _ _ _ _ _).2 (hJ l)) K LL hA
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free (D.loc l) (HW l) K 1 LL hA.2.2 T hU.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hR.2.2.2.2.2 ⟨b₀.reindex (finCongr hn)⟩
  obtain ⟨Pm, hP⟩ := exists_phi_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb (phi_mem _ hH U hU hpos)
  obtain ⟨Dm, hD⟩ := exists_gam_matrix _ l (fun a => (hR.2.2.2.2.1 a).1) b hb γ
  choose Th hTh using fun i a c => exists_rem LL (Dm i a c)
  exact ⟨b, ⟨Pm, Dm, fun i => Matrix.of (Th i)⟩, hb, hP, hD, hTh⟩

end GlobalTheory.WachFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCutoffBoundedPoincareGradient
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

noncomputable def logCutoff (k : ℕ) (z : ℂ) : ℝ :=
  if z = 0 then 0 else Real.smoothTransition (2 + Real.log ‖z‖ / ((k : ℝ) + 1))

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma logCutoff_eq_zero_of_norm_le (k : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ Real.exp (-2 * ((k : ℝ) + 1))) : _root_.GlobalTheory.GoodTop.logCutoff k z = 0 := by
  unfold _root_.GlobalTheory.GoodTop.logCutoff
  split_ifs with h0
  · rfl
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog : Real.log ‖z‖ ≤ -2 * ((k : ℝ) + 1) := by
    rw [← Real.log_exp (-2 * ((k : ℝ) + 1))]
    exact Real.log_le_log (norm_pos_iff.mpr h0) hz
  rw [← sub_nonneg, show 0 - (2 + Real.log ‖z‖ / ((k : ℝ) + 1)) =
    (-2 * ((k : ℝ) + 1) - Real.log ‖z‖) / ((k : ℝ) + 1) by field_simp; ring]
  exact div_nonneg (by linarith) hk.le

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
lemma _root_.GlobalTheory.GoodTop.contDiff_logCutoff (k : ℕ) : ContDiff ℝ ∞ (_root_.GlobalTheory.GoodTop.logCutoff k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h0 : z = 0
  · subst h0
    have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-2 * ((k : ℝ) + 1)))] with w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      exact logCutoff_eq_zero_of_norm_le k hw.le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : _root_.GlobalTheory.GoodTop.logCutoff k =ᶠ[𝓝 z]
        fun w => Real.smoothTransition (2 + Real.log ‖w‖ / ((k : ℝ) + 1)) := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      simp only [_root_.GlobalTheory.GoodTop.logCutoff, if_neg (show w ≠ 0 from hw)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine Real.smoothTransition.contDiff.contDiffAt.comp z ?_
    refine contDiffAt_const.add (ContDiffAt.div_const ?_ _)
    exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr h0)).comp z (contDiffAt_norm ℝ h0)

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem exists_ne_zero_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ k, u k ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by simp [avg, hc])

theorem exists_ne_zero_of_twOrb_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) : ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem exists_ne_zero_of_clSum_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (S : Set G) (wt f : G → ℂ) (h : clSum θ K S wt f ≠ 0) : ∃ δ ∈ S, ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  apply h
  unfold clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hS
  · by_contra hne
    exact hc ⟨c.rep, hS, exists_ne_zero_of_twOrb_ne_zero θ K c.rep f (right_ne_zero_of_mul hne)⟩
  · rfl

theorem nrmL_twConj {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ x : GLw n w) :
    nrmL n w (x⁻¹ * δ * thL n w x) = x⁻¹ * nrmL n w δ * x := by
  have hinv := TwistInvol.thL_involutive E n w x
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp
  · simp only [map_mul, map_inv, hinv]
    group

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntMatOpen

open IsDedekindDomain.HeightOneSpectrum

def intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, Valued.v (X i j) ≤ 1}
  add_mem' {X Y} hX hY i j := (Valued.v.map_add (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))
  zero_mem' i j := by simp
  neg_mem' {X} hX i j := by simpa using hX i j

theorem coe_intLat (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) :
    (intLat E w a b : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) =
      Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ fun _ : Fin b =>
        (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  ext X
  constructor
  · intro h i _ j _
    exact h i j
  · intro h i j
    exact h i trivial j trivial

theorem intMat_open_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ), ∃ Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ IsCompact (Λ : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ intMat a b w = AddSubgroup.toSubgroup Λ := by
  intro E _ _ w a b
  refine ⟨intLat E w a b, ?_, ?_, ?_⟩
  · rw [coe_intLat]
    exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_set_pi Set.finite_univ fun j _ =>
      Valued.isOpen_valuationSubring _
  · rw [coe_intLat]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
      PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w
  · have hS : {X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) |
        ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1} =
        ((AddSubgroup.toSubgroup (intLat E w a b) : Subgroup _) : Set _) := by
      ext X; rfl
    unfold intMat
    rw [hS, Subgroup.closure_eq]

end GlobalTheory.IntMatOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem exists_open_conjStable_sub_level (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (K' : Subgroup (UL n w)) (hw : IsSplitAt w) (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hUtop : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hUo : IsOpen (UL n w : Set (GLw n w)) := by rw [hUtop]; exact isOpen_univ
  have hmemU : ∀ x : GLw n w, x ∈ UL n w := fun x => by rw [hUtop]; trivial
  by_cases hKL : K' = KL n w
  · refine ⟨GlobalTheory.LFun.KGL w (n := n), hKo, ?_, ?_, fun _ => rfl⟩
    · intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hmemU x⟩, ?_, rfl⟩
      rw [hKL, KL, Subgroup.mem_subgroupOf]
      exact hx
    · intro k hk x hx
      exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).inv_mem hk) hx) hk
  · set S : Subgroup (GLw n w) := K'.map (UL n w).subtype with hSdef
    have hSo : IsOpen (S : Set (GLw n w)) := by
      rw [hSdef, Subgroup.coe_map]
      exact hUo.isOpenMap_subtype_val _ hK.1
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
    have hWo : IsOpen ((S.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) : Subgroup _) : Set (GlobalTheory.LFun.KGL w (n := n))) := by
      rw [Subgroup.coe_subgroupOf]
      exact hSo.preimage continuous_subtype_val
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ hWo, hWo⟩ (Subgroup.one_mem _)
    refine ⟨V.toSubgroup.map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, ?_, ?_, fun h => absurd h hKL⟩
    · rw [Subgroup.coe_map]
      exact hKo.isOpenMap_subtype_val _ V.isOpen'
    · rintro _ ⟨v, hv, rfl⟩
      have := hV hv
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at this
      exact this
    · rintro k hk _ ⟨v, hv, rfl⟩
      refine ⟨(⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹ * v * (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n)), ?_, ?_⟩
      · have := V.isNormal'.conj_mem v hv (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹
        simpa using this
      · simp

end GlobalTheory.BCT.CtLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def NormPin {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
    (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
      pt ≫ Formalism.L2.PjFree.gxFst y.x = (F.ex k Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
    MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

def Pinned (U : Formalism.L2.PjFree.Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
      (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)

def MoveMatch (U U' : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (k' : U'.Comp) {δ : GL (Fin r) E}
    (h : GlobalTheory.LevelCusp.IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)), FrMove ρ ν (U.un k x) y' →
    y'.x = (U'.un k' ⟨_, h.mem_dom x.2⟩).x ∧ y'.u = (U'.un k' ⟨_, h.mem_dom x.2⟩).u

theorem exists_frBor_gen (z y : FrPt Xo c (CAt σ)) (hx : y.x = z.x) (hu : y.u = z.u) :
    ∃ t₀ : (CAt σ)ˣ, FrBor (fun i => Option.elim i t₀ (fun _ => 1)) z y := by
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 hx
  refine ⟨a, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hbc⟩⟩
  rw [hu]
  exact (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) z z z).1.2.1 τ i

theorem exists_pinned_of_isUnf {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Pinned U e F ik φ ∧
      ∀ k (x : (U.X k).dom) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)),
        (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) →
        GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → NormPin F (ik k) Pm (U.un k x) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, h1, h2⟩ := hU
  refine ⟨g, e, F, ik, φ, ⟨h1, fun k x => ?_⟩, fun k x Pm hPm hx => ?_⟩
  · obtain ⟨P, a, b, c, d, -⟩ := h2 k x
    exact ⟨P, a, b, c, d⟩
  · obtain ⟨P, a, -, -, -, d⟩ := h2 k x
    obtain rfl : Pm = P := AddMonoidHom.ext fun v => funext fun j => (hPm v j).trans (a v j).symm
    exact d hx

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGeneric

theorem exists_th_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] [CharZero K] (yK : S.R →+* K), ∃ a : S.Gam, yK ⟨S.th a, S.th_mem a⟩ ≠ 0 := by
  intro hL hL₂ o Ω _ _ _ S ρ K _ _ yK
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem hL hL₂ ρ ⟨RingHom.ker yK, RingHom.ker_isPrime yK⟩ 0
  exact ⟨0 + c, fun e => h (RingHom.mem_ker.2 e)⟩

end GlobalTheory.ThetaGeneric
end

