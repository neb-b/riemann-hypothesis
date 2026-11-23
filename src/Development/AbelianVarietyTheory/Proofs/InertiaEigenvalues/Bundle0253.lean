module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.UnramSpan

open GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

theorem fg_rootRing {m : ℕ} (hm : 0 < m) : (rootRing l m).toSubmodule.FG := by
  classical
  have hfin : {x : Om l | x ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hm] using hx
  refine fg_adjoin_of_finite hfin ?_
  intro x hx
  refine IsIntegral.of_pow hm ?_
  rw [show x ^ m = 1 from hx]; exact isIntegral_one

theorem exists_mem_rootRing {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨m, hm, hl, c, hc, h⟩ := exists_mul_mem hx
  refine ⟨m, hm, hl, ?_⟩
  have key : ∀ k : ℕ, (l : Om l) ^ k * x ∈ rootRing l m → x ∈ rootRing l m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hk (by
        rw [norm_mul, norm_pow, norm_l]
        have : ((l : ℝ)⁻¹) ^ (k + 1) < 1 :=
          pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero k)
        calc _ ≤ ((l : ℝ)⁻¹) ^ (k + 1) * 1 := by gcongr
          _ < 1 := by simpa using this)
      apply ih
      have : (l : Om l) ^ k * x = z := by
        apply mul_left_cancel₀ hl0
        rw [← ez]; ring
      rwa [this]
  apply key c.valuation
  have e := PadicInt.unitCoeff_spec hc
  set u := PadicInt.unitCoeff hc
  have e2 : (l : Om l) ^ c.valuation * x =
      algebraMap ℤ_[l] (Om l) (↑u⁻¹ : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) c * x) := by
    rw [← mul_assoc, ← map_mul]
    congr 1
    conv_rhs => rw [e, Units.inv_mul_cancel_left]
    simp
  rw [e2]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) h

theorem norm_pow_sub_pow_le {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k ≠ 0) {a b : Om l}
    (ha : a ∈ rootRing l m) (hb : b ∈ rootRing l m) (h : ‖a - b‖ ≤ (l : ℝ)⁻¹) :
    ‖a ^ (l ^ k) - b ^ (l ^ k)‖ ≤ (l : ℝ)⁻¹ * ‖a - b‖ := by
  have hp : l.Prime := Fact.out
  have hd := sub_mem ha hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨b, hb⟩ : rootRing l m) ⟨a - b, hd⟩ k
  have hr' := congrArg Subtype.val hr
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, add_sub_cancel] at hr'
  have e : a ^ (l ^ k) - b ^ (l ^ k) = (a - b) ^ (l ^ k) + l * (a - b) * (b * r) := by
    rw [hr']; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ : ∃ j, l ^ k = j + 2 :=
      ⟨l ^ k - 2, by have := Nat.one_lt_pow hk hp.one_lt; omega⟩
    have h1 := norm_le_one hm hd
    have h2 : ‖a - b‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    rw [hj, norm_pow, pow_add, sq]
    calc _ ≤ 1 * ((l : ℝ)⁻¹ * ‖a - b‖) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul, norm_mul, norm_l]
    have h1 := norm_le_one hm (mul_mem hb r.2)
    calc _ ≤ (l : ℝ)⁻¹ * ‖a - b‖ * 1 := by gcongr
      _ = _ := mul_one _

def part (F : IntermediateField ℚ_[l] (Om l)) (m : ℕ) : Submodule ℤ_[l] (Om l) :=
  (rootRing l m).toSubmodule ⊓ F.toSubalgebra.toSubmodule.restrictScalars ℤ_[l]

theorem mem_part {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ} {x : Om l} :
    x ∈ part F m ↔ x ∈ rootRing l m ∧ x ∈ F := Iff.rfl

theorem fg_part (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) : (part F m).FG :=
  (fg_rootRing hm).of_le inf_le_left

theorem exists_teich (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m)
    {x : Om l} (hx : x ∈ part F m) :
    ∃ w ∈ part F m, w ^ (l ^ m.totient) = w ∧ ‖x - w‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hli : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have : ContinuousSMul ℤ_[l] (Om l) := by
    refine continuousSMul_of_algebraMap ℤ_[l] (Om l) ?_
    exact (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_int).continuous
  have hc : IsCompact ((part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹) :=
    (Submodule.isCompact_of_fg (fg_part F hm)).inter_right Metric.isClosed_closedBall
  have hstep : ∀ y ∈ rootRing l m, ‖y ^ (l ^ m.totient) - y‖ ≤ (l : ℝ)⁻¹ := by
    intro y hy
    obtain ⟨z, hz, ez⟩ := pow_sub_mem hl hy
    rw [ez, add_sub_cancel_left, norm_mul, norm_l]
    have h1 := norm_le_one hm hz
    calc _ ≤ (l : ℝ)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨w, ⟨hw, hwx⟩, hmin⟩ := hc.exists_isMinOn
    (f := fun y : Om l => ‖y ^ (l ^ m.totient) - y‖)
    ⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩ (by fun_prop)
  rw [Metric.mem_closedBall, dist_eq_norm] at hwx
  have hw' := mem_part.mp hw
  refine ⟨w, hw, ?_, by rw [norm_sub_rev]; exact hwx.trans_lt hli⟩
  have hmem : w ^ (l ^ m.totient) ∈ (part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹ := by
    refine ⟨mem_part.mpr ⟨pow_mem hw'.1 _, pow_mem hw'.2 _⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show w ^ (l ^ m.totient) - x = (w ^ (l ^ m.totient) - w) + (w - x) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep w hw'.1) hwx)
  have h1 : ‖w ^ (l ^ m.totient) - w‖ ≤ ‖(w ^ (l ^ m.totient)) ^ (l ^ m.totient) - w ^ (l ^ m.totient)‖ :=
    hmin hmem
  have h2 := norm_pow_sub_pow_le hm (Nat.totient_pos.mpr hm).ne' (pow_mem hw'.1 (l ^ m.totient))
    hw'.1 (hstep w hw'.1)
  have h3 := norm_nonneg (w ^ (l ^ m.totient) - w)
  have h4 : ‖w ^ (l ^ m.totient) - w‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

theorem part_le_span (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) :
    part F m ≤ Submodule.span ℤ_[l]
      {w : Om l | w ∈ F ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ w ^ m = 1} := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[l])
    (fg_part F hm) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x hx
  obtain ⟨w, hw, ew, hxw⟩ := exists_teich F hm hl hx
  have hd := mem_part.mp (sub_mem hx hw)
  obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hd.1 hxw
  have hzF : z ∈ F := by
    have : z = (x - w) / l := by rw [ez]; field_simp
    rw [this]
    exact div_mem hd.2 (natCast_mem F l)
  have e : x = w + (l : ℤ_[l]) • z := by
    rw [Algebra.smul_def, map_natCast, ← ez]; ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul ?_ (mem_part.mpr ⟨hz, hzF⟩))
  · by_cases h0 : w = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.mpr hm).ne' hp.one_lt
      refine Submodule.subset_span ⟨(mem_part.mp hw).2, l ^ m.totient - 1, by omega, ?_, ?_⟩
      · intro hd
        have h1 : l ∣ l ^ m.totient := dvd_pow_self l (Nat.totient_pos.mpr hm).ne'
        have h2 := Nat.dvd_sub h1 hd
        rw [show l ^ m.totient - (l ^ m.totient - 1) = 1 by omega] at h2
        exact hp.not_dvd_one h2
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, ew, one_mul]
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _

theorem exists_sum_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  intro l _ K c hc h1
  obtain ⟨m, hm, hl, h⟩ := exists_mem_rootRing (x := c) (show c ∈ K.1 ⊓ MaximalUnramifiedExtension l from hc).2 h1
  obtain ⟨n, z, g, e⟩ := Submodule.mem_span_set'.mp (part_le_span (K0 K) hm hl (mem_part.mpr ⟨h, hc⟩))
  refine ⟨n, z, fun i => g i, fun i => (g i).2, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  rfl

end GlobalTheory.UnramSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbolBasis

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_zero : J.θ 0 = 0 := by
  have h := J.θ_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem theta_sum {ι : Type} (s : Finset ι) (f : ι → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, f i) = ∑ i ∈ s, J.θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero J
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hf a) _ (Submodule.sum_mem _ fun i _ => hf i), ih]

theorem om_mul_mem (c : Om l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    algebraMap (Om l) P.R.BdR c * x ∈ (P.PD (botExt l)).Fil 0 := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) hx

theorem theta_comb {n : ℕ} (c : Fin n → Om l) (f : Fin n → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) :
    J.θ (∑ i, algebraMap (Om l) P.R.BdR (c i) * f i) = ∑ i, (c i : PadicComplex l) * J.θ (f i) := by
  rw [theta_sum J _ _ fun i => om_mul_mem (c i) (hf i)]
  exact Finset.sum_congr rfl fun i _ => by rw [J.θ_mul _ (om_mem _) _ (hf i), J.θ_Om]

omit J in
theorem shift_act (a : ℤ) (g : GQ l) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) *
        P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
  rw [map_mul, DeRhamSymbol.act_zpow, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    map_one, one_mul]

omit J in
theorem exists_adapted {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V)
    (hL : FiniteDimensional Qp LL) (hV : FiniteDimensional LL V) (hDR : IsDR PD ρ) :
    ∃ (x : Fin d → Fin d → BdR) (u : Fin d → ℤ), (∀ k, (∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x k i)) = x k) ∧
      ∀ i, x k i ∈ PD.Fil (u k)) ∧ ∀ (a : ℤ) (c : Fin d → K), (∀ k, u k ≠ a → c k = 0) →
      (∀ i, ∑ k, algebraMap K BdR (c k) * x k i ∈ PD.Fil (a + 1)) → ∀ k, c k = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  haveI : Nontrivial V := ⟨⟨b ⟨0, hd⟩, 0, b.ne_zero _⟩⟩
  haveI := PD.finK
  have hfin : Module.Finite LL ↥(DdR PD ρ) := by
    apply Module.finite_of_finrank_pos
    rw [hDR]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  obtain ⟨Φ, -, hΦ⟩ := GlobalTheory.exists_coord_tensor_dR PD ρ b
  obtain ⟨D, hD, hDf, hDr⟩ := GlobalTheory.deRham_invariants_coord_finrank PD ρ b hL hfin hDR Φ hΦ
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.exists_family_adapted_filtration K (Fin d → BdR) D
    (fun a => Submodule.pi Set.univ fun _ => PD.Fil a) d hDf hDr
    (fun a z hz i hi => PD.Fil_anti a (hz i hi))
    (fun z => by
      have anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
      choose f hf using fun i => PD.Fil_exh (z i)
      obtain ⟨m, hm⟩ := (Set.finite_range f).bddBelow
      exact ⟨m, fun i _ => anti (hm ⟨i, rfl⟩) (hf i)⟩)
    (fun z hz => funext fun i => PD.Fil_sep _ fun a => hz a i trivial)
  refine ⟨x, u, fun k => ⟨(hD _).1 (hx k).1, fun i => (hx k).2 i trivial⟩, fun a c hc hs => ?_⟩
  refine hind a c hc fun i _ => ?_
  have := hs i
  simp only [← Algebra.smul_def] at this
  simpa only [Finset.sum_apply, Pi.smul_apply, SetLike.mem_coe] using this

omit J in
theorem sum_mem_DdR {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V) (x : Fin d → BdR)
    (hx : ∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x i)) = x) :
    ∑ i, b i ⊗ₜ[Qp] x i ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro g
  have hact : ∀ (v : V) (y : BdR),
      actVdR PD ρ g (v ⊗ₜ y) = ρ g v ⊗ₜ PD.actdR g y := by
    intro v y
    unfold actVdR
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  obtain ⟨Φ, h, -⟩ := GlobalTheory.exists_tensor_coord_of_basis (M := BdR) b
  apply Φ.injective
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [hact, h, Module.Basis.repr_self]
  have h1 := congrFun (hx g) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← Algebra.smul_def] at h1
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Finsupp.single_apply, hij]
  · simp


omit J in
theorem exists_symbol_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsDR (P.PD K) T.ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)), (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∃ (u : Fin d → ℤ) (y : Fin d → Fin d → P.R.BdR), (∀ k i, y k i ∈ (P.PD K).Fil 0) ∧ (∀ k, ∑ i, b i ⊗ₜ[ℚ_[l]] (y k i * ((t ^ u k : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ) ∧ LinearIndependent (PadicComplex l) (fun k i => θ.θ (y k i)) ∧ ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ (fun i => θ.θ (y k i)) = fun i => θ.θ (y k i) := by
  intro l _ P AI J K LL T hDR d b M hM t ht
  obtain rfl : t = tU P := Units.ext ht
  obtain ⟨x, u, hx, hind⟩ := exists_adapted (P.PD K) T.ρ b LL.2 T.fdim hDR
  have key : ∀ k i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i ∈ (P.PD (botExt l)).Fil 0 :=
    fun k i => (shift_iff J (u k) 0 _).2 (by
      rw [add_zero]; exact (mem_iff K _ _).1 ((hx k).2 i))
  have heq : ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ
      (fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i)) =
      fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i) := by
    intro σ hσ k
    funext i
    generalize hN : (fun i j => b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i : Fin d → Fin d → ℚ_[l]) = N
    have hN' : ∀ i j, b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i = N i j := fun i j => congrFun (congrFun hN i) j
    have h1 := congrFun ((hx k).1 ⟨σ, hσ⟩) i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, P.PD_actdR, hN'] at h1
    have h2 : ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i =
        ∑ j, algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l)
          (((P.χQ σ ^ u k : ℚ_[l]ˣ) : ℚ_[l]) * N i j)) *
          P.actQdR σ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k j) := by
      conv_lhs => rw [← h1]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, shift_act, ← IsScalarTower.algebraMap_apply,
        map_mul (algebraMap ℚ_[l] P.R.BdR), mul_left_comm, mul_assoc]
    conv_rhs => rw [h2, theta_comb J _ _ fun j => act_mem σ (key k j)]
    simp only [twAct, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [J.θ_act σ _ (key k j), hM ⟨σ, hσ⟩ i j, hN', ← mul_assoc, chiC, ← map_mul]
    rfl
  refine ⟨u, fun k i => ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i,
    fun k i => (mem_iff K _ _).2 (key k i), fun k => ?_, ?_, heq⟩
  · have : ∀ i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i *
        ((tU P ^ u k : P.R.BdRˣ) : P.R.BdR) = x k i := fun i => by
      rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
        one_mul]
    simp only [this]
    exact sum_mem_DdR (P.PD K) T.ρ b _ (hx k).1
  · refine GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise l AI.actC P.χQ (GK K) K.1
      (tate_invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K) d d M _ u heq ?_
    intro a c hc hs
    refine hind a c hc fun i => ?_
    have h1 := congrFun hs i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← theta_comb J (fun k => ((c k : ↥K.1) : Om l)) _ (fun k => key k i),
      J.θ_ker _ (Submodule.sum_mem _ fun k _ => om_mul_mem _ (key k i))] at h1
    rw [mem_iff K, ← shift_iff J, Finset.mul_sum]
    convert h1 using 2 with k
    by_cases hk : u k = a
    · rw [hk, mul_left_comm]
      rfl
    · simp [hc k hk]

end GlobalTheory.DeRhamSymbolBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem exists_upper_mul_inc : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]), ∃ (p : GL (Fin n) ℚ_[g]) (k : GL (Fin n) ℤ_[g]), (∀ i j : Fin n, j < i → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) ∧ h = p * inc g n k := by
  intro g hg n h
  have hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  obtain ⟨k, U, hk, hU, -, hA⟩ := Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet

  have hUdet : IsUnit U.det := by
    rw [hA, Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  let K : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit
  have hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) =
      k.map (algebraMap ℤ_[g] ℚ_[g]) := rfl
  refine ⟨h * inc g n K, K⁻¹, ?_, ?_⟩
  · intro i j hij
    have e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹ := by
      rw [Units.val_mul, hinc]
      calc (h : Matrix (Fin n) (Fin n) ℚ_[g]) * k.map (algebraMap ℤ_[g] ℚ_[g])
          = (h : Matrix (Fin n) (Fin n) ℚ_[g]) * (k.map (algebraMap ℤ_[g] ℚ_[g]) * U) * U⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]
        _ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]
    rw [e1]
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU hij
  · rw [map_inv, mul_inv_cancel_right]

end GlobalTheory.GLp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedMemRange
section
open Polynomial

namespace GlobalTheory.FixedMemRange

theorem fixed_mem_range {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure (ZMod g)} (hw : w ^ g ^ d = w) :
    ∃ k : GaloisField g d,
      ((IsAlgClosed.lift : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g)) : GaloisField g d → AlgebraicClosure (ZMod g)) k = w := by
  classical
  set ι : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift with hι
  letI : Fintype (GaloisField g d) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField g d) = g ^ d := by rw [Fintype.card_eq_nat_card]; exact GaloisField.card g d hd.ne'
  have hq : 1 < g ^ d := Nat.one_lt_pow hd.ne' hg.out.one_lt
  set P : (AlgebraicClosure (ZMod g))[X] := X ^ (g ^ d) - X with hP
  have hP0 : P ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hPdeg : P.natDegree = g ^ d := Polynomial.natDegree_X_pow_sub_X hq
  have hsub : Finset.univ.image ι ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have hk : k ^ g ^ d = k := by
      rw [← hcard]; exact FiniteField.pow_card k
    simp [hP, IsRoot, sub_eq_zero, ← map_pow, hk]
  have hle : P.roots.toFinset.card ≤ (Finset.univ.image ι).card := by
    have hinj : Function.Injective ι := fun a b h => (RingHom.injective ι.toRingHom) h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard, ← hPdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hwm : w ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp [hP, IsRoot, sub_eq_zero, hw]
  rw [← heq] at hwm
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hwm
  exact ⟨k, hk⟩

theorem main : (let d1 : (g : ℕ) → ℕ → [Fact (Nat.Prime g)] → Type := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ GaloisField g d); let d2 : (g d : ℕ) → [inst : Fact (Nat.Prime g)] → d1 g d →ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ IsAlgClosed.lift); ∀ {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ}, (0 : ℕ) < d → ∀ {w : Formalism.CyclotomicNorms.Fbar g}, w ^ g ^ d = w → ∃ (k : d1 g d), (d2 g d : d1 g d → Formalism.CyclotomicNorms.Fbar g) k = w) := by
  intro d1 d2 g hg d hd w hw
  exact fixed_mem_range hd hw

end GlobalTheory.FixedMemRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem goodO_ringOfIntegers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalSelmer
section
namespace GlobalTheory.Proof.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i) (k : ℕ) (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)), InR' D.nd r S 1 → UnrOut i r Xs → ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i (cocW i r S Xs ψ) v = ⊥ := by
  intro D i r Xs S k ψ hone hU v h1 h2 h3
  have hY : ∀ γ, InY D.nd r S (yg D.nd r S γ) := fun γ =>
    ⟨1, fun _ => 1, fun _ => γ, fun _ => hone, by simp⟩
  have hy : ∀ γ x', yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
    intro γ x'
    simp [yg, rTwO, twistM, sub_mul]
  rw [resIne, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, -, h0, rfl⟩, rfl⟩
  funext γ
  exact h0 _ (hY γ.1) fun x' hx => by rw [hy, hU v h1 h2 h3 _ hx γ.1 γ.2]; simp

end GlobalTheory.Proof.LocalGlobalSelmer
end

