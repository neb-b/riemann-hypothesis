module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocusStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_immersion_generic_unit_locus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R), IsClosedImmersion i → LocallyOfFiniteType q → QuasiCompact q → (∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) → ∃ y : Sp B ⟶ Z, y ≫ i = x) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  first | exact @GlobalTheory.GenSpread.ClosedFac.exists_lift | exact GlobalTheory.GenSpread.ClosedFac.exists_lift | (intros; apply GlobalTheory.GenSpread.ClosedFac.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : n ≠ 0) (hJ : 2 ≤ J)
    (t : ZMod (n ^ J)) (ht : n • t = 0) : ∃ s : ZMod (n ^ J), t = n • s := by
  have : NeZero (n ^ J) := ⟨pow_ne_zero _ hn⟩
  have hv : n ^ J ∣ n * t.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact ht
  obtain ⟨k, hk⟩ := hv
  have h1 : t.val = n * (n ^ (J - 2) * k) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
    rw [hk, show n ^ J = n * (n * n ^ (J - 2)) by
      rw [← pow_succ', ← pow_succ']; congr 1; omega]
    ring
  refine ⟨((n ^ (J - 2) * k : ℕ) : ZMod (n ^ J)), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← h1, ZMod.natCast_zmod_val]

theorem closure_eq_ker_of_meets_torsion_cosets :
    ∀ (I X : Type) [AddCommGroup X] [Module.Free ℤ X] (n J M : ℕ), n ≠ 0 → 2 ≤ J → M = n ^ J → ∀ (yy : (I → ZMod M) →+ X ⧸ (nsmulAddMonoidHom M : X →+ X).range), Function.Surjective yy → ∀ Z : Set (I → ZMod M), Z ⊆ yy.ker → (∀ a ∈ yy.ker, ∃ b, n • b = 0 ∧ a + b ∈ Z) → AddSubgroup.closure Z = yy.ker := by
  intro I X _ _ n J M hn hJ hM yy hyy Z hZ hcov
  subst hM
  have key : ∀ b : I → ZMod (n ^ J), n • b = 0 → b ∈ yy.ker → ∃ k ∈ yy.ker, n • k = b := by
    intro b hb hbk
    have hc : ∀ i, ∃ s, b i = n • s := fun i =>
      zmod_pow_exists_eq_nsmul_of_nsmul_eq_zero n J hn hJ (b i) (by
        simpa using congrFun hb i)
    choose c hc using hc
    have hbc : b = n • c := funext fun i => by simpa using hc i
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (yy c)
    have hnx : n • x ∈ (nsmulAddMonoidHom (n ^ J) : X →+ X).range := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, hx, ← map_nsmul, ← hbc]
      exact hbk
    obtain ⟨x', hx'⟩ := hnx
    have hx'' : (n ^ J) • x' = n • x := hx'
    have hxx : x = n ^ (J - 1) • x' := by
      have h2 : (n : ℤ) • x = (n : ℤ) • (n ^ (J - 1) • x') := by
        rw [natCast_zsmul, natCast_zsmul, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega]
        exact hx''.symm
      exact smul_right_injective X (by exact_mod_cast hn) h2
    obtain ⟨c', hc'⟩ := hyy (QuotientAddGroup.mk x')
    refine ⟨c - n ^ (J - 1) • c', ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, map_nsmul, hc', ← QuotientAddGroup.mk_nsmul, ← hxx, hx,
        sub_self]
    · have h0 : (n ^ J) • c' = 0 := funext fun i => by
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [smul_sub, smul_smul, ← pow_succ', show J - 1 + 1 = J by omega, ← hbc, h0, sub_zero]
  apply le_antisymm
  · exact (AddSubgroup.closure_le _).2 hZ
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    have hbk : b ∈ yy.ker := by
      have h3 : yy (a + b) = 0 := hZ hab
      rw [AddMonoidHom.mem_ker] at ha ⊢
      rwa [map_add, ha, zero_add] at h3
    obtain ⟨k, hk, hkb⟩ := key b hb hbk
    obtain ⟨b', hb', hkb'⟩ := hcov k hk
    have h4 : a = (a + b) - n • (k + b') := by
      rw [smul_add, hb', add_zero, hkb, add_sub_cancel_right]
    rw [h4]
    exact sub_mem (AddSubgroup.subset_closure hab) (nsmul_mem (AddSubgroup.subset_closure hkb') n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EEContainsStableWeightZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.LatticeStable

open FreeNear TestBasis

theorem quadratic_nonneg {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  obtain ⟨b, hb⟩ := hq.exists_forall_le
  have h0 : q b ≤ 0 := by simpa using hb 0
  have h2 := hb ((2 : ℤ) • b)
  rw [QuadraticMap.map_smul] at h2
  simp only [zsmul_eq_mul] at h2
  push_cast at h2
  have := hb a
  linarith

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem operator_comm_proj (H : AddSubgroup S.Gam) {h : S.Gam} (hh : h ∈ H) (c : S.perp H →+ ZMod S.N) :
    S.ρ h * S.proj (S.perp H) c = S.proj (S.perp H) c * S.ρ h := by
  have := Fintype.ofFinite (S.perp H)
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : eStd S.g _ (t : S.Gam) h = 0 := t.2 h hh
  rw [mul_smul_comm, smul_mul_assoc, S.ρ_add _ _ (by rw [Weights.eStd_swap, h1, neg_zero, smul_zero]),
    S.ρ_add _ _ (by rw [h1, smul_zero]), add_comm]

variable {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem single_mem_testLattice [hA : ArithBase o Ω] (i : S.J) : Pi.single i (1 : PadicAlgCl p) ∈ τ.E := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨-, hsum⟩ := proj_orthogonal S _ τ.isoFree
  have h1 : Pi.single i (1 : PadicAlgCl p) = ∑ c : S.perp τ.yy.ker →+ ZMod S.N,
      fun j => 1 * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    funext j
    rw [Finset.sum_apply]
    simp only [_root_.one_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum, ← Matrix.sum_apply, hsum, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [h1]
  refine Submodule.sum_mem _ fun c _ => Submodule.subset_span ?_
  obtain ⟨α, hα, rfl⟩ := (test_weights o Ω S p y₀ τ).1 c
  refine ⟨α, 1, i, hα, ?_, rfl⟩
  rw [norm_one]
  exact Real.one_le_exp (div_nonneg (quadratic_nonneg τ.q τ.pos α) (Nat.cast_nonneg _))

theorem operator_mem_testLattice (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {h : S.Gam} (hh : h ∈ τ.yy.ker)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) :
    (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) * w k) ∈ τ.E := by
  induction hw using Submodule.span_induction with
  | mem _ h' =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := h'
    have h1 : (fun j => ∑ k, y₀ (algebraMap o S.R (S.ρ h j k)) *
        (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) k i)))) =
        ∑ k, (⟨_, (mem_OO_iff _).2 (hint (S.ρ h k i))⟩ : OO p) •
          fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)) := by
      funext j
      have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a))
        (congrFun (congrFun (operator_comm_proj _ hh (τ.wt α)) j) i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
      rw [Finset.sum_apply]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (h2.trans (Finset.sum_congr rfl fun k _ => ?_))
      · ring
      · change _ = y₀ (algebraMap o S.R (S.ρ h k i)) * (l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j k)))
        ring
    rw [h1]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, l, k, hα, hl, rfl⟩)
  | zero =>
    convert Submodule.zero_mem τ.E using 1
    funext j
    simp
  | add a a' _ _ ha ha' =>
    convert Submodule.add_mem _ ha ha' using 1
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  | smul s a _ ha =>
    convert Submodule.smul_mem _ s ha using 1
    funext j
    change ∑ k, _ * ((s : PadicAlgCl p) * a k) = (s : PadicAlgCl p) * ∑ k, _ * a k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem weightZero_mem [hA : ArithBase o Ω] (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1)
    {w : S.J → PadicAlgCl p} (hw : w ∈ τ.E) (j : S.J) :
    ∑ k, w k * y₀ (algebraMap o S.R (S.proj (S.perp τ.yy.ker) 0 j k)) ∈ OO p := by
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, -⟩ := proj_orthogonal S _ τ.isoFree
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hw
  rintro _ ⟨α, l, i, hα, hl, rfl⟩
  have h2 := congrArg (fun a => l * y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul 0 (τ.wt α)) j) i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum] at h2
  rw [(Finset.sum_congr rfl fun k _ => by ring).trans h2]
  split_ifs with h0
  · have h3 := q_le_of_wt_eq τ (β := 0) hα (by rw [map_zero, h0])
    rw [map_zero] at h3
    refine mul_mem ((mem_OO_iff _).2 (hl.trans ?_)) ((mem_OO_iff _).2 (hint _))
    exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg h3 (Nat.cast_nonneg _))
  · simp

variable {M : RatModel o Ω} {U₀ : M.Z.Opens}

theorem exists_opens_regular (hne : (U₀ : Set M.Z).Nonempty) {J : Type} [Finite J] (v : J → Ω) :
    ∃ U₁ : M.Z.Opens, U₁ ≤ U₀ ∧ (U₁ : Set M.Z).Nonempty ∧ ∀ j, v j ∈ M.ringOn U₁ := by
  let W : M.Z.Opens := ⟨⋂ j, {z | v j ∈ M.O z}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
  refine ⟨U₀ ⊓ W, inf_le_left, M.nonempty_inf hne ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => ?_⟩,
    fun j => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter.1 hz.2 j⟩
  rw [Set.mem_setOf_eq, M.O_genericPoint]
  exact Algebra.mem_top

theorem over_mono (hO : S.Over₀ M U₀) {U₁ : M.Z.Opens} (hle : U₁ ≤ U₀) (hne : (U₁ : Set M.Z).Nonempty) :
    S.Over₀ M U₁ :=
  ⟨hO.normal, hO.proj, hO.div, hne, hO.le.trans (RatModel.ringOn_anti hle),
    fun x hx => RatModel.ringOn_anti hle (hO.th_unit x hx),
    fun T c k hT hk => RatModel.ringOn_anti hle (hO.FF_unit T c k hT hk)⟩

theorem val_mulVec {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (A : Matrix S.J S.J o) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U₁) (j : S.J) :
    M.val (gPt p ≫ y) ((A.map (algebraMap o Ω)).mulVec v j) =
      ∑ k, M.val (gPt p ≫ y) (v k) * y₀ (algebraMap o S.R (A j k)) := by
  obtain ⟨ξ, hξU, hsp⟩ : ∃ ξ ∈ U₁, ∀ w, (gPt p ≫ y) w ⤳ ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)⟩
  rw [← Matrix.vecMul_transpose, RatModel.val_vecMul_eq_sum (c := (A.map (algebraMap o Ω)).transpose) hsp
    (fun j => RatModel.mem_ringOn.1 (hv j) _ hξU) (fun _ _ => Subalgebra.algebraMap_mem _ _)]
  exact Finset.sum_congr rfl fun k _ => by rw [hat]; rfl

theorem norm_base_le_one {U₁ : Set M.Z} {z : M.Z} {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U₁ z y) (hat : S.At M y y₀)
    (a : o) : ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := by
  rw [hat]
  exact hc.norm_val_le_one (Subalgebra.algebraMap_mem _ a)

end GlobalTheory.ZH.LatticeStable

namespace GlobalTheory.ZH


open LatticeStable in
theorem EE_contains_stable_weightZero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, (∀ i, Pi.single i (1 : Ω) ∈ EE.E ξ) ∧ (∀ h ∈ S.HH M ξ, ∀ v ∈ EE.E ξ, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E ξ) ∧ (IsClosed ({ξ} : Set M.Z) → ∀ v ∈ EE.E ξ, ((S.proj (S.TT M ξ) 0).map (algebraMap o Ω)).mulVec v = v → ∀ j, v j ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hsup hT hEE
  have hmem : ∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → _ := fun U₁ hle hne =>
    mem_EE_iff_forall_test o Ω S M U₁ EE (over_mono hO hle hne)
      ⟨fun U hU => hloc.1 U (hU.trans hle), hloc.2⟩
      (fun z p _ y hc => htest z p y ⟨hc.1, hc.2.trans hle⟩)
      ⟨fun z hz => hEE.1 z (hle hz), fun z p _ y y₀ τ hc => hEE.2 z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩⟩
  have h1 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ i, Pi.single i (1 : Ω) ∈ EE.E z := by
    intro z hz i
    refine (hmem U₀ le_rfl hO.ne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · convert single_mem_testLattice τ i using 1
      funext j
      simp only [Pi.single_apply]
      split_ifs
      exacts [RatModel.val_one _, RatModel.val_zero _]
  have h2 : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ h ∈ S.HH M z, ∀ v ∈ EE.E z,
      ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
    intro z hz h hh v hv
    obtain ⟨U₁, hle, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hmem U₁ hle hne z hz _ fun j => ?_).2 fun p _ y y₀ τ hc hat => ?_
    · exact sum_mem fun k _ => mul_mem (Subalgebra.algebraMap_mem _ _) (hreg k)
    · have h3 := (hmem U₁ hle hne z hz v hreg).1 hv p y y₀ τ hc hat
      rw [(hsup z p y y₀ τ ⟨hc.1, hc.2.trans hle⟩ hat).2] at hh
      convert operator_mem_testLattice τ (norm_base_le_one hc hat) hh h3 using 1
      funext j
      rw [val_mulVec hc hat _ hreg]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  intro ξ
  obtain ⟨W, b, hξ, -, hE⟩ := EE.loc ξ
  obtain ⟨x, hxW, hx, hsp, hI⟩ := hT.2.2.2 ξ W hξ
  have hle : ∀ v ∈ EE.E x, v ∈ EE.E ξ := fun v hv => by
    rw [hE x hxW] at hv
    rw [hE ξ hξ]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).1 hv
    exact (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) _).2
      ⟨fun i => ⟨c i, RatModel.O_le_of_specializes hsp (c i).2⟩, rfl⟩
  refine ⟨fun i => hle _ (h1 x hx i), fun h hh v hv => ?_, fun hz v hv hP j => ?_⟩
  · have hh' : h ∈ S.HH M x := by rwa [ThetaSys.HH, hI]
    rw [hE ξ hξ] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact hle _ (h2 x hx h hh' w (by rw [hE x hxW]; exact Submodule.subset_span hw))
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add a a' _ _ ha ha' => rw [Matrix.mulVec_add]; exact add_mem ha ha'
    | smul s a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ s ha
  · obtain ⟨U₁, hle₁, hne, hreg⟩ := exists_opens_regular hO.ne v
    refine (hloc.1 U₁ hle₁ hne ξ hz).2 _ (hreg j) fun p _ y hc => ?_
    have hc₀ : M.Cen U₀ ξ y := ⟨hc.1, hc.2.trans hle₁⟩
    obtain ⟨y₀, hat, hint, ⟨τ⟩⟩ := htest ξ p y hc₀
    have h3 := (hmem U₁ hle₁ hne ξ hz v hreg).1 hv p y y₀ τ hc hat
    rw [ThetaSys.TT, (hsup ξ p y y₀ τ hc₀ hat).2] at hP
    rw [← hP, val_mulVec hc hat _ hreg, ← mem_OO_iff]
    exact weightZero_mem τ hint h3 j

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_isEE_of_adm : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hb S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have h2g := @GlobalTheory.ZH.comparison_function_regular o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2ge := @GlobalTheory.ZH.FirstIneq.ff_div_ff_mem_of_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2le := @GlobalTheory.ZH.ThetaSys.FF_div_FF_mem_O_of_valuationRing o Ω _ _ _ _ S M U₀ hO h0b h2g
  have h3h := @GlobalTheory.ZH.span_lattice_eq_of_valuationRing o Ω _ _ _ _ S M U₀ hA h0b hne h2ge h2le
  have h3b := @GlobalTheory.ZH.exists_basis_lattice_near o Ω _ _ _ _ S M U₀ hA h0b hne
  obtain ⟨EE, hE₁, hE₂⟩ := @GlobalTheory.ZH.WeightBundle.exists_lat o Ω _ _ _ _ S M U₀ hA hll.2 h0b hne h3h h3b
  exact ⟨EE, @GlobalTheory.ZH.isEE_of_span_weightSpaces o Ω _ _ _ _ S M U₀ EE hA h0a h0b hne hwt h12 hE₁ hE₂, hE₁⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsComparisonCompAlongIdentity
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.Cmp

theorem Oφ_baseChange {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by
  have hb : h ≫ T.hom = T'.hom ≫ spMap φ := by
    rw [← Over.w p, ← Category.assoc, ← hp, Category.assoc, pb.1.w, ← Category.assoc, Over.w]
  let U : Over.mk (T'.hom ≫ spMap φ) ⟶ T := Over.homMk h hb
  have e : pushPt pb.1.w p' = U ≫ p := Over.OverMorphism.ext hp
  have c : pushPt pb.1.w (toUnit T' ≫ D'.c x') = toUnit _ ≫ D.c x := Over.OverMorphism.ext (by
    show (T'.hom ≫ (D'.c x').left) ≫ β = (T'.hom ≫ spMap φ) ≫ (D.c x).left
    rw [Category.assoc, hc, ← Category.assoc])
  refine Eq.trans ?_ (WeightPf.Oφ_comp U p x κ).symm
  rw [← e]
  fin_cases κ
  · exact congrArg (fun q => q.left) ((map_mul (pushHom pb T') p' (toUnit T' ≫ D'.c x')).trans
      (congrArg (pushPt pb.1.w p' * ·) c))
  · exact congrArg (fun q => q.left) c
  · rfl
  · exact congrArg (fun q => q.left) (map_one (pushHom pb T'))

theorem exists_comp_id : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D₁ D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A₁ A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U₁ : PreU I' D₁ A₁ G') (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C₁ : Cmp φ U U₁ F) (C₂ : Cmp (RingHom.id V) U₁ U' (𝟙 G'.left)) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F C₁.pb.1.w wL → (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (j : U.P.L.L.ι) (i : U₁.P.L.L.ι) (k : U'.P.L.L.ι), F (r z) ∈ U.P.L.L.U j → r z ∈ U₁.P.L.L.U i → r z ∈ U'.P.L.L.U k → gw wL r z j k = gw C₁.wL r z j i * gw C₂.wL r z i k) → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro R V _ _ _ _ I I' φ D D₁ D' A A₁ A' G _ _ G' _ _ U U₁ U' F C₁ C₂ wL hmap hw
  have g₁ := (isGen_iff _).1 C₁.v_gen
  have g₂ := (isGen_iff _).1 C₂.v_gen
  obtain ⟨v, T⟩ := exists_comp D₁.P.isLB C₁.v C₂.v g₁ g₂ D.P.isLB D'.P.isLB
  have pbB : IsGrpPullback D'.P.A D.P.A (spMap φ) (C₂.β ≫ C₁.β) := by
    have h := C₂.pbB.comp C₁.pbB
    rwa [spMap_ringHom_id, Category.id_comp] at h
  refine ⟨{
    pb := C₁.pb
    wL := wL
    wL_map := hmap
    β := C₂.β ≫ C₁.β
    pbB := pbB
    v := v
    v_gen := (isGen_iff _).2 (T.pgen_comp D₁.P.isLB g₁ g₂)
    xe := C₂.xe.trans C₁.xe
    c_pr := fun x => by
      rw [← Category.assoc, C₂.c_pr, spMap_ringHom_id, Category.id_comp, C₁.c_pr]
      rfl
    lev := fun e Z x' x hx => ?_
    map_le := C₁.map_le }, rfl⟩
  obtain ⟨a₁, b₁⟩ := C₁.lev e Z x' x hx
  obtain ⟨a₂, b₂⟩ := C₂.lev e Z x' x' (by rw [Category.comp_id])
  refine ⟨by rw [← a₁, reassoc_of% a₂], fun z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt D₁.P.isLB z
  obtain ⟨c₁, d₁⟩ := b₁ z J J₁ hJ hJ₁
  obtain ⟨c₂, d₂⟩ := b₂ z J₁ J' hJ₁ hJ'
  have tri : ∀ f : Z ⟶ D'.P.A.left, gw v f z (J (f ≫ C₂.β ≫ C₁.β)) (J' f) =
      gw C₁.v (f ≫ C₂.β) z (J (f ≫ C₂.β ≫ C₁.β)) (J₁ (f ≫ C₂.β)) * gw C₂.v f z (J₁ (f ≫ C₂.β)) (J' f) :=
    fun f => T Z f z _ _ _ (hJ (f ≫ C₂.β ≫ C₁.β)) (hJ₁ (f ≫ C₂.β)) (hJ' f)
  refine ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩
  · have hp : (U'.gt e).pG.left ≫ C₂.β = 𝟙 _ ≫ (U₁.gt e).pG.left := by
      have := (C₂.lev e _ (𝟙 _) (𝟙 _) (by rw [Category.comp_id])).1
      rwa [Category.id_comp] at this
    have o : ∀ κ, D'.Oφ (U'.gt e).pG χ κ ≫ C₂.β = D₁.Oφ (U₁.gt e).pG (C₂.xe χ) κ := fun κ =>
      (Oφ_baseChange C₂.pbB (C₂.c_pr χ) _ _ _ hp κ).trans (Category.id_comp _)
    refine (c₁ (C₂.xe χ)).trans ?_
    rw [c₂ χ, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun κ _ => ?_)
    have t := tri (x' ≫ D'.Oφ (U'.gt e).pG χ κ)
    simp only [Category.assoc] at t
    rw [t, mul_zpow, mul_comm, ← o κ]
    simp only [Category.assoc]
  · obtain ⟨i, hi⟩ := exists_chart U₁.P.L.isLB ((fstG I' e G').left (x' z))
    have t := tri (x' ≫ (U'.gt e).pG.left)
    simp only [Category.assoc] at t
    have a : x' ≫ (U'.gt e).pG.left ≫ C₂.β ≫ C₁.β = x ≫ (U.gt e).pG.left := by rw [← a₁, reassoc_of% a₂]
    rw [a, a₂] at t
    have hk₂ : F ((x' ≫ (fstG I' e G').left) z) ∈ U.P.L.L.U k := by
      have : F ((x' ≫ (fstG I' e G').left) z) = (fstG I e G).left (x z) :=
        (congrArg (fun q : Z ⟶ G.left => q z) hx).symm
      rw [this]; exact hk
    rw [t, hw Z (x' ≫ (fstG I' e G').left) z k i k' hk₂ hi hk', _root_.mul_assoc, d₂ i k' hi hk',
      ← _root_.mul_assoc, d₁ k i hk hi, _root_.mul_assoc]

end GlobalTheory.LN.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFgSubalgebraSpecFactorThroughOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω), R.FG → ∀ V : (Sp R).Opens, (V : Set (Sp R)).Nonempty → ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  first | exact @GlobalTheory.exists_fg_subalgebra_spec_factors_open | exact GlobalTheory.exists_fg_subalgebra_spec_factors_open | (intros; apply GlobalTheory.exists_fg_subalgebra_spec_factors_open <;> assumption)
end

