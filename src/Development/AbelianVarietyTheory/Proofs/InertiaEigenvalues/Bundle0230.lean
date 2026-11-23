module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExt
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.InvDescent

theorem exists_invariant_of_subgroup {G F Ω V : Type} [Group G] [Field F] [Field Ω]
    [AddCommGroup V] [Module Ω V] (H : Subgroup G) [Finite (G ⧸ H)]
    (ι : F →* Ω) (σ : G → Ω →* Ω) (hσ : ∀ g h c, σ (g * h) c = σ g (σ h c))
    (hσ1 : ∀ c, σ 1 c = c)
    (hH : ∀ g, g ∈ H ↔ ∀ c, σ g (ι c) = ι c)
    (A : G → V →+ V) (hA : ∀ g h v, A (g * h) v = A g (A h v))
    (hAs : ∀ g (c : Ω) v, A g (c • v) = σ g c • A g v)
    (N₀ N₁ : Submodule Ω V) (hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀)
    (y : V) (hy : ∀ h ∈ H, A h y = y) (h0 : y ∈ N₀) (h1 : y ∉ N₁) :
    ∃ z, (∀ g, A g z = z) ∧ z ∈ N₀ ∧ z ∉ N₁ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _

  have key : ∀ (v : V), (∀ h ∈ H, A h v = v) → ∀ g g' : G,
      (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g' → A g v = A g' v := by
    intro v hv g g' hgg'
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hgg', by group⟩
    rw [hA, hv h hh]
  have hfix : ∀ c : F, ∀ h ∈ H, A h (ι c • y) = ι c • y := by
    intro c h hh
    rw [hAs, hy h hh, ((hH h).mp hh) c]

  let T : F → V := fun c => ∑ q : G ⧸ H, A q.out (ι c • y)
  have hTinv : ∀ c g, A g (T c) = T c := by
    intro c g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, map_sum, ← hA]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun q => ?_)
    apply key _ (hfix c)
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hT0 : ∀ c, T c ∈ N₀ := by
    intro c
    refine Submodule.sum_mem _ (fun q _ => ?_)
    rw [hAs]
    exact N₀.smul_mem _ (hN _ _ h0)
  by_contra hcon
  push Not at hcon
  have hT1 : ∀ c, T c ∈ N₁ := fun c => hcon (T c) (hTinv c) (hT0 c)

  let χ : G ⧸ H → (F →* Ω) := fun q => (σ q.out).comp ι
  have hσinv : ∀ g x, σ g⁻¹ (σ g x) = x := by
    intro g x
    rw [← hσ, inv_mul_cancel, hσ1]
  have hχ : Function.Injective χ := by
    intro q q' hqq'
    have hcq : ∀ c : F, σ q.out (ι c) = σ q'.out (ι c) := fun c => DFunLike.congr_fun hqq' c
    have hmem : q.out⁻¹ * q'.out ∈ H := by
      rw [hH]
      intro c
      rw [hσ, ← hcq, hσinv]
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr hmem
  have hli : LinearIndependent Ω (fun q => (χ q : F → Ω)) :=
    (linearIndependent_monoidHom F Ω).comp χ hχ

  let w : G ⧸ H → V ⧸ N₁ := fun q => N₁.mkQ (A q.out y)
  have hrel : ∀ c : F, ∑ q, χ q c • w q = 0 := by
    intro c
    have hz := (Submodule.Quotient.mk_eq_zero N₁).mpr (hT1 c)
    simp only [T, hAs] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sum] at hz
    simpa [χ, w] using hz
  have hw : ∀ q, w q = 0 := by
    intro q
    rw [← Module.forall_dual_apply_eq_zero_iff Ω]
    intro φ
    have hsum : ∑ q', φ (w q') • (χ q' : F → Ω) = 0 := by
      funext c
      have hcq := congrArg φ (hrel c)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hcq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcq]
      exact Finset.sum_congr rfl (fun q' _ => mul_comm _ _)
    exact Fintype.linearIndependent_iff.mp hli _ hsum q
  have hy1 : A (QuotientGroup.mk (1 : G) : G ⧸ H).out y = y := by
    rw [key y hy _ 1 (QuotientGroup.out_eq' _)]
    exact hy 1 H.one_mem
  have hw1 := hw (QuotientGroup.mk 1)
  simp only [w, Submodule.mkQ_apply, hy1, Submodule.Quotient.mk_eq_zero] at hw1
  exact h1 hw1

variable {l : ℕ} [Fact l.Prime]

theorem smul_mem_Fil (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {x : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil a) : c • x ∈ (P.PD K).Fil a := by

  have hint : IsIntegral ℚ_[l] c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  obtain ⟨K', hcK⟩ : ∃ K' : FinExt l, c ∈ K'.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {c}, IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] c⟩
  have hx' : x ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, ← P.PD_Fil K K' a]
    exact hx
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]
  exact ((P.PD K').Fil a).smul_mem (⟨c, hcK⟩ : K'.1) hx'

noncomputable def filOm (P : LocPrime l) (K : FinExt l) (a : ℤ) : Submodule (Om l) P.R.BdR where
  carrier := ((P.PD K).Fil a : Set P.R.BdR)
  zero_mem' := ((P.PD K).Fil a).zero_mem
  add_mem' := fun h h' => ((P.PD K).Fil a).add_mem h h'
  smul_mem' := fun c _ hx => smul_mem_Fil P K a c hx

theorem finite_quot (K E : FinExt l) : Finite (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) := by
  classical
  have : FiniteDimensional ℚ_[l] E.1 := E.2

  let f : (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) → (E.1 →ₐ[ℚ_[l]] Om l) :=
    fun q => ((q.out : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp E.1.val
  refine Finite.of_injective f (fun q q' hqq' => ?_)
  have hres : ∀ x : E.1, (q.out : GQ l) x = (q'.out : GQ l) x := fun x => DFunLike.congr_fun hqq' x
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ ∈ IntermediateField.fixingSubgroup E.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' := hres ⟨x, hx⟩
  simp only at hx'
  rw [AlgEquiv.mul_apply, ← hx']
  exact AlgEquiv.symm_apply_apply _ _

theorem jump_descends (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l) (_hKE : K.1 ≤ E.1)
    (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l])
    (hM : ∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) (a : ℤ) (y : Fin d → P.R.BdR)
    (hy : ∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (y i)) = y)
    (h0 : ∀ i, y i ∈ (P.PD K).Fil a) (h1 : ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1))) :
    ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧
      ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  have := finite_quot K E
  let am := algebraMap ℚ_[l] P.R.BdR

  let A : ↥(GK K) → (Fin d → P.R.BdR) →+ (Fin d → P.R.BdR) := fun g =>
    AddMonoidHom.mk' (fun v => ((M g).map am).mulVec (fun i => P.actQdR g (v i)))
      (fun v w => by simp only [Pi.add_apply, map_add (f := _)]; exact Matrix.mulVec_add _ _ _)
  have hAapp : ∀ g v, A g v = ((M g).map am).mulVec (fun i => P.actQdR g (v i)) := fun _ _ => rfl
  let σ : ↥(GK K) → Om l →* Om l := fun g => MonoidHom.ofClass (g : GQ l)
  let ι : ↥E.1 →* Om l := MonoidHom.ofClass E.1.val
  have hσ : ∀ g h c, σ (g * h) c = σ g (σ h c) := fun g h c => by
    simp only [σ, MonoidHom.coe_ofClass, Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hσ1 : ∀ c, σ 1 c = c := fun c => by
    simp only [σ, MonoidHom.coe_ofClass, OneMemClass.coe_one, AlgEquiv.one_apply]
  have hH : ∀ g, g ∈ (GK E).subgroupOf (GK K) ↔ ∀ c, σ g (ι c) = ι c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    unfold GK
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h c => h c c.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcomm : ∀ (f : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) (N : Matrix (Fin d) (Fin d) ℚ_[l])
      (w : Fin d → P.R.BdR), (fun i => f ((N.map am).mulVec w i)) = (N.map am).mulVec (fun i => f (w i)) := by
    intro f N w
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, am, AlgEquiv.commutes]
  have hA : ∀ g h v, A (g * h) v = A g (A h v) := by
    intro g h v
    rw [hAapp, hAapp, hAapp, hcomm, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← hM g g.2 h h.2, Subgroup.coe_mul]
    congr 1
    funext i
    rw [map_mul, AlgEquiv.mul_apply]
  have hAs : ∀ g (c : Om l) v, A g (c • v) = σ g c • A g v := by
    intro g c v
    rw [hAapp, hAapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Algebra.smul_def,
      map_mul, P.actQdR_Om, Finset.mul_sum, σ, MonoidHom.coe_ofClass]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  let N₀ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K a)
  let N₁ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K (a + 1))
  have hmem : ∀ (b : ℤ) (v : Fin d → P.R.BdR),
      v ∈ Submodule.pi Set.univ (fun _ => filOm P K b) ↔ ∀ i, v i ∈ (P.PD K).Fil b := by
    intro b v
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀ := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro i
    rw [hAapp]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hj : P.actQdR g (v j) ∈ (P.PD K).Fil a := by
      rw [← P.PD_actdR K g]
      exact (P.PD K).Fil_G g a _ (hv j)
    rw [Matrix.map_apply, ← Algebra.smul_def]
    exact Submodule.smul_of_tower_mem _ _ hj
  obtain ⟨z, hzA, hz0, hz1⟩ := exists_invariant_of_subgroup ((GK E).subgroupOf (GK K)) ι σ hσ hσ1 hH
    A hA hAs N₀ N₁ hN y (fun h hh => hy h ((Subgroup.mem_subgroupOf).mp hh)) ((hmem a y).mpr h0)
    (fun h => h1 ((hmem (a + 1) y).mp h))
  exact ⟨z, fun g hg => hzA ⟨g, hg⟩, (hmem a z).mp hz0, fun h => hz1 ((hmem (a + 1) z).mpr h)⟩

end GlobalTheory.InvDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem deRham_invariants_coord_finrank :
    ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV hL hfin hrk Φ hΦ
  haveI := PD.finK
  let D : Submodule K (Fin d → BdR) :=
    { carrier := {y | ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec
          (fun i => PD.actdR g (y i)) = y}
      add_mem' := by
        intro a b ha hb g
        have : (fun i => PD.actdR g ((a + b) i)) =
            (fun i => PD.actdR g (a i)) + (fun i => PD.actdR g (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, ha g, hb g]
      zero_mem' := by
        intro g
        have : (fun i => PD.actdR g ((0 : Fin d → BdR) i)) = 0 := by
          funext i; simp
        rw [this, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha g
        have : (fun i => PD.actdR g ((c • a) i)) = c • (fun i => PD.actdR g (a i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, ha g] }
  have hmem : ∀ z, z ∈ DdR PD ρ ↔ Φ z ∈ D := by
    intro z
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← hΦ g z]
    exact Φ.injective.eq_iff.symm
  let e : ↥(DdR PD ρ) ≃ₗ[Qp] ↥D :=
    { toFun := fun z => ⟨Φ z.1, (hmem _).1 z.2⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmem _).2 (by simpa using y.2)⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp)
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  haveI : Module.Finite Qp ↥(DdR PD ρ) := Module.Finite.trans LL _
  haveI : Module.Finite Qp ↥D := Module.Finite.equiv e
  refine ⟨D, fun y => Iff.rfl, Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K ↥D
  have h2 := Module.finrank_mul_finrank Qp LL ↥(DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  have h4 : Module.finrank Qp V = d := by simpa using Module.finrank_eq_card_basis bV
  have h5 := e.finrank_eq
  have hpos : 0 < Module.finrank Qp K := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h5, ← h2, hrk, ← h4, ← h3]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfNormSubLtOne
section
namespace GlobalTheory.RootsOfUnityClose

theorem geom_sum_close {K : Type*} [NormedField K] [IsUltrametricDist K] {z : K}
    (hz : ‖z - 1‖ < 1) (n : ℕ) :
    ‖z ^ n - 1‖ < 1 ∧ ‖(∑ i ∈ Finset.range n, z ^ i) - (n : K)‖ < 1 := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h
    exact h.trans (max_le hz.le le_rfl)
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have e : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hz)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt h1
    · have e : (∑ i ∈ Finset.range (n + 1), z ^ i) - ((n + 1 : ℕ) : K)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : K)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)

theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {m : ℕ} (h : ¬ l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)

theorem eq_of_pow_eq_one_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] {m : ℕ} (hm : 0 < m)
    (hl : ¬ l ∣ m) {a b : Formalism.BasicNotions.Loc.Om l} (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : ‖a - b‖ < 1) : a = b := by
  have hb1 : ‖b‖ = 1 := by
    have h : ‖b‖ ^ m = 1 := by rw [← norm_pow, hb, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb1; exact zero_ne_one hb1
  have hz : ‖a / b - 1‖ < 1 := by
    rw [div_sub_one hb0, norm_div, hb1, div_one]; exact hab
  have hzm : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  by_contra hne
  have hne1 : a / b - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hne ((div_eq_one_iff_eq hb0).mp h)
  have hs : (∑ i ∈ Finset.range m, (a / b) ^ i) = 0 := by
    have h := geom_sum_mul (a / b) m
    rw [hzm, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hne1
  have h := (geom_sum_close hz m).2
  rw [hs, zero_sub, norm_neg, norm_natCast_eq_one hl] at h
  exact lt_irrefl _ h

end GlobalTheory.RootsOfUnityClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfFullLattice
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

theorem exists_basis_of_fullLattice {R F M V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V]
    (f : M →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (m : M), f (c • m) = algebraMap R F c • f m)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ m, algebraMap R F c • v = f m)
    (b0 : Module.Basis ι R M) :
    ∃ b : Module.Basis ι F V, (∀ j, b j = f (b0 j)) ∧
      ∀ m i, b.repr (f m) i = algebraMap R F (b0.repr m i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) g :=
    { map_units := fun s => by
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        exact MulAction.bijective (β := V) (Units.mk0 _ h0 : Fˣ)
      surj := fun v => by
        obtain ⟨c, hc, m, hm⟩ := hfull v
        exact ⟨(m, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b0.ofIsLocalizedModule F (nonZeroDivisors R) g,
    fun j => b0.ofIsLocalizedModule_apply F _ g j,
    fun m i => b0.ofIsLocalizedModule_repr_apply F _ g m i⟩

theorem exists_basis_of_locLat {R G F LL O ι : Type} [CommRing R] [IsDomain R] [Group G]
    [TopologicalSpace G] [Field F] [Field LL] [Algebra F LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] [Algebra R F] [IsFractionRing R F] [Algebra R O] [Fintype ι]
    (T : LocLat G F LL O)
    (hc : ∀ c : R, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hden : ∀ a : LL, ∃ c : R, c ≠ 0 ∧
      ∃ o : O, algebraMap O LL o = algebraMap F LL (algebraMap R F c) * a) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b0 : Module.Basis ι R ↥T.L.T, ∃ b : Module.Basis ι F T.V, (∀ j, b j = (b0 j : T.V)) ∧
      (∀ (m : ↥T.L.T) i, b.repr (m : T.V) i = algebraMap R F (b0.repr m i)) ∧
      (∀ (a : O) j i, b.repr (algebraMap O LL a • b j) i =
        algebraMap R F (b0.repr ⟨_, T.L.T.smul_mem a (b0 j).2⟩ i)) ∧
      ∀ v : T.V, (∀ i, ∃ c : R, b.repr v i = algebraMap R F c) → v ∈ T.L.T := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b0
  have key : ∀ (c : R) (w : T.V), algebraMap R F c • w = algebraMap R O c • w := by
    intro c w
    rw [← algebraMap_smul LL (algebraMap R F c) w, ← algebraMap_smul LL (algebraMap R O c) w, hc]
  have hfull : ∀ v : T.V, ∃ c : R, c ≠ 0 ∧ algebraMap R F c • v ∈ T.L.T := by
    intro v
    have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', hy⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, map_mul, mul_smul, key c']
        exact T.L.T.smul_mem _ hx
      · rw [map_mul, mul_smul, key c]
        exact T.L.T.smul_mem _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', o, ho⟩ := hden a
      refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
      have := T.L.T.smul_mem o hx
      rw [← algebraMap_smul LL, ho, mul_smul, algebraMap_smul,
        smul_comm a (algebraMap R F c) x] at this
      rwa [map_mul, mul_smul]
  obtain ⟨b, hb, hr⟩ := exists_basis_of_fullLattice (R := R) (F := F)
    (T.L.T.subtype.toAddMonoidHom) Subtype.val_injective
    (fun c m => (key c m).symm)
    (fun v => by
      obtain ⟨c, hc, hv⟩ := hfull v
      exact ⟨c, hc, ⟨_, hv⟩, rfl⟩) b0
  refine ⟨b, hb, hr, fun a j i => ?_, fun v hv => ?_⟩
  · rw [← hr, hb, algebraMap_smul]
    rfl
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hv i
    rw [hc, key, hb]
    exact T.L.T.smul_mem _ (b0 i).2

theorem exists_ratBasis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ b : Module.Basis (Fin d) ℚ_[l] T.V, (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) ∧ (∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr ((a : ↥LL.1) • b j) i)) ∧ ∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  intro l _ K LL T d M A h
  letI := zlMod LL T
  obtain ⟨b0, hM, hA⟩ := h
  obtain ⟨b, hb, hr, ha, hv⟩ := exists_basis_of_locLat (R := ℤ_[l]) T (fun _ => rfl) (fun a => by
    have ha : IsAlgebraic ℤ_[l] a :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
    exact ⟨c, hc, ⟨c • a, hint⟩, Algebra.smul_def c a⟩) b0
  refine ⟨b, fun g i j => ?_, fun a i j => ?_, fun v => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · have e : T.ρ g (b j) = ((actTZ LL T g (b0 j) : ↥T.L.T) : T.V) := congrArg (T.ρ g) (hb j)
    rw [e]
    exact (hM g i j).trans
      (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (hr (actTZ LL T g (b0 j)) i).symm)
  · exact (hA a i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (ha a j i).symm)
  · exact (congrArg norm (hr ⟨v, h⟩ i)).trans_le (b0.repr ⟨v, h⟩ i).2
  · exact hv v fun i => ⟨⟨_, h i⟩, rfl⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CompactRepField

theorem exists_finiteDimensional_entries_mem_of_continuous :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  intro l _ Γ _ _ _ _ a r hr
  let H : Subgroup (GL (Fin a) (PadicAlgCl l)) := r.range
  haveI : CompactSpace H := by
    have hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l))) := by
      have : (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r := by
        ext x; simp [H]
      rw [this]; exact isCompact_range hr
    exact isCompact_iff_compactSpace.1 hc
  obtain ⟨K, hK, hmem⟩ := exists_finiteDimensional_entries_mem l H a H.subtype
    fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  refine ⟨K, hK, fun g i j => ?_⟩
  exact hmem ⟨r g, ⟨g, rfl⟩⟩ i j

end GlobalTheory.CompactRepField
end

