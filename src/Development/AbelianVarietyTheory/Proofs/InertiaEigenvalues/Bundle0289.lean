module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitFor_of_tie (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W RA RW inclR φR gR πA)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E := by
  intro e₀ h₀
  obtain ⟨e₁, f₀, hf₀, hj, hN⟩ := E.one_e
  obtain ⟨u, hu, hT⟩ := W.one_line
  have huT : u ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf₀ ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h₀ ▸ Submodule.mem_top : f₀ ∈ Submodule.span O {e₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] e₀ := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hde : d • (c • e₁) = e₁ := by
    apply E.jD_inj
    rw [map_smul, hje, hj, ← hd, TensorProduct.tmul_smul]
  refine ⟨c • e₁, hje, ⟨fun x y hxy => ?_, ?_⟩, ?_, fun g => ?_, ?_⟩
  · have h1 := congrArg (E.jD W.one) hxy
    simp only at h1
    rw [E.jD_smul, E.jD_smul, hje, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact GlobalTheory.EtaleExact.ioE_injective E
      (GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one u hu huT e₀ h₀ _ _ h1)
  · have htop : Submodule.span W.EE {c • e₁} = ⊤ := by
      refine GlobalTheory.EtaleExact.eq_top_DD E hm W.one _ ?_
      rw [eq_top_iff]
      rintro z -
      have h1 : ((1 : RW) ⊗ₜ[O] e₀ : TW RW W.one) ∈ Submodule.span RW
          (E.jD W.one '' (Submodule.span W.EE {c • e₁} : Submodule W.EE (W.DD W.one))) :=
        Submodule.subset_span ⟨c • e₁, Submodule.mem_span_singleton_self _, hje⟩
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => exact Submodule.add_mem _ ha hb
      | tmul r t =>
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
          (h₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {e₀})
        have h2 : (r ⊗ₜ[O] (a • e₀) : TW RW W.one) = (a • r) • ((1 : RW) ⊗ₜ[O] e₀) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
        rw [h2]
        exact Submodule.smul_mem _ _ h1
    intro z
    exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : z ∈ Submodule.span W.EE {c • e₁})
  · apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  · obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  · rw [hN]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) d, by rw [algebraMap_smul, hde]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) c, by rw [algebraMap_smul]⟩

end Generic

theorem unitPart : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H), GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitPart l P AI H F := by
  intro l _ P AI H F K s LL h
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  refine unitFor_of_tie Subtype.val_injective _
    (GlobalTheory.EtaleExact.map_ne_top_of_tie (F.E K s LL h).tie ?_ ?_)
  · rw [hp]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL
  · rw [hp]
    exact GlobalTheory.EtaleExact.sep_RW LL

end GlobalTheory.WachUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOverFinExtOfFiniteInertiaImage
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_finite_inertia : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite →
    ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1), (∀ g ∈ IK K', ρ ⟨g, GK_le hK g.2⟩ = 1) ∧
      ∀ (g : ↥(GK K')) i j, ‖(((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) -
        (1 : Matrix n n (Om l)) i j‖ < 1 := by
  intro l _ n _ _ K r ρ hρ hfin
  let F : ↥(GK K) → (n → n → Om l) := fun g i j => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hF : Continuous F := continuous_pi fun i => continuous_pi fun j => hρ.cont i j
  let cm : GL n ↥(MaximalUnramifiedExtension l) → (n → n → Om l) := fun M i j => (((M : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)
  have hcm : Function.Injective cm := by
    intro M M' h
    ext i j
    exact congrFun (congrFun h i) j
  have hone : ∀ i j, (((1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) = (1 : Matrix n n (Om l)) i j := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  let T : Set (n → n → Om l) := cm '' (ρ '' (IK K : Set ↥(GK K)) \ {1})
  have hT : T.Finite := (hfin.sdiff).image cm
  let V : Set (n → n → Om l) := {x | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} ∩ Tᶜ
  have hV : IsOpen V := by
    refine IsOpen.inter ?_ hT.isClosed.isOpen_compl
    have : {x : n → n → Om l | ∀ i j, ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} =
        ⋂ i, ⋂ j, {x : n → n → Om l | ‖x i j - (1 : Matrix n n (Om l)) i j‖ < 1} := by
      ext
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (by fun_prop) continuous_const
  have h1V : F 1 ∈ V := by
    refine ⟨fun i j => ?_, ?_⟩
    · show ‖(((ρ 1 : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1
      rw [map_one, Units.val_one, hone, sub_self, norm_zero]
      exact one_pos
    · rintro ⟨M, hM, hMF⟩
      have hM1 : M = ρ 1 := hcm hMF
      exact hM.2 (by rw [hM1, map_one]; rfl)
  have hU : IsOpen (F ⁻¹' V) := hV.preimage hF
  obtain ⟨U', hU', hUe'⟩ := isOpen_induced_iff.1 hU
  have h1' : (1 : GQ l) ∈ U' := by
    have : (1 : ↥(GK K)) ∈ Subtype.val ⁻¹' U' := by
      rw [hUe']
      exact h1V
    exact this
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')
  refine ⟨supExt K ⟨E, hE⟩, le_sup_left, ?_⟩
  have key : ∀ g : ↥(GK (supExt K ⟨E, hE⟩)),
      F ⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ ∈ V := by
    intro g
    have : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ Subtype.val ⁻¹' U' :=
      hEU (GK_le (K := ⟨E, hE⟩) (K' := supExt K ⟨E, hE⟩) le_sup_right g.2)
    rw [hUe'] at this
    exact this
  refine ⟨fun g hg => ?_, fun g i j => (key g).1 i j⟩
  have hin : (⟨g, GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left g.2⟩ : ↥(GK K)) ∈ IK K := by
    have hmap : (IK (supExt K ⟨E, hE⟩)).map (Subgroup.inclusion (GK_le (K := K) (K' := supExt K ⟨E, hE⟩) le_sup_left)) ≤
        IK K := by
      unfold IK
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨σ, hσ, rfl⟩
      intro x hx
      exact hσ x hx
    exact hmap ⟨g, hg, rfl⟩
  by_contra hne
  exact (key g).2 ⟨_, ⟨⟨_, hin, rfl⟩, hne⟩, rfl⟩

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBounds
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_main : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  intro l _ h j r y hh hr hy
  have hl : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r := fun k =>
    (_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j r (y k) hh hr (hy k)).2.1
  have hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r := by
    intro k
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm
  have hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) := hsum.hasSum
  have hg0 : 0 ≤ gam l h j r := le_trans (norm_nonneg _) (hlam 0)
  refine ⟨hHas, ?_, ?_, ?_⟩
  · have := _root_.GlobalTheory.norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0}
      (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by
        intro k hk
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
        refine le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)
        simpa using pow_le_pow_of_le_one hl0 hl.le hk1)
    simpa using this
  · have := _root_.GlobalTheory.norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅
      (gam l h j r) hg0 hHas (by
        intro k _
        refine le_trans (hterm k) ?_
        calc ‖(l : ℂ_[l])‖ ^ k * gam l h j r ≤ 1 * gam l h j r :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl.le) hg0
          _ = gam l h j r := one_mul _)
    simpa using this
  · have hsh := _root_.GlobalTheory.PSer.Laws.sh_laws l

    have key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x := by
      intro N
      induction N with
      | zero => intro x _; simp
      | succ N ih =>
        intro x hx
        have hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r := by
          rw [hsh.2.2.2.1, norm_pow]
          have h1 : ‖sh x‖ ≤ 1 := hsh.2.2.2.2.1 x
          have hpos : 1 ≤ l ^ (h * N) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
          exact le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx
        have e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h := by
          rw [← pow_mul, ← pow_add, Nat.mul_succ]
        rw [e, (_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]
        ring
    intro N
    unfold abelian₂
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [key N (y k) (hy k)]
    ring

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrime
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PolyRoot

theorem key_exp (l : ℕ) [Fact l.Prime] (h : ℕ) (P : ℝ) (hP : 0 < P) (k : ℤ) :
    P ^ ((l:ℝ) ^ k) * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P ^ ((l:ℝ) ^ (k + h)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_add hP, zpow_add₀ hl, zpow_natCast]
  congr 1; ring

theorem rho_pow (l : ℕ) [Fact l.Prime] (h D n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ n) = P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ ((n:ℤ) - D)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
  congr 1; push_cast; ring

theorem poly_root_mod_l : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  intro l _ h μ σ h1 hμ hσ
  obtain ⟨pwadd, pwmul, pwzero, pwcomp, pwnat, pwpow, pwnorm⟩ := _root_.GlobalTheory.PSer.PwLaws.pw_laws l
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := _root_.GlobalTheory.PSer.Laws.sh_laws l
  obtain ⟨m, hm, ⟨k0, hk0⟩, hsum⟩ := _root_.GlobalTheory.PSer.exists_coef_hasSum_lam l h μ h1 hμ
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = ‖(l : ℂ_[l])‖ := ⟨_, rfl⟩
  rw [← hPd]
  have hP0 : 0 < P := hPd ▸ norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hP1 : P < 1 := hPd ▸ GlobalTheory.RingBasics.norm_p_lt
  have hσn : ‖sh σ‖ = P := by rw [hσ, hPd]
  obtain ⟨α, hα⟩ : ∃ α : ℤ → ℂ_[l], ∀ k, α k = m k * sh (pw k σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ → ℝ, ∀ k, β k = ‖α k‖ := ⟨_, fun _ => rfl⟩
  have hshσ : ∀ k : ℤ, ‖sh (pw k σ)‖ = P ^ ((l:ℝ) ^ k) := fun k => by rw [pwnorm, hσn]
  have hβ : ∀ k, β k = ‖m k‖ * P ^ ((l:ℝ) ^ k) := fun k => by
    rw [hβd, hα, norm_mul, hshσ]
  have hkey : ∀ k : ℤ, β k * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P * β (k + h) := fun k => by
    rw [hβ, hβ, hm k, norm_mul, ← hPd, ← key_exp l h P hP0 k]; ring
  have hσlt : ‖sh σ‖ < 1 := hσn ▸ hP1
  have hαsum : Summable α := by
    have := (hsum σ hσlt).summable
    rwa [show (fun k : ℤ => m k * sh (pw k σ)) = α from funext fun k => (hα k).symm] at this
  have hβt : Filter.Tendsto β Filter.cofinite (nhds 0) := by
    have := (hαsum.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    rwa [show (fun k => ‖α k‖) = β from funext fun k => (hβd k).symm] at this
  have hβne : ∃ k, β k ≠ 0 := ⟨k0, by
    rw [hβ]; exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (Real.rpow_pos_of_pos hP0 _).ne'⟩
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by rw [hβd]; exact norm_nonneg _
  obtain ⟨D, E, M, hD, hME, hpos, hmax, hstrict, htail⟩ :=
    _root_.GlobalTheory.window_around_last_max β P h hP0 hβ0 hβne hβt
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ((M + h : ℕ) : ℤ) - D := ⟨_, rfl⟩
  rw [← hN] at hpos hmax hstrict htail
  have htn : ‖α N‖ = β N := (hβd N).symm
  have ht0 : α N ≠ 0 := by intro h0; rw [← norm_eq_zero, htn] at h0; linarith
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlD : (0:ℝ) < (l:ℝ) ^ D := by positivity
  have hnorm_a : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ = β ((k:ℤ) - D) / β N := fun k => by
    rw [norm_div, htn, ← hβd]
  have hprod : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ * (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ k)
      = P * β ((k:ℤ) - D + h) / β N := fun k => by
    rw [hnorm_a, rho_pow l h D k P hP0.le, div_mul_eq_mul_div, hkey]
  refine ⟨α N, D, E, M, fun k : ℕ => α ((k:ℤ) - D) / α N, P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D),
    ht0, hME, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    show ‖α ((k:ℤ) - D) / α N‖ ≤ 1
    rw [hnorm_a, div_le_one hpos]; exact hmax _
  · show ‖α (((M + h : ℕ) : ℤ) - D) / α N‖ = 1
    rw [← hN, div_self ht0, norm_one]
  · have he : ((l:ℝ) ^ h - 1) / (l:ℝ) ^ D ≤ 1 := by
      rw [div_le_one hlD]
      have : (l:ℝ) ^ h ≤ (l:ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
      linarith
    calc P = P ^ (1:ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hP0 hP1.le he
  · have hq : (l:ℝ) ≤ (l:ℝ) ^ h := le_self_pow₀ (by linarith) (by omega)
    exact Real.rpow_lt_one hP0.le hP1 (div_pos (by linarith) hlD)
  · rw [rho_pow l h D D P hP0.le, sub_self, zpow_zero, mul_one, ← Real.rpow_natCast P (l ^ h)]
    rw [show P * P ^ ((l:ℝ) ^ h - 1) = P ^ ((1:ℝ) + ((l:ℝ) ^ h - 1)) by
      rw [Real.rpow_add hP0, Real.rpow_one]]
    congr 1; push_cast; ring
  · show ‖α ((M:ℤ) - D) / α N‖ * _ = P
    rw [hprod, show (M:ℤ) - D + h = N by rw [hN]; push_cast; ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
  · intro k hk _
    show ‖α ((k:ℤ) - D) / α N‖ * _ < P
    rw [hprod, div_lt_iff₀ hpos]
    exact mul_lt_mul_of_pos_left (hstrict _ (by omega)) hP0
  · intro u
    have hx : ‖sh (σ * u ^ l ^ D)‖ < 1 := by
      rw [shmul, shpow, norm_mul, norm_pow, hσn]
      calc P * ‖sh u‖ ^ l ^ D ≤ P * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (shle u)) hP0.le
        _ < 1 := by rw [mul_one]; exact hP1
    have hS := hsum _ hx
    have hf : ∀ k : ℤ, m k * sh (pw k (σ * u ^ l ^ D)) = α k * sh (pw (k + D) u) := fun k => by
      rw [hα, pwmul, ← pwnat D u, ← pwcomp, shmul]; ring
    rw [show (fun k : ℤ => m k * sh (pw k (σ * u ^ l ^ D))) = fun k => α k * sh (pw (k + D) u)
      from funext hf] at hS
    have htr := _root_.GlobalTheory.norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ (fun k => α k * sh (pw (k + D) u)) _
      ((Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D)) (P * ‖α N‖)
      (mul_nonneg hP0.le (norm_nonneg _)) hS (by
        intro j hj
        have hj' : j < -(D:ℤ) ∨ (E:ℤ) - D < j := by
          by_contra hc
          push_neg at hc
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + D).toNat, Finset.mem_range.2 (by omega), by omega⟩
        show ‖α j * sh (pw (j + D) u)‖ ≤ P * ‖α N‖
        rw [norm_mul, ← hβd, htn]
        exact (mul_le_of_le_one_right (hβ0 j) (shle _)).trans (htail j hj'))
    have heq : ∑ j ∈ (Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D), α j * sh (pw (j + D) u)
        = α N * ∑ k ∈ Finset.range (E + 1), α ((k:ℤ) - D) / α N * sh u ^ l ^ k := by
      rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_add_cancel, pwnat, shpow]
      field_simp
    rw [heq] at htr
    exact htr

end GlobalTheory.PolyRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGalois
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.IoComm

variable {l : ℕ} [Fact l.Prime]

theorem transfer {Z O A W S : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing W] [CommRing S]
    [Algebra Z O] [Algebra Z A] [Algebra Z W] (j : A →ₐ[Z] W)
    (hj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) j))
    (ψ : A →ₐ[Z] A) (Ψ : W →ₐ[Z] W) (h : ∀ w, Ψ (j w) = j (ψ w)) (f f' : O ⊗[Z] A →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[Z] w) = f (o ⊗ₜ[Z] ψ w)) (x y : O ⊗[Z] A)
    (hxy : Algebra.TensorProduct.map (AlgHom.id O O) j y =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j x)) :
    f y = f' x := by
  let Φ : O ⊗[Z] A →ₐ[O] O ⊗[Z] A := Algebra.TensorProduct.map (AlgHom.id _ _) ψ
  have h1 : ∀ z : O ⊗[Z] A, Algebra.TensorProduct.map (AlgHom.id O O) j (Φ z) =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ z : O ⊗[Z] A, f (Φ z) = f' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      rw [hf]
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h3 : y = Φ x := hj (hxy.trans (h1 x).symm)
  rw [h3, h2]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (w : Ainf l) : frobA l w = WittVector.frobenius w := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem frobW_inclWA (w : Ainf l) : frobW l (inclWA l w) = inclWA l (frobA l w) := by
  ext n
  change frobenius (Cb l) l (algebraMap (OCb l) (Cb l) (w.coeff n)) =
    algebraMap (OCb l) (Cb l) (frobenius (OCb l) l (w.coeff n))
  rw [frobenius_def, frobenius_def, map_pow]

theorem act_inclWA {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : Ainf l) :
    (AI.actWCbHom g).toAlgHom (inclWA l w) = inclWA l ((AI.actWHom g).toAlgHom w) := by
  ext n
  exact autCb_alg l (AI.actT g) (w.coeff n)

section

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
  {R : WSer Γ} (I : IoS AI R)

theorem incl_io_φ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letφ R.φ₀ a)) = φRW LL (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.φE_ext a).symm)).trans
    ((I.ioE_φ _).trans (congrArg (φRW LL) (I.ioE_ext a)))

theorem incl_io_γ (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = AI.gRW LL (g : GQ l) (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.γE_ext _ a).symm)).trans
    ((I.ioE_γ g _).trans (congrArg (AI.gRW LL (g : GQ l)) (I.ioE_ext a)))

end

theorem transfer_φ (LL : FinExt l) {S : Type} [CommRing S] (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) (x y : RA LL)
    (hxy : inclR LL y = φRW LL (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (frobA l) (frobW l) frobW_inclWA f f'
    (fun o w => by rw [frobA_apply, hf]) x y hxy

theorem transfer_γ {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (LL : FinExt l) {S : Type} [CommRing S]
    (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW g w)) (x y : RA LL)
    (hxy : inclR LL y = AI.gRW LL g (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (AI.actWHom g).toAlgHom
    (AI.actWCbHom g).toAlgHom (act_inclWA AI g) f f' (fun o w => hf o w) x y hxy

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  intro l _ P AI K s LL Γ R I S _ f f'
  exact ⟨fun hf a => transfer_φ LL f f' hf _ _ (incl_io_φ I a),
    fun g hf a => transfer_γ AI (g : GQ l) LL f f' hf _ _ (incl_io_γ I g a)⟩

end GlobalTheory.HWL.IoComm
end
end

