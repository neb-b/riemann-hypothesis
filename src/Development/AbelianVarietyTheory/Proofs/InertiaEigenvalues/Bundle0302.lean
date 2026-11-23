module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalExactSequenceContinuityAllTheories
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology

namespace GlobalTheory.FundCont

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem l_ne : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem small_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hb : (l : P.R.BdR) ^ k * b ∈ Lat AI M n) :
    qB P c * b ∈ Lat AI M n := by
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have hz : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one h0]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, hz⟩ hb
  convert this using 1
  rw [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul]
  congr 2
  exact (div_mul_cancel₀ _ (pow_ne_zero _ l_ne)).symm

theorem large_mul_mem (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]} {b : P.R.BdR}
    (hc : ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1) (hb : b ∈ Lat AI M (k + n)) :
    qB P c * b ∈ Lat AI M n := by
  rw [← pow_mul_mem_Lat_iff AI (k := k)]
  have := qB_mul_mem_Lat AI T ⟨_, hc⟩ hb
  convert this using 1
  simp only [map_mul, map_pow, map_natCast, mul_assoc]

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (l : ℝ) ^ (-(k : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem exists_mul_le_one (c : ℚ_[l]) : ∃ k : ℕ, ‖(l : ℚ_[l]) ^ k * c‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) (ε := (‖c‖ + 1)⁻¹) (by positivity)
  refine ⟨k, ?_⟩
  rw [norm_mul, Padic.norm_p_pow]
  calc _ ≤ (‖c‖ + 1)⁻¹ * (‖c‖ + 1) := by gcongr; linarith
    _ = 1 := inv_mul_cancel₀ (by positivity)

variable {X : Type} [TopologicalSpace X]

theorem eventually_orbit (T : LocTied l P AI) {b : P.R.BdR} (hb : b ∈ FilB P 0) (M n : ℕ)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, qB P (c x) * P.actQdR (γ x) b - qB P (c x₀) * P.actQdR (γ x₀) b ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M n
  obtain ⟨j, hj⟩ := exists_mul_le_one (c x₀)
  obtain ⟨-, he⟩ := bounded_and_eventually_sub_mem_Lat l P AI T b hb M (j + n)
  have h0 : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by
    have := (Fact.out : l.Prime).pos
    positivity
  have t1 : Tendsto (fun x => (γ x₀)⁻¹ * γ x) (𝓝 x₀) (𝓝 1) := by
    have : Continuous fun x => (γ x₀)⁻¹ * γ x := continuous_const.mul hγ
    simpa using this.tendsto x₀
  filter_upwards [t1.eventually he, Metric.tendsto_nhds.1 (hc.tendsto x₀) _ h0] with x h1 h2
  rw [dist_eq_norm] at h2
  have h3 := act_mem_Lat AI (γ x) hk
  rw [map_mul, map_pow, map_natCast] at h3
  have h4 := small_mul_mem AI T h2.le h3
  have h5 := act_mem_Lat AI (γ x₀) h1
  rw [map_sub, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left] at h5
  have h6 := large_mul_mem AI T hj h5
  convert add_mem h4 h6 using 1
  rw [map_sub]
  ring

def LatCont (h : X → P.R.BdR) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (n : ℕ) (x₀ : X), ∀ᶠ x in 𝓝 x₀, tD P ^ N * (h x - h x₀) ∈ Lat AI (N + 1) n

theorem latCont_const (b : P.R.BdR) : LatCont AI (fun _ : X => b) :=
  ⟨0, fun N _ n x₀ => Eventually.of_forall fun x => by simp⟩

theorem LatCont.add {h h' : X → P.R.BdR} (H : LatCont AI h) (H' : LatCont AI h') :
    LatCont AI (fun x => h x + h' x) := by
  obtain ⟨N₀, H⟩ := H
  obtain ⟨N₁, H'⟩ := H'
  refine ⟨max N₀ N₁, fun N hN n x₀ => ?_⟩
  filter_upwards [H N (le_of_max_le_left hN) n x₀, H' N (le_of_max_le_right hN) n x₀] with x a b
  convert add_mem a b using 1
  ring

theorem LatCont.sum {ι : Type} (s : Finset ι) (h : ι → X → P.R.BdR) (H : ∀ i, LatCont AI (h i)) :
    LatCont AI (fun x => ∑ i ∈ s, h i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using latCont_const AI 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (H i).add AI ih

theorem continuous_chi : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := by
  obtain ⟨χ, h1, h2, -⟩ := exists_integral_cyclotomicChar l P
  simp only [← h1]
  have h3 : Continuous fun g => (χ g : ℤ_[l]) := Units.continuous_val.comp h2
  exact continuous_subtype_val.comp h3

theorem latCont_orbit (T : LocTied l P AI) (b : P.R.BdR)
    {c : X → ℚ_[l]} (hc : Continuous c) {γ : X → GQ l} (hγ : Continuous γ) :
    LatCont AI (fun x => qB P (c x) * P.actQdR (γ x) b) := by
  obtain ⟨a, ha⟩ := (P.PD (botExt l)).Fil_exh b
  refine ⟨(-a).toNat, fun N hN n x₀ => ?_⟩
  have hb : tD P ^ N * b ∈ FilB P 0 :=
    FilB_anti (by omega) (FilB_mul (FilB_pow tD_mem N) ha)
  have hc' : Continuous fun x => c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ :=
    hc.mul (((continuous_chi.comp hγ).pow N).inv₀ fun x => pow_ne_zero _ (Units.ne_zero _))
  have e : ∀ x, qB P (c x * ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹) * P.actQdR (γ x) (tD P ^ N * b) =
      tD P ^ N * (qB P (c x) * P.actQdR (γ x) b) := by
    intro x
    have h1 : qB P ((P.χQ (γ x) : ℚ_[l]) ^ N)⁻¹ * qB P (P.χQ (γ x) : ℚ_[l]) ^ N = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
    rw [map_mul, map_mul, map_pow, act_tD, mul_pow]
    linear_combination (tD P ^ N * (qB P (c x) * P.actQdR (γ x) b)) * h1
  filter_upwards [eventually_orbit AI T hb (N + 1) n hc' hγ x₀] with x hx
  rwa [e, e, ← mul_sub] at hx

theorem tD_pow_not_mem (T : LocTied l P AI) (N : ℕ) : tD P ^ N ∉ FilB P ((N : ℤ) + 1) := by
  have hu : IsUnit (tD P) := by
    have := (P.PD (botExt l)).t_unit
    rw [P.period_datum_t_eq] at this
    exact this.map P.ιB
  induction N with
  | zero =>
    intro h
    apply (P.PD (botExt l)).not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq]
    simpa using FilB_mul (tD_mem (P := P)) h
  | succ N ih =>
    intro h
    obtain ⟨y, hy, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) _ _).1 h
    rw [pow_succ'] at e
    apply ih
    rw [hu.mul_left_cancel e]
    exact_mod_cast hy

theorem continuous_of_latCont (T : LocTied l P AI) {c : X → ℚ_[l]}
    (H : LatCont AI (fun x => qB P (c x))) : Continuous c := by
  obtain ⟨N, H⟩ := H
  obtain ⟨n, hn⟩ : ∃ n, tD P ^ N ∉ Lat AI (N + 1) n := by
    by_contra h
    push Not at h
    exact tD_pow_not_mem AI T N (by exact_mod_cast mem_FilB_of_forall_Lat l P AI T (N + 1) _ h)
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt (l := l) hε
  filter_upwards [H N le_rfl (k + n) x₀] with x hx
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  have h0 : 0 < ‖c x - c x₀‖ := hε.trans_le hlt
  apply hn
  have := large_mul_mem AI T (c := (c x - c x₀)⁻¹) (by
    rw [norm_mul, Padic.norm_p_pow, norm_inv, ← div_eq_mul_inv, div_le_one h0]
    exact hk.le.trans hlt) hx
  rwa [← map_sub, mul_left_comm, ← map_mul, inv_mul_cancel₀ (norm_pos_iff.1 h0), map_one,
    mul_one] at this

theorem contCore_of_tied (T : LocTied l P AI) (K : FinExt l) : contCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A k x β hβ x' f hf
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  have hLL : ∀ (φ : A.V →ₗ[ℚ_[l]] ℚ_[l]) (v : A.V), Continuous fun c : LL => φ (c • v) := fun φ v =>
    IsModuleTopology.continuous_of_linearMap
      (φ ∘ₗ (LinearMap.toSpanSingleton LL A.V v).restrictScalars ℚ_[l])
  have hV : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous φ := by
    intro φ
    let b := Module.finBasis LL A.V
    have : (φ : A.V → ℚ_[l]) = fun v => ∑ j, φ (b.coord j v • b j) := by
      funext v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      simp [b.sum_repr]
    rw [this]
    exact continuous_finsetSum _ fun j _ =>
      (hLL φ (b j)).comp (IsModuleTopology.continuous_of_linearMap (b.coord j))
  have key : ∀ φ : A.V →ₗ[ℚ_[l]] ℚ_[l], Continuous fun g => φ (f g) := by
    intro φ
    let Φ : A.V ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] P.R.BdR :=
      (TensorProduct.lid ℚ_[l] P.R.BdR).toLinearMap ∘ₗ TensorProduct.map φ P.ιB.toLinearMap
    have hΦ : ∀ v b, Φ (v ⊗ₜ b) = qB P (φ v) * P.ιB b := by
      intro v b
      simp [Φ, Algebra.smul_def]
    have h1 : ∀ (y : A.V ⊗[ℚ_[l]] P.R.B) (i : Fin k), LatCont AI fun g => Φ (β i g • y) := by
      intro y i
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        simp only [TensorProduct.smul_tmul', hΦ]
        simpa using latCont_orbit AI T (P.ιB b) ((hLL φ v).comp (hβ i))
          (γ := fun _ => 1) continuous_const
      | add y y' ih ih' =>
        simp only [smul_add, map_add (f := _)]
        exact ih.add AI ih'
    have h2 : ∀ y : A.V ⊗[ℚ_[l]] P.R.B, LatCont AI fun g => Φ (actVB (P.PD K) A.ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simpa using latCont_const AI 0
      | tmul v b =>
        have e : ∀ g : ↥(GK K), Φ (actVB (P.PD K) A.ρ g (v ⊗ₜ b)) =
            qB P (φ (A.ρ g v)) * P.actQdR (g : GQ l) (P.ιB b) := by
          intro g
          rw [← ιB_act, ← hΦ, ← P.PD_actB]
          rfl
        simp only [e]
        exact latCont_orbit AI T (P.ιB b) ((hV φ).comp (A.cont v)) continuous_subtype_val
      | add y y' ih ih' =>
        simp only [map_add (f := _)]
        exact ih.add AI ih'
    apply continuous_of_latCont AI T
    have e : ∀ g, qB P (φ (f g)) =
        ∑ i, Φ (β i g • x i) + (Φ (actVB (P.PD K) A.ρ g x') + -Φ x') := by
      intro g
      have := congrArg Φ (hf g)
      rwa [hΦ, map_one, mul_one, map_add, map_sum, map_sub, sub_eq_add_neg] at this
    simp only [e]
    exact (LatCont.sum AI _ _ fun i => h1 (x i) i).add AI ((h2 x').add AI (latCont_const AI _))
  haveI : Module.Finite ℚ_[l] A.V := Module.Finite.trans LL A.V
  let b := Module.finBasis ℚ_[l] A.V
  have : f = fun g => ∑ j, algebraMap ℚ_[l] LL (b.coord j (f g)) • b j := by
    funext g
    simp [b.sum_repr]
  rw [this]
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_algebraMap ℚ_[l] LL).comp (key (b.coord j))).smul continuous_const

theorem fundamentalExactSequence_continuity_all_theories : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm6 D := fun D l _ K =>
  contCore_of_tied (D.locA l) (D.locT l) K

end GlobalTheory.FundCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesCoboundaryComplexPadic
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem ph_c_cob : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∃ b : ℝ, 0 < b ∧ ∀ (H : Subgroup ↥(GK K)) (t : ℝ), 0 < t → (∀ g ∈ H, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t) → ∀ i j, ∃ y : ℂ_[l], ∀ g ∈ H, ‖Formalism.Per.σC (g : GQ l) y - y - algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j)‖ ≤ b * t ^ 2 := by
  intro l _ n _ _ K ρ M hM
  set Mi : Matrix n n ℂ_[l] := ((M⁻¹ : GL n ℂ_[l]) : Matrix n n ℂ_[l]) with hMi
  set a : ℝ := 1 + ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) with ha
  have hterm : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) := by
    intro i j
    calc ‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖ ≤ ∑ j', (‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖(M : Matrix n n ℂ_[l]) i j'‖ + ‖Mi i j'‖)
            (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖(M : Matrix n n ℂ_[l]) i' j'‖ + ‖Mi i' j'‖))
            (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ i)
  have hMa : ∀ i j, ‖(M : Matrix n n ℂ_[l]) i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg (Mi i j); rw [ha]; linarith
  have hMia : ∀ i j, ‖Mi i j‖ ≤ a := by
    intro i j; have := hterm i j; have := norm_nonneg ((M : Matrix n n ℂ_[l]) i j); rw [ha]; linarith
  have ha0 : 0 < a := by
    rw [ha]; have : 0 ≤ ∑ i, ∑ j, (‖(M : Matrix n n ℂ_[l]) i j‖ + ‖Mi i j‖) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
    linarith
  obtain ⟨c, hc, hAx⟩ := _root_.GlobalTheory.AxLemma.ax_lemma_matrix l
  refine ⟨c * a ^ 2, by positivity, ?_⟩
  intro H t ht hρ i j
  set rC : ↥(GK K) → Matrix n n ℂ_[l] := fun g => (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) with hrCdef
  have hrent : ∀ g : ↥(GK K), ∀ i j, (rC g - 1) i j = algebraMap ℚ_[l] ℂ_[l] (((ρ g : Matrix n n ℚ_[l]) - 1) i j) := by
    intro g i j
    have e : rC g - 1 = (algebraMap ℚ_[l] ℂ_[l]).mapMatrix ((ρ g : Matrix n n ℚ_[l]) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]; rfl
  have hrow : ∀ g ∈ H, ∀ i j, ‖(rC g - 1) i j‖ ≤ t := by
    intro g hg i j; rw [hrent, norm_algebraMap']; exact hρ g hg i j
  have hY : ∀ g ∈ H, ∀ i j, ‖(Mi.map (Formalism.Per.σC (g : GQ l)) - Mi) i j‖ ≤ a * t := by
    intro g hg i j
    have hs := _root_.GlobalTheory.PMon.galois_inv_period_matrix l n K ρ M hM g
    have e : Mi.map (Formalism.Per.σC (g : GQ l)) - Mi = Mi * (rC g - 1) := by
      rw [hMi, hs, mul_sub, mul_one]
    rw [e]
    exact _root_.GlobalTheory.matrix_mul_entry_norm_le_ultrametric ℂ_[l] n Mi (rC g - 1) a t ha0.le ht.le hMia (hrow g hg) i j
  obtain ⟨Z, hZ, hZb⟩ := hAx n K H Mi (a * t) (by positivity) hY
  refine ⟨-((M : Matrix n n ℂ_[l]) * Z) i j, fun g hg => ?_⟩
  have hcore := _root_.GlobalTheory.normalisedPeriod_algebraic_estimate ℂ_[l] n (Formalism.Per.σC (g : GQ l)) (rC g) (M : Matrix n n ℂ_[l]) Mi Z a (c * (a * t)) t
    ha0.le (by positivity) ht.le (GlobalTheory.RingBasics.norm_σC _) (by rw [hMi]; exact M.mul_inv) (hM g) (hZ g hg) hMa hZb (hrow g hg) i j
  rw [hrent] at hcore
  calc _ ≤ t * (a * (c * (a * t))) := hcore
    _ = c * a ^ 2 * t ^ 2 := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTwistedSelmerAuxprimesOfMatrixAndBounds
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys


open Classical in
theorem aeval_gen_sub_one_surjective (O : Type) [CommRing O] (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] :
    Function.Surjective (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) := by
  set φ := (MvPolynomial.aeval (R := O) fun q : ι =>
      MonoidAlgebra.of O (Multiplicative (ι → ZMod n)) (Multiplicative.ofAdd (Pi.single q 1)) - 1) with hφ
  have hg : ∀ g : Multiplicative (ι → ZMod n), MonoidAlgebra.of O _ g ∈ φ.range := by
    intro g
    refine ⟨∏ q, (MvPolynomial.X q + 1) ^ (Multiplicative.toAdd g q).val, ?_⟩
    have h1 : g = ∏ q, (Multiplicative.ofAdd (Pi.single q (1 : ZMod n) : ι → ZMod n)) ^ (Multiplicative.toAdd g q).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      funext j
      simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_one, ZMod.natCast_zmod_val]
    conv_rhs => rw [h1]
    simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add (f := _), map_one,
      MvPolynomial.aeval_X, sub_add_cancel]
  intro x
  change x ∈ φ.range
  induction x using MonoidAlgebra.induction_on with
  | of g => exact hg g
  | add f g hf hg => exact add_mem hf hg
  | smul r f hf => exact Subalgebra.smul_mem _ hf r

theorem toLam_surjective {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  exact aeval_gen_sub_one_surjective (X.O0 i) (X.l i ^ M) ι

theorem SlopeTestRemainingChoices.empty {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    {i : X.Tw} {M : ℕ} {A : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) : SlopeTestRemainingChoices X i M ∅ P d := by
  refine ⟨fun q v hv => ?_, h.2⟩
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h.1 q v hv
  exact ⟨h1, h2, h3, h4, Finset.notMem_empty _, h6⟩

theorem galois_twisted_selmer_auxprimes_of_matrix_and_bounds : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X),
    ThmS bkP → SelmerLengthsByDeterminant bkP → ResidualBoundOddPrimes bkP → ThmC bkP → GaloisSideTwistedSelmerAuxiliaryPrimes bkP := by
  intro D N X bkP hS hS4 h103 hC i T hT
  have hO : OrdBound bkP i (IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i)) := by
    rcases Nat.eq_zero_or_pos (nu X i) with h | h
    · rw [h, pow_zero, IsDiscreteValuationRing.addVal_one]
      exact h103 i h
    · exact hC i h
  obtain ⟨R, Dd, M₀, hM₀⟩ := hO T hT
  refine ⟨R, Dd, max M₀ 1, le_max_right _ _, fun M hM H S d hF z hz H' ho hn A => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨P, hA, hSt, hP⟩ := hM₀ M (le_trans (le_max_left _ _) hM) H S d hF z hz H' ho hn A
  refine ⟨P, hA, hSt, fun s hs Q hQ => ?_⟩
  obtain ⟨a, Φ, hΦ, -⟩ := hS i s (hT s hs) M _ P _ Q hM1 hA.empty hQ
  obtain ⟨F, hFΦ⟩ := toLam_surjective X i M (Fin R ⊕ Fin R) Φ.det
  exact ⟨F, hS4 i s M _ P _ Q hM1 hA.empty hQ a Φ hΦ F hFΦ, hP s hs Q hQ a Φ hΦ F hFΦ⟩

end GlobalTheory.TwSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientsExplicitSums
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem adicSpan_smul_top_mem_iff {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (x : O) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule O O) ↔ ∃ b : O, x = ϖ ^ n * b := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩

theorem adicComplete_explicit_sums {O : Type} [CommRing O] (ϖ : O)
    [h : IsAdicComplete (Ideal.span {ϖ}) O] :
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (M := O)
      (fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j) (by
        intro m n hmn
        rw [SModEq.sub_mem, adicSpan_smul_top_mem_iff]
        refine ⟨-∑ j ∈ Finset.Ico m n, ϖ ^ (j - m) * x j, ?_⟩
        rw [← Finset.sum_range_add_sum_Ico _ hmn, mul_neg, Finset.mul_sum]
        have : ∑ j ∈ Finset.Ico m n, ϖ ^ m * (ϖ ^ (j - m) * x j)
            = ∑ j ∈ Finset.Ico m n, ϖ ^ j * x j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
        rw [this]; ring)
    refine ⟨L, fun n => ?_⟩
    have h1 := (SModEq.sub_mem.mp (hL n))
    rw [adicSpan_smul_top_mem_iff] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨-b, by rw [mul_neg, ← hb]; ring⟩
  · refine IsHausdorff.haus' (I := Ideal.span {ϖ}) a fun n => ?_
    rw [SModEq.zero, adicSpan_smul_top_mem_iff]
    exact ha n

theorem goodO_coeff_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O,
      a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  intro l _ LL _ _ _ O _ _ hG
  have hc := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.2.2
  exact adicComplete_explicit_sums (h := hc) ((l : ℕ) : O)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  first | exact @GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | exact GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | (intros; apply GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfPadicCoeffStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_padicCoeff' : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  first | exact @GlobalTheory.isAdicComplete_of_padicCoeff | exact GlobalTheory.isAdicComplete_of_padicCoeff | (intros; apply GlobalTheory.isAdicComplete_of_padicCoeff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lTensor_semistable_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  first | exact @GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | exact GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | (intros; apply GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant <;> assumption)
end

