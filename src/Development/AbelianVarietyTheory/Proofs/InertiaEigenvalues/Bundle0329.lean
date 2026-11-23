module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.TateFilQuot

open GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

theorem step_invariant
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • d i) - ∑ i ∈ s, b i • d i ∈ FM (c + 1)) →
      ∃ w ∈ FM c, (∀ g, ρ g w = w) ∧ ∑ i ∈ s, b i • d i - w ∈ FM (c + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    obtain ⟨w, hw, hwg, hw'⟩ := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) (s.erase i) rfl
      (fun j => b j - b i * κ j) (fun j hj => by
        refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
        by_cases hk : k i = k j
        · have := hmul _ _ _ _ (hb i hi) (hκ j).1
          rwa [add_zero, hk] at this
        · rw [(hκ j).2.2 hk, mul_zero]
          exact (F _).zero_mem) (fun g => by
        have h2 := (FM _).sub_mem (hsum g) ((FM _).sub_mem (hMG g _ _ h1) h1)
        convert h2 using 1
        rw [map_add (ρ g) (b i • _)]
        abel)
    refine ⟨w, hw, hwg, ?_⟩
    rw [add_sub_assoc]
    exact (FM _).add_mem h1 hw'
  · have hg : ∀ g, ∀ i ∈ s, σ g (b i) - b i ∈ F (c - k i + 1) := fun g =>
      graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c
        (fun i => σ g (b i) - b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (hb i hi)) (hb i hi)) (by
          convert hsum g using 1
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib])
    have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (c - k i ≠ 0 → κ = 0) ∧
        (i ∈ s → b i - κ ∈ F (c - k i + 1)) := fun i => by
      by_cases hi : i ∈ s
      · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (hb i hi) (fun g => hg g i hi)
        exact ⟨κ, h1, h2, h3, fun _ => h4⟩
      · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
    choose κ h1 h2 h3 h4 using hκ
    refine ⟨∑ i ∈ s, κ i • d i, (FM _).sum_mem fun i _ => ?_, fun g => ?_, ?_⟩
    · by_cases hk : c - k i = 0
      · have := hsmul _ _ _ _ (h1 i) (hdk i)
        rwa [show 0 + k i = c by omega] at this
      · rw [h3 i hk, zero_smul]
        exact (FM _).zero_mem
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, hρ, hd, h2]
    · rw [← Finset.sum_sub_distrib]
      refine (FM _).sum_mem fun i hi => ?_
      have := hsmul _ _ _ _ (h4 i hi) (hdk i)
      rwa [show c - k i + 1 + k i = c + 1 by ring, sub_smul] at this

theorem invariant_mod
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (hspan : ∀ y : M, ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → M),
      (∀ i g, ρ g (d i) = d i) ∧ y = ∑ i, b i • d i)
    (a b : ℤ) (z : M) (hz : z ∈ FM a) (hg : ∀ g, ρ g z - z ∈ FM b) :
    ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM b := by
  have key : ∀ c, a ≤ c → c ≤ max a b → ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM c := by
    intro c hc
    induction c, hc using Int.leInduction with
    | base => exact fun _ => ⟨0, (FM _).zero_mem, fun g => map_zero _, by rwa [sub_zero]⟩
    | succ c hc ih =>
      intro hcb
      have hcb' : c + 1 ≤ b := by omega
      obtain ⟨w, hw, hwg, hzw⟩ := ih (by omega)
      obtain ⟨m, b₀, d₀, hd₀, e₀⟩ := hspan (z - w)
      obtain ⟨m', k', b', d', h, e⟩ := filtered σ ρ F FM hρ hmul hsmul hFG hMG hinv hT hFa hMa hFe hMe
        c (z - w) hzw m b₀ d₀ hd₀ e₀
      obtain ⟨w', hw', hwg', hzw'⟩ := step_invariant σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d'
        (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2)
        (fun g => by
          rw [← e, map_sub, hwg, sub_sub_sub_cancel_right]
          exact hMa hcb' (hg g))
      refine ⟨w + w', (FM _).add_mem hw (hMa hc hw'), fun g => by rw [map_add (f := _), hwg, hwg'], ?_⟩
      rwa [← e, sub_sub] at hzw'
  obtain ⟨w, hw, hwg, hzw⟩ := key (max a b) (le_max_left _ _) le_rfl
  exact ⟨w, hw, hwg, hMa (le_max_right _ _) hzw⟩

end Abstract

theorem tied_invariant_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (TT : LocTied l P AI) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hdR : IsDR (P.PD K) ρ) (a b : ℤ) (z : V ⊗[ℚ_[l]] P.R.BdR)
    (hz : z ∈ FilV (P.PD K) (LL := LL) (V := V) a)
    (hg : ∀ g, actVdR (P.PD K) ρ g z - z ∈ FilV (P.PD K) (LL := LL) (V := V) b) :
    ∃ w ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) a,
      z - w ∈ FilV (P.PD K) (LL := LL) (V := V) b := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  have hspan := GlobalTheory.Per.DeRhamSpan.span_of_isField (P.PD K) ρ
    (GlobalTheory.Per.TiedField.tied_field l P AI TT).1 hdR
  let φ : P.R.BdR →+* Module.End LL (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := LL) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨w, hw, hwg, hzw⟩ := invariant_mod (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := LL) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    (fun y => by
      obtain ⟨m, b, d, hd, e⟩ := hspan y
      exact ⟨m, b, d, fun i g => (hD _).1 (hd i) g, e⟩)
    a b z hz hg
  exact ⟨w, ⟨(hD _).2 hwg, hw⟩, hzw⟩

theorem tate_fil_quot : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm5 D := by
  intro D l _ K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact tied_invariant_mod l (D.loc l) (D.locA l) (D.locT l) K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltInvariantApproxByEpsilonRootsClosure
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlatInvariants

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem root_pow (j : ℕ) : AI.εroot j ^ l ^ j = AI.ε := by
  induction j with
  | zero => simp [LocAinf.εroot]
  | succ j ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem root_sub_dvd (j : ℕ) : AI.εroot j - 1 ∣ AI.ε - 1 := by
  rw [← root_pow AI j]
  exact sub_one_dvd_pow_sub_one _ _

theorem exists_pow_mul_integral (s : ℕ) (y : Cb l) : ∃ k, ∀ k' ≥ k, ∃ z : OCb l,
    algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ k') * y = algebraMap (OCb l) (Cb l) z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨k, hk⟩ : ∃ k, b ∣ (AI.εroot s - 1) ^ k := by
    by_contra h
    exact hb0 ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 b fun m =>
      (ValuationRing.dvd_total _ _).resolve_right fun h' => h ⟨m, h'⟩)
  refine ⟨k, fun k' hk' => ?_⟩
  obtain ⟨d, hd⟩ := hk.trans (pow_dvd_pow _ hk')
  have : algebraMap (OCb l) (Cb l) b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm))
  refine ⟨d * a, ?_⟩
  rw [hd, map_mul, map_mul]
  field_simp

theorem flat_invariant_approx : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (w : Cb l), (∀ g ∈ Hinf K, autCb l (AI.actT g) w = w) → ∀ m : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ u ∈ Subring.closure (Set.range AI.εroot ∪ {xb | ∃ c : Om l, c ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ c ^ m = 1 ∧ IsTiltOf c m xb}), ∃ v : OCb l, algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ N) * w = algebraMap (OCb l) (Cb l) (u + (AI.εroot s - 1) ^ (N + m) * v) := by
  intro l _ P AI K s w hw m
  obtain ⟨k, hk⟩ := exists_pow_mul_integral AI s w
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨z, hz⟩ := hk N hN
  have hfix : ∀ g ∈ Hinf K, AI.actT g z = z := fun g hg => by
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← autCb_alg, ← hz, map_mul, hw g hg, autCb_alg, map_pow (AI.actT g), map_sub (AI.actT g), map_one (AI.actT g),
      (GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial l P AI K).1 g hg s]
  obtain ⟨u, hu, hd⟩ := GlobalTheory.TiltInvariants.invariant_approx l P AI K z hfix (N + m)
  obtain ⟨v, hv⟩ := (pow_dvd_pow_of_dvd (root_sub_dvd AI s) (N + m)).trans hd
  exact ⟨u, hu, v, by rw [hz, ← hv, add_sub_cancel]⟩

end GlobalTheory.FlatInvariants
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOrthOfUntiltOrth
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem tilt_orth_of_untilt_orth : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  intro l _ h m hrat horth c j hj
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

  have hne : (Finset.univ : Finset (Fin h)).Nonempty := ⟨j, Finset.mem_univ _⟩
  set M : ℝ := Finset.univ.sup' hne (fun i => ‖sh (m i)‖) with hM
  have hMle : ∀ i, ‖sh (m i)‖ ≤ M := fun i => Finset.le_sup' (fun i => ‖sh (m i)‖) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMle j)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖sh (m i)‖)
  have hsmall : ‖(l : ℂ_[l])‖ * M < ‖sh (m j)‖ := by
    rw [GlobalTheory.PSer.Laws.norm_l, hM, hi0, inv_mul_lt_iff₀ hl]
    exact hrat i0 j

  set n : Fin h → ℕ := fun i => (c i % (l : ℤ)).toNat with hn
  have hnc : ∀ i, ((n i : ℕ) : ℤ) = c i % (l : ℤ) := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  have hcast : ∀ i, (c i : Fl l) = (n i : Fl l) := by
    intro i
    have : ((n i : ℤ) : Fl l) = (n i : Fl l) := Int.cast_natCast _
    rw [← this, CharP.intCast_eq_intCast (Fl l) l, hnc]
    exact (Int.mod_modEq _ _).symm
  have hnj : ‖((n j : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
    intro hd
    apply hj
    have h1 : (l : ℤ) ∣ c j % (l : ℤ) := by rw [← hnc]; exact_mod_cast hd
    have h2 := (Int.dvd_iff_emod_eq_zero ..).1 h1
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)] at h2
    exact Int.dvd_of_emod_eq_zero h2

  have hsum : (∑ i, (c i : Fl l) * m i) =
      ∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), m p.1 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast]
  have hsum2 : (∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), sh (m p.1)) =
      ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, map_natCast]
  obtain ⟨hd, -⟩ := _root_.GlobalTheory.untilt_sum_sub_le l ((_ : Fin h) × ℕ) ((Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)))
    M (fun p => m p.1) hM0 (fun p _ => hMle p.1)
  rw [← hsum, hsum2] at hd
  have ho := horth (fun i => ((n i : ℕ) : ℚ_[l])) j
  simp only [hnj, one_mul] at ho

  by_contra hlt
  push_neg at hlt
  set b := sh (∑ i, (c i : Fl l) * m i)
  set a := ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i)
  have : ‖a‖ ≤ max ‖b‖ ‖b - a‖ := by
    have := IsUltrametricDist.norm_add_le_max b (-(b - a))
    rwa [norm_neg, show b + -(b - a) = a by ring] at this
  have hba : ‖b - a‖ < ‖sh (m j)‖ := hd.trans_lt hsmall
  exact absurd (ho.trans this) (not_le.2 (max_lt hlt hba))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApprox
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untiltFrobeniusLaurentSeries_zero (l : ℕ) [Fact l.Prime] (h j : ℕ) : lam h j (0 : Fl l) = 0 := by
  unfold lam
  have h0 : ∀ n : ℤ, (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) (0 : Fl l)) = 0 := by
    intro n
    rw [(_root_.GlobalTheory.PSer.PwLaws.pw_laws l).2.2.1, (_root_.GlobalTheory.PSer.Laws.sh_laws l).2.1, mul_zero]
  simp only [h0, tsum_zero]

theorem norm_add_three_le {l : ℕ} [Fact l.Prime] (a b c : ℂ_[l]) (C : ℝ)
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) : ‖a + b + c‖ ≤ C := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hc)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem untiltFrobeniusLaurentSeries_nsmul_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ‖sh x‖ ≤ r) (m : ℕ) :
    ‖sh (m • x)‖ ≤ r ∧ ‖lam h j (m • x) - (m : ℂ_[l]) * lam h j x‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (_root_.GlobalTheory.gam_laws l h j r hh hr0 hr1).2.2.1
  induction m with
  | zero =>
    simp only [zero_smul, Nat.cast_zero, zero_mul, sub_zero, untiltFrobeniusLaurentSeries_zero, norm_zero, (_root_.GlobalTheory.PSer.Laws.sh_laws l).2.1]
    exact ⟨hr0, hC⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [succ_nsmul]
    obtain ⟨hadd, hsh⟩ := _root_.GlobalTheory.PSer.sh_add_le l r (m • x) x ih1 hx
    refine ⟨hsh, ?_⟩
    have hl := _root_.GlobalTheory.PSer.lam_add_sub_le l h j r (m • x) x hh hr1 ih1 hx
    have heq : lam h j (m • x + x) - ((m + 1 : ℕ) : ℂ_[l]) * lam h j x =
        (lam h j (m • x + x) - lam h j (m • x) - lam h j x) + (lam h j (m • x) - (m : ℂ_[l]) * lam h j x) + 0 := by
      push_cast; ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl ih2 (by simpa using hC)

theorem untiltFrobeniusLaurentSeries_finset_sum_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) {ι : Type*} [DecidableEq ι]
    (x : ι → Fl l) (n : ι → ℕ)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ∀ a, ‖sh (x a)‖ ≤ r) (s : Finset ι) :
    ‖sh (∑ a ∈ s, n a • x a)‖ ≤ r ∧
      ‖lam h j (∑ a ∈ s, n a • x a) - ∑ a ∈ s, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (_root_.GlobalTheory.gam_laws l h j r hh hr0 hr1).2.2.1
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, untiltFrobeniusLaurentSeries_zero, sub_zero, norm_zero, (_root_.GlobalTheory.PSer.Laws.sh_laws l).2.1]
    exact ⟨hr0, hC⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨hu1, hu2⟩ := untiltFrobeniusLaurentSeries_nsmul_approx l h j r (x a) hh hr0 hr1 (hx a) (n a)
    obtain ⟨hadd, hsh⟩ := _root_.GlobalTheory.PSer.sh_add_le l r (n a • x a) (∑ b ∈ s, n b • x b) hu1 ih1
    refine ⟨hsh, ?_⟩
    have hl := _root_.GlobalTheory.PSer.lam_add_sub_le l h j r (n a • x a) (∑ b ∈ s, n b • x b) hh hr1 hu1 ih1
    have heq : lam h j (n a • x a + ∑ b ∈ s, n b • x b) -
        ((n a : ℂ_[l]) * lam h j (x a) + ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) =
        (lam h j (n a • x a + ∑ b ∈ s, n b • x b) - lam h j (n a • x a) - lam h j (∑ b ∈ s, n b • x b)) +
        (lam h j (n a • x a) - (n a : ℂ_[l]) * lam h j (x a)) +
        (lam h j (∑ b ∈ s, n b • x b) - ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) := by ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl hu2 ih2

theorem lamsum : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j d r x n hh hr0 hr1 hx
  exact untiltFrobeniusLaurentSeries_finset_sum_approx l h j r x n hh hr0 hr1 hx Finset.univ

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobeniusStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusion_X_Q_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  first | exact @GlobalTheory.NL.IoXQ.main | exact GlobalTheory.NL.IoXQ.main | (intros; apply GlobalTheory.NL.IoXQ.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecompositionStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLetterRing_frobenius_decomposition : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  first | exact @GlobalTheory.NL.PhiDec.phi_dec | exact GlobalTheory.NL.PhiDec.phi_dec | (intros; apply GlobalTheory.NL.PhiDec.phi_dec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeaklySmallStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakly_small_of_not_isUnit_of_dvd_pow : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U := by
  first | exact @GlobalTheory.WeakClosed.weakly_small | exact GlobalTheory.WeakClosed.weakly_small | (intros; apply GlobalTheory.WeakClosed.weakly_small <;> assumption)
end

