module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcris
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter GlobalTheory.HWL.Disc

section Letters

variable {O N : Type} [CommRing O] [CommRing N] {n : ℕ} [NeZero n] (f : LetA O n →+* N)

theorem sum_letE : ∑ i, f (letE i) = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_one f]
  exact congrArg f (Finset.univ_sum_single (1 : LetA O n))

theorem sum_letE_mul (x y : ZMod n → N) :
    ∑ i, f (letE i) * (x i * y i) = (∑ i, f (letE i) * x i) * ∑ i, f (letE i) * y i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : (letE i : LetA O n) * letE i = letE i := by
      ext1 j
      by_cases h : j = i <;> simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this]
  · intro j _ hj
    have : (letE i : LetA O n) * letE j = 0 := by
      ext1 k
      by_cases h : k = i
      · simp [letE, h, hj.symm]
      · simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this, map_zero, zero_mul]
  · simp

theorem sum_letE_const (a : LetA O n) : ∑ i, f (letE i) * f (fun _ => a i) = f a := by
  simp only [← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  ext1 j
  simp [letE, Pi.single_apply]

omit [NeZero n] in
theorem letφ_letE (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letφ φ₀ (letE (i - 1)) = letE i := by
  ext1 j
  change φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases h : j = i <;> simp [letE, h]

omit [NeZero n] in
theorem letγ_letE (g : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letγ g (letE i) = letE i := by
  ext1 j
  change g ((letE i : LetA O n) j) = _
  by_cases h : j = i <;> simp [letE, h]

end Letters

variable {l : ℕ} [Fact l.Prime]

theorem frob_root {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    WittVector.frobenius (WittVector.teichmuller l (AI.εroot (s + 1)) - 1) =
      WittVector.teichmuller l (AI.εroot s) - 1 := by
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
    LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

theorem sc_map {LL : FinExt l} (a : (↥(OL LL))⟦X⟧) : SC (map (algebraMap ↥(OL LL) ↥LL.1) a) :=
  sc_of_le 0 fun k => by simpa using norm_integer_le_one (coeff k a)

theorem sc_log (LL : FinExt l) : SC (logS LL) := sc_lg (norm_natCast_inv_le LL)

theorem frob_injective {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (LL : FinExt l) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) P.φB.toLinearMap
    (GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.1

theorem crisFrobenius_periodT_eq_prime_smul (P : LocPrime l) (K : FinExt l) : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD K).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h


set_option maxHeartbeats 1000000 in
theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  intro l _ P AI T K s LL hG Γ R I hW β hβ
  obtain ⟨N, _, _, c, b, κ, φ, γ, t, ⟨hκb, hφb, hκφ, hγb, hκγ, hκt⟩, hc, hb, hbo, hκc, ⟨hφ, hφc⟩, hγ, hs, hlog, hcl⟩ :=
    _root_.GlobalTheory.HWL.BanachModel.exists_banach_model l P AI T LL β hβ
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos.ne'⟩
  let μ : ℕ → N := fun s => b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))
  have hμ : ∀ s, Small (μ s) := hs
  have hc' : Bdd c := hc
  set_option synthInstance.maxHeartbeats 200000 in
  let f : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) →+* N := b.comp I.io.toRingHom
  have hf : ∀ a, f a = b (I.io a) := fun _ => rfl
  have hfπ : f letπ = μ s := congrArg b I.io_π
  have hint : ∀ a, ev c (μ s) (map (algebraMap ↥(OL LL) ↥LL.1) a) = f (fun _ => a) := fun a =>
    ev_map (algebraMap ↥(OL LL) ↥LL.1) (hμ s) hc' (f.comp (Pi.constRingHom _ _))
      (fun o => (congrArg b (I.io.commutes o)).trans (by exact hbo o)) hfπ (fun _ => hb _) a (sc_map a)
  have hfφ : ∀ a, f (letφ R.φ₀ a) = φ (f a) := (_root_.GlobalTheory.HWL.IoComm.main l P AI K s LL Γ R I N b (φ.comp b)).1 hφb
  have hfγ : ∀ (g : ↥(GK K)) a, f (letγ (R.γ₀ (Γ.resΓ g)) a) = γ g (f a) := fun g =>
    (_root_.GlobalTheory.HWL.IoComm.main l P AI K s LL Γ R I N b ((γ g).comp b)).2 g (hγb g)
  have hsub : ∀ (ψ : N →+* N) (y : (↥(OL LL))⟦X⟧), Continuous ψ → (∀ x, ψ (c x) = c x) → constantCoeff y = 0 →
      f (fun _ => y) = ψ (μ s) → ∀ a, Conv a →
      ev c (μ s) (subst (map (algebraMap ↥(OL LL) ↥LL.1) y) a) = ψ (ev c (μ s) a) := by
    intro ψ y h1 h2 h3 h4 a ha
    have ha' := (conv_iff_sc a).1 ha
    have h5 := hasSum_subst hc' (hμ s) (y := map (algebraMap ↥(OL LL) ↥LL.1) y)
      (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h3, map_zero])
      (fun k => by simpa using norm_integer_le_one (coeff k y)) ha'
    rw [hint, h4] at h5
    exact h5.unique (hasSum_map hc' (hμ s) ha' ψ h1 h2)
  refine ⟨fun a => κ (∑ i, f (letE i) * ev c (μ s) (a i)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a' ha ha'
    rw [← map_add (f := _), ← Finset.sum_add_distrib]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.add_apply, ev_add hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i)), mul_add]
  · intro a a' ha ha'
    rw [← map_mul, ← sum_letE_mul]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.mul_apply, ev_mul hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i))]
  · intro x a ha
    have e : algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] P.R.B) x = κ (c x) := (hκc x).symm
    rw [Algebra.smul_def x (κ _), e, ← map_mul, Finset.mul_sum]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.smul_apply, ev_C_mul hc' (hμ s) x ((conv_iff_sc _).1 (ha i)), mul_left_comm]
  · intro a
    rw [← hκb, ← hf, ← sum_letE_const f a]
    exact congrArg κ (Finset.sum_congr rfl fun i _ => congrArg _ (hint (a i)))
  · intro a ha
    have hy : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
    have hy' : ((1 + X) ^ l - 1 : (↥LL.1)⟦X⟧) = map (algebraMap ↥(OL LL) ↥LL.1) (R.φ₀ X) := by
      simp [hy]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hκφ, map_sum φ, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod _))
      (fun i => φ (f (letE i) * ev c (μ s) (a i)))]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Equiv.subRight_apply, map_mul, ← hfφ, letφ_letE, hy',
      hsub φ _ hφ hφc (by simp [hy]) (hfπ ▸ hfφ letπ) _ (ha _)]
  · intro g a ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hκγ, map_sum (γ g)]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, ← hfγ, letγ_letE,
      hsub (γ g) _ (hγ g).1 (hγ g).2 (R.γ₀_X _).1 (hfπ ▸ hfγ g letπ) _ (ha _)]
  · rw [← Finset.sum_mul, sum_letE, one_mul]
    have key : ∀ k : ℕ, κ (ev c (μ k) (logS LL)) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ k)⁻¹) • P.tB) := by
      intro k
      induction k with
      | zero =>
        rw [tendsto_nhds_unique (hasSum_ev hc' (hμ 0) (sc_log LL)).tendsto_sum_nat hlog, hκt]
        simp
      | succ k ih =>
        have h1 := hasSum_map hc' (hμ (k + 1)) (sc_log LL) φ hφ hφc
        have h2 : φ (μ (k + 1)) = μ k := (hφb _ _).trans (by rw [frob_root])
        rw [h2] at h1
        apply frob_injective T LL
        have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        rw [← hκφ, h1.unique (hasSum_ev hc' (hμ k) (sc_log LL)), ih, Algebra.TensorProduct.map_tmul, map_smul,
          crisFrobenius_periodT_eq_prime_smul P K, smul_smul, map_one, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hl, mul_one]
    exact key s
  · intro i ζ ι hι hζ a ha e he m
    let π : N →+* P.R.BdR := (Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ
    have hπ : ∀ x, π x = Algebra.TensorProduct.productMap ι P.ιB (κ x) := fun _ => rfl
    have hπc : ∀ x, π (c x) = ι x := fun x => by rw [hπ, hκc]; simp
    have hπE : ∀ j, π (f (letE j)) = if i = j then 1 else 0 := fun j => by
      have h := GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants l P AI T K s LL hG Γ R I hW β hβ i ι hι (Pi.single j 1)
      have e1 : (fun k => C ((Pi.single j 1 : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) k)) =
          (letE j : LetA ↥(OL LL) _) := by
        ext1 k
        by_cases h : k = j <;> simp [letE, h]
      rw [e1] at h
      rw [hπ, hf, hκb, h]
      by_cases h : i = j <;> simp [h]
    have hπμ : π (μ s) = P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) := by
      rw [hπ, hκb, hβ]
      simp
    let τ : N := c (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ s)⁻¹) * t
    have hπτ : π τ = (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB := by
      rw [map_mul, hπc, AlgHom.commutes, hπ, hκt, Algebra.smul_def]
      simp
    have hev : ∀ x : ℕ → ↥LL.1, π (∑ k ∈ Finset.range m, c (x k) * τ ^ k) =
        ∑ k ∈ Finset.range m, ι (x k) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k := fun x => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul π, map_pow π, hπc, hπτ]
    have hlim : Tendsto (fun M : ℕ => Polynomial.eval₂ c (μ s) (trunc M (a i)) - ∑ k ∈ Finset.range m,
        c (coeff k (Polynomial.aeval (C ζ * exp ↥LL.1 - 1) (trunc M (a i)))) * τ ^ k) atTop
        (nhds (ev c (μ s) (a i) - ∑ k ∈ Finset.range m, c (coeff k e) * τ ^ k)) := by
      refine (tendsto_ev hc' (hμ s) ((conv_iff_sc _).1 (ha i))).sub (tendsto_finsetSum _ fun k _ => ?_)
      exact ((hc'.continuous.tendsto _).comp (tendsto_subtype_rng.2 (he k))).mul_const _
    have hmem := (hcl ι m).mem_of_tendsto hlim (Eventually.of_forall fun M => by
      have h := _root_.GlobalTheory.ExpImage.PolyTaylor.poly_taylor l P AI T LL s ζ ι hζ (trunc M (a i)) m
      rw [Set.mem_setOf_eq, ← hπ, map_sub, hev, Polynomial.hom_eval₂, hπμ, show π.comp c = (ι : ↥LL.1 →+* P.R.BdR) from RingHom.ext hπc]
      exact h)
    rw [Set.mem_setOf_eq, ← hπ, map_sub, hev] at hmem
    have e2 : π (∑ j, f (letE j) * ev c (μ s) (a j)) = π (ev c (μ s) (a i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_mul π, hπE]
    rw [← hπ, e2]
    exact (Set.ext_iff.1 (P.PD_Fil _ K m) _).1 hmem

end GlobalTheory.HWL.BanachEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiltrationAdaptedBasisOfSubspace
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AdaptedBasis

variable {k M : Type} [Field k] [AddCommGroup M] [Module k M]

theorem exists_adapted_family (F : ℤ → Submodule k M) (hF : Antitone F) :
    ∀ (n : ℕ) (D : Submodule k M) [FiniteDimensional k D], Module.finrank k D = n →
    (∀ x ∈ D, ∃ a, x ∈ F a) → (∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) →
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → M) (h : ι → ℤ), LinearIndependent k v ∧
      Submodule.span k (Set.range v) = D ∧ (∀ j, v j ∈ F (h j) ∧ v j ∉ F (h j + 1)) ∧
      ∀ a, D ⊓ F a ≤ Submodule.span k (v '' {j | a ≤ h j}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ hn hex hsep
  by_cases hD : D = ⊥
  · subst hD
    refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, linearIndependent_empty_type, ?_,
      fun j => j.elim, fun a => by simp⟩
    simp
  have hne : ∃ a, D ≤ F a := by
    let b := Module.finBasis k D
    have hb : ∀ i, ∃ a, (b i : M) ∈ F a := fun i => hex _ (b i).2
    choose c hc using hb
    obtain ⟨m, hm⟩ := Finite.exists_le (fun i => OrderDual.toDual (c i))
    refine ⟨OrderDual.ofDual m, ?_⟩
    intro x hx
    have hx' : (⟨x, hx⟩ : D) ∈ Submodule.span k (Set.range b) := by
      rw [b.span_eq]; trivial
    have : (Submodule.span k (Set.range b)).map D.subtype ≤ F (OrderDual.ofDual m) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hF (hm i) (hc i)
    exact this ⟨_, hx', rfl⟩
  have hbdd : ∃ b, ∀ z, D ≤ F z → z ≤ b := by
    obtain ⟨x, hxD, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have : ¬ ∀ a, x ∈ F a := fun h => hx0 (hsep x hxD h)
    push_neg at this
    obtain ⟨a, ha⟩ := this
    refine ⟨a, fun z hz => ?_⟩
    by_contra hlt
    exact ha (hF (le_of_not_ge hlt) (hz hxD))
  obtain ⟨a₀, ha₀, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  set D' := D ⊓ F (a₀ + 1) with hD'
  have hD'D : D' ≤ D := inf_le_left
  have hlt : D' < D := by
    refine lt_of_le_of_ne hD'D fun heq => ?_
    have : D ≤ F (a₀ + 1) := heq ▸ inf_le_right
    have := hmax _ this
    omega
  haveI : FiniteDimensional k D' := Submodule.finiteDimensional_of_le hD'D
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) D' rfl
      (fun x hx => hex x (hD'D hx)) (fun x hx => hsep x (hD'D hx))
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl D'
  set C := C' ⊓ D with hC
  have hCD : C ≤ D := inf_le_right
  have hdisj : Disjoint D' C := hC'.disjoint.mono_right inf_le_left
  have hsup : D' ⊔ C = D := by
    rw [hC, ← sup_inf_assoc_of_le _ hD'D, hC'.sup_eq_top, top_inf_eq]
  haveI : FiniteDimensional k C := Submodule.finiteDimensional_of_le hCD
  let bC := Module.finBasis k C
  let c : Fin (Module.finrank k C) → M := fun i => (bC i : M)
  have hcli : LinearIndependent k c := bC.linearIndependent.map' C.subtype C.ker_subtype
  have hcspan : Submodule.span k (Set.range c) = C := by
    have : Set.range c = C.subtype '' Set.range bC := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, bC.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hdeg' : ∀ j, a₀ + 1 ≤ h j := by
    intro j
    by_contra hj
    push_neg at hj
    have hvj : v j ∈ D' := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact (hdeg j).2 (hF (show h j + 1 ≤ a₀ + 1 by omega) (Submodule.mem_inf.mp hvj).2)
  refine ⟨ι ⊕ Fin (Module.finrank k C), inferInstance, Sum.elim v c,
    Sum.elim h (fun _ => a₀), ?_, ?_, ?_, ?_⟩
  · exact hli.sum_type hcli (by rw [hspan, hcspan]; exact hdisj)
  · rw [Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
  · rintro (j | i)
    · exact hdeg j
    · refine ⟨ha₀ (hCD (bC i).2), fun hmem => ?_⟩
      have h1 : c i ∈ D' := ⟨hCD (bC i).2, hmem⟩
      have h2 : c i = 0 := (Submodule.disjoint_def.mp hdisj) _ h1 (bC i).2
      exact hcli.ne_zero i h2
  · intro a x hx
    by_cases ha : a ≤ a₀
    · have hall : {j : ι ⊕ Fin (Module.finrank k C) | a ≤ Sum.elim h (fun _ => a₀) j} = Set.univ := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rcases j with j | i
        · have := hdeg' j; simp only [Sum.elim_inl]; omega
        · simpa using ha
      rw [hall, Set.image_univ, Set.Sum.elim_range, Submodule.span_union, hspan, hcspan, hsup]
      exact hx.1
    · push_neg at ha
      have hx' : x ∈ D' ⊓ F a := ⟨⟨hx.1, hF (by omega) hx.2⟩, hx.2⟩
      refine Submodule.span_mono ?_ (hfil a hx')
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨Sum.inl j, hj, rfl⟩

end GlobalTheory.AdaptedBasis

namespace GlobalTheory.AdaptedBasis

theorem exists_adapted_basis {k M : Type} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hex : ∀ x ∈ D, ∃ a, x ∈ F a) (hsep : ∀ x ∈ D, (∀ a, x ∈ F a) → x = 0) :
    ∃ (b : Module.Basis (Fin (Module.finrank k D)) k D) (h : Fin (Module.finrank k D) → ℤ),
      (∀ j, (b j : M) ∈ F (h j) ∧ (b j : M) ∉ F (h j + 1)) ∧
      ∀ (a : ℤ) (x : D), (x : M) ∈ F a → ∀ j, b.repr x j ≠ 0 → a ≤ h j := by
  classical
  obtain ⟨ι, _, v, h, hli, hspan, hdeg, hfil⟩ :=
    exists_adapted_family F hF _ D rfl hex hsep
  let b0 : Module.Basis ι k D := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb0 : ∀ i, (b0 i : M) = v i := fun i => by
    simp [b0, Module.Basis.span_apply]
  let e : ι ≃ Fin (Module.finrank k D) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b0).symm
  refine ⟨b0.reindex e, fun j => h (e.symm j), fun j => ?_, fun a x hx j hj => ?_⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact hdeg _
  · rw [Module.Basis.repr_reindex_apply] at hj
    have hxs : (x : M) ∈ Submodule.span k (v '' {i | a ≤ h i}) := hfil a ⟨x.2, hx⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination k).mp hxs
    have hrepr : b0.repr x = l := by
      have : x = Finsupp.linearCombination k b0 l := by
        apply Subtype.ext
        have h1 := Finsupp.apply_linearCombination k D.subtype b0 l
        simp only [Submodule.subtype_apply] at h1
        have hv : (⇑D.subtype ∘ ⇑b0) = v := funext hb0
        rw [h1, hv, hlx]
      rw [this, b0.repr_linearCombination]
    rw [hrepr] at hj
    exact hl (Finsupp.mem_support_iff.mpr hj)

end GlobalTheory.AdaptedBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixFCrystalBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobMat

theorem isFrac_add {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) (c : ℕ) :
    IsFrac d y (d ^ c • m) (k + c) := by
  unfold IsFrac at *
  rw [h, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul, pow_add, mul_comm]

theorem isFrac_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k a : ℕ} (h : IsFrac d y m k) (hka : k ≤ a) :
    IsFrac d y (d ^ (a - k) • m) a := by
  have := isFrac_add h (a - k)
  rwa [Nat.add_sub_cancel' hka] at this

theorem isFrac_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) :
    d ^ k • y = LocalizedModule.mk m 1 := by
  unfold IsFrac at h
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, OneMemClass.coe_one]

theorem exists_common_den {R : Type} [CommRing R] (x : R) {ι : Type} [Finite ι]
    (f : ι → Localization.Away x) : ∃ (n : ℕ) (g : ι → R), ∀ i, algebraMap R _ (g i) = x ^ n • f i := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers x) f
  choose g hg using hn
  exact ⟨n, g, hg⟩

theorem span_eq_top_of_semiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {ι : Type} [Fintype ι]
    (e : Module.Basis ι A M) : Submodule.span B (Set.range fun i => u (e i)) = ⊤ := by
  let S := Submodule.span B (Set.range fun i => u (e i))
  have hu : ∀ x, u x ∈ S := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [u.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨w, -, huniq⟩ := h (N ⧸ S) 0
  have h1 : S.mkQ = w := huniq _ fun x => by
    simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]; exact hu x
  have h2 : (0 : N →ₗ[B] N ⧸ S) = w := huniq _ fun x => by simp
  rw [eq_top_iff]
  intro y _
  have := LinearMap.congr_fun (h1.trans h2.symm) y
  simpa using this

end GlobalTheory.BSP.FrobMat

namespace GlobalTheory.BSP.FrobMat

theorem frob_matrix_general {R Mo : Type} [CommRing R] [IsDomain R] [AddCommGroup Mo] [Module R Mo]
    (φ : R →+* R) (x : R) (hx : x ≠ 0)
    (u : Mo →ₛₗ[(algebraMap R (Localization.Away x)).comp φ] LocalizedModule (Submonoid.powers x) Mo)
    (hu : SemiBC u) {d : ℕ} (e : Module.Basis (Fin d) R Mo) :
    ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) R), A * A' = x ^ b • (1 : Matrix (Fin d) (Fin d) R) ∧
      ∀ j, IsFrac x (u (e j)) (∑ i, A i j • e i) a := by
  haveI : Module.Free R Mo := Module.Free.of_basis e
  have h1 : ∀ j, ∃ m k, IsFrac x (u (e j)) m k := fun j => exists_isFrac _ _
  choose m k hmk using h1
  let a := ∑ j, k j
  have hk : ∀ j, k j ≤ a := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let m' : Fin d → Mo := fun j => x ^ (a - k j) • m j
  have hm' : ∀ j, IsFrac x (u (e j)) (m' j) a := fun j => isFrac_le (hmk j) (hk j)
  let A : Matrix (Fin d) (Fin d) R := fun i j => e.repr (m' j) i
  have hA : ∀ j, ∑ i, A i j • e i = m' j := fun j => e.sum_repr (m' j)
  have hsp := span_eq_top_of_semiBC hu e
  have h2 : ∀ k' : Fin d, ∃ c : Fin d → Localization.Away x,
      ∑ j, c j • u (e j) = LocalizedModule.mk (e k') 1 := fun k' =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.eq_top_iff'.1 hsp _)
  choose c hc using h2
  obtain ⟨n, A', hA'⟩ := exists_common_den x (fun p : Fin d × Fin d => c p.2 p.1)
  let A'' : Matrix (Fin d) (Fin d) R := fun j k' => A' (j, k')
  refine ⟨a, a + n, A, A'', ?_, fun j => (hA j).symm ▸ hm' j⟩
  have key : ∀ k', LocalizedModule.mk (x ^ (a + n) • e k') (1 : Submonoid.powers x) =
      LocalizedModule.mk (∑ j, A' (j, k') • m' j) 1 := by
    intro k'
    have hr : LocalizedModule.mk (∑ j, A' (j, k') • m' j) (1 : Submonoid.powers x) =
        ∑ j, A' (j, k') • LocalizedModule.mk (m' j) (1 : Submonoid.powers x) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← LocalizedModule.mkLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LocalizedModule.mkLinearMap_apply]
    rw [hr, ← LocalizedModule.smul'_mk, ← hc k', pow_add, mul_smul, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc (x ^ n) (c k' j), ← hA' (j, k'), algebraMap_smul, smul_comm,
      isFrac_smul (hm' j)]
  have key2 : ∀ k', x ^ (a + n) • e k' = ∑ j, A' (j, k') • m' j := by
    intro k'
    obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 (key k')
    simp only [Submonoid.smul_def, one_smul] at hr
    exact smul_right_injective _ (pow_ne_zero r hx) hr
  ext i k'
  have h3 := congrArg (fun y => e.repr y i) (key2 k')
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, e.repr_self, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul] at h3
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [eq_comm] at h3
  simp only [eq_comm (a := k') (b := i)] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.FrobMat

theorem GlobalTheory.BSP.frob_matrix_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  intro l _ K bk d M e
  haveI : IsDomain bk.prism.A := inferInstanceAs (IsDomain bk.S)
  exact GlobalTheory.BSP.FrobMat.frob_matrix_general (R := bk.prism.A) bk.prism.D.φ (bk.toP bk.E) bk.E_ne_zero
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩)
    (M.Φ_bc bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩) e
end
end

