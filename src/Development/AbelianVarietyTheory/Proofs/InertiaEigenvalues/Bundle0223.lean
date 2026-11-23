module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.CrisPerFix

variable {l : ℕ} [Fact l.Prime]

def maxUnramifiedFrobenius (P : LocPrime l) (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) :=
  AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij

theorem frobK0_apply (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    maxUnramifiedFrobenius P K x = (P.PD K).σ x := rfl

theorem nontrivial_B (P : LocPrime l) (K : FinExt l) : Nontrivial P.R.B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (P.PD K).not_mem_filtration_two (by rw [Subsingleton.elim ((P.PD K).t) 0, map_zero]; exact Submodule.zero_mem _)

theorem ιB_algebraMap (P : LocPrime l) (K : FinExt l) (a : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.BdR a := by
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes a

theorem orderOf_frobK0 (P : LocPrime l) (K : FinExt l) :
    orderOf (maxUnramifiedFrobenius P K) = finrank ℚ_[l] ↥(K0 K) := by
  haveI := (P.PD K).finK₀
  haveI := nontrivial_B P K
  have hfix : IntermediateField.fixedField (Subgroup.zpowers (maxUnramifiedFrobenius P K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hσ : (P.PD K).σ x = x := hx _ (Subgroup.mem_zpowers _)
    obtain ⟨q, hq⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x)
      (by rw [(P.PD K).φ_K₀, hσ])
      (by
        rw [(P.PD K).ι.commutes, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ x (P.PD K).one_mem)
    rw [IntermediateField.mem_bot]
    refine ⟨q, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hq
  have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers (maxUnramifiedFrobenius P K))
  rw [hfix, IntermediateField.finrank_bot', Nat.card_zpowers] at h
  exact h.symm

theorem iterate_φB_mul (P : LocPrime l) (K : FinExt l) (j : ℕ) (b : ↥(K0 K)) (x : P.R.B) :
    (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * x) =
      algebraMap ↥(K0 K) P.R.B ((maxUnramifiedFrobenius P K ^ j) b) * (⇑P.φB)^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, ← P.PD_φ K (algebraMap _ _ _), (P.PD K).φ_K₀,
      Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, frobK0_apply]

theorem det_ne_zero (P : LocPrime l) (K : FinExt l)
    (bas : Module.Basis (Fin (finrank ℚ_[l] ↥(K0 K))) ℚ_[l] ↥(K0 K)) :
    (Matrix.of fun i j : Fin (finrank ℚ_[l] ↥(K0 K)) => (maxUnramifiedFrobenius P K ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  set τ := maxUnramifiedFrobenius P K
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    { toFun := fun x => ∑ j : Fin (finrank ℚ_[l] ↥(K0 K)), u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin (finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →* ↥(K0 K)) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : _ ≃+* _).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom ↥(K0 K) ↥(K0 K)).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

theorem mem_unramified_of_frobenius_iterate_fixed_fil_alt :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c →
    (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) →
    ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  intro l _ P _ _ K c hn hF
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  haveI := (P.PD K).finK₀
  set τ := maxUnramifiedFrobenius P K
  have hord : orderOf τ = n := orderOf_frobK0 P K
  have hn0 : 0 < n := Module.finrank_pos
  let bas := Module.finBasisOfFinrankEq ℚ_[l] ↥(K0 K) hn_def.symm
  let A : Matrix (Fin n) (Fin n) ↥(K0 K) := Matrix.of fun i j => (τ ^ (j : ℕ)) (bas i)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero P K bas)
  have hs : ∀ b : ↥(K0 K), ∃ q : ℚ_[l], algebraMap ℚ_[l] P.R.B q =
      ∑ j ∈ Finset.range n, (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c) := by
    intro b
    apply (P.PD K).fund
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [P.PD_φ, map_sum]
        have e1 : ∀ j, P.φB ((⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) =
            (⇑P.φB)^[j + 1] (algebraMap ↥(K0 K) P.R.B b * c) :=
          fun j => (Function.iterate_succ_apply' _ _ _).symm
        simp_rw [e1]
        have hfn : (⇑P.φB)^[n] (algebraMap ↥(K0 K) P.R.B b * c) =
            (⇑P.φB)^[0] (algebraMap ↥(K0 K) P.R.B b * c) := by
          rw [iterate_φB_mul, hn, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply, Function.iterate_zero, id]
        have h := Finset.sum_range_succ' (fun j => (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) n
        rw [Finset.sum_range_succ, hfn] at h
        exact (add_right_cancel h).symm
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [P.PD_ι, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [iterate_φB_mul, map_mul, ιB_algebraMap, ← Algebra.smul_def]
        exact Submodule.smul_of_tower_mem _ _ (hF j)
  choose q hq using fun i => hs (bas i)
  let v : Fin n → P.R.B := fun j => (⇑P.φB)^[(j : ℕ)] c
  have hAv : Matrix.mulVec (A.map (algebraMap ↥(K0 K) P.R.B)) v =
      fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply, hq i, Finset.sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, v, Matrix.of_apply, iterate_φB_mul]
    rfl
  have hinv : (A⁻¹.map (algebraMap ↥(K0 K) P.R.B)) * (A.map (algebraMap ↥(K0 K) P.R.B)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : v = Matrix.mulVec (A⁻¹.map (algebraMap ↥(K0 K) P.R.B))
      (fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i))) := by
    rw [← hAv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨∑ i, A⁻¹ ⟨0, hn0⟩ i * algebraMap ℚ_[l] ↥(K0 K) (q i), ?_⟩
  have h0 := congrFun hv ⟨0, hn0⟩
  simp only [v, Function.iterate_zero, id] at h0
  rw [h0]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.CrisPerFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
section
noncomputable section
namespace GlobalTheory.ThetaTie
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow {P : LocPrime l} (AI : LocAinf l P) (m n : ℕ) : AI.ζ (m + n) ^ l ^ n = AI.ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem isEps {P : LocPrime l} (AI : LocAinf l P) : IsEps (l := l) AI.ε := by
  constructor
  · refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
    have := zeta_pow AI 0 n
    rw [zero_add, AI.ζ_zero] at this
    rw [this]
  · have : ((frobeniusEquiv (Per.Fl l) l).symm AI.ε).untilt = AI.ζ 1 := by
      refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
      refine ⟨AI.ζ (1 + n), ?_, ?_⟩
      · rw [add_comm]
        exact (AI.ε_coeff (n + 1)).symm.trans (PreTilt.coeff_frobeniusEquiv_symm n _).symm
      · rw [zeta_pow AI 1 n]
    rw [this]
    exact AI.ζ_one

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  have : Subsingleton (Per.AinfP l ⧸ Per.kerP l ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]; infer_instance
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 0 y).2 (Subsingleton.elim _ _)

theorem mem_filD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact GlobalTheory.RingIface.exists_of_mem_FilD_nat l
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem alg_inj {e : Per.Fl l} (he : IsEps e) :
    Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := by
  have _ := he
  exact (_root_.GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem log_mu {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have hm : algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
    refine GlobalTheory.RingIface.alg_mem_kerP l ?_
    rw [map_sub, WittVector.fontaineTheta_teichmuller, he.1, map_one, sub_self]
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  change Per.ev l 2 (algebraMap (Per.AinfP l) (Per.BdRp l)
    (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) - y) = 0
  rw [map_sub, ev_alg]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = m at hm h ⊢
  have h2 : Ideal.Quotient.mk (Per.kerP l ^ 2) (m ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hm 2)
  have hu : IsUnit ((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  have hs : (∑ k ∈ Finset.range 2, (-1) ^ k * (((2 : ℕ).factorial / (k + 1) : ℕ) : Per.AinfP l) *
      m ^ (k + 1)) = ((2 : ℕ) : Per.AinfP l) * m - m ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hs, map_sub, h2, sub_zero, map_mul, map_natCast] at h
  rw [sub_eq_zero]
  exact (hu.mul_left_cancel h).symm

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem eD_ιA (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  refine Eq.trans ?_ h
  simp

theorem fil_nat (n : ℕ) (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil n ↔
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (T.fil _ _ _).trans (mem_filD_nat n _)

theorem fil_zero (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil 0 ↔
    ∃ z, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (fil_nat T 0 x).trans ⟨fun ⟨z, _, h⟩ => ⟨z, h⟩, fun ⟨z, h⟩ => ⟨z, mem_filtration_zero' z, h⟩⟩

def th (x : P.R.BdR) : ℂ_[l] :=
  Per.θD l (Function.invFun (algebraMap (Per.BdRp l) (Per.BdR l)) (T.eD x))

theorem th_eq {x : P.R.BdR} {z : Per.BdRp l}
    (h : algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x) : th T x = Per.θD l z := by
  rw [th, ← h, Function.leftInverse_invFun (alg_inj (isEps AI))]

include T in
theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD (botExt l)).Fil (-1), P.ιB P.tB * s = 1 := by
  obtain ⟨h1, -, -, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l _ (isEps AI)
  obtain ⟨-, hk, hun, -, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  have hu := (P.PD (botExt l)).t_unit
  have t1 := (P.PD (botExt l)).mem_filtration_one
  have t2 := (P.PD (botExt l)).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at t1 t2
  rw [P.period_datum_t_eq] at hu
  obtain ⟨s, hs⟩ := (hu.map P.ιB).exists_right_inv
  refine ⟨s, ?_, hs⟩
  obtain ⟨z, hz, ez⟩ := (fil_nat T 1 _).1 t1
  obtain ⟨u, rfl⟩ := (h1 1 z).1 hz
  have huu : IsUnit u := hun u fun h0 => by
    obtain ⟨w, rfl⟩ := (h1 1 u).1 ((hk u).1 h0)
    exact t2 ((fil_nat T 2 _).2 ⟨_, (h1 2 _).2 ⟨w, by ring⟩, ez⟩)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  rw [T.fil, _root_.GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l _ (isEps AI)]
  refine ⟨v, ?_⟩
  have e1 : T.eD (P.ιB P.tB) * T.eD s = 1 := by rw [← map_mul, hs, map_one]
  have e2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv
  rw [← ez] at e1
  rw [show (- (-1 : ℤ)).toNat = 1 from rfl, show (-1 : ℤ).toNat = 0 from rfl]
  simp only [map_mul, map_one, pow_one, pow_zero, one_mul] at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi AI.ε)) = X at e1 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) u = U at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) v = V at e2 ⊢
  linear_combination V * e1 - (T.eD s * X) * e2

def thetaL : ThetaL P AI where
  θ := th T
  θ_one := by rw [th_eq T (z := 1) (by simp), map_one]
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a + b) (by rw [map_add (f := _), map_add (f := _), ha, hb]), map_add (f := _)]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨z, hz⟩ := (_root_.GlobalTheory.MemLoc.thetaD_props l).1 c
    have e : algebraMap (Per.BdRp l) (Per.BdR l) z =
        T.eD (T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) z)) := (T.eD.apply_symm_apply _).symm
    exact ⟨_, (fil_zero T _).2 ⟨z, e⟩, (th_eq T e).trans hz⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    rw [th_eq T ha, (_root_.GlobalTheory.MemLoc.thetaD_props l).2.1]
    refine ⟨fun h => (fil_nat T 1 x).2 ⟨a, h, ha⟩, fun h => ?_⟩
    obtain ⟨z, hz, e⟩ := (fil_nat T 1 x).1 h
    rwa [← alg_inj (isEps AI) (e.trans ha.symm)]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g a) = T.eD (P.actQdR g x) := by
      rw [T.actD, ← ha]
      exact (GlobalTheory.RingIface.sigD_alg l g a).symm
    rw [th_eq T ha, th_eq T e, actC_eq, (_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.2.2]
  θ_Om x := by
    obtain ⟨y, h1, h2⟩ := T.om x
    rw [th_eq T h1.symm, h2]
  θ_int a := by
    rw [th_eq T (eD_ιA T a).symm, (_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  θ_teich x y h := by
    rw [th_eq T (eD_ιA T _).symm, (_root_.GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, WittVector.fontaineTheta_teichmuller]
    have h1 := Ideal.Quotient.eq.1 ((PreTilt.mk_untilt_eq_coeff_zero x).trans h)
    have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
    simpa using h2
  fil_succ_iff_mul_t a x := by
    have t1 := (P.PD (botExt l)).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at t1
    constructor
    · intro hx
      obtain ⟨s, hs, e⟩ := exists_inverse_fontaineElement_mem_fil_neg_one T
      refine ⟨s * x, ?_, by rw [← mul_assoc, e, one_mul]⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ hs hx
      rwa [show -1 + (a + 1) = a by ring] at this
    · rintro ⟨y, hy, rfl⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ t1 hy
      rwa [add_comm] at this
  t_μ := by
    obtain ⟨y, hy, e⟩ := T.t
    refine (fil_nat T 2 _).2 ⟨_, log_mu (isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, eD_ιA]
    rfl

theorem nonempty_thetaL (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] :
    Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  ⟨thetaL (D.locT l)⟩

end GlobalTheory.ThetaTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLevel_expansion_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  first | exact @GlobalTheory.NL.lev_at_root_of_unity | exact GlobalTheory.NL.lev_at_root_of_unity | (intros; apply GlobalTheory.NL.lev_at_root_of_unity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachWeierstrass_test_and_density : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → a ∈ van W i ζ k) → W.Q ^ k ∣ a) ∧ (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → a ∈ van W i ζ k) → W.X ^ k ∣ a) ∧ (∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧ ∀ (i' : Let K) (ζ' : ↥LL.1), IsPrimitiveRoot ζ' (l ^ s) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  first | exact @GlobalTheory.NL.WDiv.weierstrass_dense | exact GlobalTheory.NL.WDiv.weierstrass_dense | (intros; apply GlobalTheory.NL.WDiv.weierstrass_dense <;> assumption)
end

