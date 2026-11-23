module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

theorem sep_complete_of_coord {R A B I : Type} [AddCommGroup R] [CommRing A] [CommRing B]
    (φ : I → R →+ B) (j : A →+* B) (hj : Function.Injective j) (t : A)
    (hs : ∀ c : I → A, ∃ x : R, ∀ i, φ i x = j (c i))
    (h1 : ∀ x : A, (∀ m : ℕ, t ^ m ∣ x) → x = 0)
    (h2 : ∀ a : ℕ → A, ∃ x : A, ∀ m : ℕ, t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i) :
    (∀ x : R, (∀ (m : ℕ) i, ∃ c, φ i x = j (t ^ m * c)) → ∀ i, φ i x = 0) ∧
    ∀ (k : ℕ) (f : ℕ → R), (∀ n i, ∃ c, φ i (f n) = j (t ^ (n + k) * c)) →
      ∃ x, ∀ (m : ℕ) i, ∃ c, φ i (x - ∑ n ∈ Finset.range m, f n) = j (t ^ (m + k) * c) := by
  refine ⟨fun x hx i => ?_, fun k f hf => ?_⟩
  · obtain ⟨y, hy⟩ := hx 0 i
    rw [pow_zero, one_mul] at hy
    have hdiv : ∀ m : ℕ, t ^ m ∣ y := by
      intro m
      obtain ⟨c, hc⟩ := hx m i
      exact ⟨c, hj (hy.symm.trans hc)⟩
    rw [hy, h1 y hdiv, map_zero]
  · choose c hc using hf
    choose y hy using fun i => h2 (fun n => c n i)
    obtain ⟨x, hx⟩ := hs (fun i => t ^ k * y i)
    refine ⟨x, fun m i => ?_⟩
    obtain ⟨d, hd⟩ := hy i m
    refine ⟨d, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hx i, Finset.sum_congr rfl (fun n _ => hc n i), ← map_sum j, ← map_sub j]
    congr 1
    have e : t ^ k * y i - ∑ n ∈ Finset.range m, t ^ (n + k) * c n i =
        t ^ k * (y i - ∑ n ∈ Finset.range m, t ^ n * c n i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hd]
    ring

def crdZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    RW LL →+ Cb l :=
  (WittVector.constantCoeff : WCb l →+* Cb l).toAddMonoidHom.comp
    (crd (W := WCb l) (basisO LL) i).toAddMonoidHom

theorem crdZero_apply {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i) (x : RW LL) :
    crdZero LL i x = (crd (basisO LL) i x).coeff 0 := rfl

private theorem crd_tmul_lemma {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (o : ↥(OL LL)) (w : WCb l) :
    crd (W := WCb l) (basisO LL) i (o ⊗ₜ[ℤ_[l]] w) = (basisO LL).coord i o • w := by
  unfold crd
  rfl

set_option maxHeartbeats 1000000 in
private theorem crd_mul_lemma_2 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (q : WCb l) (y : RW LL) :
    crd (W := WCb l) (basisO LL) i (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] q) * y) =
      q * crd (W := WCb l) (basisO LL) i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma, mul_smul_comm]
  | add y z hy hz =>
    rw [mul_add, LinearMap.map_add (f := _), LinearMap.map_add (f := _), hy, hz]
    exact (mul_add q _ _).symm

private theorem expand_lemma_3 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (y : RW LL) :
    ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] crd (W := WCb l) (basisO LL) k y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [crd_tmul_lemma, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    simp_rw [Module.Basis.coord_apply]
    rw [Module.Basis.sum_repr]
  | add y z hy hz => simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WCb l) :
    crd (W := WCb l) (basisO LL) i (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] w k) = w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, crd_tmul_lemma, Finsupp.single_apply]

private theorem wdiv_lemma_5 {l : ℕ} [Fact l.Prime] (w : WCb l) (hw : w.coeff 0 = 0) :
    ∃ v : WCb l, w = (l : WCb l) * v := by
  have e : w = WittVector.verschiebung^[1] (w.shift 1) :=
    WittVector.eq_iterate_verschiebung (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hw)
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective (p := l) (R := Cb l)).2 (w.shift 1)
  refine ⟨z, ?_⟩
  rw [e, Function.iterate_one, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private theorem rwdiv_lemma_6 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (z : RW LL)
    (hz : ∀ i, (crd (W := WCb l) (basisO LL) i z).coeff 0 = 0) : ∃ r : RW LL, z = (l : RW LL) * r := by
  choose v hv using fun i => wdiv_lemma_5 _ (hz i)
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] v k, ?_⟩
  rw [← expand_lemma_3 LL z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hv k, ← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

private theorem cc_inclW_lemma_7 {l : ℕ} [Fact l.Prime] (w : Ainf l) :
    (inclW l w).coeff 0 = algebraMap (OCb l) (Cb l) (w.coeff 0) := by
  unfold inclW
  exact WittVector.map_coeff _ _ 0

private theorem cc_pi_lemma_8 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ) :
    (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 =
      algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [cc_inclW_lemma_7]
  congr 1
  change WittVector.constantCoeff (WittVector.teichmuller l (AI.εroot s) - 1) = _
  rw [map_sub, map_one]
  rfl

private theorem inclR_piR_lemma_9 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    piR AI LL s =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (AI.εroot s) - 1) := rfl

private theorem inclR_tmul_lemma_10 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (o : ↥(OL LL)) (w : Ainf l) :
    (inclR LL) (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] inclW l w := rfl

private theorem cc_inclR_lemma_11 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l) :
    ∃ c : OCb l, (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 = algebraMap (OCb l) (Cb l) c := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o w =>
    refine ⟨((basisO LL).coord i o • w).coeff 0, ?_⟩
    rw [inclR_tmul_lemma_10, crd_tmul_lemma, ← cc_inclW_lemma_7]
    congr 1
    exact (map_smul (inclWA l) _ _).symm
  | add a b ha hb =>
    obtain ⟨c1, h1⟩ := ha
    obtain ⟨c2, h2⟩ := hb
    refine ⟨c1 + c2, ?_⟩
    have e : (inclR LL) (a + b) = (inclR LL) a + (inclR LL) b := (inclR LL).toRingHom.map_add a b
    rw [e, LinearMap.map_add (f := _), map_add (algebraMap (OCb l) (Cb l)), ← h1, ← h2]
    exact WittVector.add_coeff_zero _ _

private theorem coord_of_near_lemma_12 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL) (h : NearPi AI LL s n y)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c) := by
  unfold NearPi Near at h
  obtain ⟨a, r, rfl⟩ := h
  obtain ⟨c, hc⟩ := cc_inclR_lemma_11 LL i a
  refine ⟨c, ?_⟩
  rw [map_add (f := _), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, crdZero_apply, inclR_piR_lemma_9,
    Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2]
  change WittVector.constantCoeff (p := l) (R := Cb l) (_ * _) + _ = _
  rw [map_mul, map_pow]
  change (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
    (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 + _ = _
  rw [cc_pi_lemma_8, hc, map_mul, map_pow]
  simp

set_option maxHeartbeats 2000000 in
private theorem near_of_coord_lemma_13 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL)
    (h : ∀ i, ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c)) :
    NearPi AI LL s n y := by
  choose c hc using h
  let a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l := ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)
  obtain ⟨r, hr⟩ := rwdiv_lemma_6 LL (y - piR AI LL s ^ n * (inclR LL) a) (fun i => by
    have ha : (inclR LL) a = ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (c k)) := by
      change (inclR LL : RA LL →+* RW LL) (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [LinearMap.map_sub, inclR_piR_lemma_9, Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2, ha,
      crd_sum_lemma_4]
    change WittVector.constantCoeff (p := l) (R := Cb l) (_ - _) = 0
    rw [map_sub, map_mul, map_pow]
    change (crd (W := WCb l) (basisO LL) i y).coeff 0 -
      (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
        (inclW l (WittVector.teichmuller l (c i))).coeff 0 = 0
    rw [← crdZero_apply, hc, cc_pi_lemma_8, cc_inclW_lemma_7, WittVector.teichmuller_coeff_zero, map_mul,
      map_pow, sub_self])
  unfold NearPi Near
  exact ⟨a, r, sub_eq_iff_eq_add'.mp hr⟩

private theorem surj_lemma_14 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (c : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l) :
    ∃ x : RW LL, ∀ i, crdZero LL i x = algebraMap (OCb l) (Cb l) (c i) := by
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (c k)),
    fun i => ?_⟩
  rw [crdZero_apply, crd_sum_lemma_4, WittVector.teichmuller_coeff_zero]

theorem nearPi_sep_complete (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧
    ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) →
      ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  have key := sep_complete_of_coord (fun i => crdZero LL i) (algebraMap (OCb l) (Cb l))
    (IsFractionRing.injective (OCb l) (Cb l)) (AI.εroot s - 1) (surj_lemma_14 LL)
    (_root_.GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 (_root_.GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).2
  refine ⟨fun x hx => ?_, fun k f hf => ?_⟩
  · refine rwdiv_lemma_6 LL x fun i => ?_
    rw [← crdZero_apply]
    exact key.1 x (fun m i => coord_of_near_lemma_12 P AI LL s m x (hx m) i) i
  · obtain ⟨x, hx⟩ := key.2 k f (fun n i => coord_of_near_lemma_12 P AI LL s (n + k) (f n) (hf n) i)
    exact ⟨x, fun m => near_of_coord_lemma_13 P AI LL s (m + k) _ (hx m)⟩

end GlobalTheory.Decompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAlgebraMap
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.GroupLayer

variable {l : ℕ} [Fact l.Prime]

theorem v_le_iff (P : LocPrime l) (LL : FinExt l) (x y : ↥LL.1) :
    P.v LL y ≤ P.v LL x ↔ ‖(x : Om l)‖ ≤ ‖(y : Om l)‖ := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  by_cases hy : y = 0
  · subst hy
    simp only [AddValuation.map_zero, top_le_iff, AddValuation.top_iff, ZeroMemClass.coe_zero,
      norm_zero, norm_le_zero_iff, ZeroMemClass.coe_eq_zero]
  · have hne : P.v LL y ≠ ⊤ := fun h => hy ((AddValuation.top_iff _).1 h)
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hq, h2, (h1 y q).1 hq.symm]

theorem norm_coe_algebraMap (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) : ↥LL.1) : Om l)‖ = ‖a‖ := by
  change ‖algebraMap ℚ_[l] (Om l) (a : ℚ_[l])‖ = ‖(a : ℚ_[l])‖
  simp

theorem norm_pow_sub_one (LL : FinExt l) (a : ℤ_[l]) (k : ℕ) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 ((algebraMap ℤ_[l] ↥(OL LL) a) ^ k) - 1 : ↥LL.1) : Om l)‖
      = ‖a ^ k - 1‖ := by
  rw [← norm_coe_algebraMap LL (a ^ k - 1), map_sub, map_sub, map_one, map_one, map_pow (algebraMap ℤ_[l] ↥(OL LL))]

theorem norm_sub_one (LL : FinExt l) (a : ℤ_[l]) :
    ‖((algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) a) - 1 : ↥LL.1) : Om l)‖
      = ‖a - 1‖ := by
  simpa only [pow_one] using norm_pow_sub_one LL a 1

noncomputable def congSub (l : ℕ) [Fact l.Prime] (s : ℕ) : Subgroup ℤ_[l]ˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {(l : ℤ_[l]) ^ s})).toMonoidHom).ker

theorem mem_congSub (s : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ congSub l s ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← Ideal.Quotient.eq, congSub, MonoidHom.mem_ker,
    Units.ext_iff]
  simp

theorem nonempty_gamS : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l),
    Good K s LL → Nonempty (GamS P K s LL) := by
  intro l _ P K s LL hG
  obtain ⟨emb, hbij, hσ⟩ := GlobalTheory.HWL.exists_letters l P K s LL hG
  obtain ⟨hs1, hs2, hKs, -⟩ := hG
  obtain ⟨χ, hχ, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨one, hone1, hone2⟩ := GlobalTheory.HWL.exists_unitLat l K LL
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HWL.NormVal.locPrime_v_normalised l P LL
  let χK : ↥(GK K) →* ℤ_[l]ˣ := χ.comp (GK K).subtype
  obtain ⟨gam, gamK, D, hgam, hD, hK, hKeq, hK1⟩ := GlobalTheory.PadicUnitSub.exists_gam_gamK_torsion l s χK.range hs1 hs2 (fun u hu => by
    obtain ⟨g, hg, hgu⟩ := honto K s hKs u hu
    exact ⟨⟨g, hg⟩, hgu⟩)
  let χΓ : ↥χK.range →* (↥(OL LL))ˣ :=
    (Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom).comp χK.range.subtype
  have hχΓ : ∀ g : ↥χK.range, (χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) ((g : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hres : ∀ g : ↥(GK K), algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) =
      algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) ((χK g : ℤ_[l]ˣ) : ℤ_[l])) := fun g => by
    rw [P.PD_χ, ← hχ]; rfl
  have hs : ((s : ℚ) : WithTop ℚ) = (s : WithTop ℚ) := by norm_cast
  have hz : (l : ℝ) ^ (-((s : ℚ) : ℝ)) = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  refine ⟨{ emb := emb, emb_bij := hbij, emb_σ := hσ, n_eq := rfl, v_l := ?_, s_pos := hs1,
            s_two := fun h => hs2 (by rwa [P.PD_p] at h), Gam := ↥χK.range,
            resΓ := χK.rangeRestrict, resΓ_onto := χK.rangeRestrict_surjective, χΓ := χΓ,
            χΓ_res := fun g => (hres g).symm, χΓ_inj := ?_, gam := gam, gam_gen := ?_, DelF := D,
            DelF_def := hD, gamK := gamK, gamK_gen := ?_, gamK_eq := ?_,
            gamK_eq_one := fun h h' => hK1 h (by rwa [P.PD_p] at h'),
            GKs := (congSub l s).comap χK, GKs_def := ?_, one := one, one_triv := hone1,
            one_line := hone2 }⟩
  · rw [P.PD_p]
    have := (h1 (l : ↥LL.1) 1).2 (by
      have h := norm_coe_algebraMap LL (l : ℤ_[l])
      rw [map_natCast, map_natCast] at h
      rw [h, PadicInt.norm_p]; simp [Real.rpow_neg_one])
    simpa using this
  · intro a b hab
    have h := congrArg (fun u : (↥(OL LL))ˣ => (u : ↥(OL LL))) hab
    simp only [hχΓ] at h
    have h0 := norm_coe_algebraMap LL (((a : ℤ_[l]ˣ) : ℤ_[l]) - ((b : ℤ_[l]ˣ) : ℤ_[l]))
    rw [map_sub, h, sub_self, map_zero, ZeroMemClass.coe_zero, norm_zero, eq_comm, norm_eq_zero,
      sub_eq_zero] at h0
    exact Subtype.ext (Units.ext h0)
  · rw [← hs, h1, hχΓ, norm_sub_one, hgam, hz]
  · intro g
    rw [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one]
    exact hK g
  · intro h
    refine hKeq fun g => ?_
    have := h g
    rwa [v_le_iff, hχΓ, hχΓ, norm_pow_sub_one, norm_pow_sub_one] at this
  · intro g
    rw [Subgroup.mem_comap, mem_congSub, ← hs, h2, hres, norm_sub_one, hz]

end GlobalTheory.HWL.GroupLayer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.arith {α : Type} [Fintype α] [DecidableEq α] (f : α → ℤ) (h0 : ∑ z, f z = 0) (hf : f ≠ 0) :
    ∃ x y, x ≠ y ∧ ∑ z, (f z + eps x y z) = 0 ∧ ∑ z, (f z + eps x y z) ^ 2 < ∑ z, f z ^ 2 := by
  have hx : ∃ x, 0 < f x := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  have hy : ∃ y, f y < 0 := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x ≠ y := fun e => by rw [e] at hx; omega
  have e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x := by
    intro g
    have : ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0) := by
      intro z
      unfold eps
      by_cases a : z = x
      · subst a; simp [hxy]
      · by_cases b : z = y
        · subst b; simp [a]
        · simp [a, b]
    simp [this, Finset.sum_sub_distrib]
  have ex : eps x y x = -1 := by simp [eps]
  have ey : eps x y y = 1 := by simp [eps, hxy.symm]
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have := e1 fun _ => 1
    simp only [one_mul] at this
    rw [Finset.sum_add_distrib, h0, this]; simp
  · have a := e1 f
    have b := e1 (eps x y)
    have : ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, a, b, ex, ey]
    omega

theorem GlobalTheory.PMon.matThm_of_steps : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  intro hF hT hS hR hM l _ P AI T
  suffices H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N →
      ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from
    fun n _ _ K r ρ => H _ n rfl K r ρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro n _ _ hn K r ρ hρ hd
  obtain ⟨w, hw⟩ := (hF l P AI T n K r ρ hρ).1 hd
  obtain ⟨K', r', ρ', w', h1, h2, h3, h4⟩ := hT l P AI T n K r ρ w hρ hw
  apply h4
  suffices G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v →
      ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from
    G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl
  intro S
  induction S using Nat.strong_induction_on with
  | _ S IS =>
  intro σ v a1 a2 a3 a4
  by_cases hv : (fun z : Fin r' × n => v z.1 z.2) = 0
  · have : v = 0 := funext fun m => funext fun j => congrFun hv (m, j)
    subst this
    exact hS l P AI T n K' r' σ a1 a2
  by_cases hs : Splits r' σ
  · exact hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs
      fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2
  obtain ⟨x, y, hxy, c1, c2⟩ := GlobalTheory.PMon.arith _ a3 hv
  obtain ⟨τ, b1, b2, b3⟩ := hM l P AI T n K' r' σ v x y hxy a1 a2 hs
  refine b3 (IS _ ?_ τ _ b1 b2 c1 rfl)
  have p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S
  omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowMulInvPowMemAinfFilLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), Lev l s → ∀ u ∈ FilB P 0, io AI AI.π₁ * u = 1 → ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l, (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | exact GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | (intros; apply GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionMapPi0
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem map_pi0 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [Algebra O k] [CharP k l], PD.p = l → ∀ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, (∀ δ a, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) a)) → PowerSeries.map (algebraMap O k) W.π₀₁ = 1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1}, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l _ k _ _ _ hp e he

  have hsub : ∀ z : ℤ_[l], GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l z (1 + PowerSeries.X) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z := by
    intro z
    have ha : PowerSeries.HasSubst (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z - 1) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      rw [map_sub, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.binomialSeries_constantCoeff, map_one, sub_self]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi
    rw [← PowerSeries.coe_substAlgHom ha, map_add (f := _), map_one, PowerSeries.substAlgHom_X ha]
    ring

  have hl : (l : k⟦X⟧) = 0 := by
    rw [← map_natCast (PowerSeries.C : k →+* k⟦X⟧), CharP.cast_eq_zero, map_zero]
  unfold LocWach.π₀₁
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sub, map_one, map_natCast, hp, hl, sub_zero, map_sum, ← Finset.sum_coe_sort W.DelF,
    Finset.sum_congr rfl fun δ _ => by rw [he, map_add (f := _), map_one, PowerSeries.map_X, hsub],
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltMultiplicativeExtensionSurjective
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.TshOnto

theorem tsh_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  intro l _ F _ ι tsh _hn hsh _ t
  obtain ⟨-, -, -, -, -, honto, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  by_cases ht : ‖t‖ ≤ 1
  · obtain ⟨x, hx⟩ := honto t ht
    exact ⟨ι x, by rw [hsh, hx]⟩
  · push_neg at ht
    have hinv : ‖t⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ ht.le
    obtain ⟨x, hx⟩ := honto t⁻¹ hinv
    refine ⟨(ι x)⁻¹, ?_⟩
    rw [map_inv₀, hsh, hx, inv_inv]

end GlobalTheory.PSer.TshOnto
end

