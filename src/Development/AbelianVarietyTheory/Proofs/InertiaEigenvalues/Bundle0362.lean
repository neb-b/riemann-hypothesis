module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBases
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevelBasis

variable {A L Q : Type} [CommRing A] [CommRing L] [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A)
  {ι : Type} (m : ι → L)

def lsum (c : ι →₀ A) : L := c.sum fun k a => s a * m k

theorem lsum_add (c c' : ι →₀ A) : lsum s m (c + c') = lsum s m c + lsum s m c' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add (f := _), add_mul])

theorem lsum_sub (c c' : ι →₀ A) : lsum s m (c - c') = lsum s m c - lsum s m c' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

theorem lsum_smul (a : A) (c : ι →₀ A) : lsum s m (a • c) = s a * lsum s m c := by
  unfold lsum
  rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mul_assoc]

theorem lsum_single (k : ι) : lsum s m (Finsupp.single k 1) = m k := by
  unfold lsum; rw [Finsupp.sum_single_index (by simp), map_one, one_mul]

def IsApprox (n : ℕ) (x : Q) (c : ι →₀ A) : Prop := x - i (lsum s m c) ∈ (J ^ n).map (i.comp s)

theorem map_pow_eq (n : ℕ) : (J ^ n).map (i.comp s) = ((J.map s) ^ n).map i := by
  rw [← Ideal.map_map, Ideal.map_pow]

variable {s i J m}

theorem IsApprox.mono {n n' : ℕ} {x : Q} {c : ι →₀ A} (h : n' ≤ n) (hc : IsApprox s i J m n x c) :
    IsApprox s i J m n' x c :=
  Ideal.map_mono (Ideal.pow_le_pow_right h) hc

theorem exists_approx (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (n : ℕ) (x : Q) : ∃ c, IsApprox s i J m n x c := by
  obtain ⟨a, ha⟩ := hc.surj x n
  obtain ⟨c, hc'⟩ := H1 n a
  refine ⟨c, ?_⟩
  unfold IsApprox
  have e : x - i (lsum s m c) = (x - i a) + i (a - lsum s m c) := by rw [map_sub]; ring
  rw [e, map_pow_eq]
  refine add_mem ha (Ideal.mem_map_of_mem i ?_)
  rw [← Ideal.map_pow]; exact hc'

theorem approx_unique (hc : IsCompl i (J.map s))
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n)
    {n : ℕ} {x : Q} {c c' : ι →₀ A} (h : IsApprox s i J m n x c) (h' : IsApprox s i J m n x c') (k : ι) :
    c k - c' k ∈ J ^ n := by
  have h3 := sub_mem h' h
  have e : x - i (lsum s m c') - (x - i (lsum s m c)) = i (lsum s m (c - c')) := by
    rw [lsum_sub, map_sub]; ring
  rw [e, map_pow_eq] at h3
  have h4 := hc.ker _ n h3
  rw [← Ideal.map_pow] at h4
  simpa using H2 n (c - c') h4 k

end GlobalTheory.BSP.LevelBasis


open GlobalTheory.BSP.LevelBasis in
theorem GlobalTheory.BSP.exists_topBasis_of_levels (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι) (h1 : m k₀ = 1)
    (hA : IsAdicComplete J A) (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) :
    ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  have mt : ∀ n : ℕ, (J ^ n • ⊤ : Submodule A A) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have exA := exists_approx (m := m) hc H1
  have lim : ∀ (x : Q) (k : ι), ∃ a : A, ∀ n c, IsApprox s i J m n x c → c k - a ∈ J ^ n := by
    intro x k
    choose f hf using exA
    obtain ⟨a, ha⟩ := hA.toIsPrecomplete.prec (f := fun n => f n x k) (fun {p q} hpq => by
      rw [SModEq.sub_mem, mt]
      exact approx_unique hc H2 (hf p x) ((hf q x).mono hpq) k)
    refine ⟨a, fun n c hcn => ?_⟩
    have h2 := ha n
    rw [SModEq.sub_mem, mt] at h2
    have := add_mem (approx_unique hc H2 hcn (hf n x) k) h2
    simpa using this
  choose C hC using lim
  have uniq : ∀ x k a, (∀ n, ∃ c, IsApprox s i J m n x c ∧ c k - a ∈ J ^ n) → C x k = a := by
    intro x k a h
    refine sub_eq_zero.1 (hA.toIsHausdorff.haus _ fun n => ?_)
    rw [SModEq.sub_mem, mt, sub_zero]
    obtain ⟨c, hc1, hc2⟩ := h n
    have := sub_mem hc2 (hC x k n c hc1)
    convert this using 1; ring
  have single_approx : ∀ n k, IsApprox s i J m n (i (m k)) (Finsupp.single k 1) := by
    intro n k; unfold IsApprox; rw [lsum_single, sub_self]; exact zero_mem _
  refine ⟨{
    b := fun k => i (m k)
    c := fun k => AddMonoidHom.mk' (fun x => C x k) (fun x y => uniq (x + y) k _ fun n => by
      obtain ⟨c, hc⟩ := exA n x
      obtain ⟨c', hc'⟩ := exA n y
      refine ⟨c + c', ?_, ?_⟩
      · unfold IsApprox at hc hc' ⊢
        have e : x + y - i (lsum s m (c + c')) = (x - i (lsum s m c)) + (y - i (lsum s m c')) := by
          rw [lsum_add, map_add (f := _)]; ring
        rw [e]; exact add_mem hc hc'
      · have := add_mem (hC x k n c hc) (hC y k n c' hc')
        convert this using 1; simp only [Finsupp.add_apply]; ring)
    c_mul := fun k a x => by
      simp only [AddMonoidHom.mk'_apply]
      refine uniq _ k _ fun n => ?_
      obtain ⟨c, hc⟩ := exA n x
      refine ⟨a • c, ?_, ?_⟩
      · unfold IsApprox at hc ⊢
        have e : (i.comp s) a * x - i (lsum s m (a • c)) = (i.comp s) a * (x - i (lsum s m c)) := by
          rw [lsum_smul, map_mul, RingHom.comp_apply]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ hc
      · have e : (a • c) k - a * C x k = a * (c k - C x k) := by
          rw [Finsupp.smul_apply, smul_eq_mul]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ (hC x k n c hc)
    c_self := fun k => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ k _ fun n => ⟨_, single_approx n k, by simp⟩
    c_ne := fun j k hjk => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ j _ fun n => ⟨_, single_approx n k, by simp [Finsupp.single_apply, Ne.symm hjk]⟩
    fin := fun x n => by
      obtain ⟨c, hc⟩ := exA n x
      refine c.support.finite_toSet.subset fun k hk => ?_
      simp only [Set.mem_setOf_eq, AddMonoidHom.mk'_apply] at hk
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      have := hC x k n c hc
      rw [h, zero_sub, neg_mem_iff] at this
      exact hk this
    approx := fun x n F hF => by
      classical
      simp only [AddMonoidHom.mk'_apply] at hF ⊢
      obtain ⟨c, hc⟩ := exA n x
      have e1 : i (lsum s m c) = ∑ k ∈ F ∪ c.support, (i.comp s) (c k) * i (m k) := by
        unfold lsum
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finsupp.sum_of_support_subset c (Finset.subset_union_right (s₁ := F)) _ (fun _ _ => by simp), map_sum]
        simp [RingHom.comp_apply, map_mul]
      have e2 : ∑ k ∈ F, (i.comp s) (C x k) * i (m k) =
          ∑ k ∈ F ∪ c.support, (i.comp s) (if k ∈ F then C x k else 0) * i (m k) := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun k _ hk => by rw [if_neg hk, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
      have e3 : x - ∑ k ∈ F, (i.comp s) (C x k) * i (m k) = (x - i (lsum s m c)) +
          ∑ k ∈ F ∪ c.support, (i.comp s) (c k - if k ∈ F then C x k else 0) * i (m k) := by
        rw [e2, e1]; simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e3]
      refine add_mem hc (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      by_cases hk : k ∈ F
      · rw [if_pos hk]; exact hC x k n c hc
      · rw [if_neg hk, sub_zero]
        have := add_mem (hC x k n c hc) (hF k hk)
        simpa using this
    complete := by rw [← Ideal.map_map]; exact hc.complete
    i₀ := k₀
    b_i₀ := by simp only [h1, map_one] }, fun k => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eval_derivative_scaleRoots_mul {R : Type*} [CommRing R] (P : Polynomial R) (s x : R) :
    (Polynomial.derivative (P.scaleRoots s)).eval (s * x) =
      s ^ (P.natDegree - 1) * (Polynomial.derivative P).eval x := by
  have h1 : (Polynomial.derivative (P.scaleRoots s)).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le (P.scaleRoots s)
    rw [Polynomial.natDegree_scaleRoots] at this
    omega
  have h2 : (Polynomial.derivative P).natDegree < P.natDegree - 1 + 1 := by
    have := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eval_eq_sum_range' h1, Polynomial.eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ P.natDegree - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_scaleRoots]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
  have h3 : P.natDegree - (i + 1) = k := by omega
  rw [h3, hk]
  ring

theorem exists_approx_root_scaleRoots {R : Type*} [CommRing R] (P : Polynomial R) (hP : 0 < P.natDegree)
    (t x b : R) (c : ℕ) (hb : P.eval x ∣ b * (Polynomial.derivative P).eval x - t ^ c) (n : ℕ) :
    ∃ (m : ℕ) (q : R), P.eval x ∣ q - t ^ m * x ∧ P.eval x ^ (n + 1) ∣ (P.scaleRoots (t ^ m)).eval q := by
  induction n with
  | zero => exact ⟨0, x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, q, ⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    obtain ⟨v, hv⟩ := hb
    set E := P.eval x with hE
    set s := t ^ m with hs
    set r := t ^ c * s ^ e with hr
    have hsr : t ^ (m + (c + m * e)) = s * r := by rw [hr, hs]; ring
    set h := -(b * (P.scaleRoots s).eval q) with hh
    refine ⟨m + (c + m * e), r * q + h, ?_, ?_⟩
    · rw [hsr]
      refine ⟨r * z - b * E ^ n * w, ?_⟩
      rw [hh, hw]
      linear_combination r * hz
    · rw [hsr]
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.scaleRoots (s * r)) (r * q) h
      have h0 : (P.scaleRoots (s * r)).eval (r * q) = r ^ (e + 1) * (P.scaleRoots s).eval q := by
        rw [Polynomial.scaleRoots_mul, Polynomial.scaleRoots_eval_mul, Polynomial.natDegree_scaleRoots, he]
      have h1 := eval_derivative_scaleRoots_mul P (s * r) x
      rw [he, Nat.add_sub_cancel] at h1
      obtain ⟨y, hy⟩ := Polynomial.sub_dvd_eval_sub (r * q) (s * r * x)
        (Polynomial.derivative (P.scaleRoots (s * r)))
      have h2 : (Polynomial.derivative (P.scaleRoots (s * r))).eval (r * q) =
          (s * r) ^ e * (Polynomial.derivative P).eval x + E * (r * z * y) := by
        rw [← h1]
        linear_combination hy + r * y * hz
      rw [hk, h0, h2, hh, hw]
      refine ⟨-((s * r) ^ e * v * w) - b * w * (r * z * y) + k * b ^ 2 * w ^ 2 * E ^ n, ?_⟩
      have h3 : r ^ (e + 1) = (s * r) ^ e * t ^ c := by
        rw [pow_succ, mul_pow]; nth_rewrite 2 [hr]; ring
      rw [h3]
      linear_combination (-((s * r) ^ e * E ^ (n + 1) * w)) * hv

theorem BK.exists_approx_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ),
    ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧
      bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  intro l _ K bk n
  obtain ⟨c, a, b, hab⟩ := _root_.GlobalTheory.BSP.bezout_Ep_derivative l K bk
  have hcoe : ∀ p : Polynomial (Wq l bk.a),
      (p.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) = (p : bk.S) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe]
  have hdeg : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).natDegree = bk.Ep.natDegree :=
    bk.monic.natDegree_map _
  have hb : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) ∣
      (b : bk.S) * (Polynomial.derivative (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S))).eval X -
        (l : bk.S) ^ c := by
    rw [Polynomial.derivative_map, hcoe, hcoe]
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hab
    beta_reduce at h
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, map_pow, map_natCast] at h
    exact ⟨-(a : bk.S), by linear_combination h⟩
  obtain ⟨m, q, h1, h2⟩ := exists_approx_root_scaleRoots _ (hdeg ▸ bk.deg_pos) (l : bk.S) X b c hb n
  rw [hcoe] at h1 h2
  refine ⟨m, q, h1, (pow_dvd_pow _ n.le_succ).trans ?_⟩
  rw [← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, map_natCast]
  exact h2

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResidues
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PSer TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PSer

theorem iterate_phiB_eB_symm (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (j : ℕ) (a : Formalism.Per.Acris l) :
    P.φB^[j] (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) a)) =
      T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
        ((GlobalTheory.MemLoc.phiA l)^[j] a)) := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : P.φB (T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) a)) =
        T.eB.symm (algebraMap _ (Formalism.Per.Bcris l) (GlobalTheory.MemLoc.phiA l a)) := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact GlobalTheory.CrisMaps.φB_phiA l a
    rw [h1, ih]

theorem iterate_phiB_algebraMap_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (c : ℚ_[l]) (j : ℕ)
    (x : P.R.B) : P.φB^[j] (algebraMap ℚ_[l] P.R.B c * x) = algebraMap ℚ_[l] P.R.B c * P.φB^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes]

theorem series_residues : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ c : ℚ_[l], ∃ hm, θ ⟨algebraMap ℚ_[l] P.R.BdR c, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c) ∧
      ∀ (h : ℕ) (r : ℝ) (y : ℕ → Formalism.Per.Fl l), 2 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) →
        ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
          ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j y := by
  intro l _ P AI T
  obtain ⟨S, θ, Θ, hS, hθ1, hθc, hΘn, hΘt, hΘ⟩ := _root_.GlobalTheory.PSer.theta_fil_acris l P AI T
  refine ⟨S, θ, hS, hθ1, hθc, ?_⟩
  intro h r y hh hr hy
  have hp : l.Prime := Fact.out
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hy 0)
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlpos hr
  have hNle : N ≤ l ^ (h * N) :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_left N (by omega)))
  have key : ∀ k, ‖sh (y k ^ l ^ (h * N))‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro k
    rw [(_root_.GlobalTheory.PSer.Laws.sh_laws l).2.2.2.1, norm_pow]
    calc ‖sh (y k)‖ ^ (l ^ (h * N)) ≤ r ^ (l ^ (h * N)) := pow_le_pow_left₀ (norm_nonneg _) (hy k) _
      _ ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hNle
      _ ≤ ‖(l : ℂ_[l])‖ := hN.le
  obtain ⟨w, hwφ, hwΘ⟩ := _root_.GlobalTheory.PSer.exists_acris_Lam l h (fun k => y k ^ l ^ (h * N)) hh key
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ N)⁻¹ with hcdef
  set b' : P.R.B := T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) w) with hb'
  refine ⟨algebraMap ℚ_[l] P.R.B c * b', ?_, ?_, ?_⟩
  · refine ⟨N, w, ?_⟩
    have hc : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B c = 1 := by
      rw [← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_pow, ← map_mul, hcdef,
        mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one]
    rw [← mul_assoc, hc, one_mul, hb', RingEquiv.apply_symm_apply]
  · rw [iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, hwφ, map_mul, map_natCast, map_mul,
      map_natCast]
    ring
  · intro j
    obtain ⟨hm1, e1⟩ := hθc c
    obtain ⟨hm2, e2⟩ := hΘ ((GlobalTheory.MemLoc.phiA l)^[j] w)
    have heq : ev P j (algebraMap ℚ_[l] P.R.B c * b') = algebraMap ℚ_[l] P.R.BdR c *
        P.ιB (T.eB.symm (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)
          ((GlobalTheory.MemLoc.phiA l)^[j] w))) := by
      rw [ev, iterate_phiB_algebraMap_mul, hb', iterate_phiB_eB_symm, map_mul, AlgHom.commutes]
    refine ⟨heq ▸ S.mul_mem hm1 hm2, ?_⟩
    have hsub : (⟨ev P j (algebraMap ℚ_[l] P.R.B c * b'), heq ▸ S.mul_mem hm1 hm2⟩ : ↥S) =
        ⟨algebraMap ℚ_[l] P.R.BdR c, hm1⟩ * ⟨_, hm2⟩ := Subtype.ext heq
    rw [hsub, map_mul, e1, e2, hwΘ Θ hΘn hΘt j,
      (_root_.GlobalTheory.PSer.Lam_main l h j r y (by omega) hr hy).2.2.2 N, hcdef, map_inv₀, map_pow, map_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero))]

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ τ : Ainf l, bk.IsPer τ := by
  intro l hl K bk
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  set x : Ainf l := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := by
    rw [hx, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hφx : WittVector.frobenius x = Per.tm e := by
    rw [hx, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
      frobeniusEquiv_symm_pow_p]
  have hξ : GlobalTheory.MemLoc.xi e * (x - 1) = Per.tm e - 1 := by
    rw [GlobalTheory.MemLoc.xi, ← hx, geom_sum_mul, hxl]
  have hsp : Ideal.span {bk.ev bk.E} = Ideal.span {GlobalTheory.MemLoc.xi e} :=
    bk.span_ev.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  obtain ⟨ω, hω⟩ := Ideal.span_singleton_eq_span_singleton.1 hsp.symm
  obtain ⟨η, hη⟩ := _root_.GlobalTheory.Per.frobenius_eq_mul_solvable l ω
  refine ⟨(x - 1) * η, ?_, e, ω * η, hE, ?_⟩
  · rw [map_mul, map_sub, map_one, hφx, hη, ← hω, ← hξ]
    ring
  · rw [map_mul, map_sub, map_one, hφx, hη, Units.val_mul]
    rw [mul_comm]
end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycIntegral

theorem cyc_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
  obtain ⟨_, _, _, _, hopen⟩ := hO
  obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
  have hn : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  have hmem := GlobalTheory.GoodCoeff.padicInt_mem (algebraMap O LL).range
    (by rw [RingHom.coe_range]; exact hopen) (⟨_, hn⟩ : ℤ_[l])
  obtain ⟨b, hb⟩ := RingHom.mem_range.1 hmem
  refine ⟨b, ?_⟩
  rw [hb]
  simp [cycLL, LocPrime.PD_χ]

theorem cyc_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  intro l _ P K LL _ _ _ O _ _ hO
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := cyc_mem l P K LL O hO g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

end GlobalTheory.CycIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinearStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tatePairing_bilinear : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  first | exact @GlobalTheory.PairLine.exists_pair | exact GlobalTheory.PairLine.exists_pair | (intros; apply GlobalTheory.PairLine.exists_pair <;> assumption)
end

