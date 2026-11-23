module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltedSeriesRowSubUntiltTruncatedAdditiveRow
section
noncomputable section

open Formalism.Per GlobalTheory.PSer Finset
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem row_lam_sub_untilt_rowT : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CharP F l]
    [PerfectRing F l] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (h : ℕ) (m x : Fin h → Fl l) (ϖ : F) (K : ℕ) (τ : Fin h → ℝ) (r : Fin h), 1 ≤ h → tsh ϖ = l →
      (∀ j, ‖sh (x j)‖ < 1) →
      (∀ (j : Fin h) (n : ℤ), ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r ∧
        ((K : ℤ) < |n| → ‖GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n‖ ≤ τ r / l)) →
      ‖∑ j, sh (m j) * lam h r (x j) - tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
  intro l _ F _ _ _ _ ι tsh hn hs hsurj h m x ϖ K τ r hh hϖ hx hT
  have hid : ∀ j n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) =
      sh (m j) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((r : ℕ) : ℤ)) (x j))) := by
    intro j n
    simp only [GlobalTheory.PMonE.term, map_mul, map_zpow₀, hϖ, hs]
    rw [← _root_.GlobalTheory.PSer.map_pw_eq_pw l F ι, hs]
    rw [show ((r : ℤ) + n * h) = n * h + ((r : ℕ) : ℤ) by push_cast; ring]
    ring
  have hR : 0 ≤ τ r := (norm_nonneg _).trans (hT r 0).1
  have hR' : 0 ≤ ‖(l : ℂ_[l])‖ * τ r := mul_nonneg (norm_nonneg _) hR
  have hlb : τ r / l = ‖(l : ℂ_[l])‖ * τ r := by rw [Laws.norm_l, div_eq_inv_mul]
  have htail : ∀ j, ‖sh (m j) * lam h r (x j) -
      ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)‖
        ≤ ‖(l : ℂ_[l])‖ * τ r := by
    intro j
    have hsum : Summable (fun n => tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) := by
      simp only [hid]; exact (Laws.summable_lam hh r (hx j)).mul_left _
    have hlam : sh (m j) * lam h r (x j) =
        ∑' n, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) := by
      simp only [hid, lam]; rw [tsum_mul_left]
    rw [hlam, ← hsum.sum_add_tsum_compl (s := Icc (-(K : ℤ)) K), add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hR' fun ⟨n, hmem⟩ => ?_
    rw [← hlb]
    show ‖tsh _‖ ≤ _
    rw [hn]
    apply (hT j n).2
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hmem
    rw [lt_abs]; omega
  have hfin : ‖∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
      tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r)‖ ≤ ‖(l : ℂ_[l])‖ * τ r := by
    have := _root_.GlobalTheory.untilt_ext_sum_sub_le l F ι tsh hn hs hsurj (Fin h × ℤ) (univ ×ˢ Icc (-(K : ℤ)) K)
      (fun a => GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r a.1 a.2) (τ r) hR
      (fun a _ => (hT a.1 a.2).1)
    simp only [Finset.sum_product] at this
    rw [norm_sub_rev]
    simpa [GlobalTheory.PMonE.rowT] using this
  calc _ = ‖∑ j, (sh (m j) * lam h r (x j) -
        ∑ n ∈ Icc (-(K : ℤ)) K, tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n)) +
      (∑ j, ∑ n ∈ Icc (-(K : ℤ)) K,
        tsh (GlobalTheory.PMonE.term l ϖ (fun j => ι (m j)) (fun j => ι (x j)) r j n) -
        tsh (GlobalTheory.PMonE.rowT l ϖ (fun j => ι (m j)) K (fun j => ι (x j)) r))‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR' fun j _ => htail j) hfin

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}

theorem smul_top_ideal (J : Ideal A) : (J • ⊤ : Submodule A A) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem sub_mem_iff (J : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD ((J ^ n • ⊤ : Submodule A A))] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_top_ideal]

theorem eq_zero_of_c (TB : TopBasis s I ι) (x : A) (h : ∀ i, TB.c i x = 0) : x = 0 := by
  have hH : IsHausdorff (I.map s) A := TB.complete.toIsHausdorff
  refine hH.haus x fun n => ?_
  rw [sub_mem_iff, ← Ideal.map_pow]
  have := TB.approx x n ∅ (fun i _ => by rw [h i]; exact zero_mem _)
  simpa using this

theorem c_s (TB : TopBasis s I ι) (i : ι) (a : S) (x : A) : TB.c i (x * s a) = a * TB.c i x := by
  rw [mul_comm]; exact TB.c_mul i a x

theorem coeff_unitIndex_baseMap (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have := TB.c_mul TB.i₀ a (TB.b TB.i₀)
  rw [TB.b_i₀, mul_one, ← TB.b_i₀, TB.c_self, mul_one] at this
  exact this

theorem injective (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  rw [← coeff_unitIndex_baseMap TB a, h, coeff_unitIndex_baseMap]

theorem c_mem_of_mem_map (TB : TopBasis s I ι) (L : Ideal S) (x : A) (hx : x ∈ L.map s) (i : ι) :
    TB.c i x ∈ L := by
  let J : Ideal A :=
    { carrier := {y | ∀ a : A, ∀ i, TB.c i (a * y) ∈ L}
      add_mem' := fun {y z} hy hz a i => by rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a i) (hz a i)
      zero_mem' := fun a i => by rw [mul_zero, map_zero]; exact L.zero_mem
      smul_mem' := fun b y hy a i => by rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b) i }
  have hle : L.map s ≤ J := Ideal.map_le_iff_le_comap.2 fun y hy a i => by
    show TB.c i (a * s y) ∈ L
    rw [c_s]; exact L.mul_mem_right _ hy
  have := hle hx 1 i
  rwa [one_mul] at this

theorem mem_map_iff (TB : TopBasis s I ι) (L : Ideal S) (n : ℕ) (hL : I ^ n ≤ L) (x : A) :
    x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L := by
  refine ⟨fun hx i => c_mem_of_mem_map TB L x hx i, fun h => ?_⟩
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by
    simpa using hi
  have h1 := Ideal.map_mono (f := s) hL (TB.approx x n _ hF)
  have h2 : ∑ i ∈ (TB.fin x n).toFinset, s (TB.c i x) * TB.b i ∈ L.map s :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (h i))
  simpa using Ideal.add_mem _ h1 h2

open Classical in
theorem c_sum (TB : TopBasis s I ι) (z : ι → S) (F : Finset ι) (i : ι) :
    TB.c i (∑ j ∈ F, s (z j) * TB.b j) = if i ∈ F then z i else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [TB.c_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by rw [TB.c_ne i j (Ne.symm hj), mul_zero])
      (fun h => (h hi).elim), TB.c_self, mul_one]
  · exact Finset.sum_eq_zero fun j hj => by
      rw [TB.c_ne i j (fun e => hi (e ▸ hj)), mul_zero]

theorem exists_c_eq (TB : TopBasis s I ι) (hS : IsHausdorff I S) (z : ι → S)
    (hz : ∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) : ∃ x, ∀ i, TB.c i x = z i := by
  classical
  let F : ℕ → Finset ι := fun n => (hz n).toFinset
  have hFm : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  have hFc : ∀ n i, i ∉ F n → z i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  let f : ℕ → A := fun n => ∑ i ∈ F n, s (z i) * TB.b i
  have hP : IsPrecomplete (I.map s) A := TB.complete.toIsPrecomplete
  obtain ⟨x, hx⟩ := hP.prec' f (fun {m n} hmn => by
    rw [sub_mem_iff, ← Ideal.map_pow, ← neg_mem_iff, neg_sub]
    show (∑ i ∈ F n, s (z i) * TB.b i) - ∑ i ∈ F m, s (z i) * TB.b i ∈ _
    rw [← Finset.sum_sdiff (hFm hmn), add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem s (hFc m i (Finset.mem_sdiff.1 hi).2)))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_top_ideal]
  have h1 : TB.c i (f n - x) ∈ I ^ n := by
    have := (sub_mem_iff _ n _ _).1 (hx n)
    rw [← Ideal.map_pow] at this
    exact c_mem_of_mem_map TB _ _ this i
  have h2 : TB.c i (f n) - z i ∈ I ^ n := by
    show TB.c i (∑ j ∈ F n, s (z j) * TB.b j) - z i ∈ I ^ n
    rw [c_sum]
    split_ifs with hi
    · rw [sub_self]; exact zero_mem _
    · rw [zero_sub, neg_mem_iff]; exact hFc n i hi
  have := Ideal.sub_mem _ h2 h1
  rw [map_sub] at this
  simpa using this

theorem map_nonZeroDivisors (TB : TopBasis s I ι) (a : S) (ha : a ∈ nonZeroDivisors S) :
    s a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => eq_zero_of_c TB x fun i => ?_, fun x hx => eq_zero_of_c TB x fun i => ?_⟩
  · have := congrArg (TB.c i) hx
    rw [TB.c_mul, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)
  · have := congrArg (TB.c i) hx
    rw [c_s, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  intro S A _ _ s I ι TB hS
  exact ⟨TB.eq_zero_of_c, TB.injective, TB.mem_map_iff, TB.exists_c_eq hS, TB.map_nonZeroDivisors⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem rootT_pow_eq_untilt (e : Per.Fl l) (n : ℕ) : rootT e n ^ (l ^ n) = e.untilt := by
  induction n generalizing e with
  | zero => simp [rootT]
  | succ n ih =>
    have h : rootT e (n + 1) = rootT ((frobeniusEquiv (Per.Fl l) l).symm e) n := by
      rw [rootT, rootT, Function.iterate_succ_apply]
    rw [h, pow_succ, pow_mul, ih, ← map_pow, frobeniusEquiv_symm_pow_p]

end GlobalTheory.MemLoc

namespace GlobalTheory.BSP

theorem rootT_flat_alg_and_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  intro l _ K bk
  refine ⟨fun n => ?_, fun g y hy => ?_⟩
  · set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
    have h1 : (GlobalTheory.MemLoc.rootT bk.flat n) ^ (l ^ n) = intToOC K r := by
      rw [GlobalTheory.MemLoc.rootT_pow_eq_untilt, ← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
      exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
    set a : Om l := ((r : ↥K.1) : Om l)
    have hf : (Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos n) a
    have hroot : ((Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot
        ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) := by
      have h2 := congrArg (fun x : OC l => (x : ℂ_[l])) h1
      rw [SubmonoidClass.coe_pow] at h2
      rw [coe_intToOC] at h2
      simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [h2]
      exact sub_self _
    obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
    exact ⟨z, hz.symm⟩
  · refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g bk.flat) = PreTilt.coeff n y
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g bk.flat) =
        Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => exact Eq.refl (Per.σF g bk.flat)
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : GlobalTheory.MemLoc.rootT (Per.σF g bk.flat) n = Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) := by
      rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, hit, GlobalTheory.RingBasics.untilt_σF]
    rw [GlobalTheory.MemLoc.coeff_eq_mk_rootT, GlobalTheory.MemLoc.coeff_eq_mk_rootT, hsig, hy n]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariant
section
noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

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

theorem tmul_basis_inj {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (e₀ : M) (hs : Submodule.span O {e₀} = ⊤) (hi : ∀ c : O, c • e₀ = 0 → c = 0)
    {r r' : R} (h : r ⊗ₜ[O] e₀ = r' ⊗ₜ[O] e₀) : r = r' := by
  have hb : Function.Bijective (LinearMap.toSpanSingleton O M e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => hi c (by simpa using hc), fun x => ?_⟩
    have hx : x ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨c, by simpa using hc⟩
  let f := LinearEquiv.ofBijective _ hb
  have h1 : f.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [f]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R f.symm.toLinearMap z)) h
  simpa [h1] using this

theorem ioLaws_of_injective (E : EtTie W RA RW inclR φR gR πA)
    (hO : Function.Injective (algebraMap O LL)) : IoLaws E := by
  obtain ⟨e, e₀, hs, hj, -⟩ := E.one_e
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hT⟩ := W.one_line
    have hm : u ∈ W.one.L.T := hT ▸ Submodule.mem_span_singleton_self u
    have hx : (⟨u, hm⟩ : ↥W.one.L.T) ∈ Submodule.span O {e₀} := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact hu this.symm
  have hi : ∀ c : O, c • e₀ = 0 → c = 0 := by
    intro c hc
    have h1 : algebraMap O LL c • (e₀ : W.one.V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val hc
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hO (by rw [h2, map_zero])
    · exact absurd h2 h0
  have hx : ∀ x : W.EE, E.jD W.one (x • e) = E.ioE x ⊗ₜ[O] e₀ := by
    intro x
    rw [E.jD_smul, hj, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hact : ∀ g : G, W.one.actT g e₀ = e₀ := fun g => Subtype.ext (W.one_triv g _)
  have hφ : W.φD W.one e = e := by
    apply E.jD_inj
    rw [E.jD_φ, hj]
    simp [TWmap]
  have hγ : ∀ g : G, W.γD W.one (W.resΓ g) e = e := by
    intro g
    apply E.jD_inj
    rw [E.jD_act, hj]
    simp [TWact, hact]
  refine ⟨fun x => ?_, fun g x => ?_⟩
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_φ W.one (x • e)
    rw [W.φD_smul, hφ, hx, hx] at this
    simpa [TWmap] using this
  · apply tmul_basis_inj e₀ hs hi
    have := E.jD_act W.one g (x • e)
    rw [W.γD_smul, hγ, hx, hx] at this
    simpa [TWact, hact] using this

end Generic

theorem ioLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  intro D HW F l _ K s LL h
  exact ioLaws_of_injective _ Subtype.val_injective

end GlobalTheory.NL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Expansion

open PowerSeries GlobalTheory.HWL.Ser

section Generic

variable {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] {v : AddValuation L (WithTop ℚ)}
  {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR}
    [Algebra Qp L] [TopologicalSpace L] {n : ℕ}

noncomputable def evOne (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
  (W.lev i ζ).comp (Pi.constAlgHom O (ZMod n) O⟦X⟧)


omit [CharZero L] [Algebra ℚ L] in
theorem lev_eq (W : LocWach PD L O v n) (i : ZMod n) (ζ : L) (a : LetA O n) :
    W.lev i ζ a = evOne W i ζ (a i) := by
  have h := W.lev_letter i ζ (a - fun _ => a i) (by simp)
  rw [map_sub, sub_eq_zero] at h
  exact h

theorem evOne_X (W : LocWach PD L O v n) (i : ZMod n) {ζ : L} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    evOne W i ζ X = C ζ * exp L - 1 := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ h
  have hE : E = exp L := ode_unique 1 (by rw [h1, map_one, one_mul])
    (by rw [derivative_exp, map_one, one_mul]) (by rw [h0, constantCoeff_exp])
  rw [← hE, ← h2, lev_eq, add_sub_cancel_left]
  rfl

theorem levLaws_of_evLaw (W : LocWach PD L O v n) (hp : PD.p = l) (c : W.Gam → ℤ_[l])
    (hc : ∀ g, algebraMap ℤ_[l] O (c g) = (W.χΓ g : O)) (hφ : W.φ₀ = GlobalTheory.Cyc.phi l O)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (c g))
    (hv : ∀ (c : ℤ_[l]) (j a : ℕ), (j : WithTop ℚ) ≤ v (algebraMap ℤ_[l] L c - (a : L)) →
      (l : ℤ_[l]) ^ j ∣ c - a) (H : EvLaw l (O := O) v inferInstance) : LevLaws W := by
  have hc' : ∀ g, algebraMap O L (W.χΓ g : O) = algebraMap ℤ_[l] L (c g) :=
    fun g => by rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hpr : PD.p.Prime := hp ▸ (Fact.out : l.Prime)
  constructor
  · rintro g i ζ _ j a h hj rfl f
    rw [hc'] at hj ⊢
    have e : W.γA g f i = GlobalTheory.Fon.gam O (c g) (f i) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← hγ]; rfl
    rw [lev_eq, lev_eq, e]
    exact ev_gam H (hp ▸ h.pow_eq_one) _ (hv _ j a hj) (evOne_X W i ⟨j, h⟩)
      (evOne_X W i (root_pow hpr ⟨j, h⟩ a)) (f i)
  · rintro i ζ ⟨j, h⟩ f
    have e : W.φA f i = GlobalTheory.Fon.gam O (l : ℤ_[l]) (f (i - 1)) := by
      rw [← GlobalTheory.Cyc.Series.act_eq, ← GlobalTheory.Cyc.phi, ← hφ]; rfl
    have := ev_gam H (j := j) (hp ▸ h.pow_eq_one) (l : ℤ_[l]) (a := l) (by simp) (evOne_X W i ⟨j, h⟩)
      (evOne_X W (i - 1) (root_pow hpr ⟨j, h⟩ l)) (f (i - 1))
    rw [map_natCast] at this
    rw [lev_eq, lev_eq, e, hp]
    exact this

end Generic

theorem levLaws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  intro D HW l _ K s LL h W
  obtain ⟨χ, h1⟩ := exists_padic_char (LL := LL) (gamOf W ((HW l).W_s K s LL h))
  obtain ⟨_, hcomp, -, hu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hl : (l : ↥(OL LL)) ≠ 0 := fun h0 => by
    have h2 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  have key := fun g : W.Gam => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl hu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l])
    (by rw [W.φ₀_X, W.q₀_def, (D.loc l).PD_p K]) (W.γ₀_comm g) (W.γ₀_X g).1 ((W.γ₀_X g).2.trans (h1 g).symm)
  refine levLaws_of_evLaw W ((D.loc l).PD_p K) (fun g => χ g) h1 (key 1).1 (fun g => (key g).2) (dvd_of_le_v (D.loc l)) ?_
  convert evLaw_integers (D.loc l) LL using 1
  exact Algebra.algebra_ext _ _ fun r => PowerSeries.algebraMap_apply

end GlobalTheory.NL.Expansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlLattice_of_coefficientLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ),
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T := by
  first | exact @GlobalTheory.latticeZl_of_latticeO | exact GlobalTheory.latticeZl_of_latticeO | (intros; apply GlobalTheory.latticeZl_of_latticeO <;> assumption)
end

