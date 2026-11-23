module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansion
section
noncomputable section

open MvPolynomial Finset Equiv

namespace GlobalTheory.JSW

def antisymHExt {A : Type*} [CommRing A] (h : ℕ → A) (z : ℤ) : A :=
  if z < 0 then 0 else h z.toNat

def antisymMat {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (ν : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) A :=
  Matrix.of fun i j => antisymHExt h ((ν j : ℤ) - staircase m i)

theorem alternant_eq_sum_perm {A : Type*} [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = ∑ σ : Perm (Fin m),
      ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) * ∏ i, X i ^ μ (σ i) := by
  rw [alternant, Matrix.det_apply']
  simp [Matrix.of_apply]

theorem antisym_shift_sum {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) (μ : Fin m → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, μ i),
        (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  classical
  set F : (Fin m → ℕ) → MvPolynomial (Fin m) A :=
    fun ν => (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, X j ^ ν j with hF
  have key : ∀ k : Fin m → ℕ, (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
      ∏ j, C (h (k j)) * X j ^ (k j) = F (k + μ) := by
    intro k
    simp only [hF]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e : (((k + μ) j : ℕ) : ℤ) - μ j = k j := by simp
    rw [e, antisymHExt, if_neg (not_lt.2 (Int.natCast_nonneg _)), Int.toNat_natCast, Pi.add_apply, pow_add]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => key k]
  rw [← Finset.sum_image (g := fun k => k + μ) (by intro a _ b _ hab; exact add_right_cancel hab)]
  apply Finset.sum_subset
  · intro ν hν
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hν
    rw [Finset.Nat.mem_antidiagonalTuple] at hk ⊢
    simp [Finset.sum_add_distrib, hk]
  · intro ν hν hnot
    by_cases hle : ∀ j, μ j ≤ ν j
    · exfalso
      apply hnot
      refine Finset.mem_image.2 ⟨ν - μ, ?_, ?_⟩
      · rw [Finset.Nat.mem_antidiagonalTuple] at hν ⊢
        have : ∑ i, (ν - μ) i + ∑ i, μ i = ∑ i, ν i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        omega
      · funext j
        simp [Nat.sub_add_cancel (hle j)]
    · push_neg at hle
      obtain ⟨j, hj⟩ := hle
      simp only [hF]
      rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]
      rw [antisymHExt, if_pos (by omega), map_zero]

theorem antisym_lhs_eq {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  rw [alternant_eq_sum_perm, Finset.sum_mul]
  have hσ : ∀ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
      (∏ i, X i ^ staircase m (σ i)) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        (((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
          ∏ j, C (antisymHExt h ((ν j : ℤ) - staircase m (σ j)))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
    intro σ
    rw [mul_assoc, antisym_shift_sum m d h (fun i => staircase m (σ i)),
      Equiv.sum_comp σ (staircase m), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, Matrix.det_apply', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  rfl

theorem antisymMat_comp_perm {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (μ : Fin m → ℕ)
    (τ : Perm (Fin m)) :
    (antisymMat m h (fun i => μ (τ i))).det = (Perm.sign τ : ℤ) * (antisymMat m h μ).det := by
  rw [← Matrix.det_permute']
  rfl

theorem antisymMat_staircase {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) :
    (antisymMat m h (fun i => l i + staircase m i)).det = jtDet m h l := by
  rw [jtDet, ← Matrix.det_transpose]
  congr 1
  ext i j
  have hi := i.2
  have hj := j.2
  have e : (((l i + staircase m i : ℕ)) : ℤ) - (staircase m j : ℕ) = (l i : ℤ) - i + j := by
    simp only [staircase]
    omega
  simp only [antisymMat, Matrix.of_apply, Matrix.transpose_apply, antisymHExt]
  rw [e]

theorem antisym_strictAnti {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) :
    StrictAnti (fun i => l i + staircase m i) := by
  intro i j hij
  have h1 := hl hij.le
  have h2 : (i : ℕ) < j := hij
  have := j.2
  simp only [staircase]
  omega

theorem antisym_gap {m : ℕ} {s : Fin m → ℕ} (hs : StrictAnti s) :
    ∀ (k : ℕ) (i j : Fin m), (j : ℕ) = i + k → s j + k ≤ s i := by
  first
  | exact @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | (apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti ..)


open Classical in
theorem antisym_sum_sort {M : Type*} [AddCommMonoid M] (m d : ℕ) (g : (Fin m → ℕ) → M) :
    ∑ l ∈ antiParts m d, ∑ τ : Perm (Fin m), g (fun i => l (τ i) + staircase m (τ i)) =
      ∑ ν ∈ (Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i)).filter Function.Injective, g ν := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i) + staircase m (p.2 i)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    rw [mem_antiParts] at hl
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨?_, ?_⟩
    · rw [Equiv.sum_comp p.2 (fun i => p.1 i + staircase m i), Finset.sum_add_distrib, hl.1]
    · exact (antisym_strictAnti hl.2).injective.comp p.2.injective
  · intro p hp q hq hpq
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    obtain ⟨hl', -⟩ := Finset.mem_product.1 hq
    rw [mem_antiParts] at hl hl'
    set ν : Fin m → ℕ := fun i => p.1 (p.2 i) + staircase m (p.2 i) with hν
    have hν' : ν = fun i => q.1 (q.2 i) + staircase m (q.2 i) := hpq
    have a1 : Antitone (ν ∘ p.2.symm) := by
      have : ν ∘ p.2.symm = fun i => p.1 i + staircase m i := by funext i; simp [hν]
      rw [this]; exact (antisym_strictAnti hl.2).antitone
    have a2 : Antitone (ν ∘ q.2.symm) := by
      have : ν ∘ q.2.symm = fun i => q.1 i + staircase m i := by funext i; simp [hν']
      rw [this]; exact (antisym_strictAnti hl'.2).antitone
    have u := Tuple.unique_antitone a1 a2
    have hinj : Function.Injective ν := (antisym_strictAnti hl.2).injective.comp p.2.injective
    have hperm : p.2.symm = q.2.symm := Equiv.ext fun i => hinj (congrFun u i)
    have h2 : p.2 = q.2 := by simpa using congrArg Equiv.symm hperm
    have h1 : p.1 = q.1 := by
      funext i
      have := congrFun hν' (p.2.symm i)
      simp only [hν, h2, Equiv.apply_symm_apply] at this
      omega
    exact Prod.ext h1 h2
  · intro ν hν
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hν
    obtain ⟨hsum, hinj⟩ := hν
    set σ := Tuple.sort (fun i => OrderDual.toDual (ν i)) with hσ
    have hanti : Antitone (ν ∘ σ) := by
      have := Tuple.monotone_sort (fun i => OrderDual.toDual (ν i))
      exact monotone_toDual_comp_iff.1 this
    have hs : StrictAnti (ν ∘ σ) := hanti.strictAnti_of_injective (hinj.comp σ.injective)
    have hδ : ∀ i, staircase m i ≤ ν (σ i) := by
      intro i
      have hm : m - 1 < m := by have := i.2; omega
      have := antisym_gap hs (m - 1 - i) i ⟨m - 1, hm⟩ (by simp; have := i.2; omega)
      simp only [staircase, Function.comp] at this ⊢
      omega
    refine ⟨(fun i => ν (σ i) - staircase m i, σ.symm), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
      rw [mem_antiParts]
      refine ⟨?_, ?_⟩
      · show ∑ i, (ν (σ i) - staircase m i) = d
        have e : ∑ i, (ν (σ i) - staircase m i) + ∑ i, staircase m i = ∑ i, ν (σ i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hδ i)
        rw [Equiv.sum_comp σ ν] at e
        omega
      · intro i j hij
        have g := antisym_gap hs (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)
        have h1 := hδ i
        have h2 := hδ j
        simp only [staircase, Function.comp] at g h1 h2 ⊢
        have := j.2
        have : (i : ℕ) ≤ j := hij
        omega
    · funext i
      have := hδ (σ.symm i)
      simp only [Equiv.apply_symm_apply] at this ⊢
      omega
  · intro p _
    rfl

theorem alternant_staircase_mul_antidiagonal {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts m d,
        MvPolynomial.C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) := by
  classical
  rw [antisym_lhs_eq]
  have hr : ∀ l : Fin m → ℕ, C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) =
      ∑ τ : Perm (Fin m), (fun ν : Fin m → ℕ =>
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)
        (fun i => l (τ i) + staircase m (τ i)) := by
    intro l
    rw [alternant_eq_sum_perm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e := antisymMat_comp_perm m h (fun i => l i + staircase m i) τ
    simp only at e ⊢
    rw [e, antisymMat_staircase, map_mul, map_intCast]
    ring
  rw [Finset.sum_congr rfl fun l _ => hr l, antisym_sum_sort m d
    (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)]
  symm
  apply Finset.sum_filter_of_ne
  intro ν _ hne
  by_contra hni
  apply hne
  obtain ⟨a, b, hab, hne'⟩ : ∃ a b, ν a = ν b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, hab, hne⟩
  rw [Matrix.det_zero_of_column_eq hne' (fun k => by simp [antisymMat, hab]), map_zero, zero_mul]

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalIntegerSpanOfImageIsStableLatticeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.latY_lattice | exact GlobalTheory.Pass.LocDual.OneX.latY_lattice | (intros; apply GlobalTheory.Pass.LocDual.OneX.latY_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansionStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | exact GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachOfFrobeniusGammaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wach_of_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.CocycleInj.main | exact GlobalTheory.NL.CocycleInj.main | (intros; apply GlobalTheory.NL.CocycleInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSub
section
noncomputable section

open Finset PowerSeries

namespace GlobalTheory.JSW

theorem sum_finsuppAntidiag_univ_fin {M : Type*} [AddCommMonoid M] {m : ℕ} (d : ℕ)
    (F : (Fin m → ℕ) → M) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin m)) d, F l =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, F k := by
  refine Finset.sum_equiv Finsupp.equivFunOnFinite ?_ ?_
  · intro l
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro l _
    rfl

theorem coeff_prod_mk_fin {m : ℕ} (f : Fin m → ℕ → ℂ) (d : ℕ) :
    coeff d (∏ j, PowerSeries.mk (f j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, f j (k j) := by
  rw [coeff_prod, sum_finsuppAntidiag_univ_fin d (fun k => ∏ j, coeff (k j) (PowerSeries.mk (f j)))]
  simp only [coeff_mk]

theorem prod_map_X_eq_monomial_toFinsupp {n : ℕ} (s : Multiset (Fin n)) :
    (s.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem sum_toFinsupp_fin {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  simp [Multiset.toFinsupp_apply, Multiset.sum_count_eq_card]

theorem hsymm_fin_eq_sum_monomial {n : ℕ} (k : ℕ) :
    MvPolynomial.hsymm (Fin n) ℤ k =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  refine Finset.sum_bij (fun s _ => Multiset.toFinsupp s.1) ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [sum_toFinsupp_fin, s.2]
  · intro a _ b _ h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    refine ⟨⟨Finsupp.toMultiset l, ?_⟩, mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hl.1
    · simp
  · intro s _
    exact prod_map_X_eq_monomial_toFinsupp s.1

theorem eval₂_hsymm_fin {n : ℕ} (α : Fin n → ℂ) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ k) =
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, α i ^ l i := by
  rw [hsymm_fin_eq_sum_monomial, MvPolynomial.eval₂_sum,
    ← sum_finsuppAntidiag_univ_fin k (fun l => ∏ i, α i ^ l i)]
  refine sum_congr rfl fun l _ => ?_
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem one_sub_C_mul_X_mul_mk_pow (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, mul_comm]

theorem mk_hsymm_mul_prod_one_sub {n : ℕ} (α : Fin n → ℂ) (u : ℂ) :
    PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) *
      ∏ i, (1 - PowerSeries.C (α i * u) * PowerSeries.X) = 1 := by
  have h : PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) =
      ∏ i, PowerSeries.mk (fun k => (α i * u) ^ k) := by
    ext k
    rw [coeff_prod_mk_fin, coeff_mk, eval₂_hsymm_fin, sum_mul]
    refine sum_congr rfl fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hl]
  rw [h, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm]; exact one_sub_C_mul_X_mul_mk_pow _

theorem mk_sum_prod_hsymm_mul_prod_one_sub : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  intro m n α β T
  have h1 : PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) =
      ∏ j, PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * (β j * T) ^ k) := by
    ext d
    rw [coeff_mk, coeff_prod_mk_fin, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    simp_rw [mul_pow, ← mul_assoc, prod_mul_distrib, prod_pow_eq_pow_sum, hk]
    ring
  have h2 : ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) =
      ∏ j, ∏ i, (1 - PowerSeries.C (α i * (β j * T)) * PowerSeries.X) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [mul_assoc]
  rw [h1, h2, ← prod_mul_distrib]
  exact prod_eq_one fun j _ => mk_hsymm_mul_prod_one_sub α (β j * T)

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem modStep_holds : ModStep := by
  intro l _ P AI T n _ _ K r ρ w x y hxy hR hF hS
  choose U hU hUe using hF
  obtain ⟨hfield, -, -, -, hval, hmul, -⟩ := _root_.GlobalTheory.PMon.bdR_tied l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  have hsum : ∀ (s : Finset n) (f : n → P.R.BdR), (∀ k ∈ s, f k ∈ Fil P 1) → ∑ k ∈ s, f k ∈ Fil P 1 := by
    intro s f hf
    unfold Fil at *
    exact sum_mem hf
  have h1 : (1 : P.R.BdR) ∉ Fil P 1 := by
    intro h
    obtain ⟨a, ha, ha'⟩ := hval 1 one_ne_zero
    exact ha' (by simpa using hmul a 1 1 1 ha h)
  have hcol : ∃ i, (U x.1 : Matrix n n P.R.BdR) i x.2 ∉ Fil P 1 := by
    by_contra hc
    push_neg at hc
    have hinv : (((U x.1)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * (U x.1 : Matrix n n P.R.BdR) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he := congrFun (congrFun hinv x.2) x.2
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at he
    apply h1
    rw [← he]
    apply hsum
    intro k _
    simpa using hmul 0 1 _ _ ((hU x.1).2 x.2 k) (hc k)
  have heig : ∀ g : ↥(GK K), (matD P ρ (x.1 : ℕ) g).mulVec
      (fun i => P.actQdR (g : GQ l) ((U x.1 : Matrix n n P.R.BdR) i x.2)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w x.1 x.2 : ℚ_[l]ˣ) : ℚ_[l]) •
        (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) := by
    intro g
    funext i
    have h := congrFun (congrFun (hUe x.1 g) i) x.2
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simp only [Matrix.map_apply] at h
    rw [Matrix.mulVec, dotProduct, h, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hind := _root_.GlobalTheory.PMon.residue_indep_of_not_splits l P AI T n K r ρ (x.1 : ℕ) (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) (w x.1 x.2)
    hR hS (fun i => (hU x.1).1 i x.2) hcol heig
  obtain ⟨A, hA, hW⟩ := _root_.GlobalTheory.PMon.flAt_all r l P AI T n U x y hxy (fun m => hU m) hind
  exact _root_.GlobalTheory.PMon.exists_rep_of_fixed_frame_change l P AI T n K r ρ w (fun m j => eps x y (m, j)) U A hR hUe hA hW

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDiscPeriodBasisIsUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_disc_period_basis_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BKLim.wseed_Z_isUnit | exact GlobalTheory.BKLim.wseed_Z_isUnit | (intros; apply GlobalTheory.BKLim.wseed_Z_isUnit; all_goals assumption)
end

