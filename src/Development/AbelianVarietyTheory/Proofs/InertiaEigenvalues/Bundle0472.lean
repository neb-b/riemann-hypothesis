module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfRootsContainLthRootsConjugates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.ExpandCoeff

open Polynomial

theorem coeff_eq_zero_of_roots : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := by
  intro l hl a _ E hE hirr z hz hroot i hi
  have hl0 : 0 < l := hl.out.pos
  set K := ↥(Kunr l a)
  have hzi : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  set m := minpoly K z with hm
  set φ := algebraMap K (Om l)
  set EK := E.map (GlobalTheory.TameFrob.iota l a) with hEKdef
  set Q := E.map (GlobalTheory.TameFrob.iotaO l a) with hQdef
  have hcomp : φ.comp (GlobalTheory.TameFrob.iota l a) = GlobalTheory.TameFrob.iotaO l a := RingHom.ext fun w => rfl
  have hmapQ : EK.map φ = Q := by rw [hEKdef, Polynomial.map_map, hcomp]
  have hev : ∀ y : Om l, Polynomial.aeval y EK = Q.eval y := fun y => by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapQ]
  obtain ⟨y0, hy0⟩ := IsAlgClosed.exists_pow_nat_eq z hl0
  have hQ0 : Q.IsRoot y0 := hroot z (minpoly.aeval K z) y0 hy0
  have hEK : EK.Monic := hE.map _
  have hEKmin : EK = minpoly K y0 := minpoly.eq_of_irreducible_of_monic hirr (by rw [hev]; exact hQ0) hEK
  set P := Polynomial.expand K l m with hPdef
  have hPmon : P.Monic := (minpoly.monic hzi).expand hl0
  have hPy0 : Polynomial.aeval y0 P = 0 := by
    rw [hPdef, Polynomial.expand_aeval, hy0, minpoly.aeval]
  have hdvd : EK ∣ P := hEKmin ▸ minpoly.dvd K y0 hPy0

  have hmsep : m.Separable := Algebra.IsSeparable.isSeparable K z
  have hc0 : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hzi hz
  have hPsep : P.Separable := by
    unfold Polynomial.Separable
    rw [Polynomial.derivative_expand]
    have h1 : IsCoprime P (Polynomial.expand K l (Polynomial.derivative m)) :=
      IsCoprime.map hmsep (Polynomial.expand K l).toRingHom
    have h2 : IsCoprime P (Polynomial.X ^ (l - 1)) := by
      refine IsCoprime.pow_right ?_
      refine IsCoprime.symm ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_)
      rw [Polynomial.X_dvd_iff, hPdef, Polynomial.coeff_expand hl0, if_pos (dvd_zero l), Nat.zero_div]
      exact hc0
    have h3 : IsCoprime P ((l : K[X])) := by
      have hu : IsUnit ((l : K[X])) := by
        rw [← Polynomial.C_eq_natCast]
        exact Polynomial.isUnit_C.2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      exact ⟨0, ↑(hu.unit⁻¹), by rw [zero_mul, zero_add, IsUnit.val_inv_mul]⟩
    exact h1.mul_right (h3.mul_right h2)
  set P' := P.map φ with hP'def
  have hP'sep : P'.Separable := hPsep.map
  have hP'0 : P' ≠ 0 := (hPmon.map φ).ne_zero
  have hQne : Q ≠ 0 := (hE.map _).ne_zero
  have hnod : P'.roots.Nodup := Polynomial.nodup_roots hP'sep
  have hcard : Multiset.card P'.roots = P'.natDegree :=
    (Polynomial.splits_iff_card_roots).1 (IsAlgClosed.splits P')
  have hle : P'.roots ≤ Q.roots := by
    refine (Multiset.le_iff_subset hnod).2 fun y hy => ?_
    rw [Polynomial.mem_roots hP'0, Polynomial.IsRoot, hP'def, Polynomial.eval_map, ← Polynomial.aeval_def,
      hPdef, Polynomial.expand_aeval] at hy
    exact (Polynomial.mem_roots hQne).2 (hroot _ hy y rfl)
  have hdeg : P.natDegree ≤ EK.natDegree := by
    have e1 : P'.natDegree = P.natDegree := Polynomial.natDegree_map φ
    have e2 : EK.natDegree = Q.natDegree := by
      rw [hEKdef, hQdef, Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iota_injective l a),
        Polynomial.natDegree_map_eq_of_injective (GlobalTheory.TameFrob.iotaO_injective l a)]
    rw [← e1, e2, ← hcard]
    exact (Multiset.card_le_card hle).trans (Polynomial.card_roots' Q)
  have hEq : P = EK := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hEK hPmon hdvd hdeg
  have hci : GlobalTheory.TameFrob.iota l a (E.coeff i) = 0 := by
    rw [← Polynomial.coeff_map, ← hEKdef, ← hEq, hPdef, Polynomial.coeff_expand hl0, if_neg hi]
  exact GlobalTheory.TameFrob.iota_injective l a (hci.trans (map_zero _).symm)

end GlobalTheory.ExpandCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroNeZeroOfWittFrobeniusExpandDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem coeff_zero_ne_zero_of_expand_map_dvd {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 2 ≤ l)
    (σ : R →+* R) (P E : Polynomial R) (M : ℕ) (hP : P ≠ 0) (hE : E.coeff 0 ≠ 0)
    (h : Polynomial.expand R l (P.map σ) ∣ E ^ M * P) : P.coeff 0 ≠ 0 := by
  obtain ⟨P0, hP0, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  generalize Polynomial.rootMultiplicity 0 P = k at hP0
  simp only [map_zero, sub_zero] at hP0 hnd
  intro h0
  have hk : k ≠ 0 := by
    rintro rfl
    apply hnd
    rw [Polynomial.X_dvd_iff]
    simpa [hP0] using h0
  have h1 : (Polynomial.X : Polynomial R) ^ k * Polynomial.X ∣ Polynomial.expand R l (P.map σ) := by
    rw [hP0, Polynomial.map_mul, map_mul, Polynomial.map_pow, Polynomial.map_X, map_pow,
      Polynomial.expand_X, ← pow_mul, ← pow_succ]
    refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have h2 := h1.trans h
  have h3 : E ^ M * P = Polynomial.X ^ k * (E ^ M * P0) := by rw [hP0]; ring
  rw [h3, mul_dvd_mul_iff_left (pow_ne_zero _ Polynomial.X_ne_zero)] at h2
  rcases Polynomial.prime_X.dvd_or_dvd h2 with h4 | h4
  · exact hE (Polynomial.X_dvd_iff.mp (Polynomial.prime_X.dvd_of_dvd_pow h4))
  · exact hnd h4

theorem coeff_zero_ne_zero_of_frobenius_dvd_pow_mul :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := by
  intro l hl a _ P E M hP hE h
  exact coeff_zero_ne_zero_of_expand_map_dvd l hl.out.two_le _ P E M hP.ne_zero hE h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverse
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.TorsFree

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_le_one_of_mul {x g : K⟦X⟧} (hx : ∃ B : ℝ, ∀ n, ‖coeff n x‖ ≤ B)
    (hg : ∀ n, ‖coeff n g‖ ≤ 1) (hg1 : ∃ n, ‖coeff n g‖ = 1) (hgx : ∀ n, ‖coeff n (g * x)‖ ≤ 1) :
    ∀ n, ‖coeff n x‖ ≤ 1 := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hbdd : BddAbove (Set.range fun n => ‖coeff n x‖) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  set S := ⨆ n, ‖coeff n x‖ with hSdef
  have hxS : ∀ n, ‖coeff n x‖ ≤ S := fun n => le_ciSup hbdd n
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hxS 0)
  set d := Nat.find hg1 with hd
  have hgd : ‖coeff d g‖ = 1 := Nat.find_spec hg1
  have hlt : ∀ i < d, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne (hg i) (Nat.find_min hg1 hi)
  set θ : NNReal := (Finset.range d).sup fun i => ‖coeff i g‖₊ with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, Finset.sup_lt_iff (by simp)]
    intro i hi
    have := hlt i (Finset.mem_range.1 hi)
    rw [← NNReal.coe_lt_coe]; simpa using this
  have hθi : ∀ i < d, ‖coeff i g‖ ≤ (θ : ℝ) := fun i hi => by
    have : ‖coeff i g‖₊ ≤ θ := Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 hi)
    exact_mod_cast this
  have hθ0 : (0 : ℝ) ≤ θ := θ.2
  set Mx := max 1 ((θ : ℝ) * S) with hMx
  have hM0 : 0 ≤ Mx := le_trans zero_le_one (le_max_left _ _)
  have key : ∀ n, ‖coeff n x‖ ≤ Mx := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hmem : (d, n) ∈ Finset.HasAntidiagonal.antidiagonal (n + d) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact add_comm d n
    have hc := coeff_mul (n + d) g x
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x‖ ≤ Mx := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun p hp => ?_
      obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [norm_mul]
      rcases lt_trichotomy p.1 d with h | h | h
      · calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ θ * S :=
            mul_le_mul (hθi _ h) (hxS _) (norm_nonneg _) hθ0
          _ ≤ Mx := le_max_right _ _
      · exact absurd (Prod.ext h (by omega)) hne
      · have hj : p.2 < n := by omega
        calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ 1 * Mx :=
            mul_le_mul (hg _) (ih _ hj) (norm_nonneg _) zero_le_one
          _ = Mx := one_mul _
    have heq : coeff d g * coeff n x = coeff (n + d) (g * x) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x := by
      rw [hc]; ring
    have : ‖coeff n x‖ = ‖coeff d g * coeff n x‖ := by rw [norm_mul, hgd, one_mul]
    rw [this, heq, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hrest))
    exact (hgx _).trans (le_max_left _ _)
  have hSM : S ≤ Mx := ciSup_le key
  have hS1 : S ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : S ≤ θ * S := by
      rcases le_total 1 ((θ : ℝ) * S) with h3 | h3
      · rwa [hMx, max_eq_right h3] at hSM
      · rw [hMx, max_eq_left h3] at hSM; linarith
    have : (1 - (θ : ℝ)) * S ≤ 0 := by linarith
    have h4 : (0 : ℝ) < 1 - θ := by have := (NNReal.coe_lt_coe.2 hθ1); simp at this; linarith
    nlinarith
  exact fun n => (hxS n).trans hS1

end GlobalTheory.BK.TorsFree

namespace GlobalTheory.BK.Hom

open GlobalTheory.BK.TorsFree

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mem_imM_of_smul_mem (F : Hom P Q)
    (hg : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧
      Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧))
    (hl : ∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) {v : Vec K a κ} (hv : v ∈ Q.M) {f : K⟦X⟧}
    (hf0 : f ≠ 0) (hfv : f • v ∈ F.imM) : v ∈ F.imM := by
  unfold imM at hfv ⊢
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hfv
  rw [LinearMap.restrictScalars_apply] at hwv
  choose Y hYb hY using fun τ => (hl τ).2
  choose Y0 g hY0A hg1 hY0 using hg
  have hv' : ∀ τ i, v τ i ∈ A O K := fun τ => mem_tot.1 hv τ
  let x : Vec K a ι := fun τ => Y τ *ᵥ v τ
  have hfx : ∀ τ, f • x τ = w τ := by
    intro τ
    have h1 : f • v τ = F.mat τ *ᵥ w τ := by rw [← app_apply, hwv]; rfl
    change f • (Y τ *ᵥ v τ) = w τ
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, hY τ, one_smul, Matrix.one_mulVec]
  have hFx : F.app x = v := by
    funext τ i
    have h2 : f • F.app x τ = f • v τ := by
      rw [app_apply, ← Matrix.mulVec_smul, hfx τ, ← app_apply, hwv]; rfl
    exact mul_left_cancel₀ hf0 (congrFun h2 i)
  have hbx : ∀ τ i, ∃ B : ℝ, ∀ n, ‖coeff n (x τ i)‖ ≤ B := by
    intro τ i
    obtain ⟨c, hc⟩ := hYb τ
    refine ⟨max c 0, fun n => ?_⟩
    change ‖coeff n (∑ j, Y τ i j * v τ j)‖ ≤ max c 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun j _ => ?_
    have := norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (le_max_right c 0) zero_le_one (f := Y τ i j) (g := v τ j)
      (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _))
      (fun m => by rw [mul_one]; exact hv' τ j m) n
    rwa [mul_one, mul_one] at this
  have hgA : ∀ τ (i : ι), ∀ n, ‖coeff n (g τ)‖ ≤ 1 := by
    intro τ i
    have h5 : g τ = (Y0 τ * F.mat τ) i i := by rw [hY0 τ]; simp
    rw [h5]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (F.mem τ j i)
  have hgx : ∀ τ i, ∀ n, ‖coeff n (g τ * x τ i)‖ ≤ 1 := by
    intro τ i
    have h3 : g τ • x τ = Y0 τ *ᵥ v τ := by
      conv_rhs => rw [← hFx]
      rw [app_apply, Matrix.mulVec_mulVec, hY0 τ]
      first
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h4 : g τ * x τ i = (Y0 τ *ᵥ v τ) i := by rw [← h3]; rfl
    rw [h4]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (hv' τ j)
  have hxA : x ∈ P.M := mem_tot.2 fun τ i =>
    norm_coeff_le_one_of_mul (hbx τ i) (hgA τ i) (hg1 τ) (hgx τ i)
  exact Submodule.mem_map.2 ⟨x, hxA, by rw [LinearMap.restrictScalars_apply]; exact hFx⟩

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.coker_torsionFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hg hl v hv f _ hf0 hfv
  exact F.mem_imM_of_smul_mem hg hl hv hf0 hfv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.PotDual

def bundle {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_of_eq {k : ℕ} (M U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose) :
    IsDual1 PD (matRep M) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

end

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem continuous_loc {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL :=
    continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have hι : Continuous fun g : Br.G D.nbr i w hw => ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  exact (hM.comp hι).matrix_map hfc

theorem isDual1_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsDual1 ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) (dotProductBilin _ _) := by
  refine isDual1_of_eq _ _ _ fun g => ?_
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  have e : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
      ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥(D.nbr i w hw).LL.1 g :
        (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) :=
    congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  rw [← e]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

end


set_option maxHeartbeats 1600000 in
theorem stepPotDual : StepPotDual := by
  classical
  intro D hT i r hr Xs w hw n ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1, hc, hx⟩
  refine ⟨K', h, hN, hF, hS, Sig.image (fun a => a⁻¹), Fr, hFr, ?_, ?_,
    le_trans Finset.card_image_le hc, fun x => ?_⟩
  · intro a ha
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, hb, hab⟩ := hst a ha'
    refine ⟨b⁻¹, Finset.mem_image.2 ⟨b, hb, rfl⟩, fun g g' hg => ?_⟩
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hab g g' hg]
  · exact Finset.mem_image.2 ⟨1, h1, inv_one⟩
  · have hcont := GlobalTheory.Pass.FamCont.stepCont D i r hr x
    exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (continuous_loc D i w hw _ hcont.1))
      (bundle _ _ (Br.loc D.nbr i w hw (rDuO D.nd i r x)) (continuous_loc D i w hw _ hcont.2))
      Sig (Sig.image (fun a => a⁻¹)) (hx x).1 (hx x).2).2 (dotProductBilin _ _)
      (isDual1_loc D i w hw r x)
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.PotDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopologyStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  first | exact @GlobalTheory.WeakClosed.continuous_inclR_io_smul | exact GlobalTheory.WeakClosed.continuous_inclR_io_smul | (intros; apply GlobalTheory.WeakClosed.continuous_inclR_io_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalCoordinatesConstantCoeffEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_coordinates_constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  first | exact @GlobalTheory.CrysConst.constantCoeff_eq | exact GlobalTheory.CrysConst.constantCoeff_eq | (intros; apply GlobalTheory.CrysConst.constantCoeff_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

def cstS : Wq l a →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (C : K →+* K⟦X⟧).comp ((algebraMap O K).comp (emb t τ).toRingHom)

theorem cstS_apply (w : Wq l a) (τ : ZMod a) : cstS t K w τ = C (algebraMap O K (emb t τ w)) := rfl


variable (a) {K} in
def dpS (e n : ℕ) : ZMod a → K⟦X⟧ := fun _ => monomial n (((n / e).factorial : K)⁻¹)

end GlobalTheory.CrysPrism
end
end

