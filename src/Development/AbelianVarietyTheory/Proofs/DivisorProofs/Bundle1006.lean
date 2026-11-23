module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsEqChartForms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.ChartStalk

section Algebra

variable {K : Type} [Field K]

def IsComb (A : Subring K) (H' : Set Ω[K⁄ℤ]) (v : Ω[K⁄ℤ]) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → K) (w : ι → Ω[K⁄ℤ]),
    (∀ k, c k ∈ A) ∧ (∀ k, w k ∈ H') ∧ v = ∑ k, c k • w k

theorem isComb_single {A : Subring K} {H' : Set Ω[K⁄ℤ]} {v w : Ω[K⁄ℤ]} {c : K} (hc : c ∈ A)
    (hw : w ∈ H') (e : v = c • w) : IsComb A H' v :=
  ⟨Unit, inferInstance, fun _ => c, fun _ => w, fun _ => hc, fun _ => hw, by
    simp [Finset.univ_unique, e]⟩

theorem spanForms_le_of_isComb (A : Subring K) {M : Set K} {H H' : Set Ω[K⁄ℤ]} (a : ℕ)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (hH : ∀ v ∈ H, IsComb A H' v) :
    spanForms M H a ≤ spanForms M H' a := by
  unfold spanForms
  rw [AddSubgroup.closure_le]
  rintro η ⟨c, hc, v, hv, rfl⟩
  choose ι ft co w hco hw hv' using fun i => hH (v i) (hv i)
  have e : ExteriorAlgebra.ιMulti K a v = ∑ r : ∀ i, ι i,
      (∏ i, co i (r i)) • ExteriorAlgebra.ιMulti K a (fun i => w i (r i)) := by
    conv_lhs => rw [show v = fun i => ∑ k, co i k • w i k from funext hv']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp only [RingHom.id_apply]
  rw [e, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun r _ => AddSubgroup.subset_closure
    ⟨c * ∏ i, co i (r i), hM c hc _ (Subring.prod_mem _ fun i _ => hco i (r i)),
      fun i => w i (r i), fun i => hw i (r i), by rw [smul_smul]⟩

theorem dlog_one : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

theorem dlog_mul (g h : Kˣ) : dlog (g * h) = dlog g + dlog h := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, mul_inv_rev,
    Units.val_inv_eq_inv_val]
  rw [add_comm]
  congr 2
  · field_simp
  · field_simp

def dlogHom : Kˣ →* Multiplicative Ω[K⁄ℤ] where
  toFun g := Multiplicative.ofAdd (dlog g)
  map_one' := by rw [dlog_one]; rfl
  map_mul' g h := by rw [dlog_mul]; rfl

theorem dlog_zpow (g : Kˣ) (m : ℤ) : dlog (g ^ m) = m • dlog g := by
  have := map_zpow (dlogHom (K := K)) g m
  exact congrArg Multiplicative.toAdd this

theorem dlog_prod {ι : Type} (s : Finset ι) (g : ι → Kˣ) : dlog (∏ i ∈ s, g i) = ∑ i ∈ s, dlog (g i) := by
  have := map_prod (dlogHom (K := K)) g s
  exact congrArg Multiplicative.toAdd this

theorem smul_dlog (g : Kˣ) : (g : K) • dlog g = dK (g : K) := by
  rw [dlog, smul_smul, Units.mul_inv, one_smul]

end Algebra

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

theorem dK_eq_frame {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (i : Fin n) :
    dK (x i : X.functionField) = (if i ∈ J then (x i : X.functionField) else 1) • frame x J i := by
  unfold frame
  split_ifs with h
  · exact (smul_dlog (x i)).symm
  · rw [one_smul]

theorem isComb_dlog {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) {g : X.functionFieldˣ} (hg : LogUnit Z y g) :
    IsComb (locRing y) (Set.range (frame x J)) (dlog g) := by
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  obtain ⟨d, hd, hdu⟩ := (hc.chart y hy).deriv (u : X.functionField) hu.regAt
  refine ⟨Fin n, inferInstance,
    fun i => (u : X.functionField)⁻¹ * d i * (if i ∈ J then (x i : X.functionField) else 1) +
      (if i ∈ J then ((m i : ℤ) : X.functionField) else 0),
    frame x J, fun i => ?_, fun i => ⟨i, rfl⟩, ?_⟩
  · refine add_mem (mul_mem (mul_mem hu.inv.regAt (hd i)) ?_) ?_
    · split_ifs
      · exact (hc.chart y hy).mem i
      · exact one_mem _
    · split_ifs
      · exact intCast_mem _ _
      · exact zero_mem _
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← dK_eq_frame, ← Finset.smul_sum, ← hdu,
      ite_smul, zero_smul]
    rw [dlog_mul, dlog_prod, Finset.sum_ite_mem, Finset.univ_inter]
    congr 1
    · rw [dlog, Units.val_inv_eq_inv_val, hdu]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dK_eq_frame x J j, ite_smul]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [dlog_zpow, frame, if_pos hj, Int.cast_smul_eq_zsmul]

theorem isComb_frame {Z : Set X} {U : X.Opens} {n : ℕ} {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)}
    (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U) (i : Fin n) :
    IsComb (locRing y) (dlog '' {g | LogUnit Z y g}) (frame x J i) := by
  have hlog : ∀ w : X.functionFieldˣ, UnitAt y (w : X.functionField) → LogUnit Z y w := fun w hw =>
    (hc.logUnit y hy w).2 ⟨w, 0, hw, by simp⟩
  by_cases hi : i ∈ J
  · refine isComb_single (one_mem _) ⟨x i, (hc.logUnit y hy _).2 ⟨1, Pi.single i 1, ?_, ?_⟩, rfl⟩ ?_
    · rw [Units.val_one]; exact unitAt_one y
    · rw [one_mul, Finset.prod_eq_single_of_mem i hi (fun j _ hj => by simp [Pi.single_apply, hj])]
      simp
    · rw [frame, if_pos hi, one_smul]
  · have hm : RegAt y (x i : X.functionField) := (hc.chart y hy).mem i
    obtain ⟨s, hs⟩ := hm
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with h | h
    · have hu : UnitAt y (x i : X.functionField) := ⟨s, h, hs⟩
      refine isComb_single ((hc.chart y hy).mem i) ⟨x i, hlog _ hu, rfl⟩ ?_
      rw [frame, if_neg hi, smul_dlog]
    · have hu : UnitAt y (1 - (x i : X.functionField)) := ⟨1 - s, h, by rw [map_sub, map_one, hs]⟩
      refine isComb_single (c := -(1 - (x i : X.functionField)))
        (neg_mem (sub_mem (one_mem _) ((hc.chart y hy).mem i)))
        ⟨Units.mk0 _ hu.ne_zero, hlog _ hu, rfl⟩ ?_
      have h2 := smul_dlog (Units.mk0 _ hu.ne_zero)
      rw [Units.val_mk0] at h2
      rw [frame, if_neg hi, neg_smul, h2]
      simp [dK]

end Scheme

theorem logAt_eq_chartForms : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (U : X.Opens) {n : ℕ}
    (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n)) (G : CartierDiv X) (y : X) (t : X.functionFieldˣ)
    (a : ℕ), IsLogChart Z U x J → y ∈ U → G.IsEqn y t → logAt Z G a y = chartForms (locRing y) x J t a := by
  intro X _ Z U n x J G y t a hc hy ht
  have hM : {c | G.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => ht.regularAt_iff
  have hstab : ∀ c ∈ {c | c * (t : X.functionField) ∈ locRing y}, ∀ b ∈ locRing y,
      c * b ∈ {c | c * (t : X.functionField) ∈ locRing y} := fun c hc b hb => by
    simp only [Set.mem_setOf_eq] at hc ⊢
    rw [mul_right_comm]; exact mul_mem hc hb
  unfold logAt chartForms
  rw [hM]
  apply le_antisymm
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨g, hg, e⟩ => e ▸ isComb_dlog hc hy hg
  · exact spanForms_le_of_isComb _ a hstab fun v ⟨i, e⟩ => e ▸ isComb_frame hc hy i

end GlobalTheory.LogDR.ChartStalk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionFubiniStudyPositive
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ArchBound

theorem entries_bound : ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ), P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * P * Y = (s : ℂ) • P →
      ∀ i j, ‖Y i j‖ ^ 2 ≤ K * s :=
  GlobalTheory.T.hermitian_similitude_entry_sq_bound

theorem majorant : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 →
    ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H →
        Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P :=
  GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one

variable {p : ℕ} [Fact p.Prime]

theorem sh_inv_mul (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) * (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * ((β⁻¹ : G.Cˣ) : G.C) := by
  set u : G.Cˣ := (y : G.Cˣ × ℚˣ).1
  set s : ℚ := (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have h : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β := y.2.1
  have h1 : sh G u = algebraMap ℚ G.C s * (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C) * β) := by
    calc sh G u = (((β⁻¹ : G.Cˣ) : G.C) * ((u⁻¹ : G.Cˣ) : G.C)) * ((u : G.C) * β * sh G u) := by
          simp only [mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [h]; simp only [← Algebra.smul_def, mul_smul_comm, mul_assoc]
  rw [h1]
  simp only [← Algebra.smul_def, smul_mul_assoc, mul_assoc, Units.mul_inv_cancel_left]
  rw [Units.inv_mul, mul_one]

theorem psi_algebraMap (G : HTGroup p) (w : InfinitePlace G.F) (q : ℚ) :
    G.psi w (algebraMap ℚ G.C q) = ((q : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have := ((G.psi w).toRatAlgHom).commutes q
  simp only [RingHom.toRatAlgHom_apply] at this
  rw [this, Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, Rat.smul_def]

theorem herm_sim (G : HTGroup p) (β : G.Cˣ) (y : grp G β) (w : InfinitePlace G.F) :
    (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * herm G w β * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • herm G w β := by
  have h := congrArg (G.psi w) (sh_inv_mul G β y)
  rw [map_mul, map_mul, map_mul, psi_algebraMap] at h
  have hs : G.psi w (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
      (G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w := G.psi_star w _
  rw [hs] at h
  have hg : IsUnit (G.gram w).det := isUnit_iff_ne_zero.2 (G.gram_det w)
  unfold herm
  calc _ = G.gram w * ((G.gram w)⁻¹ * (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram w *
        G.psi w ((β⁻¹ : G.Cˣ) : G.C) * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    _ = _ := by rw [h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

theorem herm_congr (G : HTGroup p) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (v : InfinitePlace G.F) :
    ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  obtain ⟨z, hz⟩ := hR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.ArchBound

namespace GlobalTheory.ArchBound

variable {p : ℕ} [Fact p.Prime]

theorem sigPosH_eq_zero_of_ne (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (w : InfinitePlace G.F) (hw : w ≠ v) : sigPosH (G.gram_herm w) = 0 := by
  rcases G.sig w with ⟨h1, -⟩ | ⟨h0, -⟩
  · exfalso
    have hc : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} = 1 := ha
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hc
    have e1 := hx ⟨v, hv⟩
    have e2 := hx ⟨w, h1⟩
    exact hw (by rw [← e2] at e1; exact (congrArg Subtype.val e1).symm)
  · exact h0

theorem exists_majorant (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) (w : InfinitePlace G.F) :
    ∃ P : Matrix (Fin G.n) (Fin G.n) ℂ, P.IsHermitian ∧
      (∀ x : Fin G.n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ y : grp G β, FixL G v β y z →
        (G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * P * G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
          (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • P := by
  obtain ⟨Z, hZ⟩ := herm_congr G β hR w
  have hH : (herm G w β).IsHermitian := by
    rw [hZ]; unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (G.gram_herm w).eq, Matrix.mul_assoc]
  have hdet : (herm G w β).det ≠ 0 := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hz0 : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnits_det_units Z).ne_zero
    exact mul_ne_zero (mul_ne_zero (by simpa using hz0) (G.gram_det w)) hz0
  have hsig : sigPosH hH = sigPosH (G.gram_herm w) :=
    GlobalTheory.SigCong.sigPosH_congr (G.gram w) (G.gram_herm w) (G.gram_det w) Z _ hH hZ
  by_cases hw : w = v
  · subst hw
    obtain ⟨P, hPh, hPp, hPs⟩ := majorant (herm G w β) hH hdet (hsig.trans hv) z hz
    refine ⟨P, hPh, hPp, fun y hy => ?_⟩
    obtain ⟨c, hc⟩ := hy
    exact hPs _ _ c (by exact_mod_cast y.2.2) (herm_sim G β y w) hc
  · have h0 := sigPosH_eq_zero_of_ne G ha v hv w hw
    refine ⟨-herm G w β, hH.neg, fun x hx => ?_, fun y _ => ?_⟩
    · have := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (herm G w β) hH hdet (hsig.trans h0) x hx
      rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
      linarith
    · rw [Matrix.mul_neg, Matrix.neg_mul, herm_sim G β y w, smul_neg]

end GlobalTheory.ArchBound


open GlobalTheory.ArchBound in
theorem GlobalTheory.LKCx.entries_sq_le_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re →
    ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n),
      ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  intro p _ G ha v hv β _ hR z hz
  choose P hPh hPp hPs using exists_majorant G ha v hv β hR z hz
  choose K hK using fun w => entries_bound (P w) (hPh w) (hPp w)
  refine ⟨∑ w, |K w|, fun y hy w i j => ?_⟩
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  refine (hK w _ _ hs (hPs w y hy) i j).trans ?_
  refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) hs.le
  exact Finset.single_le_sum (f := fun w => |K w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix ComplexOrder

namespace GlobalTheory.QuotRational

theorem gram_of_quotMet {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : IsUnit G.det) (P : Matrix (Fin d) (Fin n) ℂ) (D : Matrix (Fin n) (Fin d) ℂ) (h1 : G * P = Dᴴ * A)
    (h2 : (P * A⁻¹ * Pᴴ)⁻¹ = G) : Dᴴ * A * D = G := by
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have hM : IsUnit (P * A⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h2
    subst h2
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact h (by simp)
    · have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      simp at hG
  have h3 : G * (P * A⁻¹ * Pᴴ) = 1 := by rw [← h2]; exact Matrix.nonsing_inv_mul _ hM
  have h4 : Dᴴ * Pᴴ = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Dᴴ, Matrix.mul_nonsing_inv _ hAu,
      Matrix.mul_one] at h3
    exact h3
  have h5 : P * D = 1 := by
    have := congrArg Matrix.conjTranspose h4
    simpa [Matrix.conjTranspose_mul] using this
  rw [← h1, Matrix.mul_assoc, h5, Matrix.mul_one]

theorem eq_of_gram {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (G : Matrix (Fin d) (Fin d) ℂ)
    (C D : Matrix (Fin n) (Fin d) ℂ) (h1 : Dᴴ * A * D = G) (h2 : Cᴴ * A * C = G) (h3 : Dᴴ * A * C = G) : C = D := by
  have hG : Gᴴ = G := by
    rw [← h1]; simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]
  have h4 : Cᴴ * A * D = G := by
    have := congrArg Matrix.conjTranspose h3
    rw [hG] at this
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  have h5 : (C - D)ᴴ * A * (C - D) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    simp
  have h6 : ∀ x, (C - D) *ᵥ x = 0 := by
    intro x
    by_contra hx
    have := hA.dotProduct_mulVec_pos hx
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h5] at this
    simp at this
  rw [← sub_eq_zero]
  ext i j
  simpa using congrFun (h6 (Pi.single j 1)) i

variable {K : Type} [Field K] [StarRing K]

theorem map_conjTranspose_twist (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) :
    (Eᴴ).map σ = (E.map (twist σ))ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply, starRingEnd_apply, star_star]

theorem twist_twist (σ : K →+* ℂ) : twist (twist σ) = σ := by
  ext a
  simp [twist]

theorem map_twist_of_mem (σ : K →+* ℂ) {n d : ℕ} (H : Matrix (Fin n) (Fin d) K) (hH : ∀ i j, H i j ∈ cmMax K) :
    H.map (twist σ) = H.map σ := by
  ext i j
  have : σ (star (H i j)) = starRingEnd ℂ (σ (H i j)) := hH i j σ
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply (R := K), this, Complex.conj_conj]

theorem entries_mem_cmMax [NumberField K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ cmMax K)
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (E : Matrix (Fin n) (Fin d) K)
    (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hR : IsRatHerm (cmMax K) (Eᴴ * H * E) (quotFrame Pr H)) : ∀ i a, E i a ∈ cmMax K := by
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hGP : Eᴴ * H * E * Pr = Eᴴ * H := by
    have h2 := hP.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Eᴴ * H), ← h2]
  have hv : ∀ v : InfinitePlace K, (Eᴴ).map v.embedding * H.map v.embedding * E.map (twist v.embedding) =
      (Eᴴ * H * E).map v.embedding := by
    intro v
    have hq := (quotFrameIsQuot K n d H hpos Pr hsurj v).2
    have hr := (hR.2 v).2
    rw [map_conjTranspose_twist]
    refine gram_of_quotMet _ (hpos v) _ ?_ (Pr.map v.embedding) _ ?_ (hq.symm.trans hr)
    · rw [← hr]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (metOfSpec d _ (hR.2 v).1).1.isUnit
    · rw [← Matrix.map_mul, hGP, Matrix.map_mul, map_conjTranspose_twist]
  have hall : ∀ σ : K →+* ℂ, (Eᴴ).map σ * H.map σ * E.map (twist σ) = (Eᴴ * H * E).map σ := by
    intro σ
    rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
    · rw [← h]; exact hv _
    · have h1 := congrArg (fun M => M.map (starRingEnd ℂ)) (hv (InfinitePlace.mk σ))
      simp only [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_map] at h1
      rw [← h]
      exact h1
  have hE : ∀ v : InfinitePlace K, E.map v.embedding = E.map (twist v.embedding) := by
    intro v
    refine eq_of_gram _ (hpos v) ((Eᴴ * H * E).map v.embedding) _ _ ?_ ?_ ?_
    · rw [← map_conjTranspose_twist]; exact hall _
    · have h1 := hall (twist v.embedding)
      rwa [map_conjTranspose_twist, twist_twist, map_twist_of_mem _ H hH, map_twist_of_mem _ _ hR.1] at h1
    · rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_twist]
  intro i a σ
  have h1 := congrFun (congrFun (hE (InfinitePlace.mk σ)) i) a
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply] at h1
  rcases InfinitePlace.mk_eq_iff.mp (InfinitePlace.mk_embedding (InfinitePlace.mk σ)) with h | h
  · rw [h] at h1
    rw [h1, starRingEnd_apply, star_star]
  · rw [← h, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h1]
    simp

theorem fE_mem_cmMax : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → ∀ a k, B.fE ℓ Z a k ∈ cmMax K := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z v0 s h hR a k
  have hE := entries_mem_cmMax (B.HV ℓ) (BlockDat.HV_rat h.conj h.ok h.irr) (BlockDat.HV_pos h.conj h.ok h.irr)
    (B.zE ℓ Z) (B.Pq ℓ Z) (BlockDat.Pq_orth h.conj h.ok h.irr) hR
  rw [BlockDat.fE, Matrix.mul_apply]
  exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (BlockDat.vE_rat h.conj h.ok h.irr a j) (hE j k)

end GlobalTheory.QuotRational
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfSerOfCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh


set_option maxHeartbeats 1000000 in
theorem oneMapRow_of_serOf_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, SerOf O (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ (t : Tp) (x : O.Cl' t → VsV D i O.c'.F), ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f) → OneMapRow (T.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA (κ i)) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange (cusp (T.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP cc hS hE
  refine ⟨hS.1, hS.2.1, 1, Subgroup.one_mem _, fun t => ⟨1, one_mem _, ⟨1, Nat.one_pos, one_pow _⟩, fun x hx => ⟨hE t x, ?_⟩⟩⟩
  intro f hf hT q
  obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple t).reps
  obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
  have hL := hP.act.2
  have h1 : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) O.c' O.lev2 1 f = f :=
    actL_one _ _ _ hL.total hL.func hL.one hf.1
  have h2 := hS.2.2 t h J' hR _ x hx₀ f hf hT q.out
  rw [h1, hA _ x hx₀, one_mul (cc _)]
  refine h2.trans ?_
  rw [mul_assoc (cc _ * _)]
  rfl

end GlobalTheory.AdTh
end

