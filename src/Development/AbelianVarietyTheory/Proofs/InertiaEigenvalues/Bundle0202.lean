module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNormGe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocyclePartialSumIterateSucc
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem iSup_pow_eq {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hb : BddAbove (Set.range f)) (k : ℕ) :
    (⨆ n, f n ^ k) = (⨆ n, f n) ^ k := by
  have hS : 0 ≤ ⨆ n, f n := le_ciSup_of_le hb 0 (h0 0)
  have hle : ∀ n, f n ^ k ≤ (⨆ n, f n) ^ k := fun n => pow_le_pow_left₀ (h0 n) (le_ciSup hb n) k
  have hb' : BddAbove (Set.range fun n => f n ^ k) := ⟨_, Set.forall_mem_range.2 hle⟩
  refine le_antisymm (ciSup_le hle) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  by_contra hlt
  push_neg at hlt
  set T := ⨆ n, f n ^ k
  have hT : 0 ≤ T := le_ciSup_of_le hb' 0 (pow_nonneg (h0 0) k)
  have hroot : T ^ ((1 : ℝ) / k) < ⨆ n, f n := by
    have := Real.rpow_lt_rpow hT hlt (by positivity : (0 : ℝ) < 1 / k)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hS, mul_one_div_cancel (by positivity), Real.rpow_one] at this
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup hroot
  have h1 := pow_lt_pow_left₀ hn (Real.rpow_nonneg hT _) hk.ne'
  rw [← Real.rpow_natCast, ← Real.rpow_mul hT, one_div_mul_cancel (by positivity), Real.rpow_one] at h1
  exact absurd (le_ciSup hb' n) (not_le.2 h1)

theorem gA_phi (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) :
    gA l ρ (Formalism.Per.φA l a) = gA l (ρ ^ ((1 : ℝ) / l)) a ^ l := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set σ := ρ ^ ((1 : ℝ) / l)
  have hσ0 : 0 ≤ σ := Real.rpow_nonneg hρ0 _
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hρ0 hρ1 (by positivity)
  have hσl : σ ^ l = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0, one_div_mul_cancel hl.ne', Real.rpow_one]
  set f : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * σ ^ n
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf1 : ∀ n, f n ≤ 1 := fun n =>
    mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
      (pow_nonneg hσ0 _) (pow_le_one₀ hσ0 hσ1)
  have hterm : ∀ n, ‖((((Formalism.Per.φA l a).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n
      = f n ^ l := by
    intro n
    have hc : (Formalism.Per.φA l a).coeff n = a.coeff n ^ l := by
      rw [GlobalTheory.RingBasics.φA_apply, WittVector.coeff_frobenius_charP]
    rw [hc, map_pow, SubmonoidClass.coe_pow, norm_pow, ← hσl, mul_pow, ← pow_mul, ← pow_mul, mul_comm n l, pow_mul]
    congr 1
    rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Real.rpow_mul_natCast (norm_nonneg _), mul_comm]
  simp only [gA]
  simp_rw [hterm]
  exact iSup_pow_eq hf0 ⟨1, Set.forall_mem_range.2 hf1⟩ l

theorem isGauss_phi (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l (ρ ^ ((1 : ℝ) / l)) (fun x => gC l ρ (φc l x) ^ ((1 : ℝ) / l)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_of_le l ρ h0 h1
  have hpos : (0 : ℝ) < 1 / l := by positivity
  refine ⟨fun x => ⟨Real.rpow_nonneg (e1 _).1 _, Real.rpow_le_one (e1 _).1 (e1 _).2 hpos.le⟩, fun x y => ?_,
    fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · simp only [map_add (f := _)]
    refine (Real.rpow_le_rpow (e1 _).1 (e2 _ _) hpos.le).trans ?_
    rcases le_total (gC l ρ (φc l x)) (gC l ρ (φc l y)) with h | h
    · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
    · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (e1 _).1 h hpos.le)]
  · simp only [map_neg, e3]
  · simp only [map_mul, e4]
    exact Real.mul_rpow (e1 _).1 (e1 _).1
  · simp only
    have ha : φc l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) =
        algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a
    rw [ha, e5, gA_phi ρ hρ0 h1.le, ← Real.rpow_natCast, ← Real.rpow_mul, mul_one_div_cancel hl.ne', Real.rpow_one]
    exact le_ciSup_of_le ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact mul_le_one₀ (Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
        (pow_nonneg (Real.rpow_nonneg hρ0 _) _) (pow_le_one₀ (Real.rpow_nonneg hρ0 _)
          (Real.rpow_le_one hρ0 h1.le (by positivity)))⟩ 0 (by positivity)

theorem gC_phi : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l,
    gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  intro l _ ρ h0 h1 x
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : (0 : ℝ) < l := by linarith
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 hl.le).trans h0
  have hσ0 : ρ ≤ ρ ^ ((1 : ℝ) / l) := by
    conv_lhs => rw [← Real.rpow_one ρ]
    exact Real.rpow_le_rpow_of_exponent_ge' hρ0 h1.le (by positivity)
      (by rw [div_le_one hl]; exact hl1.le)
  have hσ1 : ρ ^ ((1 : ℝ) / l) < 1 := Real.rpow_lt_one hρ0 h1 (by positivity)
  have e := _root_.GlobalTheory.PMon.Gauss.isGauss_unique l (ρ ^ ((1 : ℝ) / l)) _ _ (h0.trans hσ0) hσ1 (isGauss_phi ρ h0 h1)
    (isGauss_gC_of_le l _ (h0.trans hσ0) hσ1)
  have ex : gC l ρ (φc l x) ^ ((1 : ℝ) / l) = gC l (ρ ^ ((1 : ℝ) / l)) x := congrFun e x
  rw [← ex, ← Real.rpow_natCast, ← Real.rpow_mul ((isGauss_gC_of_le l ρ h0 h1).1 _).1,
    one_div_mul_cancel hl.ne', Real.rpow_one]

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen

namespace GlobalTheory.SenLines.Coords

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def zc (c : F⟦X⟧) (n : ℤ) : F := if 0 ≤ n then coeff n.toNat c else 0

theorem zc_nat (c : F⟦X⟧) (n : ℕ) : zc c n = coeff n c := by
  simp [zc]

theorem zc_neg (c : F⟦X⟧) {n : ℤ} (h : n < 0) : zc c n = 0 := by
  unfold zc
  rw [if_neg (not_le.mpr h)]

theorem zc_add (c c' : F⟦X⟧) (n : ℤ) : zc (c + c') n = zc c n + zc c' n := by
  unfold zc
  split_ifs <;> simp [map_add (f := _)]

theorem zc_mul (f c : F⟦X⟧) (n : ℤ) (N : ℕ) (h : n < N) :
    zc (f * c) n = ∑ j ∈ Finset.range N, coeff j f * zc c (n - j) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [zc_neg _ hn]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [zc_neg _ (by omega), mul_zero]
  · lift n to ℕ using hn
    have hN : n < N := by exact_mod_cast h
    rw [zc_nat, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j c),
      ← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n + 1) N) ?_, add_zero]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show ((n : ℤ) - (j : ℤ)) = ((n - j : ℕ) : ℤ) by omega, zc_nat]
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [zc_neg _ (by omega), mul_zero]

def lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) : ℤ → M :=
  ∑ k, serLine (u k) (d k) (c k)

theorem lines_apply {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c : Fin r → F⟦X⟧) (m : ℤ) :
    lines u d c m = ∑ k, zc (c k) (m + u k) • d k := by
  unfold lines
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [serLine, zc]
  split_ifs <;> simp

theorem lines_add {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (c c' : Fin r → F⟦X⟧) :
    lines u d (c + c') = lines u d c + lines u d c' := by
  funext m
  simp only [lines_apply, Pi.add_apply, zc_add, add_smul, Finset.sum_add_distrib]

theorem lines_zero {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) :
    lines u d (0 : Fin r → F⟦X⟧) = 0 := by
  funext m
  rw [lines_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : zc (0 : F⟦X⟧) (m + u k) = 0 := by
    unfold zc
    split_ifs <;> simp
  rw [Pi.zero_apply, this, zero_smul]

theorem lines_sum {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) {ι : Type} (s : Finset ι)
    (c : ι → Fin r → F⟦X⟧) : lines u d (∑ j ∈ s, c j) = ∑ j ∈ s, lines u d (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, lines_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lines_add, ih]

theorem coeff_eq_of_apply {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d)
    (c c' : Fin r → F⟦X⟧) (a : F) (m : ℤ) (h : lines u d c m = a • lines u d c' m) (k : Fin r) :
    zc (c k) (m + u k) = a * zc (c' k) (m + u k) := by
  rw [lines_apply, lines_apply, Finset.smul_sum] at h
  have h2 : ∑ k, (zc (c k) (m + u k) - a * zc (c' k) (m + u k)) • d k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [h, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hd _ h2 k)

theorem lines_injective {r : ℕ} (u : Fin r → ℤ) {d : Fin r → M} (hd : LinearIndependent F d) :
    Function.Injective (lines (F := F) u d) := by
  intro c c' h
  funext k
  ext n
  have := coeff_eq_of_apply u hd c c' 1 ((n : ℤ) - u k) (by rw [h, one_smul]) k
  rwa [sub_add_cancel, one_mul, zc_nat, zc_nat] at this

theorem serAct_lines {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (f : F⟦X⟧) (c : Fin r → F⟦X⟧) :
    serAct f (lines u d c) = lines u d (f • c) := by
  funext m
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, m + u k < N := by
    refine ⟨(Finset.univ.sup fun k => (m + u k).toNat) + 1, fun k => ?_⟩
    have h1 : (m + u k).toNat ≤ Finset.univ.sup fun k => (m + u k).toNat :=
      Finset.le_sup (f := fun k => (m + u k).toNat) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (m + u k)
    push_cast
    omega
  have hsupp : (Function.support fun j : ℕ => coeff j f • lines u d c (m - j)) ⊆ ↑(Finset.range N) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hjN
    apply hj
    rw [lines_apply, Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [zc_neg _ (by have := hN k; omega), zero_smul]
  unfold serAct
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp_rw [lines_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [zc_mul f (c k) (m + u k) N (hN k), Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show m - (j : ℤ) + u k = m + u k - j by ring]

theorem exists_coords : ∀ {F M A N : Type} [Field F] [AddCommGroup M] [Module F M] [CommRing A] [AddCommGroup N] [Module A N] (lev : A → F⟦X⟧) (L : N →+ (ℤ → M)) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d → (∀ a x, L (a • x) = serAct (lev a) (L x)) → SpanIsLines L u d F → ∃ e : N →+ (Fin r → F⟦X⟧), (∀ a x, e (a • x) = lev a • e x) ∧ Submodule.span F⟦X⟧ (Set.range e) = ⊤ ∧ ∀ (χ : F) (x y : N), χ ≠ 0 → (∀ k : ℤ, L y k = χ ^ k • L x k) → ∀ k, e y k = C (χ ^ (-u k)) * rescale χ (e x k) := by
  intro F M A N _ _ _ _ _ _ lev L r u d hd hL hS
  have hex : ∀ x, ∃ c : Fin r → F⟦X⟧, L x = lines u d c := by
    intro x
    obtain ⟨c, hc⟩ := (hS (L x)).mp ⟨1, fun _ => x, fun _ => 1, by simp only [Fin.sum_univ_one, serAct_one]⟩
    exact ⟨c, hc⟩
  choose e he using hex
  have hinj := lines_injective (F := F) u hd
  have eadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    hinj (by rw [← he, lines_add, ← he, ← he, map_add (f := _)])
  refine ⟨AddMonoidHom.mk' e eadd, ?_, ?_, ?_⟩
  · intro a x
    show e (a • x) = lev a • e x
    apply hinj
    rw [← he, hL, he x, serAct_lines]
  · rw [eq_top_iff]
    intro c _
    obtain ⟨s, x, f, hy⟩ := (hS (lines u d c)).mpr ⟨c, rfl⟩
    have hc : c = ∑ j, f j • e (x j) := by
      apply hinj
      rw [hy, lines_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [he, serAct_lines]
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x j, rfl⟩)
  · intro χ x y hχ hxy k
    show e y k = C (χ ^ (-u k)) * rescale χ (e x k)
    ext n
    have h1 : lines u d (e y) ((n : ℤ) - u k) = χ ^ ((n : ℤ) - u k) • lines u d (e x) ((n : ℤ) - u k) := by
      rw [← he, ← he]
      exact hxy _
    have h2 := coeff_eq_of_apply u hd (e y) (e x) _ _ h1 k
    rw [sub_add_cancel, zc_nat, zc_nat] at h2
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, zpow_sub₀ hχ, zpow_neg, zpow_natCast]
    ring

end GlobalTheory.SenLines.Coords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnil
section
open Matrix Polynomial

namespace GlobalTheory.UnitDiscAlg

section Residue
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]

def unitBallMaxIdeal : Ideal (unitBallSubring E) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal E

theorem mem_unitBallMaxIdeal {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := Iff.rfl

theorem unitBallMaxIdeal_isMaximal : (unitBallMaxIdeal E).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    have h' : ‖((1 : E))‖ < 1 := h
    simp at h'
  · intro J x _ hx hxJ
    have hx1 : ¬ ‖(x : E)‖ < 1 := hx
    have hx2 : ‖(x : E)‖ ≤ 1 := x.2
    have hn : ‖(x : E)‖ = 1 := le_antisymm hx2 (not_lt.mp hx1)
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv : ‖(x : E)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
    have hmem := J.mul_mem_left ⟨(x : E)⁻¹, hinv⟩ hxJ
    convert hmem using 1
    apply Subtype.ext
    exact (inv_mul_cancel₀ hx0).symm

end Residue

theorem norm_lt_one_of_pow_of_commute (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by
  intro i j
  have hM0 : M ≠ 0 := by
    rintro rfl
    have := hM i i
    simp at this
  obtain ⟨u, v, hu, hv, huv⟩ := hb
  haveI := unitBallMaxIdeal_isMaximal E
  letI : Field (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.field _
  let O := unitBallSubring E
  let π : O →+* (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.mk _
  let N' : Matrix (Fin n) (Fin n) O := fun a b => ⟨N a b, hN a b⟩
  let w' : Matrix (Fin n) (Fin n) O := fun a b => ⟨w a b, hw a b⟩
  have hNm : O.subtype.mapMatrix N' = N := by ext; rfl
  have hwm : O.subtype.mapMatrix w' = w := by ext; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) := by
    intro a b h
    ext x y
    exact congrFun (congrFun h x) y
  have hwN' : w' * N' = N' * w' := hinj (by rw [map_mul, map_mul, hNm, hwm, hwN])
  have hu' : (u.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hu m
  have hv' : (v.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hv m
  have hNmap : N'.map O.subtype = N := by ext; rfl
  have hbO : u.toSubring O hu' * N'.charpoly + v.toSubring O hv' * derivative N'.charpoly = 1 := by
    apply Polynomial.map_injective O.subtype Subtype.val_injective
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_toSubring, Polynomial.map_toSubring, ← Matrix.charpoly_map, hNmap,
      Polynomial.map_one]
    exact huv
  set N'' := N'.map π with hN''
  set w'' := w'.map π with hw''
  have hbk : (u.toSubring O hu').map π * N''.charpoly
      + (v.toSubring O hv').map π * derivative N''.charpoly = 1 := by
    have := congrArg (Polynomial.map π) hbO
    simpa [hN'', Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.derivative_map,
      Matrix.charpoly_map] using this
  have hwk : w'' * N'' = N'' * w'' := by
    rw [hN'', hw'', ← Matrix.map_mul, ← Matrix.map_mul, hwN']
  have hs : N''.charpoly.Separable := ⟨_, _, hbk⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RegSS.cyclicField (unitBallSubring E ⧸ unitBallMaxIdeal E) (Fin n) N'' hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra _ (Fin n) N'' x hx).2.2
  have hmem : w'' ∈ Algebra.adjoin (unitBallSubring E ⧸ unitBallMaxIdeal E) {N''} :=
    GlobalTheory.RegSS.mem_genAlg_of_commute hbij hwk
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hpowm : O.subtype.mapMatrix (w' ^ M) = w ^ M := by rw [map_pow, hwm]
  have hpow : w'' ^ M = 0 := by
    rw [hw'', ← Matrix.map_pow]
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallMaxIdeal]
    have := congrFun (congrFun hpowm a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    show ‖(((w' ^ M) a b : O) : E)‖ < 1
    rw [show (((w' ^ M) a b : O) : E) = (w ^ M) a b from this]
    exact hM a b
  have hfM : aeval N'' (f ^ M) = 0 := by
    rw [map_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [hf, hpow]
  have hdvd := minpoly.dvd _ N'' hfM
  have hsq : Squarefree (minpoly (unitBallSubring E ⧸ unitBallMaxIdeal E) N'') :=
    hs.squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly N'')
  have hdvd' := (Squarefree.dvd_pow_iff_dvd hsq hM0).mp hdvd
  have hf0 : aeval N'' f = 0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd' (minpoly.aeval _ _)
  have hw0 : w'' = 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [← hf, hf0]
  have hij := congrFun (congrFun hw0 i) j
  rw [hw'', Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_unitBallMaxIdeal] at hij
  exact hij

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem trace_almost_onto (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (_hL : ∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a :=
  AlmostTrace.trace_almost_onto_of_levels (GlobalTheory.Cyc.exists_trace_norm_ge l) K L S hKL hS hrep a ha ha1

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargestModel
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem exists_greatest_of_sup_closed {S V ι : Type} [CommRing S] [IsNoetherianRing S] [AddCommGroup V]
    [Module S V] [Finite ι] (C : (ι → Submodule S V) → Prop) (P N₀ : ι → Submodule S V) (h₀ : C N₀)
    (hP : ∀ i, (P i).FG) (hle : ∀ N, C N → ∀ i, N i ≤ P i)
    (hsup : ∀ N N', C N → C N' → C (fun i => N i ⊔ N' i)) :
    ∃ N, C N ∧ ∀ N', C N' → ∀ i, N' i ≤ N i := by
  classical
  have one : ∀ i, ∃ N, C N ∧ ∀ N', C N' → N' i ≤ N i := by
    intro i
    haveI : IsNoetherian S (P i) := isNoetherian_of_fg_of_noetherian _ (hP i)
    obtain ⟨_, ⟨N, hN, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 this
      {Q : Submodule S (P i) | ∃ N, C N ∧ (N i).comap (P i).subtype = Q} ⟨_, N₀, h₀, rfl⟩
    refine ⟨N, hN, fun N' hN' x hx => ?_⟩
    have h1 := hmax _ ⟨_, hsup N N' hN hN', rfl⟩
    have h2 : (N i).comap (P i).subtype = (N i ⊔ N' i).comap (P i).subtype :=
      (Submodule.comap_mono le_sup_left).eq_of_not_lt h1
    have h3 : (⟨x, hle N' hN' i hx⟩ : P i) ∈ (N i ⊔ N' i).comap (P i).subtype :=
      Submodule.mem_sup_right hx
    rw [← h2] at h3
    exact h3
  have all : ∀ s : Finset ι, ∃ N, C N ∧ ∀ N', C N' → ∀ i ∈ s, N' i ≤ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₀, h₀, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨N, hN, h⟩ := ih
      obtain ⟨N₁, hN₁, h₁⟩ := one a
      refine ⟨_, hsup N N₁ hN hN₁, fun N' hN' i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_sup_of_le_right (h₁ N' hN')
      · exact le_sup_of_le_left (h N' hN' i hi)
  haveI := Fintype.ofFinite ι
  obtain ⟨N, hN, h⟩ := all Finset.univ
  exact ⟨N, hN, fun N' hN' i => h N' hN' i (Finset.mem_univ i)⟩

theorem exists_largest_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  intro k G _ _ l n _ _ _ R F r Dt M A N₀ h₀
  obtain ⟨-, hl₀, hab₀, -⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M A N₀ h₀
  refine exists_greatest_of_sup_closed (fun N => M.Model A N)
    (fun i => sh (-(sg l Dt.h i : ℤ)) (N₀ i)) N₀ h₀ (fun i => ((hl₀ i).shift _).1) (fun N hN i => ?_)
    (fun N N' => _root_.GlobalTheory.Models.SupModel.model_sup F M A N N')
  obtain ⟨-, hl, hab, -⟩ := _root_.GlobalTheory.Models.model_obj_and_abc F M A N hN
  have h := sh_le_sh (-(sg l Dt.h i : ℤ)) (_root_.GlobalTheory.PhiGam.CloseTw.main (F.D A) Dt.h Dt.w N N₀ hl hl₀ hab hab₀ i)
  rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h

end GlobalTheory.Models
end

