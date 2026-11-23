module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparable
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleSplitOfContracting
section
noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

private theorem coe_powerSeries_smul_eq_smul {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := by
  rw [← algebraMap_smul (k⸨X⸩) a x, LaurentSeries.coe_algebraMap]

private theorem powerSeries_smul_mem_of_mem {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (N : Submodule k⟦X⟧ V) {x : V} (hx : x ∈ N)
    (a : k⟦X⟧) : (a : k⸨X⸩) • x ∈ N := by
  rw [coe_powerSeries_smul_eq_smul]; exact N.smul_mem a hx

private theorem mem_of_gmult_eq_zero_of_sub_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    (T : Module.End k U) (P Q : Submodule k U) (x : k) (s : Set U) (hs : s.Finite)
    (hP : P ≤ Submodule.span k s ⊔ Q) (h0 : gmult T P Q x = 0) (y : U) (hy : y ∈ P)
    (hT : (T - algebraMap k (Module.End k U) x) y ∈ Q) : y ∈ Q := by
  set E : Submodule k U := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hE
  have hyE : y ∈ E := by
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_iSup_of_mem 1 ?_⟩
    rw [Submodule.mem_comap, pow_one]; exact hT
  let f : E →ₗ[k] U ⧸ Q := Q.mkQ ∘ₗ E.subtype
  let W : Submodule k (U ⧸ Q) := (Submodule.span k s).map Q.mkQ
  have hWfg : W.FG := (Submodule.fg_span hs).map _
  have : Module.Finite k W := Module.Finite.iff_fg.mpr hWfg
  have hrange : ∀ z : E, f z ∈ W := by
    intro z
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hP z.2.1)
    refine ⟨a, ha, ?_⟩
    show Q.mkQ a = Q.mkQ (z : U)
    have hc0 : Q.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hc
    rw [← hac, map_add (f := _), hc0, add_zero]
  have hker : LinearMap.ker f = Q.submoduleOf E := by
    ext z
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  have hker' : LinearMap.ker (f.codRestrict W hrange) = Q.submoduleOf E := by
    rw [LinearMap.ker_codRestrict, hker]
  let g := (Q.submoduleOf E).liftQ (f.codRestrict W hrange) hker'.ge
  have hg : LinearMap.ker g = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hker'.le
  have : IsNoetherian k W := IsNoetherian.iff_fg.mpr inferInstance
  have : Module.Finite k (E ⧸ Q.submoduleOf E) := Module.Finite.of_injective g (LinearMap.ker_eq_bot.mp hg)
  have hq : Module.finrank k (E ⧸ Q.submoduleOf E) = 0 := h0
  have := Module.finrank_zero_iff.mp hq
  have h1 : (Submodule.Quotient.mk (⟨y, hyE⟩ : E) : E ⧸ Q.submoduleOf E) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

private theorem exists_finite_span_sup_shift_of_isLat {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (N : Submodule k⟦X⟧ V) (hN : IsLat N) :
    ∃ s : Set V, s.Finite ∧ N.restrictScalars k ≤ Submodule.span k s ⊔ (sh 1 N).restrictScalars k := by
  obtain ⟨t, ht⟩ := hN.1
  refine ⟨↑t, t.finite_toSet, ?_⟩
  intro x hx
  rw [Submodule.restrictScalars_mem, ← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y hy0 hy =>
    have hyN : y ∈ N := by rw [ht] at hy0; exact hy0
    obtain ⟨a', ha'⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.X_dvd_iff]; simp
    have hsplit : a = PowerSeries.C (PowerSeries.constantCoeff a) + PowerSeries.X * a' := by
      rw [← ha']; ring
    rw [hsplit, add_smul, mul_smul]
    refine add_mem ?_ (Submodule.mem_sup_right ?_)
    · have hc : (PowerSeries.C (PowerSeries.constantCoeff a) : k⟦X⟧) • y = (PowerSeries.constantCoeff a) • y := by
        rw [← algebraMap_smul (k⟦X⟧) (PowerSeries.constantCoeff a) y]; rfl
      rw [hc]; exact Submodule.smul_mem _ _ hy
    · rw [Submodule.restrictScalars_mem, mem_sh_iff_exists]
      exact ⟨a' • y, N.smul_mem a' hyN, by rw [zpow_one, vv_eq_coe_X, coe_powerSeries_smul_eq_smul]⟩

private theorem vv_pow_smul_mem_of_sen_eq_zero {k : Type} [Field k] {l : ℕ} (R : RingPG k l) {V : Type} [AddCommGroup V]
    [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V) (hN : IsLat N)
    (s : ℕ) (hsen : sen g N (-((s + 1 : ℕ) : k)) = 0) (b : V) (hb : vv k ^ (s + 1) • b ∈ N)
    (hw : g b - b ∈ sh 1 N) : vv k ^ s • b ∈ N := by
  have hv : vv k ≠ 0 := vv_ne_zero k
  obtain ⟨κ, hκ0, hκ⟩ := R.γ_v
  obtain ⟨κ₁, hκ₁⟩ : PowerSeries.X ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ0]
  have hE : ∀ t : ℕ, ∃ e : k⟦X⟧,
      (1 - κ * PowerSeries.X) ^ t - 1 + (t : k⟦X⟧) * PowerSeries.X = PowerSeries.X ^ 2 * e := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | succ t ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * (1 - κ * PowerSeries.X) - κ₁ + (t : k⟦X⟧) * κ, ?_⟩
      push_cast
      linear_combination (1 - κ * PowerSeries.X) * hc - PowerSeries.X * hκ₁
  obtain ⟨e, he⟩ := hE (s + 1)
  have he' : (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) - 1 + ((s + 1 : ℕ) : k⸨X⸩) * vv k
      = vv k ^ 2 * (e : k⸨X⸩) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ k) he
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_natCast] at h
    rw [← vv_eq_coe_X] at h
    exact h
  have hw' : (vv k)⁻¹ • (g b - b) ∈ N := by
    have h := (mem_sh_iff_smul_mem (a := 1)).mp hw
    rwa [zpow_neg_one] at h
  have hgy : g (vv k ^ (s + 1) • b) = (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1) • g b := by
    rw [show g (vv k ^ (s + 1) • b) = R.γ (vv k ^ (s + 1)) • g b from hg _ _, map_pow, hκ]
  have hz : nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b) ∈ sh 1 N := by
    rw [mem_sh_iff_smul_mem]
    have hid : vv k ^ (-(1 : ℤ)) • (nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b))
        = (e : k⸨X⸩) • (vv k ^ (s + 1) • b) + (((1 - κ * PowerSeries.X) ^ (s + 1) * PowerSeries.X ^ s : k⟦X⟧) : k⸨X⸩) • ((vv k)⁻¹ • (g b - b)) := by
      rw [nab_apply_eq, hgy, Nat.cast_smul_eq_nsmul k, ← Nat.cast_smul_eq_nsmul k⸨X⸩]
      simp only [map_mul, map_pow, map_sub, map_one]
      rw [← vv_eq_coe_X, zpow_neg_one]
      have hvi : vv k * (vv k)⁻¹ = 1 := mul_inv_cancel₀ hv
      set vi := (vv k)⁻¹
      generalize ((s + 1 : ℕ) : k⸨X⸩) = c' at he' ⊢
      generalize (e : k⸨X⸩) = E at he' ⊢
      have hA : vi * (vi * (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1))
          = (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        rw [mul_pow]
        linear_combination (vi * (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s) * hvi
      have hB : E * vv k ^ (s + 1) = -(vi * (vi * vv k ^ (s + 1))) + vi * (c' * vv k ^ (s + 1))
          + (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        linear_combination (-(vv k ^ s * vi)) * he' - (E * vv k ^ (s + 1) - vi * vv k ^ s) * hvi
      simp only [smul_add, smul_sub, smul_smul]
      rw [hA, hB]
      simp only [add_smul, neg_smul]
      abel
    rw [hid]
    exact add_mem (powerSeries_smul_mem_of_mem N hb _) (powerSeries_smul_mem_of_mem N hw' _)
  have hkey : vv k ^ (s + 1) • b ∈ sh 1 N := by
    obtain ⟨t, ht, hsp⟩ := exists_finite_span_sup_shift_of_isLat N hN
    exact mem_of_gmult_eq_zero_of_sub_mem (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
      (-((s + 1 : ℕ) : k)) t ht hsp hsen _ hb (by
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, neg_smul, sub_neg_eq_add]; exact hz)
  have h := (mem_sh_iff_smul_mem (a := 1)).mp hkey
  rw [smul_smul, zpow_neg_one, pow_succ', inv_mul_cancel_left₀ hv] at h
  exact h

theorem cocycle_split_of_contracting : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (N : ZMod n → Submodule k⟦X⟧ V) (J : ZMod n → ℕ), (∀ i, IsLat (N i)) → (∀ i, CondC (D.γ i) (N i)) → (∀ i, pull (D.φ i) (N (i - 1)) ≤ sh 1 (N i)) → (∀ i (j : ℕ), 1 ≤ j → j ≤ J i → sen (D.γ i) (N i) (-(j : k)) = 0) → ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i) → (∀ i, g i ∈ sh 1 (N i)) → (∀ i, b i ∈ sh (-(J i)) (N i)) → ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧ g i = D.γ i (m i) - m i := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D N J hlat hC hφ hsen b g hcoc hg hb
  have hsub : ∀ i, sh 1 (N i) ≤ N i := by
    intro i
    have h := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) (N i)
    rwa [sh_zero_eq] at h
  have hφ' : ∀ i, ∀ x ∈ N (i - 1), D.φ i x ∈ sh 1 (N i) := fun i x hx =>
    hφ i (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hw : ∀ i, D.γ i (b i) - b i ∈ sh 1 (N i) := by
    intro i
    rw [hcoc i]
    exact sub_mem (hφ' i _ (hsub (i - 1) (hg (i - 1)))) (hg i)
  have hbN : ∀ i, b i ∈ N i := by
    intro i
    have key : ∀ d, d ≤ J i → vv k ^ (J i - d) • b i ∈ N i := by
      intro d
      induction d with
      | zero => intro _; simpa using (mem_sh_iff_smul_mem).mp (hb i)
      | succ d ih =>
        intro hd
        have e : J i - d = (J i - (d + 1)) + 1 := by omega
        have h1 := ih (by omega)
        rw [e] at h1
        have h2 := hsen i (J i - d) (by omega) (by omega)
        rw [e] at h2
        exact vv_pow_smul_mem_of_sen_eq_zero R (D.γ i) (D.γ_semi i) (N i) (hlat i) _ h2 (b i) h1 (hw i)
    simpa using key (J i) le_rfl
  obtain ⟨m, hmN, hm⟩ := (one_sub_frob_bij R D N hlat hφ').1 b hbN
  have hhN : ∀ i, D.γ i (m i) - m i - g i ∈ N i := fun i =>
    sub_mem (hsub i (hC i (m i) (hmN i))) (hsub i (hg i))
  have hhφ : ∀ i, D.φ i (D.γ (i - 1) (m (i - 1)) - m (i - 1) - g (i - 1)) = D.γ i (m i) - m i - g i := by
    intro i
    have e1 : D.φ i (m (i - 1)) = b i + m i := by rw [← hm i]; abel
    have e2 : D.φ i (g (i - 1)) = D.γ i (b i) - b i + g i := by rw [hcoc i]; abel
    rw [map_sub, map_sub, D.comm, e1, e2, map_add (f := _)]
    abel
  have h0 := (one_sub_frob_bij R D N hlat hφ').2 (fun i => D.γ i (m i) - m i - g i) hhN hhφ
  refine ⟨m, hmN, fun i => ⟨(hm i).symm, ?_⟩⟩
  have h3 := congrFun h0 i
  simp only [Pi.zero_apply] at h3
  exact (sub_eq_zero.mp h3).symm

end GlobalTheory.PhiGam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeSmulMem
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Gauge
section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem _root_.GlobalTheory.PhiGam.Gauge.phi_sh {l : ℕ} (R : _root_.GlobalTheory.PhiGam.RingPG k l)
    (f : V →ₗ[k] V) (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (N N' : Submodule k⟦X⟧ V) (w : ℤ)
    (h : _root_.GlobalTheory.PhiGam.pull f N' ≤ _root_.GlobalTheory.PhiGam.sh (-w) N) (m : ℕ) {x : V}
    (hx : x ∈ _root_.GlobalTheory.PhiGam.sh m N') :
    f x ∈ _root_.GlobalTheory.PhiGam.sh (l * m - w) N := by
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := R.φ_v
  have hfy : f y ∈ _root_.GlobalTheory.PhiGam.sh (-w) N := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hfy
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_exists]
  refine ⟨((u : k⟦X⟧) ^ m) • z, N.smul_mem _ hz, ?_⟩
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [zpow_natCast, hf, map_pow, hu, ← hz', ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) ^ m) z, smul_smul,
    smul_smul, LaurentSeries.coe_algebraMap, map_pow, sub_eq_add_neg, zpow_add₀ hX, mul_pow, ← pow_mul]
  congr 1
  rw [show ((l : ℤ) * (m : ℤ)) = ((l * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

end

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem vv_smul_mem_sh_succ_iff (a : ℤ) (N : Submodule k⟦X⟧ V) (y : V) :
    _root_.GlobalTheory.PhiGam.vv k • y ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) N ↔
      y ∈ _root_.GlobalTheory.PhiGam.sh a N := by
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, _root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, smul_smul, ← zpow_add_one₀ hX]
  rw [show -(a + 1) + 1 = -a by ring]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem apply_sub_self_eq_vv_smul_nab (f : V →ₗ[k] V) (x : V) :
    f x - x = _root_.GlobalTheory.PhiGam.vv k • _root_.GlobalTheory.PhiGam.nab f x := by
  rw [_root_.GlobalTheory.PhiGam.nab_apply_eq, smul_smul, mul_inv_cancel₀ (_root_.GlobalTheory.PhiGam.vv_ne_zero k),
    one_smul]


open scoped LaurentSeries PowerSeries in
theorem _root_.GlobalTheory.PhiGam.Gauge.main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l]
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V] (D : _root_.GlobalTheory.PhiGam.ModPG R n V), ∀ (w w' : ZMod n → ℤ) (s : ZMod n → ℕ)
    (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, _root_.GlobalTheory.PhiGam.IsLat (N i)) →
    _root_.GlobalTheory.PhiGam.CondAB D.φ w w' N →
    (∀ i, _root_.GlobalTheory.PhiGam.CondC (D.γ i) (N i)) →
    (∀ i, (s i : ℤ) + 1 ≤ l * (s (i - 1) + 1) - w i) →
    (∀ i (a : ℕ), a ≤ s i + 1 → _root_.GlobalTheory.PhiGam.sen (D.γ i) (N i) (a : k) = 0) →
    ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i =
      D.φ i (g (i - 1)) - g i) →
    (∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh 1 (N i)) →
    (∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧
      ∀ i, g i - (D.γ i (m i) - m i) ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) ∧
    ((∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) → (∀ i, b i ∈ N i) →
      ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧
        g i = D.γ i (m i) - m i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D w w' s N hN hAB hC hs hsen b g hcoc hg
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hW : ∀ i, _ := fun i => _root_.GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ i)
    (D.γ_semi i) (N i) (hN i) (hC i) 0 (s i + 2) (fun j hj => by
      simpa using hsen i j (by omega))
  refine ⟨?_, fun hg3 hb => ?_⟩
  · have key : ∀ i, ∃ x ∈ N i, g i - (D.γ i x - x) ∈
        _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i) := by
      intro i
      have hy : (_root_.GlobalTheory.PhiGam.vv k)⁻¹ • g i ∈ _root_.GlobalTheory.PhiGam.sh 0 (N i) := by
        rw [← vv_smul_mem_sh_succ_iff, smul_inv_smul₀ hX]
        simpa using hg i
      obtain ⟨x, hx, hxy⟩ := (hW i).2 _ hy
      refine ⟨x, by rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at hx, ?_⟩
      have h3 := (vv_smul_mem_sh_succ_iff _ _ _).2 hxy
      rw [smul_sub, smul_inv_smul₀ hX, ← apply_sub_self_eq_vv_smul_nab] at h3
      convert h3 using 2
      push_cast
      ring
    choose m hm1 hm2 using key
    exact ⟨m, hm1, hm2⟩
  · set φ := D.φ
    set γ := D.γ
    have hφ : ∀ i (a : ℕ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N (i - 1)) →
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh (l * a - w i) (N i) := fun i a x hx =>
      _root_.GlobalTheory.PhiGam.Gauge.phi_sh R (φ i) (D.φ_semi i) (N i)
        (N (i - 1)) (w i) (hAB i).1 a hx
    have hγ : ∀ i (a : ℤ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N i) →
        γ i x - x ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) (N i) := fun i a x hx => by
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff]
      exact _root_.GlobalTheory.PhiGam.Window.nab_mem_sh R (D.γ_semi i) (hC i) a hx
    have hb' : ∀ i, b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i) := by
      intro i
      have h1 : γ i (b i) - b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2 + 1) (N i) := by
        rw [hcoc i]
        refine sub_mem ?_ (by convert hg3 i using 2; ring)
        have h2 := hφ i (s (i - 1) + 3) (by push_cast; exact hg3 (i - 1))
        refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ h2
        have := hs i
        push_cast
        nlinarith
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff] at h1
      have := (hW i).1 (b i) (by rw [_root_.GlobalTheory.PhiGam.sh_zero_eq]; exact hb i) (by convert h1 using 2; push_cast; ring)
      convert this using 2
      push_cast
      ring
    have hP : ∀ i, ∀ x ∈ _root_.GlobalTheory.PhiGam.sh ((s (i - 1) : ℤ) + 2) (N (i - 1)),
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh 1
          (_root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) := by
      intro i x hx
      rw [_root_.GlobalTheory.PhiGam.sh_sh_eq]
      refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ (hφ i (s (i - 1) + 2) (by push_cast; exact hx))
      have := hs i
      push_cast
      nlinarith
    have hF := _root_.GlobalTheory.PhiGam.one_sub_frob_bij R D
      (fun i => _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) (fun i => (hN i).shift _) hP
    obtain ⟨m, hmP, hmb⟩ := hF.1 b hb'
    change ∀ i, φ i (m (i - 1)) - m i = b i at hmb
    have hg0 := hF.2 (fun i => g i - (γ i (m i) - m i))
      (fun i => sub_mem (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hg3 i))
        (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hγ i _ (hmP i))))
      (fun i => by
        show φ i (g (i - 1) - (γ (i - 1) (m (i - 1)) - m (i - 1))) = g i - (γ i (m i) - m i)
        have e := hcoc i
        rw [← hmb i, map_sub] at e
        have e2 := sub_eq_iff_eq_add.1 e.symm
        have hcomm : ∀ x, φ i (γ (i - 1) x) = γ i (φ i x) := D.comm i
        simp only [map_sub, hcomm]
        rw [e2]
        abel)
    refine ⟨m, fun i => ?_, fun i => ⟨(hmb i).symm, ?_⟩⟩
    · have := _root_.GlobalTheory.PhiGam.sh_le_sh_of_le (show (0 : ℤ) ≤ (s i : ℤ) + 2 by positivity) _ (hmP i)
      rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at this
    · exact sub_eq_zero.1 (congrFun hg0 i)

end GlobalTheory.PhiGam.Gauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetModNeZeroIff
section
open scoped Classical BigOperators
open IsLocalRing Module Matrix

noncomputable section

namespace GlobalTheory.AdaptedLocalData

section Field

variable {k : Type} [Field k]

theorem card_isCompl [Finite k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (R : Submodule k V) :
    Nat.card {U : Submodule k V // IsCompl R U} =
      Nat.card k ^ (finrank k (V ⧸ R) * finrank k R) := by
  obtain ⟨f₀, hf₀⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  have h₀ : ∀ x : R, f₀ x = x := fun x => LinearMap.congr_fun hf₀ x
  rw [Nat.card_congr R.isComplEquivProj, ← Module.finrank_linearMap k k,
    ← Module.natCard_eq_pow_finrank (K := k)]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨f₀ + g.comp R.mkQ, fun x => by
      have : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).2 x.2
      rw [LinearMap.add_apply, LinearMap.comp_apply, this, map_zero, add_zero, h₀]⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.comp R.mkQ = g'.comp R.mkQ := add_left_cancel (congrArg Subtype.val h)
    exact R.linearMap_qext h1
  · rintro ⟨f, hf⟩
    refine ⟨R.liftQ (f - f₀) fun x hx => ?_, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, hf ⟨x, hx⟩, h₀ ⟨x, hx⟩, sub_self]
    · simp

theorem card_sup_eq_top [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k))
    (hR : finrank k R ≤ r) :
    Nat.card {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} =
      if finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  have key : ∀ U : Submodule k (Fin (r + t) → k), R ⊔ U = ⊤ →
      r + t + finrank k ↥(R ⊓ U) = finrank k R + finrank k U := fun U h => by
    have := Submodule.finrank_sup_add_finrank_inf_eq R U
    rwa [h, finrank_top, finrank_fin_fun] at this
  split_ifs with h
  · have hq : finrank k ((Fin (r + t) → k) ⧸ R) = t := by
      have := R.finrank_quotient_add_finrank
      rw [finrank_fin_fun] at this
      omega
    have := card_isCompl R
    rw [hq, h, mul_comm] at this
    rw [← this]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun U => ⟨fun ⟨h1, h2⟩ => ?_, fun hc => ?_⟩)
    · refine ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 ?_), codisjoint_iff.2 h2⟩
      have := key U h2
      omega
    · have := key U hc.sup_eq_top
      rw [hc.inf_eq_bot, finrank_bot] at this
      exact ⟨by omega, hc.sup_eq_top⟩
  · haveI : IsEmpty {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} :=
      ⟨fun U => by have := key U.1 U.2.2; have := U.2.1; omega⟩
    exact Nat.card_of_isEmpty

end Field

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable [Finite (ResidueField O)]

end Local

end GlobalTheory.AdaptedLocalData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSndStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by
  first | exact @GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | exact GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | (intros; apply GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd <;> assumption)
end

