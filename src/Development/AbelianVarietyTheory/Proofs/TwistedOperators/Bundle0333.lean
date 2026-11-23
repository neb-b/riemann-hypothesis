module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMean
section
open GlobalTheory.SepPer Finset

namespace GlobalTheory.SepSum

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hsn_eq_norm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hsn X = ‖X‖ := by
  rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.rpow_two]

theorem hsn_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

theorem finrank_mat (n : ℕ) : Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp only [Fintype.card_fin]
  ring

theorem dyadic (x : ℝ) (hx : 0 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 ⌊1 + x⌋₊ ≤ 1 + x ∧ 1 + x < (2 : ℝ) ^ (Nat.log 2 ⌊1 + x⌋₊ + 1) := by
  have h0 : ⌊1 + x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
  constructor
  · have h1 := Nat.pow_log_le_self 2 h0
    have h2 : ((2 ^ Nat.log 2 ⌊1 + x⌋₊ : ℕ) : ℝ) ≤ (⌊1 + x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊1 + x⌋₊
    have h2 : ((⌊1 + x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊1 + x⌋₊).succ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact (Nat.lt_floor_add_one _).trans_le h2

theorem sum_prod_inv_two_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset (ι → ℕ)) :
    ∑ j ∈ T, ∏ v, ((2 : ℝ) ^ j v)⁻¹ ≤ 2 ^ Fintype.card ι := by
  set M := T.sup fun j => univ.sup j
  have hsub : T ⊆ Fintype.piFinset fun _ : ι => range (M + 1) := by
    intro j hj
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_range, Nat.lt_succ_iff]
    exact (le_sup (f := j) (mem_univ v)).trans (le_sup (f := fun j => univ.sup j) hj)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity).trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => range (M + 1)) (fun _ k => ((2 : ℝ) ^ k)⁻¹)]
  calc ∏ v : ι, ∑ k ∈ range (M + 1), ((2 : ℝ) ^ k)⁻¹ ≤ ∏ _v : ι, (2 : ℝ) :=
        prod_le_prod₀ (fun _ _ => by positivity) fun v _ => by
          have := sum_geometric_two_le (M + 1)
          simpa [one_div, inv_pow] using this
    _ = 2 ^ Fintype.card ι := by simp

theorem card_box_le {ι : Type} [Fintype ι] [Nonempty ι] (n : ℕ) (hn : n ≠ 0) (la : ℝ) (hla : 0 < la) (hla1 : la ≤ 1)
    (T : Finset (ι → Matrix (Fin n) (Fin n) ℂ))
    (hT : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v))
    (j : ι → ℕ) (hj : ∀ s ∈ T, ∀ v, hsn (s v) ≤ (2 : ℝ) ^ (j v + 1)) :
    (T.card : ℝ) ≤ 6 ^ (2 * n ^ 2 * Fintype.card ι) * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) *
      (∏ v, (2 : ℝ) ^ j v) ^ (2 * n ^ 2) := by
  set f := Fintype.card ι with hf
  set N := 2 * n ^ 2 with hN
  have hf0 : f ≠ 0 := Fintype.card_ne_zero
  have hN1 : 1 ≤ N := by have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn); omega
  have hP := GlobalTheory.packing_geometric_mean_separated ι (fun _ => Matrix (Fin n) (Fin n) ℂ) N hN1
    (fun _ => finrank_mat n) la (T : Set _) (fun v => (2 : ℝ) ^ (j v + 1)) hla (fun v => by positivity) ?sep
  case sep =>
    intro s hs s' hs' hne
    have h := hT s hs s' hs' hne
    simp only [← hsn_eq_norm]
    calc la = (la ^ f) ^ ((1 : ℝ) / f) := by rw [one_div, Real.pow_rpow_inv_natCast hla.le hf0]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hset : {s ∈ (T : Set (ι → Matrix (Fin n) (Fin n) ℂ)) | ∀ v, ‖s v‖ ≤ (2 : ℝ) ^ (j v + 1)} = (T : Set _) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, and_iff_left_iff_imp]
    intro hs v
    rw [← hsn_eq_norm]
    exact hj s hs v
  have hc := hP.2
  rw [hset, Set.ncard_coe_finset] at hc
  set Pr : ℝ := ∏ v, (2 : ℝ) ^ (j v + 1) with hPr
  have hPr' : Pr = (∏ v, (2 : ℝ) ^ j v) * 2 ^ f := by
    simp only [hPr, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf]
  have hPr1 : 1 ≤ Pr := by
    rw [hPr, Finset.prod_pow_eq_pow_sum]
    exact one_le_pow₀ (by norm_num)
  have hPr0 : 0 ≤ Pr := by linarith
  set G : ℝ := Pr ^ ((1 : ℝ) / f) with hG
  have hGf : G ^ f = Pr := by rw [hG, one_div, Real.rpow_inv_natCast_pow hPr0 hf0]
  have hG1 : 1 ≤ G := Real.one_le_rpow hPr1 (by positivity)
  have h3 : 1 + 2 * G / la ≤ 3 * G / la := by
    have : G ≤ G / la := le_div_self (by linarith) hla hla1
    have e : 3 * G / la = G / la + 2 * G / la := by ring
    rw [e]; linarith
  calc (T.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * f) := hc
    _ ≤ (3 * G / la) ^ (N * f) := pow_le_pow_left₀ (by positivity) h3 _
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * (G ^ f) ^ N := by
      rw [div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul, mul_comm f N]; ring
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * Pr ^ N := by rw [hGf]
    _ = _ := by
      rw [hPr', show (6 : ℝ) = 3 * 2 by norm_num, mul_pow, mul_pow, ← pow_mul]
      ring

theorem sum_weights_le_of_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) →
      ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  intro ι _ _ n
  classical
  refine ⟨6 ^ (2 * n ^ 2 * Fintype.card ι) * 2 ^ Fintype.card ι, by positivity, ?_⟩
  intro la hla hla1 S hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcard : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => funext fun v => Matrix.ext fun i _ => i.elim0
    have hterm : ∀ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * 0 ^ 2 + 1))⁻¹ ≤ (1 : ℝ) := fun s _ =>
      Finset.prod_le_one₀ (fun v _ => by have := hsn_nonneg (s v); positivity)
        fun v _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hsn_nonneg (s v)]))
    calc _ ≤ ∑ s ∈ S, (1 : ℝ) := sum_le_sum hterm
      _ = S.card := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ _ := by
        have : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
        simpa using this
  · set N := 2 * n ^ 2 with hN
    set f := Fintype.card ι with hf
    let jf : (ι → Matrix (Fin n) (Fin n) ℂ) → ι → ℕ := fun s v => Nat.log 2 ⌊1 + hsn (s v)⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := jf) (t := S.image jf) (fun s hs => Finset.mem_image_of_mem jf hs)]
    have hbox : ∀ j ∈ S.image jf, ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤
        6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by
      intro j _
      have hb : ∀ s ∈ S.filter (fun s => jf s = j),
          ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
        intro s hs
        rw [Finset.mem_filter] at hs
        refine prod_le_prod₀ (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => ?_
        have hd := (dyadic _ (hsn_nonneg (s v))).1
        rw [← hs.2]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd _)
      have hcard := card_box_le n hn.ne' la hla hla1 (S.filter (fun s => jf s = j))
        (fun s hs s' hs' hne => hS s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1 hne) j (by
          intro s hs v
          rw [mem_filter] at hs
          have hd := (dyadic _ (hsn_nonneg (s v))).2
          rw [← hs.2]
          linarith)
      calc _ ≤ ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := sum_le_sum hb
        _ = (S.filter (fun s => jf s = j)).card * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (6 ^ (N * f) * la⁻¹ ^ (N * f) * (∏ v, (2 : ℝ) ^ j v) ^ N) * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
          rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun v _ => ?_
          have h2 : ((2 : ℝ) ^ j v) ≠ 0 := by positivity
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2), one_mul]
    calc _ ≤ ∑ j ∈ S.image jf, 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := sum_le_sum hbox
      _ = 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∑ j ∈ S.image jf, ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by rw [mul_sum]
      _ ≤ 6 ^ (N * f) * la⁻¹ ^ (N * f) * 2 ^ f :=
        mul_le_mul_of_nonneg_left (sum_prod_inv_two_le _) (by positivity)
      _ = _ := by ring

end GlobalTheory.SepSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOInvSmulNsmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

variable {D : D7} {S T : HSp D}

theorem cA_incA_inv_natCast (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem symplO_inv_smul_nsmul {m : ℕ} (hm : 0 < m) (y l : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • y) (m • l) = symplO S T y l := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_inv_natCast, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem symplO_inv_smul_swap (m : ℕ) (x u : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • x) u = -symplO S T (incA D ((m : D.host.E)⁻¹) • u) x := by
  rw [GlobalTheory.PlaceModel.symplO_skew S T x (incA D ((m : D.host.E)⁻¹) • u), neg_neg, GlobalTheory.PlaceModel.symplO_smul,
    cA_incA_inv_natCast]

theorem map_infPart_smul (a : AE D) {r : WO S T} (hr : r.map (infPart D) = 0) : (a • r).map (infPart D) = 0 := by
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij ⊢
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hij, mul_zero]

theorem nsmul_inv_smul {m : ℕ} (hm : 0 < m) (x : WO S T) : m • (incA D ((m : D.host.E)⁻¹) • x) = x := by
  rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem psi_shift {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) {r : WO S T} (hr : r ∈ Λ) {x : WO S T} (hx : x ∈ mLat m Λ) :
    ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • x) r) = 1 := by
  obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hx
  rw [GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]
  exact hΛ l hl r hr

def qCharM (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) : AddChar (Qm m Λ) ℂ where
  toFun u := ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r)
  map_zero_eq_one' := psi_shift hm hΛ hr repm_zero_mem
  map_add_eq_mul' a b := by
    have h := psi_shift hm hΛ hr (repm_add_sub a b)
    have e : repm (a + b) = (repm (a + b) - (repm a + repm b)) + repm a + repm b := by abel
    rw [e, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_apply (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) (u : Qm m Λ) :
    qCharM ψ Λ m hm hΛ r hr u = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r) := rfl

theorem qCharM_mk (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) {u : WO S T} (hu : u ∈ Λ) :
    qCharM ψ Λ m hm hΛ r hr (QuotientAddGroup.mk (⟨u, hu⟩ : Λ)) = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • u) r) := by
  rw [qCharM_apply]
  have h := psi_shift hm hΛ hr (repm_mk_sub (m := m) hu)
  have e : repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) =
      (repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) - u) + u := by abel
  rw [e, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_eq_zero_iff {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    {r : WO S T} (hr : r ∈ Λ) : qCharM ψ Λ m hm hΛ r hr = 0 ↔ r ∈ mLat m Λ := by
  constructor
  · intro h0
    have hx : incA D ((m : D.host.E)⁻¹) • r ∈ Λ := by
      refine hmax _ (map_infPart_smul _ (hinf r hr)) fun u hu => ?_
      have h1 := qCharM_mk ψ Λ m hm hΛ r hr hu
      rw [h0, AddChar.zero_apply] at h1
      rw [symplO_inv_smul_swap, AddChar.map_neg_eq_inv, ← h1, inv_one]
    exact mem_mLat.2 ⟨_, hx, nsmul_inv_smul hm r⟩
  · intro hrm
    obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hrm
    refine DFunLike.ext _ _ (fun u => ?_)
    rw [qCharM_apply, AddChar.zero_apply, symplO_inv_smul_nsmul hm]
    exact hΛ _ (repm_mem u) _ hl

theorem charSum_selfAnn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ), 0 < m →
    (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) →
    (∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ) →
    ∀ [Fintype (Qm m Λ)] [DecidableEq (Qm m Λ)] (q : Qm m Λ),
      ∑ u : Qm m Λ, ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) (repm q)) =
        if q = 0 then (Fintype.card (Qm m Λ) : ℂ) else 0 := by
  intro D ψ S T Λ m hm hinf hΛ hmax _ _ q
  have key : qCharM ψ Λ m hm hΛ (repm q) (repm_mem q) = 0 ↔ q = 0 := by
    rw [qCharM_eq_zero_iff hm hinf hΛ hmax (repm_mem q)]
    conv_rhs => rw [← mk_repm q]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  classical
  have hs := AddChar.sum_eq_ite (qCharM ψ Λ m hm hΛ (repm q) (repm_mem q))
  simp only [qCharM_apply, key] at hs
  convert hs
end GlobalTheory.FinDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TensIrr

theorem eq_smul_of_ann {V : Type} [AddCommGroup V] [Module ℂ V] (SV : Set (Module.End ℂ V))
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤)
    (v₀ w : V) (hv₀ : v₀ ≠ 0)
    (h : ∀ a ∈ Algebra.adjoin ℂ SV, a v₀ = 0 → a w = 0) : ∃ c : ℂ, w = c • v₀ := by
  let A := Algebra.adjoin ℂ SV
  let ev : V → (A →ₗ[ℂ] V) := fun y =>
    { toFun := fun a => (a : Module.End ℂ V) y
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hev : ∀ y (a : A), ev y a = (a : Module.End ℂ V) y := fun _ _ => rfl
  have hsurj : Function.Surjective (ev v₀) := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (ev v₀)) (fun s hs x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact ⟨⟨s * a, mul_mem (Algebra.subset_adjoin hs) a.2⟩, rfl⟩) with h0 | h0
    · exfalso; apply hv₀
      have h1 : ev v₀ 1 ∈ LinearMap.range (ev v₀) := LinearMap.mem_range_self _ _
      rw [h0, Submodule.mem_bot] at h1
      simpa [hev] using h1
    · exact h0
  have hker : LinearMap.ker (ev v₀) ≤ LinearMap.ker (ev w) := fun a ha => by
    rw [LinearMap.mem_ker, hev] at ha ⊢
    exact h a a.2 ha
  let φ : Module.End ℂ V := ((LinearMap.ker (ev v₀)).liftQ (ev w) hker).comp
    (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm.toLinearMap
  have hφ : ∀ a : A, φ ((a : Module.End ℂ V) v₀) = (a : Module.End ℂ V) w := by
    intro a
    have h2 : (LinearMap.quotKerEquivOfSurjective (ev v₀) hsurj).symm (ev v₀ a) =
        Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← hev v₀, h2, Submodule.liftQ_apply, hev]
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar SV V (fun s => s.1) hrank
    (fun N hN => hirr N (fun a ha x hx => hN ⟨a, ha⟩ x hx)) φ (fun s => by
      ext y
      obtain ⟨a, rfl⟩ := hsurj y
      have h1 : φ ((s.1 * (a : Module.End ℂ V)) v₀) = (s.1 * (a : Module.End ℂ V)) w :=
        hφ ⟨s.1 * a, mul_mem (Algebra.subset_adjoin s.2) a.2⟩
      simp only [Module.End.mul_apply, hev] at h1 ⊢
      rw [h1, hφ a])
  refine ⟨c, ?_⟩
  have h3 := hφ 1
  simp only [OneMemClass.coe_one, Module.End.one_apply] at h3
  rw [← h3, hc]
  simp

theorem rTensor_mem_adjoin {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (SV : Set (Module.End ℂ V)) (N : Submodule ℂ (V ⊗[ℂ] U))
    (hN : ∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) :
    ∀ a ∈ Algebra.adjoin ℂ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact hN a ha
  | algebraMap r =>
    intro x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.rTensor_smul, Module.End.one_eq_id,
      LinearMap.rTensor_id]
    simpa using N.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact N.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)

theorem tensor_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro V U _ _ _ _ SV SU hrank _ hV hU N hNV hNU
  classical
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x₁, hx₁N, hx₁⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ U
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : ∀ (a : Module.End ℂ V) y j, e (LinearMap.rTensor U a y) j = a (e y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  have hex : ∃ n, ∃ y ∈ N, y ≠ 0 ∧ (e y).support.card = n := ⟨_, x₁, hx₁N, hx₁, rfl⟩
  obtain ⟨x, hxN, hx0, hxc⟩ := Nat.find_spec hex
  have hmin : ∀ y ∈ N, (e y).support.card < (e x).support.card → y = 0 := by
    intro y hy hlt
    by_contra hy0
    exact Nat.find_min hex (hxc ▸ hlt) ⟨y, hy, hy0, rfl⟩
  obtain ⟨j₀, hj₀⟩ : (e x).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    exact (LinearEquiv.map_ne_zero_iff e).mpr hx0
  set v₀ := e x j₀ with hv₀def
  have hv₀ : v₀ ≠ 0 := Finsupp.mem_support_iff.mp hj₀
  have hA := rTensor_mem_adjoin SV N hNV
  have hcol : ∀ j, ∃ c : ℂ, e x j = c • v₀ := by
    intro j
    refine eq_smul_of_ann SV hrank hV v₀ (e x j) hv₀ (fun a ha hav => ?_)
    have hy := hmin _ (hA a ha x hxN) (by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j₀, hj₀, ?_⟩
        rw [Finsupp.mem_support_iff, not_not, he]
        exact hav
      · intro i hi
        rw [Finsupp.mem_support_iff] at hi ⊢
        intro h0
        apply hi
        rw [he, h0, map_zero])
    have h5 := he a x j
    rw [hy, map_zero, Finsupp.zero_apply] at h5
    exact h5.symm
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv₀
  let u : U := b.repr.symm ((e x).mapRange ℓ (map_zero ℓ))
  have hxu : x = v₀ ⊗ₜ u := by
    apply e.injective
    ext j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    simp only [u, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
    obtain ⟨c, hc⟩ := hcol j
    rw [hc, map_smul, hℓ, smul_eq_mul, mul_one]
  have hu : u ≠ 0 := by
    intro hu0
    apply hx0
    rw [hxu, hu0, TensorProduct.tmul_zero]
  have hP : N.comap ((TensorProduct.mk ℂ V U).flip u) = ⊤ := by
    rcases hV (N.comap ((TensorProduct.mk ℂ V U).flip u)) (fun a ha v hv => by
      simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply] at hv ⊢
      have h6 := hNV a ha _ hv
      rwa [LinearMap.rTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : v₀ ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by
        simp only [Submodule.mem_comap, LinearMap.flip_apply, TensorProduct.mk_apply]
        rw [← hxu]; exact hxN
      rw [h0, Submodule.mem_bot] at h7
      exact hv₀ h7
    · exact h0
  have hQ : ∀ v : V, N.comap (TensorProduct.mk ℂ V U v) = ⊤ := by
    intro v
    rcases hU (N.comap (TensorProduct.mk ℂ V U v)) (fun c hc y hy => by
      simp only [Submodule.mem_comap, TensorProduct.mk_apply] at hy ⊢
      have h6 := hNU c hc _ hy
      rwa [LinearMap.lTensor_tmul] at h6) with h0 | h0
    · exfalso
      have h7 : u ∈ N.comap (TensorProduct.mk ℂ V U v) := by
        have h8 : v ∈ N.comap ((TensorProduct.mk ℂ V U).flip u) := by rw [hP]; trivial
        simpa using h8
      rw [h0, Submodule.mem_bot] at h7
      exact hu h7
    · exact h0
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨m, n, rfl⟩
  have h9 : n ∈ N.comap (TensorProduct.mk ℂ V U m) := by rw [hQ m]; trivial
  simpa using h9

end GlobalTheory.TensIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorLatticeMulTransposeStableIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorLattice_mul_transpose_stable_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  first | exact @GlobalTheory.LatStab.latAtV_mul_transpose_iff | exact GlobalTheory.LatStab.latAtV_mul_transpose_iff | (intros; apply GlobalTheory.LatStab.latAtV_mul_transpose_iff <;> assumption)
end

