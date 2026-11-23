module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivationProdPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm GlobalTheory.JointHarm.Minor

namespace GlobalTheory.DeltaHighest

def ext0 {l : ℕ} (a : Fin l → ℕ) (i : ℕ) : ℕ := if h : i < l then a ⟨i, h⟩ else 0

theorem partitionExtendByZero_antitone {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) : Antitone (ext0 a) := by
  intro i j hij
  unfold ext0
  split_ifs with h h'
  · exact ha (by simpa using hij)
  · omega
  · omega
  · omega

def leadProd {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ) :
    MvPolynomial σ ℂ :=
  ∏ i : Fin l, lead z (n := i.1 + 1) (le_trans i.2 h) i.2 ^ (ext0 a i - ext0 a (i + 1))

theorem partition_row_difference_eq_extendByZero_difference {l : ℕ} (a : Fin l → ℕ) (i : Fin l) :
    a i - nextRow a i = ext0 a i - ext0 a (i + 1) := by
  simp [ext0, nextRow]

theorem leadProd_rows {σ : Type} {n l : ℕ} (h : l ≤ n) {a : Fin l → ℕ} (ha : Antitone a)
    (z : Fin n × Fin l → σ) (hz : Function.Injective z) :
    (∀ c d : Fin n, c < d → rowDer z c d (leadProd h a z) = 0) ∧
      ∀ c : Fin n, rowDer z c c (leadProd h a z) = (ext0 a c : ℂ) • leadProd h a z := by
  have := what₂ z hz (ext0 a) (partitionExtendByZero_antitone ha) l (fun i hi => dif_neg (by omega))
    (fun i => le_trans i.2 h) (fun i => i.2)
  simpa only [rowOp_eq_rowDer, leadProd] using this

theorem leadProd_kill {σ : Type} {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) (z : Fin n × Fin l → σ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (hD : ∀ w, D (X (z w)) = 0) :
    D (leadProd h a z) = 0 := by
  rw [leadProd, derivation_prod_pow D _ _ _ (fun _ => 0)]
  · simp
  · intro i
    rw [zero_smul, lead, derivation_det]
    refine Finset.sum_eq_zero fun j _ => Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [Matrix.updateRow_self]
    exact hD _

theorem rowDer_X_other {σ : Type} {n l : ℕ} (z : Fin n × Fin l → σ) (c d : Fin n) (v : σ)
    (hv : ∀ w, z w ≠ v) : rowDer z c d (X v) = 0 := by
  classical
  rw [← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_X_of_ne (hv _).symm, mul_zero]

variable (p q n : ℕ)

def vp : Fin n × Fin p → Ln p q n 0 := fun w => (Sum.inl w.2, Sum.inl w.1)

def vm : Fin n × Fin q → Ln p q n 0 := fun w => (Sum.inr w.2, Sum.inl w.1.rev)

theorem vp_inj : Function.Injective (vp p q n) := fun u w h => by
  simpa [vp, Prod.ext_iff, and_comm] using h

theorem vm_inj : Function.Injective (vm p q n) := fun u w h => by
  simpa [vm, Prod.ext_iff, and_comm] using h

theorem top_eq (h : p ≤ n) (a : Fin p → ℕ) :
    minorProd a (zPlus p q n) (topRows h) = leadProd h a (vp p q n) := by
  unfold minorProd leadProd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference]
  rfl

theorem bot_eq (h : q ≤ n) (a : Fin q → ℕ) :
    ∃ u : ℂ, minorProd a (zMinus p q n) (botRows h) = u • leadProd h a (vm p q n) := by
  refine ⟨∏ i : Fin q, ((Equiv.Perm.sign (Fin.revPerm (n := i.1 + 1)) : ℤ) : ℂ) ^
    (ext0 a i - ext0 a (i + 1)), ?_⟩
  unfold minorProd leadProd
  rw [Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [partition_row_difference_eq_extendByZero_difference, map_pow, ← mul_pow, map_intCast, lead, ← Matrix.det_permute]
  congr 2
  ext1 c b
  simp only [zMinus, vm, Matrix.submatrix_apply, Matrix.of_apply, id]
  congr 3
  apply Fin.ext
  have := i.2
  have := c.2
  simp [botRows, Fin.revPerm, Fin.val_rev]
  omega

theorem act_eq (c d : Fin n) (P : Pol p q n 0) :
    fockAct2 p q n 0 (Eab (.inl c) (.inl d)) P =
      rowDer (vp p q n) c d P - rowDer (vm p q n) d.rev c.rev P +
        (if c = d then ((p : ℂ) - q) / 2 else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, ← rowOp_eq_rowDer,
    ← rowOp_eq_rowDer, GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply]
  simp only [omE_pos_pos (l := (.inl _, .inl c)) (l' := (.inl _, .inl d)) rfl rfl,
    omE_neg_neg (l := (.inr _, .inl c)) (l' := (.inr _, .inl d)) rfl rfl, vp, vm, Fin.rev_rev,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_smul]
  by_cases h : c = d <;> simp [h] <;> module

theorem delta_mem_hwSub : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  intro p q n hn ap am hp hm
  have h1 : p ≤ n := by omega
  have h2 : q ≤ n := by omega
  obtain ⟨u, hu⟩ := bot_eq p q n h2 am
  have e : delta hn ap am = u • (leadProd h1 ap (vp p q n) * leadProd h2 am (vm p q n)) := by
    rw [delta, top_eq, hu, mul_smul_comm]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  have a1 := leadProd_rows h1 hp _ (vp_inj p q n)
  have a2 := leadProd_rows h2 hm _ (vm_inj p q n)
  have k1 : ∀ c d, rowDer (vp p q n) c d (leadProd h2 am (vm p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  have k2 : ∀ c d, rowDer (vm p q n) c d (leadProd h1 ap (vp p q n)) = 0 := fun c d =>
    leadProd_kill _ _ _ _ fun w => rowDer_X_other _ _ _ _ fun w' => by simp [vp, vm]
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Sum.forall,
    posC, IsEmpty.forall_iff, implies_true, and_true, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, act_eq, Derivation.leibniz, k1, k2, a1.2, a2.2, if_true]
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · have hw : ((wtH n ap am (.inl c) : ℚ) : ℂ) =
        (ext0 ap c : ℂ) - (ext0 am c.rev : ℂ) + ((p : ℂ) - q) / 2 := by
      have := c.2
      have hr := c.val_rev
      simp only [wtH, ext0]
      split_ifs with h h' h'
      · omega
      all_goals simp
    rw [hw]
    generalize leadProd h1 ap (vp p q n) = A
    generalize leadProd h2 am (vm p q n) = B
    simp only [mul_zero, zero_add, add_zero, smul_eq_mul, mul_smul_comm, mul_comm B A]
    module
  · rw [a1.1 c d hcd, a2.1 _ _ (Fin.rev_lt_rev.2 hcd), if_neg hcd.ne]
    simp

end GlobalTheory.DeltaHighest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowSlashTPow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.NrmT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem eOm_add' (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply ε.injective
  rw [map_mul, KTExp.map_eOm, KTExp.map_eOm, KTExp.map_eOm, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem eOm_zero' : eOm ε 0 = 1 := (KTExp.eOm_eq_one_iff ε 0).2 rfl

theorem eOm_nat_mul (x : ℚ) (b : ℕ) : eOm ε (x * b) = eOm ε x ^ b := by
  induction b with
  | zero => simp only [Nat.cast_zero, mul_zero, pow_zero]; exact eOm_zero'
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add', ih, pow_succ]

theorem eOm_pow_den (x : ℚ) : eOm ε x ^ x.den = 1 := by
  rw [← eOm_nat_mul, (KTExp.eOm_eq_one_iff ε _).2]
  rw [Rat.mul_den_eq_num]; simp

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {z : Ω} {d : ℕ} (hd : 0 < d) (h : z ^ d = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with hz | hz
  · exact hz
  · have h1 : z * z ^ (d - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hd, h]
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact pow_mem hz _

theorem eOm_mem (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A :=
  mem_of_pow_eq_one A x.den_pos (eOm_pow_den x)

theorem eOm_ne_zero (x : ℚ) : eOm ε x ≠ 0 := by
  intro h
  have := eOm_pow_den (ε := ε) x
  rw [h, zero_pow x.den_nz] at this
  exact zero_ne_one this

theorem eOm_inv_mem (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  have h : eOm ε (-x) * eOm ε x = 1 := by rw [← eOm_add', neg_add_cancel, eOm_zero']
  rw [← eq_inv_of_mul_eq_one_left h]
  exact eOm_mem A _

def trT (ε : Ω →+* ℂ) (b : ℕ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := eOm ε (r * b) * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem trT_coeff (b : ℕ) (φ : HahnSeries ℚ Ω) (r : ℚ) : (trT ε b φ).coeff r = eOm ε (r * b) * φ.coeff r := rfl

theorem trT_support (b : ℕ) (φ : HahnSeries ℚ Ω) : (trT ε b φ).support ⊆ φ.support :=
  fun r hr h => hr (by rw [trT_coeff, h, mul_zero])

theorem coeff_mul_sup {x y : HahnSeries ℚ Ω} {s t : Set ℚ} (hs : s.IsPWO) (ht : t.IsPWO) (hxs : x.support ⊆ s)
    (hyt : y.support ⊆ t) (a : ℚ) :
    (x * y).coeff a = ∑ ij ∈ Finset.addAntidiagonal hs ht a, x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_addAntidiagonal] at hij
    exact Finset.mem_addAntidiagonal.2 ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hn
    by_cases h1 : x.coeff ij.1 = 0
    · rw [h1, zero_mul]
    · by_cases h2 : y.coeff ij.2 = 0
      · rw [h2, mul_zero]
      · exact absurd (Finset.mem_addAntidiagonal.2 ⟨h1, h2, (Finset.mem_addAntidiagonal.1 hij).2.2⟩) hn

theorem trT_mul (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x * y) = trT ε b x * trT ε b y := by
  ext a
  rw [coeff_mul_sup x.isPWO_support y.isPWO_support (trT_support b x) (trT_support b y)]
  simp only [trT_coeff]
  rw [HahnSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.mem_addAntidiagonal] at hij
  rw [← hij.2.2, add_mul, eOm_add']
  ring

theorem trT_sub (b : ℕ) (x y : HahnSeries ℚ Ω) : trT ε b (x - y) = trT ε b x - trT ε b y := by
  ext r
  simp only [trT_coeff, HahnSeries.coeff_sub]
  ring

theorem theta_trT (s : ℚ) (b : ℕ) (φ : HahnSeries ℚ Ω) : theta s (trT ε b φ) = trT ε b (theta s φ) := by
  ext r
  show algebraMap ℚ Ω (s * r) * (eOm ε (r * b) * φ.coeff r) = eOm ε (r * b) * (algebraMap ℚ Ω (s * r) * φ.coeff r)
  ring

theorem modularTowerExp_slAction_T_pow (X : Tower Ω ε) (b : ℕ) (f : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ b)) f) = trT ε b (X.exp f) := by
  obtain ⟨h00, h01, h10, h11⟩ := KTExp.ent_T_pow b
  ext r
  have := X.exp_upper (ofSL (ModularGroup.T ^ b)) h10 f r
  rw [h00, h01, h11, mul_one, div_one, div_one] at this
  rw [trT_coeff]; exact this

theorem cgA_mul (A : ValuationSubring Ω) (l n : ℕ) {c x y : Ω} (hc : c ∈ A) (h : CgA A l n x y) :
    CgA A l n (c * x) (c * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨c * z, mul_mem hc hz, by rw [← mul_sub, e]; ring⟩

theorem prim_trT (A : ValuationSubring Ω) (b : ℕ) {φ : HahnSeries ℚ Ω} (h : Prim A φ) : Prim A (trT ε b φ) := by
  obtain ⟨hi, r, hr0, hru⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hi r), r, ?_, ?_⟩
  · rw [trT_coeff]; exact mul_ne_zero (eOm_ne_zero _) hr0
  · rw [trT_coeff, mul_inv]; exact mul_mem (eOm_inv_mem A _) hru

theorem isLogDerivQExpansionModPrimePow_slash_T_pow (X : Tower Ω ε) (A : ValuationSubring Ω) (l m : ℕ) (s : ℚ) (f : X.K) (φ : HahnSeries ℚ Ω) (b : ℕ)
    (h : IsDl X A l m s f φ) : IsDl X A l m s (X.sl (ofSL (ModularGroup.T ^ b)) f) (trT ε b φ) := by
  obtain ⟨hφ, a, c, κ, hκ, he, ha, hc, hcg⟩ := h
  refine ⟨fun r => mul_mem (eOm_mem A _) (hφ r), X.sl (ofSL (ModularGroup.T ^ b)) a,
    X.sl (ofSL (ModularGroup.T ^ b)) c, κ, hκ, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul (X.sl (ofSL (ModularGroup.T ^ b))) f c, he, map_mul, AlgEquiv.commutes]
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b ha
  · rw [modularTowerExp_slAction_T_pow]; exact prim_trT A b hc
  · intro r
    rw [modularTowerExp_slAction_T_pow, modularTowerExp_slAction_T_pow]
    simp only [theta_trT, ← trT_mul, ← trT_sub]
    simp only [trT_coeff]
    exact cgA_mul A l m (eOm_mem A _) (hcg r)

theorem sum_trT (L : ℕ) (φ : HahnSeries ℚ Ω) (hφ : ∀ r, φ.coeff r ≠ 0 → (r * L).den = 1) (φ' : HahnSeries ℚ Ω)
    (h' : ∀ r : ℚ, φ'.coeff r = if r.den = 1 then φ.coeff r else 0) :
    ∑ b ∈ Finset.range L, trT ε b φ = HahnSeries.C (L : Ω) * φ' := by
  ext r
  rw [HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, h', smul_eq_mul]
  simp only [trT_coeff, eOm_nat_mul]
  rw [← Finset.sum_mul]
  by_cases h0 : φ.coeff r = 0
  · simp [h0]
  · split_ifs with hr
    · have : eOm ε r = 1 := (KTExp.eOm_eq_one_iff ε r).2 hr
      simp [this]
    · have hz1 : eOm ε r ≠ 1 := fun e => hr ((KTExp.eOm_eq_one_iff ε r).1 e)
      have hzL : eOm ε r ^ L = 1 := by rw [← eOm_nat_mul]; exact (KTExp.eOm_eq_one_iff ε _).2 (hφ r h0)
      have hs : ∑ i ∈ Finset.range L, eOm ε r ^ i = 0 := by
        have := geom_sum_mul (eOm ε r) L
        rw [hzL, sub_self] at this
        exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz1)
      rw [hs, zero_mul, mul_zero]

theorem theta_eq_C_mul (s : ℚ) (x : HahnSeries ℚ Ω) : theta s x = HahnSeries.C (algebraMap ℚ Ω s) * theta 1 x := by
  ext r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  show algebraMap ℚ Ω (s * r) * x.coeff r = algebraMap ℚ Ω s * (algebraMap ℚ Ω (1 * r) * x.coeff r)
  rw [one_mul, map_mul]; ring

theorem coeff_mul_mem (A : ValuationSubring Ω) (t : Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, ∃ z ∈ A, x.coeff r = t * z)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : ∃ z ∈ A, (x * y).coeff r = t * z := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_induction _ (fun u => ∃ z ∈ A, u = t * z)
  · rintro u v ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', add_mem hz hz', by ring⟩
  · exact ⟨0, zero_mem A, by ring⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hx ij.1
    exact ⟨z * y.coeff ij.2, mul_mem hz (hy ij.2), by rw [e]; ring⟩

theorem int_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A) (hy : ∀ r, y.coeff r ∈ A)
    (r : ℚ) : (x * y).coeff r ∈ A := by
  obtain ⟨z, hz, e⟩ := coeff_mul_mem A 1 (fun r => ⟨x.coeff r, hx r, (one_mul _).symm⟩) hy r
  rw [e, one_mul]; exact hz

theorem isDl_congr (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (s : ℚ) (F : X.K) (φ ψ : HahnSeries ℚ Ω)
    (h : IsDl X A l n s F φ) (hψ : ∀ r, ψ.coeff r ∈ A) (hc : ∀ r, CgA A l n (ψ.coeff r) (φ.coeff r)) :
    IsDl X A l n s F ψ := by
  obtain ⟨-, a, c, κ, hκ, he, ha, hc', hcg⟩ := h
  refine ⟨hψ, a, c, κ, hκ, he, ha, hc', fun r => ?_⟩
  have hy : ∀ r, (X.exp a * X.exp c).coeff r ∈ A := int_mul A ha.1 hc'.1
  have hx : ∀ r, ∃ z ∈ A, (ψ - φ).coeff r = (l : Ω) ^ n * z := fun r => by
    obtain ⟨z, hz, e⟩ := hc r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub, e]⟩
  obtain ⟨z1, hz1, e1⟩ := coeff_mul_mem A _ hx hy r
  obtain ⟨z2, hz2, e2⟩ := hcg r
  refine ⟨z1 + z2, add_mem hz1 hz2, ?_⟩
  have : ψ * X.exp a * X.exp c = (ψ - φ) * (X.exp a * X.exp c) + φ * X.exp a * X.exp c := by ring
  rw [this, HahnSeries.coeff_add, e1, mul_add, ← e2]; ring

def resZ (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω where
  coeff r := if r.den = 1 then φ.coeff r else 0
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

theorem resZ_coeff (φ : HahnSeries ℚ Ω) (r : ℚ) : (resZ φ).coeff r = if r.den = 1 then φ.coeff r else 0 := rfl

end GlobalTheory.Glue.NrmT
end
end

