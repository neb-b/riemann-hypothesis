module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0003
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InClassOfExp
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset
open Formalism.InvariantFactorPaths.G7 (low_sum expSum exp_term sum_triangle eq_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section IntRLemmas

variable {ι K : Type} [Field K] {R : Subring K}

theorem IntR_mul {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => R.mul_mem (hf _) (hg _)

theorem IntR_C {a : K} (ha : a ∈ R) : IntR R (MvPowerSeries.C a : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem

theorem IntR_one : IntR R (1 : MvPowerSeries ι K) := by
  have := IntR_C (ι := ι) R.one_mem
  rwa [map_one] at this

theorem IntR_pow {f : MvPowerSeries ι K} (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact IntR_one
  | succ k ih => rw [pow_succ]; exact IntR_mul ih hf

theorem IntR_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∏ a ∈ s, f a) :=
  Finset.prod_induction f (IntR R) (fun _ _ => IntR_mul) IntR_one h

theorem IntR_mono {R' : Subring K} (h : R ≤ R') {f : MvPowerSeries ι K} (hf : IntR R f) : IntR R' f :=
  fun n => h (hf n)

end IntRLemmas

section Exp

variable {ι K : Type} [Field K]

def expK (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k)

theorem coeff_expK (f : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (expK f) = ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) :=
  rfl

theorem low_expK_sub {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) (M : ℕ) :
    Low M (expK f - expSum f M) := by
  intro d hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, coeff_expK, expSum, map_sum, sub_eq_zero]
  simp only [MvPowerSeries.coeff_C_mul]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_
  rw [low_pow ((low_one_iff _).2 hf) k d (by simp only [mem_range] at hk; omega), mul_zero]

theorem expK_add [CharZero K] {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    expK (a + b) = expK a * expK b := by
  have hab : MvPowerSeries.constantCoeff (a + b) = 0 := by rw [map_add (f := _), ha, hb, add_zero]
  have la := (low_one_iff _).2 ha
  have lb := (low_one_iff _).2 hb
  refine eq_of_low fun M => ?_
  have h3 : Low M (expSum a M * expSum b M - expSum (a + b) M) := by
    have e : expSum (a + b) M = ∑ k ∈ range M, ∑ l ∈ range (M - k),
        (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l) := by
      unfold expSum
      rw [Finset.sum_congr rfl fun i _ => exp_term a b i]
      exact sum_triangle (fun k l => (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) M
    rw [e]
    unfold expSum
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine low_sum _ _ _ fun k _ => ?_
    rw [Finset.mul_sum]
    intro d hd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, map_sum, sub_eq_zero]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun l _ hl => ?_
    have hkl : Low (k + l) ((MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) := by
      simpa using low_mul (low_mul (low_zero (MvPowerSeries.C ((k.factorial : K)⁻¹))) (low_pow la k))
        (low_mul (low_zero (MvPowerSeries.C ((l.factorial : K)⁻¹))) (low_pow lb l))
    exact hkl d (by simp only [mem_range] at hl; omega)
  have e : expK (a + b) - expK a * expK b = (expK (a + b) - expSum (a + b) M) -
      ((expK a - expSum a M) * expK b + expSum a M * (expK b - expSum b M) +
        (expSum a M * expSum b M - expSum (a + b) M)) := by ring
  rw [e]
  refine low_sub (low_expK_sub hab M) (low_add (low_add ?_ ?_) h3)
  · simpa using low_mul (low_expK_sub ha M) (low_zero (expK b))
  · simpa using low_mul (low_zero (expSum a M)) (low_expK_sub hb M)

theorem IntR_expK {R : Subring K} {c : K} (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    {G : MvPowerSeries ι K} (hG : IntR R G) : IntR R (expK (MvPowerSeries.C c * G)) := by
  intro n
  rw [coeff_expK]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, ← mul_assoc, mul_comm _ (c ^ k)]
  exact R.mul_mem (hc k) (IntR_pow hG k n)

theorem low_prod_sub {Pl : Type} (s : Finset Pl) (a a' : Pl → MvPowerSeries ι K) (M : ℕ)
    (h : ∀ v ∈ s, Low M (a v - a' v)) : Low M (∏ v ∈ s, a v - ∏ v ∈ s, a' v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, sub_self]
    intro d _
    simp
  | insert v s hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv]
    exact low_mul_sub (h v (Finset.mem_insert_self _ _)) (ih fun v' hv' => h v' (Finset.mem_insert_of_mem hv'))

theorem neg_pow_mem {R : Subring K} {c : K} (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R) (k : ℕ) :
    (-c) ^ k * ((k.factorial : K))⁻¹ ∈ R := by
  rw [neg_pow, mul_assoc]
  exact R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) k) (hc k)

theorem term_exp {pp c : K} (hpp : pp ≠ 0) (h : MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((i.factorial : K)⁻¹) * (-(MvPowerSeries.C (c / pp) * h)) ^ i =
      MvPowerSeries.C ((pp ^ i)⁻¹) * h ^ i * MvPowerSeries.C ((-c) ^ i * ((i.factorial : K))⁻¹) := by
  have e : -(MvPowerSeries.C (c / pp) * h) = MvPowerSeries.C (-c / pp) * h := by
    rw [neg_div, map_neg, neg_mul]
  rw [e, mul_pow, ← map_pow]
  have e2 : (MvPowerSeries.C ((-c / pp) ^ i) : MvPowerSeries ι K) =
      MvPowerSeries.C ((pp ^ i)⁻¹) * MvPowerSeries.C ((-c) ^ i) := by
    rw [← map_mul]
    congr 1
    rw [div_pow, div_eq_mul_inv, mul_comm]
  rw [e2, map_mul]
  ring

theorem inClass_of_exp {R : Subring K} {pp c : K} (hpp : pp ≠ 0) (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    (h : MvPowerSeries ι K) (h0 : MvPowerSeries.constantCoeff h = 0) {V : MvPowerSeries ι K} (hV : IntR R V) :
    ∃ g : ℕ → MvPowerSeries ι K, (∀ i, IntR R (g i)) ∧ ∀ n : ι →₀ ℕ,
      MvPowerSeries.coeff n (expK (-(MvPowerSeries.C (c / pp) * h)) * V) =
        ∑ i ∈ range (n.degree + 1), ((pp ^ i)⁻¹ * MvPowerSeries.coeff n (h ^ i * g i)) := by
  refine ⟨fun i => MvPowerSeries.C ((-c) ^ i * ((i.factorial : K))⁻¹) * V,
    fun i => IntR_mul (IntR_C (neg_pow_mem hc i)) hV, fun n => ?_⟩
  have hx : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (c / pp) * h)) = 0 := by
    rw [map_neg, map_mul, h0, mul_zero, neg_zero]
  have h1 : Low (n.degree + 1) ((expK (-(MvPowerSeries.C (c / pp) * h)) -
      expSum (-(MvPowerSeries.C (c / pp) * h)) (n.degree + 1)) * V) := by
    simpa using low_mul (low_expK_sub hx (n.degree + 1)) (low_zero V)
  have h2 := h1 n (by omega)
  rw [sub_mul, map_sub, sub_eq_zero] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, expSum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term_exp hpp, ← MvPowerSeries.coeff_C_mul]
  congr 1
  ring

theorem inProd_of_exp {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : Subring K} {pp c : K} (hpp : pp ≠ 0)
    (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    (h : Pl → MvPowerSeries ι K) (h0 : ∀ v, MvPowerSeries.constantCoeff (h v) = 0) {V : MvPowerSeries ι K}
    (hV : IntR R V) :
    ∃ g : (Pl → ℕ) → MvPowerSeries ι K, (∀ i, IntR R (g i)) ∧ ∀ α : ι →₀ ℕ,
      MvPowerSeries.coeff α ((∏ v, expK (-(MvPowerSeries.C (c / pp) * h v))) * V) =
        ∑ i ∈ Fintype.piFinset (fun _ : Pl => range (α.degree + 1)),
          MvPowerSeries.coeff α (MvPowerSeries.C (∏ v, (pp ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i) := by
  refine ⟨fun i => MvPowerSeries.C (∏ v, ((-c) ^ i v * (((i v).factorial : K))⁻¹)) * V,
    fun i => IntR_mul (IntR_C (Subring.prod_mem _ fun v _ => neg_pow_mem hc (i v))) hV, fun α => ?_⟩
  have hx : ∀ v, MvPowerSeries.constantCoeff (-(MvPowerSeries.C (c / pp) * h v)) = 0 := fun v => by
    rw [map_neg, map_mul, h0, mul_zero, neg_zero]
  have h1 : Low (α.degree + 1) ((∏ v, expK (-(MvPowerSeries.C (c / pp) * h v)) -
      ∏ v, expSum (-(MvPowerSeries.C (c / pp) * h v)) (α.degree + 1)) * V) := by
    simpa using low_mul (low_prod_sub univ _ _ (α.degree + 1) fun v _ => low_expK_sub (hx v) (α.degree + 1))
      (low_zero V)
  have h2 := h1 α (by omega)
  rw [sub_mul, map_sub, sub_eq_zero] at h2
  rw [h2]
  unfold expSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_univ_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.prod_congr rfl fun v _ => term_exp hpp (h v) (i v), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  simp only [map_prod]
  ring

end Exp

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InLatCSmulC
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem inLatC_sum {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {κ : Type*} (s : Finset κ) (f : κ → XspC (X.Pj j) Y.Kc)
    (h : ∀ k ∈ s, Y.inLatC j g L (f k)) : Y.inLatC j g L (∑ k ∈ s, f k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  exact AddSubgroup.sum_mem _ h

theorem inLatC_smulC {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (b : Y.Kc) (k : ℤ)
    (hb : b * (p : Y.Kc) ^ k ∈ Y.Oc) {y : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y) :
    Y.inLatC j (g - k) L (b • y) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  have hm := AddSubgroup.mem_map_of_mem (DistribSMul.toAddMonoidHom (XspC (X.Pj j) Y.Kc) b) h
  rw [AddMonoidHom.map_closure] at hm
  refine AddSubgroup.closure_mono ?_ hm
  rintro _ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩
  exact ⟨b * a, geC_mul_shift (Y := Y) k ha hb, z, hz, by simp [smul_smul]⟩

theorem inLatC_rep {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {y' : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y') :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Y.Kc) (z : κ → (X.Pj j).Xsp), (∀ k, Y.geC (a k) g) ∧
      (∀ k, z k ∈ (X.Pj j).HtupW L) ∧ y' = ∑ k, a k • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (z k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => a, fun _ => z, fun _ => ha, fun _ => hz, by simp⟩
  | zero =>
    exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun k => k.elim, fun k => k.elim, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    obtain ⟨κ2, i2, a2, z2, ha2, hz2, rfl⟩ := hy
    refine ⟨κ1 ⊕ κ2, inferInstance, Sum.elim a1 a2, Sum.elim z1 z2, ?_, ?_, ?_⟩
    · rintro (k | k)
      exacts [ha1 k, ha2 k]
    · rintro (k | k)
      exacts [hz1 k, hz2 k]
    · rw [Fintype.sum_sum_type]
      rfl
  | neg x _ hx =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    refine ⟨κ1, i1, fun k => -a1 k, z1, fun k => geC_neg (Y := Y) (ha1 k), hz1, ?_⟩
    simp [neg_smul]

theorem descent {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (y : (X.Pj j).Xsp)
    (h : Y.inLatC j g L (MvPolynomial.map (algebraMap X.G.Kf Y.Kc) y)) :
    y ∈ scale (X.vsc g) ((X.Pj j).HtupW L) := by
  classical
  obtain ⟨κ, _, a, z, ha, hz, hy⟩ := inLatC_rep Y h
  obtain ⟨c, hc, hyc⟩ := descent_core (K := X.G.Kf) (Kc := Y.Kc) (V := (X.Pj j).Xsp) (Vc := XspC (X.Pj j) Y.Kc)
    (MvPolynomial.map (algebraMap X.G.Kf Y.Kc)).toAddMonoidHom
    (by
      intro c v
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C])
    (fun m => MvPolynomial.lcoeff X.G.Kf m) (fun m => MvPolynomial.lcoeff Y.Kc m)
    (by intro m v; simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map])
    (by
      intro v hv
      ext m
      simpa [MvPolynomial.lcoeff_apply] using hv m)
    (RK X) (RK_val Y) (geCgrp Y g)
    (by
      intro r hr a ha
      exact geC_mul_Oc Y ha ((mem_RK_iff Y).mp hr))
    (Finset.univ : Finset κ).card Finset.univ rfl z a (fun k _ => ha k) y hy
  rw [hyc]
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 := vGeK_of_geC Y (c k) g (hc k (Finset.mem_univ k))
  unfold Sys.vGeK at h1
  rw [mem_scale_iff] at h1
  obtain ⟨o, ho, hok⟩ := h1
  obtain ⟨t, rfl⟩ := mem_intKF.mp ho
  rw [mem_scale_iff]
  refine ⟨t • z k, Submodule.smul_mem _ _ (hz k), ?_⟩
  rw [← hok, smul_eq_mul, mul_smul, algebraMap_smul]

theorem natInv_mem (m : ℕ) (hm : ¬ p ∣ m) : ((m : Y.Kc))⁻¹ ∈ Y.Oc := by
  have hk : ((m : kb p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (kb p) p]
    exact hm

  have hu : IsUnit ((m : WW p)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have hc : WittVector.constantCoeff ((m : WW p)) = (m : kb p) := map_natCast _ m
    change WittVector.constantCoeff ((m : WW p)) ≠ 0
    rw [hc]
    exact hk
  obtain ⟨u, hu⟩ := hu
  have h1 : algebraMap (K0 p) Y.Kc (algebraMap (WW p) (K0 p) (↑u⁻¹ : WW p)) * (m : Y.Kc) = 1 := by
    rw [← map_natCast (algebraMap (K0 p) Y.Kc), ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul,
      ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Y.witt_mem_integers_Cp _

theorem wt_inv (N d : ℕ) (hpos : 0 < N) (hle : padicValNat p N ≤ d) :
    ((N : Y.Kc))⁻¹ * (p : Y.Kc) ^ ((d : ℕ) : ℤ) ∈ Y.Oc := by
  have hpp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hpp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have he : e ≤ d := by
    have hv : padicValNat p (p ^ e * m) = e := by
      rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hpp.ne_zero) hm0,
        Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
    omega
  have hp := pKc_ne (Y := Y)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have key : ((p ^ e * m : ℕ) : Y.Kc)⁻¹ * (p : Y.Kc) ^ (((e + k : ℕ)) : ℤ) = ((m : Y.Kc))⁻¹ * (p : Y.Kc) ^ k := by
    rw [zpow_natCast, pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((p : Y.Kc) ^ e)⁻¹),
      mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hp)]
  rw [key]
  exact Y.Oc.mul_mem (natInv_mem Y m hm) (Y.Oc.pow_mem (natCast_mem Y.Oc p) _)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

