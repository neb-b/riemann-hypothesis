module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0006
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundOfDualFamilies
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Val

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}

theorem vK_one (p : ℕ) : vK p (1 : KK O) = 0 := by
  have h := valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero
  rw [map_one] at h
  rw [h, dvr_order_unit_eq_zero isUnit_one]
  simp

theorem vK_npow {x : KK O} {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (n : ℕ) :
    vK p (x ^ n) = (((n : ℚ) * q : ℚ) : WithTop ℚ) := by
  induction n with
  | zero => rw [pow_zero, vK_one]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, hx, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem vK_inv' {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) :
    vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have h := valuation_mul_alt (O := O) p x x⁻¹
  rw [mul_inv_cancel₀ hx0, vK_one, hx] at h
  cases ht : vK p x⁻¹ with
  | top => rw [ht] at h; simp at h
  | coe t =>
    rw [ht, ← WithTop.coe_add] at h
    have : q + t = 0 := by exact_mod_cast h.symm
    congr 1
    linarith

theorem vK_zpow {x : KK O} (hx0 : x ≠ 0) {q : ℚ} (hx : vK p x = (q : WithTop ℚ)) (k : ℤ) :
    vK p (x ^ k) = (((k : ℚ) * q : ℚ) : WithTop ℚ) := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, vK_npow hx]; push_cast; rfl
  | negSucc n =>
    rw [zpow_negSucc, vK_inv' (pow_ne_zero _ hx0) (vK_npow hx (n + 1))]
    congr 1
    push_cast
    ring

end Val

section FockMap

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fock_map (ι : ℚ_[p] →+* KK O) {σ : Type} (F G : MvPolynomial σ ℚ_[p]) :
    fock (map ι F) (map ι G) = ι (Formalism.GM.M.fockK F G) := by
  classical
  unfold fock Formalism.GM.M.fockK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [support_map_of_injective _ ι.injective, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, coeff_map, map_mul, map_mul]
  congr 1
  unfold expFact
  simp only [Finsupp.prod, Nat.cast_prod, map_prod, map_natCast]

theorem fock_smul_both {σ : Type} (a : KK O) (A B : MvPolynomial σ (KK O)) :
    fock (a • A) (a • B) = a * (a * fock A B) := by
  rw [fock_form_smul_right, fock_form_symm, fock_form_smul_right, fock_form_symm B A, smul_eq_mul, smul_eq_mul]

end FockMap

section Assemble

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem specConst_ne_zero {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) : specConst p S b ≠ 0 := by
  unfold specConst
  rw [Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  · exact one_ne_zero

theorem ramE_eq_two : ramE X.p X.O = 2 := by
  have h2 : X.setting.w ^ 2 = (X.p : X.O) := Formalism.MainNotions.G.dvrOfStd_sq X.std
  have : ramE X.p X.O = dvrOrderNat (X.p : X.O) := rfl
  rw [this, ← h2, dvr_order_pow X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr]

theorem vK_w : vK X.p (algebraMap X.O (KK X.O) X.setting.w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  rw [valuation_algebraMap_eq_alt X.p _ X.setting.w_irr.ne_zero, nv_irr' X.setting.w_irr, ramE_eq_two]
  simp

theorem vK_p : vK X.p ((X.p : ℕ) : KK X.O) = ((1 : ℚ) : WithTop ℚ) := by
  rw [valuation_natCast_padicVal X.std.1.prime X.setting X.p X.std.1.prime.ne_zero, Nat.padicValNat_def, Nat.Prime.multiplicity_self]
  simp

theorem coeff_of_int {p : ℕ} [Fact p.Prime] {σ : Type} (F : MvPolynomial σ ℚ_[p]) (hF : F ∈ Formalism.GM.M.IntPol p σ)
    (v : σ →₀ ℕ) : ∃ c : ℤ_[p], F.coeff v = (c : ℚ_[p]) := by
  obtain ⟨F0, rfl⟩ := hF
  refine ⟨F0.coeff v, ?_⟩
  simp [MvPolynomial.coeff_map]

theorem block_dual_family_bound (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) (D : ℤ) (n : ℕ)
    (x y : Fin n → MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p]) (e : ℤ)
    (hx : ∀ i, x i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hy : ∀ i, y i ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r))
    (hxy : ∀ i j, Formalism.GM.M.fockK (x i) (y j) = if i = j then (X.p : ℚ_[X.p]) ^ e else 0)
    (hmon : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) → ∀ μ ∈ z.support,
        (e : ℝ) ≤ (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + D + levelPassageLoss X) :
    ∃ L₂ : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      GoodSub X.p (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b)
        (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) L₂ ((D : ℝ) + levelPassageLoss X) ∧
      n ≤ Module.finrank X.O L₂ := by
  have hint := iotaX_int X
  set ι := iotaX X with hι
  set sp := specConst X.p (X.S C0 CE1 CE2) b with hsp
  set F : ℤ := ⌊(D : ℝ) + levelPassageLoss X⌋ with hF
  set k : ℤ := F - e - (padicValNat X.p sp : ℤ) with hk'
  set wK : KK X.O := algebraMap X.O (KK X.O) X.setting.w with hwK
  have hw0 : wK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective X.O (KK X.O))).2 X.setting.w_irr.ne_zero
  set lam : KK X.O := wK ^ k with hlam
  have hvlam : vK X.p lam = ((((k : ℚ) * (1 / 2)) : ℚ) : WithTop ℚ) := vK_zpow hw0 (vK_w X) k

  have hmemL : ∀ z : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) ℚ_[X.p],
      z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) →
      lam • map ι z ∈ blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show lam • map ι z ∈ Submodule.span (KK X.O) _
      exact Submodule.smul_mem _ _ (map_SSZ hint (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) z hz)
    · have hzi : z ∈ Formalism.GM.M.IntPol X.p (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) :=
        SSZ_int (gB C0 CE1 CE2 X aTop aPlus b) z hz
      rw [MvPolynomial.as_sum (lam • map ι z)]
      refine Submodule.sum_mem _ fun v hv => Submodule.subset_span ⟨v, _, ?_, rfl⟩
      have hcv : (lam • map ι z).coeff v = lam * ι (z.coeff v) := by
        rw [coeff_smul, coeff_map, smul_eq_mul]
      have hzv : z.coeff v ≠ 0 := by
        intro h0
        rw [MvPolynomial.mem_support_iff, hcv, h0, map_zero, mul_zero] at hv
        exact hv rfl
      have hvz : v ∈ z.support := MvPolynomial.mem_support_iff.2 hzv
      have hm := hmon z hz v hvz
      obtain ⟨c0, hc0⟩ := coeff_of_int z hzi v
      obtain ⟨o, ho⟩ := hint c0
      have hcz : ι (z.coeff v) = algebraMap X.O (KK X.O) o := by rw [hc0]; exact ho
      have ho0 : (0 : WithTop ℚ) ≤ vK X.p (algebraMap X.O (KK X.O) o) :=
        (valuation_nonneg_iff_integral X.setting _).2 ⟨o, rfl⟩
      rw [hcv, valuation_mul_alt, hvlam, hcz]
      have hint2 : (0 : ℤ) ≤ k + (padicValNat X.p (expFact v) : ℤ) + (padicValNat X.p sp : ℤ) := by
        have h1 : e - (padicValNat X.p (expFact v) : ℤ) ≤ F := by
          rw [hF]
          apply Int.le_floor.2
          simp only [Int.cast_sub, Int.cast_natCast]
          have : (e : ℝ) ≤ (padicValNat X.p (expFact v) : ℝ) + D + levelPassageLoss X := hm
          linarith
        rw [hk']
        omega
      cases hvo : vK X.p (algebraMap X.O (KK X.O) o) with
      | top => simp
      | coe t =>
        rw [hvo] at ho0
        have ht : (0 : ℚ) ≤ t := by exact_mod_cast ho0
        rw [← WithTop.coe_add, ← WithTop.coe_add]
        have hq : (0 : ℚ) ≤ (k : ℚ) + (padicValNat X.p (expFact v) : ℚ) + (padicValNat X.p sp : ℚ) := by
          have h5 := (Int.cast_le (R := ℚ)).2 hint2
          simpa only [Int.cast_add, Int.cast_zero, Int.cast_natCast] using h5
        exact_mod_cast (show (0 : ℚ) ≤ (k : ℚ) * (1 / 2) + t +
          ((padicValNat X.p (expFact v) : ℚ) / 2 + (padicValNat X.p sp : ℚ) / 2) by linarith)

  set c : KK X.O := (sp : KK X.O) * (lam * (lam * ι ((X.p : ℚ_[X.p]) ^ e))) with hc
  have hform : ∀ i j, blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (lam • map ι (x i)) (lam • map ι (y j)) = if i = j then c else 0 := by
    intro i j
    unfold blockForm
    rw [fock_smul_both, fock_map, hxy]
    split_ifs
    · rfl
    · simp
  have hvc : vLE X.p c ((D : ℝ) + levelPassageLoss X) := by
    have hsp0 : sp ≠ 0 := specConst_ne_zero X.p (X.S C0 CE1 CE2) b
    have hpe : ι ((X.p : ℚ_[X.p]) ^ e) = ((X.p : ℕ) : KK X.O) ^ e := by
      rw [map_zpow₀, map_natCast]
    have hp0 : ((X.p : ℕ) : KK X.O) ≠ 0 := by
      have := (vK_p X)
      intro h0
      rw [h0, valuation_zero_alt] at this
      exact WithTop.top_ne_coe this
    refine ⟨(padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)), ?_, ?_⟩
    · rw [hc, valuation_mul_alt, valuation_mul_alt, valuation_mul_alt, hpe, vK_zpow hp0 (vK_p X) e, hvlam,
        valuation_natCast_padicVal X.std.1.prime X.setting sp hsp0]
      simp only [← WithTop.coe_add]
    · have h1 : (padicValNat X.p sp : ℚ) + ((k : ℚ) * (1 / 2) + ((k : ℚ) * (1 / 2) + (e : ℚ) * 1)) = (F : ℚ) := by
        rw [hk']; simp only [Int.cast_sub, Int.cast_natCast]; ring
      rw [h1, hF]
      have := Int.floor_le ((D : ℝ) + levelPassageLoss X)
      exact_mod_cast this
  have hsm : ∀ (a : KK X.O) (u v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (a • u) v = a * blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v := by
    intro a u v
    unfold blockForm
    rw [fock_form_symm, fock_form_smul_right, fock_form_symm v u, smul_eq_mul]
    ring
  have hadd : ∀ (u u' v : MvPolynomial (BVar (2 * X.s + 1) X.r (X.S C0 CE1 CE2).t) (KK X.O)),
      blockForm X.O X.p X.r (X.S C0 CE1 CE2) b (u + u') v = blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u v + blockForm X.O X.p X.r (X.S C0 CE1 CE2) b u' v := by
    intro u u' v
    unfold blockForm
    rw [fock_form_symm, fock_form_add_right, fock_form_symm v u, fock_form_symm v u']
    ring
  exact goodSub_of_dual X.setting (blockForm X.O X.p X.r (X.S C0 CE1 CE2) b) hsm hadd
    (blockLat X.O X.p X.r (X.S C0 CE1 CE2) aTop aPlus X.m b) (fun i => lam • map ι (x i)) (fun i => lam • map ι (y i))
    (fun i => hmemL _ (hx i)) (fun i => hmemL _ (hy i)) c hform _ hvc

theorem block_bound_of_dual_families (hZ : BlockBoundIntegers C0 CE1 CE2 X) (hdim : RestBCdim C0 CE1 CE2 X) : BlockBoundUniformiser C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk D hD
  obtain ⟨n, x, y, e, hx, hy, hxy, hmon, hrk⟩ := hZ aTop hT aPlus hP b hk D hD
  obtain ⟨L₂, hg, hn⟩ := block_dual_family_bound C0 CE1 CE2 X aTop aPlus b D n x y e hx hy hxy hmon
  exact ⟨L₂, hg, (hdim aTop hT aPlus hP b hk).trans (hrk.trans (Nat.add_le_add_right hn _))⟩

end Assemble

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DegSubSingle
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Comm

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem pderiv_glAct (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c' d' : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    pderiv (a, c) (M.glAct p LL J c' d' x) = M.glAct p LL J c' d' (pderiv (a, c) x) +
      (if (a : ℕ) < J then
        (if LL.vec a then (if c = c' then pderiv (a, d') x else 0) else (if c = d' then -pderiv (a, c') x else 0))
       else 0) := by
  classical
  have hcomm : ∀ (u v : Fin N × Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      pderiv u (pderiv v y) = pderiv v (pderiv u y) := by
    intro u v y
    refine MvPolynomial.induction_on' y (fun s b => ?_) (fun q q' hq hq' => ?_)
    · simp only [pderiv_monomial]
      by_cases huv : u = v
      · subst huv
        rfl
      · have h1 : (s - Finsupp.single v 1 : Fin N × Fin r →₀ ℕ) u = s u := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm huv), Nat.sub_zero]
        have h2 : (s - Finsupp.single u 1 : Fin N × Fin r →₀ ℕ) v = s v := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg huv, Nat.sub_zero]
        rw [h1, h2, tsub_right_comm, mul_assoc, mul_assoc, mul_comm ((s u : ℚ_[p]))]
    · simp only [map_add (f := _), hq, hq']
  have hg : ∀ y, M.glAct p LL J c' d' y = ∑ i : Fin N, (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') y else -(X (i, d') * pderiv (i, c') y)) else 0) := by
    intro y
    simp only [M.glAct, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have key : ∀ i : Fin N, pderiv (a, c) (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') x else -(X (i, d') * pderiv (i, c') x)) else 0) =
      (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') (pderiv (a, c) x)
        else -(X (i, d') * pderiv (i, c') (pderiv (a, c) x))) else 0) +
      (if a = i then (if (i : ℕ) < J then (if LL.vec i then (if c = c' then pderiv (i, d') x else 0)
        else (if c = d' then -pderiv (i, c') x else 0)) else 0) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < J
    · by_cases hv : LL.vec i
      · simp only [hi, hv, if_true, pderiv_mul, pderiv_X, Pi.single_apply]
        rw [hcomm (a, c) (i, d') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcc : c = c'
          · subst hcc
            simp
            try abel
          · simp [hcc, Ne.symm hcc]
        · have hne : (i, c') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
      · simp only [hi, hv, if_true, Bool.false_eq_true, if_false, map_neg, pderiv_mul, pderiv_X,
          Pi.single_apply]
        rw [hcomm (a, c) (i, c') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcd : c = d'
          · subst hcd
            simp
            try abel
          · simp [hcd, Ne.symm hcd]
        · have hne : (i, d') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
    · simp [hi]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hg, hg, map_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq]
  simp

theorem pderiv_keep {σ : Type} (v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → m - Finsupp.single v 1 ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, pderiv v x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  have hx' := (mem_restrictSupport_iff ℚ_[p]).mp hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmv : m v = 0
  · simp [hmv]
  · rw [mem_restrictSupport_iff]
    intro m' hm'
    have h1 := support_monomial_subset hm'
    rw [Finset.mem_singleton] at h1
    rw [h1]
    exact h m (hx' hm) (Nat.one_le_iff_ne_zero.mpr hmv)

theorem wt_sub_single (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c0 : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (h : 1 ≤ m (a, c)) :
    M.wt LL J c0 (m - Finsupp.single (a, c) 1) =
      M.wt LL J c0 m - (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then 1 else -1) else 0) := by
  have key : ∀ i, (((m - Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ)) (i, c0) : ℤ) =
      (m (i, c0) : ℤ) - (if i = a ∧ c = c0 then 1 else 0) := by
    intro i
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hh : i = a ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hh
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Nat.cast_sub h]
      simp
    · rw [if_neg, if_neg hh]
      · simp
      · intro h'
        apply hh
        simp only [Prod.mk.injEq] at h'
        exact ⟨h'.1.symm, h'.2⟩
  unfold M.wt
  simp only [key]
  rw [show (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then (1 : ℤ) else -1) else 0) =
      ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then (if i = a ∧ c = c0 then (1 : ℤ) else 0)
        else -(if i = a ∧ c = c0 then 1 else 0)) else 0) from ?_]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  · rw [Finset.sum_eq_single a]
    · by_cases h1 : (a : ℕ) < J <;> by_cases h2 : c = c0 <;> by_cases h3 : LL.vec a <;> simp [h1, h2, h3]
    · intro b _ hb
      simp [hb]
    · simp

variable [NeZero r]

theorem ycond_vec (LL LL' : M.Letters N) (h : LL.vec = LL'.vec) (J : ℕ) (Mt : WithTop ℤ) :
    M.YCond p (r := r) LL J Mt = M.YCond p (r := r) LL' J Mt := by
  obtain ⟨v, d⟩ := LL
  obtain ⟨v', d'⟩ := LL'
  simp only at h
  subst h
  rfl

theorem pderiv_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (a : Fin N) (hva : (a : ℕ) < J → LL.vec a = true)
    (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    pderiv (a, c) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
      S' = Submodule.span ℚ_[p] {z | ∃ (c'' : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
        y ∈ M.YCond p (r := r) LL J Mt ∧ z = pderiv (a, c'') y} := ⟨_, rfl⟩
  have hgen : ∀ (c'' : Fin r) y, y ∈ M.YCond p (r := r) LL J Mt → pderiv (a, c'') y ∈ S' := by
    intro c'' y hy
    rw [hS']
    exact Submodule.subset_span ⟨c'', y, hy, rfl⟩
  have hsupp : S' ≤ MvPolynomial.restrictSupport ℚ_[p]
      {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨c'', y, hy, rfl⟩
    refine pderiv_keep (a, c'') _ _ ?_ y (Formalism.CountingSumsFrames.ycond_le_supp LL J Mt hy)
    intro m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [wt_sub_single LL J a c'' 0 m h1]
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    by_cases ha : (a : ℕ) < J
    · have hv := hva ha
      by_cases hc : c'' = 0 <;> simp [ha, hv, hc]
    · simp [ha]
  have hstab : M.GlStable p LL J S' := by
    intro c d z hz
    rw [hS'] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c'', y, hy, rfl⟩ := hz
      have e := pderiv_glAct LL J a c'' c d y
      have hy' : M.glAct p LL J c d y ∈ M.YCond p (r := r) LL J Mt :=
        Formalism.CountingSumsFrames.ycond_glStable LL J Mt c d y hy
      have hext : (if (a : ℕ) < J then
          (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) ∈ S' := by
        split_ifs
        · exact hgen d y hy
        · exact S'.zero_mem
        · exact S'.neg_mem (hgen c y hy)
        · exact S'.zero_mem
        · exact S'.zero_mem
      rw [show M.glAct p LL J c d (pderiv (a, c'') y) = pderiv (a, c'') (M.glAct p LL J c d y) -
        (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) by rw [e]; abel]
      exact S'.sub_mem (hgen c'' _ hy') hext
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add (f := _)]
      exact S'.add_mem hz hz'
    | smul t z _ hz =>
      rw [map_smul]
      exact S'.smul_mem t hz
  have hle : S' ≤ M.YCond p (r := r) LL J Mt := by
    unfold M.YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (hgen c x hx)

theorem tieF_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (W E : Fin N) (hW : (W : ℕ) < J) (hE : (E : ℕ) < J)
    (hvW : LL.vec W = true) (hvE : LL.vec E = false)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    tieF (fun c => (W, c)) (fun c => (E, c)) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  have ht : ∀ y : MvPolynomial (Fin N × Fin r) ℚ_[p], tieF (fun c => (W, c)) (fun c => (E, c)) y =
      ∑ c0 : Fin r, pderiv (W, c0) (pderiv (E, c0) y) := by
    intro y
    simp [tieF, LinearMap.sum_apply]
  refine Formalism.CountingSumsFrames.ycond_keep LL J Mt (tieF (fun c => (W, c)) (fun c => (E, c))) ?_ ?_ x hx
  · intro c d y
    have step : ∀ c0, pderiv (W, c0) (pderiv (E, c0) (M.glAct p LL J c d y)) =
        M.glAct p LL J c d (pderiv (W, c0) (pderiv (E, c0) y)) +
        (if c0 = c then pderiv (W, d) (pderiv (E, c0) y) else 0) +
        (if c0 = d then -pderiv (W, c0) (pderiv (E, c) y) else 0) := by
      intro c0
      rw [pderiv_glAct LL J E c0 c d y, map_add (f := _), pderiv_glAct LL J W c0 c d (pderiv (E, c0) y)]
      simp only [hE, hW, hvW, hvE, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> simp [map_neg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, ht, map_sum, Finset.sum_congr rfl (fun c0 _ => step c0), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, add_assoc, add_neg_cancel, add_zero]
  · intro z hz
    rw [ht]
    refine Submodule.sum_mem _ fun c0 _ => ?_
    have hQ1 : pderiv (E, c0) z ∈ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ |
        (((M.wt LL J 0 m - (if c0 = 0 then 1 else 0) : ℤ)) : WithTop ℤ) ≤ Mt} := by
      refine pderiv_keep (E, c0) {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} _ ?_ z hz
      intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J E c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hE, hvE, hc] using hm
    refine pderiv_keep (W, c0) _ {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} ?_ _ hQ1
    · intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J W c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hW, hvW, hc] using hm

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

