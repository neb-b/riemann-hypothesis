module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkFaith
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem X_sub_ne {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (q : R) {i j : Fin n} (h : i ≠ j) :
    (X i - C q * X j : MvPolynomial (Fin n) R) ≠ 0 := by
  intro h0
  have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single i 1)) h0
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_C_mul, Finsupp.single_left_inj, h, Ne.symm h] at this

theorem UpperTheory.V.AlgebraTools.hkFaith :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ c : Perm (Fin n) → MvPolynomial (Fin n) R,
      (∀ x : MvPolynomial (Fin n) R, (∑ u, b.th (c u) * b.T u) * b.th x * b.one = 0) → c = 0 := by
  classical
  intro R _ _ n q H _ _ b hfaith c hc
  let K := FractionRing (MvPolynomial (Fin n) R)
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  choose F hF1 hF2 hF3 using fun u => UpperTheory.V.AlgebraTools.hkAct R n q H b K u
  choose Y hY1 hY2 using hF1
  have key : ∀ x : MvPolynomial (Fin n) R,
      ∑ v, (∑ u, algebraMap (MvPolynomial (Fin n) R) K (c u) * F u v) *
        algebraMap (MvPolynomial (Fin n) R) K (rename v x) = 0 := by
    intro x
    have h1 : b.th (∑ u, c u * Y u x) * b.one = 0 := by
      calc b.th (∑ u, c u * Y u x) * b.one
          = ∑ u, b.th (c u) * (b.th (Y u x) * b.one) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, Finset.sum_mul]; simp [map_mul, mul_assoc]
        _ = ∑ u, b.th (c u) * (b.T u * b.th x * b.one) := by simp [hY1]
        _ = (∑ u, b.th (c u) * b.T u) * b.th x * b.one := by
            rw [Finset.sum_mul, Finset.sum_mul]; simp [mul_assoc]
        _ = 0 := hc x
    have h2 := congrArg (algebraMap (MvPolynomial (Fin n) R) K) (hfaith _ h1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    simp_rw [map_mul, hY2, Finset.mul_sum] at h2
    rw [Finset.sum_comm] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  have hD := UpperTheory.V.AlgebraTools.hkDedekind R n K _ key
  by_contra hne
  obtain ⟨w0, hw0⟩ : ∃ w, c w ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨w, hwS, hmax⟩ := (Finset.univ.filter (fun u => c u ≠ 0)).exists_max_image invN
    ⟨w0, by simp [hw0]⟩
  have hcw : c w ≠ 0 := by simpa using hwS
  have hw := congrFun hD w
  simp only [Pi.zero_apply] at hw
  rw [Finset.sum_eq_single w] at hw
  · apply mul_ne_zero _ _ hw
    · exact fun h => hcw (hinj (by rw [h, map_zero]))
    · rw [hF2 w]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hlt : p.1 < p.2 := by
        simp [invSet, pairs] at hp
        exact hp.1
      have hpne : p.1 ≠ p.2 := ne_of_lt hlt
      refine div_ne_zero ?_ ?_
      · exact fun h => X_sub_ne q hpne (hinj (by rw [h, map_zero]))
      · intro h
        apply X_sub_ne (1 : R) hpne
        apply hinj
        simpa using h
  · intro u _ hu
    by_cases hcu : c u = 0
    · simp [hcu]
    · rw [hF3 u w (fun h => hu h.symm) (hmax u (by simp [hcu])), mul_zero]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSandwich
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem simple_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H]
    (b : Bern n q H) {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := fun e => by rw [e] at h; omega
  let s := swap a c
  let d (w : Perm (Fin n)) := b.T s * b.T w - q • b.T w
  have hpair (w : Perm (Fin n)) (hw : w⁻¹ a < w⁻¹ c) : d w + d (s * w) = 0 := by
    dsimp [d, s]
    rw [b.T_mul a c h w hw, ← mul_assoc, b.T_sq a c h, add_mul, smul_mul_assoc,
      smul_mul_assoc, one_mul]
    module
  have hcancel (w : Perm (Fin n)) : d w + d (s * w) = 0 := by
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact hpair w hw
    · have hw' : (s * w)⁻¹ a < (s * w)⁻¹ c := by
        simpa [s, Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have e := hpair (s * w) hw'
      rw [show s * (s * w) = w by simp [s, swap_mul_self_mul], add_comm] at e
      exact e
  have hsum : ∑ w, d w = 0 := by
    refine Finset.sum_ninvolution (fun w => s * w) hcancel ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have he := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simpa [s, mul_assoc] using he.symm
    · intro w
      simp [s, swap_mul_self_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

private theorem symm_of_eigen {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {q : R} {H : Type} [Ring H]
    [Algebra R H] (b : Bern n q H) (hb : b.Faithful) (y : MvPolynomial (Fin n) R)
    (hy : ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) * (b.th y * b.one) = q • (b.th y * b.one))
    (w : Perm (Fin n)) : rename w y = y := by
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → rename (swap a c) y = y := by
    intro a c h
    have hac : a ≠ c := fun e => by rw [e] at h; omega
    obtain ⟨z, hz, e⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c h y
    have e1 := hy a c h
    rw [← mul_assoc, e, add_mul, mul_assoc, simple_one b h, mul_smul_comm, smul_mul_assoc] at e1
    have e2 : q • rename (swap a c) y + (q - 1) • (X a * z) - q • y = 0 := by
      apply hb
      rw [map_sub, map_add (f := _), map_smul, map_smul, map_smul, sub_mul, add_mul, smul_mul_assoc, smul_mul_assoc,
        smul_mul_assoc, e1, sub_self]
    have e3 : (C q * X c - X a) * z = 0 := by
      simp only [smul_eq_C_mul, map_sub, map_one] at e2
      linear_combination e2 - C q * hz
    rcases mul_eq_zero.1 e3 with h0 | h0
    · have := congrArg (eval fun k => if k = a then (1 : R) else 0) h0
      simp [hac.symm] at this
    · rw [h0, mul_zero] at hz
      exact (sub_eq_zero.1 hz.symm).symm
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => rename w y = y) ?_ ?_ w
  · simp
  · intro a c h w _ ih
    rw [Perm.coe_mul, ← rename_rename, ih, hs a c h]

private theorem rename_rev_NN {R : Type} [CommRing R] (n : ℕ) (q : R) :
    rename (Fin.revPerm : Perm (Fin n)) (NN n q) = ∏ p ∈ pairs n, (X p.1 - C q * X p.2) := by
  rw [NN, map_prod]
  refine Finset.prod_nbij' (fun p => (p.2.rev, p.1.rev)) (fun p => (p.2.rev, p.1.rev)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simpa [pairs] using hp
  · intro p hp
    simpa [pairs] using hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp

private theorem rename_rev_De (R : Type) [CommRing R] (n : ℕ) :
    rename (Fin.revPerm : Perm (Fin n)) (De R n) = ∏ p ∈ pairs n, (X p.1 - X p.2) := by
  simpa [NN, De] using rename_rev_NN n (1 : R)

private theorem coeff_eq {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {K : Type} [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (F : Perm (Fin n) → K)
    (hF : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (∀ w : Perm (Fin n), rename w y = y) ∧
      algebraMap _ K y = ∑ u, F u * algebraMap _ K (rename u x))
    (N D : MvPolynomial (Fin n) R) (r : Perm (Fin n))
    (hr : F r = algebraMap _ K (rename r N) / algebraMap _ K (rename r D)) (v : Perm (Fin n)) :
    F v = algebraMap _ K (rename v N) / algebraMap _ K (rename v D) := by
  obtain ⟨σ, rfl⟩ : ∃ σ, v = σ * r := ⟨v * r⁻¹, by simp⟩
  let φ : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv (renameEquiv R σ).toRingEquiv
  have hφ : ∀ x : MvPolynomial (Fin n) R, φ (algebraMap _ K x) = algebraMap _ K (rename σ x) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x
  have h0 := UpperTheory.V.AlgebraTools.hkDedekind R n K (fun u => F u - φ (F (σ⁻¹ * u))) (by
    intro x
    obtain ⟨y, hy, e⟩ := hF x
    have e' := congrArg φ e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hy, e, map_sum] at e'
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e', sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun u => ?_
    rw [map_mul, hφ, rename_rename, Equiv.coe_mulLeft, inv_mul_cancel_left, Perm.coe_mul])
  have h1 := congrFun h0 (σ * r)
  simp only [Pi.zero_apply, inv_mul_cancel_left, sub_eq_zero] at h1
  rw [h1, hr, map_div₀, hφ, hφ, rename_rename, rename_rename, Perm.coe_mul]

theorem UpperTheory.V.AlgebraTools.hkSandwich :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H), b.Faithful → ∀ x : MvPolynomial (Fin n) R, b.one * b.th x * b.one = b.th (dd (NN n q * x)) * b.one := by
  intro R _ _ n q H _ _ b hb x
  let K := FractionRing (MvPolynomial (Fin n) R)
  choose f hf hfw hf0 using UpperTheory.V.AlgebraTools.hkAct R n q H b K
  obtain ⟨-, -, -, hrev, hlt⟩ := UpperTheory.V.AlgebraTools.hkInv n
  let V := Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)
  have hdet : De R n = V.det := by
    dsimp only [V]
    rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    refine Finset.prod_congr ?_ fun _ _ => rfl
    ext j
    simp
  have hD : De R n ≠ 0 := by
    rw [hdet]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr X_injective
  have hsg (w : Perm (Fin n)) : rename w (De R n) = Perm.sign w • De R n := by
    rw [hdet, AlgHom.map_det]
    have hV : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix V =
        V.submatrix w id := by
      ext i j
      simp [V, Matrix.vandermonde_apply]
    rw [hV, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
  have hsum : ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      b.one * b.th x * b.one = b.th y * b.one ∧
      algebraMap _ K y = ∑ u, (∑ w, f w u) * algebraMap _ K (rename u x) := by
    intro x
    choose y hy hy' using fun w => hf w x
    refine ⟨∑ w, y w, ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, Finset.sum_mul, ← Finset.sum_congr rfl fun w _ => hy w, ← Finset.sum_mul, ← Finset.sum_mul]
        rfl
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, hy', Finset.sum_mul]
        exact Finset.sum_comm
  have hF := coeff_eq (K := K) (fun u => ∑ w, f w u) (by
    intro x
    obtain ⟨y, hy, e⟩ := hsum x
    refine ⟨y, symm_of_eigen b hb y fun a c h => ?_, e⟩
    rw [← hy, ← mul_assoc, ← mul_assoc, simple_one b h, smul_mul_assoc, smul_mul_assoc])
    (NN n q) (De R n) Fin.revPerm (by
    rw [Finset.sum_eq_single Fin.revPerm (fun w _ hw => hf0 w _ hw.symm (hlt w hw).le) (by simp), hfw, hrev,
      rename_rev_NN, rename_rev_De, map_prod, map_prod, Finset.prod_div_distrib])
  obtain ⟨y, hy, e⟩ := hsum x
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) R) K
  have hD' : algebraMap _ K (De R n) ≠ 0 := fun h => hD (hinj (by rw [h, map_zero]))
  have : y = dd (NN n q * x) := by
    apply mul_left_cancel₀ hD
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [UpperTheory.V.AlgebraTools.hkDdSpec, map_mul, e, alt, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu := hF u
    rw [hu, hsg, map_mul]
    rcases Int.units_eq_one_or (Perm.sign u) with h | h
    · rw [h, one_smul, one_smul, map_mul, ← mul_assoc, mul_div_cancel₀ _ hD']
    · rw [h, Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg, map_neg, map_mul, div_neg, neg_mul,
        mul_neg, ← mul_assoc, mul_div_cancel₀ _ hD']
  rw [hy, this]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFundNorm
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unif_lt {x : kˣ} (hx : IsUnif x) (y : k) :
    valuation k y < 1 ↔ valuation k y ≤ valuation k (x : k) := by
  obtain ⟨p, hp, e⟩ := hx
  have hI := Valuation.integer.integers (valuation k)
  have h1 : valuation k (x : k) < 1 := by
    rw [← e]
    refine lt_of_le_of_ne p.2 fun h => hp.not_isUnit (hI.isUnit_iff_valuation_eq_one.2 h)
  refine ⟨fun h => ?_, fun h => h.trans_lt h1⟩
  let z : 𝒪[k] := ⟨y, h.le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun hu => h.ne (hI.isUnit_iff_valuation_eq_one.1 hu)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
  rw [← e]
  exact hI.le_of_dvd hz

private def Bd (x : kˣ) (g : GL (Fin n) k) : Prop :=
  ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k (x : k) ^ (if j < i then 1 else 0 : ℤ)

private theorem mem_iw_iff {x : kˣ} (hx : IsUnif x) (g : GL (Fin n) k) :
    g ∈ iwahori k (Fin n) ↔ Bd x g ∧ Bd x g⁻¹ := by
  have h1 : valuation k (x : k) ≤ 1 := ((unif_lt hx x).2 le_rfl).le
  have A : ∀ g ∈ iwahori k (Fin n), Bd x g := by
    intro g hg i j
    have hg' := mem_iwahori.1 hg
    split_ifs with h
    · simpa using (unif_lt hx _).1 (hg'.2 i j h)
    · rw [zpow_zero]
      exact ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg'.1).1 i j
  have B : ∀ g : GL (Fin n) k, Bd x g → ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro g hg i j
    have := hg i j
    split_ifs at this with h
    · exact le_trans (by simpa using this) h1
    · simpa using this
  refine ⟨fun hg => ⟨A g hg, A _ (inv_mem hg)⟩, fun ⟨ha, hb⟩ => mem_iwahori.2
    ⟨(GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨B _ ha, B _ hb⟩, fun i j h => (unif_lt hx _).2 ?_⟩⟩
  simpa [h] using ha i j

private theorem conj_entry (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (w i) (w j) =
      (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
  have e : pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹ =
      pm k n w * (pw x a * g * diagT k (Fin n) (fun i => x ^ a i)⁻¹) * pm k n w⁻¹ := by
    rw [map_inv, map_inv, pw]; group
  rw [e]
  simp only [Units.val_mul, pw, val_diagT]
  generalize hM : (diagonal (fun i => ((x ^ a i : kˣ) : k)) * (g : Matrix (Fin n) (Fin n) k) *
    diagonal fun i => (((fun i => x ^ a i)⁻¹ i : kˣ) : k)) = M
  have hM' : M i j = (x : k) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) k) i j := by
    rw [← hM, mul_diagonal, diagonal_mul, zpow_sub₀ x.ne_zero]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    ring
  rw [← hM']
  simp only [Matrix.mul_apply, pm_apply]
  simp

private theorem bd_conj (x : kˣ) (a : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (a i - a j) + (if j < i then 1 else 0)) (g : GL (Fin n) k) :
    Bd x (pm k n w * pw x a * g * (pm k n w * pw x a)⁻¹) ↔ Bd x g := by
  have h0 : 0 < valuation k (x : k) := zero_lt_iff.2 (by simp)
  unfold Bd
  rw [w.surjective.forall₂]
  refine forall₂_congr fun i j => ?_
  rw [conj_entry, hw, map_mul, map_zpow₀, zpow_add₀ h0.ne', mul_le_mul_iff_right₀ (zpow_pos h0 _)]

private theorem exists_rot (n m : ℕ) (hm : m ≤ n) : ∃ w : Equiv.Perm (Fin n),
    ∀ i j, (if w j < w i then 1 else 0 : ℤ) = (fund n m i - fund n m j) + (if j < i then 1 else 0) := by
  let f : Fin n → Fin n := fun i => ⟨if (i : ℕ) < m then n - m + i else i - m, by
    have := i.2; split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Fin.val h
    have := i.2; have := j.2
    simp only [f] at h'
    ext
    split_ifs at h' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun i j => ?_⟩
  have := i.2; have := j.2
  simp only [Equiv.ofBijective_apply, f, fund, Fin.lt_def]
  split_ifs <;> omega

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.fundNorm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (x : kˣ), IsUnif x → ∀ m ≤ n, ∃ w : Equiv.Perm (Fin n), pm k n w * pw x (fund n m) ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n C x hx m hm
  obtain ⟨w, hw⟩ := exists_rot n m hm
  refine ⟨w, Subgroup.mem_normalizer_iff.2 fun g => ?_⟩
  have e : (pm k n w * pw x (fund n m) * g * (pm k n w * pw x (fund n m))⁻¹)⁻¹ =
      pm k n w * pw x (fund n m) * g⁻¹ * (pm k n w * pw x (fund n m))⁻¹ := by group
  rw [(memIwC k n C).1, (memIwC k n C).1, mem_iw_iff hx, mem_iw_iff hx, e, bd_conj x _ w hw, bd_conj x _ w hw]
  refine and_congr Iff.rfl ?_
  conv_rhs => rw [w.surjective.forall]
  simp only [conj_entry, sub_self, zpow_zero, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkEv
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem hkEv_coe (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x : G)
    (v : fixd ρ I) : (hk ρ I x v : M) = dc ρ I I x v := by
  have h := (UpperTheory.V.Hi.dcSum A G M ρ I I x (hI x)).2.1
  unfold hk hk2
  rw [dite_eq_left h]
  rfl

private noncomputable def hkEv_phi (ρ : Representation A G M) (I : Subgroup G) (m : M) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] M :=
  Finsupp.linearCombination A (fun q : G ⧸ I => ρ q.out m) ∘ₗ (MonoidAlgebra.coeffLinearEquiv A).toLinearMap

private theorem hkEv_phi_single (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (g : G) (c : A) :
    hkEv_phi ρ I m (MonoidAlgebra.single (g : G ⧸ I) c) = c • ρ g m := by
  have h1 : g⁻¹ * (g : G ⧸ I).out ∈ I := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h2 : ρ (g⁻¹ * (g : G ⧸ I).out) m = m := m.2 _ h1
  have h3 : ρ (g : G ⧸ I).out m = ρ g m := by
    calc ρ (g : G ⧸ I).out m = ρ (g * (g⁻¹ * (g : G ⧸ I).out)) m := by rw [mul_inv_cancel_left]
      _ = ρ g (ρ (g⁻¹ * (g : G ⧸ I).out) m) := by rw [map_mul ρ g]; rfl
      _ = ρ g m := by rw [h2]
  rw [← h3]
  simp [hkEv_phi]

private theorem hkEv_phi_equiv (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (h : G)
    (a : MonoidAlgebra A (G ⧸ I)) : hkEv_phi ρ I m (permRep A I h a) = ρ h (hkEv_phi ρ I m a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single q c =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Representation.ofMulAction_single]
    have : h • (g : G ⧸ I) = ((h * g : G) : G ⧸ I) := rfl
    rw [this, hkEv_phi_single, hkEv_phi_single, map_smul, map_mul]
    rfl

private noncomputable def hkEv_psi (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    fixd (permRep A I) I →ₗ[A] fixd ρ I :=
  (hkEv_phi ρ I m).restrict (fun a ha u hu => by rw [← hkEv_phi_equiv, ha u hu])

private theorem hkEv_psi_hk (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (m : fixd ρ I)
    (x : G) (a : fixd (permRep A I) I) :
    hkEv_psi ρ I m (hk (permRep A I) I x a) = hk ρ I x (hkEv_psi ρ I m a) := by
  apply Subtype.ext
  rw [hkEv_coe ρ I hI]
  change hkEv_phi ρ I m (hk (permRep A I) I x a : MonoidAlgebra A (G ⧸ I)) = dc ρ I I x (hkEv_phi ρ I m a)
  rw [hkEv_coe _ I hI]
  exact (UpperTheory.V.Hi.dcSum A G _ (permRep A I) I I x (hI x)).2.2.2 A M ρ
    (hkEv_phi ρ I m).toAddMonoidHom (hkEv_phi_equiv ρ I m) a

private theorem hkEv_psi_surj (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    ∃ a, hkEv_psi ρ I m a = m := by
  refine ⟨⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => ?_⟩, Subtype.ext ?_⟩
  · rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)
  · change hkEv_phi ρ I m (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = m
    rw [hkEv_phi_single]
    simp

private def hkEv_R (ρ : Representation A G M) (I : Subgroup G)
    (T : Module.End A (fixd (permRep A I) I)) (E : Module.End A (fixd ρ I)) : Prop :=
  ∀ m a, hkEv_psi ρ I m (T a) = E (hkEv_psi ρ I m a)

private theorem hkEv_uniq {ρ : Representation A G M} {I : Subgroup G}
    {T : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T E') : E = E' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨a, ha⟩ := hkEv_psi_surj ρ I m
  rw [← ha, ← h, ← h']

private theorem hkEv_alg (ρ : Representation A G M) (I : Subgroup G) (c : A) :
    hkEv_R ρ I (algebraMap A _ c) (algebraMap A _ c) := fun m a => by
  simp only [Module.algebraMap_end_apply, map_smul]

private theorem hkEv_add {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T + T') (E + E') := fun m a => by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), h, h']

private theorem hkEv_mul {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T * T') (E * E') := fun m a => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

private theorem hkEv_ex (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (T : HkAlg A I) :
    ∃ E, hkEv_R ρ I T.1 E := by
  obtain ⟨T, hT⟩ := T
  induction hT using Algebra.adjoin_induction with
  | mem T h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨hk ρ I x, fun m a => hkEv_psi_hk ρ I hI m x a⟩
  | algebraMap c => exact ⟨_, hkEv_alg ρ I c⟩
  | add T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_add h h'⟩
  | mul T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_mul h h'⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.hkEv :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G), HeckePair I → ∃ ev : HkAlg A I →ₐ[A] Module.End A (fixd ρ I), ∀ x : G, ev (hT A I x) = hk ρ I x := by
  intro A G M _ _ _ _ ρ I hI
  choose f hf using hkEv_ex ρ I hI
  have halg : ∀ c : A, f (algebraMap A _ c) = algebraMap A _ c := fun c =>
    hkEv_uniq (hf _) (hkEv_alg ρ I c)
  refine ⟨{ toFun := f
            map_one' := by simpa using halg 1
            map_mul' := fun T T' => hkEv_uniq (hf _) (hkEv_mul (hf T) (hf T'))
            map_zero' := by simpa using halg 0
            map_add' := fun T T' => hkEv_uniq (hf _) (hkEv_add (hf T) (hf T'))
            commutes' := halg }, fun x => ?_⟩
  exact hkEv_uniq (hf _) (fun m a => hkEv_psi_hk ρ I hI m x a)
end

