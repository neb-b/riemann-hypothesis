module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.PolynomialDimension.MultinomialDepth.Bundle0002
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LocalHypothesisOfGlobal
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ColumnSpanNumericalFacts
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

private theorem choose_add_succ_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + (m + 1)).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * ((A : ℚ) + m + 1) / ((m : ℚ) + 1) := by
  have h : (A + m + 1) * (A + m).choose m = (A + m + 1).choose (m + 1) * (m + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq (A + m) m
    | exact Nat.succ_mul_choose_eq (A + m) m
  rw [eq_div_iff (by positivity), show A + (m + 1) = A + m + 1 by omega]
  have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination -h'

private theorem choose_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + m).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * (A : ℚ) / ((m : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (A + m) m
  rw [Nat.add_sub_cancel] at h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast h

theorem prodA (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, choose_add_succ_succ_eq_choose_mul_div]
    ring

theorem prodB (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodA m B, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hr : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) = (m : ℚ) - ((j : ℕ) : ℚ) - 1 := by
    rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hr]
  congr 1 <;> ring

theorem weylDim_const (m : ℕ) (d : ℤ) : weylDim m (fun _ => d) = 1 := by
  unfold weylDim
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℕ) < (j : ℕ) := h
    have hq : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
    simp only [sub_self, Int.cast_zero, zero_add]
    exact div_self (sub_pos.mpr hq).ne'
  · rfl

private theorem weylDim_cons_eq_prod_mul (n : ℕ) (a : ℤ) (lam : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons a lam) =
      (∏ j : Fin n, (((a - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n lam := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [lt_self_iff_false, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [if_pos (Fin.succ_pos j)]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    push_cast
    congr 1 <;> ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.not_lt_zero, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.cons_succ, Fin.val_succ, Fin.succ_lt_succ_iff]
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

private theorem weylDim_snoc_eq_mul_prod (n : ℕ) (lam : Fin n → ℤ) (b : ℤ) :
    weylDim (n + 1) (Fin.snoc lam b) =
      weylDim n lam * ∏ i : Fin n, (((lam i - b : ℤ) : ℚ) + (n : ℚ) - ((i : ℕ) : ℚ)) / ((n : ℚ) - ((i : ℕ) : ℚ)) := by
  unfold weylDim
  have h1 : ∀ g : Fin (n + 1) → ℚ, (∏ j : Fin (n + 1), if Fin.last n < j then g j else 1) = 1 :=
    fun g => Finset.prod_eq_one fun j _ => if_neg (not_lt.mpr (Fin.le_last j))
  rw [Fin.prod_univ_castSucc, h1, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc, Fin.castSucc_lt_castSucc_iff]
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]

theorem weylDim_hwt_eq (m A B : ℕ) : weylDim (m + 2) (hwt m A B) = (dimHar (m + 1) A B : ℚ) := by
  unfold hwt
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_zero, zero_sub, neg_neg, sub_neg_eq_add, zero_add]
  rw [prodA m A, prodB m B]
  unfold dimHar dimPol
  have hle : (if A = 0 ∨ B = 0 then 0 else (A - 1 + (m + 1)).choose (m + 1) * (B - 1 + (m + 1)).choose (m + 1)) ≤
      (A + (m + 1)).choose (m + 1) * (B + (m + 1)).choose (m + 1) := by
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
  rw [Nat.cast_sub hle, Nat.cast_mul, choose_add_succ_succ_eq_choose_mul_div A m, choose_add_succ_succ_eq_choose_mul_div B m]
  split_ifs with h
  · rcases h with rfl | rfl <;> push_cast <;> field_simp <;> ring
  · push_neg at h
    rw [Nat.cast_mul, show A - 1 + (m + 1) = A + m by omega, show B - 1 + (m + 1) = B + m by omega,
      choose_succ_eq_choose_mul_div A m, choose_succ_eq_choose_mul_div B m]
    field_simp
    ring

theorem weylDim_vec (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  have hz : (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0 : Fin (m + 1) → ℤ) = fun _ => 0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [hz, weylDim_cons_eq_prod_mul, weylDim_const, mul_one]
  push_cast
  try simp only [sub_zero]
  rw [prodA (m + 1) d]

theorem weylDim_cov (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (d : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_self, zero_add, sub_zero]
  have h1 : (∏ j : Fin m, (((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = 1 :=
    Finset.prod_eq_one fun j _ => div_self (by positivity)
  rw [prodB m d, h1, one_mul, choose_add_succ_succ_eq_choose_mul_div d m]
  ring

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  classical
  haveI : IsFractionRing Kf Kf := by
    first
    | infer_instance
    | exact IsLocalization.atUnits Kf (nonZeroDivisors Kf)
        (fun x hx => (IsUnit.mem_submonoid_iff _).mpr (Ne.isUnit (nonZeroDivisors.ne_zero hx)))
  let M : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf) := fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)
  let B : ∀ s, Module.Basis (Module.Basis.ofVectorSpaceIndex Kf (M s)) Kf (M s) :=
    fun s => Module.Basis.ofVectorSpace Kf (M s)
  let b : ∀ s, Module.Basis.ofVectorSpaceIndex Kf (M s) → MvPolynomial (Fin k × Fin n) Kf :=
    fun s i => ((B s i : M s) : MvPolynomial (Fin k × Fin n) Kf)
  have hli : ∀ s, LinearIndependent Kf (b s) := fun s =>
    (B s).linearIndependent.map' (M s).subtype (Submodule.ker_subtype _)
  have hsp : ∀ s, Submodule.span Kf (Set.range (b s)) = M s := by
    intro s
    have h1 : Set.range (b s) = (M s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, (B s).span_eq, Submodule.map_subtype_top]
  obtain ⟨hT, hTs⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => Module.Basis.ofVectorSpaceIndex Kf (M s)) M b hli hsp
  show Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf M) = _
  rw [← hTs, Module.finrank_eq_nat_card_basis (Module.Basis.span hT), Nat.card_pi]
  exact Finset.prod_congr rfl fun s _ => (Module.finrank_eq_nat_card_basis (B s)).symm

theorem RS.charZeroO {p n' : ℕ} (R : RS p n') : CharZero R.O := by
  obtain ⟨c, hc⟩ := CharP.exists R.O
  rcases CharP.char_is_prime_or_zero R.O c with h | h
  · exfalso
    have hc0 : (c : R.O) = 0 := CharP.cast_eq_zero R.O c
    by_cases hcp : c = p
    · exact R.p_ne (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h R.std.1.prime).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : R.O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact R.p_not_unit (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero R.O

theorem RS.charZero {p n' : ℕ} (R : RS p n') : CharZero R.Kf := by
  have := R.charZeroO
  have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective R.O R.Kf)

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MidMeanOf
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def FM (K : Cst) (X : Dat) : Prop := FixedWeightNumericalFacts K X ∧ DensityNumericalFacts K X ∧ MeanKappaNumericalFacts K X ∧ ColumnSpanNumericalFacts K X

theorem midMean_of (D : Formalism.BasicNotions.D7) (h61a : RhoSumLowerBoundEdge) (h60ab : RhoUpperBoundSmallDepth) (hE : RestEdge) (hD : RestDims) (K : Cst)
    (hK : K.Pos) : MidMean D K (FM K) := fun hA X hF R =>
  have hk := keyIneq_of D K hA h61a h60ab hE hD X hF.1 R
  mean_of K hK X hF.2.2.2 R (avg_of hD K X hF.2.1 R hk 0 (Nat.zero_le _)) (avg_of hD K X hF.2.1 R hk X.ccl le_rfl)
    (meanX_of D K hK hA X hF.2.2.1 R)

theorem TransportedAlt.and {K : Cst} {F G : ℝ → Dat → Prop} (hF : TransportedAlt K F) (hG : TransportedAlt K G) : TransportedAlt K fun C X => F C X ∧ G C X := by
  obtain ⟨T, Cn, hT, hCn, h⟩ := hF
  obtain ⟨T', Cn', _, _, h'⟩ := hG
  exact ⟨max T T', max Cn Cn', lt_max_of_lt_left hT, lt_max_of_lt_left hCn, fun CH hCH C hC X hX =>
    ⟨h CH (le_trans (le_max_left _ _) hCH) C (le_trans (le_max_left _ _) hC) X hX,
      h' CH (le_trans (le_max_right _ _) hCH) C (le_trans (le_max_right _ _) hC) X hX⟩⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundOfEdgeCount
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestEdgeCountSrc : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (k : ℕ), 1 ≤ k → ∀ L : Submodule R.W (Fin k → R.Qq), IsLattice R.W L →
    ∃ (Ne : ℕ) (es : Fin Ne → Edge R.W R.Qq k), Function.Injective es ∧
      (∀ i, IsEdge p n' 1 (es i) ∧ (es i).src = L) ∧ gaussianNumber (p ^ n') k ≤ Ne

theorem dvd_w_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O}
    (hw : Irreducible w) (hsq : w ^ 2 = (p : O)) {z : O} (hz : z ≠ 0) {D : ℝ} {c : ℕ} (hc : 2 * D < c)
    (h : vLEO p z D) : z ∣ w ^ (c - 1) := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have hram : ramE p O = 2 := by
    unfold ramE
    rw [← hsq, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hw]
    simp
  rw [hram] at hq
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) < (c : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    linarith
  have hlt : (IsDiscreteValuationRing.addVal O z).toNat < c := by exact_mod_cast hreal
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ c - 1 := by omega
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer hw, ← ENat.coe_toNat hzt, nsmul_eq_mul, mul_one]
  exact_mod_cast hnat

theorem isUnit_det_of_one_add' {O ι : Type*} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι O) (h : ∀ i l, P i l - (1 : Matrix ι ι O) i l ∈ IsLocalRing.maximalIdeal O) :
    IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix ι ι O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem be_smulK_left (c : R.Kf) (F : Vsp R.Kf lam0) (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (c • F) G = c * be p 1 lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

theorem be_sum_left {ι : Type*} (s : Finset ι) (c : ι → R.Kf) (F : ι → Vsp R.Kf lam0)
    (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (∑ i ∈ s, c i • F i) G = ∑ i ∈ s, c i * be p 1 lam0 (F i) G := by
  unfold be
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, map_smul, smul_eq_mul]

theorem be_scale_Re (e : Edge R.W R.Qq (m + 1)) (c : ℕ) {F : Vsp R.Kf lam0}
    {G : Module.Dual R.Kf (Vsp R.Kf lam0)}
    (hF : F ∈ scale (algebraMap R.O R.Kf R.w ^ (c : ℤ)) (Re p R.ι R.σ R.w 1 lam0 e))
    (hG : G ∈ Re' p R.ι R.σ R.w 1 lam0 e) :
    ∃ b : R.O, be p 1 lam0 F G = algebraMap R.O R.Kf (R.w ^ c * b) := by
  unfold scale at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨b, hb⟩ := be_Re R lam0 e hF0 hG
  refine ⟨b, ?_⟩
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, zpow_natCast]
  rw [be_smulK_left, hb, ← map_pow, ← map_mul]

end Clean

theorem rho_upper_bound_of_edge_count (hcnt : RestEdgeCountSrc) : RhoUpperBoundSmallDepth := by
  classical
  intro p n' R m lam0 hDom t c n D hD0 hDc hfac
  have hdnn := dL_nonneg R lam0
  by_cases hn0 : n = 0
  · subst hn0; simpa using hdnn
  have hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq)) := ⟨1, by simp, rfl⟩
  obtain ⟨Ne, es, hinj, hes, hNe⟩ := hcnt p n' R (m + 1) (by omega) _ hL
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0)
      (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ CCL' R lam0 t c (es i)) ∧
      z' * z = R.w ^ (c - 1) ∧
      ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R.O R.Kf z else 0 := by
    intro i
    rcases hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩
    · exact absurd h0 hn0
    · obtain ⟨z', hz'⟩ := dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv
      refine ⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx,
        fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩
      rw [be_sum]
      exact hM a b
  choose x y z z' hz0 hx hy hzz hxy using hdata
  have hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧
      be p 1 lam0 (x i.1 i.2) (y l.1 l.2) =
        algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1) := by
    rintro ⟨i, a⟩ ⟨l, b⟩
    by_cases hil : i = l
    · subst hil
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only
      rw [hxy, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · have : ((i, a) : Fin Ne × Fin n) ≠ (i, b) := fun h => hab (Prod.mk.inj h).2
        rw [if_neg hab, if_neg this]; simp
    · have hne : es l ≠ es i := fun h => hil (hinj h).symm
      have hXs := CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b).1.2
      have h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b) := fun h => hil (Prod.mk.inj h).1
      refine ⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩
      simp only
      rw [hb, Matrix.one_apply_ne h2, zero_add]
      congr 1
      have h3 : R.w ^ c = R.w * R.w ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3, ← hzz l]
      ring
  choose β hβm hβe using hβ
  let P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O := Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l
  have hP : IsUnit P.det := by
    apply isUnit_det_of_one_add'
    intro i l
    simpa [P] using hβm i l
  have hinjK : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    have : P.det = 0 := hinjK (by rw [h0, map_zero])
    rw [this] at hP
    exact not_isUnit_zero hP
  have hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0 := by
      intro l
      have h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0 := by
        rw [hg]; simp [be]
      rw [be_sum_left] at h2
      have h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0 := by
        rw [← h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβe i l, map_mul, mul_assoc]
        rfl
      have hz : algebraMap R.O R.Kf (z l.1) ≠ 0 := fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))
      exact (mul_eq_zero.1 h3).resolve_right hz
    have h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using h1 l
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero hPK h4
    intro i
    rw [h5]; rfl
  have hpos : 0 < dimV R.Kf lam0 := Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom
  have hfin : Module.Finite R.Kf (Vsp R.Kf lam0) := Module.finite_of_finrank_pos hpos
  have hcard : Ne * n ≤ dimV R.Kf lam0 := by
    have := hli.fintype_card_le_finrank
    simpa [dimV] using this
  have hNpos := gaussianNumber_prime_pow_pos R (m + 1) (by omega)
  unfold dL
  rw [le_div_iff₀ hNpos]
  have h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ) := by exact_mod_cast hcard
  have h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne := mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)
  push_cast at h6
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

