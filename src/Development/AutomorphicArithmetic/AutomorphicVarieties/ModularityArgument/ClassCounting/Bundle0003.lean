module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FirstFace
section
noncomputable section

namespace UpperTheory.V.ZK

private def gz (q e : ℕ) (j : Fin (e + 1) → ZMod q) : Fin (2 * e + 1 + 1) → Cq q :=
  fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1

private theorem sum_pair {M : Type} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (h : ∀ t < n, f (2 * t) + f (2 * t + 1) = 0) : ∑ s ∈ Finset.range (2 * n), f s = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc,
      h n (by omega), ih fun t ht => h t (by omega), add_zero]

private theorem first_face (q : ℕ) [NeZero q] (e : ℕ) :
    ∑ j : Fin (e + 1) → ZMod q,
      (Finsupp.single (fun i : Fin (2 * e + 1) => gz q e j i.succ) 1 : Ch (ZMod q) (Cq q) (2 * e + 1)) = 0 := by
  rw [← (Fin.consEquiv fun _ : Fin (e + 1) => ZMod q).sum_comp, Fintype.sum_prod_type]
  have h : ∀ (a : ZMod q) (j : Fin e → ZMod q),
      (fun i : Fin (2 * e + 1) => gz q e ((Fin.consEquiv fun _ : Fin (e + 1) => ZMod q) (a, j)) i.succ) =
        fun i : Fin (2 * e + 1) => gz q e (Fin.cons 0 j) i.succ := by
    intro a j
    funext i
    unfold gz
    split_ifs with hi
    · have hi' : ((i : ℕ) + 1) % 2 = 0 := hi
      have : (⟨(i.succ : ℕ) / 2, by omega⟩ : Fin (e + 1)) = Fin.succ ⟨(i : ℕ) / 2, by omega⟩ := by
        ext; simp; omega
      rw [this]; rfl
    · rfl
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]

private theorem merge (q e t : ℕ) (ht : t < e + 1) (j : Fin (e + 1) → ZMod q) :
    Fin.contractNth (⟨2 * t, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (gz q e j) =
      Fin.contractNth (⟨2 * t + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·)
        (gz q e (j + fun i : Fin (e + 1) => if (i : ℕ) = t then 1 else if (i : ℕ) = t + 1 then -1 else 0)) := by
  funext k
  rcases lt_trichotomy (k : ℕ) (2 * t) with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Pi.add_apply]
    rw [if_neg (show ¬ (k : ℕ) / 2 = t by omega), if_neg (show ¬ (k : ℕ) / 2 = t + 1 by omega), add_zero]
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ h, Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
    simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
    rw [if_pos (show (k : ℕ) % 2 = 0 by omega), if_pos (show (k : ℕ) % 2 = 0 by omega),
      if_neg (show ¬ ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show (k : ℕ) / 2 = t by omega), ofAdd_add]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ h]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [Fin.contractNth_apply_of_eq _ _ _ _ h'.symm]
      simp only [gz, Fin.val_castSucc, Fin.val_succ, Pi.add_apply]
      rw [if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega), if_pos (show ((k : ℕ) + 1) % 2 = 0 by omega),
        if_neg (show ¬ (k : ℕ) % 2 = 0 by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega),
        if_pos (show ((k : ℕ) + 1) / 2 = t + 1 by omega), ← ofAdd_add]
      congr 1
      ring
    · rw [Fin.contractNth_apply_of_gt _ _ _ _ h']
      simp only [gz, Fin.val_succ, Pi.add_apply]
      have h'' : 2 * t + 1 < (k : ℕ) := h'
      by_cases h1 : ((k : ℕ) + 1) % 2 = 0
      · rw [if_neg (show ¬ ((k : ℕ) + 1) / 2 = t by omega), if_neg (show ¬ ((k : ℕ) + 1) / 2 = t + 1 by omega), add_zero]
      · rw [if_neg h1, if_neg h1]

theorem sZc : SZc := by
  intro q _ e
  have hz : zc q e = ∑ j : Fin (e + 1) → ZMod q, Finsupp.single (gz q e j) 1 := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cyc, hz, map_sum]
  simp only [bd, Finsupp.linearCombination_single, one_smul]
  rw [Finset.sum_add_distrib, first_face, zero_add, Finset.sum_comm]
  simp only [← Finset.smul_sum]
  rw [Finset.sum_fin_eq_sum_range]
  refine sum_pair _ (e + 1) fun t ht => ?_
  rw [dite_eq_left (show 2 * t < 2 * e + 1 + 1 by omega), dite_eq_left (show 2 * t + 1 < 2 * e + 1 + 1 by omega)]
  simp only [merge q e t ht]
  rw [← Equiv.sum_comp (Equiv.addRight (fun i : Fin (e + 1) => if (i : ℕ) = t then (1 : ZMod q) else
    if (i : ℕ) = t + 1 then -1 else 0)) fun j => (Finsupp.single (Fin.contractNth
      (⟨2 * t + 1, by omega⟩ : Fin (2 * e + 1 + 1)) (· * ·) (gz q e j)) 1 : Ch (ZMod q) (Cq q) (2 * e + 1))]
  simp only [Equiv.coe_addRight]
  rw [← add_smul, pow_succ (-1 : ZMod q) (2 * t + 1), mul_neg_one, add_neg_cancel, zero_smul]

end UpperTheory.V.ZK

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK.SimplicialChains

variable (A : Type) [CommRing A]

private theorem bd_single (G : Type) [Group G] (m : ℕ) (g : Fin (m + 1) → G) (a : A) :
    bd A G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  simp only [bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_comm]

private theorem cm_single {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (g : Fin m → G) (a : A) :
    cm A f m (Finsupp.single g a) = Finsupp.single (fun i => f (g i)) a := by
  simp [cm]

private theorem bd_eq (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 1)) :
    bd A G m z = groupHomology.inhomogeneousChains.d (Rep.trivial A G A) m z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
  | single g a =>
    rw [bd_single, groupHomology.inhomogeneousChains.d_single]
    simp

private theorem bd_bd (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)) :
    bd A G m (bd A G (m + 1) z) = 0 := by
  rw [bd_eq A G (m + 1) z, bd_eq]
  have h := groupHomology.inhomogeneousChains.d_comp_d (Rep.trivial A G A) m
  simpa using LinearMap.congr_fun (congrArg (fun φ => ModuleCat.Hom.hom φ) h) z

private theorem bd_cm (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)) :
    bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | single g a =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cm_single, bd_single, bd_single, map_add (f := _), cm_single, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, cm_single]
    congr 2
    funext i
    simp only [Fin.contractNth]
    split_ifs <;> simp [map_mul]

private theorem cm_prism (G H : Type) [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m) :
    cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z) := by
  have key : ∀ (g : Fin m → G) (i : Fin (m + 1)),
      (fun j => f (Fin.insertNth (α := fun _ => G) i k
        (fun j : Fin m => if (j : ℕ) < (i : ℕ) then g j else k⁻¹ * g j * k) j)) =
        Fin.insertNth (α := fun _ => H) i (f k)
          (fun j : Fin m => if (j : ℕ) < (i : ℕ) then f (g j) else (f k)⁻¹ * f (g j) * f k) := by
    intro g i
    funext j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp
    · simp only [Fin.insertNth_apply_succAbove]
      split_ifs <;> simp [map_mul]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | single g a =>
    rw [cm_single]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [prism, Finsupp.linearCombination_single, Finset.smul_sum, map_sum, map_smul, cm_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key g i]

private theorem bd_triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (a : A) :
    bd A G m (Finsupp.single 1 a) =
      Finsupp.single 1 ((1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * a) := by
  rw [bd_single]
  ext x
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply, eq_iff_true_of_subsingleton,
    Fin.sum_univ_eq_sum_range (fun j => (-1 : A) ^ (j + 1) * a), add_mul, Finset.sum_mul]

private theorem coef (m : ℕ) : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) +
    (1 + ∑ j ∈ Finset.range (m + 1 + 1), (-1 : A) ^ (j + 1)) = 1 := by
  induction m with
  | zero => norm_num [Finset.sum_range_succ]
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1 + 1), Finset.sum_range_succ _ (n + 1)]
    rw [Finset.sum_range_succ _ (n + 1)] at ih
    linear_combination ih

private theorem triv (G : Type) [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)) (hz : Cyc z) : Bd z := by
  have hz1 : z = Finsupp.single 1 (z 1) := by
    ext x
    obtain rfl : x = 1 := Subsingleton.elim _ _
    simp
  have h0 : (1 + ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ (j + 1)) * z 1 = 0 := by
    have h := hz
    unfold Cyc at h
    rw [hz1, bd_triv] at h
    simpa using congrArg (fun w => w 1) h
  show z ∈ (bd A G (m + 1)).range
  refine LinearMap.mem_range.mpr ⟨Finsupp.single 1 (z 1), ?_⟩
  rw [bd_triv]
  conv_rhs => rw [hz1]
  congr 1
  linear_combination (z 1) * coef A m - h0

end UpperTheory.V.ZK.SimplicialChains

open UpperTheory.V.ZK.SimplicialChains in
theorem UpperTheory.V.ZK.sChain :
    UpperTheory.V.ZK.SChain := by
  intro A _
  refine ⟨bd_bd A, bd_cm A, fun G H K _ _ _ f g m z => ?_, cm_prism A, triv A⟩
  simp only [cm, Finsupp.lmapDomain_apply]
  rw [← Finsupp.mapDomain_comp]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SFinal
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

private theorem sf_card (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    haveI := uniqueOfSubsingleton (0 : M')
    simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule ℤ_[l] (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    have hq : Nat.card (M ⧸ N) = l := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod l)
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      push_cast
      rfl
    · have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      rw [h2]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [hq, hc, pow_succ, mul_comm]

open KStar.TotallyRealRoots in
private theorem sf_nu {l : ℕ} [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (h0 : U.index ≠ 0) {e : ℕ} (he : e ≠ 0) :
    nu l U e ≤ ((2 + padicValNat l U.index + padicValNat l e : ℕ) : ℕ∞) := by
  have hp : Prime (l : ℤ_[l]) := PadicInt.prime_p
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ 2) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((l : ℤ_[l]) ^ 2)‖ < 1 := by
      rw [norm_pow, PadicInt.norm_p]
      have h2 : (1:ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have h3 : (0:ℝ) < (l:ℝ)⁻¹ := by positivity
      have h4 : (l:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [PadicInt.norm_add_eq_max_of_ne] <;> simp_all [ne_of_gt, le_of_lt]
  have hmem : hunit.unit ^ U.index ∈ U := U.pow_index_mem hunit.unit
  by_contra hcon
  push_neg at hcon
  have hle : (((2 + padicValNat l U.index + padicValNat l e + 1 : ℕ)) : ℕ∞) ≤ nu l U e := by
    have := Order.add_one_le_of_lt hcon
    exact_mod_cast this
  have hdvd := (KStar.TotallyRealRoots.le_nu_iff.1 hle) _ hmem
  have hw : ((hunit.unit ^ U.index : ℤ_[l]ˣ) : ℤ_[l]) ^ e = (1 + (l:ℤ_[l]) ^ 2) ^ (U.index * e) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_mul]
  rw [hw] at hdvd
  have hm := KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq (l := l) (u := 1 + (l:ℤ_[l]) ^ 2) (by simp) (U.index * e)
  rw [add_sub_cancel_left, emultiplicity_pow_self hp.ne_zero hp.not_unit,
    ← padicValNat_eq_emultiplicity (Nat.mul_ne_zero h0 he), ← Nat.padicValNat_def, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h0 he] at hm
  have h5 := (pow_dvd_iff_le_emultiplicity).1 hdvd
  rw [hm] at h5
  norm_cast at h5
  omega

private theorem sf_loc {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (D : LData L Ω l) {e : ℕ} (he : e ≠ 0) :
    sumLocalH0TwistLength D e ≤ ((Module.finrank ℚ L * (2 + Nat.log l (Module.finrank ℚ L) + e) : ℕ) : ℕ∞) := by
  rw [LDataCardLeFinrank.local_H0_length_eq_sum]
  set n := Module.finrank ℚ L with hn
  have hv : ∀ v : D.S, KStar.TotallyRealRoots.nu l (LDataCardLeFinrank.decImage L l (D.A v)) ((e : ℤ).natAbs) ≤
      ((2 + Nat.log l n + e : ℕ) : ℕ∞) := by
    intro v
    obtain ⟨_, hi0, hin⟩ := LDataCardLeFinrank.ineOpen L Ω l v (D.A v) (LDataCardLeFinrank.above_of_mem D v) (D.hA v)
    have hdvd : (LDataCardLeFinrank.decImage L l (D.A v)).index ∣ (LDataCardLeFinrank.ineImage L l (D.A v)).index :=
      Subgroup.index_dvd_of_le (LDataCardLeFinrank.ineImage_le_decImage L l (D.A v))
    have hd0 : (LDataCardLeFinrank.decImage L l (D.A v)).index ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact hi0 (Nat.eq_zero_of_zero_dvd hdvd)
    have hdn : (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ n :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd) hin
    have hne : (e : ℤ).natAbs ≠ 0 := by simpa using he
    refine le_trans (sf_nu _ hd0 hne) ?_
    have a1 : padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ Nat.log l n :=
      le_trans (by simpa only [Nat.padicValNat_def] using (padicValNat_le_nat_log (LDataCardLeFinrank.decImage L l (D.A v)).index)) (Nat.log_mono_right hdn)
    have a2 : padicValNat l e ≤ e := by
      have hp := (Fact.out : l.Prime)
      have b1 : l ^ padicValNat l e ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
      have b2 : padicValNat l e < l ^ padicValNat l e := Nat.lt_pow_self hp.one_lt
      omega
    have hea : (e : ℤ).natAbs = e := rfl
    rw [hea]
    exact_mod_cast (by omega : 2 + padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index + padicValNat l e ≤
      2 + Nat.log l n + e)
  calc _ ≤ ∑ _v : D.S, ((2 + Nat.log l n + e : ℕ) : ℕ∞) := Finset.sum_le_sum fun v _ => hv v
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, ← Nat.cast_mul]
      exact_mod_cast Nat.mul_le_mul_right _ (LDataCardLeFinrank.cardAbove L Ω l D)

theorem UpperTheory.V.ZK.sFinal :
    UpperTheory.V.ZK.SFinal := by
  rw [SFinal.eq_1]
  rintro hPT hLF hLTD ⟨C, hC⟩
  obtain ⟨CK, _, hCK⟩ := K.numFin C
  refine ⟨CK, ?_⟩
  rw [LemmaK.eq_1]
  intro l _ L Ω _ _ _ _ _ D htc hmu e he
  rw [ShaK.eq_1] at hC
  obtain ⟨s, hs, hslog⟩ := hC l L htc hmu e he
  set n := Module.finrank ℚ L with hn
  have hV := LDataCardLeFinrank.VLen_le_shaLen_add hPT hLF hLTD (LDataCardLeFinrank.ptCase_of_isTotallyComplex L l) D (e : ℤ)
  rw [VLen.eq_1, LDataCardLeFinrank.shaLen_eq_shaInv, hs] at hV
  have hloc := sf_loc D (e := e) (by omega)
  have hlen : Module.length ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) ≤ ((s + n * (2 + Nat.log l n + e) : ℕ) : ℕ∞) := by
    rw [Nat.cast_add]
    rw [← hn] at hloc
    exact le_trans hV (add_le_add le_rfl hloc)
  have hfl : IsFiniteLength ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) := by
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  obtain ⟨k, hk, hcard⟩ := sf_card l _ hfl
  have hkK : k ≤ s + n * (2 + Nat.log l n + e) := by
    rw [hk] at hlen
    exact_mod_cast hlen
  have hfin : Finite (H2 (zlTw D ((e : ℤ) + 1))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  refine ⟨hfin, ?_⟩
  rw [hcard, Nat.cast_pow, Real.log_pow]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1.le
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hD1 : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (discr_ne_zero L)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hDR : (1 : ℝ) ≤ (discr L).natAbs := by exact_mod_cast hD1
  have hln : (l : ℝ) ≤ n + 1 := by exact_mod_cast K.primeLe l L hmu
  have hX : Real.log l ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hln
  have hX0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLog : (Nat.log l n : ℝ) * Real.log l ≤ Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_pow]
    have hpl : ((l : ℝ) ^ Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
    exact Real.log_le_log (by positivity) (by linarith)
  have hY : 1 / 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hnum := hCK e n (discr L).natAbs he hn1 hD1
  have hk' : (k : ℝ) ≤ s + n * (2 + Nat.log l n + e) := by exact_mod_cast hkK
  have e1 : (k : ℝ) * Real.log l ≤ (s + n * (2 + Nat.log l n + e)) * Real.log l :=
    mul_le_mul_of_nonneg_right hk' hlogl
  have e2 : (n : ℝ) * (2 + e) * Real.log l ≤ n * (2 + e) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have e3 : (n : ℝ) * ((Nat.log l n : ℝ) * Real.log l) ≤ n * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hLog (by positivity)
  have hcoef : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have q1 : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * (1 / 2) := by nlinarith
    have q2 : 4 * (2 * e * (2 * e + 3)) * (1 / 2 : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    linarith
  have e4 : (n : ℝ) * (3 + e) * Real.log ((n : ℝ) + 1) ≤
      n * (4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ))) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) hX0
  linarith [e1, e2, e3, e4, hnum, hslog]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism
section
namespace UpperTheory.V.ZK

theorem sPrism : SPrism := by
  intro A _ G _ k m z
  obtain ⟨y, rfl⟩ := toInh_surjective A (m + 1) z
  rw [prism_toInh, bd_toInh, bd_toInh, prism_toInh, conj_toInh, ← map_add (f := _), ← map_sub, hbd_hprism]

end UpperTheory.V.ZK
end

