module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem cf_norm_root {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : n ≠ 0) {x : Om v} (hx : x ^ n = 1) :
    ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h

private theorem cf_root_one {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x : Om v} (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  by_contra hne
  have hx1 := cf_norm_root hn0 hx
  have hs : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have := mul_geom_sum x n
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hp : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x * (x ^ i - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rwa [norm_mul, hx1, one_mul]
  have hq : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, x ^ i - (k : Om v)‖ < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ∑ i ∈ Finset.range (k + 1), x ^ i - ((k + 1 : ℕ) : Om v) =
          (∑ i ∈ Finset.range k, x ^ i - (k : Om v)) + (x ^ k - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hp k))
  have h1 := hq n
  rw [hs, zero_sub, norm_neg] at h1
  have h2 : ((n : ℕ) : Om v) = algebraMap ℚ_[v] (Om v) (n : ℚ_[v]) := by simp
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
  exact hn h1

private theorem cf_root_eq {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x y : Om v} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : ‖x - y‖ < 1) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  have hy1 := cf_norm_root hn0 hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  have h1 : x / y = 1 := by
    refine cf_root_one hn (by rw [div_pow, hx, hy, div_one]) ?_
    rw [div_sub_one hy0, norm_div, hy1, div_one]
    exact h
  exact (div_eq_one_iff_eq hy0).1 h1

private theorem cf_toZModPow (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (g : GQ v) (m a : ℕ)
    (h : ∀ ζ : Om v, IsPrimitiveRoot ζ (l ^ m) → g ζ = ζ ^ a) :
    PadicInt.toZModPow m ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) = (a : ZMod (l ^ m)) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) (l ^ m)
  have hs := cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ v) (Om v) g) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hs' : g ζ = ζ ^ (PadicInt.toZModPow m c).val := hs
  have h3 := hs'.symm.trans (h ζ hζ)
  have h4 : (PadicInt.toZModPow m c).val ≡ a [MOD l ^ m] := by
    have := (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mp h3
    rwa [← hζ.eq_orderOf] at this
  rw [← (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4, ZMod.natCast_zmod_val]

private theorem cf_chi (l : ℕ) [Fact l.Prime] (P : LocPrime l) (g : GQ l) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) -
      (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ.pow_eq_one
    have h4 := cf_toZModPow l l g m a (fun ξ hξ => by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
      rw [map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])
    set c : ℤ_[l] := ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have h5 : PadicInt.toZModPow m ((a : ℤ_[l]) - c) = 0 := by
      rw [map_sub, map_natCast, h4, sub_self]
    have h6 : ‖(a : ℤ_[l]) - c‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow]
      exact h5
    have h7 : ‖(a : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have : (((a : ℤ_[l]) - c : ℤ_[l]) : ℚ_[l]) = (a : ℚ_[l]) - (c : ℚ_[l]) := by push_cast; rfl
      rw [← this]; exact h6
    have h8 := IsUltrametricDist.norm_add_le_max (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) ((a : ℚ_[l]) - c)
    rw [sub_add_sub_cancel] at h8
    exact h8.trans (max_le ha h7)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have hlt : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt) fun m => ?_
  have := key m
  rwa [zpow_neg, zpow_natCast, ← inv_pow] at this

theorem UpperTheory.V.Loc.cycFacts :
    ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime], Continuous (cyc v l) ∧
      (v ≠ l → (∀ g ∈ Iq v, cyc v l g = 1) ∧
        ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ → ((cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]) = (v : ℤ_[l])) ∧
      ∀ g : GQ l, (((PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro v l _ _
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  refine ⟨cyclotomicCharacter.continuous l ℚ_[v] (Om v), fun hvl => ?_, cf_chi l (PP l)⟩
  have hnd : ∀ m : ℕ, ¬ v ∣ l ^ m := fun m h =>
    hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 (hv.dvd_of_dvd_pow h))
  refine ⟨fun g hg => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l g m 1 (fun ζ hζ => ?_)]
    · simp
    · rw [pow_one]
      have hm : ζ ∈ MaximalUnramifiedExtension v :=
        IntermediateField.subset_adjoin _ _ ⟨l ^ m, pow_pos hl.pos m, hnd m, hζ.pow_eq_one⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hm
  · refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l σ m v (fun ζ hζ => ?_)]
    · simp
    · have h1 := cf_norm_root (pow_ne_zero m hl.ne_zero) hζ.pow_eq_one
      refine cf_root_eq (hnd m) ?_ ?_ (hσ ζ h1.le)
      · rw [← map_pow, hζ.pow_eq_one, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.ci_closed (l : ℕ) [Fact l.Prime] (x y : PadicAlgCl l) :
    IsClosed {σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l | σ x = y} := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hx
  have hU := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ := by fun_prop
  have h1 := (hU.preimage hc).mem_nhds (x := σ) (by simp)
  refine Filter.mem_of_superset h1 fun τ hτ h => hσ ?_
  have h2 : (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)
  have h3 : τ x = y := h
  have h4 : σ ((σ⁻¹ * τ) x) = τ x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  show σ x = y
  rw [← h3, ← h4, h2]

private theorem UpperTheory.V.Loc.ci_dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

private theorem UpperTheory.V.Loc.ci_pow_congr {K : Type*} [Monoid K] {x : K} {M a b : ℕ} (hx : x ^ M = 1)
    (h : a ≡ b [MOD M]) : x ^ a = x ^ b := by
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]

private theorem UpperTheory.V.Loc.ci_crt (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (M : ℕ) (hM : M ≠ 0) :
    ∃ c : ℕ, c.Coprime M ∧ c ≡ 1 [MOD ordCompl[l] M] ∧
      ∀ k ≤ M.factorization l, (c : ZMod (l ^ k)) = PadicInt.toZModPow k (a : ℤ_[l]) := by
  have hp : l.Prime := Fact.out
  set v := M.factorization l with hv
  have hcop : Nat.Coprime (ordCompl[l] M) (l ^ v) := (Nat.coprime_ordCompl hp hM).symm.pow_right _
  haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, h1, h2⟩ := Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val
  have hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]
  have hcoP : c.Coprime (l ^ v) := by
    rw [← ZMod.isUnit_iff_coprime, hc]
    exact (Units.isUnit a).map _
  have hcoN : c.Coprime (ordCompl[l] M) := by
    unfold Nat.Coprime
    rw [h1.gcd_eq, Nat.gcd_one_left]
  refine ⟨c, ?_, h1, fun k hk => ?_⟩
  · have := Nat.Coprime.mul_right hcoP hcoN
    rwa [hv, Nat.ordProj_mul_ordCompl_eq_self] at this
  · have hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l]) := by
      rw [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]
    have := (pow_dvd_pow _ hk).trans hd
    rwa [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast] at this

private theorem UpperTheory.V.Loc.ci_fin (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (n : ℕ) :
    ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l),
      (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val := by
  have hp : l.Prime := Fact.out
  obtain ⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)
  have hv : n ≤ M.factorization l :=
    (hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)
  obtain ⟨c, hcM, hc1, hc2⟩ := UpperTheory.V.Loc.ci_crt l a M hM0
  have hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N] := by
    intro N h
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  obtain ⟨σ, hσ⟩ := (UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0
    (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)
  have hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c := by
    intro d ⟨e, he⟩ x hx
    have hxM : x ^ M = 1 := by rw [he, pow_mul, hx, one_pow]
    rw [hσ x hxM]
    exact UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)
  refine ⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩
  · have hmM : m ∣ M := by
      rw [hM]
      exact (Nat.dvd_factorial hm0 hm).mul_right _
    have hm' : m ∣ ordCompl[l] M := Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm
    rw [hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]
  · have hkM : l ^ k ∣ M := by
      rw [hM]
      exact (pow_dvd_pow _ hk).mul_left _
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [hσc _ hkM x hx]
    refine UpperTheory.V.Loc.ci_pow_congr hx ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact hc2 k (le_trans hk hv)

private theorem UpperTheory.V.Loc.ci_surj (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) : ∃ g ∈ Iq l, cyc l l g = a := by
  have hp : l.Prime := Fact.out
  let S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) := fun n =>
    {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        UpperTheory.V.Loc.ci_closed l _ _
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩)
    (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩
  · unfold MaximalUnramifiedExtension at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm0, hlm, hx⟩ := hx
      exact (hσ m).1 m le_rfl hm0 hlm x hx
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)
    have h1 := cyclotomicCharacter.spec l (n := k)
      (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one
    have h2 := (hσ k).2 k le_rfl η hη.pow_eq_one
    have h3 := h1.symm.trans h2
    exact ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

private theorem UpperTheory.V.Loc.ci_inf (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one,
    Nat.pow_eq_one] at h2
  have := hp.one_lt
  omega

theorem UpperTheory.V.Loc.cycInertia :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l]ˣ, ∃ g ∈ Iq l, cyc l l g = u) ∧ ∀ U : Subgroup (GQ l), IsOpen (U : Set (GQ l)) → IsOpen (((U ⊓ Iq l).map (cyc l l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ∧ ∃ s ∈ U ⊓ Iq l, ¬ IsOfFinOrder (cyc l l s) := by
  intro l _
  refine ⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  constructor
  · have hs : Function.Surjective ((cyc l l).comp (Iq l).subtype) := fun u => by
      obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
      exact ⟨⟨g, hg⟩, h⟩
    have he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype) := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by
      rw [he]
      exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((U.isClosed_of_isOpen hU).inter
      (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed
  · obtain ⟨u, hu⟩ := UpperTheory.V.Loc.ci_inf l
    obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    refine ⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩
    rw [map_pow, h] at hf
    exact hf.of_pow hn.ne'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantBlockDetNormEqPowOfMemSpectrum
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem norm_eq_of_aeval_minpoly_eq_zero' {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) (a μ : Om l)
    (h : Polynomial.aeval μ (minpoly L a) = 0) : ‖μ‖ = ‖a‖ := by
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic a) h
  rw [← hσ]
  exact spectralNorm_eq_of_equiv (K := ℚ_[l]) (L := PadicAlgCl l) (σ.restrictScalars ℚ_[l]) μ

private theorem aeval_mul_eq_mul_aeval_of_semiconj {K : Type} [Field K] {d r : ℕ} (F : Matrix (Fin d) (Fin d) K)
    (Y : Matrix (Fin d) (Fin r) K) (F' : Matrix (Fin r) (Fin r) K) (h : F * Y = Y * F')
    (q : Polynomial K) : Polynomial.aeval F q * Y = Y * Polynomial.aeval F' q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    have hpow : ∀ m : ℕ, F ^ m * Y = Y * F' ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, hpow]

private theorem norm_det_eq_pow_of_aeval_minpoly_eq_zero {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ↥L) (a : Om l) (hA : Polynomial.aeval A (minpoly L a) = 0) :
    ‖((A.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  set M : Matrix (Fin r) (Fin r) (Om l) := A.map (algebraMap ↥L (Om l)) with hMdef
  have hdet : ((A.det : ↥L) : Om l) = M.det := by
    rw [hMdef]
    exact RingHom.map_det (algebraMap ↥L (Om l)) A
  have hMp : Polynomial.aeval M (minpoly L a) = 0 := by
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin r)) A (minpoly L a)
    rw [hA, map_zero] at e
    exact e
  have hroot : ∀ μ ∈ M.charpoly.roots, ‖μ‖ = ‖a‖ := by
    intro μ hμ
    have hr : Polynomial.IsRoot M.charpoly μ := (Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hμ
    have hs : μ ∈ spectrum (Om l) M := Matrix.mem_spectrum_of_isRoot_charpoly hr
    have hs2 := spectrum.subset_polynomial_aeval M ((minpoly L a).map (algebraMap ↥L (Om l))) ⟨μ, hs, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hMp] at hs2
    have hz : Polynomial.eval μ ((minpoly L a).map (algebraMap ↥L (Om l))) = 0 := by
      by_contra hx
      rw [spectrum.mem_iff, sub_zero] at hs2
      exact hs2 ((Units.mk0 _ hx).isUnit.map (algebraMap (Om l) (Matrix (Fin r) (Fin r) (Om l))))
    rw [Polynomial.eval_map_algebraMap] at hz
    exact norm_eq_of_aeval_minpoly_eq_zero' L a μ hz
  rw [hdet, Matrix.det_eq_prod_roots_charpoly]
  have hn := map_multiset_prod (normHom : Om l →*₀ ℝ) M.charpoly.roots
  simp only [normHom_apply] at hn
  rw [hn, Multiset.map_congr rfl hroot, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

private theorem exists_invariant_subspace_in_ker_of_det_zero {K : Type} [Field K] {d : ℕ} (F P : Matrix (Fin d) (Fin d) K)
    (hP : P.det = 0) (hc : F * P = P * F) :
    ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) K) (Z : Matrix (Fin r) (Fin d) K) (F' : Matrix (Fin r) (Fin r) K),
      0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ P * Y = 0 := by
  classical
  set W := LinearMap.ker (Matrix.toLin' P) with hWdef
  have hW : W ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hP
    intro h
    have hvW : v ∈ W := by
      rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hv
    rw [h, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hr : 0 < Module.finrank K W := Nat.pos_of_ne_zero (fun h => hW (Submodule.finrank_eq_zero.mp h))
  have hinv : ∀ w ∈ W, Matrix.toLin' F w ∈ W := by
    intro w hw
    rw [hWdef, LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
  set e := (Module.finBasis K W).equivFun
  set ι : (Fin (Module.finrank K W) → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ e.symm.toLinearMap with hι
  have hιker : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp e.symm.injective
  obtain ⟨g, hg⟩ := ι.exists_leftInverse_of_injective hιker
  set G := e.toLinearMap ∘ₗ (Matrix.toLin' F).restrict hinv ∘ₗ e.symm.toLinearMap with hG
  refine ⟨Module.finrank K W, LinearMap.toMatrix' ι, LinearMap.toMatrix' g, LinearMap.toMatrix' G, hr, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · have hcomp : ι ∘ₗ G = Matrix.toLin' F ∘ₗ ι := by
      apply LinearMap.ext
      intro x
      simp [hι, hG, LinearMap.restrict_apply]
    calc F * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' F) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' F ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = LinearMap.toMatrix' (ι ∘ₗ G) := by rw [hcomp]
      _ = _ := LinearMap.toMatrix'_comp _ _
  · have hzero : Matrix.toLin' P ∘ₗ ι = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.zero_apply]
      exact (e.symm x).2
    calc P * LinearMap.toMatrix' ι = LinearMap.toMatrix' (Matrix.toLin' P) * LinearMap.toMatrix' ι := by
          rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (Matrix.toLin' P ∘ₗ ι) := (LinearMap.toMatrix'_comp _ _).symm
      _ = 0 := by rw [hzero, map_zero]

theorem UpperTheory.exists_invariant_block_det_norm_eq_pow_of_mem_spectrum :
    ∀ {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l)) {d : ℕ} (F : Matrix (Fin d) (Fin d) ↥L), ∀ a ∈ spectrum (Om l) (F.map (algebraMap ↥L (Om l))), ∃ (r : ℕ) (Y : Matrix (Fin d) (Fin r) ↥L) (Z : Matrix (Fin r) (Fin d) ↥L) (F' : Matrix (Fin r) (Fin r) ↥L), 0 < r ∧ Z * Y = 1 ∧ F * Y = Y * F' ∧ ‖((F'.det : ↥L) : Om l)‖ = ‖a‖ ^ r := by
  intro l _ L d F a ha
  set p := minpoly (↥L) a with hp
  have hPdet : (Polynomial.aeval F p).det = 0 := by
    have hs2 := spectrum.subset_polynomial_aeval (F.map (algebraMap ↥L (Om l)))
      (p.map (algebraMap ↥L (Om l))) ⟨a, ha, rfl⟩
    beta_reduce at hs2
    rw [Polynomial.eval_map_algebraMap, hp, minpoly.aeval, Polynomial.aeval_map_algebraMap] at hs2
    have e := Polynomial.aeval_algHom_apply ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F (minpoly (↥L) a)
    rw [show ((Algebra.ofId ↥L (Om l)).mapMatrix (m := Fin d)) F = F.map (algebraMap ↥L (Om l)) from rfl] at e
    rw [e, spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hs2
    have h3 : algebraMap ↥L (Om l) (Polynomial.aeval F (minpoly (↥L) a)).det = 0 := by
      rw [RingHom.map_det]
      exact hs2
    exact (map_eq_zero_iff _ (algebraMap ↥L (Om l)).injective).mp h3
  have hcomm : F * Polynomial.aeval F p = Polynomial.aeval F p * F := (aeval_mul_eq_mul_aeval_of_semiconj F F F rfl p).symm
  obtain ⟨r, Y, Z, F', hr, hZY, hFY, hPY⟩ := exists_invariant_subspace_in_ker_of_det_zero F (Polynomial.aeval F p) hPdet hcomm
  have hF' : Polynomial.aeval F' p = 0 := by
    have h1 := aeval_mul_eq_mul_aeval_of_semiconj F Y F' hFY p
    rw [hPY] at h1
    calc Polynomial.aeval F' p = (Z * Y) * Polynomial.aeval F' p := by rw [hZY, Matrix.one_mul]
      _ = Z * (Y * Polynomial.aeval F' p) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← h1, Matrix.mul_zero]
  exact ⟨r, Y, Z, F', hr, hZY, hFY, norm_det_eq_pow_of_aeval_minpoly_eq_zero L F' a hF'⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsSquareSubmatrixDetNeZeroOfLeftInverse
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse :
    ∀ {B : Type} [CommRing B] [IsDomain B] {d r : ℕ} (X : Matrix (Fin d) (Fin r) B) (Z : Matrix (Fin r) (Fin d) B), Z * X = 1 → ∃ s : Fin r → Fin d, (X.submatrix s id).det ≠ 0 := by
  intro B _ _ d r X Z hZX
  classical
  by_contra h
  push_neg at h
  have hM : (Z * X) = fun a => ∑ k, Z a k • X k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det := by
    have e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k) := by
      rw [← hM]
      rfl
    rw [e1]
    have e2 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum
      (fun a k => Z a k • X k)
    simp only [AlternatingMap.coe_multilinearMap] at e2
    rw [e2]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have e3 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ
      (fun a => Z a (s a)) (fun a => X (s a))
    simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3
    rw [e3]
    rfl
  have h0 : (Z * X).det = 0 := by
    rw [key]
    exact Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])
  rw [hZX, Matrix.det_one] at h0
  exact one_ne_zero h0
end

