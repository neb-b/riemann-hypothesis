module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0004
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0006
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0003
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RootEqOfSubMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffMult
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.diff_mult :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by
  intro φ H l hl P _ _
  haveI := H.galois
  obtain ⟨-, -, hram, -⟩ := grp_bridge H hl P
  have hmap : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = span {(l : 𝓞 H.E)} := by
    simp [Ideal.map_span]
  have hne : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≠ ⊥ :=
    map_ne_bot_of_ne_bot (by simp [hl.ne_zero])
  have hmult : multiplicity P (span {(l : 𝓞 H.E)}) = H.el l := by
    rw [← hmap, ← IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hne, hram]
  have hmem : (l : 𝓞 H.E) ∈ P := by
    have hle : span {(l : 𝓞 H.E)} ≤ P := by
      rw [← hmap]
      exact map_le_of_le_comap (Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)})).le
    exact hle (Ideal.mem_span_singleton_self _)
  have hrat := GlobalTheory.DifferentElement.mult_ratio H.E l hl P inferInstance hmem
  rw [hmult, Nat.factorization_def _ hl] at hrat
  have hel0 : (0 : ℝ) < H.el l := by exact_mod_cast HostRaw.el_pos _ l
  have hvd : H.vdH l = (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) / H.el l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hrat
    push_cast at hr
    simp only [HostRaw.vdH, Nat.padicValNat_def]
    exact hr.symm
  have h1 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l := by
    rw [hvd]
    field_simp
  obtain ⟨htw1, htw2, -⟩ := vd_tame_wild H hl
  refine ⟨h1, hmult, fun hnd => ?_, fun hd => ?_⟩
  · have hv := htw1 hnd
    have hle : 1 ≤ H.el l := HostRaw.el_pos _ l
    have h2 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = ((H.el l - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, h1, hv]
      field_simp
      push_cast
      ring
    exact_mod_cast h2
  · have hv := htw2 hd
    have h2 : (H.el l : ℝ) ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
      rw [h1]
      nlinarith
    exact_mod_cast h2
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds2
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.rad_bounds2 :
    ∀ {φ : Frame} (H : HostAx φ), (∀ α β : ℝ, 0 ≤ α → 0 ≤ β → ∑ l ∈ H.ram, (α * H.vdH l + β) * Real.log l ≤ (α + 2 * β) * Real.log H.rd) ∧ (H.d : ℝ) ≤ H.rd ^ 2 ∧ H.d ^ (2 * φ.ord) ∣ (discr H.E).natAbs ∧ 1 / 2 * Real.log H.d ≤ Real.log H.rd ∧ H.ram.card ≤ H.small.card + 2 ∧ ∀ (M : ℕ) (L : ℝ), 0 < M → 0 ≤ L → Real.log M ≤ 30 * L → Real.log H.rd ≤ L / 100 → ((((discr H.E).natAbs * M).primeFactors.card : ℕ) : ℝ) ≤ 44 * L := by
  intro φ H
  have hd0 : (0:ℝ) < H.d := by exact_mod_cast (HostRaw.d_prime H.toHostRaw).pos
  obtain ⟨h67, hle, h8, -, -⟩ := rd_lower H
  have hsq : 0 < √(H.d:ℝ) := Real.sqrt_pos.2 hd0
  have hrd0 : 0 < H.rd := by linarith
  have hlt : √(H.d:ℝ) < H.rd := by
    have h1 : 1 < H.rd / √(H.d:ℝ) := by linarith
    rwa [lt_div_iff₀ hsq, one_mul] at h1
  have hdrd : (H.d:ℝ) ≤ H.rd ^ 2 := by
    nlinarith [Real.mul_self_sqrt hd0.le, hsq]
  have hlogd : 1 / 2 * Real.log H.d ≤ Real.log H.rd := by
    have h := Real.log_le_log hd0 hdrd
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  refine ⟨?_, hdrd, Dvd.intro_left _ (norm_diff_EK H).1, hlogd, ?_, ?_⟩
  · intro α β hα hβ
    rw [(log_rd_sum H).1, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hp : l.Prime := Nat.prime_of_mem_primeFactors hl
    have hv : 1 / 2 ≤ H.vdH l := (mem_ram H hp).2.2.2.1 hl
    have hlog : 0 ≤ Real.log l := Real.log_natCast_nonneg l
    nlinarith [mul_nonneg (mul_nonneg hβ hlog) (by linarith : (0:ℝ) ≤ 2 * H.vdH l - 1)]
  · have hsub : H.ram ⊆ insert H.q (insert H.d H.small) := by
      intro l hl
      have hp : l.Prime := Nat.prime_of_mem_primeFactors hl
      have hN := (log_rd_sum H).2.2.1 hl
      have hdv : l ∣ H.QS * H.q * H.d := Nat.dvd_of_mem_primeFactors hN
      rcases (Nat.Prime.dvd_mul hp).1 hdv with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rw [Finset.mem_insert, Finset.mem_insert]
          right; right
          exact (HostRaw.mem_small_iff H.toHostRaw).2 ⟨hp, h⟩
        · rw [Finset.mem_insert]
          left
          exact (Nat.prime_dvd_prime_iff_eq hp (HostRaw.q_prime H.toHostRaw)).1 h
      · rw [Finset.mem_insert, Finset.mem_insert]
        right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (HostRaw.d_prime H.toHostRaw)).1 h
    calc H.ram.card ≤ (insert H.q (insert H.d H.small)).card := Finset.card_le_card hsub
      _ ≤ (insert H.d H.small).card + 1 := Finset.card_insert_le _ _
      _ ≤ H.small.card + 1 + 1 := by
        have := Finset.card_insert_le H.d H.small
        omega
      _ = H.small.card + 2 := by ring
  · intro M L hM hL hlogM hrdL
    have hlog2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl2 : (0:ℝ) < Real.log 2 := by linarith
    have hram : (((discr H.E).natAbs.primeFactors.card : ℕ) : ℝ) ≤ 2 * Real.log H.rd / Real.log 2 :=
      (rad_bounds H).2.1
    have hMcard : ((M.primeFactors.card : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
      rw [le_div_iff₀ hl2, ← Real.log_pow]
      have h1 : 2 ^ M.primeFactors.card ≤ ∏ p ∈ M.primeFactors, p := by
        calc 2 ^ M.primeFactors.card = ∏ p ∈ M.primeFactors, 2 := by simp
          _ ≤ ∏ p ∈ M.primeFactors, p :=
            Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      have h2 : ∏ p ∈ M.primeFactors, p ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)
      apply Real.log_le_log (by positivity)
      exact_mod_cast h1.trans h2
    by_cases ha : (discr H.E).natAbs = 0
    · rw [ha, zero_mul, Nat.primeFactors_zero, Finset.card_empty]
      push_cast
      linarith
    have hcard : ((((discr H.E).natAbs * M).primeFactors.card : ℕ) : ℝ) ≤
        ((discr H.E).natAbs.primeFactors.card : ℕ) + ((M.primeFactors.card : ℕ) : ℝ) := by
      rw [Nat.primeFactors_mul ha hM.ne']
      exact_mod_cast Finset.card_union_le _ _
    have hsum : 2 * Real.log H.rd / Real.log 2 + Real.log M / Real.log 2 ≤ 44 * L := by
      rw [← add_div, div_le_iff₀ hl2]
      nlinarith [mul_le_mul_of_nonneg_left hlog2.le hL]
    linarith
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.inertQ
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem ordCompl_q {φ : Frame} (H : HostRaw φ) : ordCompl[H.q] H.condN = H.QS * H.d := by
  have hq := H.q_prime
  have hQd : H.QS * H.d ≠ 0 := Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero
  have hnd : ¬ H.q ∣ H.QS * H.d := fun h =>
    hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm H.coprime_QSd_q) h)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hfac : H.condN.factorization H.q = 1 := by
    rw [hN, Nat.factorization_mul hQd hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, hq.factorization_self]
  rw [hfac, pow_one, hN]
  exact Nat.mul_div_cancel _ hq.pos

private theorem QSd_dvd {φ : Frame} (H : HostRaw φ) : H.QS * H.d ∣ H.condN :=
  ⟨H.q, by unfold HostRaw.condN; ring⟩

private theorem cyc_unitsOne {φ : Frame} (H : HostRaw φ) : IsCyclic (H.unitsOne (H.QS * H.d)) := by
  haveI : Fact (Nat.Prime H.q) := ⟨H.q_prime⟩
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  haveI : NeZero H.condN := ⟨by
    rw [hN]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_ne_zero H.d_prime.ne_zero) H.q_prime.ne_zero⟩
  let f : H.unitsOne (H.QS * H.d) →* ZMod H.q :=
    (Units.coeHom (ZMod H.q)).comp ((ZMod.unitsMap H.q_dvd_condN).comp (Subgroup.subtype _))
  refine isCyclic_of_injective_ringHom f ?_
  intro a b hab
  have ha := (H.mem_unitsOne (QSd_dvd H) a).1 a.2
  have hb := (H.mem_unitsOne (QSd_dvd H) b).1 b.2
  have hq : ((a : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ ((b : (ZMod H.condN)ˣ) : ZMod H.condN).val [MOD H.q] := by
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply, Subgroup.coe_subtype,
      ZMod.unitsMap_val] at hab
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
    exact hab
  have hm := (Nat.modEq_and_modEq_iff_modEq_mul H.coprime_QSd_q).1 ⟨ha.trans hb.symm, hq⟩
  rw [← hN] at hm
  have := Nat.ModEq.eq_of_lt_of_lt hm (ZMod.val_lt _) (ZMod.val_lt _)
  exact Subtype.ext (Units.ext (ZMod.val_injective _ this))

private theorem el_q_dvd {φ : Frame} (H : HostRaw φ) : H.el H.q ∣ 2 := by
  show Nat.card (H.inertG H.q) ∣ 2
  show Nat.card (H.imgOne (H.condN / H.q ^ H.condN.factorization H.q)) ∣ 2
  rw [ordCompl_q H]
  show Nat.card (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) ∣ 2
  haveI := cyc_unitsOne H
  haveI : IsCyclic (Subgroup.map H.art (H.unitsOne (H.QS * H.d))) :=
    isCyclic_of_surjective (H.art.subgroupMap _) (H.art.subgroupMap_surjective _)
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  rintro ⟨g, hg⟩
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact H.art_q u ((H.mem_unitsOne (QSd_dvd H) u).1 hu)

private theorem el_q_ne_one {φ : Frame} (H : HostRaw φ) (h : H.PsQ) : H.el H.q ≠ 1 := by
  intro h1
  have hq := H.q_prime
  have hbot : H.inertG H.q = ⊥ := Subgroup.card_eq_one.1 h1
  obtain ⟨p, hp1, hp2⟩ := Nat.chineseRemainder H.coprime_QSd_q 1 (H.q - 1)
  have hN : H.condN = H.QS * H.d * H.q := by
    show H.QS * H.q * H.d = H.QS * H.d * H.q
    ring
  have hcq : Nat.Coprime p H.q := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp2, Nat.gcd_comm, ← Nat.Coprime, hq.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by have := hq.two_le; omega) (by have := hq.two_le; omega)
  have hcQd : Nat.Coprime p (H.QS * H.d) := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hp1, Nat.gcd_one_left]
  have hcop : Nat.Coprime p H.condN := by
    rw [hN]
    exact Nat.Coprime.mul_right hcQd hcq
  set u := ZMod.unitOfCoprime p hcop
  have hu : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hcop
  have hmem : H.art u ∈ H.inertG H.q := by
    refine (H.mem_inertG H.q _).2 ⟨u, ?_, rfl⟩
    rw [ordCompl_q H]
    exact (hu.of_dvd (QSd_dvd H)).trans hp1
  rw [hbot, Subgroup.mem_bot] at hmem
  have hJ := h u
  rw [hmem, jacobi_congr ((hu.of_dvd H.q_dvd_condN).trans hp2)] at hJ
  have hc : ((H.q - 1 : ℕ) : ℤ) = -1 + (H.q : ℤ) * 1 := by
    push_cast [Nat.cast_sub hq.one_le]
    ring
  rw [hc, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left,
    jacobiSym.at_neg_one (hq.odd_of_ne_two H.q_ne_two), ZMod.χ₄_nat_three_mod_four H.q_mod_four] at hJ
  simp at hJ

theorem UpperTheory.HF.inert_q :
    ∀ {φ : Frame} (H : HostAx φ), H.el H.q ≤ 2 ∧ H.sl H.q = 1 ∧ (H.q ∈ H.ram → H.el H.q = 2 ∧ H.vdH H.q = 1 / 2 ∧ H.condE.factorization H.q = 1) ∧ (H.q ∉ H.ram → H.vdH H.q = 0) ∧ (H.PsQ → H.q ∈ H.ram) := by
  intro φ H
  have hq := H.q_prime
  have h2 := el_q_dvd H.toHostRaw
  have hndvd : ¬ H.q ∣ H.el H.q := fun h =>
    H.q_ne_two ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (h.trans h2))
  have htw := vd_tame_wild H hq
  have hram := mem_ram H hq
  have hs : H.sl H.q = 1 := htw.2.2 hndvd
  refine ⟨Nat.le_of_dvd two_pos h2, hs, fun hmem => ?_, fun hmem => ?_, fun hP => ?_⟩
  · have hel : H.el H.q = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
      · exact absurd h (hram.1.1 hmem)
      · exact h
    refine ⟨hel, ?_, ?_⟩
    · rw [htw.1 hndvd, hel]
      norm_num
    · have hpos := (condE_spec H.toHostRaw).2.1
      have hdvd : H.q ∣ H.condE := hram.2.1.1 hmem
      have hle : H.condE.factorization H.q ≤ 1 := by
        have h : max 1 (H.condE.factorization H.q) = 1 := hs
        exact max_eq_left_iff.1 h
      exact le_antisymm hle ((hq.dvd_iff_one_le_factorization hpos.ne').1 hdvd)
  · by_contra h
    exact hmem (hram.2.2.1.2 h)
  · exact hram.1.2 (el_q_ne_one H.toHostRaw hP)
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.locRoots
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Formalism.HC.Der Formalism.TwoAdicCyclotomicDecomposition

private theorem stab_iff (N : ℕ) [NeZero N] (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime]
    [Q.LiesOver (span {(l : ℤ)})] (u : (ZMod N)ˣ) :
    tauN N u ∈ MulAction.stabilizer _ Q ↔ ∃ k : ℕ, (u : ZMod N).val ≡ l ^ k [MOD ordCompl[l] N] := by
  set M := ordCompl[l] N with hM
  have hMN : M ∣ N := Nat.ordCompl_dvd N l
  have hlM : l.Coprime M := Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)
  obtain ⟨u0, hu0⟩ := exists_unit_modEq (N := N) hMN l hlM
  have hF : IsArithFrobAt ℤ (tauN N u0) Q := tauN_frob N l Q u0 hu0
  have hu0' : ((ZMod.unitsMap hMN u0 : (ZMod M)ˣ) : ZMod M) = (l : ZMod M) :=
    (val_modEq_iff hMN u0 l).mp hu0
  constructor
  · intro hs
    obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul l Q (tauN N u0) (tauN N u) hF hs
    obtain ⟨w, rfl⟩ := (tauN N).surjective ρ
    refine ⟨k, ?_⟩
    have hw1 : ZMod.unitsMap hMN w = 1 :=
      (val_modEq_one_iff hMN w).mp ((tauN_inertia_iff N l Q w).mp hρ)
    have huw : u = w * u0 ^ k := (tauN N).injective (by rw [map_mul, map_pow]; exact hρeq)
    rw [val_modEq_iff hMN, huw, map_mul, map_pow, hw1, one_mul, Units.val_pow_eq_pow_val, hu0',
      Nat.cast_pow]
  · rintro ⟨k, hk⟩
    have hw1 : ZMod.unitsMap hMN (u * (u0 ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
      apply Units.ext
      rw [(val_modEq_iff hMN u _).mp hk, Units.val_pow_eq_pow_val, hu0', Nat.cast_pow]
    have hwin := (tauN_inertia_iff N l Q (u * (u0 ^ k)⁻¹)).mpr ((val_modEq_one_iff hMN _).mpr hw1)
    have hwst := Decomp.mem_stab_of _ Q (smul_mem_of_inertia _ Q hwin)
    have hFst := IsArithFrobAt.mem_stabilizer hF
    have hu : u = (u * (u0 ^ k)⁻¹) * u0 ^ k := by rw [inv_mul_cancel_right]
    rw [hu, map_mul, map_pow]
    exact Subgroup.mul_mem _ hwst (Subgroup.pow_mem _ hFst k)

private theorem act_of (N : ℕ) [NeZero N] {K : Type*} [Field K] (J : Cond.Cyc N →+* K) (σ : K →+* K) (u : (ZMod N)ˣ)
    (h : ∀ x, σ (J x) = J (tauN N u x)) (x : K) (hx : x ^ N = 1) : σ x = x ^ (u : ZMod N).val := by
  have hζ := (zO_prim N).map_of_injective (f := algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N))
    (FaithfulSMul.algebraMap_injective _ _)
  have hJ := hζ.map_of_injective J.injective
  obtain ⟨i, -, rfl⟩ := hJ.eq_pow_of_pow_eq_one hx
  have hg : IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N) (tauN N u) = u :=
    MulEquiv.apply_symm_apply _ _
  have hτ : tauN N u (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) =
      (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) ^ (u : ZMod N).val := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) (tauN N u) hζ.pow_eq_one,
      hg]
  rw [map_pow, h, hτ, map_pow]
  ring

end

theorem UpperTheory.HF.loc_roots :
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] ∧ ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val) ∧ ∀ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] → ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val := by
  intro l _ M hM
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI := Formalism.HC.Der.cyc_isGalois M
  let J : Cond.Cyc M →+* PadicAlgCl l := (IsAlgClosed.lift : Cond.Cyc M →ₐ[ℚ] PadicAlgCl l).toRingHom
  obtain ⟨P, hPp, hPlo, -, hstab, hsurj, -⟩ := UpperTheory.HF.loc_onto l (Cond.Cyc M) J
  haveI := hPp
  haveI := hPlo
  constructor
  · intro σ
    obtain ⟨τ, hτ⟩ := hsurj σ
    obtain ⟨u, rfl⟩ := (Formalism.HC.Der.tauN M).surjective τ
    have hst : Formalism.HC.Der.tauN M u ∈ MulAction.stabilizer _ P := (hstab _).mpr ⟨σ, hτ⟩
    obtain ⟨k, hk⟩ := (stab_iff M l P u).mp hst
    exact ⟨u, k, hk, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hτ x hx⟩
  · intro u j hj
    obtain ⟨σ, hσ⟩ := (hstab (Formalism.HC.Der.tauN M u)).mp ((stab_iff M l P u).mpr ⟨j, hj⟩)
    exact ⟨σ, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hσ x hx⟩
end

