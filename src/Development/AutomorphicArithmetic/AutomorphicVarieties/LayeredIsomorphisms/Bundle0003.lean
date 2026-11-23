module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Exc
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.exc :
    ∀ (l R : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀], ABound l R L₀ →
      ∃ c : ℕ, (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ c)) ∧ ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound l R c L₀ Z Exc := by
  intro l R _ L₀ _ h
  classical
  obtain ⟨⟨K, _, _, hU, c, R', s, hR', hζ, hb⟩, -⟩ := h
  refine ⟨c, hζ, fun Z => ?_⟩
  obtain ⟨near, hnear⟩ : ∃ near : Fin R' → Finset ℕ, near = fun i =>
      (Finset.Icc 1 Z : Finset ℕ).filter
        (fun e : ℕ => ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ))) :=
    ⟨_, rfl⟩
  refine ⟨Finset.univ.biUnion near, ?_⟩
  unfold FirstBound
  refine ⟨?_, ?_⟩
  · have hone : ∀ i : Fin R', (near i).card ≤ 1 := by
      intro i
      rw [Finset.card_le_one]
      intro a ha b hb'
      rw [hnear] at ha hb'
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb'
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb'.1.1 hb'.1.2 ha.2 hb'.2
    calc (Finset.univ.biUnion near).card ≤ ∑ i : Fin R', (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin R', 1 := Finset.sum_le_sum (fun i _ => hone i)
      _ = R' := by simp
      _ ≤ R := hR'
  · intro e he1 heZ hne m L₁ _ _ _ hL
    have hfar : ∀ i : Fin R', (l : ℝ) ^ (-(Nat.log l Z : ℤ)) ≤ ‖s i - (e : K)‖ := by
      intro i
      by_contra hlt
      push_neg at hlt
      apply hne
      rw [hnear]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨i, ⟨he1, heZ⟩, hlt⟩
    have h1 := hb e he1 m L₁ hL (Nat.log l Z) hfar
    exact h1.trans (by gcongr)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Klen
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem isTotallyComplex_of_hasMuQ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (h : HasMuQ l L) :
    IsTotallyComplex L := by
  obtain ⟨ζ, hζ⟩ := h
  set n := if l = 2 then 4 else l with hn
  have hn2 : 2 < n := by
    have := (Fact.out : l.Prime).two_le
    rw [hn]; split_ifs with h2
    · norm_num
    · omega
  have : NeZero n := ⟨by omega⟩
  have : IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsTotallyComplex (IntermediateField.adjoin ℚ {ζ}) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (IntermediateField.adjoin ℚ {ζ}) hn2
  exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {ζ}) L

theorem UpperTheory.V.Win.klen :
    ∀ CK : ℝ, LemmaK CK → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
      [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ e : ℕ, 1 ≤ e →
        VLen D e ≠ ⊤ ∧ ((VLen D e).toNat : ℝ) ≤ 2 * kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
  intro CK hK l _ L Ω _ _ _ _ _ D hmu e he
  have htc := isTotallyComplex_of_hasMuQ l L hmu
  obtain ⟨hfin, hlog⟩ := hK l L Ω D htc hmu e he
  obtain ⟨k, hlen, hcard⟩ := Kum.lenOfCard l (ReciprocityTheory.Gal.H2 (zlTw D ((e : ℤ) + 1)))
  have hV : VLen D e = (k : ℕ∞) := hlen
  refine ⟨by rw [hV]; exact ENat.coe_ne_top k, ?_⟩
  rw [hV, ENat.toNat_coe]
  rw [hcard] at hlog
  push_cast at hlog
  rw [Real.log_pow] at hlog
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlogl : (1 / 2 : ℝ) ≤ Real.log l := by
    have h1 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkB : (0 : ℝ) ≤ kBound CK e (Module.finrank ℚ L) (discr L).natAbs := by
    unfold kBound; exact (Real.exp_pos _).le
  nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Layeremb
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.layeremb :
    ∀ (l j N : ℕ), l.Prime → 0 < N → ∀ (L₀ L₁ : Type) [Field L₀] [NumberField L₀] [Field L₁] [NumberField L₁]
      [Algebra L₀ L₁], Nonempty (L₀ →ₐ[ℚ] CyclotomicField N ℚ) → IsLayer l j L₀ L₁ →
        ∃ N' : ℕ, 0 < N' ∧ N' ≤ 2 * Module.finrank ℚ L₁ * N ∧ Nonempty (L₁ →ₐ[ℚ] CyclotomicField N' ℚ) := by
  intro l j N hl hN L₀ L₁ _ _ _ _ _ ⟨f⟩ ⟨⟨k, hk⟩, _⟩
  have hlk : 0 < l ^ k := pow_pos hl.pos k
  have hM : 0 < l ^ k * N := Nat.mul_pos hlk hN
  haveI : NeZero (l ^ k) := ⟨hlk.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  haveI : NeZero ((l ^ k * N : ℕ) : ℚ) := ⟨by exact_mod_cast hM.ne'⟩
  refine ⟨l ^ k * N, hM, ?_, ?_⟩
  · exact Nat.mul_le_mul_right N (rootdeg L₁ l k hl ⟨_, IsCyclotomicExtension.zeta_spec (l ^ k) L₀ L₁⟩)
  · obtain ⟨ζ, hζ⟩ := @IsCyclotomicExtension.exists_isPrimitiveRoot _ ℚ (CyclotomicField (l ^ k * N) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension _ ℚ) _ (Set.mem_singleton _) hM.ne'
    have hN' := hζ.pow hM rfl
    have hl' := hζ.pow hM (Nat.mul_comm _ _)
    have i2 := @IsCyclotomicExtension.isSplittingField_X_pow_sub_one N _ ℚ (CyclotomicField N ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension N ℚ)
    let e : CyclotomicField N ℚ →+* CyclotomicField (l ^ k * N) ℚ :=
      (@Polynomial.IsSplittingField.lift (CyclotomicField (l ^ k * N) ℚ) ℚ (CyclotomicField N ℚ) _ _ _ _ _
        (Polynomial.X ^ N - 1) i2 (by simpa using Polynomial.X_pow_sub_one_splits hN')).toRingHom
    letI : Algebra L₀ (CyclotomicField (l ^ k * N) ℚ) := (e.comp f.toRingHom).toAlgebra
    haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one (l ^ k) L₀ L₁
    let h : L₁ →ₐ[L₀] CyclotomicField (l ^ k * N) ℚ :=
      Polynomial.IsSplittingField.lift _ (Polynomial.X ^ (l ^ k) - 1)
        (by simpa using Polynomial.X_pow_sub_one_splits hl')
    exact ⟨h.toRingHom.toRatAlgHom⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Window
section
open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

theorem UpperTheory.V.Win.window :
    ∀ (R : ℕ) (eta Ct X : ℝ) (Exc : Finset ℕ), 0 < eta → eta ≤ Ct → 1 < X → Exc.card ≤ R →
      ∃ Y : ℝ, InRange (2 ^ (R + 2) * (Ct / eta) ^ R) X Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good eta Ct Exc x := by
  intro R eta Ct X Exc heta hle hX hcard
  classical
  have hCt : 0 < Ct := lt_of_lt_of_le heta hle
  have hX0 : 0 < X := by linarith
  have hB : 1 ≤ Ct / eta := (one_le_div heta).mpr hle
  obtain ⟨y, hy1, hy2, hy3⟩ := UpperTheory.V.Win.window1 R (Ct / eta) (Real.log X)
    (Exc.image fun e : ℕ => Real.log (e : ℝ) / Ct) hB (Real.log_pos hX)
    (le_trans Finset.card_image_le hcard)
  have hsq : Real.exp y ^ (2 : ℝ) = Real.exp (2 * y) := by
    rw [← Real.exp_mul, mul_comm]
  refine ⟨Real.exp y, ⟨?_, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hX0, Real.exp_le_exp, mul_one_div]
    exact hy1
  · rw [hsq, ← Real.le_log_iff_exp_le hX0]
    exact hy2
  · intro x hx1 hx2 e he hex
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos y) hx1
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0
      simpa using (Real.rpow_pos_of_pos hx0 eta).le
    have he0 : (0 : ℝ) < e := by exact_mod_cast hpos
    have hu1 : y ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx1
    have hu2 : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx0, ← hsq]
      exact hx2
    have hu3 : Real.log (e : ℝ) / Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt, mul_comm, ← Real.log_rpow hx0]
      exact Real.log_le_log he0 hex
    have h := hy3 _ (Finset.mem_image_of_mem _ he) (Real.log x) hu1 hu2 hu3
    have h' : Ct / eta * (Real.log (e : ℝ) / Ct) = Real.log (e : ℝ) / eta := by
      field_simp
    rw [h', div_le_iff₀ heta] at h
    rw [Real.rpow_def_of_pos hx0, ← Real.log_le_iff_le_exp he0]
    exact h
end

