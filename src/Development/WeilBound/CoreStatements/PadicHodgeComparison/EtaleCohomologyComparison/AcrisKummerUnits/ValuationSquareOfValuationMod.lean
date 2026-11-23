module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0029
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem CrystallineSemistableComparison.RL.surj_pass : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := GlobalTheory.T.surjective_preserves_closedness_comparability

theorem CrystallineSemistableComparison.RL.glue : ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' → Q (e + e')) → (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := _root_.GlobalTheory.CompanionTheory.Idem.glue_idempotent_property

theorem CrystallineSemistableComparison.RL.dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime → (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧ (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := _root_.GlobalTheory.CompanionTheory.CompDich.dich_comp

theorem CrystallineSemistableComparison.RL.val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := _root_.GlobalTheory.CompanionTheory.Idem.val_of_dich

theorem CrystallineSemistableComparison.RL.valuation_square_of_valuation_mod : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  intro S _ ϖ _ h P hP f g
  have hcomp := GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span ϖ h P hP f g
  exact hcomp

theorem CrystallineSemistableComparison.RL.dich_of_mod : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := _root_.GlobalTheory.CompanionTheory.DichMod.dich_of_mod

open Polynomial in
theorem CrystallineSemistableComparison.RL.step_comp : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA
  have hStep : Step ϖ := by
    intro Q n hQ hd hn
    have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
    have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
    have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
      Ideal.subset_span (by simp)
    rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
    · refine ⟨0, ?_, ?_⟩
      · rw [← hq0]; exact hdiv
      · rw [zero_pow hd.ne']; exact dvd_zero _
    ·
      have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
      have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
        intro x hx
        obtain ⟨e, he⟩ := hdiv
        have h0 : ϖ ^ (n + 1) * x = 0 := by
          rw [he]; linear_combination e * hx
        exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
      obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := _root_.GlobalTheory.CompanionTheory.NewtonSlope.first_slope ϖ hD hRoots (fun i => Q.coeff i)
        Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
      have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
          (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
        intro i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
        · by_cases hid : i ≤ Q.natDegree
          · obtain ⟨t, ht⟩ := hc1 i hi hid
            exact ⟨t, fun h => by omega, fun _ => ht⟩
          · exact ⟨0, fun h => by omega, fun h => by omega⟩
      choose s hs0 hsd using hs
      have hunit : IsUnit (s i0) := by
        obtain ⟨t, ht⟩ := hi3
        have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
          have h6 := hsd i0 hi2
          rw [h6] at ht
          linear_combination -ht
        have h7 := hcancel _ h5
        exact IsUnit.of_mul_eq_one t (by linear_combination h7)
      let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (s i) * Polynomial.X ^ i
      have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
        intro j hj'
        simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        simp [Nat.lt_succ_of_le hj']
      have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
        intro y
        simp [R, Polynomial.eval_finsetSum]
      let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
      have hP0 : P.coeff 0 = 1 := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
      have hPi : IsUnit (P.coeff i0) := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc i0 hi2]
        exact hunit.map _
      have hroot : ∃ y', P.eval y' = 0 := by
        let T := S ⧸ Ideal.span {ϖ ^ 2}
        rcases subsingleton_or_nontrivial T with hT | hT
        · exact ⟨0, Subsingleton.elim _ _⟩
        have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
          GlobalTheory.CompanionTheory.NewtonStep.isUnit_or_of_add_quot ϖ hj hD
        have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
            ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
          intro d
          induction d with
          | zero =>
            intro F hF hdeg k hk
            omega
          | succ d ih =>
            intro F hF hdeg k hk hcoeff
            obtain ⟨x, hx⟩ := hA F hF (by omega)
            by_cases hxu : IsUnit x
            · obtain ⟨u, rfl⟩ := hxu
              exact ⟨u, hx⟩
            let G := F /ₘ (X - C x)
            have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
            have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
            have hGdeg : G.natDegree = d := by
              have h := (monic_X_sub_C x).natDegree_mul hG
              rw [hfactor, hdeg, natDegree_X_sub_C] at h
              omega
            cases k with
            | zero =>
              rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
              have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
            | succ k =>
              rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
              rcases hAdd _ _ hcoeff with hGu | hneg
              · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
                exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
              · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                  simpa only [neg_neg] using hneg.neg
                exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
        have htd : P.natTrailingDegree = 0 :=
          Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
        have hmon : P.reverse.Monic := by
          rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
        have hdeg : P.reverse.natDegree = P.natDegree := by
          rw [reverse_natDegree, htd, Nat.sub_zero]
        have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
        have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
          rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
          congr 1
          omega
        obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
          (by omega) (hcoeff.symm ▸ hPi)
        refine ⟨↑(u⁻¹), ?_⟩
        let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
        have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
        have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
        rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
        exact hre.symm
      obtain ⟨y', hy'⟩ := hroot
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
      have hRy : ϖ ^ 2 ∣ R.eval y := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
        simp only [P, Polynomial.eval_map] at hy'
        rwa [Polynomial.eval₂_at_apply] at hy'
      have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
        rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        rw [mul_pow]
        linear_combination (y ^ i) * h8
      have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
      refine ⟨c * y, ?_, ?_⟩
      · rw [hQz]
        have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
        refine dvd_trans ?_ h9
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
          have h11 := hc1 Q.natDegree hd le_rfl
          simpa [hQ.coeff_natDegree] using h11
        rw [mul_pow]
        exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _
  exact hStep

theorem CrystallineSemistableComparison.RL.step_glob : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := GlobalTheory.T.newton_approximation_local_to_global

theorem CrystallineSemistableComparison.RL.pow_dvd : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z := _root_.GlobalTheory.CompanionTheory.ValPowDvd.dvd_of_pow_mul_dvd_pow

theorem CrystallineSemistableComparison.RL.aic_limit : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := GlobalTheory.T.absolutely_integrally_closed_of_newton

theorem CrystallineSemistableComparison.RL.int_closed : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := _root_.GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral

theorem CrystallineSemistableComparison.RL.loc_aic : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc (S := S) ∧ Loc (S := Localization.Away ϖ)) ∧ (Aic (S := S) → Aic (S := Localization.Away ϖ)) := by
  intro S _ ϖ
  have hloc := GlobalTheory.CompanionTheory.LocAic.main ϖ
  exact hloc

theorem CrystallineSemistableComparison.RL.val_pow : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := _root_.GlobalTheory.CompanionTheory.PowComp.val_pow

theorem CrystallineSemistableComparison.RL.split_pt : ∀ {S : Type} [CommRing S] , Aic (S := S) → Loc (S := S) → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨B, i, hi, z, hz⟩ := Y.exists_Spec_apply_eq y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S B := φ.hom.toAlgebra
  have : Algebra.Etale S B := RingHom.etale_algebraMap.1 hφe
  let Q : Ideal B := z.asIdeal
  have hQ : Q.IsPrime := z.2
  have hQm : Q.comap (algebraMap S B) = m := by
    have hx : (Spec.map φ) z = x := by rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal hx
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  let q := Q.map (algebraMap B Bg)
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hq : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : q.comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hqm : q.comap (algebraMap S Bg) = m := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap, hQm]
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := Bg)
  have hroot_of_mem (F : Polynomial S) (hF : F.Monic) (hmem : Polynomial.aeval P.x F ∈ q) :
      ∃ b : S, F.IsRoot b ∧ P.x - algebraMap S Bg b ∈ q := by
    have : Nontrivial S := nontrivial_of_ne 0 1 fun h =>
      hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))
    induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
    | ind n ih =>
      by_cases hn : n = 0
      · have h1 := Polynomial.eq_one_of_monic_natDegree_zero hF (hd.trans hn)
        rw [h1, map_one] at hmem
        exact (hq.ne_top ((Ideal.eq_top_iff_one q).2 hmem)).elim
      obtain ⟨b, hb⟩ := hA F hF (by omega)
      let G := F /ₘ (Polynomial.X - Polynomial.C b)
      have hFG : (Polynomial.X - Polynomial.C b) * G = F :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.2 hb
      have hG : G.Monic := (Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C b))
        (hFG.symm ▸ hF)
      have hdeg := (Polynomial.monic_X_sub_C b).natDegree_mul hG
      rw [hFG, Polynomial.natDegree_X_sub_C, hd] at hdeg
      rw [← hFG, map_mul] at hmem
      rcases hq.mem_or_mem hmem with hbq | hGq
      · exact ⟨b, hb, by simpa using hbq⟩
      · obtain ⟨c, hc, hcq⟩ := ih G.natDegree (by omega) G hG hGq rfl
        exact ⟨c, by rw [← hFG, Polynomial.IsRoot, Polynomial.eval_mul, hc, mul_zero], hcq⟩
  obtain ⟨b, hb, hbq⟩ := hroot_of_mem P.f P.monic_f (P.hasMap.1.symm ▸ q.zero_mem)
  let c : S := Polynomial.eval b P.g
  have hcm : c ∉ m := by
    rw [← hqm]
    intro hcq
    have hdvd : P.x - algebraMap S Bg b ∣ Polynomial.aeval P.x P.g - algebraMap S Bg c := by
      have h := Polynomial.sub_dvd_eval_sub P.x (algebraMap S Bg b) (P.g.map (algebraMap S Bg))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at h
    have hgq : Polynomial.aeval P.x P.g ∈ q := by
      simpa using q.add_mem (Ideal.mem_of_dvd q hdvd hbq) (show algebraMap S Bg c ∈ q from hcq)
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hgq P.hasMap.2)
  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ m := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ m := by
    intro hem
    have h1 : (1 : S) ∈ m := by simpa using m.add_mem hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have hmul : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [hmul] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hb.eq_zero, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  let ψ := ((P.P.lift _ hmap).comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom S B Bg)
  refine ⟨e, he, hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

theorem CrystallineSemistableComparison.RL.sec_rules : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := _root_.GlobalTheory.CompanionTheory.SecRules.main

theorem CrystallineSemistableComparison.RL.sec_add : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)) (e e' : S), IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → SecOn f e → SecOn f e' → SecOn f (e + e') := _root_.GlobalTheory.CompanionTheory.SecAdd.secOn_add

theorem CrystallineSemistableComparison.RL.pd_quot : ∀ {S : Type} [CommRing S] , TF (S := S) → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  intro S _ hS I J hI hJ
  have hpd := GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient hS I J hI hJ
  exact hpd

theorem CrystallineSemistableComparison.RL.pd_mor : ∀ {S : Type} [CommRing S] {S' E E' : Type} [CommRing S'] [CommRing E] [CommRing E'] (π : S →+* E) (π' : S' →+* E') (I : Ideal S) (I' : Ideal S') {J : Ideal E} {J' : Ideal E'} (δ : DividedPowers J) (δ' : DividedPowers J') (F₀ : S →+* S') (F : E →+* E'), Function.Surjective π → PdI I → IsPd π I δ → IsPd π' I' δ' → (∀ x ∈ I, F₀ x ∈ I') → (∀ x, F (π x) = π' (F₀ x)) → DividedPowers.IsDPMorphism δ δ' F := _root_.GlobalTheory.CompanionTheory.PdMor.isDPMorphism_of_isPd
