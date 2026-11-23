module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocEq
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocEqAux
variable {L : Type} [Field L] [Algebra ℂ L]

private def locRes {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ) : R →ₐ[ℂ] ℂ :=
  e.comp (Subalgebra.inclusion h)

private lemma loc_val_eq {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ)
    (hB : B ≤ loc R (locRes h e)) :
    loc B e = loc R (locRes h e) ∧ ∀ v c, Val B e v c ↔ Val R (locRes h e) v c := by
  have key : ∀ {b v : L} (hb : b ∈ B) (hbv : b * v ∈ B),
      ∃ t : L, ∃ (ht : t ∈ B), e ⟨t, ht⟩ ≠ 0 ∧ t * b ∈ R ∧ t * b * v ∈ R := by
    intro b v hb hbv
    obtain ⟨⟨r, hr⟩, hr0, hrb⟩ := hB hb
    obtain ⟨⟨r', hr'⟩, hr'0, hr'bv⟩ := hB hbv
    refine ⟨r' * r, B.mul_mem (h hr') (h hr), ?_, ?_, ?_⟩
    · rw [show (⟨r' * r, B.mul_mem (h hr') (h hr)⟩ : B) = ⟨r', h hr'⟩ * ⟨r, h hr⟩ from rfl, map_mul]
      exact mul_ne_zero hr'0 hr0
    · rw [mul_assoc]
      exact R.mul_mem hr' hrb
    · have hre : r' * r * b * v = r * (r' * (b * v)) := by ring
      rw [hre]
      exact R.mul_mem hr hr'bv
  refine ⟨le_antisymm ?_ ?_, fun v c => ⟨?_, ?_⟩⟩
  · rintro v ⟨⟨b, hb⟩, hb0, hbv⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨⟨t * b, htb⟩, ?_, htbv⟩
    show e ⟨t * b, h htb⟩ ≠ 0
    rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_ne_zero ht0 hb0
  · rintro v ⟨⟨r, hr⟩, hr0, hrv⟩
    exact ⟨⟨r, h hr⟩, hr0, h hrv⟩
  · rintro ⟨b, hb, hbv, hb0, hval⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨t * b, htb, htbv, ?_, ?_⟩
    · show e ⟨t * b, h htb⟩ ≠ 0
      rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
      exact mul_ne_zero ht0 hb0
    · show e ⟨t * b * v, h htbv⟩ = e ⟨t * b, h htb⟩ * c
      rw [show (⟨t * b * v, h htbv⟩ : B) = ⟨t, ht⟩ * ⟨b * v, hbv⟩ from Subtype.ext (mul_assoc _ _ _),
        show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, hval, mul_assoc]
  · rintro ⟨r, hr, hrv, hr0, hval⟩
    exact ⟨r, h hr, h hrv, hr0, hval⟩

end LocEqAux

section LocEqAux2

private lemma mem_rB_of {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {f : F}
    (hf : f ∈ rA ℂ x I) : algebraMap F L f ∈ rB ℂ L x I := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hx : algebraMap F L f = algebraMap (rA ℂ x I) L ⟨f, hf⟩ := rfl
  rw [hx]
  exact isIntegral_algebraMap

private lemma div_mem_rA {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

end LocEqAux2

theorem UpperTheory.Gal.productCup_of_system.locEq_of :
    ValBasic → RYBasic → LocEq := by
  intro hV hY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY0 I J i hi e
  obtain ⟨hRY0, -, hmono, h4, h5⟩ := hY F K K' d x j2 hY0
  have hRB : rB ℂ K' (xv x) {i} ≤ RY (xv x) j2 I J := by
    have hle := hmono {i} I ∅ J (Finset.singleton_subset_iff.mpr hi) (Finset.empty_subset _)
    rwa [hRY0] at hle
  obtain ⟨hRloc, -, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {i}) (locRes hRB e)
  obtain ⟨j, hj⟩ := hY0.cov i (locRes hRB e)
  have hIB : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := le_sup_left
  have hR2B : R2 (xv x) j2 J ≤ RY (xv x) j2 I J := le_sup_right
  have unit_lemma : ∀ {y w w' : K'}, w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      w' ∈ RY (xv x) j2 I J → w * w' = 1 → y * w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      y ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y w w' hw hw' hww hyw
    obtain ⟨⟨b, hbR⟩, hb0, hbw⟩ := hw
    have hne : locRes hRB e ⟨b * w, hbw⟩ ≠ 0 := by
      intro h0
      have hprod : e ⟨b * w, hRB hbw⟩ * e ⟨w', hw'⟩ = e ⟨b, hRB hbR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show b * w * w' = b
        rw [mul_assoc, hww, mul_one]
      rw [show e ⟨b * w, hRB hbw⟩ = 0 from h0, zero_mul] at hprod
      exact hb0 hprod.symm
    have hval : Val (rB ℂ K' (xv x) {i}) (locRes hRB e) w
        (locRes hRB e ⟨b * w, hbw⟩ / locRes hRB e ⟨b, hbR⟩) := by
      refine ⟨b, hbR, hbw, hb0, ?_⟩
      field_simp
    obtain ⟨hw0, hwinv⟩ := hinv w _ hval (div_ne_zero hne hb0)
    have hy : y = (y * w) * w⁻¹ := by field_simp
    rw [hy]
    exact Subalgebra.mul_mem _ hyw hwinv
  have hI : rB ℂ K' (xv x) I ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y hy
    obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K' d (xv x) hY0.covY I i hi).2 y).1 hy
    refine unit_lemma (w := algebraMap F K' (∏ a ∈ I, xv x a / xv x i) ^ N)
      (w' := algebraMap F K' (∏ a ∈ I, xv x i / xv x a) ^ N) ?_ ?_ ?_ (hRloc hN)
    · exact hRloc (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) {i}
        (Subalgebra.prod_mem _ (fun a _ => div_mem_rA (xv x) (Finset.mem_singleton_self i) a))) N)
    · exact hIB (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) I
        (Subalgebra.prod_mem _ (fun a ha => div_mem_rA (xv x) ha i))) N)
    · rw [← mul_pow, ← map_mul, ← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_one (fun a _ => by
        rw [div_mul_div_comm, mul_comm (xv x a), div_self (mul_ne_zero (x i).ne_zero (x a).ne_zero)])]
      rw [map_one, one_pow]
  have hR2 : ∀ S : Finset (Fin (d + 1)), S ⊆ J →
      R2 (xv x) j2 (insert j S) ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.insert_empty]
      exact hj
    | insert m S hmS ih =>
      intro hS y hy
      rw [Finset.insert_comm] at hy
      obtain ⟨N, hN⟩ := h5 (insert j S) j (Finset.mem_insert_self _ _) m y hy
      have hmJ : m ∈ J := hS (Finset.mem_insert_self _ _)
      refine unit_lemma (w := j2 (algebraMap F K (xv x m / xv x j)) ^ N)
        (w' := j2 (algebraMap F K (xv x j / xv x m)) ^ N) ?_ ?_ ?_
        (ih (fun a ha => hS (Finset.mem_insert_of_mem ha)) hN)
      · exact Subalgebra.pow_mem _ (hj (h4 {j} _ (mem_rB_of (L := K) (xv x) {j}
          (div_mem_rA (xv x) (Finset.mem_singleton_self j) m))).2) N
      · exact Subalgebra.pow_mem _ (hR2B (h4 J _ (mem_rB_of (L := K) (xv x) J
          (div_mem_rA (xv x) hmJ j))).2) N
      · rw [← mul_pow, ← map_mul, ← map_mul, div_mul_div_comm, mul_comm (xv x m),
          div_self (mul_ne_zero (x j).ne_zero (x m).ne_zero), map_one, map_one, one_pow]
  have hB : RY (xv x) j2 I J ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    refine le_trans (hmono I I J (insert j J) (subset_refl _) (Finset.subset_insert _ _)) ?_
    exact sup_le hI (hR2 J (subset_refl _))
  obtain ⟨h1, h2⟩ := loc_val_eq hRB e hB
  exact ⟨locRes hRB e, h1, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocForms
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocFormsAux

private def Hs {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
    (B : Subalgebra ℂ L) (P : Finset ι) (g : ι → V) (w : V) : Prop :=
  ∃ c : ι → L, (∀ S, c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

variable {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
  {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V}

private lemma Hs_zero : Hs B P g 0 := ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩

private lemma Hs_add {w w' : V} (h : Hs B P g w) (h' : Hs B P g w') : Hs B P g (w + w') := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun S => c S + c' S, fun S => B.add_mem (hc S) (hc' S), by
    simp [add_smul, Finset.sum_add_distrib]⟩

private lemma Hs_smul {b : L} (hb : b ∈ B) {w : V} (h : Hs B P g w) : Hs B P g (b • w) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun S => b * c S, fun S => B.mul_mem hb (hc S), by
    simp [Finset.smul_sum, mul_smul]⟩

private lemma Hs_single [DecidableEq ι] {S : ι} (hS : S ∈ P) : Hs B P g (g S) :=
  ⟨fun T => if T = S then 1 else 0, fun T => by dsimp only; split_ifs <;> simp [B.one_mem, B.zero_mem], by
    simp [ite_smul, Finset.sum_ite_eq', hS]⟩

private lemma Hs_sum {α : Type} (s : Finset α) (f : α → V) (h : ∀ a ∈ s, Hs B P g (f a)) :
    Hs B P g (∑ a ∈ s, f a) :=
  _root_.UpperTheory.Reformulated.B.Qh70.Hs_sum s f h

private lemma alt_sorted {V : Type} [AddCommGroup V] [Module L V] {d : ℕ} (t : Fin d → V)
    (S : Finset (Fin d)) (f : Fin S.card → Fin d) (hf : Function.Injective f)
    (hS : ∀ a, f a ∈ S) :
    ∃ n : ℤ, ExteriorAlgebra.ιMulti L S.card (fun a => t (f a)) =
      (n : L) • ExteriorAlgebra.ιMulti L S.card (fun a => t (S.orderEmbOfFin rfl a)) := by
  set σ := Tuple.sort f
  have hs : StrictMono (f ∘ σ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
  have hu : f ∘ σ = S.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun a => hS _) hs
  have hp := (ExteriorAlgebra.ιMulti L S.card (M := V)).map_perm (fun a => t (f a)) σ
  have hv : ((fun a => t (f a)) ∘ σ) = fun a => t (S.orderEmbOfFin rfl a) := by
    funext a
    simpa using congrArg t (congrFun hu a)
  rw [hv] at hp
  refine ⟨((Equiv.Perm.sign σ : ℤˣ) : ℤ), ?_⟩
  rw [hp, Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

private lemma alt_expand {V : Type} [AddCommGroup V] [Module L V] {q d : ℕ} (t : Fin d → V)
    (c : Fin q → Fin d → L) :
    ExteriorAlgebra.ιMulti L q (fun j => ∑ l, c j l • t l) =
      ∑ f : Fin q → Fin d, (∏ j, c j (f j)) • ExteriorAlgebra.ιMulti L q (fun j => t (f j)) := by
  have h := (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_sum
    (fun j l => c j l • t l)
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_smul_univ _ _

end LocFormsAux

theorem UpperTheory.Gal.productCup_of_system.locForms_of :
    LocOne → LocForms := by
  intro hone F L _ _ _ _ _ _ d x hfc hr e q w
  have ht : ∀ j, tt L x j ∈ loc (rB ℂ L (xv x) {0}) e.1 := fun j =>
    ⟨1, by simp, by simpa [tt] using tco_mem ℂ L (xv x) j⟩
  constructor
  · intro hw
    change Hs _ _ _ w
    refine Submodule.span_induction ?_ Hs_zero (fun _ _ _ _ => Hs_add) ?_ hw
    · rintro _ ⟨b, hb, v, hv, rfl⟩
      refine Hs_smul hb ?_
      choose c hcB hcD using fun j => hone F L d x hfc hr e (v j) (hv j)
      simp only [hcD]
      rw [alt_expand]
      refine Hs_sum _ _ fun f _ => Hs_smul (Subalgebra.prod_mem _ fun j _ => hcB j _) ?_
      by_cases hf : Function.Injective f
      · obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.image f := ⟨_, rfl⟩
        have hcard : S.card = q := by
          rw [hS, Finset.card_image_of_injective _ hf]; simp
        subst hcard
        obtain ⟨n, hn⟩ := alt_sorted (L := L) (fun l => D ℂ L (tt L x l)) S f hf
          (fun a => by simp [hS])
        rw [hn]
        exact Hs_smul (intCast_mem _ n) (Hs_single (g := dtS L x) (by simp))
      · have : ¬ Function.Injective (fun j => D ℂ L (tt L x (f j))) := fun h =>
          hf fun a b hab => h (by simp [hab])
        rw [AlternatingMap.map_eq_zero_of_not_injective _ _ this]
        exact Hs_zero
    · intro a w _ h
      rw [← algebraMap_smul L a w]
      exact Hs_smul (Subalgebra.algebraMap_mem _ a) h
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun S hS => ?_
    have hcard := (Finset.mem_powersetCard.1 hS).2
    subst hcard
    exact Submodule.subset_span ⟨c S, hc S, fun a => tt L x (S.orderEmbOfFin rfl a),
      fun j => ht _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocMax
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma red_art {R : Type} [CommRing R] [IsArtinianRing R] [IsReduced R] (y : R) :
    ∃ z, y * (1 - y * z) = 0 := by
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd y (1 : R)
  simp only [smul_eq_mul, mul_one] at hw
  refine ⟨w, IsReduced.eq_zero _ ⟨n + 1, ?_⟩⟩
  have h : y ^ n * (1 - y * w) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hw, sub_self]
  rw [mul_pow, pow_succ, pow_succ]
  calc y ^ n * y * ((1 - y * w) ^ n * (1 - y * w))
      = y * (1 - y * w) ^ n * (y ^ n * (1 - y * w)) := by ac_rfl
    _ = 0 := by rw [h, mul_zero]

private theorem exists_const_sub_mem_span_tco_of_mem_rA {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (f : F) (hf : f ∈ rA ℂ (xv x) {0}) :
    ∃ c : ℂ, ∃ hb : algebraMap F L f ∈ rB ℂ L (xv x) {0},
      (⟨_, hb⟩ : rB ℂ L (xv x) {0}) - algebraMap ℂ _ c ∈ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
  have memB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F L g ∈ rB ℂ L (xv x) {0} := by
    intro g hg
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := (⟨g, hg⟩ : rA ℂ (xv x) {0}))
  unfold rA at hf
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine ⟨1, memB _ (Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, 0, rfl⟩), ?_⟩
      convert Ideal.zero_mem _
      rw [sub_eq_zero]
      apply Subtype.ext
      simp
    · refine ⟨0, tco_mem ℂ L (xv x) k, ?_⟩
      rw [map_zero, sub_zero]
      exact Ideal.subset_span ⟨k, rfl⟩
  | algebraMap c0 =>
    refine ⟨c0, memB _ (Subalgebra.algebraMap_mem _ c0), ?_⟩
    convert Ideal.zero_mem _
    rw [sub_eq_zero]
    apply Subtype.ext
    simp [IsScalarTower.algebraMap_apply ℂ F L]
  | add f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c + c', by rw [map_add (f := _)]; exact Subalgebra.add_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ h h' using 1
    apply Subtype.ext
    simp only [map_add (f := _), Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_algebraMap]
    ring
  | mul f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c * c', by rw [map_mul]; exact Subalgebra.mul_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ (Ideal.mul_mem_right (⟨_, hb'⟩ : rB ℂ L (xv x) {0}) _ h)
      (Ideal.mul_mem_left _ (algebraMap ℂ (rB ℂ L (xv x) {0}) c) h') using 1
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap]
    ring

private lemma fin_quot {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ L (xv x)) :
    Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := by
  classical
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F L d (xv x) hc {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun z => Ideal.Quotient.mk _ (⟨z.1, z.2⟩ : rB ℂ L (xv x) {0})), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) ∈
      Submodule.span (rA ℂ (xv x) {0}) (s : Set (integralClosure (rA ℂ (xv x) {0}) L)) := by
    rw [hs]
    trivial
  change Ideal.Quotient.mk _ (⟨(⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).1,
    (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).2⟩ : rB ℂ L (xv x) {0}) ∈ _
  generalize (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) = z at hy ⊢
  induction hy using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  | zero =>
    convert Submodule.zero_mem _ using 1
    exact map_zero (Ideal.Quotient.mk _)
  | add u w _ _ hu hw =>
    convert Submodule.add_mem _ hu hw using 1
    exact map_add (Ideal.Quotient.mk _) _ _
  | smul r u _ hu =>
    obtain ⟨c, hb, hc'⟩ := exists_const_sub_mem_span_tco_of_mem_rA (L := L) d x r.1 r.2
    set_option synthInstance.maxHeartbeats 200000 in
    have e : (⟨((r • u : integralClosure (rA ℂ (xv x) {0}) L) : L), (r • u).2⟩ : rB ℂ L (xv x) {0}) =
        ⟨_, hb⟩ * ⟨u.1, u.2⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
      exact Or.inl rfl
    rw [e, map_mul, Ideal.Quotient.eq.mpr hc', Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hu

theorem UpperTheory.Gal.productCup_of_system.locMax_of :
    ValBasic → LocMax := by
  intro _ F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨b, hb, hbv, heb, hev⟩ := hv
  rw [mul_zero] at hev
  haveI : Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := fin_quot d x hc
  haveI : IsArtinianRing ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := IsArtinianRing.of_finite ℂ _
  haveI : IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := hred
  obtain ⟨zq, hz⟩ := red_art (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))) ⟨b * v, hbv⟩)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hmem : (⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) ∈
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, map_mul]
    exact hz
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have he1 : e.1 (1 - ⟨b * v, hbv⟩ * z) = 1 := by
    rw [map_sub, map_one, map_mul]
    change 1 - e.1 ⟨b * v, hbv⟩ * e.1 z = 1
    rw [hev, zero_mul, sub_zero]
  have hes : e.1 (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z)) ≠ 0 := by
    rw [map_mul, he1, mul_one]
    exact heb
  have hs0 : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) ≠ 0 := by
    intro h
    apply hes
    rw [show (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) = 0 from Subtype.ext h, map_zero]
  have key : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v =
      ∑ l, (c l : L) * tt L x l := by
    have h1 : (((⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) =
        ∑ l, (c l : L) * tt L x l := by
      rw [← hcsum]
      simp [tt]
    rw [← h1]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    ring
  refine ⟨fun l => (c l : L) * ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹,
    fun l => ⟨⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z), hes, ?_⟩, ?_⟩
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact (c l).2
  · calc v = ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹ *
          (((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [key, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrTop
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem kahlerMap_volumeForm {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
    [IsScalarTower ℂ F K'] {d : ℕ} (x : Fin (d + 1) → F) :
    mapDR ℂ K K' (vol0 ℂ K x) = vol0 ℂ K' x := by
  simp only [vol0, ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext j
  have h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w := fun w => by
    simp [mapDR]
  have h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a)) := fun a => by
    simp [map1, ι1, KaehlerDifferential.map_D]
  simp only [Function.comp, h1, map_smul, h2, map_inv₀]
  rw [← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]

theorem UpperTheory.Gal.productCup_of_system.trTop_of :
    TrTop := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ
  haveI : FiniteDimensional F K := hY.covZ.fin
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'
  have hTr := (GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1
  have second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h) := by
    intro h
    rw [← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]
    rw [Algebra.trace_trace]
  refine ⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨⟨τ', hτ'⟩, hvol⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY
  have key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0 := by
    intro i
    have hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧
        (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then
        omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K')) :=
      hy' (Finset.univ.erase i) (Set.mem_univ _)
    by_cases hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty
    · have hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 := by
        simp
      rw [if_pos ⟨hne, hc⟩] at hm
      have hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, -, v, -, rfl⟩
        refine (⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hvol τ' hτ' _ (hle hm), second]
      have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1
        (one_mem _)
      rw [mul_one] at h1
      exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1
    · rw [if_neg (fun h => hne h.1)] at hm
      rw [(Submodule.mem_bot ℂ).1 hm]
      simp
  change trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_zsmul, key i, smul_zero]
end

