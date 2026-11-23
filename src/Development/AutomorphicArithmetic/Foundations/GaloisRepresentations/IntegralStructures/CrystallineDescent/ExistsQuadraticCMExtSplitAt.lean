module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open GlobalTheory.GalCut GlobalTheory.Cong GlobalTheory.CongL UpperTheory.Gal.UnramifiedFromSplittingCriterion

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.Int.Core.exists_quadratic_CM_ext_split_at : UpperTheory.Gal.Int.Core.Quad2Ex := by
  intro E Y Ω _ _ _ _ _ _ _ _ _ δ hδ T hT
  have hTP := twoPrimes (primeWith decGen)
  have hS := sqrtFix
  have hMk := mkQ
  have hUL := unrLarge
  have hSI := splitIff
  have hIS := inertSplit decGen
  have absNorm_pos {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
      0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have valuation_lt_of_norm_dvd {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : IsPlaceOver A v)
      {c : ℕ} (hc : Ideal.absNorm v.asIdeal ∣ c) : A.valuation (c : Ω) < 1 := by
    obtain ⟨k, rfl⟩ := hc
    refine GlobalTheory.TameCoupledEx.val_g_lt A v hA ?_
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ (Ideal.absNorm_mem v.asIdeal)
  let F := maximalRealSubfield Y
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ Y Ω⟩
  have hRfin := GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F (fixGrp F Ω Y) (isOpen_fixGrp F Ω Y)
  have hQfin := GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω ℚ (fixGrp ℚ Ω Y) (isOpen_fixGrp ℚ Ω Y)
  set R := hRfin.toFinset with hRdef
  set R' := hQfin.toFinset with hR'def
  set TT := hT.toFinset with hTTdef
  obtain ⟨c, hc0, hc2, hc3, hcT, hcR, hcQ⟩ : ∃ c : ℕ, 0 < c ∧ 2 ∣ c ∧ 3 ∣ c ∧
      (∀ t ∈ T, Ideal.absNorm t.asIdeal ∣ c) ∧ (∀ v ∈ R, Ideal.absNorm v.asIdeal ∣ c) ∧
      ∀ v ∈ R', Ideal.absNorm v.asIdeal ∣ c := by
    refine ⟨6 * ((∏ v ∈ R, Ideal.absNorm v.asIdeal) *
        ((∏ t ∈ TT, Ideal.absNorm t.asIdeal) * ∏ t ∈ R', Ideal.absNorm t.asIdeal)),
      ?_, Dvd.dvd.mul_right (by norm_num) _,
      Dvd.dvd.mul_right (by norm_num) _, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
    · exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Finset.prod_pos fun v _ => absNorm_pos v)
        (Nat.mul_pos (Finset.prod_pos fun v _ => absNorm_pos v) (Finset.prod_pos fun v _ => absNorm_pos v)))
    · exact (((Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)).mul_right _).mul_left _).mul_left _
    · exact ((Finset.dvd_prod_of_mem _ ht).mul_right _).mul_left _
    · exact (((Finset.dvd_prod_of_mem _ ht).mul_left _).mul_left _).mul_left _
  obtain ⟨B₀, hB₀⟩ := hUL Y
  obtain ⟨p₁, p₂, h1, h2, hB, hlt, hM, hTw⟩ := hTP E Y Ω δ hδ (8 * c) (max B₀ c) (by omega)
  have hB0 : B₀ < p₁ := lt_of_le_of_lt (le_max_left _ _) hB
  have hBc : c < p₁ := lt_of_le_of_lt (le_max_right _ _) hB
  have hc2le : 2 ≤ c := Nat.le_of_dvd hc0 hc2
  set p : ℕ := p₁ * p₂ with hp
  have hp0 : 0 < p := Nat.mul_pos h1.pos h2.pos
  set a : ℤ := -(p : ℤ) with ha
  obtain ⟨x, hx2'⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℤ) : Ω) two_pos
  have hx2 : x ^ 2 = ((a : ℤ) : Ω) := hx2'
  have hd : ((8 * c : ℕ) : ℤ) ∣ a - 1 := by
    have h : ((8 * c : ℕ) : ℤ) ∣ ((p + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hM
    have h' : a - 1 = -((p + 1 : ℕ) : ℤ) := by rw [ha]; push_cast; ring
    rw [h']
    exact h.neg_right

  obtain ⟨u, hu⟩ := GlobalTheory.ExSplitCM.exists_mem_of_prime (F := Y) h1
  obtain ⟨A₀, hA₀⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  obtain ⟨τ₀, hτ₀, hτ₀x⟩ : ∃ τ ∈ Ine (F := Y) A₀, τ x ≠ x := by
    have : Fact p₁.Prime := ⟨h1⟩
    obtain ⟨Y0, hY0⟩ := IsAlgClosed.exists_pow_nat_eq ((p₁ : ℕ) : Ω) two_pos
    have hnd : ¬ p₁ ∣ 2 := fun h => by have := Nat.le_of_dvd two_pos h; omega
    obtain ⟨τ, hτ, hτY⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj Y Ω A₀ u hA₀ p₁ hu (hB₀ p₁ h1 hB0 u) 2 two_pos hnd Y0 (-1) hY0 (by norm_num)
    have hp10 : ((p₁ : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 h1.ne_zero
    have hY00 : Y0 ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hY0
      exact hp10 hY0.symm
    have hv1 : A₀.valuation ((p₁ : ℕ) : Ω) < 1 := GlobalTheory.TameCoupledEx.val_g_lt A₀ u hA₀ hu
    set z : Ω := x / Y0 with hz
    have hz2 : z ^ 2 = ((-(p₂ : ℤ) : ℤ) : Ω) := by
      rw [hz, div_pow, hx2, ha, hp, hY0]
      push_cast
      field_simp
    have hcop : IsCoprime (p₁ : ℤ) (2 * (-(p₂ : ℤ))) := by
      have ha : IsCoprime (p₁ : ℤ) 2 := by
        have : Nat.Coprime p₁ 2 := (Nat.Prime.coprime_iff_not_dvd h1).2 hnd
        exact_mod_cast Nat.isCoprime_iff_coprime.2 this
      have hb : IsCoprime (p₁ : ℤ) (p₂ : ℤ) := by
        have : Nat.Coprime p₁ p₂ := (Nat.coprime_primes h1 h2).2 hlt.ne
        exact Nat.isCoprime_iff_coprime.2 this
      exact ha.mul_right hb.neg_right
    have hv2 : A₀.valuation ((2 * (-(p₂ : ℤ)) : ℤ) : Ω) = 1 := by
      obtain ⟨s, t, hst⟩ := hcop
      refine le_antisymm ((A₀.valuation_le_one_iff _).2 (intCast_mem A₀ _)) (not_lt.1 fun hlt1 => ?_)
      have h3 : ((s * (p₁ : ℤ) + t * (2 * (-(p₂ : ℤ))) : ℤ) : Ω) = 1 := by rw [hst]; simp
      have hs1 : A₀.valuation ((s : ℤ) : Ω) ≤ 1 := (A₀.valuation_le_one_iff _).2 (intCast_mem A₀ _)
      have ht1 : A₀.valuation ((t : ℤ) : Ω) ≤ 1 := (A₀.valuation_le_one_iff _).2 (intCast_mem A₀ _)
      have h4 : A₀.valuation (((s * (p₁ : ℤ) + t * (2 * (-(p₂ : ℤ))) : ℤ)) : Ω) < 1 := by
        rw [Int.cast_add, Int.cast_mul, Int.cast_mul t]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hs1) (by simpa using hv1)
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' ht1) hlt1
      rw [h3, map_one] at h4
      exact lt_irrefl _ h4
    have hτz : τ z = z := (hS Y Ω A₀ z (-(p₂ : ℤ)) hz2).2 hv2 τ hτ
    have hxz : x = z * Y0 := by rw [hz]; field_simp
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero, ha] at hx2
      exact hp0.ne' (by simpa using hx2.symm)
    refine ⟨τ, hτ, fun hfix => ?_⟩
    have h6 : τ x = -x := by
      rw [hxz, map_mul, hτz, hτY]
      ring
    rw [hfix] at h6
    have h7 : (2 : Ω) * x = 0 := by linear_combination h6
    exact hx0 ((mul_eq_zero.1 h7).resolve_left two_ne_zero)
  obtain ⟨Q, hxQ, -, hfixQ⟩ := hMk Y Ω x a hx2 ⟨τ₀, hτ₀x⟩
  have hu_notT : u ∉ T := by
    intro huT
    have hmem : ((c : ℕ) : 𝓞 Y) ∈ u.asIdeal := by
      obtain ⟨k, hk⟩ := hcT u huT
      rw [hk, Nat.cast_mul]
      exact u.asIdeal.mul_mem_right _ (Ideal.absNorm_mem u.asIdeal)
    have hcop : Nat.Coprime p₁ c := (Nat.Prime.coprime_iff_not_dvd h1).2 fun h => by
      have := Nat.le_of_dvd hc0 h; omega
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have := GlobalTheory.CMFam.dvd_of_mem u h1 hu hmem
      exact absurd this ((Nat.Prime.coprime_iff_not_dvd h1).1 hcop)))
  have fixes_sqrt {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      (A : ValuationSubring Ω) (hv : A.valuation (c : Ω) < 1)
      (g : G K Ω) (hg : g ∈ Dec (F := K) A) : g x = x := by
    obtain ⟨t, ht, htc, htv⟩ :=
      UpperTheory.Reformulated.B.Qi55.val_prime_of_lt A c hc0.ne' hv
    have htd : ((8 * t : ℕ) : ℤ) ∣ a - 1 :=
      (Int.natCast_dvd_natCast.2 (Nat.mul_dvd_mul_left 8 htc)).trans hd
    exact (hS K Ω A x a hx2).1 t ht htv htd g hg
  let restrict_to_real (g : G (maximalRealSubfield ↥Q.K) Ω) : G F Ω :=
    AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun y => by
      have hy : algebraMap Y ↥Q.K (y : Y) ∈ maximalRealSubfield ↥Q.K :=
        (mem_maximalRealSubfield_iff _).2 fun φ =>
          (mem_maximalRealSubfield_iff _).1 y.2 (φ.comp (algebraMap Y ↥Q.K))
      exact g.commutes ⟨_, hy⟩
  have fixes_of_real {Z K : Type} [Field Z] [NumberField Z] [IsCMField Z]
      [Algebra Z Ω] [Field K] [Algebra K Ω] (g : G K Ω)
      (X : Z) (d : ℕ) (hd : 0 < d) (hX : X ^ 2 = -(d : Z))
      (hreal : Fixes (maximalRealSubfield Z) g)
      (hgx : g (algebraMap Z Ω X) = algebraMap Z Ω X) : Fixes Z g := by
    have hd0 : (d : Z) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hX0 : X ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hX
      exact hd0 (neg_eq_zero.1 hX.symm)
    have hnr : X ∉ maximalRealSubfield Z := by
      intro hr
      obtain ⟨φ⟩ : Nonempty (Z →+* ℂ) := inferInstance
      have h1 := (mem_maximalRealSubfield_iff X).1 hr φ
      have h2 : (φ X) ^ 2 = -(d : ℂ) := by rw [← map_pow, hX, map_neg, map_natCast]
      have h3 : (φ X).im = 0 := Complex.conj_eq_iff_im.1 h1
      have h4 := congrArg Complex.re h2
      simp [pow_two, h3] at h4
      have : (0 : ℝ) < d := by exact_mod_cast hd
      nlinarith [mul_self_nonneg (φ X).re]
    set c := IsCMField.complexConj Z with hc
    have hcX : c X = -X := by
      have h1 : (c X) ^ 2 = X ^ 2 := by rw [← map_pow, hX, map_neg, map_natCast]
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
      · exact absurd ((IsCMField.complexConj_eq_self_iff Z X).1 h) hnr
      · exact h
    intro y
    have ha : (y + c y) / 2 ∈ maximalRealSubfield Z := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat]
      ring
    have hb : (y - c y) / (2 * X) ∈ maximalRealSubfield Z := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, ← hc, hcX]
      field_simp
      ring
    have hy : y = (y + c y) / 2 + X * ((y - c y) / (2 * X)) := by
      field_simp
      ring
    have h1 : g (algebraMap Z Ω ((y + c y) / 2)) = algebraMap Z Ω ((y + c y) / 2) := hreal ⟨_, ha⟩
    have h2 : g (algebraMap Z Ω ((y - c y) / (2 * X))) = algebraMap Z Ω ((y - c y) / (2 * X)) := hreal ⟨_, hb⟩
    rw [hy, map_add (f := _), map_mul, map_add (f := _), map_mul, h1, h2, hgx]
  have conj_of_nat_sq {u : ℂ} {q : ℕ} (hq : 0 < q) (h : u ^ 2 = (q : ℂ)) :
      star u = u := by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have him : u.im = 0 := by
      have h3 : u.re * u.im = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h | h
      · rw [h] at h1
        nlinarith [mul_self_nonneg u.im]
      · exact h
    exact Complex.conj_eq_iff_im.2 him
  have hX2 : (⟨x, hxQ⟩ : ↥Q.K) ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa [ha] using hx2)
  have haux (w : HeightOneSpectrum (𝓞 ↥Q.K)) (hw : ¬ IsSplitAt w)
      (A : ValuationSubring Ω) (hA : IsPlaceOver A w) :
      ¬ A.valuation (c : Ω) < 1 ∧ A.valuation ((2 * a : ℤ) : Ω) = 1 ∧
        ∃ g ∈ Dec (F := F) A, ¬ Fixes Y g := by
    have hnot : ¬ ∀ g ∈ Dec (F := maximalRealSubfield ↥Q.K) A, Fixes ↥Q.K g :=
      fun h => hw ((hSI ↥Q.K Ω A w hA).2 h)
    push Not at hnot
    obtain ⟨g, hg, hng⟩ := hnot
    have hZr : Fixes (maximalRealSubfield ↥Q.K) g := fun y => g.commutes y
    have hgY : ¬ Fixes Y g := fun h => hng (realSpan Y ↥Q.K Ω (maximalRealSubfield ↥Q.K) g h hZr)
    have hgx : g x ≠ x := fun h => hng (fixes_of_real g ⟨x, hxQ⟩ p hp0 hX2 hZr h)
    have hvc : ¬ A.valuation (c : Ω) < 1 := fun h => hgx (fixes_sqrt A h g hg)
    have hδZ : algebraMap Y ↥Q.K δ ∈ maximalRealSubfield ↥Q.K := by
      obtain ⟨q, hq, hδsq⟩ := hδ.1
      refine (mem_maximalRealSubfield_iff _).2 fun φ => conj_of_nat_sq hq ?_
      rw [← map_pow, ← map_pow, hδsq, map_natCast, map_natCast]
    have hgδ : g (algebraMap Y Ω δ) = algebraMap Y Ω δ := by
      have h := hZr ⟨_, hδZ⟩
      exact h
    have hvp : ¬ A.valuation ((p : ℕ) : Ω) < 1 := fun h =>
      hgY (fun y => hTw A h g.toRingEquiv (fun z => apply_mem_iff_of_mem_Dec hg z) hgδ y)
    have hvp1 : A.valuation ((p : ℕ) : Ω) = 1 := le_antisymm (valuation_natCast_le_one A p) (not_lt.1 hvp)
    have hv2 : A.valuation ((2 : ℕ) : Ω) = 1 := by
      refine le_antisymm (valuation_natCast_le_one A 2) (not_lt.1 fun h => hvc ?_)
      obtain ⟨k, rfl⟩ := hc2
      rw [Nat.cast_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (valuation_natCast_le_one A k)) h
    refine ⟨hvc, ?_, restrict_to_real g, (GlobalTheory.AboveL.mem_dec_congr A (restrict_to_real g) g (fun _ => rfl)).2 hg, fun h => hgY h⟩
    have : ((2 * (-(p : ℤ)) : ℤ) : Ω) = -(((2 : ℕ) : Ω) * ((p : ℕ) : Ω)) := by push_cast; ring
    rw [ha, this, Valuation.map_neg, map_mul, hv2, hvp1, one_mul]
  have hunderY : ∀ (w : HeightOneSpectrum (𝓞 ↥Q.K)) (A : ValuationSubring Ω), IsPlaceOver A w →
      IsPlaceOver A (w.under (𝓞 Y)) := fun w A hA x => by
    rw [IsScalarTower.algebraMap_apply Y ↥Q.K Ω]
    exact hA (algebraMap (𝓞 Y) (𝓞 ↥Q.K) x)
  have hunderF : ∀ (w : HeightOneSpectrum (𝓞 Y)) (A : ValuationSubring Ω), IsPlaceOver A w →
      IsPlaceOver A (w.under (𝓞 F)) := fun w A hA x => by
    rw [IsScalarTower.algebraMap_apply F Y Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 Y) x)

  have hIneY : ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v →
      ¬ A.valuation (c : Ω) < 1 → ∀ τ ∈ Ine (F := F) A, Fixes Y τ := by
    intro v A hA hvc τ hτ
    by_contra hnf
    have hvR : v ∈ R := hRfin.mem_toFinset.2 ⟨A, hA, fun hle => hnf (hle hτ)⟩
    exact hvc (valuation_lt_of_norm_dvd A v hA (hcR v hvR))
  have hall : ∀ (w : HeightOneSpectrum (𝓞 ↥Q.K)), ¬ IsSplitAt w → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ¬ A.valuation (c : Ω) < 1 ∧ (∀ τ ∈ Ine (F := F) A, Fixes Y τ ∧ τ x = x) ∧
        ∃ g ∈ Dec (F := F) A, ¬ Fixes Y g := by
    intro w hw A hA
    obtain ⟨hvc, hv2, hg⟩ := haux w hw A hA
    exact ⟨hvc, fun τ hτ => ⟨hIneY _ A (hunderF _ A (hunderY w A hA)) hvc τ hτ, (hS F Ω A x a hx2).2 hv2 τ hτ⟩, hg⟩
  have hS1 : Step1 T Q := by
   refine ⟨⟨⟨x, hxQ⟩, p, hp0, hX2⟩, GlobalTheory.CMFam.even_finrank Y Ω Q, ?_, ?_, u, hu_notT, A₀, hA₀, τ₀, hτ₀,
     fun h => hτ₀x (h ⟨x, hxQ⟩)⟩
   · intro t ht A hA g hg
     exact hfixQ Y g (fun y => g.commutes y)
       (fixes_sqrt A (valuation_lt_of_norm_dvd A t hA (hcT t ht)) g hg)
   · intro w hw
     obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
     refine ⟨fun hT' => (hall w hw A hA).1 (valuation_lt_of_norm_dvd A _ (hunderY w A hA) (hcT _ hT')), ?_, ?_⟩
     · have hfix : ∀ σ ∈ Ine (F := maximalRealSubfield ↥Q.K) A, ∀ z : ↥Q.K,
           σ (algebraMap ↥Q.K Ω z) = algebraMap ↥Q.K Ω z := by
         intro σ hσ
         have hσ' : restrict_to_real σ ∈ Ine (F := F) A :=
           mem_Ine.2 ⟨(GlobalTheory.AboveL.mem_dec_congr A (restrict_to_real σ) σ (fun _ => rfl)).2 (Ine_le_Dec A hσ), (mem_Ine.1 hσ).2⟩
         obtain ⟨h3, h4⟩ := (hall w hw A hA).2.1 _ hσ'
         exact hfixQ _ σ h3 h4
       haveI : IsAlgClosure (maximalRealSubfield ↥Q.K) Ω :=
         ⟨IsAlgClosure.isAlgClosed ↥Q.K, Algebra.IsAlgebraic.trans _ ↥Q.K Ω⟩
       have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield ↥Q.K))) := fun x => by
         rw [IsScalarTower.algebraMap_apply (maximalRealSubfield ↥Q.K) ↥Q.K Ω]
         exact hA (algebraMap (𝓞 (maximalRealSubfield ↥Q.K)) (𝓞 ↥Q.K) x)
       obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A
         (w.under (𝓞 (maximalRealSubfield ↥Q.K))) w hAv hA hfix
       exact Ideal.ramificationIdx_eq_one_iff.1 he
     · intro A' hA' h hh
       obtain ⟨-, hI, hg⟩ := hall w hw A' hA'
       exact hfixQ Y h (fun y => h.commutes y)
         (hIS Y Ω A' (w.under (𝓞 Y)) (hunderY w A' hA') x a hx2 hI hg h hh)
  refine ⟨Q, hS1, fun w hw => ?_, p, ⟨hp0, _, hX2⟩, fun w hw => ⟨by_contra fun h => (hS1.2.2.2.1 w h).1 hw, fun q hq hqw => ?_⟩⟩
  · obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    obtain ⟨hvc, hv2, -⟩ := haux w hw A hA
    have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield ↥Q.K))) := fun x => by
      rw [IsScalarTower.algebraMap_apply (maximalRealSubfield ↥Q.K) ↥Q.K Ω]
      exact hA (algebraMap (𝓞 (maximalRealSubfield ↥Q.K)) (𝓞 ↥Q.K) x)
    generalize w.under (𝓞 (maximalRealSubfield ↥Q.K)) = v at hAv ⊢
    have hn : ∀ k : ℕ, k ∣ c → ((k : ℕ) : 𝓞 (maximalRealSubfield ↥Q.K)) ∉ v.asIdeal := by
      rintro k ⟨j, rfl⟩ hk
      refine hvc (GlobalTheory.TameCoupledEx.val_g_lt A v hAv ?_)
      rw [Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hk
    refine ⟨by exact_mod_cast hn 2 hc2, ?_, ?_⟩
    · have h1 := Ideal.absNorm_mem v.asIdeal
      have h2 : Ideal.absNorm v.asIdeal ≠ 0 := (absNorm_pos v).ne'
      have h3 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h4 : Ideal.absNorm v.asIdeal ≠ 2 := fun h => hn 2 hc2 (h ▸ h1)
      have h5 : Ideal.absNorm v.asIdeal ≠ 3 := fun h => hn 3 hc3 (h ▸ h1)
      omega
    · have hA0 : IsPlaceOver A (v.under (𝓞 ℚ)) := fun x => by
        rw [IsScalarTower.algebraMap_apply ℚ (maximalRealSubfield ↥Q.K) Ω]
        exact hAv (algebraMap (𝓞 ℚ) (𝓞 (maximalRealSubfield ↥Q.K)) x)
      obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (v.under (𝓞 ℚ)) v hA0 hAv fun τ hτ z => by
        refine hfixQ ℚ τ ?_ ((hS ℚ Ω A x a hx2).2 hv2 τ hτ) (z : ↥Q.K)
        by_contra hnf
        exact hvc (valuation_lt_of_norm_dvd A _ hA0 (hcQ _ (hQfin.mem_toFinset.2 ⟨A, hA0, fun hle => hnf (hle hτ)⟩)))
      have hu1 : Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal := Ideal.ramificationIdx_eq_one_iff.1 he
      have hu2 : Algebra.FormallyUnramified ℤ (𝓞 ℚ) := Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
        fun y => ⟨Rat.ringOfIntegersEquiv y, by simpa using (eq_intCast Rat.ringOfIntegersEquiv.symm _).symm.trans (Rat.ringOfIntegersEquiv.symm_apply_apply y)⟩
      have hu3 : Algebra.IsUnramifiedAt ℤ v.asIdeal := Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) _
      rw [← Ideal.dvd_iff_le]
      exact not_dvd_differentIdeal_iff.2 hu3
  · haveI : Fact q.Prime := ⟨hq⟩
    have h1 : q ∣ c := by
      refine (GlobalTheory.CMFam.dvd_of_mem (w.under (𝓞 Y)) hq ?_ (Ideal.absNorm_mem (w.under (𝓞 Y)).asIdeal)).trans (hcT _ hw)
      show algebraMap (𝓞 Y) (𝓞 ↥Q.K) _ ∈ w.asIdeal
      rwa [map_natCast]
    refine GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_
    exact_mod_cast (Nat.mul_dvd_mul_left 8 h1).trans hM
