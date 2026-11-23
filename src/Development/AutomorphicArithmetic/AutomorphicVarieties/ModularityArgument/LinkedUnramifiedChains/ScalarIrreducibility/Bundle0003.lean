module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CompDim
section
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem dim_arith {h : ℕ∞} {D E : WithBot ℕ∞} {N N' a : ℕ}
    (h1 : (h : WithBot ℕ∞) + D = ((N + 1 : ℕ) : WithBot ℕ∞)) (h2 : h ≤ (N' : ℕ∞)) (h3 : N = N' + (a + 1))
    (h4 : D ≤ E + ((1 : ℕ) : WithBot ℕ∞)) : ((1 + a : ℕ) : WithBot ℕ∞) ≤ E := by
  induction E using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, le_bot_iff] at h4
    rw [h4, WithBot.add_bot] at h1
    exact absurd h1.symm (WithBot.natCast_ne_bot _)
  | coe E =>
    induction D using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot] at h1
      exact absurd h1.symm (WithBot.natCast_ne_bot _)
    | coe D =>
      have h1' : h + D = ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h4' : D ≤ E + ((1 : ℕ) : ℕ∞) := by exact_mod_cast h4
      have : ((1 + a : ℕ) : ℕ∞) ≤ E := by
        induction E using ENat.recTopCoe with
        | top => exact le_top
        | coe e =>
          induction D using ENat.recTopCoe with
          | top => simp at h4'
          | coe d =>
            induction h using ENat.recTopCoe with
            | top => simp at h2
            | coe k =>
              have a1 : k + d = N + 1 := by exact_mod_cast h1'
              have a2 : k ≤ N' := by exact_mod_cast h2
              have a4 : d ≤ e + 1 := by exact_mod_cast h4'
              have : 1 + a ≤ e := by omega
              exact_mod_cast this
      exact_mod_cast this

private theorem min_below {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (hf : f.Flat) (Q : Ideal R)
    (hQ : Q.IsPrime) (P : Ideal A) (hP : P ∈ minimalPrimes A) (h : P ≤ Q.comap f) :
    ∃ P' ∈ minimalPrimes R, P'.comap f = P := by
  letI := f.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : P.IsPrime := hP.1.1
  haveI : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  haveI : Q.LiesOver (Q.comap f) := ⟨rfl⟩
  obtain ⟨Q', -, hQ', hl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := Q.comap f) Q h
  obtain ⟨P', hP', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Q') bot_le
  refine ⟨P', hP', ?_⟩
  have e : Q'.comap f = P := hl.over.symm
  have h1 : P'.comap f ≤ P := e ▸ Ideal.comap_mono hle
  haveI : P'.IsPrime := hP'.1.1
  exact le_antisymm h1 (hP.2 ⟨Ideal.IsPrime.comap f, bot_le⟩ h1)

theorem UpperTheory.V.J.compDim :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → ∀ P ∈ minimalPrimes S.A, P ≤ q →
          ((1 + n * F.d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.B ⧸ S.π P) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO hTI P hP hPq
  obtain ⟨hQ, hQq, -, -⟩ := hO
  have hflat := (Fr.loc_flat hF hn S x L).1
  obtain ⟨P', hP', hc⟩ := min_below (L.ι : S.A →+* L.R) hflat Q hQ P hP (by
    have : Q.comap (L.ι : S.A →+* L.R) = q := hQq
    rw [this]; exact hPq)
  have hPp : P'.IsPrime := hP'.1.1
  have him : L.im P' = P := hc
  have hoff : S.u.OffTri P :=
    ⟨fun h => hTI.1.1 (h.trans hPq), fun h => hTI.1.2 (h.trans hPq)⟩
  have htd : S.td (L.im P') ≤ ((1 : ℕ) : Cardinal) := by
    rw [him, Nat.cast_one]
    exact Fr.fibre hF hn S P hP.1.1 hoff
  have hdim := (Fr.loc_dim hF hn S x L).1 P' hPp 1 htd
  have hπ : L.π P' = S.π P := by
    show S.π (L.im P') = _
    rw [him]
  rw [hπ] at hdim
  obtain ⟨N, N', p, f, hN, hs, hk⟩ := Fr.pres hF hn S x L
  obtain ⟨e1, e2⟩ := htPres L.O' N N' L.R (p : MvPowerSeries (Fin N) L.O' →+* L.R) f hs hk P' hPp
  have h0 : P'.height = 0 := Ideal.height_eq_zero_iff.mpr hP'
  rw [h0, zero_add] at e2
  exact dim_arith e1 e2 (by rw [hN]) hdim
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerCont
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Abs

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R]

private theorem sup_pow_le (t : R) (B : Ideal R) (k : ℕ) :
    (Ideal.span {t} ⊔ B) ^ k ≤ Ideal.span {t ^ k} ⊔ B := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton, ← pow_succ]
    have h1 : Ideal.span {t ^ k} * B ≤ B := Ideal.mul_le_right
    have h2 : B * (Ideal.span {t} ⊔ B) ≤ B := Ideal.mul_le_left
    exact sup_le (sup_le le_sup_left (le_trans h1 le_sup_right)) (le_trans h2 le_sup_right)

private theorem exists_pow_le [IsLocalRing O] [Finite (ResidueField O)] [IsLocalRing R] (I : Ideal R)
    (hI : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I) (s : Finset R)
    (hs : ∀ a : R, ∃ b ∈ Submodule.span O (s : Set R), a - b ∈ I) :
    ∃ j, maximalIdeal R ^ j ≤ I := by
  classical
  have hfin : Finite (R ⧸ I) := by
    let σ : ResidueField O → O := Function.surjInv (residue_surjective (R := O))
    have hσ : ∀ x, residue O (σ x) = x := Function.surjInv_eq _
    let φ : (s → ResidueField O) → R ⧸ I :=
      fun x => Ideal.Quotient.mk I (∑ e : s, algebraMap O R (σ (x e)) * (e : R))
    refine Finite.of_surjective φ fun z => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb, hab⟩ := hs a
    obtain ⟨f, rfl⟩ := Submodule.mem_span_finset'.1 hb
    refine ⟨fun e => residue O (f e), ?_⟩
    have h1 : (∑ e : s, algebraMap O R (σ (residue O (f e))) * (e : R)) - ∑ e : s, f e • (e : R) ∈ I := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun e _ => ?_
      rw [Algebra.smul_def, ← sub_mul, ← map_sub]
      refine Ideal.mul_mem_right _ _ (hI _ ?_)
      rw [← residue_eq_zero_iff, map_sub, hσ, sub_self]
    have h2 := I.sub_mem h1 hab
    rw [sub_sub_sub_cancel_right] at h2
    exact Ideal.Quotient.eq.2 h2
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨j, hj⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  refine ⟨j, ?_⟩
  have hm : (maximalIdeal R).map (Ideal.Quotient.mk I) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hu : IsUnit (a * b + 1) := by
      by_contra h
      have h2 := Ideal.sub_mem _ ((mem_maximalIdeal _).2 h) (Ideal.mul_mem_right b _ ha)
      rw [add_sub_cancel_left] at h2
      exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal R).ne_top h2
    simpa using hu.map (Ideal.Quotient.mk I)
  have h3 := Ideal.pow_right_mono hm j
  rw [hj, ← Ideal.map_pow] at h3
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.1 (h3 (Ideal.mem_map_of_mem _ ha))

private theorem exists_span_mod_sq [IsNoetherianRing R] [CommRing K] [Algebra O K] (y : R →ₐ[O] K)
    (h : Module.Finite O y.range) :
    ∃ s : Finset R, ∀ a : R, ∃ b ∈ Submodule.span O (s : Set R), a - b ∈ RingHom.ker y ^ 2 :=
  _root_.UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq y h

private theorem derCont_abs [IsLocalRing O] [Finite (ResidueField O)] [IsLocalRing R] [IsNoetherianRing R]
    [NormedField K] [Algebra O K] (y : R →ₐ[O] K) (hfin : Module.Finite O y.range) (hle : ∀ a, ‖y a‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal R, ‖y a‖ < 1) (p : O) (hp : maximalIdeal O = Ideal.span {p})
    (hpR : algebraMap O R p ∈ maximalIdeal R) (D : R →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = y f * D g + y g * D f) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, ‖D a‖ ≤ ε ∧ ‖y a‖ ≤ ε := by
  classical
  have hDq : ∀ x ∈ RingHom.ker y ^ 2, D x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun f hf g hg => ?_)
      (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    have hf' : y f = 0 := RingHom.mem_ker.1 hf
    have hg' : y g = 0 := RingHom.mem_ker.1 hg
    rw [hD, hf', hg']
    simp
  have hyq : ∀ x ∈ RingHom.ker y ^ 2, y x = 0 := fun x hx =>
    RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero hx)
  obtain ⟨s, hs⟩ := exists_span_mod_sq y hfin
  have hO : ∀ o : O, ‖algebraMap O K o‖ ≤ 1 := fun o => by simpa using hle (algebraMap O R o)
  have hC : 0 ≤ ∑ e ∈ s, ‖D e‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbd : ∀ b, ‖D b‖ ≤ ∑ e ∈ s, ‖D e‖ := by
    intro b
    obtain ⟨b₀, hb₀, hc⟩ := hs b
    have e0 : D b = D b₀ := by
      have := hDq _ hc
      rwa [map_sub, sub_eq_zero] at this
    rw [e0]
    obtain ⟨f, rfl⟩ := Submodule.mem_span_finset'.1 hb₀
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_coe_sort s]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [map_smul, Algebra.smul_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hO _)
  obtain ⟨j, hj⟩ := exists_pow_le (Ideal.span {algebraMap O R p} ⊔ RingHom.ker y ^ 2)
    (fun a ha => by
      rw [hp] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)))
    s (fun a => by
      obtain ⟨b, hb, hab⟩ := hs a
      exact ⟨b, hb, Ideal.mem_sup_right hab⟩)
  have hρ : ‖y (algebraMap O R p)‖ < 1 := hlt _ hpR
  have hyp : y (algebraMap O R p) = algebraMap O K p := y.commutes p
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (div_pos hε (by positivity : 0 < ∑ e ∈ s, ‖D e‖ + 1)) hρ
  rw [lt_div_iff₀ (by positivity)] at hn
  have hρ0 : 0 ≤ ‖y (algebraMap O R p)‖ ^ n := by positivity
  refine ⟨j * n, fun a ha => ?_⟩
  have ha' : a ∈ Ideal.span {algebraMap O R p ^ n} ⊔ RingHom.ker y ^ 2 :=
    sup_pow_le _ _ n (Ideal.pow_right_mono hj n (by rwa [← pow_mul]))
  obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have e1 : b * algebraMap O R p ^ n = p ^ n • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  constructor
  · rw [map_add (f := _), hDq c hc, add_zero, e1, map_smul, Algebra.smul_def, norm_mul, map_pow, norm_pow, ← hyp]
    have := mul_le_mul_of_nonneg_left (hbd b) hρ0
    nlinarith
  · rw [map_add (f := _), hyq c hc, add_zero, map_mul, norm_mul, map_pow, norm_pow]
    have := mul_le_mul (hle b) (le_refl (‖y (algebraMap O R p)‖ ^ n)) hρ0 zero_le_one
    nlinarith

end Abs

theorem UpperTheory.V.J.derCont :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (y : R →ₐ[c.O] Qbar l),
        ∀ D ∈ PtDer y (Qbar l), ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal R ^ k, ‖D a‖ ≤ ε ∧ ‖y a‖ ≤ ε := by
  intro l _ c _ R _ _ _ y D hD ε hε
  obtain ⟨hfin, hle, hlt⟩ := coPt l c R y
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hpR : algebraMap c.O R p ∈ maximalIdeal R := fun h => hp.not_isUnit (isUnit_of_map_unit _ _ h)
  exact derCont_abs y hfin hle hlt p hp.maximalIdeal_eq hpR D (fun f g => hD f g) hε
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtOfSum
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem ht_of_sum {h : ℕ∞} {N : ℕ} {D : WithBot ℕ∞} (hD : D = 1)
    (e : (h : WithBot ℕ∞) + D = (N + 1 : ℕ)) : h = N := by
  subst hD
  have e2 : ((h + 1 : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast]
    exact e
  have e3 : h + 1 = ((N + 1 : ℕ) : ℕ∞) := WithBot.coe_injective e2
  induction h using ENat.recTopCoe with
  | top =>
    rw [top_add] at e3
    exact absurd e3.symm (ENat.coe_ne_top _)
  | coe k =>
    norm_cast at e3 ⊢
    omega

private theorem le_of_add {a : ℕ∞} {b c : ℕ} (h : ((c + b : ℕ) : ℕ∞) ≤ a + b) : (c : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    norm_cast at h ⊢
    omega

theorem UpperTheory.V.J.htLow :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q →
          ((n * F.d + 1 : ℕ) : ℕ∞) ≤ q.height ∧ (Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) → ∀ P ∈ associatedPrimes S.A S.A, P ≤ q → P ∈ minimalPrimes S.A) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO
  obtain ⟨hQ, him, hmin, hdim⟩ := hO
  obtain ⟨N, N', p, f, hN, hp, hker⟩ := Fr.pres hF hn S x L
  obtain ⟨hfl, -, -⟩ := Fr.loc_flat hF hn S x L
  have hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  have hR : IsNoetherianRing L.R := inferInstance
  obtain ⟨h1, h2⟩ := htPres L.O' N N' L.R p f hp hker Q hQ
  have hc : (Ideal.comap p Q).height = N := ht_of_sum hdim h1
  have hfh : Q.height = q.height := flatHt S.A L.R L.ι hfl q Q hQ him hmin
  have hlow : ((n * F.d + 1 : ℕ) : ℕ∞) ≤ Q.height := by
    apply le_of_add (b := N')
    rw [Nat.add_comm, ← hN, ← hc]
    exact h2
  refine ⟨hfh ▸ hlow, fun hle P hP hPq => ?_⟩
  have hu : Q.height + N' ≤ (Ideal.comap p Q).height := by
    rw [hc, hN, Nat.cast_add, add_comm (N' : ℕ∞)]
    exact add_le_add hle le_rfl
  refine flatAss S.A L.R L.ι hfl Q hQ (unmix L.O' N N' L.R p f hp hker Q hQ hu) P hP ?_
  change P ≤ L.im Q
  rw [him]
  exact hPq
end

