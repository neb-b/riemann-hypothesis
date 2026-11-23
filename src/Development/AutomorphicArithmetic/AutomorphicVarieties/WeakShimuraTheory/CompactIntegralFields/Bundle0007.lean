module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ValLtIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CmplEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.HomOfDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FibLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChCore
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)

private theorem UpperTheory.V.Ws.ch_core {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hS : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hg : Φ.Good ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes} := (List.finite_toSet redTypes).to_subtype
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (red Φ l a hS d C hB c hc hg R _ hdef S.1 S.2).trans_lt (by exact_mod_cast hN1))
    (fun t q hq hle hr => ch_num
      (fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
        ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx))
        fun S hS => hr ⟨S, hS⟩))
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2) _ hPQ.2.2
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) fun S hS => hA ⟨S, hS⟩)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]

theorem UpperTheory.V.Ws.ch :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PM ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C → 30 * (C + 1) * (C + 1) ≤ T.d →
      ∀ x : X.A →ₐ[c'.O] ResidueField c'.O, (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) → (T.fr ∅).Good ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x) := by
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg ⟨q₀, hq₀, hq₀x, hq₀J⟩ q hq hqx
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, _, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact ch_core hS X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => nn hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hg f hdef hPQ ih
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiagConst
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.DiagonalConstancy

private theorem exists_form (R : Fin 4 → Fin 4 → Prop) (hr : ∀ i, R i i) (ht : ∀ i j k, R i j → R j k → R i k)
    (hv : ∀ i j, R i j → R j.rev i.rev) (hd : ∀ i j, i ≠ j → R i j → ¬ R j i) :
    ∃ φ : ℤ × ℤ →+ ℤ, ∀ i j, i ≠ j → R i j → 0 < φ (wt i j) := by
  classical
  let a : Fin 4 → ℕ := fun i => (Finset.univ.filter fun k => R i k).card
  have ha : ∀ i j, i ≠ j → R i j → a j < a i := fun i j hij h => by
    refine Finset.card_lt_card ⟨fun k hk => ?_, fun hs => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ht _ _ _ h hk
    · have := hs (Finset.mem_filter.2 ⟨Finset.mem_univ i, hr i⟩)
      exact hd i j hij h (Finset.mem_filter.1 this).2
  let h : Fin 4 → ℤ := fun i => (a i : ℤ) - a i.rev
  refine ⟨(h 0 - h 1) • AddMonoidHom.fst ℤ ℤ + (h 0 - h 2) • AddMonoidHom.snd ℤ ℤ, fun i j hij hR => ?_⟩
  have h1 := ha i j hij hR
  have h2 := ha _ _ (fun e => hij (Fin.rev_injective e).symm) (hv i j hR)
  have key : ((h 0 - h 1) • AddMonoidHom.fst ℤ ℤ + (h 0 - h 2) • AddMonoidHom.snd ℤ ℤ) (wt i j) = h i - h j := by
    have r0 : (0 : Fin 4).rev = 3 := rfl
    have r1 : (1 : Fin 4).rev = 2 := rfl
    have r2 : (2 : Fin 4).rev = 1 := rfl
    have r3 : (3 : Fin 4).rev = 0 := rfl
    fin_cases i <;> fin_cases j <;> simp [h, wt, lamW, muW, r0, r1, r2, r3] <;> ring
  rw [key]
  simp only [h]
  omega

private theorem mono_fin {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (φ : ℤ × ℤ →+ ℤ)
    (hφ : ∀ i j, i ≠ j → Ge r i j → 0 < φ (wt i j)) (hf : ∀ g i, IsOfFinOrder (r g i i)) :
    ∀ x ∈ mono r 0, x = 0 ∨ IsOfFinOrder x := by
  rintro x ⟨L, hL, rfl⟩
  have key : ∀ L : List (H × Fin 4 × Fin 4), (L.map fun a => r a.1 a.2.1 a.2.2).prod = 0 ∨
      (0 ≤ φ (L.map fun a => wt a.2.1 a.2.2).sum ∧
        (φ (L.map fun a => wt a.2.1 a.2.2).sum = 0 → IsOfFinOrder (L.map fun a => r a.1 a.2.1 a.2.2).prod)) := by
    intro L
    induction L with
    | nil => right; simp
    | cons a L ih =>
      obtain ⟨g, i, j⟩ := a
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add (f := _)]
      rcases ih with h | ⟨h1, h2⟩
      · left; rw [h, mul_zero]
      by_cases h0 : r g i j = 0
      · left; rw [h0, zero_mul]
      right
      by_cases hij : i = j
      · subst hij
        rw [(wt_eq_zero i i).2 rfl, map_zero, zero_add]
        exact ⟨h1, fun h => (hf g i).mul (h2 h)⟩
      · have := hφ i j hij ⟨g, h0⟩
        exact ⟨by omega, fun h => by omega⟩
  rcases key L with h | h
  · exact Or.inl h
  · exact Or.inr (h.2 (by rw [hL, map_zero]))

private theorem frob_fix {K : Type} [CommRing K] [IsDomain K] (l : ℕ) [hl : Fact l.Prime] [CharP K l] (x : K)
    (hx : x = 0 ∨ IsOfFinOrder x) : ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x := by
  rcases hx with rfl | hx
  · exact ⟨1, one_pos, by simp [hl.out.ne_zero]⟩
  obtain ⟨N, hN, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hx
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.out.ne_one
  have h1 : x ^ m = 1 := by
    have h2 : (x ^ m - 1) ^ l ^ a = 0 := by rw [sub_pow_char_pow, ← pow_mul, mul_comm, h, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero a hl.out.ne_zero) |>.1 h2)
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  refine ⟨m.totient, Nat.totient_pos.2 hm0, ?_⟩
  have h3 : l ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)
  rw [pow_eq_pow_mod _ h1, h3, ← pow_eq_pow_mod _ h1, pow_one]

private theorem unip {R : Type} [CommRing R] (l : ℕ) [hl : Fact l.Prime] [CharP R l] (u X : M4 R) (hu : IsGSp 1 u)
    (h1 : IsUp (adj u * X * u)) (h2 : ∀ i, (adj u * X * u) i i = 1) : X ^ l ^ 2 = 1 := by
  have hu1 : adj u * u = 1 := by simpa [IsGSp] using hu
  have hu2 : u * adj u = 1 := mul_eq_one_comm.1 hu1
  set M := adj u * X * u with hM
  have hX : X - 1 = u * (M - 1) * adj u := by
    rw [hM, mul_sub, sub_mul, mul_one, hu2, ← mul_assoc, ← mul_assoc, hu2, one_mul, mul_assoc, hu2, mul_one]
  have hN : ∀ i j, j ≤ i → (M - 1) i j = 0 := fun i j h => by
    rcases h.lt_or_eq with h | rfl
    · rw [Matrix.sub_apply, h1 i j h, Matrix.one_apply_ne h.ne', sub_zero]
    · rw [Matrix.sub_apply, h2, Matrix.one_apply_eq, sub_self]
  generalize M - 1 = N at hX hN
  have h4 : N ^ 4 = 0 := by
    have e : N ^ 4 = N * N * N * N := by noncomm_ring
    rw [e]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_four, hN 0 0, hN 1 0, hN 1 1, hN 2 0, hN 2 1, hN 2 2, hN 3 0, hN 3 1, hN 3 2, hN 3 3]
    fin_cases i <;> fin_cases j <;>
      simp [hN 0 0, hN 1 0, hN 1 1, hN 2 0, hN 2 1, hN 2 2, hN 3 0, hN 3 1, hN 3 2, hN 3 3]
  have h5 : (X - 1) ^ 4 = 0 := by
    have e : (u * N * adj u) ^ 4 = u * (N * (adj u * u) * N * (adj u * u) * N * (adj u * u) * N) * adj u := by noncomm_ring
    have e' : N ^ 4 = N * N * N * N := by noncomm_ring
    rw [hX, e, hu1, mul_one, mul_one, mul_one, ← e', h4, mul_zero, zero_mul]
  have h6 : (X - 1) ^ l ^ 2 = 0 := pow_eq_zero_of_le (by nlinarith [hl.out.two_le]) h5
  rw [sub_pow_char_pow_of_commute l 2 (Commute.one_right X), one_pow] at h6
  exact sub_eq_zero.1 h6

private def dchar {H K : Type} [Group H] [CommRing K] [IsDomain K] (r : H →* M4 K) (h : DiagType r) (i : Fin 4) : H →* K where
  toFun g := r g i i
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      by_contra h0
      exact h i k hk.symm ⟨a, left_ne_zero_of_mul h0⟩ ⟨b, right_ne_zero_of_mul h0⟩
    · simp

private theorem mink {Ω A : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (κ : G ℚ Ω →* A) (hc : AdicCont (maximalIdeal A) κ) (N : ℕ)
    (h : ∀ B : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) B, κ g ^ N = 1) (g : G ℚ Ω) : κ g ^ N = 1 := by
  have hk : ∀ k : ℕ, κ g ^ N - 1 ∈ maximalIdeal A ^ k := by
    intro k
    let f : G ℚ Ω →* A ⧸ maximalIdeal A ^ k :=
      (powMonoidHom N).comp ((Ideal.Quotient.mk (maximalIdeal A ^ k)).toMonoidHom.comp κ)
    have hf : ∀ x, f x = Ideal.Quotient.mk (maximalIdeal A ^ k) (κ x ^ N) := fun x => by
      rw [map_pow]; rfl
    have ho : IsOpen (f.ker : Set (G ℚ Ω)) := ((hc k).comp (· ^ N)).isOpen_fiber 1
    have ht := UpperTheory.V.CF.minkAbs Ω f.ker ho fun B x hx => by
      rw [MonoidHom.mem_ker, hf, h B x hx, map_one]
    have hg : g ∈ f.ker := ht ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker, hf] at hg
    exact Ideal.Quotient.eq.1 hg
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have : κ g ^ N - 1 ∈ (⊥ : Ideal A) := hb ▸ Ideal.mem_iInf.2 hk
  exact sub_eq_zero.1 this

private theorem a_kill {l : ℕ} [hl : Fact l.Prime] (c : Coef l) (𝔞 : Amb l) [CharP 𝔞.V l] (x : c.O)
    (hx : x ∈ maximalIdeal c.O) : 𝔞.a c x = 0 := by
  have hp : (RingHom.ker (𝔞.a c)).IsPrime := RingHom.ker_isPrime _
  have hne : RingHom.ker (𝔞.a c) ≠ ⊥ := fun h => by
    have h1 : (l : c.O) ∈ RingHom.ker (𝔞.a c) := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rw [h, Ideal.mem_bot] at h1
    exact hl.out.ne_zero (Nat.cast_eq_zero.1 h1)
  have hm : (RingHom.ker (𝔞.a c)).IsMaximal := hp.isMaximal hne
  rwa [← eq_maximalIdeal hm] at hx

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem diag_fin (D : Raw Ω c) (hD : D.Good) (𝔞 : Amb l) [CharP 𝔞.V l] (r : G ℚ Ω →* M4 𝔞.V) (u : M4 𝔞.V)
    (hP : KPair D 𝔞 r u) (hd : DiagType r) (g : G ℚ Ω) (i : Fin 4) : IsOfFinOrder (r g i i) := by
  have hl : l.Prime := Fact.out
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨f1, -, -, -, -, -, -, -, -, -, -, f12, -⟩ := facts D hD
  let U : Subgroup (G ℚ Ω) := D.rbar.ker ⊓ D.ψ.ker
  have hU : IsOpen (U : Set (G ℚ Ω)) := f12.inter hD.psi_open
  haveI : Finite (G ℚ Ω ⧸ U) := U.quotient_finite_of_isOpen hU
  have hI : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hT : ∀ p ∈ D.T, p.Prime ∧ ∀ g ∈ D.Ip p, g ∈ U → r g ^ l ^ 2 = 1 := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨hl, fun s hs hu => unip p u (r s) hP.sp (hP.flag s (Ine_le_Dec _ hs)) fun j => ?_⟩
      rw [hP.inert s hs j, ← sub_eq_zero, ← map_one (𝔞.a c), ← map_sub]
      refine a_kill c 𝔞 _ ?_
      have h0 : D.rbar s = 1 := hu.1
      have h1 : D.rbar s j j = (1 : M4 (ResidueField c.O)) j j := by rw [h0]
      rw [Raw.rbar, mapRep_apply, Raw.r0, show diagRep D.ps s j j = D.ps j s from Matrix.diagonal_apply_eq _ j,
        Matrix.one_apply_eq] at h1
      rw [← residue_eq_zero_iff, map_sub, h1, map_one, sub_self]
    · exact ⟨(f1 p hp).1, fun s hs hu => by rw [hP.atP p hp s ⟨hs, hu.2⟩, one_pow]⟩
  have hone : ∀ s, r s = 1 → dchar r hd i s = 1 := fun s hs => by
    show r s i i = 1
    rw [hs, Matrix.one_apply_eq]
  have hine : ∀ B : ValuationSubring Ω, ∀ s ∈ Ine (F := ℚ) B, dchar r hd i s ^ (U.index * l ^ 2) = 1 := by
    intro B s hs
    by_cases hB : Raw.Away D.T B
    · rw [pow_mul, ← map_pow, hone _ (hP.unr B hB _ (pow_mem hs _) (U.pow_index_mem s).1), one_pow]
    · simp only [Raw.Away, not_forall, not_not] at hB
      obtain ⟨p, hp, hv⟩ := hB
      obtain ⟨t, ht⟩ := (B3.placesQ Ω).2.2 p (D.pl p) B (hT p hp).1 (hD.pl_over p (hT p hp).1) hv
      have h1 := (hT p hp).2 _ (pow_mem (ht s hs) _) (U.pow_index_mem _)
      rw [← map_pow, ← pow_mul] at h1
      have h2 := hone _ h1
      have h3 : dchar r hd i (t⁻¹ * s * t) = dchar r hd i s := by
        rw [map_mul, map_mul, mul_right_comm, ← map_mul, inv_mul_cancel, map_one, one_mul]
      rwa [map_pow, h3] at h2
  obtain ⟨A, _, _, _, f, P₁, hf, hc, hm⟩ := hP.small
  have hr : ∀ s a b, f (P₁.r s a b) = r s a b := fun s a b =>
    congrFun (congrFun (DFunLike.congr_fun (congrArg PD.r hm) s) a) b
  have hd₁ : DiagType P₁.r := fun a b hab ⟨s, hs⟩ ⟨t, ht⟩ =>
    hd a b hab ⟨s, fun e => hs (hf.inj (by rw [hr, e, map_zero]))⟩ ⟨t, fun e => ht (hf.inj (by rw [hr, e, map_zero]))⟩
  have h := mink (dchar P₁.r hd₁ i) (hc i i) (U.index * l ^ 2) (fun B s hs => hf.inj (by
    rw [map_pow, map_one, ← hine B s hs]
    exact congrArg (· ^ _) (hr s i i))) g
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨U.index * l ^ 2, Nat.pos_of_ne_zero (mul_ne_zero hI (pow_ne_zero _ hl.ne_zero)), ?_⟩
  rw [← hr, ← map_pow, ← map_one f]
  exact congrArg f h

end UpperTheory.V.Ws.DiagonalConstancy

open UpperTheory.V.Ws.DiagonalConstancy in
theorem UpperTheory.V.Ws.diagConst :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l), CharP 𝔞.K l → ∀ r, VPt D 𝔞 r → ∀ u, KPair D 𝔞 r u → DiagType r → ∀ x ∈ mono r 0, ∃ n : ℕ, 0 < n ∧ x ^ l ^ n = x := by
  intro Ω _ _ _ l _ c D hD 𝔞 hK r hV u hP hd x hx
  haveI : CharP 𝔞.V l := 𝔞.toK.charP Subtype.val_injective l
  obtain ⟨-, R, i1, i2, i3, ρ, y, hρ, hy, -, hr⟩ := hV
  letI : Algebra c.O 𝔞.K := (𝔞.toK.comp (𝔞.a c)).toAlgebra
  let y' : R →ₐ[c.O] 𝔞.K :=
    { toRingHom := 𝔞.toK.comp y
      commutes' := fun a => congrArg 𝔞.toK (RingHom.congr_fun hy a) }
  have hpt : D.PtIn 𝔞.K (mapRep 𝔞.toK r) := ⟨R, i1, i2, i3, ρ, y', hρ, by subst hr; ext g i j; rfl⟩
  obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ _ hpt
  obtain ⟨-, g2, g3, g4, -⟩ := geAlg _ _ _ p1 p6
  have hiff : ∀ i j, Ge (mapRep 𝔞.toK r) i j ↔ Ge r i j := fun i j =>
    exists_congr fun g => by simp
  simp only [hiff] at g2 g3 g4
  obtain ⟨φ, hφ⟩ := exists_form (Ge r) g2 g3 g4 hd
  exact frob_fix l x (mono_fin r φ hφ (diag_fin D hD 𝔞 r u hP hd) x hx)
end

