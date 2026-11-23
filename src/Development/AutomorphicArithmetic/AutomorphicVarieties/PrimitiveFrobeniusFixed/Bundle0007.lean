module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XCongJac
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Bundle0001
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.AlgStep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem alg_step {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (A B x z ζ : L)
    (hA : w A = 1) (hx : w x = 1) (hζ : w ζ = 1) (h1 : w (A - B) < 1) (h2 : w (A / x - ζ * (B / z)) < 1) :
    w (x - ζ⁻¹ * z) < 1 := by
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hA
    exact zero_ne_one hA
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact zero_ne_one hζ
  have hB : w B = 1 := by
    have e : B = (B - A) + A := by ring
    rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hA]), hA]
  have hAx : w (A / x) = 1 := by rw [map_div₀, hA, hx, div_one]
  have hz : w z = 1 := by
    have h3 : w (ζ * (B / z)) = 1 := by
      have e : ζ * (B / z) = (ζ * (B / z) - A / x) + A / x := by ring
      rw [e, w.map_add_eq_of_lt_right (by rwa [w.map_sub_swap, hAx]), hAx]
    rw [map_mul, map_div₀, hζ, hB, one_mul, one_div] at h3
    exact inv_eq_one.mp h3
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have e : x - ζ⁻¹ * z = x * (A - B) / A - (A / x - ζ * (B / z)) * (x * z * ζ⁻¹ / A) := by
    field_simp
    ring
  rw [e]
  refine lt_of_le_of_lt (w.map_sub _ _) (max_lt ?_ ?_)
  · rw [map_div₀, map_mul, hx, hA, one_mul, div_one]
    exact h1
  · rw [map_mul, map_div₀, map_mul, map_mul, map_inv₀, hx, hz, hζ, hA]
    simpa using h2

private theorem isX_unit (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]
    (b q : ℕ) (𝔞 : Ideal (𝓞 K)) (X : K) (h0 : 𝔞 ≠ ⊥) (hc : IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K)})) (hX : IsX N K b 𝔞 X)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (q : 𝓞 K) ∈ v.asIdeal) : v.valuation K X = 1 := by
  haveI := v.isPrime
  obtain ⟨a, ha, c, hc', hac⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hc'
  have hne : ∀ t, conjI N K 𝔞 t ≠ ⊥ := by
    intro t hb
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hm : (sgO N K t).symm e ∈ conjI N K 𝔞 t := by
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact he
    rw [hb, Ideal.mem_bot] at hm
    exact he0 (by simpa using hm)
  have hnle : ∀ t, ¬ conjI N K 𝔞 t ≤ v.asIdeal := by
    intro t ht'
    have ha' : (sgO N K t).symm a ∈ v.asIdeal := by
      apply ht'
      rw [mem_conjI, RingEquiv.apply_symm_apply]
      exact ha
    have hc'' : (sgO N K t).symm (r * (q : 𝓞 K)) ∈ v.asIdeal := by
      rw [map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ hv
    have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
      have e : (1 : 𝓞 K) = (sgO N K t).symm a + (sgO N K t).symm (r * (q : 𝓞 K)) := by
        rw [← map_add (f := _), hac, map_one]
      rw [e]
      exact Ideal.add_mem _ ha' hc''
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hcount : ∀ t, FractionalIdeal.count K v ((conjI N K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro t
    rw [FractionalIdeal.count_coe K v (hne t), Nat.cast_eq_zero]
    by_contra hc0
    have hdvd := (Associates.count_ne_zero_iff_dvd (hne t) v.irreducible).mp hc0
    exact hnle t (Ideal.le_of_dvd hdvd)
  have hX0 : X ≠ 0 := by
    intro h
    have h1 := hX.1
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have hcs := GroundTheory.Global.count_spanSingleton v hX0
  rw [hX.2, FractionalIdeal.count_prod K v _ _
    (fun t _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne t))),
    Finset.sum_eq_zero (fun t _ => by rw [FractionalIdeal.count_zpow, hcount t, mul_zero])] at hcs
  have hv0 : v.valuation K X ≠ 0 := (Valuation.ne_zero_iff _).mpr hX0
  have hl : WithZero.log (v.valuation K X) = 0 := by linarith
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

theorem UpperTheory.V.ML.xCong :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < M → b < q → ∀ (𝔞 : Ideal (𝓞 K')) (X' : K') (X : K), IsCoprime 𝔞 (Ideal.span {(q : 𝓞 K')}) →
    IsX (q * M) K' b 𝔞 X' → IsX M K b (Ideal.relNorm (𝓞 K) 𝔞) X →
    ∃ ζ : K', ζ ^ (2 * (q * M)) = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → v.valuation K' (X' - ζ * algebraMap K K' ((sg M K u)⁻¹ X)) < 1 := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hbM hbq 𝔞 X' X hc hX' hX
  have key : ∀ I : Ideal (𝓞 K'), IsCoprime I (Ideal.span {(q : 𝓞 K')}) →
      ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → ¬ I ≤ v.asIdeal := by
    intro I hI v hv hle
    rw [Ideal.isCoprime_iff_sup_eq] at hI
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← hI]
    exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  by_cases h0 : 𝔞 = ⊥
  · refine ⟨1, one_pow _, fun v hv => ?_⟩
    exact (key 𝔞 hc v hv (by rw [h0]; exact bot_le)).elim
  have h𝔞nz : 𝔞 ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero h0
  have hS : {v : HeightOneSpectrum (𝓞 K') | ((q * M : ℕ) : 𝓞 K') ∈ v.asIdeal}.Finite := by
    have hne : Ideal.span {((q * M : ℕ) : 𝓞 K')} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr (NeZero.ne _)
    exact (Ideal.finite_factors hne).subset (fun v hv => Ideal.dvd_span_singleton.mpr hv)
  obtain ⟨P, hPS, hPp, hPcl⟩ := degOne K' _ hS (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹
  set p := Ideal.absNorm P.asIdeal with hpdef
  haveI : Fact p.Prime := ⟨hPp⟩
  obtain ⟨π, hπ⟩ := (red K' p P.asIdeal).1 rfl
  have hPnz : P.asIdeal ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have hprin : Submodule.IsPrincipal (P.asIdeal * 𝔞) := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem hPnz h𝔞nz)]
    have hm : ClassGroup.mk0 ⟨P.asIdeal * 𝔞, mul_mem hPnz h𝔞nz⟩ =
        ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ * ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩ := by
      rw [← map_mul]
      rfl
    have hcl : ClassGroup.mk0 ⟨P.asIdeal, hPnz⟩ = (ClassGroup.mk0 ⟨𝔞, h𝔞nz⟩)⁻¹ := hPcl
    rw [hm, hcl, inv_mul_cancel]
  obtain ⟨⟨y, hy⟩⟩ := hprin
  rw [Ideal.submodule_span_eq] at hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hy
    exact (Ideal.mul_eq_bot.mp hy).elim P.ne_bot h0
  have hPc : IsCoprime P.asIdeal (Ideal.span {(q : 𝓞 K')}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have heq := P.isMaximal.eq_of_le hne le_sup_left
    have hqP : (q : 𝓞 K') ∈ P.asIdeal := by
      rw [heq]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqP
  have hpcop : p.Coprime (q * M) := by
    rw [Nat.Prime.coprime_iff_not_dvd hPp]
    rintro ⟨k, hk⟩
    apply hPS
    show ((q * M : ℕ) : 𝓞 K') ∈ P.asIdeal
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ ((red K' p P.asIdeal).2 π hπ).2.2.2
  obtain ⟨-, hm2, -, -, hm5⟩ := xMul (q * M) K' b
  obtain ⟨-, hn2, -, -, hn5⟩ := xMul M K b
  have hA : IsX (q * M) K' b (Ideal.span {y}) (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) :=
    hm5 y hy0
  have hXP' := hm2 P.asIdeal 𝔞 _ X' P.ne_bot h0 (by rw [hy]; exact hA) hX'
  have hrel : Ideal.relNorm (𝓞 K) (Ideal.span {y}) ≠ ⊥ := by
    rw [Ne, Ideal.relNorm_eq_bot_iff, Ideal.span_singleton_eq_bot]
    exact hy0
  have hB : IsX M K b (Ideal.relNorm (𝓞 K) (Ideal.span {y}))
      (∏ t, ((sg M K) t)⁻¹ (Algebra.norm K (y : K')) ^ th M b ↑t) := by
    rw [Ideal.relNorm_singleton] at hrel ⊢
    have hn0 : Algebra.intNorm (𝓞 K) (𝓞 K') y ≠ 0 := by
      intro h
      apply hrel
      rw [h]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have h5 := hn5 _ hn0
    have hcoe : ((Algebra.intNorm (𝓞 K) (𝓞 K') y : 𝓞 K) : K) = Algebra.norm K (y : K') :=
      Algebra.algebraMap_intNorm y
    rw [hcoe] at h5
    exact h5
  have hXP := hn2 _ _ _ X (mt Ideal.relNorm_eq_bot_iff.mp P.ne_bot) (mt Ideal.relNorm_eq_bot_iff.mp h0)
    (by rw [← map_mul, hy]; exact hB) hX
  obtain ⟨ζ1, hζ1, hjac⟩ := xCongJac M q K K' hq u hu b hbM p π hpcop _ _
    (by rw [hπ]; exact hXP') (by rw [hπ]; exact hXP)
  refine ⟨ζ1⁻¹, by rw [inv_pow, hζ1, inv_one], fun v hv => ?_⟩
  have hyv : ∀ v : HeightOneSpectrum (𝓞 K'), (q : 𝓞 K') ∈ v.asIdeal → y ∉ v.asIdeal := by
    intro v hv hyv
    apply key _ (IsCoprime.mul_left hPc hc) v hv
    rw [hy, Ideal.span_singleton_le_iff_mem]
    exact hyv
  have hpr := xCongPrin M q K K' hq u hu b hbq y hyv v hv
  have hX'1 := isX_unit (q * M) K' b q 𝔞 X' h0 hc hX' v hv
  have hP1 := isX_unit (q * M) K' b q P.asIdeal _ P.ne_bot hPc hXP' v hv
  have hX'0 : X' ≠ 0 := by
    intro h
    rw [h, map_zero] at hX'1
    exact zero_ne_one hX'1
  have hAv : v.valuation K' (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) = 1 := by
    rw [← div_mul_cancel₀ (∏ t, ((sg (q * M) K') t)⁻¹ (y : K') ^ th (q * M) b ↑t) hX'0, map_mul, hP1, hX'1, one_mul]
  have hζv : v.valuation K' ζ1 = 1 := by
    have h := congrArg (v.valuation K') hζ1
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff.mp h).resolve_right (mul_ne_zero two_ne_zero (NeZero.ne _))
  have h2 := hjac v hv
  rw [map_div₀, map_div₀] at h2
  exact alg_step (v.valuation K') _ _ X' _ ζ1 hAv hX'1 hζv hpr h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem derivation_ne_zero (q : ℕ) (t : G ℚ Ω) {u : Ω} (hu : u ≠ 0) : der1 q t u ≠ 0 := by
  unfold der1
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)

private theorem derivation_mul (q : ℕ) (t : G ℚ Ω) (u v : Ω) : der1 q t (u * v) = der1 q t u * der1 q t v := by
  unfold der1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, mul_pow]

private theorem derivation_zpow (q : ℕ) (t : G ℚ Ω) (u : Ω) (k : ℤ) : der1 q t (u ^ k) = der1 q t u ^ k := by
  unfold der1
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul,
    mul_comm]

private theorem derivation_galois_equivariant (q : ℕ) (t g : G ℚ Ω) (u : Ω) (h : ∀ s : G ℚ Ω, g (s u) = s (g u)) :
    g (der1 q t u) = der1 q t (g u) := by
  unfold der1
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, h]

private theorem der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => simp only [der.eq_1]
  | cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]

private theorem der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rw [der.eq_1]
  | cons q L ih =>
    rw [der.eq_2, ih]
    unfold der1
    simp

private def derHom (τ : ℕ → G ℚ Ω) (L : List ℕ) : Ω →* Ω where
  toFun := der τ L
  map_one' := der_one τ L
  map_mul' := der_mul τ L

private theorem tele (q : ℕ) (t : G ℚ Ω) (u : Ω) (hu : u ≠ 0) (h : (t ^ (q - 1)) u = u) :
    t (der1 q t u) / der1 q t u = u ^ (q - 1) / nrm q t u := by
  have key : ∀ (a : ℕ → Ω) (n : ℕ),
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n =
        a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range n, a (i + 1) ^ i) * a (n + 1) ^ n * ((∏ i ∈ Finset.range n, a i) * a n) * a (n + 1)
          = ((∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n) * a (n + 1) ^ (n + 1) := by ring
        _ = a 0 * a n ^ n * (∏ i ∈ Finset.range n, a i ^ i) * a (n + 1) ^ (n + 1) := by rw [ih]
        _ = a 0 * a (n + 1) ^ (n + 1) * ((∏ i ∈ Finset.range n, a i ^ i) * a n ^ n) := by ring
  have hD : der1 q t u ≠ 0 := derivation_ne_zero q t hu
  have hN : nrm q t u ≠ 0 := by
    unfold nrm
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu
  have htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i := by
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, pow_succ', AlgEquiv.mul_apply]
  have hk := key (fun i => (t ^ i) u) (q - 1)
  simp only [pow_zero, AlgEquiv.one_apply, h] at hk
  rw [div_eq_div_iff hD hN, htD]
  have hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i := rfl
  have hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u := rfl
  rw [hD', hN']
  apply mul_right_cancel₀ hu
  linear_combination hk

end

theorem UpperTheory.V.ML.derBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N r : ℕ), N ≠ 0 → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω), u ≠ 0 → (∀ g ∈ fixMu ℚ Ω N, g u = u) →
    der τ L u ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g (der τ L u) = der τ L u) ∧ (∀ g : G ℚ Ω, g (der τ L u) = der τ L (g u)) ∧
    ((∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (der τ L u) = 1) ∧
    (∀ v : Ω, der τ L (u * v) = der τ L u * der τ L v) ∧ (∀ k : ℤ, der τ L (u ^ k) = der τ L u ^ k) ∧
    (∀ q, der τ L (der1 q (τ q) u) = der1 q (τ q) (der τ L u)) ∧ (∀ L', L.Perm L' → der τ L u = der τ L' u) ∧
    ∀ q : ℕ, 1 ≤ q → (τ q ^ (q - 1)) u = u → τ q (der1 q (τ q) u) / der1 q (τ q) u = u ^ (q - 1) / nrm q (τ q) u := by
  intro Ω _ _ _ N r hN τ L u hu hfix
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -⟩ := galBasic Ω N hN
  have hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x := by
    intro q t x hx g hg
    rw [derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]
  have hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x := by
    intro L x hx
    induction L with
    | nil => simpa only [der.eq_1] using hx
    | cons q L ih =>
      rw [der.eq_2]
      exact hfix1 q (τ q) _ ih
  have hneL : ∀ L : List ℕ, der τ L u ≠ 0 := by
    intro L
    induction L with
    | nil =>
      rw [der.eq_1]
      exact hu
    | cons q L ih =>
      rw [der.eq_2]
      exact derivation_ne_zero q (τ q) ih
  have hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x) := by
    intro L x hx g
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih =>
      rw [der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]
  have hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x) := by
    intro L x hx q t
    have e : der τ L (der1 q t x) = derHom τ L (der1 q t x) := rfl
    rw [e]
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    show der τ L ((t ^ i) x) ^ i = _
    rw [← hcommL L x hx]
  have hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) →
      ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1 := by
    intro x hx s A hA
    obtain ⟨-, -, -, hlt, heq⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s
    have hsA : s • (s⁻¹ • A) = A := smul_inv_smul s A
    rw [hsA] at hlt heq
    apply (heq x).mpr
    apply hx
    intro hB
    apply hA
    have hr := (hlt (r : Ω)).mpr hB
    show A.valuation (r : Ω) < 1
    simpa using hr
  have hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) →
      ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1 := by
    intro hu1 L
    induction L with
    | nil => simpa only [der.eq_1] using hu1
    | cons q L ih =>
      intro A hA
      rw [der.eq_2]
      unfold der1
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Valuation.map_pow, hconj _ ih _ A hA, one_pow]
  have hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k := by
    intro L k
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]
  have hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u := by
    intro L' hp
    induction hp with
    | nil => rfl
    | cons q _ ih => rw [der.eq_2, der.eq_2, ih]
    | swap a b l =>
      rw [der.eq_2, der.eq_2, der.eq_2, der.eq_2]
      have hx := hfixL l u hfix
      have h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u)) := by
        rw [der.eq_2, der.eq_1]
      rw [h1, hder1 [b] _ hx, der.eq_2, der.eq_1]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L,
    fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ImportsAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.ext :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ), F ≠ 0 → ∀ (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W), IsNu M F n β ν → ∀ δ : G ℚ Ω, IsUnit ((β δ : O) - 1) →
    ∃ c : G ℚ Ω → W, IsCoc β c ∧ (∀ u ∈ fixMu ℚ Ω F, c u = ν u) ∧ ∀ g, ∃ u ∈ fixMu ℚ Ω F, ∃ y : O, c g = y • ν u := by
  intro Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ
  obtain ⟨hN, -, hcomm, -⟩ := galBasic Ω F hF
  have hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1 := hδ.val_inv_mul
  have h1 : ν 1 = 0 := by
    have := hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem
    simpa using this
  have hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u := by
    intro u hu
    have := hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)
  have hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := fun g => hcomm g δ
  refine ⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩
  · have hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹) := by
      have c1 : Continuous (fun g : G ℚ Ω => g * δ) := continuous_mul_const δ
      have c2 : Continuous (fun g : G ℚ Ω => g⁻¹) := continuous_inv
      have c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹) := c1.mul c2
      exact (continuous_mul_const δ⁻¹).comp c3
    have hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F)) := hc.subtype_mk hcm
    have hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹)) := hν.lc.comp_continuous hf
    exact hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)
  · intro g h
    have e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹) := by
      group
    have hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ (hcm h) g
    show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) =
      (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))
    rw [e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]
    abel
  · intro u hu
    have hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ
    have e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹) := by
      group
    have e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u) := by
      rw [sub_smul, one_smul, smul_neg]
      abel
    show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u
    rw [e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul,
      neg_neg, smul_smul, hk, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y) → ∃ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ := by
  intro Ω _ _ _ M F n a _ hFn ζ hζ δ hδ y hy hfix hz
  have hM : M ≠ 0 := NeZero.ne M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hM)
  have hcomm := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 y hfix
  have hroot : ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ∃ k : ℕ, k < M ∧ ζ ^ k = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro g _ z hz'
    apply hζ.eq_pow_of_pow_eq_one
    have hgy : g y ≠ 0 := by simpa using hy
    have hdy : δ y ≠ 0 := by simpa using hy
    have hdgy : δ (g y) ≠ 0 := by simpa using hgy
    unfold opP
    calc (g (δ Y / Y ^ a) / (δ Y / Y ^ a) / (δ z / z ^ a)) ^ M
        = g (δ (Y ^ M)) / (g (Y ^ M)) ^ a / (δ (Y ^ M) / (Y ^ M) ^ a) / (δ (z ^ M) / (z ^ M) ^ a) := by
          simp only [map_div₀, map_pow, div_pow]
          ring
      _ = 1 := by
          rw [hY, hz', map_div₀ δ, hcomm g δ]
          field_simp
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero a hy)]
  classical
  choose! zf hzf using hz
  have hk := fun g hg => hroot g hg (zf g) (hzf g hg).2
  choose! kf hkf using hk
  refine ⟨fun g => (kf g : ZMod M), Y, hY, fun g hg => ⟨zf g, (hzf g hg).1, (hzf g hg).2, ?_⟩⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hkf g hg).1]
  exact (hkf g hg).2
end

