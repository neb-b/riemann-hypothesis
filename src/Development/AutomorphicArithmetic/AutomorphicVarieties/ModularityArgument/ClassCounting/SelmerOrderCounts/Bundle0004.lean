module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.UnitLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
public import Development.EtaleCohomology.CyclotomicDiscriminants.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_prod (E : Type) [AddCommGroup E] (δ : Module.End ℤ E) (m : ℕ) :
    Nonempty (((E × ℤ) ⧸ (LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ))) ≃
      (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m) := by
  let φ : (E × ℤ) →ₗ[ℤ] (E ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ E)) × ZMod m :=
    (Submodule.mkQ _).prodMap (Int.castAddHom (ZMod m)).toIntLinearMap
  have hs : Function.Surjective φ := fun ⟨x, y⟩ => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective y
    exact ⟨(x, y), rfl⟩
  have hk : LinearMap.ker φ =
      LinearMap.range (δ.prodMap ((-(m : ℤ)) • LinearMap.id)) ⊔ Submodule.torsion ℤ (E × ℤ) := by
    ext ⟨x, y⟩
    rw [LinearMap.mem_ker, Prod.ext_iff, Submodule.mem_sup]
    change (Submodule.Quotient.mk x = 0 ∧ (y : ZMod m) = 0) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, hr⟩, rfl⟩, k, rfl⟩
      exact ⟨_, ⟨(a, -k), rfl⟩, (t, 0), ⟨r, Prod.ext hr (by simp)⟩, by simp⟩
    · rintro ⟨_, ⟨⟨a, k⟩, rfl⟩, ⟨t, s⟩, ⟨r, hr⟩, h⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
      obtain ⟨h3, h4⟩ := Prod.ext_iff.1 hr
      have hs : s = 0 := (mul_eq_zero.1 (show (r : ℤ) * s = 0 from h4)).resolve_left (nonZeroDivisors.coe_ne_zero r)
      refine ⟨⟨_, ⟨a, rfl⟩, t, ⟨r, h3⟩, h1⟩, -k, ?_⟩
      simpa [hs] using h2.symm
  exact ⟨((Submodule.quotEquivOfEq _ _ hk.symm).trans (φ.quotKerEquivOfSurjective hs)).toEquiv⟩

theorem UpperTheory.V.ZK.Ct.cardEQ :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a : ℕ) (D : Dat (Additive Fˣ) (HeightOneSpectrum (𝓞 F) →₀ ℤ)), IsTotallyComplex L → IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → IsDat γ a D → Finite D.EQ ∧ Nat.card D.EQ * (a - 1) = (a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L := by
  intro L F _ _ _ _ _ γ a D hL hG hγ hD
  classical
  obtain ⟨hF, hc, hfree⟩ := places L F γ hL hG hγ
  have ha : 2 ≤ a := hD.a_eq ▸ D.two_le
  have hn : 0 < orderOf γ := hD.n_eq ▸ D.n_pos
  let ι : Additive (𝓞 F)ˣ →ₗ[ℤ] Additive Fˣ :=
    (MonoidHom.toAdditive (Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F))).toIntLinearMap
  have hι : Function.Injective ι := Units.map_injective RingOfIntegers.coe_injective
  have hr : LinearMap.range ι = LinearMap.ker D.d := by
    ext α
    obtain ⟨α, rfl⟩ := Additive.ofMul.surjective α
    have hv : D.d (Additive.ofMul α) = 0 ↔ ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F (α : F) = 1 := by
      rw [Finsupp.ext_iff]
      refine forall_congr' fun P => ?_
      rw [hD.d_eq, valuation_eq_exp_ordP, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]; rfl
    rw [LinearMap.mem_ker, hv]
    constructor
    · rintro ⟨u, hu⟩ P
      obtain rfl : Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u.toMul = α := hu
      refine le_antisymm (P.valuation_le_one (K := F) _) ?_
      have h1 := P.valuation_le_one (K := F) ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
      have h2 : P.valuation F (algebraMap (𝓞 F) F (u.toMul : (𝓞 F)ˣ)) *
          P.valuation F (algebraMap (𝓞 F) F ((u.toMul⁻¹ : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
        rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
      calc (1 : _) = _ := h2.symm
        _ ≤ _ * 1 := mul_le_mul_right h1 _
        _ = _ := mul_one _
    · intro h
      obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (α : F) fun P => (h P).le
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((α⁻¹ : Fˣ) : F) fun P => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h P, inv_one]
      have hxy : x * y = 1 := RingOfIntegers.coe_injective (by rw [map_mul, hx, hy, map_one, Units.mul_inv])
      exact ⟨Additive.ofMul (Units.mkOfMulEqOne x y hxy), Units.ext hx⟩
  let g : Module.End ℤ (Additive (𝓞 F)ˣ) := (MonoidHom.toAdditive (Units.map
    (RingOfIntegers.mapRingEquiv (γ⁻¹).toRingEquiv : 𝓞 F →* 𝓞 F))).toIntLinearMap
  let δ : Module.End ℤ (Additive (𝓞 F)ˣ) := g - (a : ℤ) • 1
  have hδ : ∀ u, ι (δ u) = D.del (ι u) := fun u => by
    have : ι (g u) = D.g (ι u) := by
      refine Eq.trans ?_ (hD.g_eq (ι u).toMul).symm
      exact congrArg Additive.ofMul (Units.ext rfl)
    simp only [δ, Dat.del, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_zsmul, this, hD.a_eq]
  let e : Additive (𝓞 F)ˣ ≃ₗ[ℤ] LinearMap.ker D.d := (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ u, (e u : Additive Fˣ) = ι u := fun _ => rfl
  have e2 : (Additive (𝓞 F)ˣ ⧸ (LinearMap.range δ ⊔ Submodule.torsion ℤ _)) ≃ₗ[ℤ] D.EQ := by
    refine Submodule.Quotient.equiv _ _ e ?_
    ext y
    obtain ⟨u, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, e.symm_apply_apply, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, he,
      Submodule.mem_sup, Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, t, ⟨r, ht⟩, rfl⟩
      refine ⟨_, ⟨ι v, hr ▸ ⟨v, rfl⟩, rfl⟩, ι t, ⟨r, ?_⟩, by rw [map_add (f := _), hδ]⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [← map_smul, ht, map_zero]
    · rintro ⟨_, ⟨v, hv, rfl⟩, t, ⟨r, ht⟩, h⟩
      rw [← hr] at hv
      obtain ⟨v, rfl⟩ := hv
      refine ⟨_, ⟨v, rfl⟩, u - δ v, ⟨r, hι ?_⟩, by abel⟩
      rw [Submonoid.smul_def] at ht ⊢
      rw [map_smul, map_sub, hδ, ← h, add_sub_cancel_left, ht, map_zero]
  let lam : Additive (𝓞 F)ˣ × ℤ →ₗ[ℤ] (InfinitePlace F → ℝ) := AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Real.log (w ((x.1.toMul : 𝓞 F) : F)) + x.2
      map_zero' := by ext w; simp
      map_add' := fun x y => by
        ext w
        simp only [Prod.fst_add, toMul_add, Units.val_mul, map_mul, Prod.snd_add, Int.cast_add, Pi.add_apply]
        rw [Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne']; ring }
  obtain ⟨u1, u2, u3⟩ := unitLat F hF lam fun _ _ _ => rfl
  have hdet := permDet (InfinitePlace F) (MulAction.toPerm γ) (orderOf γ) _ (a : ℝ) hn (by exact_mod_cast (by omega : 1 ≤ a)) hc
    fun k w => by rw [← hfree, ← MulAction.toPermHom_apply, ← map_pow]; rfl
  have h1 : (1 : ℝ) < (a : ℝ) ^ orderOf γ := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < a)) hn.ne'
  obtain ⟨f1, f2⟩ := latDet _ _ lam (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id))
    (LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) - (a : ℝ) • LinearMap.id) (by
      rintro ⟨u, m⟩
      have h2 : lam (g u, m) = LinearMap.funLeft ℝ ℝ (MulAction.toPerm γ : Equiv.Perm (InfinitePlace F)) (lam (u, m)) := by
        ext w; rfl
      have h3 : (δ.prodMap ((-((a - 1 : ℕ) : ℤ)) • LinearMap.id)) (u, m) = (g u, m) - (a : ℤ) • (u, m) := by
        refine Prod.ext rfl ?_
        simp only [LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, Prod.snd_sub, Prod.smul_snd]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [h3, map_sub, h2, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul,
        Nat.cast_smul_eq_nsmul]) u1 u2 u3
    (by rw [← abs_pos, hdet]; exact pow_pos (by linarith) _)
  obtain ⟨e3⟩ := card_prod _ δ (a - 1)
  haveI : NeZero (a - 1) := ⟨by omega⟩
  have f3 := (e3.finite_iff).1 f1
  refine ⟨e2.toEquiv.finite_iff.1 (Finite.prod_left (ZMod (a - 1))), ?_⟩
  rw [Nat.card_congr e3, Nat.card_prod, Nat.card_zmod, Nat.card_congr e2.toEquiv, hdet] at f2
  have h4 : 1 ≤ a ^ orderOf γ := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast f2.trans (by rw [Nat.cast_pow, Nat.cast_sub h4]; push_cast; rfl :
    ((a : ℝ) ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L = (((a ^ orderOf γ - 1) ^ InfinitePlace.nrComplexPlaces L : ℕ) : ℝ))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PowEqOneOfDvd
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {l c ν : ℕ} {ζ : (𝓞 F)ˣ}
  {γ : F ≃ₐ[L] F}

theorem UpperTheory.V.ZK.Ct.pow_act (h : Lay l c ν ζ γ) (j : ℕ) :
    (γ ^ j) ((ζ : 𝓞 F) : F) = ((ζ : 𝓞 F) : F) ^ (1 + l ^ c) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h.act, map_pow, ih, ← pow_mul, ← pow_succ]

private theorem pow_sub_dvd_of_pow_dvd_one_add_pow_pow_sub_one (l c ν j : ℕ) (hl : l.Prime) (h1 : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hcν : c ≤ ν) (hj : l ^ ν ∣ (1 + l ^ c) ^ j - 1) : l ^ (ν - c) ∣ j := by
  have hpl : Prime l := hl.prime
  have hndvd : ¬ l ∣ 1 + l ^ c := fun h =>
    hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left (dvd_pow_self l (by omega))).mp h))
  have key : emultiplicity l ((1 + l ^ c) ^ j - 1) = c + emultiplicity l j := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have hc2 := h2 rfl
      have hle : 1 ≤ (1 + 2 ^ c) ^ j := Nat.one_le_pow _ _ (by positivity)
      have := Int.two_pow_sub_pow' (x := 1 + 2 ^ c) (y := 1) j ?_ ?_
      · rw [one_pow, add_sub_cancel_left] at this
        rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity, Nat.cast_sub hle]
        push_cast
        rw [this, emultiplicity_pow_self_of_prime Int.prime_two]
      · rw [add_sub_cancel_left]
        exact (pow_dvd_pow 2 hc2 : (2:ℤ) ^ 2 ∣ 2 ^ c)
      · intro h
        apply hndvd
        exact_mod_cast h
    · have := Nat.emultiplicity_pow_sub_pow hl hodd (x := 1 + l ^ c) (y := 1)
        (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self l (by omega)) hndvd j
      rw [one_pow, Nat.add_sub_cancel_left, emultiplicity_pow_self_of_prime hpl] at this
      exact this
  have hν := (pow_dvd_iff_le_emultiplicity.mp hj)
  rw [key] at hν
  apply pow_dvd_iff_le_emultiplicity.mpr
  have e : ((ν : ℕ) : ℕ∞) = (c : ℕ∞) + ((ν - c : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add, Nat.add_sub_cancel' hcν]
  rw [e] at hν
  exact (WithTop.add_le_add_iff_left (ENat.coe_ne_top c)).mp hν

theorem UpperTheory.V.ZK.Ct.pow_eq_one_of_dvd (hl : l.Prime) (h : Lay l c ν ζ γ) (j : ℕ)
    (hj : l ^ ν ∣ (1 + l ^ c) ^ j - 1) : γ ^ j = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, h.ord]
  exact pow_sub_dvd_of_pow_dvd_one_add_pow_pow_sub_one l c ν j hl h.c_pos h.c_two h.c_le hj

theorem UpperTheory.V.ZK.Ct.inertia_eq_bot (hl : l.Prime) (h : Lay l c ν ζ γ) (P : HeightOneSpectrum (𝓞 F))
    (hP : (l : 𝓞 F) ∉ P.asIdeal) : P.asIdeal.inertia (F ≃ₐ[L] F) = ⊥ := by
  have hG := h.gal
  have : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hPp : P.asIdeal.IsPrime := P.isPrime
  have hPne : P.asIdeal ≠ ⊥ := P.ne_bot
  haveI : NeZero P.asIdeal := ⟨hPne⟩
  have hz : IsPrimitiveRoot (ζ : 𝓞 F) (l ^ ν) := IsPrimitiveRoot.coe_units_iff.mpr h.prim
  have hn1 : Ideal.absNorm P.asIdeal ≠ 1 := fun e => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp e)
  have hcop : (Ideal.absNorm P.asIdeal).Coprime (l ^ ν) := by
    apply Nat.Coprime.pow_right
    have hq := Nat.absNorm_under_prime P.asIdeal
    rw [Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal hq]
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_primes hq hl]
    intro e
    apply hP
    have := Int.absNorm_under_mem P.asIdeal
    rw [e] at this
    exact_mod_cast this
  have hzq := hz.idealQuotient_mk hn1 hcop
  rw [eq_bot_iff]
  intro σ hσ
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr (h.gen σ))
  rw [Subgroup.mem_bot]
  apply UpperTheory.V.ZK.Ct.pow_eq_one_of_dvd hl h j
  have hm := AddSubgroup.mem_inertia.mp hσ (ζ : 𝓞 F)
  have hact : (γ ^ j) • (ζ : 𝓞 F) = (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j := by
    apply RingOfIntegers.coe_injective
    exact UpperTheory.V.ZK.Ct.pow_act h j
  rw [hact] at hm
  have hq : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ^ (1 + l ^ c) ^ j =
      Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hpos : 1 ≤ (1 + l ^ c) ^ j := Nat.one_le_pow _ _ (by positivity)
  have hne : Ideal.Quotient.mk P.asIdeal (ζ : 𝓞 F) ≠ 0 := hzq.ne_zero (pow_ne_zero _ hl.ne_zero)
  apply hzq.dvd_of_pow_eq_one
  rw [← Nat.sub_add_cancel hpos, pow_succ] at hq
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact (mul_comm _ _).trans hq)

end

theorem UpperTheory.V.ZK.Ct.unram :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), l.Prime → Lay l c ν ζ γ → ∀ (x : Lˣ) (P : HeightOneSpectrum (𝓞 F)) (p : HeightOneSpectrum (𝓞 L)), (l : 𝓞 L) ∉ p.asIdeal → P.asIdeal.LiesOver p.asIdeal → ordP P (Units.map (algebraMap L F : L →* F) x) = ordP p x := by
  intro L F _ _ _ _ _ l c ν ζ γ hl h x P p hlp hlies
  have hG := h.gal
  have : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  have hlP : (l : 𝓞 F) ∉ P.asIdeal := by
    intro hm
    apply hlp
    rw [Ideal.over_def P.asIdeal p.asIdeal]
    apply Ideal.mem_comap.mpr
    simpa using hm
  have hI := UpperTheory.V.ZK.Ct.inertia_eq_bot hl h P hlP
  have he : p.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.asIdeal p.ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal P.asIdeal (F ≃ₐ[L] F),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[L] F) p.asIdeal P.asIdeal, hI]
    simp
  have hv := HeightOneSpectrum.valuation_liesOver F p P (x : L)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.asIdeal p.ne_bot] at he
  rw [he, pow_one] at hv
  simp only [ordP, Units.coe_map, MonoidHom.coe_coe, ← hv]
end

