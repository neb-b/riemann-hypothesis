module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AlgK
section
open UpperTheory.V.FW

theorem UpperTheory.V.FW.algK :
    ∀ (l : ℕ) [Fact l.Prime] (a m b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [IsAlgClosed k] [CommGroup G] [Finite G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ J : G) (θ : MonoidAlgebra k G), m.Coprime l → γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, (g * (p g)⁻¹) ^ (l ^ a * m) = 1) → p J = 1 → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → (∀ χ : G →* kˣ, χ J = -1 → tw χ π θ ≠ 0) → (MonoidAlgebra.of k G γ - 1) ^ (l ^ K * l ^ a) ∈ Ideal.span {θ, 1 + MonoidAlgebra.of k G J} := by
  intro l _ a m b K k G Q _ _ _ _ _ _ p π γ J θ hml hγ hp hord hpJ hπ hπγ htw
  have hl : l.Prime := Fact.out
  let I : Ideal (MonoidAlgebra k G) := Ideal.span {θ, 1 + MonoidAlgebra.of k G J}
  let r : MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⧸ I) := Ideal.Quotient.mkₐ k I
  have hr : ∀ x, r x = 0 ↔ x ∈ I := fun x => by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem
  let qh : G →* G :=
    { toFun := fun g => (g * (p g)⁻¹) ^ (l ^ a)
      map_one' := by simp
      map_mul' := by
        intro x y
        rw [map_mul, mul_inv, mul_mul_mul_comm, mul_pow] }
  let D : Subgroup G := qh.range
  let qD : G →* D := qh.rangeRestrict
  have hcard : (Nat.card D : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k l] at h
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' l h
    obtain ⟨g, hg⟩ := d.2
    have h1 : (d : G) ^ m = 1 := by
      rw [← hg]
      show ((g * (p g)⁻¹) ^ (l ^ a)) ^ m = 1
      rw [← pow_mul]
      exact hord g
    have h2 : orderOf d ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using h1)
    rw [hd] at h2
    have h3 : l ∣ Nat.gcd m l := Nat.dvd_gcd h2 dvd_rfl
    rw [hml] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  let ρ : D →* (MonoidAlgebra k G ⧸ I) :=
    ((r : MonoidAlgebra k G →+* (MonoidAlgebra k G ⧸ I)) : MonoidAlgebra k G →* (MonoidAlgebra k G ⧸ I)).comp
      ((MonoidAlgebra.of k G).comp D.subtype)
  have hρ : ∀ g, ρ (qD g) = r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ (l ^ a))) := fun g => rfl
  have hθ : r θ = 0 := (hr θ).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hJ : r (MonoidAlgebra.of k G J) = -1 := by
    have h0 : r (1 + MonoidAlgebra.of k G J) = 0 :=
      (hr _).mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [map_add (f := _), map_one] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have hla : l ^ a ≠ 0 := pow_ne_zero _ hl.ne_zero
  rw [← hr]
  apply sepChar k D _ ρ _ hcard
  intro ψ e he
  by_cases he0 : e = 0
  · rw [he0, mul_zero]
  let F : k ≃+* k := (iterateFrobeniusEquiv k l a).symm
  let χ : G →* kˣ := (Units.map (F : k →* k)).comp (ψ.comp qD)
  have hχ : ∀ g, (χ g : k) ^ (l ^ a) = ψ (qD g) := by
    intro g
    show (F (ψ (qD g) : k)) ^ (l ^ a) = _
    rw [← iterateFrobeniusEquiv_def]
    exact RingEquiv.apply_symm_apply _ _
  have hT : r (tw χ p θ) ^ (l ^ a) * e = 0 := by
    have := frobEig l a k G _ r p χ e θ (by
      intro g
      rw [hχ g, ← hρ g]
      exact he (qD g))
    rw [← this, hθ, zero_pow hla, zero_mul]
  have hχJ : χ J = -1 := by
    have h1 := he (qD J)
    rw [hρ J, hpJ, inv_one, mul_one, map_pow, map_pow, hJ] at h1
    have h2 : ((-1 : k) ^ (l ^ a)) • e = (ψ (qD J) : k) • e := by
      rw [← h1, Algebra.smul_def, map_pow, map_neg, map_one]
    have h3 := smul_left_injective k he0 h2
    rw [← hχ J] at h3
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    apply (iterateFrobeniusEquiv k l a).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def]
    exact h3.symm
  obtain ⟨c, hc⟩ := phiDvd l b K k G Q p π γ χ θ hγ hp hπ hπγ (htw χ hχJ)
  rw [pow_mul, hc, mul_pow, map_mul, map_pow, map_pow, mul_right_comm, hT, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardRangeInfTorsionLeIndexPow
section
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.card_range_inf_torsion_le_index_pow (l : ℕ) [Fact l.Prime] (C : Type) [CommGroup C] [Finite C]
    (φ ψ : C →* C) (N : ℕ) (hc : ∀ x, φ (ψ x) = ψ (φ x))
    (hN : ∀ x, ∃ y, (φ y) ^ l = φ (ψ^[N] x)) :
    Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ ψ.range).index ^ N := by
  set U : Subgroup C := (powR (C := φ.range) l).comap φ.rangeRestrict with hUdef
  have hU : ∀ x, x ∈ U ↔ ∃ y, (φ y) ^ l = φ x := by
    intro x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨φ y, y, rfl⟩, Subtype.ext hy⟩
  have h1 : Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) = U.index := by
    rw [hUdef, Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective,
      (cardTors φ.range).1 l]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩,
      fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hle : U ≤ U.comap ψ := by
    intro x hx
    obtain ⟨y, hy⟩ := (hU x).1 hx
    exact (hU _).2 ⟨ψ y, by rw [hc, hc, ← hy, map_pow]⟩
  set S : C ⧸ U →* C ⧸ U := QuotientGroup.map U U ψ hle with hS
  let T : AddMonoid.End (Additive (C ⧸ U)) := MonoidHom.toAdditive S
  have hT : ∀ n (x : C), (T ^ n) (Additive.ofMul (x : C ⧸ U)) =
      Additive.ofMul ((ψ^[n] x : C) : C ⧸ U) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Function.iterate_succ_apply, ← ih]
      rfl
  have hT0 : T ^ N = 0 := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have : v = Additive.ofMul (x : C ⧸ U) := by rw [hx]; rfl
    subst this
    have h := hT N x
    rw [(QuotientGroup.eq_one_iff _).2 ((hU _).2 (hN x))] at h
    exact h
  have h2 := nilCard _ T N hT0
  have h3 : (AddMonoidHom.range T).index = S.range.index := rfl
  have h4 : S.range.index ∣ (powR (C := C) l ⊔ ψ.range).index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]
    refine Subgroup.index_dvd_of_le (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff _).2 ((hU _).2 ⟨x, by simp⟩)).symm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : C ⧸ U), rfl⟩
  rw [h1]
  refine le_trans (le_of_eq ?_) (h2.trans ?_)
  · rfl
  · rw [h3]
    exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h4) N

theorem UpperTheory.V.FW.core :
    ∀ (l : ℕ) [Fact l.Prime] (G C : Type) [CommGroup G] [CommGroup C] [Finite C] (ρ : Representation ℤ G (Additive C)) (J γ : G) (Jc γc : C →* C) (θ : MonoidAlgebra ℤ G) (N : ℕ), J * J = 1 → (∀ x, ρ J (Additive.ofMul x) = Additive.ofMul (Jc x)) → (∀ x, ρ γ (Additive.ofMul x) = Additive.ofMul (γc x)) → ρ.asAlgebraHom (θ * (1 - MonoidAlgebra.of ℤ G J)) = 0 → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} → Nat.card (difR Jc ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ difR γc).index ^ N := by
  intro l _ G C _ _ _ ρ J γ Jc γc θ N hJJ hJ hγ hθ hmem
  have key : ∀ (g : G) (gc : C →* C), (∀ x, ρ g (Additive.ofMul x) = Additive.ofMul (gc x)) →
      ∀ x, ρ.asAlgebraHom (1 - MonoidAlgebra.of ℤ G g) (Additive.ofMul x) =
        Additive.ofMul ((MonoidHom.id C / gc) x) := by
    intro g gc h x
    rw [map_sub, map_one, Representation.asAlgebraHom_of, LinearMap.sub_apply, h]
    simp
  have hφ := key J Jc hJ
  have hψ := key γ γc hγ
  set φ := MonoidHom.id C / Jc
  set ψ := MonoidHom.id C / γc
  set a := 1 - MonoidAlgebra.of ℤ G J with ha
  set b := 1 - MonoidAlgebra.of ℤ G γ with hb
  have hit : ∀ n x, ρ.asAlgebraHom (b ^ n) (Additive.ofMul x) = Additive.ofMul (ψ^[n] x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, map_mul, mul_apply_eq_comp, hψ, ih, Function.iterate_succ_apply]
  refine card_range_inf_torsion_le_index_pow l C φ ψ N (fun x => ?_) (fun x => ?_)
  · apply Additive.ofMul.injective
    rw [← hφ, ← hψ, ← hψ, ← hφ, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul,
      ← map_mul, mul_comm]
  · have hmem' : b ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} := by
      have : b = -(MonoidAlgebra.of ℤ G γ - 1) := by rw [hb, neg_sub]
      rw [this, neg_pow]
      exact Ideal.mul_mem_left _ _ hmem
    obtain ⟨u, w, hw, h1⟩ := Ideal.mem_span_insert.1 hmem'
    obtain ⟨v, z, h2⟩ := Ideal.mem_span_pair.1 hw
    have hJ2 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by
      rw [← map_mul, hJJ, map_one]
    have h3 : a * b ^ N = u * (θ * a) + l • (a * z) := by
      rw [h1, ← h2, ha, nsmul_eq_mul]
      linear_combination (-v) * hJ2
    refine ⟨Additive.toMul (ρ.asAlgebraHom z (Additive.ofMul x)), ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow, ← hφ, ← hφ, ← hit, ofMul_toMul, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
      ← map_mul, ← map_mul, h3, map_add, map_mul _ u, hθ, mul_zero, zero_add, map_nsmul,
      LinearMap.smul_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DeltaBij
section
open UpperTheory.V.FW

private theorem crt_apply {a b : ℕ} (hab : a.Coprime b) (x : ZMod (a * b)) :
    ZMod.chineseRemainder hab x =
      (ZMod.castHom (Dvd.intro b rfl) (ZMod a) x, ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, map_intCast, map_intCast]
  rfl

private theorem crt_inj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b) (x y : (ZMod (a * b))ˣ)
    (h1 : ZMod.unitsMap ha x = ZMod.unitsMap ha y) (h2 : ZMod.unitsMap hb x = ZMod.unitsMap hb y) : x = y := by
  apply Units.ext
  apply (ZMod.chineseRemainder hab).injective
  rw [crt_apply, crt_apply]
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

private theorem crt_surj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b)
    (u : (ZMod a)ˣ) (v : (ZMod b)ˣ) :
    ∃ x : (ZMod (a * b))ˣ, ZMod.unitsMap ha x = u ∧ ZMod.unitsMap hb x = v := by
  let x : (ZMod (a * b))ˣ :=
    Units.map (ZMod.chineseRemainder hab).symm.toMonoidHom (MulEquiv.prodUnits.symm (u, v))
  have hx : ZMod.chineseRemainder hab (x : ZMod (a * b)) = ((u : ZMod a), (v : ZMod b)) :=
    (ZMod.chineseRemainder hab).apply_symm_apply _
  rw [crt_apply] at hx
  exact ⟨x, Units.ext (congrArg Prod.fst hx), Units.ext (congrArg Prod.snd hx)⟩

private theorem map_map {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 x) = ZMod.unitsMap (h1.trans h2) x := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

private theorem map_redU (l : ℕ) [Fact l.Prime] {m n : ℕ} (hmn : m ≤ n) (h : l ^ m ∣ l ^ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redU l n w) = redU l m w := by
  apply Units.ext
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

theorem UpperTheory.V.FW.deltaBij :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (h' : l ^ n ∣ f * l ^ n), f.Coprime l → ee l ≤ n → Function.Bijective ((ZMod.unitsMap h).comp (((WW l).map (redU l n)).comap (ZMod.unitsMap h')).subtype) := by
  intro l _ f n h h' hf hn
  have hen : l ^ ee l ∣ l ^ n := pow_dvd_pow l hn
  have hfe : f ∣ f * l ^ ee l := Dvd.intro _ rfl
  have hle : l ^ ee l ∣ f * l ^ ee l := Dvd.intro_left _ rfl
  have hfn : f ∣ f * l ^ n := Dvd.intro _ rfl
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨g, w, hw, hwg⟩ hg
    have hg' : ZMod.unitsMap h g = 1 := hg
    have h1 : redU l (ee l) w = 1 := by
      rw [← map_redU l hn hen, hwg, map_map, ← map_map hle h, hg', map_one]
    have h2 : (⟨w, hw⟩ : WW l) = 1 := (injective_iff_map_eq_one _).1 (teich l).1 _ h1
    have h3 : w = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    show g = 1
    apply crt_inj (hf.pow_right n) hfn h'
    · rw [← map_map hfe h, hg', map_one, map_one]
    · rw [← hwg, h3, map_one, map_one]
  · intro u
    obtain ⟨w, hw⟩ := (teich l).2 (ZMod.unitsMap hle u)
    have hw' : redU l (ee l) w = ZMod.unitsMap hle u := hw
    obtain ⟨g, hg1, hg2⟩ := crt_surj (hf.pow_right n) hfn h' (ZMod.unitsMap hfe u) (redU l n w)
    refine ⟨⟨g, w, w.2, hg2.symm⟩, ?_⟩
    show ZMod.unitsMap h g = u
    apply crt_inj (hf.pow_right (ee l)) hfe hle
    · rw [map_map, hg1]
    · rw [map_map, ← map_map hen h', hg2, map_redU l hn, hw']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EvenTot
section
open UpperTheory.V.FW

private theorem even_tot (l : ℕ) [hl : Fact l.Prime] : Even (Nat.totient (l ^ ee l)) := by
  apply Nat.totient_even
  unfold ee
  split_ifs with h
  · subst h; norm_num
  · have := hl.out.two_le
    rw [pow_one]; omega

private theorem pos_tot (l : ℕ) [hl : Fact l.Prime] : 0 < Nat.totient (l ^ ee l) :=
  Nat.totient_pos.2 (pow_pos hl.out.pos _)

private theorem neg_ne (l : ℕ) [Fact l.Prime] (r : ℤ_[l]ˣ) : r ≠ -r := by
  intro h
  have h1 : (r : ℤ_[l]) = -(r : ℤ_[l]) := by
    have := congrArg Units.val h
    simpa using this
  exact r.ne_zero (self_eq_neg.1 h1)

theorem UpperTheory.V.FW.reps :
    ∀ (l : ℕ) [Fact l.Prime], ∃ R : Finset ℤ_[l]ˣ, R.Nonempty ∧ (∀ r ∈ R, r ∈ WW l) ∧ (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∀ a b : ℤ, (a : ℤ_[l]) * r = (b : ℤ_[l]) * r' → a = 0) ∧ (∀ r ∈ R, -r ∉ R) ∧ (∀ w ∈ WW l, w ∈ R ∨ -w ∈ R) ∧ (-1 : ℤ_[l]ˣ) ∈ WW l ∧ ∀ n, 2 ≤ n → ∀ w ∈ WW l, redU l n w = 1 → w = 1 := by
  intro l _
  classical
  have hev := even_tot l
  have hpos := pos_tot l
  haveI : NeZero (Nat.totient (l ^ ee l)) := ⟨hpos.ne'⟩
  have hfin : (WW l : Set ℤ_[l]ˣ).Finite := by
    have : Finite (rootsOfUnity (Nat.totient (l ^ ee l)) ℤ_[l]) := inferInstance
    exact Set.finite_coe_iff.1 this
  have hm1 : (-1 : ℤ_[l]ˣ) ∈ WW l := by
    unfold WW
    rw [mem_rootsOfUnity]
    exact hev.neg_one_pow
  have hneg : ∀ w ∈ WW l, -w ∈ WW l := fun w hw => by
    have := (WW l).mul_mem hm1 hw
    simpa using this
  letI : LinearOrder ℤ_[l]ˣ := linearOrderOfSTO WellOrderingRel
  let R : Finset ℤ_[l]ˣ := hfin.toFinset.filter fun r => r < -r
  have hR : ∀ r, r ∈ R ↔ r ∈ WW l ∧ r < -r := fun r => by simp [R]
  have h4 : ∀ r ∈ R, -r ∉ R := fun r hr hr' => by
    have h1 := ((hR _).1 hr).2
    have h2 := ((hR _).1 hr').2
    rw [neg_neg] at h2
    exact lt_asymm h1 h2
  have h5 : ∀ w ∈ WW l, w ∈ R ∨ -w ∈ R := fun w hw => by
    rcases lt_or_gt_of_ne (neg_ne l w) with h | h
    · exact Or.inl ((hR _).2 ⟨hw, h⟩)
    · exact Or.inr ((hR _).2 ⟨hneg w hw, by rwa [neg_neg]⟩)
  refine ⟨R, ?_, fun r hr => ((hR r).1 hr).1, ?_, h4, h5, hm1, ?_⟩
  · rcases h5 1 (WW l).one_mem with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  · intro r hr r' hr' hne a b hab
    by_contra ha
    have e1 : (r : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr).1
    have e2 : (r' : ℤ_[l]) ^ Nat.totient (l ^ ee l) = 1 :=
      (mem_rootsOfUnity' _ _).1 ((hR _).1 hr').1
    have e3 := congrArg (· ^ Nat.totient (l ^ ee l)) hab
    simp only [mul_pow, e1, e2, mul_one] at e3
    have e4 : a ^ Nat.totient (l ^ ee l) = b ^ Nat.totient (l ^ ee l) := by exact_mod_cast e3
    have ha' : (a : ℤ_[l]) ≠ 0 := by exact_mod_cast ha
    rcases (pow_eq_pow_iff_of_ne_zero hpos.ne').1 e4 with h | ⟨h, -⟩
    · subst h
      exact hne (Units.ext (mul_left_cancel₀ ha' hab))
    · have hb : (b : ℤ_[l]) = -(a : ℤ_[l]) := by rw [h]; simp
      rw [hb, neg_mul, ← mul_neg] at hab
      have : r = -r' := Units.ext (by simpa using mul_left_cancel₀ ha' hab)
      exact h4 r' hr' (this ▸ hr)
  · intro n hn w hw h1
    have hle : ee l ≤ n := by
      unfold ee; split_ifs <;> omega
    have h2 : PadicInt.toZModPow n (w : ℤ_[l]) = 1 := by
      have := congrArg Units.val h1
      simpa [redU] using this
    have h3 : PadicInt.toZModPow (ee l) (w : ℤ_[l]) = 1 := by
      rw [← PadicInt.zmod_cast_comp_toZModPow (ee l) n hle, RingHom.comp_apply, h2, map_one]
    have h4 : ((redU l (ee l)).comp (WW l).subtype) ⟨w, hw⟩ = ((redU l (ee l)).comp (WW l).subtype) 1 := by
      rw [map_one]
      apply Units.ext
      simpa [redU] using h3
    exact congrArg Subtype.val ((teich l).1 h4)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcShift
section
open UpperTheory.V.FW

private theorem gauss_count_shift_eq_sum (M c : ℕ) [NeZero M] (s : ZMod M) (hc : c.Coprime M) (n : ℕ) :
    gc M c s - gc M c (s - ((c * n : ℕ) : ZMod M)) =
      ∑ j ∈ Finset.range (c * n), if (j : ZMod M) = s then (1 - if c ∣ j then (c : ℤ) else 0) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc
    have e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c := by
      push_cast; ring
    rw [e, Nat.mul_succ, Finset.sum_range_add, ← ih]
    have key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then
        (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) =
        (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) -
          if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp
      have h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) =
          ∑ j ∈ Finset.range c, if j = 0 then
            (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range c) 0]
        simp [hpos]
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) := by
        rw [Nat.cast_add, eq_sub_iff_add_eq']
      have h4 : c ∣ c * n + j ↔ j = 0 := by
        rw [Nat.dvd_add_right (dvd_mul_right c n)]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩
      simp only [h3, h4]
      generalize s - ((c * n : ℕ) : ZMod M) = t
      by_cases h0 : j = 0
      · subst h0
        by_cases ht : t = 0
        · simp [ht]
        · simp [ht, Ne.symm ht]
      · simp [h0]
    rw [key, ← h]
    ring

theorem UpperTheory.V.FW.gcShift :
    ∀ (M c F : ℕ) [NeZero M] (k : Type) [CommRing k] (Ψ : ZMod M → k) (s : ZMod M), c.Coprime M → (∀ x, Ψ (x + F) = Ψ x) → (gc M c s : k) * Ψ s - (gc M c (s - ((c * F : ℕ) : ZMod M)) : k) * Ψ (s - ((c * F : ℕ) : ZMod M)) = ∑ j ∈ Finset.range (c * F), if (j : ZMod M) = s then Ψ j * (1 - if c ∣ j then (c : k) else 0) else 0 := by
  intro M c F _ k _ Ψ s hc hΨ
  have hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]
      congr 1
      push_cast; ring
  rw [hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod M) = s
  · rw [if_pos h, if_pos h, h, mul_comm]
    by_cases h' : c ∣ j <;> simp [h']
  · simp [h]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
section
open UpperTheory.V.FW

private theorem coeff_thetaH (M c : ℕ) [NeZero M] (s : (ZMod M)ˣ) :
    (thetaH M c).coeff s = if 2 * (s : ZMod M).val < M then gc M c s else 0 := by
  classical
  simp [thetaH, Finsupp.single_apply, Finset.sum_ite_eq']

private theorem coeff_mul_J (M : ℕ) [NeZero M] (f : MonoidAlgebra ℤ (ZMod M)ˣ) (s : (ZMod M)ˣ) :
    (f * MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)).coeff s = f.coeff (-s) := by
  rw [show MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ) = MonoidAlgebra.single (-1) 1 from rfl]
  rw [MonoidAlgebra.coeff_mul_single_eq_coeff_mul (-s), mul_one]
  intro m _
  rw [mul_neg_one, neg_eq_iff_eq_neg]

private theorem half (M : ℕ) [NeZero M] (hM : 2 < M) (s : (ZMod M)ˣ) :
    (s : ZMod M) ≠ 0 ∧ (2 * (-(s : ZMod M)).val < M ↔ ¬ 2 * (s : ZMod M).val < M) := by
  have hs0 : (s : ZMod M) ≠ 0 := by
    haveI : Fact (1 < M) := ⟨by omega⟩
    exact s.ne_zero
  refine ⟨hs0, ?_⟩
  rw [ZMod.neg_val, if_neg hs0]
  have hlt := ZMod.val_lt (s : ZMod M)
  have hne : 2 * (s : ZMod M).val ≠ M := by
    intro h
    have h2 : (2 : ZMod M) * (s : ZMod M) = 0 := by
      have : ((2 * (s : ZMod M).val : ℕ) : ZMod M) = 0 := by
        rw [h]
        exact ZMod.natCast_self M
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    have h3 : (2 : ZMod M) = 0 := by
      have := congrArg (· * ((s⁻¹ : (ZMod M)ˣ) : ZMod M)) h2
      simpa [mul_assoc] using this
    have h4 : ((2 : ℕ) : ZMod M) = 0 := by exact_mod_cast h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  omega

theorem UpperTheory.V.FW.thetaFull :
    ∀ (M c : ℕ) [NeZero M], c.Coprime M → Odd c → 2 < M → thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ)) = ∑ s : (ZMod M)ˣ, MonoidAlgebra.single s (gc M c s) ∧ ∀ s : (ZMod M)ˣ, (((thetaH M c * (1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))).coeff s : ℤ) : ZMod 2) = (gc M c s : ZMod 2) := by
  intro M c _ hc hodd hM
  have key : ∀ s : (ZMod M)ˣ, (thetaH M c).coeff (-s) = if 2 * (s : ZMod M).val < M then 0 else -gc M c s := by
    intro s
    obtain ⟨hs0, hiff⟩ := half M hM s
    rw [coeff_thetaH, Units.val_neg]
    by_cases h : 2 * (s : ZMod M).val < M
    · rw [if_neg (fun h' => hiff.mp h' h), if_pos h]
    · rw [if_pos (hiff.mpr h), if_neg h, gcNeg M c _ hc hodd hs0]
  constructor
  · rw [mul_sub, mul_one, sub_eq_iff_eq_add]
    refine MonoidAlgebra.ext (Finsupp.ext fun s => ?_)
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    classical
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs <;> simp
  · intro s
    rw [mul_add, mul_one, MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mul_J, key, coeff_thetaH]
    split_ifs
    · simp
    · push_cast
      simp [ZMod.neg_eq_self_mod_two]
end

