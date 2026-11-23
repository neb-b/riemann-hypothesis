module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GenFlag
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem UpperTheory.V.Ws.Pp.gf_adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev] <;> ring

private theorem UpperTheory.V.Ws.Pp.gf_adj_one {R : Type} [CommRing R] : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem UpperTheory.V.Ws.Pp.gf_conj {R : Type} [CommRing R] {ν : R} {X : M4 R} (h : IsGSp ν X) (u v : M4 R)
    (hv : v * u = 1) : adj (u * X * v) * (adj v * v) * (u * X * v) = ν • (adj v * v) := by
  have h1 : adj u * adj v = 1 := by
    rw [← gf_adj_mul, hv, gf_adj_one]
  unfold IsGSp at h
  rw [gf_adj_mul, gf_adj_mul]
  calc _ = adj v * (adj X * (adj u * adj v) * (v * u) * X) * v := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, hv, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private theorem UpperTheory.V.Ws.Pp.gf_gram {K : Type} [Field K] {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0)
    (h : adj M * A * M = ν • A)
    (hc : ∀ i j : Fin 4, j < i → M i.rev i.rev * M j j ≠ ν) : ∀ i j, j < i → A i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m30 := hM 3 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have m31 := hM 3 1 (by decide)
  have m32 := hM 3 2 (by decide)
  have k : ∀ {a b x : K}, a ≠ b → a * x = b * x → x = 0 := fun hab hx => by
    by_contra h0
    exact hab (mul_right_cancel₀ h0 hx)
  have e30 := e 3 0
  have e20 := e 2 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e21 := e 2 1
  have e32 := e 3 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, m10, m20, m30, m21, m31, m32] at e30 e20 e10 e31 e21 e32
  have a30 : A 3 0 = 0 := k (hc 3 0 (by decide)) (by show M 0 0 * M 0 0 * _ = _; linear_combination e30)
  rw [a30] at e20 e10 e31 e21 e32
  have a20 : A 2 0 = 0 := k (hc 2 0 (by decide)) (by show M 1 1 * M 0 0 * _ = _; linear_combination e20)
  have a31 : A 3 1 = 0 := k (hc 3 1 (by decide)) (by show M 0 0 * M 1 1 * _ = _; linear_combination e31)
  simp only [a20, a31] at e10 e21 e32
  have a10 : A 1 0 = 0 := k (hc 1 0 (by decide)) (by show M 2 2 * M 0 0 * _ = _; linear_combination e10)
  have a21 : A 2 1 = 0 := k (hc 2 1 (by decide)) (by show M 1 1 * M 1 1 * _ = _; linear_combination e21)
  have a32 : A 3 2 = 0 := k (hc 3 2 (by decide)) (by show M 0 0 * M 2 2 * _ = _; linear_combination e32)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem UpperTheory.V.Ws.Pp.genFlag :
    ∀ {H K : Type} [Group H] [Field K] (I : Subgroup H) (ps : Fin 4 → H → K) (s₀ : H) (ν : K) (r : H →* M4 K), s₀ ∈ I → Function.Injective (fun i => ps i s₀) → (∀ i, ps i s₀ * ps i.rev s₀ = ν) → ν ≠ 0 → IsGSp ν (r s₀) → Ord I ps s₀ r → ∃ h : M4 K, IsGSp 1 h ∧ (∀ g, IsUp (adj h * r g * h)) ∧ (∀ s ∈ I, ∀ i, (adj h * r s * h) i i = ps i s) ∧ ∀ i g, (∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)) * (adj h * r g * h) i i = (prj (fun a => ps a s₀) (r s₀) i * r g).trace := by
  intro H K _ _ I ps s₀ ν r hs hinj hrev hν hg ho
  obtain ⟨u, κ, h1, h2, h3, h4⟩ := ordFlag I K ps s₀ r hinj ho
  have hA := gf_gram (h1 s₀) (gf_conj hg _ _ u.inv_mul) fun i j hij e => by
    rw [h2, h2, h3 _ _ hs, h3 _ _ hs, ← hrev i, mul_comm (ps i s₀)] at e
    have h0 : ps i.rev s₀ ≠ 0 := fun h => hν (by rw [← hrev i, h, mul_zero])
    exact hij.ne (hinj (mul_left_cancel₀ h0 e))
  obtain ⟨t, ht, hh⟩ := gram u⁻¹ hA
  have hadj : adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) = ((t⁻¹ : (M4 K)ˣ) : M4 K) * (u : M4 K) := by
    have e := adj_mul_self hh
    rw [← mul_assoc, Units.mul_eq_one_iff_eq_inv, Units.mul_inv_eq_iff_eq_mul] at e
    exact e
  have key : ∀ g, adj (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K)) * r g * (((u⁻¹ : (M4 K)ˣ) : M4 K) * (t : M4 K))
      = ((t⁻¹ : (M4 K)ˣ) : M4 K) * ((u : M4 K) * r g * ((u⁻¹ : (M4 K)ˣ) : M4 K)) * (t : M4 K) := fun g => by
    rw [hadj]
    simp only [mul_assoc]
  have up := fun g => upConj t.inv_mul (IsUp_inv ht) ht (h1 g)
  refine ⟨_, hh, fun g => ?_, fun s hs i => ?_, fun i g => ?_⟩
  · rw [key]
    exact (up g).1
  · rw [key, (up s).2, h2, h3 i s hs]
  · rw [key, (up g).2, h2, h4]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.NearPoly
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem nearPoly_local (B S : Type) [CommRing B] [HenselianLocalRing B] [CommRing S] [IsDomain S]
    [Algebra B S] [Module.Finite B S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian B q
  refine .of_unique_max_ideal ⟨q, hq, fun n hn => (H n hn).1 ?_⟩
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · rw [h]
    exact (Ideal.ne_top_iff_one _).1 hn.ne_top

theorem UpperTheory.V.Ws.Pp.nearPoly :
    ∀ {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [HenselianLocalRing B] [Algebra O B] (x : B →ₐ[O] O) (d : O) (t : B) (v : FractionRing B), d ≠ 0 → x t = 0 → IsIntegral B v → algebraMap B (FractionRing B) (algebraMap O B d) * v = algebraMap B (FractionRing B) t → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro O B _ _ _ _ _ _ x d t v hd ht hv h
  let S := Algebra.adjoin B ({v} : Set (FractionRing B))
  haveI : Module.Finite B S := Module.Finite.iff_fg.2 hv.fg_adjoin_singleton
  haveI : IsLocalRing S := nearPoly_local B S
  let w : S := ⟨v, Algebra.self_mem_adjoin_singleton B v⟩
  have hw : w ∈ maximalIdeal S := by
    intro hu
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have h1 : algebraMap B S (algebraMap O B d) * w = algebraMap B S t := Subtype.ext h
    have h2 : algebraMap B S (algebraMap O B d) = algebraMap B S t * u := by
      rw [← h1, mul_assoc, hu, mul_one]
    haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
    have hinj : Function.Injective (algebraMap B S) := fun a b e =>
      IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val e)
    obtain ⟨Q, _, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) (RingHom.ker x)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
    have h3 : t ∈ Q.comap (algebraMap B S) := by
      change t ∈ Ideal.under B Q
      rw [hQ]
      exact ht
    have h4 : algebraMap O B d ∈ Q.comap (algebraMap B S) := by
      rw [Ideal.mem_comap, h2]
      exact Q.mul_mem_right _ h3
    change algebraMap O B d ∈ Ideal.under B Q at h4
    rw [hQ, RingHom.mem_ker, x.commutes] at h4
    exact hd h4
  obtain ⟨p, hp, h0⟩ := nilPoly (B := B) w hw
  refine ⟨p, hp, ?_⟩
  have := aeval_algHom_apply S.val w p
  rw [h0, map_zero] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.SpIwa
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.spIwa :
    ∀ {F : Type} [Field F] (V : ValuationSubring F) (h : M4 F), IsGSp 1 h → ∃ k : M4 V, IsGSp 1 k ∧ IsUp (adj (k.map V.subtype) * h) := by
  intro F _ V h hh
  let f : V →+* F := V.subtype
  let hU : GL (Fin 4) F := ⟨h, adj h, mul_adj_self hh, adj_mul_self hh⟩
  obtain ⟨k0, b, hb, hk⟩ := GlobalTheory.ValIwasawa.iwasawa V F 4 hU
  have hbU : IsUp (b : M4 F) := (isUp_iff _).mpr hb
  have hbi : IsUp ((b⁻¹ : GL (Fin 4) F) : M4 F) := IsUp_inv hbU
  have hKmap : (k0 : M4 V).map f = h * ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    have h1 : (hU : M4 F) =
        ((Matrix.GeneralLinearGroup.map (algebraMap V F) k0 : GL (Fin 4) F) : M4 F) * (b : M4 F) := by
      rw [hk]
      rfl
    have h2 : (hU : M4 F) = h := rfl
    rw [h2] at h1
    rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rfl
  have hadjh : adj (h * ((b⁻¹ : GL (Fin 4) F) : M4 F)) * h = adj ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    rw [(grp F).1, Matrix.mul_assoc, adj_mul_self hh, Matrix.mul_one]
  have hmapadj : ∀ X : M4 V, adj (X.map f) = (adj X).map f := fun X => (grp V).2.2.2.2.2.1 F f X
  have upMap : ∀ X : M4 V, IsUp (X.map f) → IsUp X := by
    intro X hX i j hij
    have hz := hX i j hij
    simpa [f] using hz
  have hQ : IsUp (adj (k0 : M4 V) * (k0 : M4 V)) := by
    apply upMap
    rw [Matrix.map_mul, ← hmapadj, hKmap, (grp F).1, Matrix.mul_assoc,
      ← Matrix.mul_assoc (adj h), adj_mul_self hh, Matrix.one_mul]
    exact IsUp_mul (IsUp_adj hbi) hbi
  obtain ⟨t, ht, hkt⟩ := gram k0 hQ
  refine ⟨(k0 : M4 V) * (t : M4 V), hkt, ?_⟩
  have htU : IsUp ((t : M4 V).map f) := by
    intro i j hij
    simp [ht i j hij]
  rw [Matrix.map_mul, (grp F).1, hKmap, Matrix.mul_assoc, hadjh]
  exact IsUp_mul (IsUp_adj htU) (IsUp_adj hbi)
end

