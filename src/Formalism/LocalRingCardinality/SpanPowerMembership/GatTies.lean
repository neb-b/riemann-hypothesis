module

public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LevelValuationRings

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField QuadraticAlgebra

section Orbit

variable {G : Type} [Group G] [Finite G] (g : G)

abbrev Quo : Type := G ⧸ Subgroup.zpowers g

def eQuo : Fin (Nat.card (Quo g)) ≃ Quo g := (Finite.equivFin (Quo g)).symm


open Classical in
def secOf (T : Set G) (q : Quo g) : G :=
  if h : ∃ x ∈ T, (QuotientGroup.mk x : Quo g) = q then h.choose else q.out

theorem mk_secOf (T : Set G) (q : Quo g) : (QuotientGroup.mk (secOf g T q) : Quo g) = q := by
  unfold secOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact QuotientGroup.out_eq' q

def orbFun (T : Set G) (x : Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) : G :=
  secOf g T (eQuo g x.1) * g ^ (x.2 : ℕ)

theorem orbFun_bij (T : Set G) : Function.Bijective (orbFun g T) := by
  have key : ∀ (q : Quo g) (n : ℕ), (QuotientGroup.mk (secOf g T q * g ^ n) : Quo g) = q := by
    intro q n
    have h1 : (QuotientGroup.mk (secOf g T q) : Quo g) = QuotientGroup.mk (secOf g T q * g ^ n) := by
      rw [QuotientGroup.eq, inv_mul_cancel_left]
      exact Subgroup.npow_mem_zpowers g n
    rw [← h1, mk_secOf]
  have hinj : Function.Injective (orbFun g T) := by
    rintro ⟨v1, s1⟩ ⟨v2, s2⟩ h
    simp only [orbFun] at h
    have hv : v1 = v2 := by
      have h3 := congrArg (fun y => (QuotientGroup.mk y : Quo g)) h
      simp only [key] at h3
      exact (eQuo g).injective h3
    subst hv
    have hs : g ^ (s1 : ℕ) = g ^ (s2 : ℕ) := mul_left_cancel h
    have h4 : (s1 : ℕ) = s2 := pow_injOn_Iio_orderOf s1.2 s2.2 hs
    rw [Fin.ext h4]
  refine hinj.bijective_of_nat_card_le ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers g), Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)), Fintype.card_sigma]
  simp

def orbEquiv (T : Set G) : (Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) ≃ G :=
  Equiv.ofBijective (orbFun g T) (orbFun_bij g T)

theorem orbEquiv_step (T : Set G) (v : Fin (Nat.card (Quo g))) (s : Fin (orderOf g)) :
    orbEquiv g T ⟨v, posAdd s 1⟩ = orbEquiv g T ⟨v, s⟩ * g := by
  show orbFun g T ⟨v, posAdd s 1⟩ = orbFun g T ⟨v, s⟩ * g
  simp only [orbFun, posAdd, pow_mod_orderOf, pow_succ, mul_assoc]

end Orbit

variable {R : Ranks} (H : Host R) (p : ℕ)

theorem of_cls (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧
    jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold Host.cls primeClass at h
  by_cases h1 : p ∈ H.small
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : p = H.q
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : p = H.d
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : jacobiSym (-(H.d : ℤ)) p = 1
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  by_cases h5 : H.psAt p = 1
  · rw [if_pos h5] at h
    cases h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem coprime_of_cls (hp : p.Prime) (hc : H.cls p = .inertClass) : p.Coprime H.condN := by
  obtain ⟨h2, hq, hd, -, -⟩ := of_cls H p hc
  have h1 : ¬ p ∣ H.QS := fun h => h2 (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.2 h1)
    ((Nat.coprime_primes hp H.hyp.1).2 hq)) ((Nat.coprime_primes hp H.hyp.2.1).2 hd)

def hOf : R.MA :=
  if h : p.Coprime H.condN then (H.art (ZMod.unitOfCoprime p h)).2 else 1

theorem hOf_of_coprime (h : p.Coprime H.condN) : hOf H p = (H.art (ZMod.unitOfCoprime p h)).2 := by
  rw [hOf, dite_eq_left h]

theorem unit_eq_neg_one (x : ℤˣ) (h : (x : ℤ) ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · rw [hx] at h
    exact absurd rfl h
  · exact hx

theorem frob_val (hp : p.Prime) (hc : H.cls p = .inertClass) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.galE σ = (c0, hOf H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  obtain ⟨h2, hq, hd, hjd, hjq⟩ := of_cls H p hc
  obtain ⟨-, hiff, hval, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  obtain ⟨h1, h3, -⟩ := hval σ hσ
  have h4 := (hiff σ (ZMod.unitOfCoprime p hco) (ZMod.coe_unitOfCoprime p hco)).1 hσ
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact unit_eq_neg_one _ (by rw [h1]; exact hjq)
  · exact unit_eq_neg_one _ (by rw [h3]; exact hjd)
  · show (H.gal σ).2 = hOf H p
    rw [hOf_of_coprime H p hco, h4]

open Ideal in
theorem exists_frob (hp : p.Prime) (hc : H.cls p = .inertClass) :
    ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  exact ⟨P, hPp, hPl, σ, hσ⟩

theorem hOf_even (hp : p.Prime) (hc : H.cls p = .inertClass) (hn : HNeZero H p) :
    Even (orderOf (hOf H p)) := by
  obtain ⟨P, hP, hL, σ, hσ⟩ := exists_frob H p hp hc
  have h1 := @hn P hP hL σ hσ
  rwa [@frob_val R H p hp hc P hP hL σ hσ] at h1

def inPsi (φ : Formalism.HC.Frame) : φ.MA →* ↥φ.Psi :=
  (MonoidHom.inr G0 φ.MA).codRestrict φ.Psi (fun _ => rfl)

theorem inPsi_inj (φ : Formalism.HC.Frame) : Function.Injective (inPsi φ) := by
  intro a b h
  have h' := congrArg (fun x : ↥φ.Psi => (Subtype.val x).2) h
  exact h'

theorem order_spec (φ : Formalism.HC.Frame) (h : φ.MA) (h1 : Even (orderOf h)) :
    orderOf (inPsi φ h) = orderOf h ∧ 2 ≤ orderOf (inPsi φ h) ∧ Even (orderOf (inPsi φ h)) := by
  rw [orderOf_injective (inPsi φ) (inPsi_inj φ) h]
  refine ⟨rfl, ?_, h1⟩
  have hpos : 0 < orderOf h := orderOf_pos h
  obtain ⟨r, hr⟩ := h1
  omega

instance (φ : Formalism.HC.Frame) : Finite ↥φ.Psi := inferInstance

structure Served {R : Ranks} (H : Host R) (p : ℕ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  cls : H.cls p = .inertClass
  hne : HNeZero H p

variable {H p}

def gPsi (S : Served H p) : ↥(R.Psi) := inPsi R.toFrame (hOf H p)

abbrev nOrb (S : Served H p) : ℕ := Nat.card (Quo (gPsi S))

def posPsi (S : Served H p) (T : Set ↥(R.Psi)) :
    (Σ _ : Fin (nOrb S), Fin (orderOf (gPsi S))) ≃ ↥(R.Psi) := orbEquiv (gPsi S) T

theorem posPsi_step (S : Served H p) (T : Set ↥(R.Psi)) (v : Fin (nOrb S))
    (s : Fin (orderOf (gPsi S))) : posPsi S T ⟨v, posAdd s 1⟩ = posPsi S T ⟨v, s⟩ * gPsi S :=
  orbEquiv_step (gPsi S) T v s

theorem ord_spec (S : Served H p) :
    orderOf (gPsi S) = orderOf (hOf H p) ∧
      2 ≤ orderOf (gPsi S) ∧ Even (orderOf (gPsi S)) :=
  order_spec R.toFrame (hOf H p) (hOf_even H p S.prime S.cls S.hne)

theorem k_pos (R : Ranks) : R.k - 1 + 1 = R.k := by
  have := R.m_add_three_le_k
  omega

def placesOf (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0)) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    Places p (On p (orderOf (gPsi S))) (Kn p (orderOf (gPsi S))) :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  { w := ω
    nV := nOrb S
    n' := fun _ => orderOf (gPsi S)
    W := fun _ => Wn p (orderOf (gPsi S))
    Qq := fun _ => Qn p (orderOf (gPsi S))
    ι := fun _ => iotaN p _
    σ := fun _ => sigN p _
    j := fun _ => algebraMap _ _
    setting := fun _ => hidaSettingOfEven p _ S.five_le (ord_spec S).2.1 (ord_spec S).2.2
    m := R.k - 1
    r := r
    lam0 := fun v s i => (lam (posPsi S T ⟨v, s⟩)).w
      ⟨i.1, by have h1 := k_pos R; have h2 := i.2; simp only [Ranks.N]; omega⟩
    dom := fun v s a b hab => (lam (posPsi S T ⟨v, s⟩)).anti (show (_ : Fin _) ≤ _ from hab) }

theorem orderOf_frobenius_image_eq (S : Served H p) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    orderOf (gPsi S) = orderOf (H.galE σ).2 := by
  rw [(ord_spec S).1, @frob_val R H p S.prime S.cls P _ _ σ hσ]

theorem position_succ_eq_mul_frobenius (S : Served H p) (T : Set ↥(R.Psi)) {Tau : Type} (eTau : Tau ≃ ↥(R.Psi))
    (v : Fin (nOrb S)) (s : Fin (orderOf (gPsi S))) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    ((eTau (((posPsi S T).trans eTau.symm) ⟨v, posAdd s 1⟩) : R.Psi) : R.GG) =
      ((eTau (((posPsi S T).trans eTau.symm) ⟨v, s⟩) : R.Psi) : R.GG) *
        H.galE σ * R.cc := by
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    posPsi_step, Subgroup.coe_mul, mul_assoc, @frob_val R H p S.prime S.cls P _ _ σ hσ]
  congr 1
  simp [gPsi, inPsi, Formalism.HC.Frame.cc, Prod.ext_iff]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem served_of {T : ℕ} (h : GIdx H T p) : Served H p := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.BasicNotions.Examples₂.LevelValuationRings

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂
