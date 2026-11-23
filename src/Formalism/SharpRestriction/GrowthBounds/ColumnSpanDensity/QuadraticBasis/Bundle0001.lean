module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.StatementO

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.PresIso
section
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

section
variable {W O : Type} [CommRing W] [CommRing O]

def pbE (j : W →+* O) (θ w : O) (t : W × W × W × W) : O :=
  j t.1 + j t.2.1 * θ + j t.2.2.1 * w + j t.2.2.2 * θ * w

def pbM (f0 f1 ϖ : W) (t s : W × W × W × W) : W × W × W × W :=
  (t.1 * s.1 - t.2.1 * s.2.1 * f0 + ϖ * (t.2.2.1 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f0),
   t.1 * s.2.1 + t.2.1 * s.1 - t.2.1 * s.2.1 * f1
     + ϖ * (t.2.2.1 * s.2.2.2 + t.2.2.2 * s.2.2.1 - t.2.2.2 * s.2.2.2 * f1),
   t.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f0 + t.2.2.1 * s.1 - t.2.2.2 * s.2.1 * f0,
   t.1 * s.2.2.2 + t.2.1 * s.2.2.1 - t.2.1 * s.2.2.2 * f1 + t.2.2.1 * s.2.1 + t.2.2.2 * s.1
     - t.2.2.2 * s.2.1 * f1)

theorem pbE_mul (j : W →+* O) (θ w : O) (f0 f1 ϖ : W) (hθ : θ ^ 2 + j f1 * θ + j f0 = 0)
    (hw : w ^ 2 = j ϖ) (t s : W × W × W × W) :
    pbE j θ w t * pbE j θ w s = pbE j θ w (pbM f0 f1 ϖ t s) := by
  simp only [pbE, pbM, map_add (f := _), map_sub, map_mul]
  linear_combination (j t.2.2.1 * j s.2.2.1 + (j t.2.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.2.1) * θ +
      j t.2.2.2 * j s.2.2.2 * θ ^ 2) * hw +
    (j t.2.1 * j s.2.1 + (j t.2.1 * j s.2.2.2 + j t.2.2.2 * j s.2.1) * w +
      j t.2.2.2 * j s.2.2.2 * j ϖ) * hθ

theorem pbE_add (j : W →+* O) (θ w : O) (t s : W × W × W × W) :
    pbE j θ w t + pbE j θ w s = pbE j θ w (t + s) := by
  simp only [pbE, Prod.fst_add, Prod.snd_add, map_add (f := _)]
  ring

theorem pbE_bij {j : W →+* O} {θ w : O} (h : IsQuadBasis j θ w) : Function.Bijective (pbE j θ w) := by
  constructor
  · intro t s hts
    obtain ⟨u, -, hu⟩ := h (pbE j θ w t)
    exact (hu t rfl).trans (hu s hts).symm
  · intro x
    obtain ⟨t, ht, -⟩ := h x
    exact ⟨t, ht.symm⟩

end

def pbF {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂) (t : W₁ × W₁ × W₁ × W₁) :
    W₂ × W₂ × W₂ × W₂ :=
  (φ t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2)

private theorem pbF_pbM_eq_pbM_map {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (f0 f1 ϖ : W₁) (t s : W₁ × W₁ × W₁ × W₁) :
    pbF φ (pbM f0 f1 ϖ t s) = pbM (φ f0) (φ f1) (φ ϖ) (pbF φ t) (pbF φ s) := by
  simp [pbF, pbM]

private theorem pbF_add {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (t s : W₁ × W₁ × W₁ × W₁) : pbF φ (t + s) = pbF φ t + pbF φ s := by
  simp [pbF]

theorem presentationIso_holds : PresIso := by
  intro W₁ W₂ O₁ O₂ _ _ _ _ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 ϖ φW hθ₁ hθ₂ hw₁ hw₂ hB₁ hB₂
  let e₁ : (W₁ × W₁ × W₁ × W₁) ≃ O₁ := Equiv.ofBijective _ (pbE_bij hB₁)
  let e₂ : (W₂ × W₂ × W₂ × W₂) ≃ O₂ := Equiv.ofBijective _ (pbE_bij hB₂)
  let eF : (W₁ × W₁ × W₁ × W₁) ≃ (W₂ × W₂ × W₂ × W₂) :=
    { toFun := pbF φW
      invFun := pbF φW.symm
      left_inv := fun t => by simp [pbF]
      right_inv := fun t => by simp [pbF] }
  let E : O₁ ≃ O₂ := (e₁.symm.trans eF).trans e₂
  have hE : ∀ t, E (pbE j₁ θ₁ w₁ t) = pbE j₂ θ₂ w₂ (pbF φW t) := by
    intro t
    have h1 : e₁.symm (pbE j₁ θ₁ w₁ t) = t := e₁.symm_apply_apply t
    simp only [E, Equiv.trans_apply, h1]
    rfl
  have hsurj : ∀ x : O₁, ∃ t, x = pbE j₁ θ₁ w₁ t :=
    fun x => ⟨e₁.symm x, (e₁.apply_symm_apply x).symm⟩
  refine ⟨{ E with
    map_mul' := ?_
    map_add' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ * E _
    rw [pbE_mul j₁ θ₁ w₁ f0 f1 ϖ hθ₁ hw₁, hE, hE, hE, pbF_pbM_eq_pbM_map,
      pbE_mul j₂ θ₂ w₂ (φW f0) (φW f1) (φW ϖ) hθ₂ hw₂]
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ + E _
    rw [pbE_add, hE, hE, hE, pbF_add, pbE_add]
  · intro x
    have h1 := hE (x, 0, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (x, 0, 0, 0) = j₁ x by simp [pbE]] at h1
    show E (j₁ x) = j₂ (φW x)
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 0, 1, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 0, 1, 0) = w₁ by simp [pbE]] at h1
    show E w₁ = w₂
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 1, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 1, 0, 0) = θ₁ by simp [pbE]] at h1
    show E θ₁ = θ₂
    rw [h1]
    simp [pbE, pbF]

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.QuadBasis
section
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

section
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]

theorem qb_unit_of_not_dvd {p : ℕ} (hpW : Irreducible (p : W)) {b : W} (hb : ¬ (p : W) ∣ b) :
    IsUnit b := by
  by_contra h
  have h1 : b ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal b).2 h
  rw [hpW.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
  exact hb h1

theorem qb_I {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b : W} (h : w ∣ j a + j b * θ) :
    (p : W) ∣ a ∧ (p : W) ∣ b := by
  have hb : (p : W) ∣ b := by
    by_contra hb
    obtain ⟨u, rfl⟩ := qb_unit_of_not_dvd hpW hb
    apply hθ (-(↑u⁻¹ * a))
    have h0 := Dvd.dvd.mul_left h (j ↑u⁻¹)
    have e : j ↑u⁻¹ * (j a + j ↑u * θ) = θ - j (-(↑u⁻¹ * a)) := by
      have h1 : j ↑u⁻¹ * j ↑u = 1 := by rw [← map_mul]; simp
      rw [map_neg, map_mul]
      linear_combination θ * h1
    rwa [e] at h0
  refine ⟨?_, hb⟩
  by_contra ha
  have hu := (qb_unit_of_not_dvd hpW ha).map j
  obtain ⟨b', rfl⟩ := hb
  have h2 : w ∣ j ((p : W) * b') * θ := by
    rw [map_mul, map_natCast, ← hw2]
    exact ⟨w * j b' * θ, by ring⟩
  have h3 : w ∣ j a := (dvd_add_left h2).1 h
  exact hw.not_isUnit (isUnit_of_dvd_unit h3 hu)

theorem qb_S {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hw2 : w ^ 2 = (p : O)) (hw : Irreducible w)
    (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n')) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ (a b : W) (x' : O), x = j a + j b * θ + w * x' := by
  have hle : Ideal.span {(p : W)} ≤ Ideal.comap j (Ideal.span {w}) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hw2, Ideal.mem_span_singleton]
    exact dvd_pow_self w two_ne_zero
  let ι := Ideal.quotientMap (Ideal.span {w}) j hle
  let g : (W ⧸ Ideal.span {(p : W)}) × (W ⧸ Ideal.span {(p : W)}) → O ⧸ Ideal.span {w} :=
    fun t => ι t.1 + ι t.2 * Ideal.Quotient.mk _ θ
  have hg : ∀ a b : W, g (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b)
      = Ideal.Quotient.mk _ (j a + j b * θ) := by
    intro a b
    simp only [g, ι, Ideal.quotientMap_mk, map_add (f := _), map_mul]
  have hinj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hg, hg, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h2 : w ∣ j (a - a') + j (b - b') * θ := by
      have e : j (a - a') + j (b - b') * θ = j a + j b * θ - (j a' + j b' * θ) := by
        simp only [map_sub]; ring
      rwa [e]
    obtain ⟨h3, h4⟩ := qb_I j w θ hpW hw2 hw hθ h2
    have k3 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) a = Ideal.Quotient.mk _ a' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h3)
    have k4 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) b = Ideal.Quotient.mk _ b' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h4)
    rw [k3, k4]
  haveI : Finite (O ⧸ Ideal.span {w}) :=
    Nat.finite_of_card_ne_zero (by rw [cO]; exact (pow_pos hp.pos _).ne')
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, cW, cO, two_mul, pow_add])
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [hg, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hab
  obtain ⟨x', hx'⟩ := hab
  exact ⟨a, b, x', by linear_combination hx'⟩

theorem qb_step {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) :
    ∃ a' b' c' d' : W, a = p * a' ∧ b = p * b' ∧ c = p * c' ∧ d = p * d' ∧
      j a' + j b' * θ + j c' * w + j d' * θ * w = 0 := by
  have hw0 : w ≠ 0 := hw.ne_zero
  have h1 : w ∣ j a + j b * θ := ⟨-(j c + j d * θ), by linear_combination h⟩
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h1
  simp only [map_mul, map_natCast, ← hw2] at h
  have h2 : w * (w * (j a' + j b' * θ) + (j c + j d * θ)) = 0 := by linear_combination h
  have h3 := (mul_eq_zero.1 h2).resolve_left hw0
  have h4 : w ∣ j c + j d * θ := ⟨-(j a' + j b' * θ), by linear_combination h3⟩
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := qb_I j w θ hpW hw2 hw hθ h4
  simp only [map_mul, map_natCast, ← hw2] at h3
  refine ⟨a', b', c', d', rfl, rfl, rfl, rfl, ?_⟩
  have h5 : w * (j a' + j b' * θ + j c' * w + j d' * θ * w) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h5).resolve_left hw0

theorem qb_pow {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (m : ℕ) : ∀ {a b c d : W},
    j a + j b * θ + j c * w + j d * θ * w = 0 →
    (p : W) ^ m ∣ a ∧ (p : W) ^ m ∣ b ∧ (p : W) ^ m ∣ c ∧ (p : W) ^ m ∣ d := by
  induction m with
  | zero => intro a b c d _; simp
  | succ m ih =>
    intro a b c d h
    obtain ⟨a', b', c', d', rfl, rfl, rfl, rfl, h'⟩ := qb_step j w θ hpW hw2 hw hθ h
    obtain ⟨ha, hb, hc, hd⟩ := ih h'
    simp only [pow_succ']
    exact ⟨mul_dvd_mul_left _ ha, mul_dvd_mul_left _ hb, mul_dvd_mul_left _ hc, mul_dvd_mul_left _ hd⟩

theorem qb_zero_of_pow {p : ℕ} (hpW : Irreducible (p : W)) {a : W} (h : ∀ m, (p : W) ^ m ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpW.not_isUnit ha
  exact hn (h _)

theorem qb_indep {p : ℕ} (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W)) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (hθ : ∀ a : W, ¬ w ∣ θ - j a) {a b c d : W}
    (h : j a + j b * θ + j c * w + j d * θ * w = 0) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.1,
   qb_zero_of_pow hpW fun m => (qb_pow j w θ hpW hw2 hw hθ m h).2.2.2⟩

theorem qb_span {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hfin : j.Finite) (hw2 : w ^ 2 = (p : O))
    (hw : Irreducible w) (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n'))
    (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ a b c d : W, x = j a + j b * θ + j c * w + j d * θ * w := by
  letI : Algebra W O := j.toAlgebra
  haveI : Module.Finite W O := hfin
  have hsm : ∀ (r : W) (y : O), r • y = j r * y := fun r y => Algebra.smul_def r y
  let M : Submodule W O :=
    { carrier := {y | ∃ a b c d : W, y = j a + j b * θ + j c * w + j d * θ * w}
      add_mem' := by
        rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
        exact ⟨a + a', b + b', c + c', d + d', by simp only [map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, 0, 0, 0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨a, b, c, d, rfl⟩
        exact ⟨r * a, r * b, r * c, r * d, by rw [hsm]; simp only [map_mul]; ring⟩ }
  have hJ : Ideal.span {(p : W)} ≤ Ideal.jacobson (⊥ : Ideal W) := by
    rw [← hpW.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  have hle : (⊤ : Submodule W O) ≤ M ⊔ Ideal.span {(p : W)} • (⊤ : Submodule W O) := by
    intro y _
    obtain ⟨a, b, y', hy⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y
    obtain ⟨c, d, y'', hy'⟩ := qb_S hp j w θ hpW cW hw2 hw cO hθ y'
    refine Submodule.mem_sup.2 ⟨j a + j b * θ + j c * w + j d * θ * w, ⟨a, b, c, d, rfl⟩,
      (p : W) • y'', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top, ?_⟩
    rw [hsm, map_natCast, ← hw2, hy, hy']
    ring
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ hle
  exact htop (Submodule.mem_top : x ∈ ⊤)

end

theorem basisCriterion_holds : QuadBasis := by
  intro p n' hp W O _ _ _ _ _ _ j w θ hpW cW hfin hw2 hw cO hθ x
  obtain ⟨a, b, c, d, hx⟩ := qb_span hp j w θ hpW cW hfin hw2 hw cO hθ x
  refine ⟨(a, b, c, d), hx, ?_⟩
  rintro ⟨a', b', c', d'⟩ hx'
  simp only at hx'
  have h : j (a' - a) + j (b' - b) * θ + j (c' - c) * w + j (d' - d) * θ * w = 0 := by
    simp only [map_sub]
    linear_combination hx - hx'
  obtain ⟨h1, h2, h3, h4⟩ := qb_indep j w θ hpW hw2 hw hθ h
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3, sub_eq_zero.1 h4]

end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end

