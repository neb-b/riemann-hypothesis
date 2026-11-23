module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCard
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quot_pow_maximal_charP_local_card : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  intro L _ _ la J hmax l e b hl he hb hJ hspan
  have hn0 : e * b ≠ 0 := Nat.mul_ne_zero he.ne' hb.ne'
  set n := e * b with hn
  set q := Ideal.Quotient.mk (la ^ n) with hq
  have hlla : ((l : ℕ) : 𝓞 L) ∈ la := by
    have : ((l:ℕ) : 𝓞 L) ∈ la ^ e * J := by rw [← hspan]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.pow_le_self he.ne' : la ^ e ≤ la) ((Ideal.mul_le_left : la ^ e * J ≤ la ^ e) this)
  have hl0 : ((l : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hla0 : la ≠ ⊥ := fun h => hl0 (by rw [h] at hlla; simpa using hlla)
  have hlatop : la ≠ ⊤ := hmax.ne_top
  have hpowle : ∀ i j : ℕ, la ^ i ≤ la ^ j ↔ j ≤ i := fun i j =>
    ⟨fun h => by
      by_contra hc
      rw [not_le] at hc
      exact absurd h (Ideal.pow_right_strictAnti la hla0 hlatop hc).not_ge,
     fun h => Ideal.pow_le_pow_right h⟩
  have hle : la ^ n ≤ la := Ideal.pow_le_self hn0
  have hnil : ∀ c ∈ la, IsNilpotent (q c) := fun c hc =>
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hc n⟩
  have hunit : ∀ a : 𝓞 L, IsUnit (q a) ↔ a ∉ la := by
    intro a
    constructor
    · intro hu ha
      obtain ⟨d, hd⟩ := hu.exists_right_inv
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
      have : a * c - 1 ∈ la ^ n := by
        rw [← Ideal.Quotient.eq]; simpa [hq] using hd
      have h1 : (1 : 𝓞 L) ∈ la := by
        have := la.sub_mem (la.mul_mem_right c ha) (hle this)
        simpa using this
      exact hlatop ((Ideal.eq_top_iff_one _).mpr h1)
    · intro ha
      obtain ⟨c, y, hy, hcy⟩ := hmax.exists_inv ha
      have h1 : q c * q a = 1 - q y := by
        rw [← map_mul, ← map_one q, ← map_sub, ← hcy]; simp
      have : IsUnit (q c * q a) := h1 ▸ (hnil y hy).isUnit_one_sub
      exact isUnit_of_mul_isUnit_right this
  have hmem : ∀ a : 𝓞 L, q a ∈ la.map q ↔ a ∈ la := fun a => Ideal.mem_quotient_iff_mem hle

  obtain ⟨π₀, hπla, hπ2⟩ := SetLike.exists_of_lt ((Ideal.pow_right_strictAnti la hla0 hlatop) (by norm_num : 1 < 2))
  replace hπla : π₀ ∈ la := by simpa using hπla
  change π₀ ∉ la ^ 2 at hπ2
  have hQ : Ideal.span {π₀} ⊔ la ^ 2 = la := by
    have := Ideal.eq_prime_pow_of_succ_lt_of_le (P := la) (I := Ideal.span {π₀} ⊔ la ^ 2) hla0 (i := 1)
      (lt_of_le_of_ne le_sup_right (fun h => hπ2 (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π₀))))
      (by rw [pow_one]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hπla) (Ideal.pow_le_self two_ne_zero))
    simpa using this
  have hk : ∀ k, 1 ≤ k → la ≤ Ideal.span {π₀} ⊔ la ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [pow_one]; exact le_sup_right
    | succ k _ ih =>
      calc la = Ideal.span {π₀} ⊔ la ^ 2 := hQ.symm
        _ ≤ Ideal.span {π₀} ⊔ la * (Ideal.span {π₀} ⊔ la ^ k) :=
            sup_le_sup_left (by rw [pow_two]; exact Ideal.mul_mono_right ih) _
        _ = Ideal.span {π₀} ⊔ (la * Ideal.span {π₀} ⊔ la ^ (k + 1)) := by rw [Ideal.mul_sup, pow_succ']
        _ ≤ Ideal.span {π₀} ⊔ la ^ (k + 1) :=
            sup_le le_sup_left (sup_le (le_trans Ideal.mul_le_right le_sup_left) le_sup_right)
  have hm : Ideal.span {q π₀} = la.map q := by
    apply le_antisymm
    · rw [Ideal.span_singleton_le_iff_mem]; exact (hmem π₀).mpr hπla
    · calc la.map q ≤ (Ideal.span {π₀} ⊔ la ^ n).map q := Ideal.map_mono (hk n (Nat.one_le_iff_ne_zero.mpr hn0))
        _ = Ideal.span {q π₀} := by
            rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hq, Ideal.map_quotient_self, sup_bot_eq]
  have hJtop : J.map q = ⊤ := by
    have : (1 : 𝓞 L) ∈ la ⊔ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp this
    have hz' : q z = 1 - q y := by rw [← map_one q, ← hyz, map_add (f := _)]; ring
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem q hz) (hz' ▸ (hnil y hy).isUnit_one_sub)
  have hlspan : Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ n)} = (la.map q) ^ e := by
    have : ((l : ℕ) : 𝓞 L ⧸ la ^ n) = q (l : 𝓞 L) := (map_natCast q l).symm
    rw [this, ← Set.image_singleton, ← Ideal.map_span, hspan, Ideal.map_mul, Ideal.map_pow, hJtop, Ideal.mul_top]
  refine ⟨⟨fun k => ?_⟩, ?_, q π₀, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    obtain ⟨v, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0.ne' l hl.ne_one
    have hcop : Nat.Coprime l m' := (Nat.Prime.coprime_iff_not_dvd hl).mpr hm'
    have hm'la : ((m' : ℕ) : 𝓞 L) ∉ la := by
      intro h
      obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      have h1 : ((u * l + w * m' : ℤ) : 𝓞 L) = 1 := by rw [huw]; simp
      push_cast at h1
      have : (1 : 𝓞 L) ∈ la := h1 ▸ la.add_mem (la.mul_mem_left _ hlla) (la.mul_mem_left _ h)
      exact hlatop ((Ideal.eq_top_iff_one _).mpr this)
    have hmu : IsUnit ((m' : ℕ) : 𝓞 L ⧸ la ^ n) := by
      rw [← map_natCast q]; exact (hunit _).mpr hm'la
    rw [Nat.cast_mul, Nat.cast_pow, hmu.mul_left_eq_zero, ← Ideal.span_singleton_eq_bot,
      ← Ideal.span_singleton_pow, hlspan, ← pow_mul, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, hq,
      Ideal.mk_ker, hpowle, (Nat.Coprime.pow_left b hcop).dvd_mul_right,
      Nat.pow_dvd_pow_iff_le_right hl.one_lt, hn]
    exact ⟨fun h => Nat.le_of_mul_le_mul_left h he, fun h => Nat.mul_le_mul_left e h⟩
  · exact Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero n hla0)
  · intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.mem_span_singleton, hm, hmem]
    exact (not_congr (hunit a)).trans not_not
  · rw [← Ideal.span_singleton_pow, hm, hlspan]
  · have hc1 : Nat.card ((𝓞 L ⧸ la ^ n) ⧸ la.map q) = Nat.card (𝓞 L ⧸ la) :=
      Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
    have hc2 : ∀ I : Ideal (𝓞 L), Nat.card (𝓞 L ⧸ I) = Ideal.absNorm I := fun I => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hm, hc1, hc2, hc2, map_pow, hn, mul_comm e b]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientEquivRestrictedComponentFamilies
section
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem quotient_equiv_restrictedFamilies : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ), (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) → (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) → ∃ e : Γ ⧸ K ≃ {f : ∀ v, Γ ⧸ K.comap (c v) // {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite}, ∀ (g : Γ) v, (e (QuotientGroup.mk g)).1 v = (QuotientGroup.mk g : Γ ⧸ K.comap (c v)) := by
  intro Γ _ K ι c hK hfin hidem horth
  classical
  have hmk : ∀ v (g h : Γ), ((QuotientGroup.mk g : Γ ⧸ K.comap (c v)) = QuotientGroup.mk h) ↔
      c v (g⁻¹ * h) ∈ K := by
    intro v g h
    rw [QuotientGroup.eq, Subgroup.mem_comap]
  have hle : ∀ v, K ≤ K.comap (c v) := fun v g hg => (hK g).1 hg v
  let F : Γ ⧸ K → ∀ v, Γ ⧸ K.comap (c v) := fun q v =>
    Quotient.liftOn' q (fun g => (QuotientGroup.mk g : Γ ⧸ K.comap (c v))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      exact (QuotientGroup.eq).2 (hle v hab))
  have hF : ∀ g v, F (QuotientGroup.mk g) v = QuotientGroup.mk g := fun g v => rfl
  have hsupp : ∀ g, {w | F (QuotientGroup.mk g) w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))} =
      {v | c v g ∉ K} := by
    intro g
    ext w
    simp only [Set.mem_setOf_eq, hF, ne_eq, hmk, mul_one, map_inv, inv_mem_iff]
  let G : Γ ⧸ K → {f : ∀ v, Γ ⧸ K.comap (c v) //
      {w | f w ≠ (QuotientGroup.mk 1 : Γ ⧸ K.comap (c w))}.Finite} := fun q =>
    ⟨F q, by
      refine QuotientGroup.induction_on q ?_
      intro g
      rw [hsupp]
      exact hfin g⟩
  have hinj : Function.Injective G := by
    intro q₁ q₂ h12
    refine QuotientGroup.induction_on q₁ (fun g => ?_) h12
    refine QuotientGroup.induction_on q₂ (fun k => ?_)
    intro h12
    have h' : ∀ v, F (QuotientGroup.mk g) v = F (QuotientGroup.mk k) v :=
      fun v => congrFun (congrArg Subtype.val h12) v
    rw [QuotientGroup.eq, hK]
    intro v
    have := h' v
    rw [hF, hF, hmk] at this
    exact this
  have hcw : ∀ w (g : Γ), (QuotientGroup.mk (c w g) : Γ ⧸ K.comap (c w)) = QuotientGroup.mk g := by
    intro w g
    rw [hmk, map_mul, map_inv, hidem, inv_mul_cancel]
    exact K.one_mem
  have hlist : ∀ (x : ι → Γ) (l : List ι), l.Nodup → ∀ w,
      c w ((l.map (fun v => c v (x v))).prod) = if w ∈ l then c w (x w) else 1 := by
    intro x l
    induction l with
    | nil => intro _ w; simp
    | cons a t ih =>
      intro hl w
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
      by_cases hw : w = a
      · subst hw
        simp [hidem, hl.1]
      · rw [horth a w _ (Ne.symm hw), one_mul]
        simp [hw]
  have hsurj : Function.Surjective G := by
    rintro ⟨f, hf⟩
    let x : ι → Γ := fun v => (f v).out
    refine ⟨QuotientGroup.mk ((hf.toFinset.toList.map (fun v => c v (x v))).prod), ?_⟩
    apply Subtype.ext
    funext w
    show F (QuotientGroup.mk _) w = f w
    rw [hF, ← hcw w, hlist x hf.toFinset.toList (Finset.nodup_toList _) w]
    by_cases hw : w ∈ hf.toFinset.toList
    · rw [if_pos hw, hcw]
      exact Quotient.out_eq (f w)
    · rw [if_neg hw]
      rw [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hw
      exact hw.symm
  exact ⟨Equiv.ofBijective G ⟨hinj, hsurj⟩, fun g v => rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelMap
section
namespace GlobalTheory.RelationExtension

section
variable {A E F : Type} [CommRing A] [CommRing E] [CommRing F]

def Rel (ι : A →+* E) (f : A →+* F) (π P : A) (e : E) (x : F) : Prop :=
  ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y ∧ x * f π ^ m = f a

theorem rel_unique (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) {e : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e x') : x = x' := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  obtain ⟨b, hb⟩ := hk (a * π ^ m' - a' * π ^ m) (y' * ι π ^ m - y * ι π ^ m') (by
    simp only [map_sub, map_mul, map_pow]
    linear_combination (-(ι π ^ m')) * h1 + (ι π ^ m) * h1')
  have hf := congrArg f hb
  rw [map_mul, hP, zero_mul, map_sub, map_mul, map_mul, map_pow, map_pow] at hf
  have hu' : IsUnit (f π ^ (m + m')) := hu.pow _
  have h3 : x * f π ^ (m + m') = x' * f π ^ (m + m') := by
    rw [pow_add]
    linear_combination (f π ^ m') * h2 - (f π ^ m) * h2' + hf
  exact hu'.mul_right_cancel h3

theorem rel_map (ι : A →+* E) (f : A →+* F) (π P : A) (a : A) : Rel ι f π P (ι a) (f a) := ⟨a, 0, 0, by simp, by simp⟩

theorem rel_add (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e + e') (x + x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * π ^ m' + a' * π ^ m, m + m', y * ι π ^ m' + y' * ι π ^ m, ?_, ?_⟩
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (ι π ^ m') * h1 + (ι π ^ m) * h1'
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (f π ^ m') * h2 + (f π ^ m) * h2'

theorem rel_mul (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e * e') (x * x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * a', m + m', y * ι a' + ι a * y' + ι P * y * y', ?_, ?_⟩
  · rw [pow_add, map_mul]
    linear_combination (e' * ι π ^ m') * h1 + (ι a + ι P * y) * h1'
  · rw [pow_add, map_mul]
    linear_combination (x' * f π ^ m') * h2 + f a * h2'

end

theorem exists_extension {A E F : Type} [CommRing A] [CommRing E] [CommRing F]
    (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hs : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) :
    ∃ g : E →+* F, ∀ a : A, g (ι a) = f a := by
  have hex : ∀ e, ∃ x, Rel ι f π P e x := fun e => by
    obtain ⟨a, m, y, h⟩ := hs e
    exact ⟨f a * Ring.inverse (f π ^ m), a, m, y, h, by rw [mul_assoc, Ring.inverse_mul_cancel _ (hu.pow m), mul_one]⟩
  choose g hg using hex
  have hgu : ∀ e x, Rel ι f π P e x → g e = x := fun e x h => rel_unique ι f π P hu hP hk (hg e) h
  have h1 := rel_map ι f π P 1
  rw [map_one, map_one] at h1
  have h0 := rel_map ι f π P 0
  rw [map_zero, map_zero] at h0
  exact ⟨{ toFun := g
           map_one' := hgu _ _ h1
           map_mul' := fun e e' => hgu _ _ (rel_mul ι f π P (hg e) (hg e'))
           map_zero' := hgu _ _ h0
           map_add' := fun e e' => hgu _ _ (rel_add ι f π P (hg e) (hg e')) },
    fun a => hgu _ _ (rel_map ι f π P a)⟩

end GlobalTheory.RelationExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTopFactorThroughBottom
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem residue_top_factor_through_bottom : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t : ℕ) (U : Submodule O (Fin r ⊕ Fin t → O)) (a : Fin r → IsLocalRing.ResidueField O), (∀ u ∈ U, (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0) → ∀ g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → g.mulVec v = v) → ∃ b : Matrix (Fin r) (Fin t) (IsLocalRing.ResidueField O), ∀ u ∈ U, g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) + b.mulVec (fun i => IsLocalRing.residue O (u (Sum.inr i))) = (fun i => IsLocalRing.residue O (u (Sum.inl i))) := by
  intro O _ _ r t U a ha g hg
  let res : (Fin r ⊕ Fin t → O) → (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    fun u j => IsLocalRing.residue O (u j)
  let Wsp : Submodule (IsLocalRing.ResidueField O) (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) :=
    { carrier := {w | ∃ u ∈ U, res u = w}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        exact ⟨u + v, U.add_mem hu hv, by ext j; simp [res]⟩
      zero_mem' := ⟨0, U.zero_mem, by ext j; simp [res]⟩
      smul_mem' := by
        rintro c _ ⟨u, hu, rfl⟩
        obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨o • u, U.smul_mem o hu, by ext j; simp [res]⟩ }
  let top : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inl
  let bot : (Fin r ⊕ Fin t → IsLocalRing.ResidueField O) →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) :=
    LinearMap.funLeft _ _ Sum.inr
  let π : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin t → IsLocalRing.ResidueField O) := bot.comp Wsp.subtype
  let f : Wsp →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    (LinearMap.id - Matrix.toLin' g).comp (top.comp Wsp.subtype)
  have hker : LinearMap.ker π ≤ LinearMap.ker f := by
    rintro ⟨w, u, hu, rfl⟩ hw
    rw [LinearMap.mem_ker] at hw ⊢
    have h2 : ∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0 := fun i => congrFun hw i
    have h3 := hg _ (ha u hu h2)
    simp only [f, top, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Matrix.toLin'_apply]
    rw [sub_eq_zero]
    exact h3.symm
  let b₀ : LinearMap.range π →ₗ[IsLocalRing.ResidueField O] (Fin r → IsLocalRing.ResidueField O) :=
    ((LinearMap.ker π).liftQ f hker).comp (π.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨B, hB⟩ := LinearMap.exists_extend b₀
  refine ⟨LinearMap.toMatrix' B, ?_⟩
  intro u hu
  have hw : res u ∈ Wsp := ⟨u, hu, rfl⟩
  have key : B (π ⟨res u, hw⟩) = f ⟨res u, hw⟩ := by
    have h1 := LinearMap.congr_fun hB ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    show (LinearMap.ker π).liftQ f hker
      (π.quotKerEquivRange.symm ⟨π ⟨res u, hw⟩, LinearMap.mem_range_self π _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have e : π ⟨res u, hw⟩ = fun i => IsLocalRing.residue O (u (Sum.inr i)) := rfl
  have e2 : f ⟨res u, hw⟩ = (fun i => IsLocalRing.residue O (u (Sum.inl i))) -
      g.mulVec (fun i => IsLocalRing.residue O (u (Sum.inl i))) := rfl
  rw [e, e2] at key
  rw [LinearMap.toMatrix'_mulVec, key]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RightInvariantMulEqFinprodComponents
section
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem finprod_components_of_rightInvariant_mul :
    ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (ι : Type) (c : ι → Γ →* Γ) (a : Γ → ℂ),
      (∀ g, g ∈ K ↔ ∀ v, c v g ∈ K) → (∀ g, {v | c v g ∉ K}.Finite) →
      (∀ v g, c v (c v g) = c v g) → (∀ v w g, v ≠ w → c w (c v g) = 1) →
      (∀ g k, k ∈ K → a (g * k) = a g) → a 1 = 1 →
      (∀ v g h, c v g = 1 → c v h = h → a (g * h) = a g * a h) →
      ∀ g, a g = ∏ᶠ v, a (c v g) := by
  intro Γ _ K ι c a hK hfin hidem horth hinv ha1 hmul
  classical

  have haK : ∀ k, k ∈ K → a k = 1 := by
    intro k hk
    have := hinv 1 k hk
    rw [one_mul] at this
    rw [this, ha1]
  have key : ∀ (s : Finset ι) (g : Γ), {v | c v g ∉ K} ⊆ (s : Set ι) →
      a g = ∏ v ∈ s, a (c v g) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hgK : g ∈ K := (hK g).2 (fun v => by
        by_contra h
        simpa using hg h)
      simp [haK g hgK]
    | @insert v s hv ih =>
      intro g hg
      set g' := g * (c v g)⁻¹ with hg'
      have hcv : c v g' = 1 := by
        rw [hg', map_mul, map_inv, hidem, mul_inv_cancel]
      have hcw : ∀ w, w ≠ v → c w g' = c w g := by
        intro w hw
        rw [hg', map_mul, map_inv, horth v w g (Ne.symm hw), inv_one, mul_one]
      have hsupp : {w | c w g' ∉ K} ⊆ (s : Set ι) := by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        by_cases hwv : w = v
        · subst hwv
          exact absurd (hcv ▸ K.one_mem) hw
        · rw [hcw w hwv] at hw
          have := hg hw
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
          exact this.resolve_left hwv
      have ih' := ih g' hsupp
      have hprod : ∏ w ∈ s, a (c w g') = ∏ w ∈ s, a (c w g) := by
        apply Finset.prod_congr rfl
        intro w hw
        rw [hcw w (fun h => hv (h ▸ hw))]
      have hsplit : g = g' * c v g := by
        rw [hg', inv_mul_cancel_right]
      have hag : a g = a g' * a (c v g) := by
        conv_lhs => rw [hsplit]
        exact hmul v g' (c v g) hcv (hidem v g)
      rw [hag, ih', hprod, Finset.prod_insert hv, mul_comm]
  intro g
  have hsub : Function.mulSupport (fun v => a (c v g)) ⊆ ((hfin g).toFinset : Set ι) := by
    intro w hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hwK
    exact hw (haK _ hwK)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact key _ g (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPow
section
namespace GlobalTheory.FixedOfPower
open Polynomial

theorem fix_of_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (c : k) (hc : c ^ p = c) : τ c = c := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let f : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  have hc' : ∃ a, f a = c := by
    by_contra hcon
    have hP0 : (X ^ p - X : k[X]) ≠ 0 := X_pow_sub_X_ne_zero (R := k) hp1
    have hsub : insert c (Finset.univ.image f) ⊆ (X ^ p - X : k[X]).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hP0]
      show eval x (X ^ p - X) = 0
      rw [eval_sub, eval_pow, eval_X, sub_eq_zero]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hc
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        rw [← map_pow, ZMod.pow_card]
    have hcard : (insert c (Finset.univ.image f)).card = p + 1 := by
      rw [Finset.card_insert_of_notMem (by simpa using hcon),
        Finset.card_image_of_injective _ f.injective, Finset.card_univ, ZMod.card]
    have hle := (Finset.card_le_card hsub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' (X ^ p - X : k[X])))
    rw [hcard, Polynomial.natDegree_X_pow_sub_X (R := k) hp1] at hle
    omega
  obtain ⟨a, rfl⟩ := hc'
  exact DFunLike.congr_fun (RingHom.ext_zmod (τ.comp f) f) a

theorem ringHom_apply_eq_pow {k : Type} [Field k] (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (τ : k →+* k) (N : ℕ) (hN : 0 < N) (z : k) (hz : z ^ p ^ N = z) :
    ∃ e : ℕ, τ z = z ^ p ^ e := by
  have : ExpChar k p := ExpChar.prime Fact.out
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let g : k[X] := ∏ e ∈ Finset.range (M + 1), (X - C (z ^ p ^ e))
  have hg : g.map (frobenius k p) = g := by
    have e1 : ∀ e : ℕ, (z ^ p ^ e) ^ p = z ^ p ^ (e + 1) := fun e => by rw [← pow_mul, pow_succ]
    simp only [g, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      frobenius_def, e1]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun e => X - C (z ^ p ^ e)), hz, pow_zero,
      pow_one]
  have hcoef : ∀ i, (g.coeff i) ^ p = g.coeff i := by
    intro i
    have h := congrArg (fun q : k[X] => q.coeff i) hg
    simpa [Polynomial.coeff_map, frobenius_def] using h
  have hτ : g.map τ = g := by
    ext i
    rw [Polynomial.coeff_map]
    exact fix_of_pow p τ _ (hcoef i)
  have hz0 : g.eval z = 0 := by
    simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos M)) (by simp)
  have hτz : g.eval (τ z) = 0 := by
    rw [← hτ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hz0, map_zero]
  simp only [g, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hτz
  obtain ⟨e, -, he⟩ := Finset.prod_eq_zero_iff.mp hτz
  exact ⟨e, sub_eq_zero.mp he⟩

end GlobalTheory.FixedOfPower
end

