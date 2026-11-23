module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.Bundle0001
public import Mathlib.NumberTheory.Multiplicity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.OchOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.ochOf :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (Q : QCh T) (c' : Coef l) (h : c.O ≤ c'.O) (κ β : G T.L Ω →* c'.Oˣ), toQ κ = Q.κ → toQ β = Q.β → (AdicCont (maximalIdeal c'.O) fun g => (κ g : c'.O)) → (AdicCont (maximalIdeal c'.O) fun g => (β g : c'.O)) → (∀ g, residue c'.O (β g) = 1) → Nonempty (OCh T c' h) := by
  intro Ω _ _ _ l _ c D T Q c' h κ β hκQ hβQ hκc hβc hβr
  let U : (c'.O)ˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c'.O (PadicAlgCl l) : c'.O →* PadicAlgCl l)
  have hUinj : Function.Injective U := fun a b hab => Units.ext (Subtype.val_injective (congrArg Units.val hab))
  have hUκ : ∀ g, U (κ g) = Q.κ g := fun g => by
    rw [← hκQ]
    rfl
  have hUβ : ∀ g, U (β g) = Q.β g := fun g => by
    rw [← hβQ]
    rfl
  have hUchi : ∀ g, U (chiO T.L Ω l c'.O g) = cycBar T.L Ω l g := fun g => by
    rw [← (auChi T.L Ω c').1]
    rfl
  have hUth : ∀ r, ((inc h (D.th r : c.O) : c'.O) : PadicAlgCl l) = ((toQ D.th r : (PadicAlgCl l)ˣ) : PadicAlgCl l) := fun r => rfl
  refine ⟨{ κ := κ, β := β, t := Q.t, κ_cont := hκc, β_cont := hβc, t_cont := Q.t_cont, β_t := ?_, β_red := hβr, conj := ?_, t_unr := Q.t_unr, unr := ?_, tame := ?_, mu := ?_, cyc := ?_ }⟩
  · intro g hg
    have h1 := Q.β_t hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUβ, map_one]
    exact h1
  · intro σ hσ g g' hg
    obtain ⟨e1, e2, e3⟩ := Q.conj σ hσ g g' hg
    refine ⟨?_, ?_, e3⟩
    · apply Subtype.val_injective
      have e1' := congrArg Units.val e1
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at e1'
      have k1 : ((κ g : c'.O) : PadicAlgCl l) = (Q.κ g : PadicAlgCl l) := congrArg Units.val (hUκ g)
      have k2 : ((κ g' : c'.O) : PadicAlgCl l) = (Q.κ g' : PadicAlgCl l) := congrArg Units.val (hUκ g')
      have k3 : ((chiO T.L Ω l c'.O g : c'.O) : PadicAlgCl l) = (cycBar T.L Ω l g : PadicAlgCl l) := congrArg Units.val (hUchi g)
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, k1, k2, k3, hUth]
      exact e1'
    · apply hUinj
      rw [map_mul, hUβ, hUβ, map_one]
      exact e2
  · intro A hA g hg
    have h1 := Q.unr A hA hg
    rw [MonoidHom.mem_ker] at h1 ⊢
    apply hUinj
    rw [hUκ, map_one]
    exact h1
  · obtain ⟨m, hm, hmA⟩ := Q.tame
    refine ⟨m, hm, fun A hA g hg => hUinj ?_⟩
    rw [map_pow, hUκ, map_one]
    exact hmA A hA g hg
  · intro g a ha
    refine ⟨hUinj ?_, (Q.mu g a ha).2⟩
    rw [hUκ, map_one]
    exact (Q.mu g a ha).1
  · intro A hA
    obtain ⟨a, b, k, hk, hb, hall⟩ := Q.cyc A hA
    refine ⟨a, b, k, hk, hb, fun g hg => ⟨hUinj ?_, hUinj ?_⟩⟩
    · rw [map_pow, map_mul, map_zpow, hUκ, hUchi, map_one]
      exact (hall g hg).1
    · rw [map_pow, map_mul, map_pow, map_zpow, hUβ, hUchi, map_one]
      exact (hall g hg).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PadicPowL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem kill {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommGroup M] (f : Γ →* M)
    (hf : IsClosed (f.ker : Set Γ)) {g : Γ} {n : ℕ} (hg : g ^ n ∈ (commutator Γ).topologicalClosure) : f g ^ n = 1 := by
  rw [← map_pow]
  have hle : (commutator Γ).topologicalClosure ≤ f.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker f) hf
  exact hle hg

private theorem padic_pow_l {l : ℕ} [hl : Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  have hp := PadicInt.prime_p (p := l)
  have hodd : Odd l := hl.out.odd_of_ne_two h2
  have hc : PadicInt.toZMod x = 1 := by
    have h1 : PadicInt.toZMod x ^ l = 1 := by rw [← map_pow, hx, map_one]
    rw [ZMod.pow_card] at h1
    exact h1
  have hdvd : (l : ℤ_[l]) ∣ x - 1 := by
    have hs := PadicInt.toZMod_spec x
    rw [hc, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, ZMod.cast_eq_val, ZMod.val_one,
      Nat.cast_one] at hs
    exact hs
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by
    intro h
    have h1 : (l : ℤ_[l]) ∣ x ^ l := dvd_pow h hl.out.ne_zero
    rw [hx] at h1
    exact hp.not_dvd_one h1
  have key := emultiplicity_pow_prime_sub_pow_prime hp hodd hdvd hnd
  rw [hx, one_pow, sub_self, emultiplicity_zero] at key
  by_contra hne
  have hfin : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_not_isUnit hp.not_unit (sub_ne_zero.2 hne)
  rw [hfin.emultiplicity_eq_multiplicity] at key
  exact ENat.coe_ne_top (multiplicity (l : ℤ_[l]) (x - 1) + 1) (by push_cast; exact key.symm)

private theorem padic_pow {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (a : ℕ) (x : ℤ_[l]) (hx : x ^ l ^ a = 1) : x = 1 := by
  induction a generalizing x with
  | zero => simpa using hx
  | succ a ih =>
    apply ih
    apply padic_pow_l h2
    rw [← pow_mul, ← pow_succ]
    exact hx

theorem UpperTheory.V.Ws.Lk.kapMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} (P : Pre T), D.Good → ∀ (g : G T.L Ω) (a : ℕ), g ^ l ^ a ∈ (commutator (G T.L Ω)).topologicalClosure → P.κ g = 1 ∧ P.tL g = 1 := by
  intro Ω _ _ _ l _ c D T P hD g a hg
  have h2 : l ≠ 2 := Raw.Good.l_odd hD
  have hl := (Fact.out : l.Prime)
  have hcLe : Continuous (resLe (K_le T)) := by
    letI : Algebra T.K T.L := (IntermediateField.inclusion (K_le T)).toAlgebra
    haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    exact Af.continuous_restrictScalarsHom T.K T.L Ω
  have ht : P.tL g = 1 := by
    have hk : IsClosed ((P.t.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage (P.t_cont.comp hcLe)
    have hp := kill (P.t.comp (resLe (K_le T))) hk hg
    change (P.t.comp (resLe (K_le T))) g = 1
    have hz : (l ^ a) • Multiplicative.toAdd ((P.t.comp (resLe (K_le T))) g) = 0 := by
      rw [← toAdd_pow, hp, toAdd_one]
    have hz' := (smul_eq_zero.1 hz).resolve_left (pow_ne_zero _ hl.ne_zero)
    rw [← ofAdd_toAdd ((P.t.comp (resLe (K_le T))) g), hz', ofAdd_zero]
  refine ⟨?_, ht⟩
  have hβ : P.βL g = 1 := P.β_t ht
  have hγ : P.γ (resQ T.L g) = 1 := by
    have hcQ : Continuous (resQ T.L) := Af.continuous_restrictScalarsHom ℚ T.L Ω
    have hk : IsClosed (((cycZ ℚ Ω l).comp (resQ T.L)).ker : Set (G T.L Ω)) :=
      isClosed_singleton.preimage ((continuous_cycZ ℚ Ω l).comp hcQ)
    have hp := kill ((cycZ ℚ Ω l).comp (resQ T.L)) hk hg
    have hu : ((((cycZ ℚ Ω l).comp (resQ T.L)) g : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
      padic_pow h2 a _ (by rw [← Units.val_pow_eq_pow_val, hp, Units.val_one])
    exact P.γ_ker (Units.ext hu)
  have hκ : P.κ₀ (resLe (K_le T) g) = 1 := by
    have hk : IsClosed ((P.κ₀.comp (resLe (K_le T))).ker : Set (G T.L Ω)) :=
      (Subgroup.isClosed_of_isOpen _ P.κ₀_open).preimage hcLe
    have hp := kill (P.κ₀.comp (resLe (K_le T))) hk hg
    obtain ⟨m, hm, hm1⟩ := P.κ₀_ord
    have hq : P.κ₀ (resLe (K_le T) g) ^ m = 1 := by
      rw [← MonoidHom.pow_apply, hm1, MonoidHom.one_apply]
    have hcop : Nat.Coprime (l ^ a) m := Nat.Coprime.pow_left a hm
    have := pow_gcd_eq_one.2 ⟨hp, hq⟩
    rwa [hcop, pow_one] at this
  have hγ' : P.γ (AlgEquiv.restrictScalars ℚ g) = 1 := hγ
  simp only [Pre.κ, MonoidHom.mul_apply, MonoidHom.comp_apply, hβ, hγ, hκ]
  simp [hγ', hβ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem plus_eq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (x : Ω) : x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x := by
  classical
  set E : Subfield T.L := Subfield.comap (T.L.val : T.L →+* Ω) T.F.toSubfield with hEdef
  let e : E ≃+* T.F :=
    { toFun := fun y => ⟨((y : T.L) : Ω), y.2⟩
      invFun := fun z => ⟨⟨(z : Ω), T.F_le z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI : IsTotallyReal E := IsTotallyReal.ofRingEquiv e.symm
  have hEM : E ≤ maximalRealSubfield T.L := IsTotallyReal.le_maximalRealSubfield E
  have hdE : Module.finrank ℚ E = Module.finrank ℚ T.F :=
    (RingEquiv.toRatAlgEquiv e).toLinearEquiv.finrank_eq
  have hsup : Module.finrank ℚ T.L ≤ Module.finrank ℚ T.F * 2 := by
    have h1 := IntermediateField.finrank_sup_le T.F T.K
    rw [T.degK, ← T.hL] at h1
    exact h1
  have hM : Module.finrank ℚ (maximalRealSubfield T.L) * 2 = Module.finrank ℚ T.L := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield T.L) T.L]
    exact (letI : Module.Free (maximalRealSubfield T.L) T.L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield T.L) T.L)
  letI : Module.Free E T.L := Module.Free.of_divisionRing _ _
  have hE2 : Module.finrank ℚ E * Module.finrank E T.L = Module.finrank ℚ T.L :=
    Module.finrank_mul_finrank ℚ E T.L
  have hle : Module.finrank ℚ E ≤ Module.finrank ℚ (maximalRealSubfield T.L) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (Subfield.inclusion hEM).toRatAlgHom.toLinearMap) (Subfield.inclusion hEM).injective
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hposM : 0 < Module.finrank ℚ (maximalRealSubfield T.L) := Module.finrank_pos
  have hdeg : Module.finrank E T.L = 2 := by
    apply le_antisymm
    · have : Module.finrank ℚ E * Module.finrank E T.L ≤ Module.finrank ℚ E * 2 := by
        rw [hE2, hdE]; exact hsup
      exact Nat.le_of_mul_le_mul_left this hpos
    · have : Module.finrank ℚ (maximalRealSubfield T.L) * 2 ≤
          Module.finrank ℚ (maximalRealSubfield T.L) * Module.finrank E T.L := by
        rw [hM, ← hE2]
        exact Nat.mul_le_mul_right _ hle
      exact Nat.le_of_mul_le_mul_left this hposM
  haveI : Algebra.IsQuadraticExtension E T.L := { finrank_eq_two' := hdeg }
  have hEq : E = maximalRealSubfield T.L := NumberField.CMExtension.eq_maximalRealSubfield T.L E
  constructor
  · intro hx
    have hy : (⟨x, T.F_le hx⟩ : T.L) ∈ maximalRealSubfield T.L := by
      rw [← hEq]; exact hx
    exact ⟨⟨⟨x, T.F_le hx⟩, hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    have hy : (y : T.L) ∈ E := by rw [hEq]; exact y.2
    exact hy

private theorem fix_L {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (τ : G T.F Ω) : τ ∈ T.GalL ↔ ∀ x : T.L, τ (x : Ω) = x := by
  have hF : resQ T.F τ ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact τ.commutes ⟨y, hy⟩
  unfold Tower.GalL
  rw [Subgroup.mem_comap]
  constructor
  · intro h x
    have hsup : resQ T.F τ ∈ (T.F ⊔ T.K).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF, h⟩
    rw [← T.hL, IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff] at hsup
    exact hsup x x.2
  · intro h
    rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
    intro y hy
    exact h ⟨y, Lk.K_le T hy⟩

theorem UpperTheory.V.Ws.Lk.galEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), (∀ x : Ω, x ∈ T.F ↔ ∃ y : W.Lp T.L, algebraMap (W.Lp T.L) Ω y = x) ∧ (∃ φ : G (W.Lp T.L) Ω ≃* G T.F Ω, (∀ σ x, φ σ x = σ x) ∧ ∀ σ, φ σ ∈ T.GalL ↔ σ ∈ (W.resP T.L Ω).range) ∧ ∀ τ : G T.F Ω, τ ∈ T.GalL ↔ τ ∈ (resLe T.F_le).range := by
  intro Ω _ _ _ l _ c D T
  have hP := plus_eq T
  refine ⟨hP, ?_, ?_⟩
  · let φ : G (W.Lp T.L) Ω ≃* G T.F Ω :=
      { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => by
            obtain ⟨y, hy⟩ := (hP (x : Ω)).1 x.2
            change σ (x : Ω) = (x : Ω)
            rw [← hy]
            exact σ.commutes y)
        invFun := fun σ => AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun y => by
            have hx := (hP (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
            exact σ.commutes ⟨_, hx⟩)
        left_inv := fun σ => by ext; rfl
        right_inv := fun σ => by ext; rfl
        map_mul' := fun σ τ => by ext; rfl }
    refine ⟨φ, fun σ x => rfl, fun σ => ?_⟩
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃ₐ[W.Lp T.L] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
  · intro τ
    rw [fix_L, MonoidHom.mem_range]
    constructor
    · intro h
      exact ⟨AlgEquiv.ofRingEquiv (f := (τ : Ω ≃ₐ[T.F] Ω).toRingEquiv) (fun x => h x), by ext; rfl⟩
    · rintro ⟨ρ, rfl⟩ x
      exact ρ.commutes x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PrFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.prFacts :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), Function.Surjective V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, W.resP L Ω g' = s.c * W.resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : G L Ω), (V.frame.eps O R (V.pr g) : R) = algebraMap O R (chiO L Ω l O g)) ∧ ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), g ∈ V.frame.mu v → ∃ a : ℕ, (g : G L Ω) ^ l ^ a ∈ (commutator (G L Ω)).topologicalClosure := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨fun x => ?_, fun t => ?_, fun O _ _ R _ _ g => ?_, fun v g hg => ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, toGS Ω V.S' y = x.1 := QuotientGroup.mk'_surjective _ x.1
    obtain ⟨t, rfl⟩ : y ∈ (W.resP L Ω).range := (V.hη y).1 (by rw [hy]; exact x.2)
    exact ⟨t, Subtype.ext hy⟩
  · obtain ⟨t', ht'⟩ : s.c * W.resP L Ω t * s.c⁻¹ ∈ (W.resP L Ω).range := by
      rw [← V.hη, map_mul (toGS Ω V.S'), map_mul (toGS Ω V.S'), map_inv (toGS Ω V.S')]
      exact (V.frame.conj (V.pr t)).2
    refine ⟨t', ht', Subtype.ext ?_⟩
    show toGS Ω V.S' s.c * toGS Ω V.S' (W.resP L Ω t) * (toGS Ω V.S' s.c)⁻¹ = toGS Ω V.S' (W.resP L Ω t')
    rw [ht', map_mul, map_mul, map_inv]
  · have h : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ L Ω l g := DFunLike.congr_fun V.hε (W.resP L Ω g)
    show algebraMap O R (algebraMap ℤ_[l] O (V.ε (toGS Ω V.S' (W.resP L Ω g)) : ℤ_[l]ˣ)) = _
    rw [h]
    rfl
  · have hg' : (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ∈
        CommGroup.primaryComponent (TopologicalAbelianization (Dec (F := L) (s.A v))) l := hg
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (QuotientGroup.mk' _ g : TopologicalAbelianization (Dec (F := L) (s.A v))) ^ l ^ a = 1 := by
      first
      | exact exists_orderOf_eq_prime_pow_iff.1 hg'
      | exact hg'
      | simpa using hg'
    refine ⟨a, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    have hle : (commutator (Dec (F := L) (s.A v))).topologicalClosure ≤
        (commutator (G L Ω)).topologicalClosure.comap (Dec (F := L) (s.A v)).subtype := by
      refine Subgroup.topologicalClosure_minimal _ ?_
        ((Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val)
      rw [← Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.map_commutator]
      exact (Subgroup.commutator_mono le_top le_top).trans (Subgroup.le_topologicalClosure _)
    exact hle ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.RangeOpen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem range_open (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] : IsOpen ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (W.Lp L) L
  have hadj : Algebra.adjoin (W.Lp L) {α} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)).mp hα
  have hset : ((W.resP L Ω).range : Set (G (W.Lp L) Ω)) =
      {τ | τ (algebraMap L Ω α) = algebraMap L Ω α} := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      exact σ.commutes α
    · intro hτ
      have hext : (τ.toAlgHom.comp (IsScalarTower.toAlgHom (W.Lp L) L Ω)) =
          IsScalarTower.toAlgHom (W.Lp L) L Ω := by
        refine AlgHom.ext_of_adjoin_eq_top hadj ?_
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hτ
      have hfix : ∀ l : L, τ (algebraMap L Ω l) = algebraMap L Ω l := fun l =>
        DFunLike.congr_fun hext l
      refine ⟨{ τ with commutes' := hfix }, ?_⟩
      ext x
      rfl
  rw [hset]
  exact isOpen_setOf_apply (algebraMap L Ω α) (fun y => y = algebraMap L Ω α)

theorem UpperTheory.V.Ws.Lk.v0Ex :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)), IsOpen (U : Set (G L Ω)) → ∀ (g : G L Ω) (M : ℕ), M ≠ 0 → ∃ (v : W.Plc (W.Lp L)) (A : ValuationSubring Ω) (p : ℕ), p.Prime ∧ ¬ p ∣ M ∧ ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ normV v = p ∧ IsPlaceOver A v ∧ Dec (F := W.Lp L) A ≤ (W.resP L Ω).range ∧ (∀ d ∈ Dec (F := L) A, ∃ n : ℤ, d⁻¹ * g ^ n ∈ U) ∧ ∃ d ∈ Dec (F := L) A, d⁻¹ * g ∈ U := by
  intro L Ω _ _ _ _ _ _ _ U hU g M hM
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => DFunLike.congr_fun h x
  have hemb := (W.continuous_resP (L := L) (Ω := Ω)).isClosedEmbedding hinj
  have himg : IsOpen ((W.resP L Ω) '' (U : Set (G L Ω))) := by
    obtain ⟨t, ht, hpre⟩ := hemb.isInducing.isOpen_iff.mp hU
    rw [← hpre, Set.image_preimage_eq_inter_range]
    refine ht.inter ?_
    rw [← MonoidHom.coe_range]
    exact range_open L Ω
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one himg
    ⟨1, U.one_mem, map_one _⟩
  obtain ⟨v, A, p, σ, -, hp, hpM, -, hpv, hnv, -, hAv, hIne, hfrob, hσg⟩ :=
    Loc.v00 (F := W.Lp L) (Ω := Ω) N.toSubgroup N.isOpen' (W.resP L Ω g) ∅ M hM
  have hback : ∀ x : G L Ω, W.resP L Ω x ∈ N.toSubgroup → x ∈ U := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hN hx
    rw [hinj hux] at hu
    exact hu
  have hdec : ∀ d : G L Ω, d ∈ Dec (F := L) A ↔ W.resP L Ω d ∈ Dec (F := W.Lp L) A := by
    intro d
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hσH : σ ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    have h1 : W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2 : σ⁻¹ * W.resP L Ω g ∈ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :=
      Subgroup.mem_sup_right hσg
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    have h4 : W.resP L Ω g * (σ⁻¹ * W.resP L Ω g)⁻¹ = σ := by group
    rwa [h4] at h3
  have hHclosed : IsClosed ((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup :
      Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right N.isOpen')
  have hDecH : Dec (F := W.Lp L) A ≤ Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup := by
    intro d hd
    have hfrob' : IsFrob A (normV v) σ := by
      rw [hnv]
      exact hfrob
    have hcl := GlobalTheory.TameQuot.closure_frob_sup_Ine (W.Lp L) Ω A v hAv ⟨σ, hfrob.1⟩ hfrob'
    have hle : (Subgroup.zpowers (⟨σ, hfrob.1⟩ : Dec (F := W.Lp L) A) ⊔
        (Ine A).subgroupOf (Dec (F := W.Lp L) A)) ≤
        (Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf (Dec (F := W.Lp L) A) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
        exact hσH
      · intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact Subgroup.mem_sup_right (hIne hx)
    have hclosed : IsClosed (((Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup).subgroupOf
        (Dec (F := W.Lp L) A) : Subgroup (Dec (F := W.Lp L) A)) : Set (Dec (F := W.Lp L) A)) :=
      hHclosed.preimage continuous_subtype_val
    have hmin := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at hmin
    exact Subgroup.mem_subgroupOf.mp (hmin (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := W.Lp L) A)))
  have hHrange : Subgroup.zpowers (W.resP L Ω g) ⊔ N.toSubgroup ≤ (W.resP L Ω).range := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨g, rfl⟩
    · intro x hx
      obtain ⟨u, -, hu⟩ := hN hx
      exact ⟨u, hu⟩
  obtain ⟨d0, hd0⟩ := hHrange hσH
  refine ⟨v, A, p, hp, hpM, hpv, hnv, hAv, hDecH.trans hHrange, ?_, d0, ?_, ?_⟩
  · intro d hd
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hDecH ((hdec d).mp hd))
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨n, hback _ ?_⟩
    rw [map_mul, map_inv, map_zpow, ← hyz]
    have h5 : (W.resP L Ω g ^ n * z)⁻¹ * W.resP L Ω g ^ n = z⁻¹ := by group
    rw [h5]
    exact N.toSubgroup.inv_mem hz
  · rw [hdec, hd0]
    exact hfrob.1
  · apply hback
    rw [map_mul, map_inv, hd0]
    exact hσg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.StarOp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (χ : Fin n → F.G₀ →* Rˣ) (π : Equiv.Perm (Fin n)), (∀ i g, χ i (F.conj g) * χ (π i) g * F.eps O R g ^ ((n : ℤ) - 1) = 1) → F.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
  intro l _ F O _ _ R _ _ n χ π hχ B _ _ _ _ y
  let Ψ : Fin n → MonoidAlgebra B F.G₀ →ₐ[B] B := fun i =>
    MonoidAlgebra.lift B B F.G₀ ((Units.coeHom B).comp (W.pushCh (algebraMap R B) (χ i)))
  have hrep : ∀ z, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => Ψ i z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
      congr 1
      funext i
      rw [map_add (f := _)]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, Ψ]
      ext i j
      simp [W.diagRep, W.pushCh, Matrix.diagonal_apply]
  have hst : ∀ i z, Ψ i (F.star O B n z) = Ψ (π i) z := by
    intro i z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single g b =>
      simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, Ψ]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, map_smul,
        MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, W.pushCh, Units.coe_map,
        smul_eq_mul]
      congr 1
      have he : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O R B]
      have key : F.eps O R g ^ (1 - (n : ℤ)) * χ i (F.conj g)⁻¹ = χ (π i) g := by
        have h := hχ i g
        have hb : χ (π i) g = ((χ i) (F.conj g) * F.eps O R g ^ ((n : ℤ) - 1))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_left_comm, ← mul_assoc]
          exact h
        rw [hb, mul_inv, show (1 : ℤ) - n = -((n : ℤ) - 1) by ring, zpow_neg, map_inv, mul_comm]
      rw [he, ← map_zpow, Units.coe_map, ← key, Units.val_mul]
      simp
  show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (F.star O B n y)) =
    Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
  rw [hrep, hrep, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [hst]
  exact Equiv.prod_comp π (fun i => Ψ i y)
end

