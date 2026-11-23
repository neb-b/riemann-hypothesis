module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {S U : Subgroup G}

private theorem dc_up {x g : S} (h : g ∈ DC (U.subgroupOf S) x) : (g : G) ∈ DC U (x : G) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := h
  exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u', Subgroup.mem_subgroupOf.mp hu', by simp⟩

private theorem dc_left {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : w * z ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨w * u, U.mul_mem hw hu, u', hu', by simp only [mul_assoc]⟩

private theorem dc_right {b w z : G} (hw : w ∈ U) (hz : z ∈ DC U b) : z * w ∈ DC U b := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hz
  exact ⟨u, hu, u' * w, U.mul_mem hu' hw, by simp only [mul_assoc]⟩

private theorem dc_rep {x : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    {y : G} (hy : y ∈ DC U (x : G)) :
    ∃ t : S, t ∈ U.subgroupOf S ∧ ((t * x : S) : G)⁻¹ * y ∈ U := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨c, hc, hcx, hcS⟩ := hx u hu
  refine ⟨⟨u * c⁻¹, hcS⟩, Subgroup.mem_subgroupOf.mpr (U.mul_mem hu (U.inv_mem hc)), ?_⟩
  have e : ((⟨u * c⁻¹, hcS⟩ * x : S) : G)⁻¹ * (u * (x : G) * u') = c * u' := by
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc c, hcx]
    group
  rw [e]
  exact U.mul_mem hc hu'

private theorem dc_down {x g : S} (hx : ∀ u ∈ U, ∃ c ∈ U, c * (x : G) = x * c ∧ u * c⁻¹ ∈ S)
    (hg : (g : G) ∈ DC U (x : G)) : g ∈ DC (U.subgroupOf S) x := by
  obtain ⟨t, ht, hw⟩ := dc_rep hx hg
  refine ⟨t, ht, (t * x)⁻¹ * g, Subgroup.mem_subgroupOf.2 (by simpa using hw), ?_⟩
  group

private theorem mk_eq_of {r r' : S} (h : (r : G)⁻¹ * r' ∈ U) :
    (r : S ⧸ U.subgroupOf S) = r' := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using h

private theorem finOrb_sub {a : S} (h : AlgebraTools.FinOrb U U (a : G)) :
    AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a := by
  have inj : Function.Injective
      (fun q : S ⧸ U.subgroupOf S => (((Quotient.out q : S) : G) : G ⧸ U)) := by
    intro q1 q2 e
    dsimp only at e
    have e' := QuotientGroup.eq.mp e
    calc q1 = ((Quotient.out q1 : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q1).symm
      _ = ((Quotient.out q2 : S) : S ⧸ U.subgroupOf S) := mk_eq_of e'
      _ = q2 := QuotientGroup.out_eq' q2
  apply Set.Finite.of_finite_image _ inj.injOn
  apply h.subset
  rintro _ ⟨q, ⟨k, rfl⟩, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (k.1 * a)
  refine ⟨⟨((k.1 : S) : G), k.2⟩, ?_⟩
  have hq : (k • (a : S ⧸ U.subgroupOf S)) = ((k.1 * a : S) : S ⧸ U.subgroupOf S) := rfl
  dsimp only
  rw [hq, ht]
  show ((((k.1 : S) : G) * (a : G) : G) : G ⧸ U) = _
  rw [QuotientGroup.eq]
  convert Subgroup.mem_subgroupOf.mp t.2 using 1
  simp only [Subgroup.coe_mul]
  group

private theorem uf_sub {a b : S}
    (hab : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ c * (b : G) = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (hUF : UF U (a : G) (b : G)) : UF (U.subgroupOf S) a b := by
  have ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, -, h3, -⟩ := hab u hu
    exact ⟨c, hc, h1, h3⟩
  have hb : ∀ u ∈ U, ∃ c ∈ U, c * (b : G) = b * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, -, h2, h3, -⟩ := hab u hu
    exact ⟨c, hc, h2, h3⟩
  have hab' : ∀ u ∈ U, ∃ c ∈ U, c * ((a * b : S) : G) = ((a * b : S) : G) * c ∧ u * c⁻¹ ∈ S :=
    fun u hu => by
      obtain ⟨c, hc, h1, h2, h3, -⟩ := hab u hu
      refine ⟨c, hc, ?_, h3⟩
      simp only [Subgroup.coe_mul]
      rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  intro g
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · have hg' : (g : G) ∈ DC U ((a : G) * b) := by
      rw [← Subgroup.coe_mul]
      exact dc_up hg
    obtain ⟨Y, ⟨hY1, hY2⟩, hYu⟩ := (hUF g).1 hg'
    obtain ⟨t, ht, htY⟩ := dc_rep ha hY1
    have hrg : (t * a)⁻¹ * g ∈ DC (U.subgroupOf S) b := by
      apply dc_down hb
      have e : (((t * a)⁻¹ * g : S) : G)
          = (((t * a : S) : G)⁻¹ * Quotient.out Y) * ((Quotient.out Y)⁻¹ * g) := by
        push_cast
        group
      rw [e]
      exact dc_left htY hY2
    have hrY : ((((t * a : S) : G)) : G ⧸ U) = Y := by
      rw [← QuotientGroup.out_eq' Y]
      exact QuotientGroup.eq.mpr htY
    have key : ∀ s : G, s ∈ DC U a → s⁻¹ * g ∈ DC U b → (s : G ⧸ U) = Y := by
      intro s hs1 hs2
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul U s
      refine hYu _ ⟨?_, ?_⟩
      · rw [hk]
        exact dc_right k.2 hs1
      · rw [hk, mul_inv_rev, mul_assoc]
        exact dc_left (inv_mem k.2) hs2
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · rw [hk]
      exact dc_right k.2 ⟨t, ht, 1, one_mem _, (mul_one _).symm⟩
    · rw [hk, mul_inv_rev, mul_assoc]
      exact dc_left (inv_mem k.2) hrg
    · rintro z ⟨hz1, hz2⟩
      have hz : (((Quotient.out z : S) : G) : G ⧸ U) = Y :=
        key _ (dc_up hz1) (by simpa using dc_up hz2)
      calc z = ((Quotient.out z : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' z).symm
        _ = _ := mk_eq_of (QuotientGroup.eq.mp (hz.trans hrY.symm))
  · have h1 := (hUF g).2 y (dc_up hy) (by simpa using dc_up hyg)
    apply dc_down hab'
    rw [Subgroup.coe_mul]
    exact h1

private theorem reps_sub {a : S} (ha : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S)
    (hfin : AlgebraTools.FinOrb (U.subgroupOf S) (U.subgroupOf S) a) :
    ∃ R : Finset S, (∀ y ∈ R, y ∈ DC (U.subgroupOf S) a) ∧
      (∀ y ∈ DC (U.subgroupOf S) a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U.subgroupOf S) ∧
      ∀ y ∈ DC U (a : G), ∃! r : S, r ∈ R ∧ (r : G)⁻¹ * y ∈ U := by
  classical
  have orb : ∀ k : S, k ∈ U.subgroupOf S →
      ((k * a : S) : S ⧸ U.subgroupOf S) ∈
        MulAction.orbit (U.subgroupOf S) (a : S ⧸ U.subgroupOf S) :=
    fun k hk => ⟨⟨k, hk⟩, rfl⟩
  refine ⟨hfin.toFinset.image (fun q => Quotient.out q), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.mp hq
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) ((k : S) * a)
    have hq' : k • (a : S ⧸ U.subgroupOf S) = (((k : S) * a : S) : S ⧸ U.subgroupOf S) := rfl
    dsimp only
    rw [hq', hh]
    exact dc_right h.2 ⟨k, k.2, 1, one_mem _, (mul_one _).symm⟩
  · intro y hy
    obtain ⟨u, hu, u', hu', rfl⟩ := hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (u * a)
    refine ⟨Quotient.out ((u * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb u hu), rfl⟩
    · rw [hh]
      have e : (u * a * (h : S))⁻¹ * (u * a * u') = (h : S)⁻¹ * u' := by group
      rw [e]
      exact mul_mem (inv_mem h.2) hu'
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((u * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = ((u * a * u' : S) : S ⧸ U.subgroupOf S) := QuotientGroup.eq.mpr hry
          _ = _ := QuotientGroup.eq.mpr (by
            rw [show (u * a * u')⁻¹ * (u * a) = u'⁻¹ by group]
            exact inv_mem hu')
      rw [e]
  · intro y hy
    obtain ⟨t, ht, hty⟩ := dc_rep ha hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf S) (t * a)
    refine ⟨Quotient.out ((t * a : S) : S ⧸ U.subgroupOf S), ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr (orb t ht), rfl⟩
    · rw [hh]
      have e : ((t * a * (h : S) : S) : G)⁻¹ * y
          = ((h : S) : G)⁻¹ * (((t * a : S) : G)⁻¹ * y) := by
        push_cast
        group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp h.2)) hty
    · rintro r ⟨hr, hry⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      have e : q = ((t * a : S) : S ⧸ U.subgroupOf S) :=
        calc q = ((Quotient.out q : S) : S ⧸ U.subgroupOf S) := (QuotientGroup.out_eq' q).symm
          _ = _ := mk_eq_of (by
            have m := U.mul_mem hry (U.inv_mem hty)
            convert m using 1
            group)
      rw [e]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcSub :
    UpperTheory.V.Z.Sym.So.DcSub := by
  intro G V _ _ _ S U a hfin ha _
  have ha' : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S := fun u hu => by
    obtain ⟨c, hc, h1, h2, _⟩ := ha u hu
    exact ⟨c, hc, h1, h2⟩
  have hfin' := finOrb_sub hfin
  exact ⟨hfin', fun g => ⟨dc_up, dc_down ha'⟩, fun b hb hUF => uf_sub hb hUF, reps_sub ha' hfin'⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.PosSpec
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma mul_of_genEig {P M : Type} [CommSemigroup P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (u : P → Module.End ℂ M) (hu : ∀ p q, u (p * q) = u p * u q) (hc : ∀ p q, Commute (u p) (u q))
    (ψ : P → ℂ) (h : IsGenEig u ψ) (p q : P) : ψ (p * q) = ψ p * ψ q := by
  obtain ⟨v, hv0, hv⟩ := (Tf.eigVec P M u hc ψ).1 h
  have h1 := hv (p * q)
  rw [hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul] at h1
  rw [mul_comm (ψ p)]
  exact (smul_left_injective ℂ hv0 h1).symm

theorem UpperTheory.V.Z.Sym.So.posSpec :
    UpperTheory.V.Z.Sym.So.PosSpec := by
  unfold UpperTheory.V.Z.Sym.So.PosSpec
  intro P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex
  have hcu : ∀ j p q, Commute (u j p) (u j q) := fun j p q => by
    unfold Commute SemiconjBy
    rw [← hu, ← hu, mul_comm]
  have hcw : ∀ p q, Commute (w p) (w q) := fun p q => by
    unfold Commute SemiconjBy
    rw [← hw, ← hw, mul_comm]
  by_cases hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v
  · exact Or.inr hN
  left
  choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)
  obtain ⟨XN, dN, hXN, hdN, htrN⟩ := Tf.trPos P N w hcw
  obtain ⟨j0, v0, hv0, hv0'⟩ := hex
  have hχj0 : χ ∈ XX j0 :=
    (hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)
  have hχN : χ ∉ XN := fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))
  let T : Option J → Finset (P → ℂ) := fun o => Option.elim o XN XX
  let S' : Finset (Σ _ : Option J, P → ℂ) := Finset.univ.sigma T
  let b' : (Σ _ : Option J, P → ℂ) → ℂ := fun k =>
    Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))
  let β' : (Σ _ : Option J, P → ℂ) → P → ℂ := fun k => k.2
  refine Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_
  · rintro ⟨o, ψ⟩ hk p q
    simp only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk
    cases o with
    | none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q
    | some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q
  · intro p
    rw [htr p, htrN p]
    simp only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim,
      Finset.mul_sum, mul_assoc]
    exact add_comm _ _
  · open ComplexOrder in
    · refine (Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'
      · rintro ⟨o, ψ⟩ hk
        simp only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, rfl⟩ := hk
        cases o with
        | none => exact absurd hk1 hχN
        | some j =>
          simp only [b', Option.elim]
          exact mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)
      · simp [S', β', T, hχj0]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Box

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K U : ∀ v, Subgroup (Gv v)}

private theorem memBox (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) :
    g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

private theorem smulMk {A : Type} [Group A] (W W' : Subgroup A) (u : W) (x : A) :
    u • (x : A ⧸ W') = (((u : A) * x : A) : A ⧸ W') := rfl

end Box

end UpperTheory.V.Z.Sym.So

private theorem mem_doubleCoset_iff_exists_eq_mul_mul {A : Type} [Group A] {W : Subgroup A} {a x : A} :
    x ∈ DC W a ↔ ∃ u ∈ W, ∃ u' ∈ W, x = u * a * u' := Iff.rfl

private theorem mul_mem_doubleCoset_of_mem_doubleCoset_of_mem {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : x * c ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨u, hu, u' * c, mul_mem hu' hc, by simp only [mul_assoc]⟩

private theorem mul_mem_doubleCoset_of_mem_of_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : c * x ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨c * u, mul_mem hc hu, u', hu', by simp only [mul_assoc]⟩

private theorem out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a b g x : A}
    (h1 : x ∈ DC W a) (h2 : x⁻¹ * g ∈ DC W b) :
    Quotient.out (x : A ⧸ W) ∈ DC W a ∧ (Quotient.out (x : A ⧸ W))⁻¹ * g ∈ DC W b := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul W x
  rw [hc]
  refine ⟨mul_mem_doubleCoset_of_mem_doubleCoset_of_mem h1 c.2, ?_⟩
  rw [mul_inv_rev, mul_assoc]
  exact mul_mem_doubleCoset_of_mem_of_mem_doubleCoset h2 (inv_mem c.2)

private theorem quotientGroup_coe_out_eq_self {A : Type} [Group A] (W : Subgroup A) (y : A ⧸ W) :
    ((Quotient.out y : A) : A ⧸ W) = y := Quotient.out_eq y

theorem UpperTheory.V.Z.Sym.So.uFBox :
    UpperTheory.V.Z.Sym.So.UFBox := by
  intro I G _ Gv _ K U P S _ a ha
  classical
  have hB : ∀ g, g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := memBox P U
  have glue : ∀ x : (v : I) → Gv v, (∀ v ∉ S, x v = 1) → ∃ h : G, ∀ v, P.p v h = x v := by
    intro x hx
    apply P.surj
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
    intro v hv
    by_contra hvS
    exact hv (by rw [hx v hvS]; exact one_mem _)
  have key : ∀ c : G, (∀ v ∉ S, P.p v c ∈ U v) → ∀ g : G, g ∈ DC (P.box U) c ↔
      (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v c)) ∧ ∀ v ∉ S, P.p v g ∈ U v := by
    intro c hc g
    constructor
    · intro hg
      obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hg
      rw [hB] at hu hu'
      refine ⟨fun v _ => mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨P.p v u, hu v, P.p v u', hu' v, by rw [map_mul, map_mul]⟩, fun v hv => ?_⟩
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hu v) (hc v hv)) (hu' v)
    · rintro ⟨h1, h2⟩
      have h1' : ∀ v ∈ S, ∃ u ∈ U v, ∃ u' ∈ U v, P.p v g = u * P.p v c * u' :=
        fun v hv => mem_doubleCoset_iff_exists_eq_mul_mul.1 (h1 v hv)
      choose! u hu u' hu' hg using h1'
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then u v else 1) (fun v hv => if_neg hv)
      refine mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨w, ?_, c⁻¹ * w⁻¹ * g, ?_, by group⟩
      · rw [hB]
        intro v
        rw [hw]
        split_ifs with hv
        exacts [hu v hv, one_mem _]
      · rw [hB]
        intro v
        rw [map_mul, map_mul, map_inv, map_inv, hw]
        split_ifs with hv
        · rw [hg v hv]
          have e : (P.p v c)⁻¹ * (u v)⁻¹ * (u v * P.p v c * u' v) = u' v := by group
          rw [e]
          exact hu' v hv
        · rw [inv_one, mul_one]
          exact mul_mem (inv_mem (hc v hv)) (h2 v hv)
  refine ⟨key a ha, ?_, ?_⟩
  · intro hf
    unfold UpperTheory.V.AlgebraTools.FinOrb at hf ⊢
    have hout : ∀ u : P.box U, ∀ v ∉ S,
        P.p v (Quotient.out (u • (a : G ⧸ P.box U))) ∈ U v := by
      intro u v hv
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      rw [smulMk, hc, map_mul, map_mul]
      exact mul_mem (mul_mem ((hB _).1 u.2 v) (ha v hv)) ((hB _).1 c.2 v)
    apply Set.Finite.of_finite_image
      (f := fun (y : G ⧸ P.box U) (v : S) => ((P.p v.1 (Quotient.out y) : Gv v.1) : Gv v.1 ⧸ U v.1))
    · refine (Set.Finite.pi (t := fun v : S =>
        MulAction.orbit (U v.1) ((P.p v.1 a : Gv v.1) : Gv v.1 ⧸ U v.1)) (fun v => hf v.1 v.2)).subset ?_
      rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
      rw [Set.mem_univ_pi]
      intro v
      refine ⟨⟨P.p v.1 u, (hB _).1 u.2 v.1⟩, ?_⟩
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      simp only [smulMk]
      rw [hc, QuotientGroup.eq]
      convert (hB _).1 c.2 v.1 using 1
      simp only [map_mul, Subgroup.coe_mk]
      group
    · rintro _ ⟨u1, rfl⟩ _ ⟨u2, rfl⟩ h12
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans ((QuotientGroup.eq.2 ?_).trans (quotientGroup_coe_out_eq_self _ _))
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      by_cases hv : v ∈ S
      · exact QuotientGroup.eq.1 (congrFun h12 ⟨v, hv⟩)
      · exact mul_mem (inv_mem (hout u1 v hv)) (hout u2 v hv)
  · intro b hb hloc g
    have hab : ∀ v ∉ S, P.p v (a * b) ∈ U v := fun v hv => by
      rw [map_mul]
      exact mul_mem (ha v hv) (hb v hv)
    constructor
    · intro hg
      obtain ⟨hgS, hgN⟩ := (key _ hab g).1 hg
      have hgl : ∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a * P.p v b) := fun v hv => by
        rw [← map_mul]
        exact hgS v hv
      have hl : ∀ v ∈ S, ∃ z, z ∈ DC (U v) (P.p v a) ∧ z⁻¹ * P.p v g ∈ DC (U v) (P.p v b) := by
        intro v hv
        obtain ⟨y, hy, -⟩ := (hloc v hv (P.p v g)).1 (hgl v hv)
        exact ⟨_, hy⟩
      choose! z hz1 hz2 using hl
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then z v else 1) (fun v hv => if_neg hv)
      have hw1 : w ∈ DC (P.box U) a := (key a ha w).2
        ⟨fun v hv => by rw [hw, if_pos hv]; exact hz1 v hv,
         fun v hv => by rw [hw, if_neg hv]; exact one_mem _⟩
      have hw2 : w⁻¹ * g ∈ DC (P.box U) b := (key b hb _).2
        ⟨fun v hv => by rw [map_mul, map_inv, hw, if_pos hv]; exact hz2 v hv,
         fun v hv => by rw [map_mul, map_inv, hw, if_neg hv, inv_one, one_mul]; exact hgN v hv⟩
      refine ⟨(w : G ⧸ P.box U), out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hw1 hw2, ?_⟩
      rintro y ⟨hy1, hy2⟩
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans (QuotientGroup.eq.2 ?_)
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      have ha1 := (key a ha _).1 hy1
      have hb1 := (key b hb _).1 hy2
      by_cases hv : v ∈ S
      · have hb2 := hb1.1 v hv
        rw [map_mul, map_inv] at hb2
        have hz2' := hz2 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz2'
        have hz1' := hz1 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz1'
        have e := ((hloc v hv (P.p v g)).1 (hgl v hv)).unique
          (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset (ha1.1 v hv) hb2) (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hz1' hz2')
        exact QuotientGroup.eq.1 e
      · rw [hw, if_neg hv]
        exact mul_mem (inv_mem (ha1.2 v hv)) (one_mem _)
    · intro y hy1 hy2
      refine (key _ hab g).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := ((key b hb _).1 hy2).1 v hv
        rw [map_mul, map_inv] at h2
        rw [map_mul]
        exact (hloc v hv (P.p v g)).2 (P.p v y) (((key a ha y).1 hy1).1 v hv) h2
      · have h1 := ((key a ha y).1 hy1).2 v hv
        have h2 := ((key b hb _).1 hy2).2 v hv
        rw [map_mul, map_inv] at h2
        have h3 := mul_mem h1 h2
        rwa [mul_inv_cancel_left] at h3

end
end

