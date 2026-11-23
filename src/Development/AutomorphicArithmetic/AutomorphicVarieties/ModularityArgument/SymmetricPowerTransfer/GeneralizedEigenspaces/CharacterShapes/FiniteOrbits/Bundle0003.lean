module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ConjMemLevel
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.So.extF :
    UpperTheory.V.Z.Sym.So.ExtF := by
  intro Γ G V _ _ _ _ ι W S U hSn hcomm hΓ ψ hψΓ hψU
  classical
  have wd : ∀ (γ γ' : Γ) (s s' : S) (u u' : G), u ∈ U → u' ∈ U →
      ι γ * s * u = ι γ' * s' * u' → W γ (ψ s) = W γ' (ψ s') := by
    intro γ γ' s s' u u' hu hu' h
    have hv : u * u'⁻¹ ∈ U := U.mul_mem hu (U.inv_mem hu')
    have h1 : ι (γ'⁻¹ * γ) * s * (u * u'⁻¹) = s' := by
      rw [map_mul, map_inv]
      rw [show (ι γ')⁻¹ * ι γ * ↑s * (u * u'⁻¹) = (ι γ')⁻¹ * (ι γ * ↑s * u) * u'⁻¹ by group, h]
      group
    have hδ : ι (γ'⁻¹ * γ) ∈ S := by
      apply hΓ (γ'⁻¹ * γ) (u * u'⁻¹) hv
      have e : ι (γ'⁻¹ * γ) * (u * u'⁻¹) =
          ↑s' * ((u * u'⁻¹)⁻¹ * (↑s)⁻¹ * (u * u'⁻¹)) := by
        rw [← h1]
        group
      rw [e]
      apply S.mul_mem s'.2
      have hc := hSn.conj_mem _ (S.inv_mem s.2) (u * u'⁻¹)⁻¹
      rw [inv_inv] at hc
      exact hc
    have hvS : u * u'⁻¹ ∈ S := by
      have e : u * u'⁻¹ = (ι (γ'⁻¹ * γ) * ↑s)⁻¹ * ↑s' := by
        rw [← h1]
        group
      rw [e]
      exact S.mul_mem (S.inv_mem (S.mul_mem hδ s.2)) s'.2
    have e1 : s' = ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ * ⟨u * u'⁻¹, hvS⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      exact h1.symm
    rw [e1, hψU ⟨u * u'⁻¹, hvS⟩ hv,
      hψΓ (γ'⁻¹ * γ) s ⟨ι (γ'⁻¹ * γ) * s, S.mul_mem hδ s.2⟩ rfl, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]
  obtain ⟨P, hP⟩ : ∃ P : G → Prop, ∀ g, P g ↔ ∃ γ : Γ, ∃ s : S, ∃ u ∈ U, g = ι γ * s * u :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : G → V, ∀ g, Φ g = if h : P g then
      W ((hP g).1 h).choose (ψ ((hP g).1 h).choose_spec.choose) else 0 := ⟨_, fun _ => rfl⟩
  have Φ_spec : ∀ (γ : Γ) (s : S) (u : G), u ∈ U → Φ (ι γ * s * u) = W γ (ψ s) := by
    intro γ s u hu
    have h : P (ι γ * s * u) := (hP _).2 ⟨γ, s, u, hu, rfl⟩
    rw [hΦ, dite_eq_left h]
    obtain ⟨u0, hu0, e⟩ := ((hP _).1 h).choose_spec.choose_spec
    exact wd _ _ _ _ _ _ hu0 hu e.symm
  have Φ_neg : ∀ g, ¬ P g → Φ g = 0 := fun g h => by rw [hΦ, dite_eq_right h]
  have hUinv : ∀ u ∈ U, ∀ g : G, Φ (g * u) = Φ g := by
    intro u hu g
    by_cases hg : P g
    · obtain ⟨γ, s, u0, hu0, rfl⟩ := (hP g).1 hg
      rw [show ι γ * ↑s * u0 * u = ι γ * ↑s * (u0 * u) by group, Φ_spec _ _ _ (U.mul_mem hu0 hu),
        Φ_spec _ _ _ hu0]
    · rw [Φ_neg _ hg, Φ_neg]
      intro h'
      apply hg
      obtain ⟨γ, s, u1, hu1, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s, u1 * u⁻¹, U.mul_mem hu1 (U.inv_mem hu), ?_⟩
      rw [← mul_assoc, ← e]
      group
  refine ⟨Φ, ?_, ?_, hUinv, ?_⟩
  · intro g
    have h := Φ_spec 1 g 1 U.one_mem
    simpa using h
  · intro γ g
    by_cases hg : P g
    · obtain ⟨δ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [show ι γ * (ι δ * ↑s * u) = ι (γ * δ) * ↑s * u by rw [map_mul]; group,
        Φ_spec _ _ _ hu, Φ_spec _ _ _ hu, map_mul, Module.End.mul_apply]
    · rw [Φ_neg _ hg, map_zero, Φ_neg]
      intro h'
      apply hg
      obtain ⟨δ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ⁻¹ * δ, s, u, hu, ?_⟩
      have e2 : g = (ι γ)⁻¹ * (ι γ * g) := by group
      rw [e2, e, map_mul, map_inv]
      group
  · intro a c hfin hz heig
    obtain ⟨hfinS, hmem, -, R, hR1, hR2, hR3⟩ := dcSub G V S U a hfin hz hSn
    have hψU' : ∀ u ∈ U.subgroupOf S, ∀ g : S, ψ (g * u) = ψ g :=
      fun u hu g => hψU u (Subgroup.mem_subgroupOf.1 hu) g
    have hval : ∀ x ∈ U, ∀ g : G, dcF U (↑a) Φ g = ∑ r ∈ R, Φ (g * (x⁻¹ * ↑r * x)) := by
      intro x hx g
      let e : S ↪ G := ⟨fun r => x⁻¹ * ↑r * x, fun r1 r2 h => Subtype.ext (by simpa using h)⟩
      have h1 : ∀ y ∈ R.map e, y ∈ DC U (↑a) := by
        intro y hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨v, hv, w, hw, h⟩ := (hmem r).1 (hR1 r hr)
        refine ⟨x⁻¹ * v, U.mul_mem (U.inv_mem hx) hv, w * x, U.mul_mem hw hx, ?_⟩
        show x⁻¹ * ↑r * x = _
        rw [h]
        group
      have h2 : ∀ y ∈ DC U (↑a), ∃! r, r ∈ R.map e ∧ r⁻¹ * y ∈ U := by
        intro y hy
        have hxy : x * y ∈ DC U (↑a) := by
          obtain ⟨v, hv, w, hw, rfl⟩ := hy
          exact ⟨x * v, U.mul_mem hx hv, w, hw, by group⟩
        obtain ⟨r, ⟨hr, hry⟩, huniq⟩ := hR3 _ hxy
        refine ⟨x⁻¹ * ↑r * x, ⟨Finset.mem_map_of_mem e hr, ?_⟩, ?_⟩
        · have e3 : (x⁻¹ * ↑r * x)⁻¹ * y = x⁻¹ * ((↑r)⁻¹ * (x * y)) := by group
          rw [e3]
          exact U.mul_mem (U.inv_mem hx) hry
        · rintro y' ⟨hy', hy'y⟩
          obtain ⟨r1, hr1, rfl⟩ := Finset.mem_map.1 hy'
          have hr1y : (↑r1 : G)⁻¹ * (x * y) ∈ U := by
            have e4 : (↑r1 : G)⁻¹ * (x * y) = x * ((x⁻¹ * ↑r1 * x)⁻¹ * y) := by group
            rw [e4]
            exact U.mul_mem hx hy'y
          rw [huniq r1 ⟨hr1, hr1y⟩]
          rfl
      rw [(dcBasic G V U a hfin Φ hUinv).2.2.2.2 (R.map e) h1 h2 g, Finset.sum_map]
      rfl
    funext g
    rw [Pi.smul_apply]
    by_cases hg : P g
    · obtain ⟨γ, s, u, hu, rfl⟩ := (hP g).1 hg
      rw [hval u hu, Φ_spec γ s u hu]
      have e5 : ∀ r : S, Φ (ι γ * ↑s * u * (u⁻¹ * ↑r * u)) = W γ (ψ (s * r)) := by
        intro r
        rw [show ι γ * ↑s * u * (u⁻¹ * ↑r * u) = ι γ * ↑(s * r) * u by
          simp only [Subgroup.coe_mul]; group, Φ_spec _ _ _ hu]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl (fun r _ => e5 r), ← map_sum (W γ),
        ← (dcBasic S V (U.subgroupOf S) a hfinS ψ hψU').2.2.2.2 R hR1 hR2 s, heig, Pi.smul_apply,
        map_smul]
    · rw [hval 1 U.one_mem, Φ_neg _ hg, smul_zero]
      apply Finset.sum_eq_zero
      intro r _
      apply Φ_neg
      intro h'
      apply hg
      obtain ⟨γ, s, u, hu, e⟩ := (hP _).1 h'
      refine (hP g).2 ⟨γ, s * ⟨u * (↑r)⁻¹ * u⁻¹, hSn.conj_mem _ (S.inv_mem r.2) u⟩, u, hu, ?_⟩
      have e6 : g = g * (1⁻¹ * ↑r * 1) * (↑r)⁻¹ := by group
      rw [e6, e]
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      group

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem dc_right (U : Subgroup G) (a : G) {r s : G} (h : r⁻¹ * s ∈ U) (hr : r ∈ DC U a) :
    s ∈ DC U a := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hr
  refine ⟨u, hu, w * ((u * a * w)⁻¹ * s), U.mul_mem hw h, ?_⟩
  group

private theorem dc_left (U : Subgroup G) (b : G) {c g : G} (h : c ∈ U) (hg : g ∈ DC U b) :
    c * g ∈ DC U b := by
  obtain ⟨u, hu, w, hw, rfl⟩ := hg
  exact ⟨c * u, U.mul_mem h hu, w, hw, by group⟩

private theorem out_inv_mul_mem (U : Subgroup G) (s : G) :
    (Quotient.out (s : G ⧸ U))⁻¹ * s ∈ U :=
  QuotientGroup.eq.1 (QuotientGroup.out_eq' (s : G ⧸ U))

private theorem uf_unique_iff (U : Subgroup G) (a b g : G) :
    (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
      ∃ r, (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ∧
        ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b → r⁻¹ * s ∈ U := by
  have hq : ∀ s, s ∈ DC U a → s⁻¹ * g ∈ DC U b →
      (Quotient.out (s : G ⧸ U)) ∈ DC U a ∧ (Quotient.out (s : G ⧸ U))⁻¹ * g ∈ DC U b := by
    intro s hs hs'
    have h1 := out_inv_mul_mem U s
    have h2 : s⁻¹ * Quotient.out (s : G ⧸ U) ∈ U := by
      have := U.inv_mem h1
      simpa using this
    refine ⟨dc_right U a h2 hs, ?_⟩
    have := dc_left U b h1 hs'
    simpa [mul_assoc] using this
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, huniq⟩
    refine ⟨y.out, ⟨hy1, hy2⟩, fun s hs hs' => ?_⟩
    have h3 : (s : G ⧸ U) = y := huniq _ (hq s hs hs')
    have h4 : ((y.out : G) : G ⧸ U) = (s : G ⧸ U) := by
      rw [h3]; exact QuotientGroup.out_eq' y
    exact QuotientGroup.eq.1 h4
  · rintro ⟨r, ⟨hr1, hr2⟩, hall⟩
    refine ⟨(r : G ⧸ U), hq r hr1 hr2, fun y hy => ?_⟩
    have h5 := hall _ hy.1 hy.2
    have h6 : (r : G ⧸ U) = ((y.out : G) : G ⧸ U) := QuotientGroup.eq.2 h5
    rw [h6]
    exact (QuotientGroup.out_eq' y).symm

private theorem reps_of_finOrb (U : Subgroup G) (a : G) (h : AlgebraTools.FinOrb U U a) :
    ∃ R : Finset G, (∀ y ∈ R, y ∈ DC U a) ∧ (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) := by
  classical
  have hf : (MulAction.orbit U (a : G ⧸ U)).Finite := h
  have hmk : ∀ y ∈ DC U a, (y : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro y ⟨u, hu, w, hw, rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * w : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using hw
  refine ⟨hf.toFinset.image (fun q : G ⧸ U => q.out), ?_, ?_⟩
  · intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨u, rfl⟩ := hf.mem_toFinset.1 hq
    have h1 : ((Quotient.out (u • (a : G ⧸ U)) : G) : G ⧸ U) = ((u * a : G) : G ⧸ U) :=
      QuotientGroup.out_eq' _
    have h2 := QuotientGroup.eq.1 h1
    refine ⟨u, u.2, _, U.inv_mem h2, ?_⟩
    group
  · intro y hy
    refine ⟨Quotient.out (y : G ⧸ U), ⟨?_, out_inv_mul_mem U y⟩, ?_⟩
    · exact Finset.mem_image.2 ⟨_, hf.mem_toFinset.2 (hmk y hy), rfl⟩
    · rintro r ⟨hr, hr'⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hr
      have h3 : ((q.out : G) : G ⧸ U) = (y : G ⧸ U) := QuotientGroup.eq.2 hr'
      have h4 : q = (y : G ⧸ U) := (QuotientGroup.out_eq' q).symm.trans h3
      rw [h4]

private theorem finOrb_of_cover (U : Subgroup G) (a : G) (R : Finset G)
    (h : ∀ y ∈ DC U a, ∃ r ∈ R, r⁻¹ * y ∈ U) : AlgebraTools.FinOrb U U a := by
  classical
  refine (R.image (fun r : G => (r : G ⧸ U))).finite_toSet.subset ?_
  rintro q ⟨u, rfl⟩
  obtain ⟨r, hr, hr'⟩ := h ((u : G) * a) ⟨u, u.2, 1, U.one_mem, by simp⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨r, hr, ?_⟩)
  exact QuotientGroup.eq.2 hr'

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcMap :
    UpperTheory.V.Z.Sym.So.DcMap := by
  classical
  intro G G' V _ _ _ _ e he U' a b
  set U := U'.comap e with hU
  set inv : G' → G := Function.surjInv he.2 with hinv
  have einv : ∀ x, e (inv x) = x := Function.surjInv_eq he.2
  have hDC : ∀ c g : G, g ∈ DC U c ↔ e g ∈ DC U' (e c) := by
    intro c g
    constructor
    · rintro ⟨u, hu, w, hw, rfl⟩
      exact ⟨e u, hu, e w, hw, by simp⟩
    · rintro ⟨u, hu, w, hw, h⟩
      refine ⟨inv u, ?_, inv w, ?_, he.1 ?_⟩
      · show e (inv u) ∈ U'
        rwa [einv]
      · show e (inv w) ∈ U'
        rwa [einv]
      · simp [einv, h]
  have hmem : ∀ x y : G, x⁻¹ * y ∈ U ↔ (e x)⁻¹ * e y ∈ U' := by
    intro x y
    show e (x⁻¹ * y) ∈ U' ↔ _
    simp
  have hfin : AlgebraTools.FinOrb U U a ↔ AlgebraTools.FinOrb U' U' (e a) := by
    constructor
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U a h
      refine finOrb_of_cover U' (e a) (R.image e) fun y' hy' => ?_
      have hy : inv y' ∈ DC U a := (hDC a _).2 (by rwa [einv])
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ hy
      refine ⟨e r, Finset.mem_image_of_mem _ hr, ?_⟩
      have := (hmem _ _).1 hr'
      rwa [einv] at this
    · intro h
      obtain ⟨R, -, hR⟩ := reps_of_finOrb U' (e a) h
      refine finOrb_of_cover U a (R.image inv) fun y hy => ?_
      obtain ⟨r, ⟨hr, hr'⟩, -⟩ := hR _ ((hDC a y).1 hy)
      refine ⟨inv r, Finset.mem_image_of_mem _ hr, (hmem _ _).2 ?_⟩
      rwa [einv]
  refine ⟨hDC a, hfin, ?_, ?_⟩
  · have hQ : ∀ g : G, (∃! y : G ⧸ U, y.out ∈ DC U a ∧ y.out⁻¹ * g ∈ DC U b) ↔
        ∃! y : G' ⧸ U', y.out ∈ DC U' (e a) ∧ y.out⁻¹ * e g ∈ DC U' (e b) := by
      intro g
      rw [uf_unique_iff, uf_unique_iff]
      have hin : ∀ (r : G), (r ∈ DC U a ∧ r⁻¹ * g ∈ DC U b) ↔
          (e r ∈ DC U' (e a) ∧ (e r)⁻¹ * e g ∈ DC U' (e b)) := by
        intro r
        rw [hDC a r, hDC b (r⁻¹ * g)]
        simp
      constructor
      · rintro ⟨r, hr, hall⟩
        refine ⟨e r, (hin r).1 hr, fun s' h1 h2 => ?_⟩
        have h3 := (hin (inv s')).2 (by rw [einv]; exact ⟨h1, h2⟩)
        have := (hmem _ _).1 (hall _ h3.1 h3.2)
        rwa [einv] at this
      · rintro ⟨r', hr', hall⟩
        have h0 := (hin (inv r')).2 (by rw [einv]; exact hr')
        refine ⟨inv r', h0, fun s h1 h2 => (hmem _ _).2 ?_⟩
        have h3 := (hin s).1 ⟨h1, h2⟩
        rw [einv]
        exact hall _ h3.1 h3.2
    have hR : ∀ g y : G, (y ∈ DC U a → y⁻¹ * g ∈ DC U b → g ∈ DC U (a * b)) ↔
        (e y ∈ DC U' (e a) → (e y)⁻¹ * e g ∈ DC U' (e b) → e g ∈ DC U' (e a * e b)) := by
      intro g y
      rw [hDC a y, hDC b (y⁻¹ * g), hDC (a * b) g]
      simp
    constructor
    · intro h g'
      have hg : e (inv g') = g' := einv g'
      obtain ⟨h1, h2⟩ := h (inv g')
      rw [← hg]
      refine ⟨fun hm => (hQ _).1 (h1 ((hDC _ _).2 (by simpa using hm))), fun y' hy1 hy2 => ?_⟩
      have := (hR (inv g') (inv y')).1 (h2 _)
      rw [einv] at this
      exact this hy1 hy2
    · intro h g
      obtain ⟨h1, h2⟩ := h (e g)
      refine ⟨fun hm => (hQ g).2 (h1 (by simpa using (hDC _ _).1 hm)), fun y hy1 hy2 => ?_⟩
      exact (hR g y).2 (h2 (e y)) hy1 hy2
  · intro hf φ hφ
    obtain ⟨R', hR1', hR2'⟩ := reps_of_finOrb U' (e a) hf
    have hφe : ∀ u ∈ U, ∀ g, (φ ∘ e) (g * u) = (φ ∘ e) g := by
      intro u hu g
      simp only [Function.comp_apply, map_mul]
      exact hφ _ hu _
    have hinj : Set.InjOn inv (R' : Set G') := fun x _ y _ h => by
      rw [← einv x, ← einv y, h]
    have hR1 : ∀ y ∈ R'.image inv, y ∈ DC U a := by
      intro y hy
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact (hDC a _).2 (by rw [einv]; exact hR1' r hr)
    have hR2 : ∀ y ∈ DC U a, ∃! r, r ∈ R'.image inv ∧ r⁻¹ * y ∈ U := by
      intro y hy
      obtain ⟨r, ⟨hr, hr'⟩, huniq⟩ := hR2' _ ((hDC a y).1 hy)
      refine ⟨inv r, ⟨Finset.mem_image_of_mem _ hr, (hmem _ _).2 (by rwa [einv])⟩, ?_⟩
      rintro s ⟨hs, hs'⟩
      obtain ⟨s', hs1, rfl⟩ := Finset.mem_image.1 hs
      have := (hmem _ _).1 hs'
      rw [einv] at this
      rw [huniq s' ⟨hs1, this⟩]
    funext g
    rw [(dcBasic G V U a (hfin.2 hf) (φ ∘ e) hφe).2.2.2.2 _ hR1 hR2 g, Function.comp_apply,
      (dcBasic G' V U' (e a) hf φ hφ).2.2.2.2 R' hR1' hR2' (e g), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [einv]

end
end

