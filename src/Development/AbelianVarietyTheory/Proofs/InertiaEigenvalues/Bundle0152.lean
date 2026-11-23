module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuCocycleCoboundaryLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.MuTowerInj

section Abstract

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]

def twoCocycleMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : Z2 ρ₁ →+ Z2 ρ₂ where
  toFun f := ⟨u ∘ f.1, (continuous_of_discreteTopology (f := u)).comp f.2.1, fun g h k => by
    simp only [Function.comp_apply, ← hu, ← map_sub, ← map_add (f := _), f.2.2 g h k, map_zero]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' f f' := Subtype.ext (funext fun _ => map_add u _ _)

def secondCohomologyMapOfEquivariantAdd (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) : H2 ρ₁ →+ H2 ρ₂ :=
  QuotientAddGroup.map ((B2 ρ₁).comap (Z2 ρ₁).subtype).toAddSubgroup
    ((B2 ρ₂).comap (Z2 ρ₂).subtype).toAddSubgroup (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₁ _).1 hf
    refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨u ∘ c, (continuous_of_discreteTopology (f := u)).comp hc, ?_⟩
    funext p
    have e := congrFun hcf p
    simp only [Submodule.coe_subtype] at e
    change _ = u (f.1 p)
    rw [← e]
    simp [d1, hu]

theorem mapH2Add_mk (ρ₁ : Representation R₁ Γ M₁) (ρ₂ : Representation R₂ Γ M₂) (u : M₁ →+ M₂)
    (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m)) (z : Z2 ρ₁) :
    secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (twoCocycleMapOfEquivariantAdd ρ₁ ρ₂ u hu z) := rfl

theorem ker_le_range [ContinuousMul Γ] (ρ₁ : Representation R₁ Γ M₁)
    (ρ₂ : Representation R₂ Γ M₂) (ρ₃ : Representation R₃ Γ M₃) (h₂ : ContAction ρ₂)
    (u : M₁ →+ M₂) (hu : ∀ g m, u (ρ₁ g m) = ρ₂ g (u m))
    (p : M₂ →+ M₃) (hp : ∀ g m, p (ρ₂ g m) = ρ₃ g (p m))
    (hinj : Function.Injective u) (hsurj : Function.Surjective p)
    (hex : ∀ m, p m = 0 → ∃ k, u k = m) :
    (secondCohomologyMapOfEquivariantAdd ρ₂ ρ₃ p hp).ker ≤ (secondCohomologyMapOfEquivariantAdd ρ₁ ρ₂ u hu).range := by
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [AddMonoidHom.mem_ker, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hx
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem ρ₃ _).1 hx

  have hsc : Continuous (Function.surjInv hsurj ∘ c) :=
    (continuous_of_discreteTopology (f := Function.surjInv hsurj)).comp hc
  have hb : d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ :=
    coboundaries2_le_cocycles2 ρ₂ h₂ ((separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨_, hsc, rfl⟩)
  have hf' : f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c) ∈ Z2 ρ₂ := (Z2 ρ₂).sub_mem f.2 hb

  have hker : ∀ q, p ((f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q) = 0 := by
    rintro ⟨g, h⟩
    have e : ρ₃ g (c h) - c (g * h) + c g = p (f.1 (g, h)) := by
      have e0 := congrFun hcf (g, h)
      rw [d1_apply] at e0
      exact e0
    rw [Pi.sub_apply, d1_apply, map_sub, map_add (f := _), map_sub, hp]
    simp only [Function.comp_apply, Function.surjInv_eq hsurj]
    rw [e, sub_self]
  obtain ⟨k, hk⟩ : ∃ k : Γ × Γ → M₁, ∀ q, u (k q) = (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) q :=
    ⟨fun q => Function.invFun u _, fun q => Function.invFun_eq (hex _ (hker q))⟩
  have hkc : Continuous k := by
    have hk' : k = Function.invFun u ∘ (f.1 - d1 ρ₂ (Function.surjInv hsurj ∘ c)) := by
      funext q
      rw [Function.comp_apply, ← hk q, Function.leftInverse_invFun hinj]
    rw [hk']
    exact (continuous_of_discreteTopology (f := Function.invFun u)).comp ((mem_cocycles2 ρ₂ _).1 hf').1
  have hkZ : k ∈ Z2 ρ₁ := by
    refine (mem_cocycles2 ρ₁ k).2 ⟨hkc, fun g h t => hinj ?_⟩
    rw [map_zero, map_sub, map_add (f := _), map_sub, hu, hk, hk, hk, hk]
    exact ((mem_cocycles2 ρ₂ _).1 hf').2 g h t
  refine AddMonoidHom.mem_range.2 ⟨Submodule.Quotient.mk ⟨k, hkZ⟩, ?_⟩
  rw [mapH2Add_mk, Submodule.Quotient.eq, Submodule.mem_comap]
  refine (separated_dvr_second_cohomology_mem ρ₂ _).2 ⟨-(Function.surjInv hsurj ∘ c), hsc.neg, ?_⟩
  funext q
  rw [map_neg, Pi.neg_apply]
  show _ = u (k q) - f.1 q
  rw [hk q, Pi.sub_apply]
  abel

theorem injective_of_card {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    (hc : Nat.card B = Nat.card A * Nat.card C) : Function.Injective f := by
  have eA : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have eB : Nat.card g.ker * Nat.card g.range = Nat.card B := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have h1 : Nat.card g.ker ≤ Nat.card f.range := AddSubgroup.card_le_of_le h
  have h2 : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpos : 0 < Nat.card f.range * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos

  have hk : Nat.card f.ker ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have hlt : Nat.card f.range * Nat.card C < Nat.card f.range * Nat.card C :=
      calc Nat.card f.range * Nat.card C
          < Nat.card f.ker * (Nat.card f.range * Nat.card C) := lt_mul_of_one_lt_left hpos hne
        _ = Nat.card A * Nat.card C := by rw [← eA, mul_assoc]
        _ = Nat.card B := hc.symm
        _ = Nat.card g.ker * Nat.card g.range := eB.symm
        _ ≤ Nat.card f.range * Nat.card C := Nat.mul_le_mul h1 h2
    exact lt_irrefl _ hlt
  rw [AddSubgroup.card_le_one_iff_eq_bot] at hk
  exact (AddMonoidHom.ker_eq_bot_iff f).1 hk

end Abstract

section Cyclic

variable (l : ℕ) [Fact l.Prime] (n : ℕ)

omit [Fact l.Prime] in
theorem pow_mul_val (x : ℕ) :
    ((l ^ n * (x : ZMod (l ^ 1)).val : ℕ) : ZMod (l ^ (n + 1))) = ((l ^ n * x : ℕ) : _) := by
  rw [ZMod.val_natCast, pow_one]
  conv_rhs => rw [← Nat.mod_add_div x l]
  rw [mul_add, Nat.cast_add, ← mul_assoc, ← pow_succ, Nat.cast_mul (l ^ (n + 1)), ZMod.natCast_self,
    zero_mul, add_zero]

def iota : ZMod (l ^ 1) →+ ZMod (l ^ (n + 1)) :=
  AddMonoidHom.mk' (fun b => ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1)))) fun a b => by
    obtain ⟨x, rfl⟩ := ZMod.natCast_zmod_surjective a
    obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
    rw [← Nat.cast_add, pow_mul_val, pow_mul_val, pow_mul_val, mul_add, Nat.cast_add]

theorem iota_apply (b : ZMod (l ^ 1)) :
    iota l n b = ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1))) := rfl

theorem iota_natCast (x : ℕ) : iota l n x = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
  rw [iota_apply, pow_mul_val]

theorem iota_injective : Function.Injective (iota l n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro b hb
  rw [iota_apply, CharP.cast_eq_zero_iff (ZMod (l ^ (n + 1))) (l ^ (n + 1)), pow_succ,
    Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : l.Prime).pos n)] at hb
  have hlt : b.val < l := by simpa using ZMod.val_lt b
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hb hlt

theorem iota_mul (u : ℤ_[l]) (b : ZMod (l ^ 1)) :
    iota l n (PadicInt.toZModPow 1 u * b) = PadicInt.toZModPow (n + 1) u * iota l n b := by
  obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
  set w := PadicInt.toZModPow (n + 1) u with hw

  have h1 : PadicInt.toZModPow 1 u = ((w.val : ℕ) : ZMod (l ^ 1)) := by
    rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply,
      ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : ((w.val : ℕ) : ZMod (l ^ (n + 1))) = w := ZMod.natCast_zmod_val w
  rw [h1, ← Nat.cast_mul, iota_natCast, iota_natCast]
  conv_rhs => rw [← h2]
  push_cast
  ring

def red : ZMod (l ^ (n + 1)) →+* ZMod (l ^ n) :=
  ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))

theorem red_toZModPow (u : ℤ_[l]) :
    red l n (PadicInt.toZModPow (n + 1) u) = PadicInt.toZModPow n u := by
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) u

omit [Fact l.Prime] in
theorem red_surjective : Function.Surjective (red l n) := by
  exact ZMod.ringHom_surjective (red l n)

theorem exists_iota_of_red (m : ZMod (l ^ (n + 1))) (hm : red l n m = 0) :
    ∃ k, iota l n k = m := by
  have h0 : ((m.val : ℕ) : ZMod (l ^ n)) = 0 := by
    rw [← ZMod.cast_eq_val]
    exact hm
  rw [CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n)] at h0
  obtain ⟨t, ht⟩ := h0
  exact ⟨t, by rw [iota_natCast, ← ht, ZMod.natCast_zmod_val]⟩

end Cyclic

theorem card_H2_muLoc (hD : LocalTateDuality) (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsPlaceOver A v) (r : ℕ) :
    Nat.card (H2 (muLoc F l r A)) = l ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  ·
    have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    have : Subsingleton (H2 (muLoc F l 0 A)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (funext fun _ => Subsingleton.elim _ _))⟩
    exact (Nat.card_of_subsingleton (0 : H2 (muLoc F l 0 A))).trans (pow_zero l).symm
  · obtain ⟨⟨e⟩, -⟩ := hD F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
      (GlobalTheory.TameQuot.contAction_muDec A l r)
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_zmod _)

theorem mk_eq_zero_of_coboundary : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (n : ℕ) (w : Z2 (muLoc F l 1 A)) (a : Dec (F := F) A → ZMod (l ^ (n + 1))), Continuous a → (∀ g h : Dec (F := F) A, ((cycMod F Ω l (n + 1) g : (ZMod (l ^ (n + 1)))ˣ) : ZMod (l ^ (n + 1))) * a h - a (g * h) + a g = ((l ^ n * (w.1 (g, h)).val : ℕ) : ZMod (l ^ (n + 1)))) → (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  intro hD F Ω _ _ _ _ _ l _ A v hA n w a ha hrel

  have hu : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ 1)),
      iota l n (muLoc F l 1 A g m) = muLoc F l (n + 1) A g (iota l n m) := fun g m =>
    iota_mul l n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) m
  have hp : ∀ (g : Dec (F := F) A) (m : ZMod (l ^ (n + 1))),
      (red l n).toAddMonoidHom (muLoc F l (n + 1) A g m) =
        muLoc F l n A g ((red l n).toAddMonoidHom m) := by
    intro g m
    show red l n (PadicInt.toZModPow (n + 1) ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * m) =
      PadicInt.toZModPow n ((cycZ F Ω l (g : G F Ω) : ℤ_[l]ˣ) : ℤ_[l]) * red l n m
    rw [map_mul, red_toZModPow]
  have hcard : ∀ r, Nat.card (H2 (muLoc F l r A)) = l ^ r := card_H2_muLoc hD F Ω l A v hA
  have : ∀ r, Finite (H2 (muLoc F l r A)) := fun r =>
    Nat.finite_of_card_ne_zero (by rw [hcard r]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)

  have hinj := injective_of_card
    (secondCohomologyMapOfEquivariantAdd (muLoc F l 1 A) (muLoc F l (n + 1) A) (iota l n) hu)
    (secondCohomologyMapOfEquivariantAdd (muLoc F l (n + 1) A) (muLoc F l n A) (red l n).toAddMonoidHom hp)
    (ker_le_range _ _ _ (GlobalTheory.TameQuot.contAction_muDec A l (n + 1)) _ hu _ hp
      (iota_injective l n) (red_surjective l n) (exists_iota_of_red l n))
    (by rw [hcard, hcard, hcard]; ring)
  apply hinj
  rw [map_zero, mapH2Add_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨a, ha, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply]
  exact (hrel g h).trans (iota_apply l n _).symm

end GlobalTheory.MuTowerInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGlOrbitEqFourierEtaleKProd
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

theorem map_pair_selfDual {F : Type} [NontriviallyNormedField F] [LocallyCompactSpace F] [MeasurableSpace F]
    [BorelSpace F] {r : ℕ} {V : Type} [AddCommGroup V] [Module F V] [TopologicalSpace V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V] [MeasurableSpace V] [BorelSpace V]
    (ψ : AddChar F ℂ) (B : V → V → F) (hBs : ∀ x y, B x y = B y x)
    (e₁ e₂ : V ≃ₗ[F] (Fin r → F)) (hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = B x y)
    (μV : Measure V) (hV : SelfDual μV (fun x y => ψ (B x y)))
    (ν : Measure (Fin r → F)) (hν : SelfDual ν (fun x y => ψ (x ⬝ᵥ y)))
    (h₀ : (Fin r → F) → ℂ) (ht₀ : IsTest h₀) (h₀0 : h₀ 0 = 1) :
    ∃ c₁ c₂ : ℂ, (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₁ x) ∂μV = c₁ * ∫ y, φ y ∂ν) ∧
      (∀ φ : (Fin r → F) → ℂ, ∫ x, φ (e₂ x) ∂μV = c₂ * ∫ y, φ y ∂ν) ∧ c₁ * c₂ = 1 := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI := hV.1
  haveI := hν.1
  let E₁ : V ≃L[F] (Fin r → F) :=
    { e₁ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₁.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₁.symm.toLinearMap }
  let E₂ : V ≃L[F] (Fin r → F) :=
    { e₂ with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₂.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₂.symm.toLinearMap }
  haveI : (Measure.map E₁ μV).IsAddHaarMeasure := E₁.isAddHaarMeasure_map μV
  haveI : (Measure.map E₂ μV).IsAddHaarMeasure := E₂.isAddHaarMeasure_map μV
  have hm₁ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₁ μV) ν
  have hm₂ := Measure.isAddLeftInvariant_eq_smul (Measure.map E₂ μV) ν
  set c₁ := (Measure.map E₁ μV).addHaarScalarFactor ν
  set c₂ := (Measure.map E₂ μV).addHaarScalarFactor ν
  let M₁ := E₁.toHomeomorph.toMeasurableEquiv
  let M₂ := E₂.toHomeomorph.toMeasurableEquiv
  have hM₁ : ∀ x, M₁ x = e₁ x := fun _ => rfl
  have hM₂ : ∀ x, M₂ x = e₂ x := fun _ => rfl
  have hmap : ∀ (M : V ≃ᵐ (Fin r → F)) (c : ENNReal), Measure.map M μV = c • ν →
      ∀ φ : (Fin r → F) → ℂ, ∫ x, φ (M x) ∂μV = (c.toReal : ℂ) * ∫ y, φ y ∂ν := by
    intro M c hc φ
    rw [← integral_map_equiv M φ, hc, integral_smul_measure, Complex.real_smul]
  set FF := fourB ν (fun x y => ψ (x ⬝ᵥ y))
  set FV := fourB μV (fun x y => ψ (B x y))
  set f : V → ℂ := h₀ ∘ E₁
  have hf : IsTest f := ⟨ht₀.1.comp_continuous E₁.continuous, ht₀.2.comp_homeomorph E₁.toHomeomorph⟩
  have ha : ∀ c, FV f c = (c₁ : ℂ) * FF h₀ (e₂ c) := by
    intro c
    have := hmap M₁ c₁ hm₁ (fun y => h₀ y * ψ (y ⬝ᵥ e₂ c))
    simp only [hM₁, ENNReal.coe_toReal] at this
    simp only [FV, FF, fourB, f, Function.comp_apply]
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← hB]; rfl
  have hb : ∀ b, FV (FV f) b = (c₁ : ℂ) * (c₂ : ℂ) * FF (FF h₀) (e₁ b) := by
    intro b
    have := hmap M₂ c₂ hm₂ (fun y => FF h₀ y * ψ (y ⬝ᵥ e₁ b))
    simp only [hM₂, ENNReal.coe_toReal] at this
    show ∫ c, FV f c * ψ (B c b) ∂μV = _
    simp only [ha]
    have e : ∀ c, (c₁ : ℂ) * FF h₀ (e₂ c) * ψ (B c b) = (c₁ : ℂ) * (FF h₀ (e₂ c) * ψ (e₂ c ⬝ᵥ e₁ b)) := by
      intro c; rw [hBs, ← hB, dotProduct_comm, mul_assoc]
    simp only [e]
    rw [integral_const_mul, this, mul_assoc]
    rfl
  refine ⟨c₁, c₂, fun φ => ?_, fun φ => ?_, ?_⟩
  · have := hmap M₁ c₁ hm₁ φ; simpa only [hM₁, ENNReal.coe_toReal] using this
  · have := hmap M₂ c₂ hm₂ φ; simpa only [hM₂, ENNReal.coe_toReal] using this
  have h1 := hb 0
  have h3 : FV (FV f) 0 = f (-0) := hV.2 f hf 0
  have h4 : FF (FF h₀) 0 = h₀ (-0) := hν.2 h₀ ht₀ 0
  rw [h3, map_zero, h4] at h1
  simp only [neg_zero, f, Function.comp_apply, map_zero, h₀0, mul_one] at h1
  rw [← h1]

theorem pi_selfDual (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] [MeasurableSpace F] [BorelSpace F] (μF : Measure F) [μF.IsAddHaarMeasure]
    (hvol : μF (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) :
    SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (x ⬝ᵥ y)) ∧
      IsTest ((Set.univ.pi fun _ : Fin r => Metric.closedBall (0 : F) 1).indicator 1) := by
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  set S : Set (Fin r → F) := Set.univ.pi fun _ => Metric.closedBall 0 1 with hSdef
  have hmem : ∀ y : Fin r → F, y ∈ S ↔ ∀ i, ‖y i‖ ≤ 1 := by
    intro y; simp [S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hSo : IsOpen S :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hSc : IsCompact S := isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hScl : IsClosed S := isClosed_set_pi fun _ _ => Metric.isClosed_closedBall
  let Mg : AddSubgroup (Fin r → F) :=
    { carrier := S
      zero_mem' := by rw [hmem]; simp
      add_mem' := by
        intro a b ha hb
        rw [hmem] at ha hb ⊢
        intro i; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
      neg_mem' := by
        intro a ha
        rw [hmem] at ha ⊢
        intro i; simpa using ha i }
  have hMg : (Mg : Set (Fin r → F)) = S := rfl
  let β : LinearMap.BilinForm F (Fin r → F) := Matrix.toBilin' 1
  have hβ : ∀ x y, β x y = x ⬝ᵥ y := by intro x y; simp [β, Matrix.toBilin'_apply']
  have hβs : β.IsSymm := by
    first
    | exact ⟨fun x y => by simp [hβ, dotProduct_comm]⟩
    | exact fun x y => by simp [hβ, dotProduct_comm]
  have hβn : β.Nondegenerate := Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have key := (_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ (Fin r → F) β hβs hβn (Measure.pi fun _ => μF) inferInstance).1 Mg
    (by rw [hMg]; exact hSo) (by rw [hMg]; exact hSc)
  have hdual : {y | ∀ x ∈ Mg, ψ (β x y) = 1} = S := by
    ext y
    simp only [Set.mem_setOf_eq, hβ]
    constructor
    · intro h
      rw [hmem]
      intro i
      by_contra hi
      push_neg at hi
      obtain ⟨x0, hx0, hx0'⟩ := hψ.2
      have hyi : y i ≠ 0 := by intro h0; rw [h0, norm_zero] at hi; linarith
      have hsmall : ‖(y i)⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hi
      have hx : Pi.single i (x0 * (y i)⁻¹) ∈ Mg := by
        show _ ∈ S
        rw [hmem]
        intro j
        by_cases hj : j = i
        · subst hj; simp only [Pi.single_eq_same]; exact hx0' _ hsmall
        · simp [Pi.single_eq_of_ne hj]
      have h2 := h _ hx
      have e : Pi.single i (x0 * (y i)⁻¹) ⬝ᵥ y = x0 := by
        simp only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [mul_assoc, inv_mul_cancel₀ hyi, mul_one]
      rw [e] at h2
      exact hx0 h2
    · intro hy x hx
      have hx' : x ∈ S := hx
      rw [hmem] at hy hx'
      apply hψ.1
      simp only [dotProduct]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]; exact mul_le_one₀ (hx' i) (norm_nonneg _) (hy i)
  have hvolS : (Measure.pi fun _ : Fin r => μF) S = 1 := by
    rw [hSdef, Measure.pi_pi]; simp [hvol]
  have hsd : SelfDual (Measure.pi fun _ : Fin r => μF) (fun x y => ψ (β x y)) :=
    key.1.2 (by rw [hdual, hMg, hvolS, one_mul])
  refine ⟨?_, ?_⟩
  · have e : (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) = (fun x y => ψ (β x y)) := by funext x y; rw [hβ]
    rw [e]; exact hsd
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hScl, hSo⟩).isLocallyConstant,
      HasCompactSupport.intro hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem fourG_act_pt_eq_fourK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ f' : Gl r F → ℂ, IsTest f' → ∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c) := by
  intro F E _ _ _ _ hU A r τ p hG lam M ψ hψ μK hK f' _ g b c
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI := hU.lcF
  obtain ⟨hsd, ht0⟩ := pi_selfDual F E M.μF M.volF ψ hψ r
  set ν : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hν
  let gm : Matrix (Fin r) (Fin r) F := (g : Matrix (Fin r) (Fin r) F)
  let gi : Matrix (Fin r) (Fin r) F := ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
  have hgig : gi * gm = 1 := by simp [gi, gm]
  have hggi : gm * gi = 1 := by simp [gi, gm]
  let gL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => gm *ᵥ v
      invFun := fun v => gi *ᵥ v
      map_add' := fun v w => mulVec_add _ _ _
      map_smul' := fun a v => by simp [mulVec_smul]
      left_inv := fun v => by simp [mulVec_mulVec, hgig]
      right_inv := fun v => by simp [mulVec_mulVec, hggi] }
  let hL : (Fin r → F) ≃ₗ[F] (Fin r → F) :=
    { toFun := fun v => v ᵥ* gi
      invFun := fun v => v ᵥ* gm
      map_add' := fun v w => add_vecMul _ _ _
      map_smul' := fun a v => by simp [smul_vecMul]
      left_inv := fun v => by simp [vecMul_vecMul, hgig]
      right_inv := fun v => by simp [vecMul_vecMul, hggi] }
  let ρL : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun c i => Algebra.trace F A.K (τ ^ (i : ℕ) * c)
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro a x; funext i; simp [mul_smul_comm] }
  have hρ : Function.Bijective ρL := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let e₁ : A.K ≃ₗ[F] (Fin r → F) := (bas A hG).equivFun.trans gL
  let e₂ : A.K ≃ₗ[F] (Fin r → F) := (LinearEquiv.ofBijective ρL hρ).trans hL
  have he₁ : ∀ x, e₁ x = gm *ᵥ (bas A hG).equivFun x := fun _ => rfl
  have he₂ : ∀ x, e₂ x = (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * x)) ᵥ* gi := fun _ => rfl
  have hB : ∀ x y, e₁ x ⬝ᵥ e₂ y = Algebra.trace F A.K (x * y) := by
    intro x y
    rw [he₁, he₂, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hgig, one_mulVec]
    conv_rhs => rw [← (bas A hG).sum_equivFun x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bas_apply, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
  obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := map_pair_selfDual ψ (fun x y => Algebra.trace F A.K (x * y))
    (fun x y => by rw [mul_comm]) e₁ e₂ hB μK hK ν hsd _ ht0 (by simp)
  let X : Matrix (Fin r) (Fin r) F := gm * companion p * gi
  let G : (Fin r → F) → (Fin r → F) → ℂ := fun x y => f' (X, x, y, lam) * ψ (y ⬝ᵥ e₁ b + e₂ c ⬝ᵥ x)
  have lhs : fourG M ψ f' (act g (pt A hG lam b c)) = ∫ x, (∫ y, G x y ∂ν) ∂ν := rfl
  have rhs : A.fourK μK ψ (fun x => f' (act g (pt A hG lam x.1 x.2))) (b, c) =
      ∫ x, (∫ y, G (e₁ x) (e₂ y) ∂μK) ∂μK := by
    unfold Et.fourK
    refine integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun y => ?_))
    show f' (act g (pt A hG lam x y)) * A.psiK ψ (b * y + x * c) = G (e₁ x) (e₂ y)
    simp only [G]
    congr 1
    rw [Et.psiK, map_add (f := _), ← hB, ← hB, dotProduct_comm (e₁ b), dotProduct_comm (e₁ x)]
  rw [lhs, rhs]
  have inner : ∀ x, ∫ y, G (e₁ x) (e₂ y) ∂μK = c₂ * ∫ y, G (e₁ x) y ∂ν := fun x => h₂ (fun y => G (e₁ x) y)
  rw [integral_congr_ae (Eventually.of_forall inner), integral_const_mul, h₁ (fun x => ∫ y, G x y ∂ν)]
  rw [← mul_assoc, mul_comm c₂, hc, one_mul]

end GlobalTheory.JR.LinDesc
end
end

