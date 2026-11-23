module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicIntegralReadingOfTrivialisations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTranslatedMembersLeadingTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem gs_scal_one {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) : gs (𝟙 Y) y ⊤ (scal p 1) = 1 := by
  have h : scal p (1 : R) = 1 := by simp [scal]
  rw [h, gs_eq _ y ⊤ trivial, map_one, map_one]

theorem secScal_generic (D : DegData R (maximalIdeal R)) (k : ℕ) (α : D.toPre.X) (b : D.toPre.SecB k α) :
    GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k)
      (GlobalTheory.FieldBaseChange.genericTerm D k α b) (D.toPre.famφB α) (DegPre.famε k) b
      (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
  refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  exact (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm.trans
    ((_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_one _ y).symm))

theorem lead_units {X : Type} [AddCommGroup X] (κ κ' : X → (FractionRing R)ˣ) (u : X → Rˣ)
    (hu : ∀ a, ((κ' a : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u a : R))
    (k : ℕ) (α mu : X) :
    ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) = (lead κ' k α mu : FractionRing R) *
      algebraMap R (FractionRing R) (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R) := by
  have e : ∀ x : Rˣ, algebraMap R (FractionRing R) ((x⁻¹ : Rˣ) : R) = (algebraMap R (FractionRing R) (x : R))⁻¹ :=
    fun x => map_units_inv (algebraMap R (FractionRing R) : R →* FractionRing R) x
  have ne : ∀ x : Rˣ, algebraMap R (FractionRing R) (x : R) ≠ 0 := fun x =>
    (x.isUnit.map (algebraMap R (FractionRing R))).ne_zero
  have h₁ := ne (u mu); have h₂ := ne (u (mu + α)); have h₃ := ne (u α)
  have h₄ := (κ mu).ne_zero; have h₅ := (κ (mu + α)).ne_zero; have h₆ := (κ α).ne_zero
  simp only [lead, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu, e, map_mul, map_pow]
  field_simp
  ring

theorem core (hR : Base R) (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ)
    (hκ : Reads D.toPre κ) (κ' : D.toPre.X → (FractionRing R)ˣ)
    (hu : ∀ a, ∃ u : Rˣ, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (k : ℕ) (hk : 1 ≤ k) (α : D.toPre.X)
    (h1 : ∀ mu, mu ≠ 0 → ∃ s ∈ maximalIdeal R,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s)
    (h2 : ∀ n : ℕ, {mu | ¬ ∃ s ∈ maximalIdeal R ^ n,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s}.Finite)
    (b : D.toPre.SecB k α) : ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b := by
  classical
  choose u hu using hu
  have inj := IsFractionRing.injective R (FractionRing R)
  have h1' : ∀ mu, ∃ s : R, mu ≠ 0 → s ∈ maximalIdeal R ∧
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := fun mu => by
    by_cases h : mu = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨s, hs, e⟩ := h1 mu h
      exact ⟨s, fun _ => ⟨hs, e⟩⟩
  choose s hs using h1'
  let w : D.toPre.X → R := fun mu => (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R)
  let r : D.toPre.X → R := fun mu => s mu * w mu
  have hr : ∀ mu, mu ≠ 0 → algebraMap R (FractionRing R) (r mu) =
      ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) ∧ r mu ∈ maximalIdeal R := fun mu h =>
    ⟨by rw [lead_units κ κ' u hu k α mu, (hs mu h).2, map_mul], Ideal.mul_mem_right _ _ (hs mu h).1⟩
  have key : ∀ mu, mu ≠ 0 → ∀ e : ℕ, r mu ∉ maximalIdeal R ^ (e + 1) → ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s' := by
    rintro mu h e hn ⟨s', hs'm, hs'e⟩
    have : s mu = s' := inj ((hs mu h).2.symm.trans hs'e)
    exact hn (Ideal.mul_mem_right _ _ (this ▸ hs'm))
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hcls : ∀ a c : D.toPre.X, α + k • a = α + k • c → a = c := fun a c h => by
    have h' : (k : ℤ) • a = (k : ℤ) • c := by simpa using add_left_cancel h
    exact smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) h'
  obtain ⟨F, hFα, hF0⟩ := ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult k α hcls
    (GlobalTheory.FieldBaseChange.genericTerm D k α b)
  have hb : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
      (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
    rw [hFα]; exact secScal_generic D k α b
  have hex : ∀ β : D.toPre.X, ∃ g : D.toPre.SecB k β, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) β)
      (DegPre.famε k) (F.s β) (D.toPre.famφB β) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ (β ≠ α → VanMod (maximalIdeal R) g 0 ∧
        ∀ e : ℕ, ¬ VanMod (maximalIdeal R) g e → ∃ mu, α + k • mu = β ∧ ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
          ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s') := by
    intro β
    by_cases hβ : β = α
    · subst hβ
      exact ⟨b, hb, fun h => absurd rfl h⟩
    by_cases hc : ∃ mu, α + k • mu = β
    · obtain ⟨mu, rfl⟩ := hc
      have hmu : mu ≠ 0 := by
        rintro rfl
        exact hβ (by simp)
      obtain ⟨f, hf1, hf2⟩ := _root_.GlobalTheory.ThFam.member_integral R hR D κ hκ k hk α b F hb mu (r mu) (hr mu hmu).1
      refine ⟨f, hf1, fun _ => ⟨hf2 0 (by simpa using (hr mu hmu).2), fun e he => ⟨mu, rfl, ?_⟩⟩⟩
      exact key mu hmu e (fun h => he (hf2 e h))
    · push_neg at hc
      refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero, ?_, fun _ => ⟨fun j => map_zero _, fun e he => absurd (fun j => map_zero _) he⟩⟩
      refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _),
        ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (hF0 β hc) _ y J (hJ.mem _ _), mul_zero]
  choose g hg using hex
  refine ⟨⟨F, Function.update g α b, fun β => ?_, fun e => ?_⟩, Function.update_self α b g, fun β hβ => ?_⟩
  · by_cases h : β = α
    · subst h
      rw [Function.update_self]
      exact hb
    · rw [Function.update_of_ne h]
      exact (hg β).1
  · refine (((h2 (e + 1)).image (fun mu => α + k • mu)).insert α).subset fun β hβ => ?_
    by_cases h : β = α
    · exact Or.inl h
    · right
      have hβ' : ¬ VanMod (maximalIdeal R) (g β) e := by
        have := hβ
        simp only [Set.mem_setOf_eq] at this
        rwa [Function.update_of_ne h] at this
      obtain ⟨mu, hmu, hn⟩ := ((hg β).2 h).2 e hβ'
      exact ⟨mu, hn, hmu⟩
  · show VanMod (maximalIdeal R) (Function.update g α b β) 0
    rw [Function.update_of_ne hβ]
    exact ((hg β).2 hβ).1

theorem exists_intFam_lead : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α,
      ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  intro R _ _ _ hR D
  haveI := hR.1.1
  haveI := hR.1.2.2.1
  obtain ⟨κ, hκ, hev, hcub, hpos, htend⟩ := _root_.GlobalTheory.ThFamRead.exists_reading R hR D
  obtain ⟨κ', hev', hcub', hu⟩ := GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing R D.toPre.X κ hev hcub
  have hu0 := hu
  choose u hu' using hu0
  have hpos' : ∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R (FractionRing R) s := fun a ha => by
    obtain ⟨s, hs, e⟩ := hpos a ha
    exact ⟨s * u a, Ideal.mul_mem_right _ _ hs, by rw [hu' a, e, map_mul]⟩
  have h0 : κ' 0 = 1 := by
    have := hcub' 0 0 0
    simp only [add_zero] at this
    exact mul_eq_left.1 this
  refine ⟨fun α => ?_, fun k hk b => ?_⟩
  · obtain ⟨k₁, H⟩ := _root_.GlobalTheory.LeadTerm.lead_mem R D.toPre.X κ' hev' hcub' hpos' α
    exact ⟨max k₁ 1, fun k hk b => core hR D κ hκ κ' hu k (le_of_max_le_right hk) α
      (H k (le_of_max_le_left hk)).1 (H k (le_of_max_le_left hk)).2 b⟩
  · have hl : ∀ mu, lead κ' k 0 mu = κ' mu ^ k := fun mu => by
      simp [lead, h0]
    refine core hR D κ hκ κ' hu k hk 0 (fun mu hmu => ?_) (fun n => ?_) b
    · obtain ⟨s, hs, e⟩ := hpos' mu hmu
      exact ⟨s ^ k, Ideal.pow_mem_of_mem _ hs k (by omega), by rw [hl, Units.val_pow_eq_pow_val, e, map_pow]⟩
    · refine (htend n).subset fun mu hmu h => hmu ?_
      obtain ⟨s, hs, e⟩ := h
      refine ⟨(s * u mu) ^ k, Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ hs) k (by omega), ?_⟩
      rw [hl, Units.val_pow_eq_pow_val, hu' mu, e, ← map_mul, ← map_pow]

end GlobalTheory.ThFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetracts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RetractPullback

theorem exists_isGrpPullback_of_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  intro S S' B j f G _ G' _ P _ φ ψ hφ hψ e e₀ e' he' h₁ h₂ H _ i r hi hr hir hri C _ k p hk hp hkp hpk
  have hb := isGrpPullback_pullback C f
  have wk : k.left ≫ P.hom = C.hom := Over.w k
  have wp : p.left ≫ C.hom = P.hom := Over.w p
  have wi : i.left ≫ G.hom = H.hom := Over.w i
  have wr : r.left ≫ H.hom = G.hom := Over.w r
  have we' : e'.left ≫ G'.hom = G'.hom := Over.w e'
  have kp : k.left ≫ p.left = 𝟙 _ := by rw [← Over.comp_left, hkp]; rfl
  have pk : p.left ≫ k.left = e₀.left := by rw [← Over.comp_left, hpk]
  have ir : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir]; rfl
  have ri : r.left ≫ i.left = e.left := by rw [← Over.comp_left, hri]
  have hmw : (pullback.fst C.hom f ≫ k.left) ≫ P.hom = pullback.snd C.hom f ≫ f := by
    rw [Category.assoc, wk]; exact pullback.condition
  let m : pullback C.hom f ⟶ G'.left := hψ.1.lift (pullback.fst C.hom f ≫ k.left) (pullback.snd C.hom f) hmw
  have mψ : m ≫ ψ = pullback.fst C.hom f ≫ k.left := hψ.1.lift_fst _ _ _
  have mh : m ≫ G'.hom = pullback.snd C.hom f := hψ.1.lift_snd _ _ _
  have fix : ∀ {T : Scheme.{0}} (x : T ⟶ pullback C.hom f), x ≫ m ≫ e'.left = x ≫ m := by
    intro T x
    apply hψ.1.hom_ext
    · simp only [Category.assoc, h₂, reassoc_of% mψ, mψ, ← pk, reassoc_of% kp]
    · simp only [Category.assoc, we']
  refine ⟨(Over.pullback f).obj C, inferInstance, m ≫ φ ≫ r.left, pullback.fst C.hom f, ⟨?_, ?_⟩, hb⟩
  · have comm : (m ≫ φ ≫ r.left) ≫ H.hom = pullback.snd C.hom f ≫ j := by
      rw [Category.assoc, Category.assoc, wr, hφ.1.w, reassoc_of% mh]
    refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm (fun s => pullback.lift
        (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left) s.snd
        (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc])) ?_ ?_ ?_⟩⟩
    · intro s
      have hm : pullback.lift (hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ ψ ≫ p.left)
          s.snd (by simp only [Category.assoc, wp, hψ.1.w, hφ.1.lift_snd_assoc]) ≫ m =
          hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) ≫ e'.left := by
        apply hψ.1.hom_ext
        · simp only [Category.assoc, mψ, h₂, pullback.lift_fst_assoc, pk]
        · simp only [Category.assoc, mh, we', pullback.lift_snd, hφ.1.lift_snd]
      rw [reassoc_of% hm, reassoc_of% h₁, hφ.1.lift_fst_assoc, ← ri]
      simp only [Category.assoc, reassoc_of% ir, ir, Category.comp_id]
    · intro s
      exact pullback.lift_snd _ _ _
    · intro s n hn1 hn2
      have hx : n ≫ m = hφ.1.lift (s.fst ≫ i.left) s.snd (by rw [Category.assoc, wi, s.condition]) := by
        apply hφ.1.hom_ext
        · rw [hφ.1.lift_fst, ← hn1]
          calc (n ≫ m) ≫ φ = n ≫ m ≫ e'.left ≫ φ := by rw [reassoc_of% (fix n), Category.assoc]
            _ = _ := by rw [h₁, ← ri]; simp only [Category.assoc]
        · rw [hφ.1.lift_snd, Category.assoc, mh]; exact hn2
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← reassoc_of% hx, reassoc_of% mψ, kp, Category.comp_id]
      · rw [pullback.lift_snd]; exact hn2
  · intro T x y x₀ y₀ hx hy
    let M : (Over.pullback f).obj C ⟶ G' := Over.homMk m mh
    have pt : ∀ z : T ⟶ (Over.pullback f).obj C, pushPt hψ.1.w (z ≫ M) = pushPt hb.1.w z ≫ k :=
      fun z => Over.OverMorphism.ext (by
        show (z.left ≫ m) ≫ ψ = (z.left ≫ pullback.fst C.hom f) ≫ k.left
        rw [Category.assoc, mψ, Category.assoc])
    have Mmul : (x * y) ≫ M = (x ≫ M) * (y ≫ M) := by
      apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have e1 := hb.2 T x y (pushPt hb.1.w x) (pushPt hb.1.w y) rfl rfl
        have e2 := hψ.2 T (x ≫ M) (y ≫ M) (pushPt hψ.1.w (x ≫ M)) (pushPt hψ.1.w (y ≫ M)) rfl rfl
        rw [← e2, pt, pt, ← MonObj.mul_comp]
        show ((x * y).left ≫ m) ≫ ψ = (pushPt hb.1.w x * pushPt hb.1.w y).left ≫ k.left
        rw [e1, Category.assoc, mψ, Category.assoc]
      · rw [Over.w ((x * y) ≫ M), Over.w ((x ≫ M) * (y ≫ M))]
    have ex : x₀ = pushPt hφ.1.w (x ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hx]; show _ = ((x.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have ey : y₀ = pushPt hφ.1.w (y ≫ M) ≫ r := Over.OverMorphism.ext (by
      rw [hy]; show _ = ((y.left ≫ m) ≫ φ) ≫ r.left; simp only [Category.assoc])
    have e3 := hφ.2 T (x ≫ M) (y ≫ M) (pushPt hφ.1.w (x ≫ M)) (pushPt hφ.1.w (y ≫ M)) rfl rfl
    rw [ex, ey, ← MonObj.mul_comp, Over.comp_left, e3, ← Mmul]
    show ((x * y).left ≫ m) ≫ φ ≫ r.left = _
    simp only [Category.assoc]

end GlobalTheory.RetractPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfJoinGen
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.PowData

section ProdPow

variable {X Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]

def prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (K := I × K) (fun p => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2)) where
  s := fun j => ∏ i, res ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)) :
      LB.wchart L (fun p : I × K => φ p.1 p.2) j ≤ LB.wchart L (φ i) (fun k => j (i, k)))
    ((t i).s fun k => j (i, k)) ^ n i

variable {L}

theorem val_prodZGen (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ) (n : I → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (prodZGen L φ ε n t) r z J = ∏ i, val (t i) r z J ^ n i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans ?_)
  exact congrArg (· ^ n i) (gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

theorem prodZGen_isGen (hL : L.IsLB) {φ : I → K → (Y ⟶ X)} {ε : I → K → ℤ} (n : I → ℤ)
    {t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))} (ht : ∀ i, (t i).IsGen) : (prodZGen L φ ε n t).IsGen := by
  intro j j'
  refine unit_ext fun y hy => ?_
  have m : ∀ (j : I × K → L.ι) (i : I), y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (φ i) (fun k => j (i, k)) :=
    fun _ i hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y _ ((prodZGen L φ ε n t).s j) = ∏ i, gm (𝟙 Y) y _ ((t i).s fun k => j (i, k)) ^ n i := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans
      (congrArg (· ^ n i) (gm_res _ y _ hj _)))
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy, v j hy.1, v j' hy.2]
  erw [gm_linComb L (fun p : I × K => φ p.1 p.2) (fun p => n p.1 * ε p.1 p.2) (𝟙 Y) y j j' hy.1 hy.2]
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  erw [gen_trans (ht i) (𝟙 Y) y (m j i hy.1) (m j' i hy.2)]
  rw [mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

end ProdPow

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

section JoinIso

variable {X X₁ X₂ Z : Scheme.{0}}

theorem part_gm_g_eq_one {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) (hM : M.IsLB)
    {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {i j : N.ι} (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) :
    gm f z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  subst hf
  rw [h.g _ ψ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

theorem part_gm_g_sec {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι} (h : IsPart N M e π) {σ : M.ι → N.ι}
    (hσ : ∀ i, π (σ i) = i) {ψ : Z ⟶ X₁} {f : Z ⟶ X} (hf : f = ψ ≫ e) {z : Z} {a b : M.ι} (ha : ψ z ∈ M.U a)
    (hb : ψ z ∈ M.U b) : gm f z (N.U (σ a) ⊓ N.U (σ b)) (N.g (σ a) (σ b)) = gm ψ z (M.U a ⊓ M.U b) (M.g a b) := by
  subst hf
  rw [h.g _ ψ z _ _ (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)]
  have : ∀ a b a' b', a = a' → b = b' → gm ψ z (M.U a ⊓ M.U b) (M.g a b) = gm ψ z (M.U a' ⊓ M.U b') (M.g a' b') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact this _ _ _ _ (hσ a) (hσ b)

variable {M₁ : LB X₁} {M₂ : LB X₂} {K : Type} [Fintype K]

theorem exists_iso_of_joinGen (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) [Nonempty X₁] [Nonempty X₂] {φ : K → (X₁ ⟶ X₂)}
    {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
      (Sum.elim ε (fun _ => -1)))) (ht : t.IsGen) :
    ∃ w : LB.Iso M₁ (LB.LinComb M₂ φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ X₁) (z : Z) (J),
      Good (join M₁ M₂) z J → gm p z _ (w.s (fun k => rr J (p ≫ φ k), rl J p)) = val t p z J := by
  have hp₁ := isPart_inl M₁ M₂
  have hp₂ := isPart_inr M₁ M₂
  choose σ₂ hσ₂ using snd_surjective (M₂ := M₂) h₁
  choose σ₁ hσ₁ using fst_surjective (M₁ := M₁) h₂
  let ix : (K → M₂.ι) × M₁.ι → K ⊕ PUnit → (join M₁ M₂).ι := fun a =>
    Sum.elim (fun k => σ₂ (a.1 k)) (fun _ => σ₁ a.2)
  have le : ∀ a, (LB.div (LB.LinComb M₂ φ ε) M₁).U a ≤
      LB.wchart (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) (ix a) :=
    fun a y hy => Set.mem_iInter.2 fun k => by
      rcases k with k | u
      · exact (hp₂.mem _ _).2 ((hσ₂ _).symm ▸ Set.mem_iInter.1 hy.1 k)
      · exact (hp₁.mem _ _).2 ((hσ₁ _).symm ▸ hy.2)
  let c : ChartPull (LB.div (LB.LinComb M₂ φ ε) M₁)
      (LB.LinComb (join M₁ M₂) (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl))
        (Sum.elim ε (fun _ => -1))) (𝟙 X₁) :=
    { idx := ix
      le := le
      g := fun y a b ha hb => by
        erw [gm_div M₁ (LB.LinComb M₂ φ ε) (𝟙 X₁) y a b ⟨ha, hb⟩, gm_linComb M₂ φ ε (𝟙 X₁) y a.1 b.1 ha.1 hb.1,
          gm_linComb (join M₁ M₂) _ _ (𝟙 X₁) y (ix a) (ix b) (le a ha) (le b hb)]
        rw [Fintype.prod_sum_type]
        simp only [Finset.univ_unique, Finset.prod_singleton]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) ?_
        · exact congrArg (· ^ ε k) (part_gm_g_sec hp₂ hσ₂ (ψ := 𝟙 X₁ ≫ φ k) (f := 𝟙 X₁ ≫ φ k ≫ coprod.inr)
            (Category.assoc _ _ _).symm (a := a.1 k) (b := b.1 k) (Set.mem_iInter.1 ha.1 k)
            (Set.mem_iInter.1 hb.1 k)).symm
        · refine (congrArg (·⁻¹) ?_).trans (zpow_neg_one _).symm
          refine Eq.trans ?_ (part_gm_g_sec hp₁ hσ₁ (ψ := 𝟙 X₁) (f := 𝟙 X₁ ≫ 𝟙 X₁ ≫ coprod.inl)
            (by rw [Category.id_comp]) (a := a.2) (b := b.2) ha.2 hb.2).symm
          rfl }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z p z J hJ => ?_⟩
  have m : p z ∈ (LB.div (LB.LinComb M₂ φ ε) M₁).U (fun k => rr J (p ≫ φ k), rl J p) :=
    ⟨(hp₂.good hJ).mem φ p, hp₁.good hJ p⟩
  have n := hJ.mem (Sum.elim (fun k => φ k ≫ coprod.inr) (fun _ : PUnit => 𝟙 X₁ ≫ coprod.inl)) p
  refine (gm_res p z _ m _).trans ((gen_trans ht p z (le _ m) n).trans ?_)
  refine (congrArg (· * val t p z J) ?_).trans (one_mul _)
  rw [trF, Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  refine (congrArg₂ (· * ·) (Finset.prod_eq_one fun k _ => ?_) ?_).trans (one_mul 1)
  · refine (congrArg (· ^ ε k) (part_gm_g_eq_one hp₂ h₂ (ψ := p ≫ φ k) (f := p ≫ φ k ≫ coprod.inr)
      (Category.assoc _ _ _).symm (i := σ₂ (rr J (p ≫ φ k))) (j := J (p ≫ φ k ≫ coprod.inr))
      ((hσ₂ _).trans (show (J ((p ≫ φ k) ≫ coprod.inr)).2 = _ by rw [Category.assoc])) ?_)).trans (one_zpow _)
    rw [hσ₂]; exact (hp₂.good hJ) (p ≫ φ k)
  · refine (congrArg (· ^ (-1 : ℤ)) (part_gm_g_eq_one hp₁ h₁ (ψ := p) (f := p ≫ 𝟙 X₁ ≫ coprod.inl)
      (by rw [Category.id_comp]) (i := σ₁ (rl J p)) (j := J (p ≫ 𝟙 X₁ ≫ coprod.inl))
      ((hσ₁ _).trans (show (J (p ≫ coprod.inl)).1 = _ by rw [Category.id_comp])) ?_)).trans (one_zpow _)
    rw [hσ₁]; exact hp₁.good hJ p

end JoinIso

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisedGroupsSameSiegelFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_iso_of_overPt : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  intro X g n B _ ζ sX c R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hp₁, β₁, hsq₁, hL₁⟩ := hO₁
  obtain ⟨hp₂, β₂, hsq₂, hL₂⟩ := hO₂
  obtain ⟨cA, hcA, hcα⟩ := grpPullback_iso hp₁ hp₂
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  haveI := hcA
  let e : (Over.pullback (jK R)).obj G₁ ≅ (Over.pullback (jK R)).obj G₂ := U₁.gen ≪≫ cA ≪≫ U₂.gen.symm
  haveI : IsMonHom e.hom := by
    show IsMonHom (U₁.gen.hom ≫ cA.hom ≫ U₂.gen.inv)
    infer_instance
  obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
    GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁ G₂ hG₁ hG₂ e
  refine ⟨a, cA, ha, hcA, ?_, hcα, ?_⟩
  · show (Over.pullback (jK R)).map a.hom ≫ U₂.gen.hom = U₁.gen.hom ≫ cA.hom
    rw [show (Over.pullback (jK R)).map a.hom = e.hom from hae]
    simp [e]
  · set β := (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left with hβdef
    have hβ : β ≫ β₂ = β₁ := by
      have h1 : (β ≫ β₂) ≫ (fst c.A c.A).left = β₁ ≫ (fst c.A c.A).left := by
        rw [Category.assoc, hsq₂.1, hsq₁.1, ← Category.assoc, hβdef, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, hcα]
      have h2 : (β ≫ β₂) ≫ (snd c.A c.A).left = β₁ ≫ (snd c.A c.A).left := by
        rw [Category.assoc, hsq₂.2, hsq₁.2, ← Category.assoc, hβdef, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, hcα]
      simp only [Over.fst_left, Over.snd_left] at h1 h2
      exact pullback.hom_ext h1 h2
    have iL₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb A₁.isLB _ _
    have iL₂ : ((abelian₂ A₂.A A₂.L).pull β).IsLB := pull_isLB (LB.isLB_linComb A₂.isLB _ _) _
    have iP₁ : (c.P.pull β₁).IsLB := pull_isLB c.isLB _
    have iP₂ : ((c.P.pull β₂).pull β).IsLB := pull_isLB (pull_isLB c.isLB _) _
    have h₃ : LBIso ((abelian₂ A₂.A A₂.L).pull β) ((c.P.pull β₂).pull β) :=
      LBIso.chartPull (chartPullPull _ β) (chartPullPull _ β) hL₂
    exact hL₁.trans iL₁ iP₁ iL₂ ((GlobalTheory.ClosedPol.lbIso_pull_comp c.isLB β₂ β β₁ hβ).trans iP₁ iP₂ iL₂ h₃.symm)

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.PhiLinear

theorem exists_linear_phi : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  intro R _ _ _ I _ D F _ _ _ N hN p w hw
  exact ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of_globalFns GlobalTheory.globalFns_holds R I D F N hN.pos p w hw.1

end GlobalTheory.Mum.PhiLinear
end
end

