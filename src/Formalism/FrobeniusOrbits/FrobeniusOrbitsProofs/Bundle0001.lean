module

public import Mathlib
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.TameInertiaTowers.TowerFieldFoundations
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.JumpSets
public import Formalism.FrobeniusOrbits.HostThickExists

@[expose] public section

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
section
open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace ConjReal

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

lemma hcl_neg_one (e : ℕ) : hcl e (-1) = 1 := by
  unfold hcl
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

theorem conj_main (hGal : HostGalois) (hSpec : HostGalSpec) (hqd : HypOdd q d)
    (h : IsLayer (e + 2) q d ζ a b) :
    ∃ (τ : L ≃ₐ[ℚ] L) (σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
      galMap h.1 a b τ = JJ (e + 2) ∧ (∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x) ∧
      galE e ζ a b σc = cc e ∧
      ∀ (φ : hostE ζ a b →+* ℂ) (x : hostE ζ a b), φ (σc x) = starRingEnd ℂ (φ x) := by
  obtain ⟨hG, _, _, _⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨τ, hτ⟩ := (layerGalois (e + 2) q d (by omega) hqd L ζ a b h).2.2.2.2 (JJ (e + 2))
  let σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b := τ.restrictNormal (hostE ζ a b)
  have hres : ∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x := fun x =>
    AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  refine ⟨τ, σc, hτ, hres, ?_, ?_⟩
  · rw [(hSpec e q d hqd L ζ a b h σc).2.2.2 τ hres, hτ]
    simp [JJ, cc, c0, hcl_neg_one]
  · intro φ x
    let ψ : L →+* ℂ := ComplexEmbedding.lift L φ
    have hψ : ∀ y : hostE ζ a b, ψ (y : L) = φ y := fun y =>
      ComplexEmbedding.lift_algebraMap_apply L φ y
    have hc := (layerConj (e + 2) q d (by omega) hqd L ζ a b h ψ τ).2 hτ
    rw [← hψ (σc x), ← hψ x, hres x]
    exact hc x

lemma aE_sq (h : IsLayer (e + 2) q d ζ a b) : aE ζ a b ^ 2 = -(q : hostE ζ a b) := by
  apply Subtype.ext
  push_cast
  exact h.2.1

end ConjReal

open ConjReal

theorem hostConj_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostConj := by
  intro e q d hqd L _ _ ζ a b h
  obtain ⟨hG, _, _, hbij⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨_, σc, _, _, hσc, hconj⟩ := conj_main hGal hSpec hqd h
  have hq : 0 < q := hqd.1.pos
  have haE := aE_sq h
  have hTC : IsTotallyComplex (hostE ζ a b) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw (aE ζ a b)
    rw [ComplexEmbedding.conjugate_coe_eq, UnitConjugation.phi_conj hq haE] at h2
    have h3 : (2 : ℂ) * w.embedding (aE ζ a b) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (UnitConjugation.ne_zero_of_sq hq haE) h4
  have hCM : IsCMField (hostE ζ a b) := by
    refine IsCMField.of_forall_isConj (hostE ζ a b) (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hconj φ x).symm
  refine ⟨hCM, fun φ σ => ⟨fun hx => ?_, fun hσ => ?_⟩⟩
  · have hσ : σ = σc := AlgEquiv.ext fun x => φ.injective (by rw [hx, hconj])
    rw [hσ, hσc]
  · have hσ' : σ = σc := hbij.1 (hσ.trans hσc.symm)
    subst hσ'
    exact hconj φ

theorem hostReal_of (hGal : HostGalois) (hSpec : HostGalSpec) (hConj : HostConj) : HostReal :=
  _root_.UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of hGal hSpec hConj

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
section
open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Frob

theorem frob_mul_inertia {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] (Q : Ideal S) (ρ τ : G) (hρ : ρ ∈ Q.inertia G)
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ (ρ * τ) Q := by
  intro x
  have h1 : ρ • (τ • x) - τ • x ∈ Q := hρ (τ • x)
  have h2 := hτ x
  try simp only [MulSemiringAction.toAlgHom_apply] at h2 ⊢
  rw [mul_smul]
  have h3 := Q.add_mem h1 h2
  rwa [sub_add_sub_cancel] at h3

end Frob

theorem hostFrob_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostFrob := by
  intro e q d hqd L _ _ ζ a b h p _ hp2 hpq hpd P _ _
  obtain ⟨hEgal, -, hmulE, hbijE⟩ := hGal e q d hqd L ζ a b h
  obtain ⟨hLgal, -, hmulL, hbijL⟩ := layerGalois (e + 2) q d (by omega) hqd L ζ a b h
  have := hEgal
  have := hLgal
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P (span {(p : ℤ)})
  have hFr := layerFrob (e + 2) q d (by omega) hqd L ζ a b h p hp2 hpq hpd Q
  obtain ⟨⟨τ, hτ⟩, hτspec⟩ := hFr
  obtain ⟨hτ1, hτ2, hτ3⟩ := (hτspec τ).mp hτ

  have hgm1 : galMap h.1 a b (1 : Gal(L/ℚ)) = 1 := by
    have := hmulL 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)

  have hIQ : ∀ ρ ∈ Q.inertia Gal(L/ℚ), ρ = 1 := by
    intro ρ hρ
    have hF := Frob.frob_mul_inertia Q ρ τ hρ hτ
    obtain ⟨h1, h2, h3⟩ := (hτspec (ρ * τ)).mp hF
    have heq : galMap h.1 a b (ρ * τ) = galMap h.1 a b τ := by
      refine Prod.ext (Units.ext (h1.trans hτ1.symm)) (Prod.ext ?_ ?_)
      · exact Units.ext (h2.trans hτ2.symm)
      · exact Units.ext (h3.trans hτ3.symm)
    rw [hmulL, mul_eq_right] at heq
    exact hbijL.1 (heq.trans hgm1.symm)
  have heQ : Q.ramificationIdx ℤ = 1 := by
    rw [← odd_card L p Q]
    have : Q.inertia Gal(L/ℚ) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hIQ
    rw [this]
    simp
  have heP : P.ramificationIdx ℤ = 1 := by
    have hte := Ideal.ramificationIdx_tower (R := ℤ) P Q
    rw [heQ] at hte
    exact Nat.eq_one_of_mul_eq_one_right hte.symm
  have hIP : ∀ σ ∈ P.inertia Gal(hostE ζ a b/ℚ), σ = 1 := by
    have hc := odd_card (hostE ζ a b) p P
    rw [heP, Nat.card_eq_one_iff_unique] at hc
    intro σ hσ
    have : (⟨σ, hσ⟩ : P.inertia Gal(hostE ζ a b/ℚ)) = ⟨1, one_mem _⟩ := hc.1.elim _ _
    exact congrArg Subtype.val this

  let σ₀ : Gal(hostE ζ a b/ℚ) := τ.restrictNormal (hostE ζ a b)
  have hσ₀ : ∀ x : hostE ζ a b, ((σ₀ x : hostE ζ a b) : L) = τ x :=
    fun x => AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  have hσ₀F : IsArithFrobAt ℤ σ₀ P := by
    intro x
    have hx := hτ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x)
    rw [odd_card_under p Q] at hx
    rw [odd_card_under p P]
    rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]
    convert hx using 1
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_pow, MulSemiringAction.toAlgHom_apply]
    congr 1
    show (((σ₀ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L) =
      τ (((x : 𝓞 (hostE ζ a b)) : hostE ζ a b) : L)
    exact hσ₀ x
  have hval := (hSpec e q d hqd L ζ a b h σ₀).2.2.2 τ hσ₀
  have hgalE1 : galE e ζ a b (1 : Gal(hostE ζ a b/ℚ)) = 1 := by
    have := hmulE 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have huniq : ∀ σ : Gal(hostE ζ a b/ℚ), IsArithFrobAt ℤ σ P → σ = σ₀ := by
    intro σ hσ
    have := hIP _ (hσ.mul_inv_mem_inertia hσ₀F)
    exact mul_inv_eq_one.mp this
  refine ⟨⟨σ₀, hσ₀F⟩, fun σ => ⟨fun hσ => ?_, fun hs => ?_⟩, fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩⟩
  · rw [huniq σ hσ, hval]
    exact ⟨hτ2, hτ3, (galMap h.1 a b τ).1, hτ1, rfl⟩
  · obtain ⟨s1, s2, u, hu, hu2⟩ := hs
    have : σ = σ₀ := by
      apply hbijE.1
      rw [hval]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · exact Units.ext (s1.trans hτ2.symm)
      · exact Units.ext (s2.trans hτ3.symm)
      · rw [hu2]
        exact congrArg (hcl e) (Units.ext (hu.trans hτ1.symm))
    rw [this]
    exact hσ₀F
  · exact hIP σ (AddSubgroup.mem_inertia.mpr hσ)
  · subst hσ
    intro x
    simp

end Formalism.FrobeniusOrbits
end
end

-- bundled from Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickOrbit
section
open Classical

namespace Formalism.FrobeniusOrbits
namespace ThickOrbit

theorem bound_aux {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ L) (hs : 4 * L * s < n) :
    4 * (j * (s : ℤ)) < n := by
  have hs' : (4 * L * s : ℤ) < n := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ s := by positivity
  nlinarith

theorem int_mul_lt_of_le_four_mul {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ 4 * L) (hs : 4 * L * s < n) :
    j * (s : ℤ) < n := by
  have hs' : (4 * L * s : ℤ) < n := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ s := by positivity
  nlinarith

theorem key {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : InTranslate T u₀ (t + a • h)) (hxb : InTranslate T u₀ (t + b • h))
    (hxc : InTranslate T u₀ (t + c • h)) : False := by
  rw [Finset.mem_Ico] at ha hc
  obtain ⟨sa, hsa, ea⟩ := hxa
  obtain ⟨sb, hsb, eb⟩ := hxb
  obtain ⟨sc, hsc, ec⟩ := hxc
  rw [zsmul_eq_mul] at ea eb ec

  have hz : ∀ d : ℤ, 0 < d → d ≤ 4 * L → (d : ZMod n) * h ≠ 0 := by
    intro d hd hdL hdz
    have hdv : (addOrderOf h : ℤ) ∣ d :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [zsmul_eq_mul]; exact hdz)
    have := Int.le_of_dvd hd hdv
    omega
  have hab' : sa ≠ sb := by
    rintro rfl
    exact hz (b - a) (by omega) (by omega) (by push_cast; linear_combination eb - ea)
  have hac' : sa ≠ sc := by
    rintro rfl
    exact hz (c - a) (by omega) (by omega) (by push_cast; linear_combination ec - ea)
  have hbc' : sb ≠ sc := by
    rintro rfl
    exact hz (c - b) (by omega) (by omega) (by push_cast; linear_combination ec - eb)
  set X : ℤ := (c - a) * ((sb : ℤ) - sa) - (b - a) * ((sc : ℤ) - sa) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑b - ↑a) * (ec - ea) - (↑c - ↑a) * (eb - ea)
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := bound_aux (c - a) sb (by omega) (hT sb hsb)
  have h2 := bound_aux (c - a) sa (by omega) (hT sa hsa)
  have h3 := bound_aux (b - a) sc (by omega) (hT sc hsc)
  have h4 := bound_aux (b - a) sa (by omega) (hT sa hsa)
  have p1 : 0 ≤ (c - a) * (sb : ℤ) := mul_nonneg (by omega) (by positivity)
  have p2 : 0 ≤ (c - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have p3 : 0 ≤ (b - a) * (sc : ℤ) := mul_nonneg (by omega) (by positivity)
  have p4 : 0 ≤ (b - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  refine hR sa hsa sb hsb sc hsc hab' hac' hbc' (b - a) (c - a) ?_ ?_ ?_ ?_ (by omega) ?_
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [hX] at hXz; linarith

theorem part_one {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2 := by
  set S := (Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h)) with hS
  by_contra hlt
  push_neg at hlt
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a := S.min' hne
  set c := S.max' hne
  have hcard : 0 < ((S.erase c).erase a).card := by
    have h1 := Finset.pred_card_le_card_erase (s := S) (a := c)
    have h2 := Finset.pred_card_le_card_erase (s := S.erase c) (a := a)
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbS' : b ∈ S.erase c := Finset.mem_of_mem_erase hb
  have hbc : b ≠ c := Finset.ne_of_mem_erase hbS'
  have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
  have haS : a ∈ S := S.min'_mem hne
  have hcS : c ∈ S := S.max'_mem hne
  have hab : a < b := lt_of_le_of_ne (S.min'_le b hbS) (Ne.symm hba)
  have hbc' : b < c := lt_of_le_of_ne (S.le_max' b hbS) hbc
  rw [hS, Finset.mem_filter] at haS hbS hcS
  exact key T hT hR u₀ t h hord i₀ a b c haS.1 hcS.1 hab hbc' haS.2 hbS.2 hcS.2

theorem part_two {n L : ℕ} (hn : 0 < n) (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n)
    (u₀ t h : ZMod n) (hord : addOrderOf h ≤ 4 * L) :
    {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [Set.ncard_le_one]
  rintro x ⟨⟨i, rfl⟩, s₁, hs₁, e₁⟩ y ⟨⟨i', rfl⟩, s₂, hs₂, e₂⟩
  set m := addOrderOf h with hm
  have hmpos : 0 < m := addOrderOf_pos h
  have hmh : (m : ZMod n) * h = 0 := by
    have := addOrderOf_nsmul_eq_zero h
    rwa [nsmul_eq_mul] at this
  rw [zsmul_eq_mul] at e₁ e₂
  set X : ℤ := (m : ℤ) * ((s₁ : ℤ) - s₂) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑m : ZMod n) * (e₂ - e₁) + ((↑i : ZMod n) - ↑i') * hmh
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := int_mul_lt_of_le_four_mul (m : ℤ) s₁ (by exact_mod_cast hord) (hT s₁ hs₁)
  have h2 := int_mul_lt_of_le_four_mul (m : ℤ) s₂ (by exact_mod_cast hord) (hT s₂ hs₂)
  have p1 : 0 ≤ (m : ℤ) * (s₁ : ℤ) := by positivity
  have p2 : 0 ≤ (m : ℤ) * (s₂ : ℤ) := by positivity
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hs : (s₁ : ℤ) = s₂ := by
    rw [hX] at hXz
    rcases mul_eq_zero.mp hXz with h0 | h0
    · omega
    · linarith
  have hs' : s₁ = s₂ := by exact_mod_cast hs
  subst hs'
  rw [zsmul_eq_mul, zsmul_eq_mul, e₁, e₂]

end ThickOrbit

theorem hostThickOrbit : HostThickOrbit := by
  intro n L hn _ T hT hR u₀ t h
  exact ⟨fun hord i₀ => ThickOrbit.part_one T hT hR u₀ t h hord i₀,
    fun hord => ThickOrbit.part_two hn T hT u₀ t h hord⟩

end Formalism.FrobeniusOrbits
end

