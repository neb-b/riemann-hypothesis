module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterSetMapCoefficientFieldProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem mem_mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL')
    (Sig : Finset (I →* LLˣ)) (x : I →* LL'ˣ) :
    x ∈ mapSig f Sig ↔ ∃ a ∈ Sig, (Units.map (f : LL →* LL')).comp a = x := by
  classical
  unfold mapSig
  exact Finset.mem_image

theorem orbLen_map {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL')
    (I : Subgroup G) (Fr : G) (a b : I →* LLˣ) :
    Formalism.MainNotions.ElementDenominator.orbLen I Fr ((Units.map (f : LL →* LL')).comp a * ((Units.map (f : LL →* LL')).comp b)⁻¹) =
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (a * b⁻¹) := by
  set φ : LLˣ →* LL'ˣ := Units.map (f : LL →* LL') with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Units.ext
    have := congrArg Units.val huv
    simpa [hφ] using f.injective this
  have hcomp : φ.comp a * (φ.comp b)⁻¹ = φ.comp (a * b⁻¹) := by
    ext x
    simp
  rw [hcomp]
  unfold Formalism.MainNotions.ElementDenominator.orbLen
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, MonoidHom.comp_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => hinj (h g g' hg)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => congrArg φ (h g g' hg)⟩

theorem mapSig_props : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  intro G LL LL' _ _ _ f I Fr Sig
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig a').1 ha'
    obtain ⟨b, hb, hab⟩ := hS a ha
    refine ⟨(Units.map (f : LL →* LL')).comp b, (mem_mapSig f Sig _).2 ⟨b, hb, rfl⟩, ?_⟩
    intro g h hgh
    simp [hab g h hgh]
  · unfold Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig p).1 hpq.1
      obtain ⟨b, hb, rfl⟩ := (mem_mapSig f Sig q).1 hpq.2
      rw [orbLen_map f I Fr a b]
      exact Finset.le_sup (s := Sig ×ˢ Sig)
        (f := fun p : (↥I →* LLˣ) × (↥I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹)) (b := (a, b))
        (Finset.mem_product.2 ⟨ha, hb⟩)
    · apply Finset.sup_le
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have := Finset.le_sup (s := mapSig f Sig ×ˢ mapSig f Sig)
        (f := fun p : (↥I →* LL'ˣ) × (↥I →* LL'ˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (b := ((Units.map (f : LL →* LL')).comp a, (Units.map (f : LL →* LL')).comp b))
        (Finset.mem_product.2 ⟨(mem_mapSig f Sig _).2 ⟨a, hab.1, rfl⟩, (mem_mapSig f Sig _).2 ⟨b, hab.2, rfl⟩⟩)
      simpa only [orbLen_map f I Fr a b] using this
  · classical
    unfold mapSig
    exact Finset.card_image_le
  · intro h1
    exact (mem_mapSig f Sig 1).2 ⟨1, h1, MonoidHom.comp_one _⟩

end GlobalTheory.BaseCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ClassRefine

open scoped Classical

variable {G : Type*} [Group G] (Q : Subgroup G)

def stabQ (J : Subgroup G) (t : G) : Subgroup Q :=
  (J.comap (MulAut.conj t⁻¹).toMonoidHom).comap Q.subtype

variable {Q}

theorem mem_stabQ {J : Subgroup G} {t : G} {q : Q} : q ∈ stabQ Q J t ↔ t⁻¹ * (q : G) * t ∈ J := by
  rw [stabQ, Subgroup.mem_comap, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]

theorem card_stabQ_eq (J : Subgroup G) (t : G) :
    Nat.card (stabQ Q J t) = Nat.card {q : Q // t⁻¹ * (q : G) * t ∈ J} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabQ)

theorem card_stabQ_left (J : Subgroup G) (x : G) (γ : Q) :
    Nat.card (stabQ Q J ((γ : G) * x)) = Nat.card (stabQ Q J x) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨γ⁻¹ * q * γ, ?_⟩
      invFun := fun q => ⟨γ * q * γ⁻¹, ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem card_stabQ_split {J J' : Subgroup G} (hJ : J' ≤ J) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J)
    (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') (t s : G) (γ₀ : Q) (κ₀ : G) (hκ₀ : κ₀ ∈ J)
    (hs : s = (γ₀ : G) * t * κ₀) :
    Nat.card (stabQ Q J t) =
      (F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j).card * Nat.card (stabQ Q J' s) := by
  have hex : ∀ κ ∈ J, ∃ u, u ∈ F ∧ u⁻¹ * κ ∈ J' := fun κ hκ => (hFu κ hκ).exists
  choose! uF huF hJu using hex
  have huniq : ∀ κ ∈ J, ∀ u ∈ F, u⁻¹ * κ ∈ J' → u = uF κ := fun κ hκ u hu h =>
    (hFu κ hκ).unique ⟨hu, h⟩ ⟨huF κ hκ, hJu κ hκ⟩
  have hSΓ : stabQ Q J' (t * κ₀) ≤ stabQ Q J t := by
    intro q hq
    rw [mem_stabQ] at hq ⊢
    have : κ₀ * ((t * κ₀)⁻¹ * (q : G) * (t * κ₀)) * κ₀⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hκ₀ (hJ hq)) (J.inv_mem hκ₀)
    simpa [mul_assoc] using this
  set Γ := stabQ Q J t with hΓ
  set S := stabQ Q J' (t * κ₀) with hS
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j with hU
  let κf : Γ → G := fun q => t⁻¹ * ((q : Q) : G) * t * κ₀
  have hκ : ∀ q : Γ, κf q ∈ J := fun q => J.mul_mem (mem_stabQ.1 q.2) hκ₀
  have hψ : ∀ q : Γ, uF (κf q) ∈ U := by
    intro q
    rw [hU, Finset.mem_filter]
    refine ⟨huF _ (hκ q), (q : Q) * γ₀⁻¹, ((uF (κf q))⁻¹ * κf q)⁻¹, J'.inv_mem (hJu _ (hκ q)), ?_⟩
    simp only [κf, hs]
    push_cast
    group
  let ψ : Γ → U := fun q => ⟨uF (κf q), hψ q⟩
  have hresp : ∀ a b : Γ, a⁻¹ * b ∈ S.subgroupOf Γ → ψ a = ψ b := by
    intro a b h
    rw [Subgroup.mem_subgroupOf, hS, mem_stabQ] at h
    apply Subtype.ext
    show uF (κf a) = uF (κf b)
    refine huniq (κf b) (hκ b) (uF (κf a)) (huF _ (hκ a)) ?_
    have e : (uF (κf a))⁻¹ * κf b =
        ((uF (κf a))⁻¹ * κf a) * ((t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀)) := by
      simp only [κf]
      push_cast
      group
    rw [e]
    exact J'.mul_mem (hJu _ (hκ a)) h
  let Φ : Γ ⧸ S.subgroupOf Γ → U := Quotient.lift ψ (fun a b h => hresp a b (QuotientGroup.leftRel_apply.1 h))
  have hΦ : ∀ a : Γ, Φ (a : Γ ⧸ S.subgroupOf Γ) = ψ a := fun a => rfl
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hΦ, hΦ] at hxy
      have hab : uF (κf a) = uF (κf b) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hS, mem_stabQ]
      have h1 := hJu _ (hκ a)
      have h2 := hJu _ (hκ b)
      rw [hab] at h1
      have e : (t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀) =
          ((uF (κf b))⁻¹ * κf a)⁻¹ * ((uF (κf b))⁻¹ * κf b) := by
        simp only [κf]
        push_cast
        group
      rw [e]
      exact J'.mul_mem (J'.inv_mem h1) h2
    · rintro ⟨u, hu⟩
      have hu' := hu
      rw [hU, Finset.mem_filter] at hu'
      obtain ⟨huF', q, j, hj, e⟩ := hu'
      have hu_eq : u = t⁻¹ * ((q : G) * ((γ₀ : G) * t * κ₀) * j) := by
        rw [← hs, ← e]; group
      have hmem : t⁻¹ * (((q * γ₀ : Q)) : G) * t = u * j⁻¹ * κ₀⁻¹ := by
        rw [hu_eq]; push_cast; group
      have hqΓ : q * γ₀ ∈ Γ := by
        rw [hΓ, mem_stabQ, hmem]
        exact J.mul_mem (J.mul_mem (hF u huF') (J.inv_mem (hJ hj))) (J.inv_mem hκ₀)
      refine ⟨((⟨q * γ₀, hqΓ⟩ : Γ) : Γ ⧸ S.subgroupOf Γ), ?_⟩
      rw [hΦ]
      apply Subtype.ext
      show uF (κf ⟨q * γ₀, hqΓ⟩) = u
      refine (huniq _ (hκ _) u huF' ?_).symm
      have e2 : u⁻¹ * κf ⟨q * γ₀, hqΓ⟩ = j⁻¹ := by
        show u⁻¹ * (t⁻¹ * (((q * γ₀ : Q)) : G) * t * κ₀) = j⁻¹
        rw [hmem]; group
      rw [e2]
      exact J'.inv_mem hj
  have h1 := Subgroup.card_mul_index (S.subgroupOf Γ)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv, Subgroup.index,
    Nat.card_eq_of_bijective Φ hbij, Nat.card_eq_finsetCard] at h1
  have h2 : Nat.card (stabQ Q J' s) = Nat.card S := by
    rw [hS, hs, mul_assoc]
    exact card_stabQ_left J' (t * κ₀) γ₀
  rw [h2, ← h1, mul_comm]

theorem sum_classReps_refine {J J' : Subgroup G} (hJ : J' ≤ J) {T T' : Finset G}
    (hT : ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Q) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ)
    (hT' : ∀ g : G, ∃! t, t ∈ T' ∧ ∃ (γ : Q) (κ : G), κ ∈ J' ∧ g = (γ : G) * t * κ)
    (φ : G → ℂ) (hφQ : ∀ (γ : Q) g, φ ((γ : G) * g) = φ g) (hφJ : ∀ κ ∈ J', ∀ g, φ (g * κ) = φ g)
    {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J) (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') :
    ∑ t' ∈ T', ((Nat.card (stabQ Q J' t') : ℂ))⁻¹ * φ t' =
      ∑ t ∈ T, ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * ∑ u ∈ F, φ (t * u) := by
  choose! rep hrepT hrep using fun g => (hT' g).exists
  have hrepeq : ∀ g t', t' ∈ T' → ∀ (γ : Q) (κ : G), κ ∈ J' → g = γ * t' * κ → rep g = t' :=
    fun g t' ht' γ κ hκ e => (hT' g).unique ⟨hrepT g, hrep g⟩ ⟨ht', γ, κ, hκ, e⟩
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product' (f := fun t u => ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * φ (t * u)),
    ← Finset.sum_fiberwise_of_maps_to (s := T ×ˢ F) (t := T') (g := fun p => rep (p.1 * p.2))
      (fun p _ => hrepT _)]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  obtain ⟨t₀, ht₀, γ₀, κ₀, hκ₀, e₀⟩ := (hT t').exists
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t₀ * u = q * t' * j with hU
  have hfib : (T ×ˢ F).filter (fun p => rep (p.1 * p.2) = t') = {t₀} ×ˢ U := by
    ext ⟨a, u⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, hU]
    constructor
    · rintro ⟨⟨ha, hu⟩, hp⟩
      obtain ⟨γ, κ, hκ, e⟩ := hrep (a * u)
      rw [hp] at e
      have ha0 : a = t₀ := by
        refine (hT a).unique ⟨ha, 1, 1, J.one_mem, by simp⟩
          ⟨ht₀, γ * γ₀, κ₀ * κ * u⁻¹, J.mul_mem (J.mul_mem hκ₀ (hJ hκ)) (J.inv_mem (hF u hu)), ?_⟩
        have ea : a = a * u * u⁻¹ := by group
        rw [ea, e, e₀]
        push_cast
        group
      subst ha0
      exact ⟨rfl, hu, γ, κ, hκ, e⟩
    · rintro ⟨rfl, hu, q, j, hj, e⟩
      exact ⟨⟨ht₀, hu⟩, hrepeq _ t' ht' q j hj e⟩
  rw [hfib, Finset.sum_product, Finset.sum_singleton]
  have hval : ∀ u ∈ U, ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ (t₀ * u) =
      ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ t' := by
    intro u hu
    rw [hU, Finset.mem_filter] at hu
    obtain ⟨_, q, j, hj, e⟩ := hu
    rw [e, mul_assoc, hφQ, hφJ j hj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_stabQ_split hJ hF hFu t₀ t' γ₀ κ₀ hκ₀ e₀]
  have hne : U.card ≠ 0 := by
    obtain ⟨u, hu, hj⟩ := (hFu κ₀ hκ₀).exists
    refine Finset.card_ne_zero_of_mem (s := U) (a := u) ?_
    rw [hU, Finset.mem_filter]
    refine ⟨hu, γ₀⁻¹, (u⁻¹ * κ₀)⁻¹, J'.inv_mem hj, ?_⟩
    rw [e₀]
    push_cast
    group
  have hc : (U.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  rw [nsmul_eq_mul, Nat.cast_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem classSum_smaller_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), IsInvForm a β → ∀ (J J' : Subgroup (GAf L n)) (T T' : Finset (GAf L n)), IsBounded J → J' ≤ J → J'.relIndex J ≠ 0 → IsClassReps J T → IsClassReps J' T' → ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, (∀ κ ∈ J', ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g)) → ∀ F : Finset (GAf L n), (∀ κ ∈ F, κ ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') → classSum a β J' T' f f' = ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * ∑ u ∈ F, β (f (t * u)) (f' (t * u)) := by
  intro L _ _ _ n a β hβ J J' T T' _ hJ _ hT hT' f hf f' hf' hinv F hF hFu
  have key := sum_classReps_refine (Q := GQ L n) hJ hT hT' (fun g => β (f g) (f' g))
    (fun γ g => by rw [hf.1 γ g, hf'.1 γ g, hβ.2.2]) (fun κ hκ g => hinv κ hκ g) hF hFu
  simp only [card_stabQ_eq] at key
  exact key

end GlobalTheory.ClassRefine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOne
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section Abstract

variable {R O B K V C : Type} [CommSemiring R] [Semiring O] [Algebra R O] [Semiring B] [Algebra R B]
  [CommSemiring K] [AddCommMonoid V] [Module K V] [Semiring C] [Module K C]

theorem tensorAct_mul (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ (o o' : O) (v : V), s (o * o') v = s o (s o' v))
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (d d' : O ⊗[R] B) (w : V ⊗[K] C) : act (d * d') w = act d (act d' w) := by
  induction d using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [add_mul, map_add (f := _), AddMonoidHom.add_apply, hx, hy]
  | tmul o b =>
    induction d' using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
    | add x y hx hy => simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hx, hy]
    | tmul o' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul v c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, h, h, h, hs, map_mul, mul_assoc]

theorem tensorAct_one (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ v : V, s 1 v = v)
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (w : V ⊗[K] C) : act 1 w = w := by
  rw [Algebra.TensorProduct.one_def]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v c => rw [h, hs, map_one, one_mul]

end Abstract

theorem odAct_mul_one : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → (∀ (d d' : OD l ↥(OL LL)) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), act (d * d') w = act d (act d' w)) ∧ ∀ w : T.V ⊗[ℚ_[l]] Pl.R.BdR, act 1 w = w :=
  fun _ _ LL T _ _ Td act h =>
    ⟨tensorAct_mul (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) h,
      tensorAct_one (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun v => one_smul ↥LL.1 v) h⟩

end GlobalTheory.BKGal.JumpDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isHomogeneous_det_of_linear {σ R : Type} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => M (τ i) i) (fun _ => 1) (fun i _ => h (τ i) i)
  simpa using this

theorem coeff_aeval_of_isHomogeneous {R : Type} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin 2) R) (h : P.IsHomogeneous n) (j : ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1] P).coeff j =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1]
        (MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d))).coeff j =
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  simp_rw [hterm]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have hd' : AddMonoidAlgebra.coeff P d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have := h hd'
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

theorem coeff_det_pencil_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  intro Γ X O _ _ n T rep hT a b ha hb j
  set c : Fin 2 → X → Matrix (Fin n) (Fin n) O := ![a, b] with hc
  have hcR : ∀ k, InRing T rep (c k) := by
    intro k; fin_cases k
    · exact ha
    · exact hb
  have key := _root_.GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing T rep hT 2 c hcR
  set P : X → MvPolynomial (Fin 2) O := fun x =>
    Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin 2) O) • (c k x).map MvPolynomial.C) with hP
  have hhom : ∀ x, (P x).IsHomogeneous n := by
    intro x
    refine isHomogeneous_det_of_linear _ fun i j => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X O k).mul (MvPolynomial.isHomogeneous_C (Fin 2) (c k x i j))
  have hdet : ∀ x, Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O))) =
      MvPolynomial.aeval ![(Polynomial.X : Polynomial O), 1] (P x) := by
    intro x
    rw [hP, AlgHom.map_det]
    congr 1
    ext i j
    simp [hc, Fin.sum_univ_two, Matrix.map_apply]
  have hfun : (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O)))).coeff j) =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        (fun x => if d 0 = j then AddMonoidAlgebra.coeff (P x) d else 0) := by
    funext x
    rw [hdet x, coeff_aeval_of_isHomogeneous _ (hhom x) j, Finset.sum_apply]
  rw [hfun]
  refine Subalgebra.sum_mem _ fun d _ => ?_
  by_cases hd : d 0 = j
  · simp only [hd, if_true]
    exact key d
  · simp only [hd, if_false]
    exact T.zero_mem

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

def dpDen (e i n : ℕ) : ℕ := i.factorial * (n / e).factorial

theorem dpDen_pos (e i n : ℕ) : 0 < dpDen e i n := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofW (w : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n => algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K)

def QSet : Set (ZMod a → K⟦X⟧⟦X⟧) := Set.range (ofW t K e)

theorem coeff_ofW (w : ℕ × ℕ → Wq l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (ofW t K e w τ)) = algebraMap O K (emb t τ (w (i, n))) / (dpDen e i n : K) := by
  simp [ofW, coeff_mk]

variable {K}

def GoodSet (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {z | z ∈ QSet t K e ∧ frob2 φ₂ z ∈ QSet t K e ∧
    ∃ B ∈ QSet t K e, frob2 φ₂ z = z ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * B}


variable (K) in
def cstW (c : Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ => C (C (algebraMap O K (emb t τ c)))

end Q

variable (a : ℕ) (K : Type) [NormedField K]

def uFam : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C X

def dFam (e q : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((q.factorial : K)⁻¹) * X ^ (e * q))

def xFam (i : ℕ) : ZMod a → K⟦X⟧⟦X⟧ := fun _ => C (C ((i.factorial : K)⁻¹)) * X ^ i

end GlobalTheory.CrysPrism
end
end

