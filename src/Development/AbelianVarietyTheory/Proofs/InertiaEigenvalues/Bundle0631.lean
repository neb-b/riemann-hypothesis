module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeRepresentativesSplitPlaceSmallerLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerLevelHecke
open Formalism.IndefR.Lev Formalism.L2.NTheta GlobalTheory.SplitHeckeAdj

theorem local_group_two {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L L' : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1)
    (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (he : IsIdemAt e P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (hoff' : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ g, SuppAt e V g → fin V g ∈ Lc) ∧
      (∀ g, SuppAt e V g → fin V g⁻¹ ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l) ∧
      (levEnv V β L).J ⊓ Lc ≤ (levEnv V β L').J := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e _ hP
  have hff := h01.1
  have hcf := h01.2.1
  have h02 := ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).1 _ hff hcf).1
  refine h02.elim fun L₀ hL₀ => ?_
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e _ hP h1 hoff
  have hK' := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L') hβ).2 P e _ hP h1 hoff').1
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hL : ∀ g, g ∈ L₀ ↔ SuppAt e V g := hL₀
  have h04 := (_root_.GlobalTheory.SplitPlace.split_local V P e he).1
  have h05 := transport_local (fin V) (GfC V) (levG V β (flag1L L)) L₀ (levEnv V β L).J (SuppAt e V)
    (SuppF V (1 - (e + cA D e))) (KsphC V ∅) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L))
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L) (fun g hg => hg.1) hL (fun g => supp_fin V he)
    (fun g g' => commute_compl V _ hff hcf) (fun g => chi_eq V β L) hK hχ hsp h04
  refine ⟨L₀.map (fin V), fun g hg => ⟨g, (hL g).2 hg, rfl⟩,
    fun g hg => ⟨g⁻¹, L₀.inv_mem ((hL g).2 hg), rfl⟩, h05.1, ?_⟩
  rintro _ ⟨hj, g, hg, rfl⟩
  have a := (hL g).1 hg
  have b := supp_fin V he a
  exact (mem_J V β L' b).2 ((hK' g a).2 ((hK g a).1 ((mem_J V β L b).1 hj)))

theorem isDC_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  intro D V β Λ hSD L Q' xq hQ Pl0 pl ok i hoff hi x A hx hA hDC
  have hle := (GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ).1
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  obtain ⟨α, ⟨e, ϖ, he, -, -, hα⟩, hxα⟩ := hx hi
  obtain ⟨Lc, l1, l2, l3, l4⟩ := local_group_two V β Λ L { L with Q := Q', xq := xq } hβ (pl i.1) e he
    (fun PP h => hoff PP (h.imp_right fun h' => hQ h')) hoff
  have e1 : x = fin V α⁻¹ := Subtype.ext hxα
  refine GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local _ _ Lc x A hle l4 l3 ?_ (fun a ha => ?_) hDC
  · rw [e1]
    exact l2 α hα.2.1
  · obtain ⟨g, hg, rfl⟩ := loc_supp V (hA a ha) he
    exact l1 g hg

end GlobalTheory.SmallerLevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorLiftEquivariantMapsOfIrreducible
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmGL.EvalInj

open ValuativeRel Topology in
private theorem eq_zero_of_sum_intertwining_apply_eq_zero {H X Y : Type} [Group H] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X)
    (ρ : Representation ℂ H Y) (hρ : ρ.IsIrreducible)
    (hschur : ∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) :
    ∀ (m : ℕ) (φ : Fin m → (Y →ₗ[ℂ] X)), LinearIndependent ℂ φ →
      (∀ i g v, φ i (ρ g v) = τ g (φ i v)) → ∀ y : Fin m → Y, ∑ i, φ i (y i) = 0 → y = 0 := by
  intro m
  induction m with
  | zero => intro φ _ _ y _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hli hφ y hy
    let Φ : (Fin (m + 1) → Y) →ₗ[ℂ] X := ∑ i, (φ i).comp (LinearMap.proj i)
    have hΦ : ∀ w, Φ w = ∑ i, φ i (w i) := fun w => by simp [Φ]
    let S := LinearMap.ker Φ
    have hSinv : ∀ g, ∀ w ∈ S, (fun i => ρ g (w i)) ∈ S := by
      intro g w hw
      rw [LinearMap.mem_ker, hΦ] at hw ⊢
      simp_rw [hφ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hw, map_zero]
    let p : S →ₗ[ℂ] Y := (LinearMap.proj (Fin.last m)).comp S.subtype
    have hp : Function.Injective p := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hw0 : (w : Fin (m + 1) → Y) (Fin.last m) = 0 := hw
      have hsum : ∑ i : Fin m, φ (Fin.castSucc i) ((w : Fin (m + 1) → Y) (Fin.castSucc i)) = 0 := by
        have hw' := w.2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc, hw0, map_zero, add_zero] at hw'
        exact hw'
      have hzero := ih (fun i => φ (Fin.castSucc i)) (hli.comp _ (Fin.castSucc_injective m))
        (fun i => hφ _) _ hsum
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hw0
      · exact congrFun hzero j
    let R : Subrepresentation ρ := ⟨LinearMap.range p, by
      rintro g _ ⟨w, rfl⟩
      exact ⟨⟨fun i => ρ g ((w : Fin (m + 1) → Y) i), hSinv g w w.2⟩, rfl⟩⟩
    have hyS : y ∈ S := by rw [LinearMap.mem_ker, hΦ]; exact hy
    haveI := hρ
    rcases IsSimpleOrder.eq_bot_or_eq_top R with hR | hR
    · have hrange : LinearMap.range p = ⊥ := congrArg Subrepresentation.toSubmodule hR
      have hpy : p ⟨y, hyS⟩ = 0 := by
        rw [LinearMap.range_eq_bot] at hrange
        rw [hrange]
        rfl
      exact congrArg Subtype.val (hp (hpy.trans (map_zero p).symm))
    · exfalso
      have hrange : LinearMap.range p = ⊤ := congrArg Subrepresentation.toSubmodule hR
      let e := LinearEquiv.ofBijective p ⟨hp, LinearMap.range_eq_top.mp hrange⟩
      have hlast : ∀ v, (e.symm v : Fin (m + 1) → Y) (Fin.last m) = v := fun v =>
        e.apply_symm_apply v
      have he : ∀ g v, e.symm (ρ g v) =
          ⟨fun i => ρ g ((e.symm v : Fin (m + 1) → Y) i), hSinv g _ (e.symm v).2⟩ := by
        intro g v
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        show ρ g v = ρ g ((e.symm v : Fin (m + 1) → Y) (Fin.last m))
        rw [hlast]
      let T : Fin m → ρ.IntertwiningMap ρ := fun j =>
        ⟨(LinearMap.proj (Fin.castSucc j)).comp (S.subtype.comp e.symm.toLinearMap), by
          intro g
          ext v
          simp [he]⟩
      choose c hc using fun j => hschur (T j)
      have hT : ∀ j v, (e.symm v : Fin (m + 1) → Y) (Fin.castSucc j) = c j • v := fun j v => hc j v
      have hzero : ∑ i, (Fin.snoc (α := fun _ => ℂ) c 1 i) • φ i = 0 := by
        ext v
        have hv := (e.symm v).2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc] at hv
        simp only [hT, hlast, map_smul] at hv
        simpa [Fin.sum_univ_castSucc] using hv
      have h1 := (Fintype.linearIndependent_iff.mp hli) _ hzero (Fin.last m)
      simp at h1


open ValuativeRel Topology in
theorem _root_.GlobalTheory.SmGL.EvalInj.lift_subtype_injective :
    ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible →
      (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) →
      ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) →
      Function.Injective (TensorProduct.lift M.subtype) := by
  intro H X Y _ _ _ _ _ τ ρ hρ hschur M hM
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨M', hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {t} (Set.finite_singleton t)
  obtain ⟨t₀, rfl⟩ := hsub (Set.mem_singleton t)
  haveI := hfin
  let b := Module.finBasis ℂ M'
  set y : Fin (Module.finrank ℂ M') → Y := fun i => TensorProduct.equivFinsuppOfBasisLeft b t₀ i
    with hy
  have ht₀ : t₀ = ∑ i, b i ⊗ₜ[ℂ] y i := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t₀]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
    intro i
    exact TensorProduct.tmul_zero _ _
  let φ : Fin (Module.finrank ℂ M') → (Y →ₗ[ℂ] X) := fun i => ((b i : M) : Y →ₗ[ℂ] X)
  have hli : LinearIndependent ℂ φ :=
    (b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)).map' M.subtype
      (Submodule.ker_subtype _)
  have hsum : ∑ i, φ i (y i) = 0 := by
    rw [ht₀] at ht
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, φ] using ht
  have hy0 := eq_zero_of_sum_intertwining_apply_eq_zero τ ρ hρ hschur _ φ hli
    (fun i g v => hM _ (b i : M).2 g v) y hsum
  rw [ht₀, hy0]
  simp

end GlobalTheory.SmGL.EvalInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

section Core

def IsUnitOver {E : Type} [Field E] [NumberField E] (l : ℕ) (y : (Af E)ˣ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((y : Af E) P) = 1 ∧ ((l : 𝓞 E) ∉ P.asIdeal → (y : Af E) P = 1)

theorem isUnitOver_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ}
    {v : HeightOneSpectrum (𝓞 K)} (hv : (l : 𝓞 K) ∈ v.asIdeal) {x : (v.adicCompletion K)ˣ} (hx : Formalism.L2.Host.IsUnitAt v x) :
    IsUnitOver l (upIdele K E (single v x)) := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Formalism.L2.Host.IsUnitAt v x → ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v ((upIdele K E (single v x) : Af E) P) ≤ 1 := fun x hx P => by
    refine GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo K E P (x := (single v x : Af K) (P.under (𝓞 K))) ?_
    show Valued.v ((single v x : Af K) (P.under (𝓞 K))) ≤ 1
    by_cases h : P.under (𝓞 K) = v
    · subst h
      rw [single_self]
      exact le_of_eq hx
    · rw [suppAt_single v x _ h, map_one]
  refine fun P => ⟨le_antisymm (key x hx P) ?_, fun hP => ?_⟩
  · have h1 := key x⁻¹ (by
      show Valued.v _ = 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : v.adicCompletion K) = 1 from hx, inv_one]) P
    rw [map_inv, map_inv, ← coe_coord, Fibre.coord_inv', Units.val_inv_eq_inv_val, map_inv₀,
      inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Units.ne_zero _)))] at h1
    exact h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K E P ((single v x : Af K) (P.under (𝓞 K))) = 1
    rw [suppAt_single v x _ fun h => hP ?_, map_one]
    subst h
    rw [← map_natCast (algebraMap (𝓞 K) (𝓞 E))]
    exact hv

theorem finPart_of_isUnitOver {E : Type} [Field E] [NumberField E] {l : ℕ} {ξ : HChar E}
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → ξ.UnrAt P) {y : (Af E)ˣ} (hy : IsUnitOver l y) :
    finPart ξ y = 1 := by
  refine (Fibre.hasProd_loc ξ y).unique ?_
  have e : (fun P => ξ.loc P (coord P y)) = fun _ => 1 := funext fun P => by
    by_cases hP : (l : 𝓞 E) ∈ P.asIdeal
    · exact h P hP _ (hy P).1
    · rw [show coord P y = 1 from Units.ext ((hy P).2 hP), map_one]
  rw [e]
  exact hasProd_one

variable {R : Ranks} {H : Host R} {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF H.E)} {χ : HChar H.E}

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : 𝔣 ≠ ⊥) (Q : Finset (HeightOneSpectrum (OF E))) :
    condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem partialSum_mem (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hk : IsAlgClosed (IsLocalRing.ResidueField O)) {l : ℕ} (hl : l ≠ 0) (hO : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (ι : ℂ →+* AlgebraicClosure (FractionRing O))
    (hE : ∀ (σ : H.E →+* ℂ) (x : H.E), ι (σ x) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range)
    (S : Finset (HeightOneSpectrum (𝓞 H.E)))
    (hS : ∀ P ∉ S, ι (χ.val P : ℂ) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range)
    {T₀ : ℂ} (hT₀ : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀) (h0 : T₀ ≠ 0)
    {Q : Finset (HeightOneSpectrum (OF H.E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) [Finite (PicO (condQ 𝔣 Q))]
    {T : PicO (condQ 𝔣 Q) → ℂ} (hT : ∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q))
    {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : PicO (condQ 𝔣 Q) →* Δ)
    (hπ : ∀ y, IsUnitOver l y → π (QuotientGroup.mk y) = 1) (δ : Δ) :
    (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range := by
  classical
  have : IsCMField H.E := H.isCMField_hostE
  have : CharZero (AlgebraicClosure (FractionRing O)) := ι.charZero_iff ι.injective |>.1 inferInstance
  have : CharZero (FractionRing O) := RingHom.charZero (algebraMap _ (AlgebraicClosure (FractionRing O)))
  have : CharZero O := RingHom.charZero (algebraMap _ (FractionRing O))
  obtain ⟨τ₀, -⟩ := hD.1 H.φ₀
  let Ω := AlgebraicClosure H.K
  let _ : Algebra H.K ℂ := ((φ τ₀).comp (algebraMap H.K H.E)).toAlgebra
  let j : Ω →ₐ[H.K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hj : ∀ x : H.K, j.toRingHom (algebraMap H.K Ω x) = φ τ₀ x := j.commutes
  obtain ⟨art, ha⟩ := hA H.K Ω
  obtain ⟨ρ, hρ, hg⟩ := hG R H I φ s κ 𝔣 χ hD Ω j.toRingHom τ₀ hj art ha T₀ hT₀ h0 Q hQ inferInstance T hT
  generalize j.toRingHom = j at hj hρ hg
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  obtain ⟨z, hz, hfix⟩ := exists_fixed j (fun δ => (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) / T₀) (fun r => ρ (r.comp π)) (fun r => by
    rw [hρ, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), Finset.sum_div]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset,
      ← mul_div_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← (Finset.mem_filter.1 hq).2, map_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀, MonoidHom.comp_apply]) δ
  obtain ⟨v, A, hv, hA', hτ⟩ := exists_inertia (K := H.K) hk hl hO (ι.comp j) fun x => by
    rw [RingHom.comp_apply, hj]
    exact hE _ _
  have hfin := hT₀.1
  have hval : ∀ y, lamF s χ y ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).fieldRange.comap ι := fun y => by
    refine mul_mem (finPart_mem hD.2.2.2.2.2.2.2.1 (condQ_ne_bot hD.2.2.2.2.1.1 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) _ hE S hS y) ?_
    rw [Complex.ofReal_pow]
    exact pow_mem (modF_mem _ y) s
  rw [mul_comm, ← div_eq_mul_inv, ← map_div₀, ← hz]
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => ?_
  obtain ⟨g, hgI, hgτ⟩ := hτ τ
  have hfx : ∀ x : Ω, ι (j x) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range → g x = x :=
    fun x ⟨y, hy⟩ => (ι.comp j).injective ((hgτ x).trans (by rw [RingHom.comp_apply, ← hy, τ.commutes]))
  obtain ⟨x, hx, hax⟩ := (ha.ine v A hA' _).2 ⟨g⁻¹, inv_mem hgI, rfl⟩
  refine (hgτ z).symm.trans (congrArg (ι.comp j) (hfix g.toRingEquiv fun r => ?_))
  refine (hg g (fun x τ y h => hfx x (h ▸ hE _ _)) (fun x y h => hfx x (h ▸ hval y)) (single v x) hax (r.comp π)).trans ?_
  rw [MonoidHom.comp_apply, hπ _ (isUnitOver_up hv hx), map_one, Units.val_one, map_one, inv_one, one_mul]
  rfl

theorem isCMValueHeckeCharacter_auxiliarySet_of_empty {E : Type} [Field E] [NumberField E] {φ : I → E →+* ℂ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    {Q : Finset (HeightOneSpectrum (OF E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h : IsValChar φ s κ 𝔣 ∅ χ) : IsValChar φ s κ 𝔣 Q χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun v P hP => ⟨fun hv => ?_, fun _ => (h.2.2.2 v P hP).2 (Finset.notMem_empty v)⟩⟩
  refine ((h.2.2.2 v P hP).2 (Finset.notMem_empty v) 1).2 ?_
  rw [expIn, multiplicity_eq_zero_of_not_dvd (hQ v hv).2]
  exact zero_le_one

theorem exists_classTerms (hL : ToricSumFormula) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ)
    {Q : Finset (HeightOneSpectrum (OF H.E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) :
    Finite (PicO (condQ 𝔣 Q)) ∧ ∃ T : PicO (condQ 𝔣 Q) → ℂ, ∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q) := by
  have : IsCMField H.E := H.isCMField_hostE
  have hv := isCMValueHeckeCharacter_auxiliarySet_of_empty hQ hD.2.2.2.2.2
  obtain ⟨Λ, hΛ⟩ := exists_isHeckeL hD.2.2.2.2.1 hQ hv
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hD.2.2.2.2.1.2.1
  obtain ⟨P₀, -⟩ := (hD.2.2.2.2.1.2.2 ⟨M, hM.isPrime, fun h => hD.2.2.2.2.1.1 (le_bot_iff.1 (h ▸ hle))⟩
    (Ideal.dvd_iff_le.2 hle)).1
  have : ∀ q : HeightOneSpectrum (OF H.E), ∃ P, q ∈ Q → Over P q := fun q => by
    by_cases hq : q ∈ Q
    · obtain ⟨P, -, -, hP, -⟩ := (hQ q hq).1
      exact ⟨P, fun _ => hP⟩
    · exact ⟨P₀, fun h => absurd h hq⟩
  choose Pq hPq using this
  obtain ⟨h1, T, hT, -⟩ := (isToricSum_iff _ _ _ _ _ _).1
    (hL _ I φ hD.1 s κ 𝔣 Q χ Pq Λ hU hD.2.2.1 hD.2.2.2.2.1 hQ hv hPq hΛ)
  exact ⟨h1, T, hT⟩

theorem exists_toricSum_ne_zero (hL : ToricSumFormula) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ) :
    ∃ T₀, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  have : IsCMField H.E := H.isCMField_hostE
  have hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 ∅ := fun _ h => absurd h (Finset.notMem_empty _)
  obtain ⟨Λ, hΛ⟩ := exists_isHeckeL hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hD.2.2.2.2.1.2.1
  obtain ⟨P₀, -⟩ := (hD.2.2.2.2.1.2.2 ⟨M, hM.isPrime, fun h => hD.2.2.2.2.1.1 (le_bot_iff.1 (h ▸ hle))⟩
    (Ideal.dvd_iff_le.2 hle)).1
  refine ⟨_, hL _ I φ hD.1 s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hD.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
    (fun _ h => absurd h (Finset.notMem_empty _)) hΛ, ?_⟩
  rw [Finset.filter_empty, Finset.prod_empty, mul_one]
  refine heckeL_ne_zero_nat exists_isHeckeL_of_hasInf H.E I φ hD.1 _ χ Λ s hD.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.1 (fun i => ?_) hΛ hD.2.2.1
  have := hD.2.2.1
  omega

end Core

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_isRecMap (hA : GlobalTheory.Published.GlobalArtinReciprocity) {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (hQ : BlochKatoReduction.Gen.QOk X i Q) (𝔣 : Ideal (OF D.host.E)) :
    ∃ π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q, IsRecMap X i Q π ∧
      ∀ y, IsUnitOver (X.l i) y → π (QuotientGroup.mk y) = 1 := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := hA D.host.E N.Om
  let θ : (Af D.host.E)ˣ →* X.RCG i Q := (liftOpen (X.art i Q) (X.art_cont i Q)).comp (art.comp (finIdele D.host.E))
  have key : ∀ r : X.RCG i Q →* ℂˣ, ∃ ξ, Corr art (r.comp (X.art i Q)) ξ ∧ ∀ y, r (θ y) = finPart ξ y := fun r => by
    obtain ⟨ξ, hξ⟩ := exists_corr (r := r.comp (X.art i Q)) ha
      (Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]) (X.art_cont i Q))
    refine ⟨ξ, hξ, fun y => ?_⟩
    obtain ⟨σ, hσ⟩ := toAb_surjective (art (finIdele D.host.E y))
    show r (liftOpen _ (X.art_cont i Q) (art (finIdele D.host.E y))) = _
    rw [← hσ, liftOpen_toAb]
    exact (hξ _ σ hσ.symm).symm
  have hQl : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((X.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∉ Q := fun P hP h =>
    Finset.disjoint_left.1 hQ.2.1 h (X.twistExcludedPlaces_contains_residueChar i hP)
  obtain ⟨n, hn⟩ := exists_exponent X i Q
  have hk : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ θ.ker := by
    refine sup_le ?_ fun u hu => eq_one_of_chars (Ω := ℂ) fun r => ?_
    · rintro _ ⟨k, rfl⟩
      refine eq_one_of_chars (Ω := ℂ) fun r => ?_
      obtain ⟨ξ, hξ, e⟩ := key r
      have hp := hξ.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
      have := finPart_mul_inf ξ k
      rwa [inf_of_pow (pow_ne_zero n (X.lPrime i).out.ne_zero) hp, mul_one, ← e] at this
    · obtain ⟨ξ, hξ, e⟩ := key r
      have hp := hξ.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
      rw [e]
      refine OrderUnits.finPart_eq_one_of_level (trivOnF_of_corr ha hξ) (fun v => ?_) hu
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P hP => ?_⟩
        · rw [pow_one]
          exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF D.host.E) => q.asIdeal) hv) _
        · by_cases hPl : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          · exact fun x hx _ => unrAt_of_corr ha hξ (hQl P hPl) x hx
          · exact levelLe_one_of_pow (X.lPrime i).out hp hPl
      · exact ⟨0, by simp, fun P hP x hx _ => unrAt_of_corr ha hξ
          (fun hm => hv (Finset.mem_image.2 ⟨P, hm, HeightOneSpectrum.ext hP⟩)) x hx⟩
  refine ⟨QuotientGroup.lift _ θ hk, fun P _ hP σ hσ => ?_, fun y hy => eq_one_of_chars (Ω := ℂ) fun r => ?_⟩
  · rw [eq_inv_iff_mul_eq_one]
    refine eq_one_of_chars (Ω := ℂ) fun r => ?_
    obtain ⟨ξ, hξ, e⟩ := key r
    rw [map_mul, QuotientGroup.lift_mk, e, finPart_unifAt, hξ.val ha (N.plOm.2 P) (unrAt_of_corr ha hξ hP) hσ]
    exact inv_mul_cancel _
  · obtain ⟨ξ, hξ, e⟩ := key r
    rw [QuotientGroup.lift_mk, e]
    exact finPart_of_isUnitOver (fun P hP => unrAt_of_corr ha hξ (hQl P hP)) hy

theorem atSide_emb_mem {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (h : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) (b : Bool) (σ : D.host.E →+* ℂ) (x : D.host.E) :
    atSide X b ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ σ : D.host.E →+* ℂ, ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range := fun σ => by
    let _ : Algebra D.host.E ℂ := D.host.φ₀.toAlgebra
    have : IsScalarTower ℚ D.host.E ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast D.host.φ₀ q).symm
    have e : D.host.φ₀ (σ.toRatAlgHom.restrictNormal D.host.E x) = σ x := σ.toRatAlgHom.restrictNormal_commutes D.host.E x
    rw [← e, ← D.embE_φ₀]
    exact ⟨_, (h ⟨_, D.hostField_le_fixedField _⟩).symm⟩
  cases b
  · exact key ((starRingEnd ℂ).comp σ)
  · exact key σ

end Record

end GlobalTheory.ToricRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
section
open NumberField Formalism.IndefR.NX

namespace GlobalTheory

theorem isKsForm_of_formsIso {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G') :
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  intro f hA'
  obtain ⟨n, b, hmem, _hKi, hKs, hLi, hLs⟩ := hA'
  have hmem' : ∀ i, f.e.symm (b i) ∈ A.WK := fun i => (f.wk _).2 (by simpa using hmem i)
  have hLi' : LinearIndependent LL (fun i => f.e.symm (b i)) :=
    hLi.map' f.e.symm.toLinearMap (LinearEquiv.ker _)
  refine ⟨n, fun i => f.e.symm (b i), hmem', ?_, ?_, hLi', ?_⟩
  · refine LinearIndependent.restrict_scalars (K := LL) ?_ hLi'
    intro r s h
    have h' : algebraMap Ks LL r = algebraMap Ks LL s := by
      simpa [Algebra.algebraMap_eq_smul_one] using h
    exact (algebraMap Ks LL).injective h'
  · apply le_antisymm
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 hmem')
    · intro y hy
      have hy' : f.e y ∈ Submodule.span Ks' (Set.range b) := by rw [hKs]; exact (f.wk y).1 hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ks').1 hy'
      have hyeq : y = ∑ i, f.eK.symm (c i) • f.e.symm (b i) := by
        have : y = f.e.symm (∑ i, c i • b i) := by rw [hc]; simp
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul LL (c i) (b i), LinearEquiv.map_smul, ← algebraMap_smul LL (f.eK.symm (c i)),
          ← f.eK_LL, RingEquiv.apply_symm_apply]
      rw [hyeq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : Set.range (fun i => f.e.symm (b i)) = f.e.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, show (⇑f.e.symm : WL' → WL) = ⇑(f.e.symm : WL' →ₗ[LL] WL) from rfl, Submodule.span_image, hLs,
      Submodule.map_top, LinearEquiv.range]

end GlobalTheory
end

