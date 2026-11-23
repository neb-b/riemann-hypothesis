module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0021
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import GroundTheory.AutomorphicForms.SatakeTriangular
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.GeometricLemma
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

abbrev leviInvSqrtModular (γ : Fin n → ℕ) : levi F n γ →* ℂ :=
  (invSqrtModular F n γ).comp leviIncl

theorem leviInvSqrtModular_ne_zero (m : levi F n γ) : leviInvSqrtModular (F := F) γ m ≠ 0 :=
  right_ne_zero_of_mul_eq_one (sqrtModular_mul_invSqrtModular (leviIncl m))

theorem exists_leviInvSqrtModular_eq_one :
    ∃ U : Subgroup (levi F n γ), IsOpen (U : Set (levi F n γ)) ∧
      ∀ u ∈ U, leviInvSqrtModular (F := F) γ u = 1 :=
  ⟨(integralGL F n).subgroupOf (levi F n γ),
    (isOpen_integralGL F n).preimage continuous_subtype_val,
    fun u hu => invSqrtModular_leviIncl_of_mem u (Subgroup.mem_subgroupOf.1 hu)⟩

theorem cellCoinvEquiv_twist (w : Equiv.Perm (Fin n)) (b : cellLeviSub F β γ w)
    (x : Representation.Coinvariants (cellRepA β γ w σ)) :
    cellCoinvEquiv β γ w σ (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ) b x) =
      normInducing σ γ w b (cellCoinvEquiv β γ w σ x) := by
  have hid := congrArg (fun ψ : leviPar F n γ (β ∘ w) →* ℂ => ψ (cellLeviSubIncl F β γ w b))
    (cellScalarHom_eq_normScalarHom (F := F) (β := β) (γ := γ) (w := w))
  rw [twist_apply, cellInducing_apply, map_smul, map_smul, cellCoinvEquiv_cellCoinvRep,
    smul_smul, smul_smul]
  show _ = (normLeviParSqrtModular F γ (β ∘ w) (cellLeviSubIncl F β γ w b)) •
    twist (normLeviParInvSqrtModular F β (γ ∘ ⇑w⁻¹)) (levJacquetAction β σ (γ ∘ ⇑w⁻¹))
      (cellInnerHom β γ w (cellLeviSubIncl F β γ w b)) (cellCoinvEquiv β γ w σ x)
  rw [twist_apply, smul_smul]
  congr 1

def indTwistHom (w : Equiv.Perm (Fin n)) :
    Representation.IntertwiningMap
      (twist (leviInvSqrtModular (F := F) γ) (indRep (cellLeviSub F β γ w) (cellInducing β γ w σ)))
      (indRep (cellLeviSub F β γ w) (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ))) :=
  ⟨(indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).toLinearMap,
    fun g => LinearMap.ext fun φ => indTwist_twist _ _ _ g φ⟩

def indCongrHom (w : Equiv.Perm (Fin n)) :
    Representation.IntertwiningMap
      (indRep (cellLeviSub F β γ w) (twist ((leviInvSqrtModular (F := F) γ).comp
        (cellLeviSub F β γ w).subtype) (cellInducing β γ w σ)))
      (indRep (cellLeviSub F β γ w) (normInducing σ γ w)) :=
  ⟨(indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).toLinearMap,
    fun g => LinearMap.ext fun φ => indCongr_indRep _ _ g φ⟩

theorem indTwistHom_injective (w : Equiv.Perm (Fin n)) :
    Function.Injective (indTwistHom (F := F) (β := β) (γ := γ) σ w) :=
  (indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).injective

theorem indTwistHom_surjective (w : Equiv.Perm (Fin n)) :
    Function.Surjective (indTwistHom (F := F) (β := β) (γ := γ) σ w) :=
  (indTwist (leviInvSqrtModular (F := F) γ) leviInvSqrtModular_ne_zero
      exists_leviInvSqrtModular_eq_one).surjective

theorem indCongrHom_injective (w : Equiv.Perm (Fin n)) :
    Function.Injective (indCongrHom (F := F) (β := β) (γ := γ) σ w) :=
  (indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).injective

theorem indCongrHom_surjective (w : Equiv.Perm (Fin n)) :
    Function.Surjective (indCongrHom (F := F) (β := β) (γ := γ) σ w) :=
  (indCongr (cellCoinvEquiv β γ w σ) (cellCoinvEquiv_twist σ w)).surjective

theorem geometricLemma (hσ : IsSmooth σ) :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
        V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
        ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
          ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
              ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
              (indRep (cellLeviSub F β γ (w j)) (normInducing σ γ (w j))),
            Function.Surjective Ψ ∧
              ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  obtain ⟨k, w, hcov, V, h0, hk, hmono, hV, hΨ⟩ := exists_filtration_jacquetModule_parabolicInd σ hσ
  refine ⟨k, w, hcov, V, h0, hk, hmono, hV, fun j => ?_⟩
  obtain ⟨Ψ₀, hsurj, hker⟩ := hΨ j
  refine ⟨(indCongrHom σ (w j)).comp ((indTwistHom σ (w j)).comp Ψ₀), ?_, fun x => ?_⟩
  · exact (indCongrHom_surjective σ (w j)).comp ((indTwistHom_surjective σ (w j)).comp hsurj)
  · rw [← hker x]
    constructor
    · intro h
      apply indTwistHom_injective σ (w j)
      apply indCongrHom_injective σ (w j)
      rw [map_zero, map_zero]
      exact h
    · intro h
      show (indCongrHom σ (w j)) ((indTwistHom σ (w j)) (Ψ₀ x)) = 0
      rw [h, map_zero, map_zero]

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.Satake
section
noncomputable section

universe u

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa HeckeAlgebra HeckeAlgebraLevel AddMonoidAlgebra

namespace Spherical

variable {n : ℕ}

theorem evalAt_polyEmb (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb (n := n) Q) = MvPolynomial.aeval (fun i => (z i : ℂ)) Q := by
  have : (evalAt z).comp (polyEmb (n := n)) = MvPolynomial.aeval (fun i => (z i : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ i) h)]
    simp
  exact AlgHom.congr_fun this Q

theorem polyEmb_esymm_mem (k : ℕ) :
    polyEmb (n := n) (MvPolynomial.esymm (Fin n) ℂ k) ∈ symmetricLaurent (n := n) := fun σ => by
  rw [← polyEmb_rename, MvPolynomial.esymm_isSymmetric (Fin n) ℂ k σ]

theorem exists_perm_of_map_eq {z z' : Fin n → ℂˣ}
    (h : Multiset.map (fun i => (z i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val) :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ :=
  _root_.UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq h

theorem exists_perm_of_evalAt_eq {z z' : Fin n → ℂˣ}
    (h : ∀ p ∈ symmetricLaurent (n := n), evalAt z p = evalAt z' p) :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  apply exists_perm_of_map_eq
  have he : ∀ k, (Multiset.map (fun i => (z i : ℂ)) Finset.univ.val).esymm k =
      (Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val).esymm k := fun k => by
    have := h _ (polyEmb_esymm_mem k)
    rwa [evalAt_polyEmb, evalAt_polyEmb, MvPolynomial.aeval_esymm_eq_multiset_esymm,
      MvPolynomial.aeval_esymm_eq_multiset_esymm] at this
  have hp : ((Multiset.map (fun i => (z i : ℂ)) Finset.univ.val).map
      fun t => Polynomial.X - Polynomial.C t).prod =
      ((Multiset.map (fun i => (z' i : ℂ)) Finset.univ.val).map
        fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
    simp only [Multiset.card_map, he]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

theorem evalAt_comp_of_mem {p : LaurentRing n} (hp : p ∈ symmetricLaurent (n := n))
    (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) : evalAt (z ∘ σ) p = evalAt z p := by
  rw [← evalAt_permAct, hp σ]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem range_satakeTransform :
    (satakeTransform μ (F := F) (n := n)).range = symmetricLaurent (n := n) := by
  refine le_antisymm (fun p hp => ?_) symmetricLaurent_le_range
  obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).1 hp
  exact satakeTransform_mem_symmetric h


theorem evalAt_comp_satakeTransform (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n))
    (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt (z ∘ σ) (satakeTransform μ h) = evalAt z (satakeTransform μ h) :=
  evalAt_comp_of_mem (satakeTransform_mem_symmetric h) z σ

theorem evalAt_comp_satakeTransform_eq_iff (z z' : Fin n → ℂˣ) :
    (evalAt z).comp (satakeTransform μ (F := F) (n := n)) = (evalAt z').comp (satakeTransform μ) ↔
      ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  constructor
  · intro hzz
    refine exists_perm_of_evalAt_eq fun p hp => ?_
    rw [← range_satakeTransform (μ := μ) (F := F)] at hp
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).1 hp
    exact AlgHom.congr_fun hzz h
  · rintro ⟨σ, rfl⟩
    exact AlgHom.ext fun h => (evalAt_comp_satakeTransform z σ h).symm

theorem sphericalCharacter_unramifiedChar_eq (w : Fin n → ℂˣ)
    (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) h =
      evalAt (w * (halfPoint F n)⁻¹) (satakeTransform μ h) := by
  rw [satakeTransform_apply, evalAt_normalize, inv_mul_cancel_right, evalAt_satake]

def IsSatakeParameter {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    (z : Fin n → ℂˣ) : Prop :=
  ∀ (h : SphericalHecke μ (F := F) (n := n)), ∀ v ∈ fixedVectors ρ (integralGL F n),
    heckeAct μ ρ (h : HeckeAlgebra μ) v = evalAt z (satakeTransform μ h) • v

theorem exists_satakeParameter {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    ∃ z : Fin n → ℂˣ, IsSatakeParameter ρ μ z := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let s₀ := LinearMap.toSpanSingleton (SphericalHecke μ (F := F) (n := n))
    (fixedVectors ρ (integralGL F n)) ⟨v₀, hv₀⟩
  let I : Ideal (SphericalHecke μ (F := F) (n := n)) := LinearMap.ker s₀
  have hsimple := isSimpleModule_fixedVectors (μ := μ) hKc hKo hρ hK
  have hsurj : Function.Surjective s₀ :=
    ((isSimpleModule_iff_toSpanSingleton_surjective).1 hsimple).2 _
      fun h => h0 (congrArg Subtype.val h)
  have hI : I.IsMaximal := by
    rw [Ideal.isMaximal_def]
    exact isSimpleModule_iff_isCoatom.1
      (IsSimpleModule.congr (LinearMap.quotKerEquivOfSurjective _ hsurj))
  letI := hI
  obtain ⟨w, hw⟩ := exists_ker_sphericalCharacter_eq (μ := μ) I
  refine ⟨w * (halfPoint F n)⁻¹, fun h v hv => ?_⟩
  rw [← sphericalCharacter_unramifiedChar_eq]
  set c := sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) h
  have hmem : h - algebraMap ℂ _ c ∈ I := by
    rw [← hw, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  obtain ⟨h', hh'⟩ := hsurj ⟨v, hv⟩
  have hkill : (h - algebraMap ℂ _ c) • (⟨v, hv⟩ : fixedVectors ρ (integralGL F n)) = 0 := by
    rw [← hh', LinearMap.toSpanSingleton_apply, smul_smul, mul_comm, ← smul_smul]
    have : (h - algebraMap ℂ _ c) • (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n)) = 0 := hmem
    rw [this, smul_zero]
  rw [sub_smul, sub_eq_zero] at hkill
  have hv' := congrArg Subtype.val hkill
  rw [coe_smul_fixedVectors, coe_smul_fixedVectors] at hv'
  rw [hv', Algebra.algebraMap_eq_smul_one, val_smul, val_one, HeckeAlgebra.coe_smul,
    heckeAct_smul_left _ (idem μ hKc hKo).mem (smooth_of_mem_fixedVectors hKo hv),
    heckeAct_idem_of_mem hKc hKo hv]

theorem algebraMap_smul_fixedVectors {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (c : ℂ) (v : fixedVectors ρ (integralGL F n)) :
    (algebraMap ℂ (SphericalHecke μ (F := F) (n := n)) c) • v = c • v := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  refine Subtype.ext ?_
  rw [coe_smul_fixedVectors, Algebra.algebraMap_eq_smul_one, val_smul, val_one,
    HeckeAlgebra.coe_smul, heckeAct_smul_left _ (idem μ hKc hKo).mem
      (smooth_of_mem_fixedVectors hKo v.2), heckeAct_idem_of_mem hKc hKo v.2]
  rfl

theorem smul_fixedVectors_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {z : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z)
    (h : SphericalHecke μ (F := F) (n := n)) (v : fixedVectors ρ (integralGL F n)) :
    h • v = evalAt z (satakeTransform μ h) • v :=
  Subtype.ext (by rw [coe_smul_fixedVectors, Submodule.coe_smul]; exact hz h v v.2)

theorem satakeParameter_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hK : fixedVectors ρ (integralGL F n) ≠ ⊥)
    {z z' : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z) (hz' : IsSatakeParameter ρ μ z') :
    ∃ σ : Equiv.Perm (Fin n), z' = z ∘ σ := by
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  refine (evalAt_comp_satakeTransform_eq_iff (μ := μ) z z').1 (AlgHom.ext fun h => ?_)
  have := (hz h v hv).symm.trans (hz' h v hv)
  exact smul_left_injective ℂ h0 this

theorem isSatakeParameter_comp {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} {z : Fin n → ℂˣ} (hz : IsSatakeParameter ρ μ z)
    (σ : Equiv.Perm (Fin n)) : IsSatakeParameter ρ μ (z ∘ σ) := fun h v hv => by
  rw [evalAt_comp_satakeTransform]
  exact hz h v hv

theorem isSatakeParameter_principalSeries (z : Fin n → ℂˣ) :
    IsSatakeParameter (principalSeries F n (paramChar F z)) μ z := by
  intro h v hv
  have hχ := isUnramified_paramChar (F := F) z
  rw [fixedVectors_eq_span hχ, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  have hs := Parabolic.isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n))
    (charRep (paramChar F z))
  rw [heckeAct_smul_right (h : HeckeAlgebra μ).mem c (hs _), heckeAct_sphericalVector hχ,
    ← sphericalCharacter_apply hχ, sphericalCharacter_paramChar, smul_comm]

end Measure

theorem finrank_fixedVectors_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ (integralGL F n) ≠ ⊥) :
    Module.finrank ℂ (fixedVectors ρ (integralGL F n)) = 1 := by
  borelize (GL (Fin n) F)
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  obtain ⟨z, hz⟩ := exists_satakeParameter (μ := (Measure.haar : Measure (GL (Fin n) F))) hρ hK
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hv₀' : (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n)) ≠ 0 :=
    fun h => h0 (congrArg Subtype.val h)
  have hsimple := isSimpleModule_fixedVectors (μ := (Measure.haar : Measure (GL (Fin n) F)))
    hKc hKo hρ hK
  have hsurj := ((isSimpleModule_iff_toSpanSingleton_surjective).1 hsimple).2 _ hv₀'
  have htop : (ℂ ∙ (⟨v₀, hv₀⟩ : fixedVectors ρ (integralGL F n))) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun v => ?_
    obtain ⟨h, rfl⟩ := hsurj v
    rw [LinearMap.toSpanSingleton_apply, smul_fixedVectors_eq hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  rw [← finrank_top, ← htop, finrank_span_singleton hv₀']

section Classification

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem nonempty_equiv_of_isSatakeParameter {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin n) F) V}
    {σ : Representation ℂ (GL (Fin n) F) W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) [ρ.IsIrreducible]
    [σ.IsIrreducible] (hKρ : fixedVectors ρ (integralGL F n) ≠ ⊥)
    (hKσ : fixedVectors σ (integralGL F n) ≠ ⊥) {z : Fin n → ℂˣ} (hzρ : IsSatakeParameter ρ μ z)
    (hzσ : IsSatakeParameter σ μ z) : Nonempty (ρ.Equiv σ) := by
  have hKc := isCompact_integralGL F n
  have hKo := isOpen_integralGL F n
  have h1 := finrank_fixedVectors_eq_one hρ hKρ
  have h2 := finrank_fixedVectors_eq_one hσ hKσ
  have : FiniteDimensional ℂ (fixedVectors ρ (integralGL F n)) :=
    Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  have : FiniteDimensional ℂ (fixedVectors σ (integralGL F n)) :=
    Module.finite_of_finrank_pos (by rw [h2]; exact one_pos)
  let f : fixedVectors ρ (integralGL F n) ≃ₗ[ℂ] fixedVectors σ (integralGL F n) :=
    LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  let e : fixedVectors ρ (integralGL F n) ≃ₗ[SphericalHecke μ (F := F) (n := n)]
      fixedVectors σ (integralGL F n) :=
    { toFun := f
      invFun := f.symm
      map_add' := f.map_add
      map_smul' := fun h v => by
        rw [RingHom.id_apply, smul_fixedVectors_eq hzρ, smul_fixedVectors_eq hzσ, f.map_smul]
      left_inv := f.left_inv
      right_inv := f.right_inv }
  exact nonempty_equiv_of_fixedVectors_equiv hKc hKo hρ hσ hKρ e

end Classification

end Spherical

end GroundTheory.Automorphic
end
end

