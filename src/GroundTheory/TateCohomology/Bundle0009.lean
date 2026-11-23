module

public import Mathlib
public import GroundTheory.TateCohomology.Bundle0008
public import GroundTheory.TateCohomology.Bundle0006
public import GroundTheory.TateCohomology.CoresRes
public import GroundTheory.TateCohomology.DimensionShift

@[expose] public section

-- bundled from GroundTheory.TateCohomology.CohTrivial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section Index

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem index_smul_tateCohomology_eq_zero (A : Rep.{u} k G) (n : ℤ) (P : Subgroup G) [Fintype P]
    (hP : IsZero (tateCohomology (res P.subtype A) n)) (x : tateCohomology A n) :
    P.index • x = 0 := by
  have hm : P.index • 𝟙 (tateCohomology A n) = 0 := by
    rw [← tateRes_app_comp_tateCores_app P A n, hP.eq_of_tgt ((tateRes P n).app A) 0, zero_comp]
  have h := congrArg (fun φ : tateCohomology A n ⟶ tateCohomology A n => φ.hom x) hm
  simpa using h

theorem isZero_tateCohomology_of_index (A : Rep.{u} k G) (n : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Subgroup G, ¬ p ∣ P.index ∧
      ∀ [Fintype P], IsZero (tateCohomology (res P.subtype A) n)) :
    IsZero (tateCohomology A n) := by
  have hx : ∀ x : tateCohomology A n, x = 0 := by
    intro x
    by_contra hne
    have ho : addOrderOf x ∣ Fintype.card G :=
      addOrderOf_dvd_of_nsmul_eq_zero (card_smul_tateCohomology A n x)
    have ho1 : addOrderOf x ≠ 1 := fun h1 => hne (AddMonoid.addOrderOf_eq_one_iff.1 h1)
    obtain ⟨P, hidx, hP⟩ := h _ (Nat.minFac_prime ho1) ((Nat.minFac_dvd _).trans ho)
    let _ : Fintype P := Fintype.ofFinite P
    exact hidx ((Nat.minFac_dvd _).trans
      (addOrderOf_dvd_of_nsmul_eq_zero (index_smul_tateCohomology_eq_zero A n P hP x)))
  have : Subsingleton (tateCohomology A n) := ⟨fun a b => by rw [hx a, hx b]⟩
  exact ModuleCat.isZero_of_subsingleton _

end Index

section Subgroups

variable {k G : Type u} [CommRing k] [Group G]

theorem tateAcyclic_res_res_iff (A : Rep.{u} k G) (S : Subgroup G) (T : Subgroup S) [Fintype T]
    (U : Subgroup G) [Fintype U] (hU : T.map S.subtype = U) :
    TateAcyclic (res T.subtype (res S.subtype A)) ↔ TateAcyclic (res U.subtype A) := by
  subst hU
  let U := T.map S.subtype
  let φ : T →* U := (S.subtype.comp T.subtype).codRestrict U fun t =>
    Subgroup.mem_map.2 ⟨t, t.2, rfl⟩
  have hinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun x : U => (x : G)) hab))
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hu
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [← tateAcyclic_res_iff φ ⟨hinj, hsurj⟩ (res U.subtype A)]
  have e : U.subtype.comp φ = S.subtype.comp T.subtype := rfl
  rw [res_res φ U.subtype A, e, res_res]

theorem tateAcyclic_res_of_le {A : Rep.{u} k G} {P : Subgroup G} (hP : CohTrivial (res P.subtype A))
    {V : Subgroup G} [Fintype V] (hV : V ≤ P) : TateAcyclic (res V.subtype A) := by
  classical
  let _ : Fintype (V.subgroupOf P) :=
    Fintype.ofInjective (fun x : V.subgroupOf P => (⟨(x : P), Subgroup.mem_subgroupOf.1 x.2⟩ : V))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun y : V => (y : G)) hab))
  refine (tateAcyclic_res_res_iff A P (V.subgroupOf P) V ?_).1 (hP _)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hV]

end Subgroups

section Sylow

variable {G : Type} [Group G] [Fintype G]

theorem cohTrivial_of_sylow (A : Rep ℤ G)
    (h : ∀ p : ℕ, p.Prime → ∃ (P : Sylow p G) (q : ℤ), ∀ [Fintype (P : Subgroup G)],
      IsZero (tateCohomology (res (P : Subgroup G).subtype A) q) ∧
        IsZero (tateCohomology (res (P : Subgroup G).subtype A) (q + 1))) :
    CohTrivial A := by
  classical

  have hSyl : ∀ p : ℕ, p.Prime → ∃ P : Sylow p G, CohTrivial (res (P : Subgroup G).subtype A) := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, q, hPq⟩ := h p hp
    let _ : Fintype (P : Subgroup G) := Fintype.ofFinite _
    exact ⟨P, cohTrivial_of_isZero_of_isZero P.isPGroup' _ q (hPq).1 (hPq).2⟩

  have hp_sub : ∀ (p : ℕ), p.Prime → ∀ (U : Subgroup G) [Fintype U], IsPGroup p U →
      TateAcyclic (res U.subtype A) := by
    intro p hp U _ hU
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := hSyl p hp
    obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
    let V : Subgroup G := U.comap (MulAut.conj g).toMonoidHom
    let _ : Fintype V := Fintype.ofFinite _
    have hVP : V ≤ P := by
      intro y hy
      have h1 : g * y * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := hUQ hy
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      simpa [mul_assoc] using h1
    refine tateAcyclic_res_conj U V g (fun x => ?_) (tateAcyclic_res_of_le hP hVP)
    simp [V, mul_assoc]
  intro S _ n
  refine isZero_tateCohomology_of_index (res S.subtype A) n fun p hp _ => ?_
  have : Fact p.Prime := ⟨hp⟩
  let T : Sylow p S := default
  refine ⟨T, T.not_dvd_index, fun {_} => ?_⟩
  let _ : Fintype ((T : Subgroup S).map S.subtype) := Fintype.ofFinite _
  refine ((tateAcyclic_res_res_iff A S T _ rfl).2 ?_) n
  exact hp_sub p hp _ (T.isPGroup'.map S.subtype)

theorem cohTrivial_of_forall_subgroup (A : Rep ℤ G) (q : ℤ)
    (h : ∀ (S : Subgroup G) [Fintype S], IsZero (tateCohomology (res S.subtype A) q) ∧
      IsZero (tateCohomology (res S.subtype A) (q + 1))) :
    CohTrivial A := by
  classical
  refine cohTrivial_of_sylow A fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨default, q, fun {_} => h _⟩

end Sylow

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.CupTateNatural
section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Naturality





theorem tateIsoH_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (n : ℕ) [NeZero n]
    (x : tateCohomology X n) :
    (tateIsoH Y n n rfl).hom.hom (((tateCohomologyFunctor n).map φ).hom x) =
      groupCohomology.map (MonoidHom.id G) φ n ((tateIsoH X n n rfl).hom.hom x) :=
  congr(($((TateCohomology.isoGroupCohomology n).hom.naturality φ)).hom x)

end Naturality

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.TateCupUnit
section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Unitors

variable (E : ShortComplex (Rep.{u} k G))

noncomputable def leftUnitorSCIso : E.map (tensorLeft (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (λ_ E.X₁) (λ_ E.X₂) (λ_ E.X₃) (leftUnitor_naturality E.f).symm
    (leftUnitor_naturality E.g).symm

noncomputable def rightUnitorSCIso : E.map (tensorRight (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (ρ_ E.X₁) (ρ_ E.X₂) (ρ_ E.X₃) (rightUnitor_naturality E.f).symm
    (rightUnitor_naturality E.g).symm

variable {E}

theorem shortExact_tensorLeft_unit (hE : E.ShortExact) :
    (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (leftUnitorSCIso E).symm hE

theorem shortExact_tensorRight_unit (hE : E.ShortExact) :
    (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (rightUnitorSCIso E).symm hE

variable [Fintype G]

theorem δ_leftUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (𝟙_ (Rep.{u} k G) ⊗ E.X₃) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (λ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (λ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (leftUnitorSCIso E).hom i)).hom x).symm

theorem δ_rightUnitor_apply (hE : E.ShortExact)
    (hE' : (E.map (tensorRight (𝟙_ (Rep.{u} k G)))).ShortExact) (i : ℤ)
    (x : tateCohomology (E.X₃ ⊗ 𝟙_ (Rep.{u} k G)) i) :
    (TateCohomology.δ hE i).hom (((tateCohomologyFunctor i).map (ρ_ E.X₃).hom).hom x) =
      ((tateCohomologyFunctor (i + 1)).map (ρ_ E.X₁).hom).hom ((TateCohomology.δ hE' i).hom x) :=
  congr(($(TateCohomology.δ_naturality hE' hE (rightUnitorSCIso E).hom i)).hom x).symm

end Unitors

variable [Fintype G]


variable (k G) in
noncomputable def tateOne : tateCohomology (𝟙_ (Rep.{u} k G)) 0 :=
  ((tateCohomologyZeroIso k G).app (𝟙_ (Rep.{u} k G))).inv.hom
    (Submodule.Quotient.mk ⟨(1 : k), fun _ => rfl⟩)


set_option maxHeartbeats 800000 in
theorem leftUnitor_tateCup_tateOne_zero (B : Rep.{u} k G) (b : tateCohomology B 0) :
    ((tateCohomologyFunctor 0).map (λ_ B).hom).hom
      (tateCup 0 0 (𝟙_ (Rep.{u} k G)) B 0 (zero_add 0) (tateOne k G) b) = b := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (((tateCohomologyZeroIso k G).app B).hom.hom b)
  have hb : b = ((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y) := by
    rw [hy]
    exact (((tateCohomologyZeroIso k G).app B).hom_inv_id_apply b).symm
  subst hb
  have h0 := tateCup_zero_zero (𝟙_ (Rep.{u} k G)) B ⟨(1 : k), fun _ => rfl⟩ y
  refine (congrArg (((tateCohomologyFunctor 0).map (λ_ B).hom).hom) h0).trans ?_
  have hn := congr(($((tateCohomologyZeroIso k G).inv.naturality (λ_ B).hom)).hom
    (Submodule.Quotient.mk (tensorInvariants (⟨(1 : k), fun _ => rfl⟩ :
      (𝟙_ (Rep.{u} k G)).ρ.invariants) y)))
  refine hn.symm.trans ?_
  change ((tateCohomologyZeroIso k G).inv.app B).hom (Submodule.Quotient.mk _) = _
  congr 2
  apply Subtype.ext
  change (λ_ B).hom.hom ((1 : k) ⊗ₜ[k] (y : B)) = y
  rw [leftUnitor_hom_tmul, one_smul]

theorem leftUnitor_tateCup_tateOne_down (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q'),
      ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := augSES_shortExact B
  have hAE := augSES_tensorLeft_shortExact (𝟙_ (Rep.{u} k G)) B
  have hiso : IsIso (TateCohomology.δ hE q) :=
    isIso_δ_of_tateAcyclic hE (tateAcyclic_leftRegular_tensor B) q
  apply moduleIso_hom_injective (@asIso _ _ _ _ _ hiso)
  refine (δ_leftUnitor_apply hE hAE q _).trans ?_
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) b
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr).trans ?_
  exact h _ _

theorem leftUnitor_tateCup_tateOne_up (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q),
      ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q') :
    ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := coindSES_shortExact B
  have hAE := shortExact_tensorLeft_unit hE
  have hiso : IsIso (TateCohomology.δ hE q) := isIso_δ_coindSES B q
  obtain ⟨c, rfl⟩ : ∃ c, (TateCohomology.δ hE q).hom c = b :=
    ⟨(@asIso _ _ _ _ _ hiso).inv.hom b, (@asIso _ _ _ _ _ hiso).inv_hom_id_apply b⟩
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) c
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr.symm).trans ?_
  refine (δ_leftUnitor_apply hE hAE q _).symm.trans ?_
  exact congrArg (TateCohomology.δ hE q).hom (h _ _)

theorem leftUnitor_tateCup_tateOne (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  induction q using Int.induction_on generalizing B with
  | zero => exact leftUnitor_tateCup_tateOne_zero B b
  | succ i ih => exact leftUnitor_tateCup_tateOne_up (i : ℤ) _ rfl ih B b
  | pred i ih => exact leftUnitor_tateCup_tateOne_down _ (-(i : ℤ)) (by ring) ih B b

end GroundTheory.GroupCoh
end

