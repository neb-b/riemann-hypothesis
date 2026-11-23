module

public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.EulerCharGaloisOfCardEq
public import GroundTheory.LocalFields.Examples
public import GroundTheory.LocalFields.Bundle0002
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Core

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [IsDiscreteRep A]

theorem coc_inj (n : ℕ) {x y : cocycles A n}
    (h : cochainOf A (cocycleι A n x) = cochainOf A (cocycleι A n y)) : x = y :=
  cocycleι_injective (cochainOf_injective h)

theorem exists_coc (n : ℕ) (c : (Fin n → G) → A) (hc : IsLocallyConstant c)
    (hd : (inhomogeneousCochains.d A n).hom c = 0) :
    ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = c := by
  refine ⟨(cochainsComplex A).cyclesMk (mkCochain A c hc) (n + 1) (by simp) ?_, ?_⟩
  · apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans hd
  · exact congrArg (cochainOf A) ((cochainsComplex A).i_cyclesMk _ _ _ _)

theorem pi_succ_eq_zero_iff (n : ℕ) (x : cocycles A (n + 1)) :
    cohomologyπ A (n + 1) x = 0 ↔ ∃ w : (Fin n → G) → A, IsLocallyConstant w ∧
      (inhomogeneousCochains.d A n).hom w = cochainOf A (cocycleι A (n + 1) x) := by
  change ((cochainsComplex A).homologyπ (n + 1)).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨cochainOf A w, isLocallyConstant_cochainOf w, ?_⟩
    rw [← cochainOf_d]
    exact congrArg (cochainOf A) hw
  · rintro ⟨w, hw, h⟩
    refine ⟨mkCochain A w hw, ?_⟩
    apply cochainOf_injective (A := A)
    exact (cochainOf_d (A := A) _).trans h

theorem pi_zero_eq_zero_iff (x : cocycles A 0) :
    cohomologyπ A 0 x = 0 ↔ cochainOf A (cocycleι A 0 x) = 0 := by
  change ((cochainsComplex A).homologyπ 0).hom x = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_zero]
  have h0 : (cochainsComplex A).d 0 0 = 0 := (cochainsComplex A).shape 0 0 (by simp)
  rw [h0]
  constructor
  · rintro ⟨w, hw⟩
    exact (congrArg (cochainOf A) hw).symm
  · intro h
    refine ⟨0, ?_⟩
    apply cochainOf_injective (A := A)
    exact h.symm

theorem core_hom {Z : Type} [AddCommGroup Z] (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z) :
    ∃ f : Z →+ cohomology A n, Function.Surjective f ∧
      ∀ z x, cochainOf A (cocycleι A n x) = φ z → f z = cohomologyπ A n x := by
  choose ψ hψ using hex
  have hadd : ∀ z z', ψ (z + z') = ψ z + ψ z' := fun z z' => coc_inj A n (by
    rw [map_add (f := _), cochainOf_add, hψ, hψ, hψ, map_add (f := _)])
  let f : Z →+ cohomology A n := AddMonoidHom.mk' (fun z => cohomologyπ A n (ψ z))
    (fun z z' => by rw [hadd, map_add (f := _)])
  have hf : ∀ z x, cochainOf A (cocycleι A n x) = φ z → f z = cohomologyπ A n x := fun z x h => by
    have : ψ z = x := coc_inj A n ((hψ z).trans h.symm)
    change cohomologyπ A n (ψ z) = _
    rw [this]
  refine ⟨f, fun y => ?_, hf⟩
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A n y
  obtain ⟨z, hz⟩ := hsurj x
  exact ⟨z, hf z x hz⟩

theorem core_quot {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (B : Submodule R Z)
    (n : ℕ) (φ : Z →+ ((Fin n → G) → A))
    (hex : ∀ z, ∃ x : cocycles A n, cochainOf A (cocycleι A n x) = φ z)
    (hsurj : ∀ x : cocycles A n, ∃ z, cochainOf A (cocycleι A n x) = φ z)
    (hB : ∀ z x, cochainOf A (cocycleι A n x) = φ z → (cohomologyπ A n x = 0 ↔ z ∈ B)) :
    ∃ e : (Z ⧸ B) ≃+ cohomology A n,
      ∀ z x, cochainOf A (cocycleι A n x) = φ z →
        e (Submodule.Quotient.mk z) = cohomologyπ A n x := by
  obtain ⟨f, hs, hf⟩ := core_hom A n φ hex hsurj
  have hk : ∀ z, f z = 0 ↔ z ∈ B := fun z => by
    obtain ⟨x, hx⟩ := hex z
    rw [hf z x hx, hB z x hx]
  let g : (Z ⧸ B) →+ cohomology A n :=
    QuotientAddGroup.lift B.toAddSubgroup f (fun z hz => (hk z).2 hz)
  have hg : ∀ z, g (Submodule.Quotient.mk z) = f z := fun z => rfl
  refine ⟨AddEquiv.ofBijective g ⟨?_, ?_⟩, fun z x h => (hg z).trans (hf z x h)⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective B q
    rw [hg, hk] at hq
    exact (Submodule.Quotient.mk_eq_zero B).2 hq
  · intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨_, hg z⟩

end Core

theorem neg_one_pow_smul' {S V : Type} [Ring S] [AddCommGroup V] [Module S V] (j : ℕ) (v : V) :
    (-1 : S) ^ j • v = (-1 : ℤ) ^ j • v := by
  rw [← Int.cast_smul_eq_zsmul S]
  simp

section Cmp

variable {k G : Type} [CommRing k] [Group G]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  (rho : Representation R G M) (A : Rep.{0} k G) (e : M ≃+ A.V)
  (he : ∀ g m, e (rho g m) = A.ρ g (e m))

theorem dn_app (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → G) :
    dn rho n f g = rho (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := rfl

include he in
theorem d_comp (n : ℕ) (f : (Fin n → G) → M) :
    (inhomogeneousCochains.d A n).hom (fun s => e (f s)) = fun s => e (dn rho n f s) := by
  funext s
  set_option synthInstance.maxHeartbeats 100000 in
    rw [inhomogeneousCochains.d_hom_apply, dn_app, map_add (f := _), map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_one_pow_smul' (S := k), neg_one_pow_smul' (S := R), map_zsmul]

theorem dn_zero (f : (Fin 0 → G) → M) (s : Fin 1 → G) :
    dn rho 0 f s = rho (s 0) (f default) - f default := by
  have h : ∀ t, f t = f default := fun t => congrArg f (Subsingleton.elim _ _)
  rw [dn_app]
  simp [h, sub_eq_add_neg]

theorem dn_one (f : G → M) (s : Fin 2 → G) :
    dn rho 1 (fun t => f (t 0)) s = rho (s 0) (f (s 1)) - f (s 0 * s 1) + f (s 0) := by
  rw [dn_app]
  simp [Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

theorem dn_two (f : G × G → M) (s : Fin 3 → G) :
    dn rho 2 (fun t => f (t 0, t 1)) s =
      rho (s 0) (f (s 1, s 2)) - f (s 0 * s 1, s 2) + f (s 0, s 1 * s 2) - f (s 0, s 1) := by
  rw [dn_app]
  have h3 : (-1 : R) ^ 3 = -1 := by norm_num
  simp [h3, Fin.sum_univ_succ, Fin.contractNth, sub_eq_add_neg, add_assoc]

end Cmp

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohEuler
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem exists_card_eq_pow (l : ℕ) [hl : Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] : ∃ k, Nat.card M = l ^ k := by
  have h : IsPGroup l (Multiplicative M) := fun g => ⟨r, by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self,
      zero_smul]⟩
  exact (IsPGroup.iff_card (p := l) (G := Multiplicative M)).1 h

theorem euler_of (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) (hF : SgcField) :
    Formalism.GaloisCohomology.LocalEulerCharK := by
  intro l hl K hK r M _ _ _ _ _ rho _ hrho
  obtain ⟨hsep, v, t, hloc, hcard⟩ := hF l K hK
  obtain ⟨A, hA, e, he⟩ := hRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := h0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := h1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := h2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := by
    rw [hA']
    exact Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne 1
  rw [hA', hcard k] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, hk]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hp2 : (((l ^ k) ^ Module.finrank ℚ_[l] K : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul, Nat.cast_mul, (div_eq_iff hp1).1 hE]
  field_simp

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem integer_padic_eq (p : ℕ) [Fact p.Prime] : 𝒪[ℚ_[p]] = PadicInt.subring p := by
  ext x
  change valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← (valuation ℚ_[p]).map_one, ← Valuation.Compatible.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem card_quotient_padic (p : ℕ) [Fact p.Prime] (m : ℕ) :
    Nat.card (𝒪[ℚ_[p]] ⧸ Ideal.span {((p ^ m : ℕ) : 𝒪[ℚ_[p]])}) = p ^ m := by
  let e : 𝒪[ℚ_[p]] ≃+* ℤ_[p] := RingEquiv.subringCongr (integer_padic_eq p)
  have h1 : Ideal.span {((p ^ m : ℕ) : ℤ_[p])} =
      (Ideal.span {((p ^ m : ℕ) : 𝒪[ℚ_[p]])}).map (e : 𝒪[ℚ_[p]] →+* ℤ_[p]) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e h1).toEquiv, Nat.cast_pow,
    ← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow m))).toEquiv, Nat.card_zmod]

theorem isSepClosure_padic (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    IsSepClosure ↥K (PadicAlgCl l) :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩

theorem gcField : SgcField := by
  intro l _ K hK
  refine ⟨isSepClosure_padic l K, ?_⟩
  obtain ⟨v, t, h1, h2⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K
  refine ⟨v, t, h1, fun m => ?_⟩
  rw [@card_quotient_span_natCast_finiteExtension ℚ_[l] K _ _ _ _ _ v t h1 _ h2 hK,
    card_quotient_padic]

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohMu
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem cycKSpec : Formalism.GaloisCohomology.CycKSpec := by
  intro l _ K r σ ζ hζ
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) ζ hζ

theorem gcMu : SgcMu := by
  intro l hl K r
  have : IsSepClosure ↥K (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl l) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl l)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g x =
        (Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine cycKSpec l K r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTateA
section
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

attribute [local instance 2000] Rep.hV2

section Alg

variable {n : ℕ}

theorem bij_transport {X Y Z X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module (ZMod n) X] [Module (ZMod n) Y] [Module (ZMod n) Z] [AddCommGroup X'] [AddCommGroup Y']
    (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] Z) (β : X' →+ Y' →+ ZMod n) (eX : X ≃+ X') (eY : Y ≃+ Y')
    (τ : Z ≃+ ZMod n) (h : ∀ x y, τ (c x y) = β (eX x) (eY y)) (hβ : Function.Bijective β) :
    Function.Bijective c := by
  refine ⟨fun x₁ x₂ hx => ?_, fun φ => ?_⟩
  · refine eX.injective (hβ.1 (AddMonoidHom.ext fun y' => ?_))
    obtain ⟨y, rfl⟩ := eY.surjective y'
    rw [← h, ← h, hx]
  · obtain ⟨x', hx'⟩ := hβ.2
      (τ.toAddMonoidHom.comp (φ.toAddMonoidHom.comp eY.symm.toAddMonoidHom))
    obtain ⟨x, rfl⟩ := eX.surjective x'
    refine ⟨x, LinearMap.ext fun y => τ.injective ?_⟩
    rw [h, hx']
    simp

theorem nsmul_zmod {Y : Type*} [AddCommGroup Y] [Module (ZMod n) Y] (y : Y) : n • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

theorem bij_flip [NeZero n] {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module (ZMod n) X] [Module (ZMod n) Y] [Module (ZMod n) Z] [Finite Y]
    (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] Z) (τ : Z ≃+ ZMod n) (hc : Function.Bijective c) :
    Function.Bijective c.flip := by
  let β : Y →+ X →+ ZMod n :=
    (AddMonoidHom.compHom τ.toAddMonoidHom).comp (bilinAddHom c.flip)
  refine bij_transport c.flip β (AddEquiv.refl _) (AddEquiv.refl _) τ (fun _ _ => rfl) ?_
  refine bijective_of_bijective_flip (X := Y) nsmul_zmod (bilinAddHom c.flip) τ.toAddMonoidHom ?_
  refine ⟨fun x₁ x₂ hx => hc.1 (LinearMap.ext fun y => τ.injective ?_), fun χ => ?_⟩
  · exact DFunLike.congr_fun hx y
  · obtain ⟨x, hx⟩ := hc.2 ((τ.symm.toAddMonoidHom.comp χ).toZModLinearMap n)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    change τ (c x y) = χ y
    rw [hx]
    simp

end Alg

section Core

variable {n : ℕ} {G : Type} [Group G]
  {M M' P : Type} [AddCommGroup M] [Module (ZMod n) M] [AddCommGroup M'] [Module (ZMod n) M']
  [AddCommGroup P] [Module (ZMod n) P]
  (rho : Representation (ZMod n) G M) (rho' : Representation (ZMod n) G M')
  (rhoP : Representation (ZMod n) G P) (b : M →ₗ[ZMod n] M' →ₗ[ZMod n] P)
  (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
  (A D : Rep.{0} (ULift.{0} ℤ) G) (eA : M ≃+ A.V) (hA : ∀ g m, eA (rho g m) = A.ρ g (eA m))
  (eD : P ≃+ D.V) (hD : ∀ g m, eD (rhoP g m) = D.ρ g (eD m))

include hbe hA hD in
theorem exists_dualEquiv (hb : Function.Bijective b.flip) :
    ∃ eB : M' ≃+ (dualRep D A).V, (∀ g y, eB (rho' g y) = (dualRep D A).ρ g (eB y)) ∧
      ∀ x y, (eB y : A →ₗ[ULift.{0} ℤ] D) (eA x) = eD (b x y) := by
  let F : M' →+ (A.V →+ D.V) :=
    { toFun := fun y => eD.toAddMonoidHom.comp
        ((b.flip y).toAddMonoidHom.comp eA.symm.toAddMonoidHom)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  have hF : Function.Bijective F := by
    refine ⟨fun y₁ y₂ hy => hb.1 (LinearMap.ext fun x => eD.injective ?_), fun χ => ?_⟩
    · simpa [F] using DFunLike.congr_fun hy (eA x)
    · obtain ⟨y, hy⟩ := hb.2
        ((eD.symm.toAddMonoidHom.comp (χ.comp eA.toAddMonoidHom)).toZModLinearMap n)
      refine ⟨y, AddMonoidHom.ext fun a => ?_⟩
      change eD (b.flip y (eA.symm a)) = χ a
      rw [hy]
      simp
  let eB : M' ≃+ (A →ₗ[ULift.{0} ℤ] D) :=
    (AddEquiv.ofBijective F hF).trans (uliftIntLinearEquivAddHom A.V D.V).symm
  have h2 : ∀ x y, eB y (eA x) = eD (b x y) := fun x y => by
    simp [eB, uliftIntLinearEquivAddHom_symm_apply, F]
  refine ⟨eB, fun g y => LinearMap.ext fun a => ?_, h2⟩
  obtain ⟨x, rfl⟩ := eA.surjective a
  change eB (rho' g y) (eA x) = D.ρ g (eB y (A.ρ g⁻¹ (eA x)))
  rw [← hA, h2, h2, ← hD, ← hbe, Representation.self_inv_apply]

end Core

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

