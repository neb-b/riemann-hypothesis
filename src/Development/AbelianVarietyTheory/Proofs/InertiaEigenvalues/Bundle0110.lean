module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCharpolyInvAlgBaseChangeUnramified
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_separable : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  intro K K' d φ _ B ψ hψ hσ hsep

  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hsep

  have hP : aeval B.g B.P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
    have h2 : aeval (LinearMap.mulLeft K.E B.g) B.P = Algebra.lmul K.E B.A (aeval B.g B.P) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    have h3 := congrArg (fun f : Module.End K.E B.A => f 1) (h2.symm.trans h1)
    simpa using h3
  set B' := overExt φ B ψ hψ hσ with hB'
  have hg : B'.g = B.g := rfl
  have hmap : ∀ x : K'.E, algebraMap K'.E B'.A x = ψ x := fun x => rfl
  have hint : IsIntegral K'.E B'.g := Algebra.IsIntegral.isIntegral _

  have htop : Algebra.adjoin K'.E {B'.g} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : (y : B.A) = ∑ i, (e.repr y i) • e i := (e.sum_repr y).symm
    change (y : B'.A) ∈ Algebra.adjoin K'.E {B'.g}
    have : (y : B'.A) = ∑ i, algebraMap K'.E B'.A (φ (e.repr y i)) * B'.g ^ (i : ℕ) := by
      refine hy.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hmap, hψ, he, Algebra.smul_def]; rfl
    rw [this]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hchar : B'.P = minpoly K'.E B'.g := by
    have h1 := charpoly_leftMulMatrix pb
    rw [PowerBasis.ofAdjoinEqTop_gen] at h1
    rw [← h1, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    rfl
  have hdvd : minpoly K'.E B'.g ∣ B.P.map φ := by
    refine minpoly.dvd _ _ ?_
    rw [aeval_def, eval₂_map]
    have : (algebraMap K'.E B'.A).comp φ = algebraMap K.E B.A := RingHom.ext fun x => hψ x
    rw [this]
    exact hP
  rw [hchar]
  exact (hsep.map).of_dvd hdvd

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPowGeneratorEqTopOfCharpolySeparable
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem span_pow_eq_top_of_separable (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  have hint : IsIntegral K.E B.g := Algebra.IsIntegral.isIntegral _
  have hz : minpoly K.E B.g ≠ 0 := minpoly.ne_zero hint
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hdvd : B.P ∣ minpoly K.E B.g := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
      Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
    intro p hp
    rw [Polynomial.mem_normalizedFactors_iff hP] at hp
    rw [Polynomial.mem_normalizedFactors_iff hz]
    exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
  have hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree := by
    have h1 : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [← h1]
    exact natDegree_le_of_dvd hdvd hz
  have hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ) :=
    linearIndependent_pow B.g
  have hge := hli.fintype_card_le_finrank
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticeLeIntegralUnitsSubgroup
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩

theorem stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StabilizerStableLatticePairRelIndexIntegralUnits
section
noncomputable section

namespace GlobalTheory.UnitLemma.PairStab

open GlobalTheory.UnitLemma Polynomial

theorem relIndex_prod_prod {A B : Type} [Group A] [Group B] (H₁ K₁ : Subgroup A) (H₂ K₂ : Subgroup B) :
    (H₁.prod H₂).relIndex (K₁.prod K₂) = H₁.relIndex K₁ * H₂.relIndex K₂ := by
  have h : (H₁.prod H₂).subgroupOf (K₁.prod K₂) =
      ((H₁.subgroupOf K₁).prod (H₂.subgroupOf K₂)).comap (K₁.prodEquiv K₂).toMonoidHom := by
    ext x
    rfl
  unfold Subgroup.relIndex
  rw [h, Subgroup.index_comap_of_surjective _ (K₁.prodEquiv K₂).surjective, Subgroup.index_prod]

section

variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]

theorem intUnits_prod_eq :
    intUnits O (A₁ × A₂) = ((intUnits O A₁).prod (intUnits O A₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  change (IsIntegral O (t : A₁ × A₂) ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂)) ↔
    (IsIntegral O (t : A₁ × A₂).1 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).1) ∧
    (IsIntegral O (t : A₁ × A₂).2 ∧ IsIntegral O ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂).2)
  rw [IsIntegral.pair_iff, IsIntegral.pair_iff]
  tauto

variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]

theorem stabilizer_latPair_eq (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂) :
    MulAction.stabilizer (A₁ × A₂)ˣ y = ((MulAction.stabilizer A₁ˣ y.1).prod
      (MulAction.stabilizer A₂ˣ y.2)).comap (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by
  ext t
  rw [MulAction.mem_stabilizer_iff, latPair_smul, Subgroup.mem_comap, Subgroup.mem_prod,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Prod.ext_iff

end

theorem stabilizer_pair_relIndex : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂), MulAction.stabilizer A₁ˣ y.1 ≤ intUnits O A₁ → MulAction.stabilizer A₂ˣ y.2 ≤ intUnits O A₂ → MulAction.stabilizer (A₁ × A₂)ˣ y ≤ intUnits O (A₁ × A₂) ∧ (MulAction.stabilizer (A₁ × A₂)ˣ y).relIndex (intUnits O (A₁ × A₂)) = (MulAction.stabilizer A₁ˣ y.1).relIndex (intUnits O A₁) * (MulAction.stabilizer A₂ˣ y.2).relIndex (intUnits O A₂) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ y h₁ h₂
  rw [stabilizer_latPair_eq, intUnits_prod_eq]
  refine ⟨Subgroup.comap_mono (fun t ht => ⟨h₁ ht.1, h₂ ht.2⟩), ?_⟩
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
    (f := (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom) MulEquiv.prodUnits.surjective,
    relIndex_prod_prod]

end GlobalTheory.UnitLemma.PairStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticeOrbitCountEqSumOrbits
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma

section Bridge

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem stabLat_eq_stabilizer (g : A) (L : stLat O E g) :
    stabLat O (L : Submodule O A) = MulAction.stabilizer Aˣ L := by
  ext t
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, stLat_smul_val]
  constructor
  · intro h
    ext x
    rw [mem_mulLat_iff]
    have := h (((t⁻¹ : Aˣ) : A) * x)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this
  · intro h y
    have := SetLike.ext_iff.mp h ((t : A) * y)
    rw [mem_mulLat_iff, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this

def orbEquiv (g : A) : Orb O (⊤ : Subgroup Aˣ) (stLat O E g) ≃ MulAction.orbitRel.Quotient Aˣ (stLat O E g) where
  toFun := Quot.lift (fun L => (Quotient.mk _ L : MulAction.orbitRel.Quotient Aˣ (stLat O E g)))
    (by
      rintro L M ⟨t, -, h⟩
      exact (Quotient.sound (show M ∈ MulAction.orbit Aˣ L from ⟨t, Subtype.ext (by rw [stLat_smul_val]; exact h.symm)⟩)).symm)
  invFun := Quotient.lift (fun L => (Quot.mk _ L : Orb O (⊤ : Subgroup Aˣ) (stLat O E g)))
    (by
      rintro a b ⟨t, ht⟩
      exact (Quot.sound ⟨t, Subgroup.mem_top t, by rw [← ht, stLat_smul_val]⟩).symm)
  left_inv := by
    intro o
    induction o using Quot.ind
    rfl
  right_inv := by
    intro o
    induction o using Quotient.inductionOn
    rfl

theorem stabilizer_eq_of_mem_orbit (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by
  obtain ⟨t, rfl⟩ := h
  ext s
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_smul, mul_comm, ← smul_smul,
    smul_left_cancel_iff]

theorem countGL_eq_sum_orbits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
    (g : A) : countGL O E g = ∑ᶠ o : MulAction.orbitRel.Quotient Aˣ (stLat O E g),
      ((MulAction.stabilizer Aˣ (Quotient.out o)).relIndex (intUnits O A) : ℚ) := by
  change orbSum O ⊤ (stLat O E g) (fun _ => 1) = _
  unfold orbSum
  rw [← finsum_comp_equiv (orbEquiv (O := O) (E := E) g)]
  refine finsum_congr fun o => ?_
  have h1 : (Quotient.mk _ (Quot.out o) : MulAction.orbitRel.Quotient Aˣ (stLat O E g)) = orbEquiv g o := by
    conv_rhs => rw [← Quot.out_eq o]
    rfl
  have h2 := Quotient.out_eq (orbEquiv (O := O) (E := E) g o)
  have h3 := Quotient.exact (h2.trans h1.symm)
  rw [one_mul, inf_top_eq, inf_top_eq, stabLat_eq_stabilizer g (Quot.out o),
    stabilizer_eq_of_mem_orbit g h3]

end Bridge

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairOrbitsFiniteAndCardProd
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section PairOrbits

variable (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
  [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂)

theorem latPair_orbitRel_iff (p q : LatPair O E g₁ g₂) :
    (MulAction.orbitRel (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) p q ↔
      (MulAction.orbitRel A₁ˣ (stLat O E g₁)) p.1 q.1 ∧ (MulAction.orbitRel A₂ˣ (stLat O E g₂)) p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
    refine ⟨MulEquiv.prodUnits.symm (t₁, t₂), ?_⟩
    rw [latPair_smul]
    have e₁ : Units.map (MonoidHom.fst A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₁ :=
      congrArg Prod.fst (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    have e₂ : Units.map (MonoidHom.snd A₁ A₂) (MulEquiv.prodUnits.symm (t₁, t₂)) = t₂ :=
      congrArg Prod.snd (MulEquiv.prodUnits.apply_symm_apply (t₁, t₂))
    rw [e₁, e₂, h₁, h₂]
    rfl

def latPairOrbitEquiv :
    MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂) ≃
      MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂) where
  toFun := Quotient.lift (fun p : LatPair O E g₁ g₂ => ((Quotient.mk _ p.1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)),
      (Quotient.mk _ p.2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))))
    (fun p q h => by
      obtain ⟨h₁, h₂⟩ := (latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ p q).1 h
      exact Prod.ext (Quotient.sound h₁) (Quotient.sound h₂))
  invFun x := Quotient.lift₂ (fun (a : stLat O E g₁) (b : stLat O E g₂) =>
      (Quotient.mk _ ((a, b) : LatPair O E g₁ g₂) : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)))
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound
      ((latPair_orbitRel_iff O E A₁ A₂ g₁ g₂ (a₁, b₁) (a₂, b₂)).2 ⟨h₁, h₂⟩)) x.1 x.2
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h p => rfl
  right_inv x := by
    obtain ⟨x₁, x₂⟩ := x
    induction x₁ using Quotient.inductionOn with
    | h a => induction x₂ using Quotient.inductionOn with
      | h b => rfl

end PairOrbits

theorem latPair_orbit_finite_and_sum : ∀ (O E A₁ A₂ : Type) [CommRing O] [Field E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] (g₁ : A₁) (g₂ : A₂), Finite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) → Finite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) → Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) ∧ ∀ (f₁ : stLat O E g₁ → ℚ) (f₂ : stLat O E g₂ → ℚ), (∀ (t : A₁ˣ) (y : stLat O E g₁), f₁ (t • y) = f₁ y) → (∀ (t : A₂ˣ) (y : stLat O E g₂), f₂ (t • y) = f₂ y) → ∑ᶠ o : MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂), f₁ (Quotient.out o).1 * f₂ (Quotient.out o).2 = (∑ᶠ o : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁), f₁ (Quotient.out o)) * (∑ᶠ o : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂), f₂ (Quotient.out o)) := by
  intro O E A₁ A₂ _ _ _ _ _ _ _ _ g₁ g₂ h₁ h₂
  let e := latPairOrbitEquiv O E A₁ A₂ g₁ g₂
  haveI hfin : Finite (MulAction.orbitRel.Quotient (A₁ × A₂)ˣ (LatPair O E g₁ g₂)) := Finite.of_equiv _ e.symm
  refine ⟨hfin, ?_⟩
  intro f₁ f₂ hf₁ hf₂

  have inv₁ : ∀ a b : stLat O E g₁, (MulAction.orbitRel A₁ˣ (stLat O E g₁)) a b → f₁ a = f₁ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₁ t b
  have inv₂ : ∀ a b : stLat O E g₂, (MulAction.orbitRel A₂ˣ (stLat O E g₂)) a b → f₂ a = f₂ b := by
    intro a b h
    obtain ⟨t, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact hf₂ t b
  have key : ∀ x : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁) × MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂),
      f₁ (Quotient.out (e.symm x)).1 * f₂ (Quotient.out (e.symm x)).2 = f₁ (Quotient.out x.1) * f₂ (Quotient.out x.2) := by
    intro x
    have hx : e (e.symm x) = x := e.apply_symm_apply x
    set o := e.symm x
    have h1 : (Quotient.mk _ (Quotient.out o).1 : MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁)) = x.1 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    have h2 : (Quotient.mk _ (Quotient.out o).2 : MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂)) = x.2 := by
      rw [← hx]
      conv_rhs => rw [← Quotient.out_eq o]
      rfl
    rw [inv₁ _ _ (Quotient.exact (h1.trans (Quotient.out_eq x.1).symm)),
      inv₂ _ _ (Quotient.exact (h2.trans (Quotient.out_eq x.2).symm))]
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₁ˣ (stLat O E g₁))
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient A₂ˣ (stLat O E g₂))
  rw [← finsum_comp_equiv e.symm]
  simp_rw [key]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type,
    Finset.sum_mul_sum]

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnits
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem latProj_smul (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) :
    latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  rw [latPair_smul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).comap (LinearMap.inl O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.fst A₁ A₂) t : A₁ˣ) : A₁) ((M : Submodule O (A₁ × A₂)).comap (LinearMap.inl O A₁ A₂))
    ext y
    rw [Submodule.mem_comap, mem_mulLat_iff, mem_mulLat_iff, Submodule.mem_comap]
    have h : ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂) * (LinearMap.inl O A₁ A₂ y) =
        LinearMap.inl O A₁ A₂ (((Units.map (MonoidHom.fst A₁ A₂) t)⁻¹ : A₁ˣ) * y) := by
      ext <;> simp
    rw [h]
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).map (LinearMap.snd O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.snd A₁ A₂) t : A₂ˣ) : A₂) ((M : Submodule O (A₁ × A₂)).map (LinearMap.snd O A₁ A₂))
    unfold mulLat
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableAbsNormRpowHeightOneSpectrum
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_absNorm_rpow_heightOneSpectrum :
    ∀ (F : Type) [Field F] [NumberField F] (σ : ℝ), 1 < σ →
      Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) :=
  fun F _ _ σ hσ => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 σ hσ).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntOfIsIntegral
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem IsUnrExt.ne_zero {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : d ≠ 0 := by
  intro hd
  have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
    rw [K'.card_res, hU.1, hd, pow_zero, one_pow]
  have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
  omega

theorem trace_int_of_isIntegral {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E)
    (hz : @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra z) :
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra z = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)
  have h := Algebra.isIntegral_trace (R := K.O) (L := K.E) hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha.symm⟩

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquivStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), ((SelfDual μ B ∧ ∀ x : V, AEMeasurable (x + ·) μ) → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  obtain ⟨htransport, hfour⟩ := GlobalTheory.transport_selfDual_fourB h hc hs μ B
  exact ⟨fun hsd => (htransport hsd).1, hfour⟩
end

