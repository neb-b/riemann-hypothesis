module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcLocEuler
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

private noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

private theorem ef_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  haveI := v.isPrime
  have h1 := Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal
  have h2 := Ideal.inertiaDeg_pos v.asIdeal ℤ
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (v.asIdeal.under ℤ) (NumberField.RingOfIntegers ℚ)
  rw [NumberField.RingOfIntegers.rank, Module.finrank_self] at hsum
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun q : (v.asIdeal.under ℤ).primesOver (NumberField.RingOfIntegers ℚ) =>
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨v.asIdeal, inferInstance, ⟨rfl⟩⟩)
  rw [hsum] at hle
  exact le_antisymm hle (Nat.mul_pos h1 h2)

private theorem card_H0dual {R k Γ Γ' M : Type} [Field R] [Field k] [Finite k] [Algebra R k] [Group Γ] [Group Γ']
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower R k M] [Finite M]
    (ρ : Representation k Γ M) (ρ' : Representation R Γ' M) (e : Γ' ≃* Γ) (h : ∀ g m, ρ' g m = ρ (e g) m)
    (χ : Γ →* kˣ) (χ' : Γ' →* Rˣ) (hχ : ∀ g, (χ (e g) : k) = algebraMap R k (χ' g)) :
    Nat.card (Loc.H0dual χ ρ) = Nat.card (Loc.H0dual χ' ρ') := by
  haveI : Finite R := Finite.of_injective _ (algebraMap R k).injective
  let T : Module.Dual k M →+ Module.Dual R M :=
    { toFun := fun f => (Algebra.trace R k).comp (f.restrictScalars R)
      map_zero' := by ext; simp
      map_add' := fun f f' => by ext; simp }
  have hT : ∀ f m, T f m = Algebra.trace R k (f m) := fun _ _ => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext m
    refine (traceForm_nondegenerate R k).1 (f m) fun a => ?_
    have := hT f (a • m)
    rw [hf, f.map_smul, smul_eq_mul, mul_comm] at this
    exact this.symm
  haveI : Finite (Module.Dual R M) := DFunLike.finite _
  have hbij : Function.Bijective T := hinj.bijective_of_nat_card_le (by
    rw [Module.natCard_eq_pow_finrank (K := R) (V := Dual R M), Module.natCard_eq_pow_finrank (K := k) (V := Dual k M),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank])
  refine Nat.card_congr ((Equiv.ofBijective _ hbij).subtypeEquiv fun f => ?_)
  rw [Equiv.ofBijective_apply]
  constructor
  · intro hf g x
    rw [hT, hT, h, hf, hχ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro hf g x
    obtain ⟨g, rfl⟩ := e.surjective g
    have : f.comp (ρ (e g)) = (χ (e g) : k) • f := hinj (LinearMap.ext fun y => by
      have := hf g y
      rw [hT, hT, h] at this
      rw [hT, hT, LinearMap.comp_apply, this, LinearMap.smul_apply, smul_eq_mul, hχ, ← Algebra.smul_def,
        map_smul, smul_eq_mul])
    exact LinearMap.congr_fun this x

private theorem card_twDual {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (ρ : Representation R Γ M) :
    Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id Γ))) = Nat.card (Loc.H0dual χ ρ) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (α := TDual R M) fun y => ?_)
  constructor
  · intro hy g m
    have e := congrArg (fun φ : TDual R M => φ (ρ g m)) (hy g)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at e
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e
    exact e.symm
  · intro hy g
    apply LinearMap.ext
    intro m
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply]
    have := hy g (ρ g⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem UpperTheory.V.X.locEuler :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (p : ℕ), p.Prime → ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (Dec (F := ℚ) A) M), ContAction ρ → Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧ finrank k (H1 ρ) = finrank k (H0 ρ) + finrank k (H2 ρ) + (if p = l then finrank k M else 0) ∧ finrank k (H2 ρ) = finrank k (Loc.H0dual ((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) ρ) := by
  intro hF hT hE0 Ω _ _ _ l _ p hp A hA k _ _ hc M _ _ _ _ _ ρ hρ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) A hA
  have hw : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := hw
  have hl : l.Prime := Fact.out
  haveI : Fact (l ^ 1).Prime := ⟨by rwa [pow_one]⟩
  haveI : CharP k (l ^ 1) := by rwa [pow_one]
  letI : Algebra (ZMod (l ^ 1)) k := ZMod.algebra k (l ^ 1)
  letI : Module (ZMod (l ^ 1)) M := Module.compHom M (algebraMap (ZMod (l ^ 1)) k)
  haveI : IsScalarTower (ZMod (l ^ 1)) k M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Finite M := Module.finite_of_finite k
  let ρ' : Representation (ZMod (l ^ 1)) ↥(Dec (F := ℚ) A) M := Loc.resCoef (ZMod (l ^ 1)) ρ
  have h : ∀ g m, ρ' g m = ρ (MulEquiv.refl _ g) m := fun _ _ => rfl
  have hρ' : ContAction ρ' := hρ
  have e0 : H0 ρ ≃ H0 ρ' := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have e1 : H1 ρ ≃ H1 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have e2 : H2 ρ ≃ H2 ρ' := subquotEquiv _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨-, f1, f2, -⟩ := hF ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  obtain ⟨⟨inv⟩, -, -, -, hb⟩ := hT ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  have hE := hE0 ℚ Ω l 1 M A ρ' w one_pos hAw hρ'
  haveI : Finite (H1 ρ) := Finite.of_equiv _ e1.symm
  haveI : Finite (H2 ρ) := Finite.of_equiv _ e2.symm
  have hk : 1 < Nat.card k := Finite.one_lt_card
  have hd : locDeg w = 1 := ef_eq_one w
  refine ⟨Module.Finite.of_finite, Module.Finite.of_finite, ?_, ?_⟩
  · apply Nat.pow_right_injective hk
    beta_reduce
    rw [pow_add, pow_add, ← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank,
      ← Module.natCard_eq_pow_finrank, Nat.card_congr e0, Nat.card_congr e1, Nat.card_congr e2]
    split_ifs with hvl
    · subst hvl
      have h1 : Nat.card (H1 ρ') = Nat.card (H0 ρ') * Nat.card (H2 ρ') * Nat.card M ^ locDeg w := hE.1 hw
      rw [hd, pow_one (Nat.card M)] at h1
      rw [← Module.natCard_eq_pow_finrank]
      exact h1
    · rw [pow_zero, mul_one]
      refine hE.2 fun hlw => w.isPrime.ne_top ?_
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hvl)).map
        (Int.castRingHom (𝓞 ℚ))
      rw [Ideal.eq_top_iff_one, ← hab]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by simpa using hw))
        (w.asIdeal.mul_mem_left _ (by simpa using hlw))
  · apply Nat.pow_right_injective hk
    beta_reduce
    let χ := (cycMod ℚ Ω l 1).comp (Dec (F := ℚ) A).subtype
    haveI : Finite (Module.Dual k M) := DFunLike.finite _
    haveI : Finite (TDual (ZMod (l ^ 1)) M) := (DFunLike.finite _ : Finite (M →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)))
    let B : Type := H0 ((twDual χ ρ').comp (MonoidHom.id _))
    let E : H2 ρ' ≃ Module.Dual (ZMod (l ^ 1)) B :=
      (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight inv).toEquiv
    haveI : Finite B := Subtype.finite
    haveI := hc
    have hχ : ∀ g, ((((cycK Ω l k).comp (Dec (F := ℚ) A).subtype) (MulEquiv.refl _ g) : kˣ) : k) =
        algebraMap (ZMod (l ^ 1)) k (χ g) := fun g =>
      RingHom.congr_fun (Subsingleton.elim (ZMod.castHom (dvd_pow_self l one_ne_zero) k)
        (algebraMap (ZMod (l ^ 1)) k)) _
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank, Nat.card_congr e2,
      card_H0dual ρ ρ' (MulEquiv.refl _) h _ χ hχ,
      ← card_twDual, Nat.card_congr E, Module.natCard_eq_pow_finrank (K := ZMod (l ^ 1)),
      Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUnrOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.unrOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ) (K : Subgroup (G ℚ Ω)) [K.Normal], K ≤ γ.ker → ∀ (SP : Set (HeightOneSpectrum (𝓞 ℚ))) (T : Finset ℕ) (z : GS Ω SP → k), (∀ g h, z (toGS Ω SP (g * h)) = z (toGS Ω SP g) + (γ g : k) * z (toGS Ω SP h)) → (∀ v ∈ SP, (∃ p ∈ T, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) ∨ ∃ A, IsPlaceOver A v ∧ ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0) → ∀ A : ValuationSubring Ω, (∀ p ∈ T, ¬ A.valuation (p : Ω) < 1) → ∀ g ∈ Ine (F := ℚ) A, g ∈ K → z (toGS Ω SP g) = 0 := by
  intro Ω _ _ _ k _ γ K hKn hK SP T z hz hS A hA g hg hgK
  have h1 : z (toGS Ω SP 1) = 0 := by
    have e := hz 1 1
    rw [mul_one, map_one γ, Units.val_one, one_mul] at e
    linear_combination (-1 : k) * e
  obtain ⟨hTop, hPl, -, hAb⟩ := UpperTheory.V.Kum.placeDict ℚ Ω
  by_cases hAT : A = ⊤
  · subst hAT
    rw [hTop, Subgroup.mem_bot] at hg
    subst hg
    exact h1
  obtain ⟨v, hv⟩ := hPl A hAT
  by_cases hvS : v ∈ SP
  · rcases hS v hvS with ⟨p, hpT, hp⟩ | ⟨A', hA', hz0⟩
    · exact absurd ((hAb A v p hv).mpr hp) (hA p hpT)
    · obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA' hv
      subst hσ
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) A' := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg
      have hcK : σ⁻¹ * g * σ ∈ K := by
        have e := hKn.conj_mem g hgK σ⁻¹
        simpa only [inv_inv] using e
      have e0 := hz0 _ hc hcK
      have e1 := hz g σ
      have e2 := hz σ (σ⁻¹ * g * σ)
      have hγ : γ g = 1 := hK hgK
      have hm : σ * (σ⁻¹ * g * σ) = g * σ := by group
      rw [hγ, Units.val_one, one_mul] at e1
      rw [hm, e0, mul_zero, add_zero] at e2
      linear_combination e2 - e1
  · have hN : g ∈ NS Ω SP := by
      unfold NS
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hg⟩
    have e : toGS Ω SP g = toGS Ω SP 1 := by
      rw [map_one]
      exact (QuotientGroup.eq_one_iff g).mpr hN
    rw [e]
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcUrAbs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

namespace UpperTheory.V.X.UnramifiedH1RankEqH0

variable {k D M : Type} [Field k] [Group D] [AddCommGroup M] [Module k M]

private def NI (ρ : Representation k D M) (I : Subgroup D) : Submodule k M where
  carrier := {m | ∀ s ∈ I, ρ s m = m}
  zero_mem' := fun s _ => map_zero _
  add_mem' := fun {a b} ha hb s hs => by rw [map_add (f := _), ha s hs, hb s hs]
  smul_mem' c a ha s hs := by rw [map_smul, ha s hs]

private theorem NI_stable (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (g : D) {m : M}
    (hm : m ∈ NI ρ I) : ρ g m ∈ NI ρ I := by
  intro s hs
  have h1 := hm (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹)
  calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
    _ = ρ g m := by rw [h1]

private theorem inv_apply (ρ : Representation k D M) (g : D) (m : M) : ρ g⁻¹ (ρ g m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem apply_inv (ρ : Representation k D M) (g : D) (m : M) : ρ g (ρ g⁻¹ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [TopologicalSpace D] [IsTopologicalGroup D]

private theorem all_of_closed {I : Subgroup D} {σ : D}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup D) (hH : IsClosed (H : Set D))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : D) : g ∈ H := by
  have := Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers σ)
    (sup_le hI ((Subgroup.zpowers_le).2 hσ)) hH
  rw [hd] at this
  exact this (Subgroup.mem_top g)

private theorem exists_hom {E : Type} [Group E] [Finite E] {I : Subgroup D} {φ : D}
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) (e : E) :
    ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ w φ = e := by
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  refine ⟨f.comp d, hdl.comp f, fun s hs => by simp [hdI s hs], ?_⟩
  show f (d φ) = e
  rw [hdφ, hf1]

variable [TopologicalSpace M] [DiscreteTopology M]

private theorem exists_cocycle [Finite M] (ρ : Representation k D M) (hρ : ContAction ρ) {I : Subgroup D} [I.Normal] {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) {x : M} (hx : x ∈ NI ρ I) :
    ∃ z ∈ Z1 ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  let e : Equiv.Perm (NI ρ I) :=
    { toFun := fun m => ⟨x + ρ φ m, add_mem hx (NI_stable ρ I φ m.2)⟩
      invFun := fun m => ⟨ρ φ⁻¹ (m - x), NI_stable ρ I _ (sub_mem m.2 hx)⟩
      left_inv := fun m => Subtype.ext (by simp only [add_sub_cancel_left, inv_apply])
      right_inv := fun m => Subtype.ext (by simp only [apply_inv, add_sub_cancel]) }
  obtain ⟨w, hw, hwI, hwφ⟩ := exists_hom hd e
  have hc : ∀ m : NI ρ I, Continuous fun g => ((w g m : NI ρ I) : M) := fun m =>
    (hw.comp fun σ : Equiv.Perm (NI ρ I) => ((σ m : NI ρ I) : M)).continuous
  let H : Subgroup D :=
    { carrier := {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      mul_mem' := fun {a b} ha hb m m' => by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb, Module.End.mul_apply]
      one_mem' := fun m m' => by simp
      inv_mem' := fun {a} ha m m' => by
        have h1 := ha (w a⁻¹ m) (w a⁻¹ m')
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h1
        rw [h1, inv_apply] }
  have hH : ∀ g, g ∈ H := by
    refine all_of_closed hcl H ?_ (fun s hs m m' => ?_) (fun m m' => ?_)
    · change IsClosed {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun m' => isClosed_eq ((hc m).sub (hc m'))
        (Continuous.comp (f := fun g : D => (g, (m : M) - m')) hρ (by fun_prop))
    · rw [hwI s hs, (sub_mem m.2 m'.2 : _ ∈ NI ρ I) s hs]
      rfl
    · rw [hwφ, map_sub]
      change x + ρ φ m - (x + ρ φ m') = _
      abel
  refine ⟨fun g => ((w g 0 : NI ρ I) : M), ⟨hc 0, fun g h => ?_⟩, fun s hs => ?_, ?_⟩
  · have h1 := hH g (w h 0) 0
    rw [Submodule.coe_zero, sub_zero] at h1
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [← h1]
    abel
  · simp only [hwI s hs]
    rfl
  · simp only [hwφ]
    change x + ρ φ 0 = x
    simp

private theorem eq_zero_of (ρ : Representation k D M) {I : Subgroup D} {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) {d : D → M} (hd0 : d ∈ Z1 ρ)
    (hI : ∀ s ∈ I, d s = 0) (hφ : d φ = 0) (g : D) : d g = 0 := by
  have d1 : d 1 = 0 := by
    have := hd0.2 1 1
    simpa using this
  let H : Subgroup D :=
    { carrier := {g | d g = 0}
      mul_mem' := fun {a b} ha hb => by
        change d (a * b) = 0
        rw [hd0.2, show d a = 0 from ha, show d b = 0 from hb]
        simp
      one_mem' := d1
      inv_mem' := fun {a} ha => by
        have := hd0.2 a⁻¹ a
        rw [inv_mul_cancel, d1, show d a = 0 from ha] at this
        change d a⁻¹ = 0
        simpa using this.symm }
  exact all_of_closed hcl H (isClosed_eq hd0.1 continuous_const) hI hφ g

private def Z0 (ρ : Representation k D M) (I : Subgroup D) : Submodule k (Z1 ρ) where
  carrier := {z | ∀ s ∈ I, z.1 s = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb s hs => by
    change a.1 s + b.1 s = 0
    rw [ha s hs, hb s hs, add_zero]
  smul_mem' c a ha s hs := by
    change c • a.1 s = 0
    rw [ha s hs, smul_zero]

private theorem val_mem (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (z : Z0 ρ I) (g : D) :
    z.1.1 g ∈ NI ρ I := by
  intro s hs
  have h1 := z.1.2.2 s g
  have h2 := z.1.2.2 g (g⁻¹ * s * g)
  rw [z.2 s hs, zero_add] at h1
  rw [z.2 (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹), map_zero, add_zero,
    show g * (g⁻¹ * s * g) = s * g by group] at h2
  rw [← h1, h2]

end UpperTheory.V.X.UnramifiedH1RankEqH0

open UpperTheory.V.X.UnramifiedH1RankEqH0 in
theorem UpperTheory.V.X.urAbs :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → finrank k (H1ur ρ I) = finrank k (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  haveI : FiniteDimensional k M := Module.Finite.of_finite
  let ev : Z0 ρ I →ₗ[k] NI ρ I :=
    { toFun := fun z => ⟨z.1.1 φ, val_mem ρ I z φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    refine ⟨(injective_iff_map_eq_zero ev).2 fun z hz => ?_, fun x => ?_⟩
    · exact Subtype.ext (Subtype.ext (funext
        (eq_zero_of ρ hcl z.1.2 z.2 (congrArg Subtype.val hz))))
    · obtain ⟨z, hz, hzI, hzφ⟩ := exists_cocycle ρ hρ hcl hd x.2
      exact ⟨⟨⟨z, hz⟩, hzI⟩, Subtype.ext hzφ⟩
  let E := LinearEquiv.ofBijective ev hev
  haveI : FiniteDimensional k (Z0 ρ I) := E.symm.finiteDimensional
  let p : Z0 ρ I →ₗ[k] H1 ρ := (Submodule.mkQ _).comp (Z0 ρ I).subtype
  let δ : NI ρ I →ₗ[k] Z0 ρ I :=
    { toFun := fun m => ⟨⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (m.2 s hs)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (d0 ρ) _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (d0 ρ) _ _)) }
  have h1 : LinearMap.range p = H1ur ρ I := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩)
      rw [map_zero, sub_zero]
      exact z.2 s s.2
    · intro c hc
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)
      refine ⟨⟨z - ⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs =>
        sub_eq_zero.2 (show z.1 s = d0 ρ m s from hm ⟨s, hs⟩)⟩, ?_⟩
      refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.subtype_apply, sub_sub_cancel_left]
      exact neg_mem ⟨m, rfl⟩
  have h2 : LinearMap.range δ = LinearMap.ker p := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
    · intro z hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
      refine ⟨⟨m, fun s hs => sub_eq_zero.1 ((hm s).symm.trans (z.2 s hs))⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))
  have h3 : (LinearMap.ker δ).map (NI ρ I).subtype = H0 ρ := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩ g
      exact sub_eq_zero.1 (congrFun (congrArg (fun z : Z0 ρ I => z.1.1) hm) g)
    · intro m hm
      exact ⟨⟨m, fun s _ => hm s⟩, Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g))), rfl⟩
  have a1 := p.finrank_range_add_finrank_ker
  have a2 := δ.finrank_range_add_finrank_ker
  have a3 := E.finrank_eq
  rw [← h1, ← h3, Submodule.finrank_map_subtype_eq]
  rw [h2] at a2
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.bkMap :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (C V : Type) [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (C' V' : Type) [CommRing C'] [Algebra ℚ_[l] C'] [AddCommGroup V'] [Module C' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C' V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul C' V'] (ρ : Representation C (G F Ω) V) (ρ' : Representation C' (G F Ω) V') (f : V →ₗ[ℚ_[l]] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c : G F Ω → V, Continuous (fun g => f (c g)) → IsBK l ρ c → IsBK l ρ' (fun g => f (c g)) := by
  intro l _ F Ω _ _ _ _ C V _ _ _ _ _ _ _ _ _ C' V' _ _ _ _ _ _ _ _ _ ρ ρ' f hf c hfc hc
  refine ⟨fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := hc.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨_, hcc⟩, x, hx⟩ := hc.above τ
    refine ⟨j, hj, ⟨?_, fun g h => ?_⟩, LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f x, fun g => ?_⟩
    · exact hfc.comp (continuous_fst.comp continuous_subtype_val)
    · have h1 := congrArg f (hcc g h)
      simpa only [map_add (f := _), hf, MonoidHom.comp_apply] using h1
    · have key : ∀ y : TensorProduct ℚ_[l] V (UpperTheory.V.Loc.Bcr l),
          LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f
            (UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
              (ρ.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g y) =
          UpperTheory.V.Loc.actC ((MonoidHom.snd _ _).comp (decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (decJ F j).subtype)) g
            (LinearMap.rTensor (UpperTheory.V.Loc.Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [UpperTheory.V.Loc.actC, hf]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoEmbConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.embConj :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (j₀ : Ω →+* Om l) (τ : K →+* Om l), ∃ g : G ℚ Ω, (j₀.comp (g : Ω →+* Ω)).comp (algebraMap K Ω) = τ := by
  intro l _ K Ω _ _ _ _ _ _ _ j₀ τ
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hsub : ∀ x : K, ∃ b : Ω, j₀ b = τ x := by
    intro x
    have hp : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hrat : j₀.comp (algebraMap ℚ Ω) = τ.comp (algebraMap ℚ K) := Subsingleton.elim _ _
    have hroot : τ x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j₀).roots := by
      rw [Polynomial.map_map, Polynomial.mem_roots_map hp, hrat, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    rw [(IsAlgClosed.splits ((minpoly ℚ x).map (algebraMap ℚ Ω))).roots_map j₀] at hroot
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hroot
    exact ⟨b, hb⟩
  choose f hf using hsub
  let τ' : K →+* Ω :=
    { toFun := f
      map_one' := j₀.injective (by rw [hf, map_one, map_one])
      map_mul' := fun a b => j₀.injective (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := j₀.injective (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => j₀.injective (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let g0 : Ω →ₐ[ℚ] Ω := (τ'.toRatAlgHom).liftNormal Ω
  refine ⟨AlgEquiv.ofBijective g0 (Algebra.IsAlgebraic.algHom_bijective g0), ?_⟩
  ext x
  show j₀ (g0 (algebraMap K Ω x)) = τ x
  rw [AlgHom.liftNormal_commutes]
  exact hf x
end

