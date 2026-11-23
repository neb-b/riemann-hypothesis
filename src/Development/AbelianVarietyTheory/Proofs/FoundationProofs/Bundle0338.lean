module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

noncomputable section

namespace GlobalTheory.NegVan

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral


open TensorProduct in
private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

private theorem coef_finext {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x ∈ c.O, x ∈ K := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))
  refine ⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩
  let K := IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))
  let M : Submodule ℤ_[l] (PadicAlgCl l) := (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule
  have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  have hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap := by
    rw [Submodule.span_le]
    intro q hq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩
  exact hle hmem

end GlobalTheory.NegVan


open GlobalTheory.NegVan in
theorem GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight :
    Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) →
      ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w →
      ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  intro hP l _ κ hκc c hκO w hw hwt f hf
  obtain ⟨K₀, hK₀, hK⟩ := coef_finext c
  obtain ⟨E, _, κ', c', hκ, hc', hf'⟩ := desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w := by
    obtain ⟨U, hU, hUw⟩ := hwt
    refine ⟨U, hU, fun g hg hI => ?_⟩
    have h := hUw g hg hI
    have hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)
        (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    apply Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l))
      (algebraMap E (PadicAlgCl l)).injective
    rw [map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]
    exact Units.ext (hκ g)
  have hz := (Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ'
    (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw
  rw [hz.1, mem_coboundaries1] at hf'
  obtain ⟨m, hm⟩ := hf'
  refine ⟨(m : PadicAlgCl l), fun σ => ?_⟩
  have h4 : c' σ = κ' σ * m - m := hm σ
  rw [← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutator
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem fix_root {l : ℕ} [Fact l.Prime] {s : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) {n : ℕ} {x : Ω}
    (hx : x ^ (l ^ n) = 1) : s x = x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hs)
    apply Units.ext
    have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
      (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
    apply hinj
    simpa [cycBar] using h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x hx
  have h3 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := h1
  rw [h3] at h2
  have h4 : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x = s x := rfl
  rw [h4, Units.val_one, map_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one] at h2
  exact h2

theorem comm_apply {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a)
    {s t : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) (ht : t ∈ (cycBar ℚ Ω l).ker) {y : Ω}
    (hy : y ^ (l ^ n) = a) : s (t y) = t (s y) := by
  by_cases h0 : y = 0
  · simp [h0]
  have key : ∀ g : G ℚ Ω, (g y / y) ^ (l ^ n) = 1 := fun g => by
    rw [div_pow, ← map_pow, hy, ha, ← hy]
    exact div_self (pow_ne_zero _ h0)
  obtain ⟨c, hcr, es⟩ : ∃ c : Ω, c ^ (l ^ n) = 1 ∧ s y = c * y :=
    ⟨s y / y, key s, (div_mul_cancel₀ _ h0).symm⟩
  obtain ⟨d, hdr, et⟩ : ∃ d : Ω, d ^ (l ^ n) = 1 ∧ t y = d * y :=
    ⟨t y / y, key t, (div_mul_cancel₀ _ h0).symm⟩
  rw [et, es, map_mul, map_mul, fix_root hs hdr, fix_root ht hcr, es, et]
  ring

theorem comm_fix {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a) {σ : G ℚ Ω}
    (hσ : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆) {y : Ω} (hy : y ^ (l ^ n) = a) : σ y = y := by
  let K : Subgroup (G ℚ Ω) := ⨅ z : {z : Ω // z ^ (l ^ n) = a}, MulAction.stabilizer (G ℚ Ω) (z : Ω)
  have hK : ∀ g, g ∈ K ↔ ∀ z : Ω, z ^ (l ^ n) = a → g z = z := fun g => by
    simp only [K, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, Subtype.forall]
  have hle : ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [hK]
    intro z hz
    have hz' : ((t * s)⁻¹ z) ^ (l ^ n) = a := by rw [← map_pow, hz, ha]
    have e : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
    rw [commutatorElement_def, e, AlgEquiv.mul_apply, AlgEquiv.mul_apply, comm_apply ha hs ht hz', ← AlgEquiv.mul_apply,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  exact (hK σ).1 (hle hσ) y hy

theorem isOpen_stab (x : Ω) : IsOpen {τ : G ℚ Ω | τ x = x} := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hx : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) := IntermediateField.adjoin.finiteDimensional hx
  have h := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {x})
  have hle : (IntermediateField.adjoin ℚ {x}).fixingSubgroup ≤ MulAction.stabilizer (G ℚ Ω) x := fun g hg => by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : {τ : G ℚ Ω | τ x = x} = (MulAction.stabilizer (G ℚ Ω) x : Set (G ℚ Ω)) := by
    ext τ; simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [e]
  exact Subgroup.isOpen_mono hle h

theorem root_mod {B : ValuationSubring Ω} {p m N : ℕ} (hp : p.Prime) (hpB : B.valuation (p : Ω) < 1) (hm : m ≠ 0)
    {α : Ω} (hα : α ^ m = (N : Ω)) (hfr : B.valuation α ≤ 1 → B.valuation (α - α ^ p) < 1) :
    ∃ x : ZMod p, x ^ m = (N : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hαle : B.valuation α ≤ 1 := by
    have h1 : B.valuation α ^ m ≤ 1 := by
      rw [← map_pow, hα]; exact (B.valuation_le_one_iff _).2 (natCast_mem B N)
    exact (pow_le_one_iff hm).1 h1
  have hαB : α ∈ B := (B.valuation_le_one_iff α).1 hαle
  let a : B := ⟨α, hαB⟩
  have hmax : ∀ b : B, B.valuation (b : Ω) < 1 → IsLocalRing.residue B b = 0 := fun b hb =>
    (IsLocalRing.residue_eq_zero_iff b).2 ((B.valuation_lt_one_iff b).2 hb)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField B) = 0 := by
    have := hmax (p : B) (by simpa using hpB)
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField B) p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  let φ : ZMod p →+* IsLocalRing.ResidueField B := ZMod.castHom (dvd_refl p) _
  have hφ : Function.Injective φ := φ.injective
  have hr : IsLocalRing.residue B a ^ p = IsLocalRing.residue B a := by
    have := hmax (a - a ^ p) (by simpa [a] using hfr hαle)
    rw [map_sub, map_pow, sub_eq_zero] at this
    exact this.symm
  have hP : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero hp.one_lt
  have hsub : Finset.univ.image φ ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hcard : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset.card ≤
      (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, ZMod.card]
    calc _ ≤ Multiset.card (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).natDegree :=
          Polynomial.card_roots' _
      _ = p := Polynomial.natDegree_X_pow_sub_X hp.one_lt
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hrmem : IsLocalRing.residue B a ∈
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hr, sub_self]
  rw [← heq] at hrmem
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hrmem
  refine ⟨x, hφ ?_⟩
  have ha : a ^ m = (N : B) := Subtype.ext (by simp [a, hα])
  rw [map_pow, hx, map_natCast, ← map_pow, ha, map_natCast]

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem normV_eq_absNorm (v : Pl) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem absNorm_dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem natCast_mem_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq_absNorm]
  refine ⟨absNorm_dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime' (v : Pl) : (normV v).Prime := by
  have h1 : 1 < normV v := by
    rw [normV_eq_absNorm]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (natCast_mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((natCast_mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((natCast_mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem val_natCast_lt_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {w : Pl}
    (h : IsPlaceOver A w) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ normV w ∣ n := by
  rw [← natCast_mem_iff, ← h]
  simp

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem exists_odd_prime_gt_two_bounds : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ)
    (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) →
    σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω),
      w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧
      l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  intro l hl Ω _ _ _ n S S' U σ hU hσ
  classical
  haveI hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hm : 0 < l ^ n := pow_pos hl.out.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ n) := by
    haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hm.ne'⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hm).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  have hα : ∀ v : Pl, ∃ α : Ω, α ^ (l ^ n) = (normV v : Ω) := fun v => IsAlgClosed.exists_pow_nat_eq _ hm
  choose α hα using hα
  let T : Finset Ω := insert ζ (S.image α)
  let O : Set (G ℚ Ω) := {τ | σ⁻¹ * τ ∈ U} ∩ ⋂ x ∈ T, {τ | τ x = x}
  have hO : IsOpen O := (hU.preimage (continuous_const_mul σ⁻¹)).inter
    (isOpen_biInter_finset fun x _ => isOpen_stab x)
  have hσker : σ ∈ (cycBar ℚ Ω l).ker := Subgroup.commutator_le_left _ _ hσ
  have hσO : σ ∈ O := by
    refine ⟨by simp [U.one_mem], Set.mem_iInter₂.2 fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact fix_root hσker hζ.pow_eq_one
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
      exact comm_fix (fun g => map_natCast g _) hσ (hα v)
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  have hTfin : ((S : Set Pl) ∪ (S' : Set Pl) ∪ {v : Pl | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 ℚ)}}).Finite :=
    ((S.finite_toSet).union (S'.finite_toSet)).union (Ideal.finite_factors hl0)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hTfin
  obtain ⟨τ, hτO, w, hwT, -, B, hB, hτ⟩ := hdense.inter_open_nonempty O hO ⟨σ, hσO⟩
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or] at hwT
  obtain ⟨⟨hwS, hwS'⟩, hwl⟩ := hwT
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
    hwl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hfix : ∀ x ∈ T, τ x = x := fun x hx => Set.mem_iInter₂.1 hτO.2 x hx
  have hp : (normV w).Prime := normV_prime' w
  have hpB : B.valuation ((normV w : ℕ) : Ω) < 1 := (val_natCast_lt_one_iff hB _).2 dvd_rfl
  have hlB : ¬ B.valuation ((l : ℕ) : Ω) < 1 := fun h => hlw ((hB _).1 (by simpa using h))
  have hnot : ¬ B.valuation ((l ^ n : ℕ) : Ω) < 1 := fun h =>
    hlB ((val_natCast_lt_one_iff hB l).2 (hp.dvd_of_dvd_pow ((val_natCast_lt_one_iff hB (l ^ n)).1 h)))
  have hpows := (ML.placeBasic Ω).2.2.2.2.2.2.1 B (normV w) (l ^ n) τ hτ hnot
  have h1 : ζ ^ normV w = ζ := (hpows ζ hζ.pow_eq_one).symm.trans (hfix ζ (Finset.mem_insert_self _ _))
  have h2 : ζ ^ (normV w - 1) = 1 := by
    have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
    refine mul_right_cancel₀ hz ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul, h1]
  refine ⟨w, B, τ, hwS, hwS', hB, hτ, hτ.1, hτO.1, hζ.dvd_of_pow_eq_one _ h2, fun v hv => ?_⟩
  have hτv : τ (α v) = α v := hfix _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem α hv))
  refine root_mod hp hpB hm.ne' (hα v) fun h => ?_
  have := hτ.2 (α v) h
  rwa [hτv] at this

end GlobalTheory.Ord2.AuxiliaryInertOddPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CoefJoin

theorem isIntegral_iff_norm_le {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem coef_of_finite : ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (Qbar l)), FiniteDimensional ℚ_[l] E →
    ∃ c : Coef l, ∀ x : Qbar l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ E hE
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l E
  let f : E →ₐ[ℤ_[l]] PadicAlgCl l := E.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] E).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] E).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, ?_⟩
  intro x
  have hn := fun y : E => isIntegral_iff_norm_le (l := l) E.val y
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (hn y).1 hy⟩
  · rintro ⟨hx, hle⟩
    exact ⟨⟨x, hx⟩, (hn ⟨x, hx⟩).2 hle, rfl⟩

end GlobalTheory.CoefJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobeniusPowInvMulMemOpenSubgroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem exists_frob_pow_inv_mul_mem : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl) (B : ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), IsPlaceOver B q → Ine (F := ℚ) B ≤ K → IsOpen ((K.subgroupOf (Dec (F := ℚ) B) : Subgroup ↥(Dec (F := ℚ) B)) : Set ↥(Dec (F := ℚ) B)) → ∃ (φ : ↥(Dec (F := ℚ) B)) (m : ℕ), 0 < m ∧ ((φ ^ m : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K ∧ ∀ N : ℕ, 0 < N → ∃ d : ↥(Dec (F := ℚ) B) →* Multiplicative (ZMod (m * N)), IsOpen (d.ker : Set ↥(Dec (F := ℚ) B)) ∧ ∀ s : ↥(Dec (F := ℚ) B), (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K := by
  intro Ω _ _ _ q B K hq hIK hKo
  obtain ⟨φ, -, hcl, hd⟩ := UpperTheory.V.GC.decZhat ℚ Ω q B hq
  haveI : CompactSpace (Dec (F := ℚ) B) :=
    isCompact_iff_compactSpace.1 (ReciprocityTheory.Gal.isClosed_Dec (F := ℚ) B).isCompact
  set K' : Subgroup (Dec (F := ℚ) B) := K.subgroupOf (Dec (F := ℚ) B) with hK'
  haveI : Finite (Dec (F := ℚ) B ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hKo
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨m, hm0, -, hmK'⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K')) φ
  refine ⟨φ, m, hm0, Subgroup.mem_subgroupOf.1 hmK', fun N hN => ?_⟩
  obtain ⟨d, hdlc, hdI, hdφ⟩ := hd (m * N) (Nat.mul_pos hm0 hN)
  haveI : NeZero (m * N) := ⟨(Nat.mul_pos hm0 hN).ne'⟩
  refine ⟨d, hdlc.isOpen_fiber 1, ?_⟩

  have hK'cl : IsClosed (K' : Set (Dec (F := ℚ) B)) := Subgroup.isClosed_of_isOpen K' hKo
  have hcont : Continuous (fun s : Dec (F := ℚ) B => (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s) := by
    have h1 : IsLocallyConstant (fun s : Dec (F := ℚ) B => (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹) :=
      hdlc.comp (fun x => (φ ^ (Multiplicative.toAdd x).val)⁻¹)
    exact h1.continuous.mul continuous_id
  have hS : IsClosed {s : Dec (F := ℚ) B | (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s ∈ K'} :=
    hK'cl.preimage hcont
  have hI'K' : (Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ≤ K' := fun i hi =>
    Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hi))
  have hsub : ((((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ⊔ Subgroup.zpowers φ :
      Subgroup (Dec (F := ℚ) B))) : Set (Dec (F := ℚ) B)) ⊆
      {s : Dec (F := ℚ) B | (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s ∈ K'} := by
    intro x hx
    rw [Subgroup.normal_mul] at hx
    obtain ⟨i, hi, y, hy, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    simp only [Set.mem_ofPred_eq]
    set v := (Multiplicative.toAdd (d (i * φ ^ j))).val with hv
    have hdv : ((v : ℤ) : ZMod (m * N)) = (j : ZMod (m * N)) := by
      rw [Int.cast_natCast, hv, ZMod.natCast_zmod_val, map_mul, hdI i hi, one_mul, map_zpow, hdφ,
        ← ofAdd_zsmul, toAdd_ofAdd, zsmul_one]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (j - v) (m * N)).1 (by
      rw [Int.cast_sub, hdv, sub_self])
    have e : (φ ^ v)⁻¹ * (i * φ ^ j) = ((φ ^ v)⁻¹ * i * ((φ ^ v)⁻¹)⁻¹) * (φ ^ m) ^ ((N : ℤ) * t) := by
      rw [← zpow_natCast φ m, ← zpow_mul, ← zpow_natCast φ v]
      have : j = (v : ℤ) + (m : ℤ) * (N * t) := by push_cast at ht; linarith [ht]
      rw [this, zpow_add]
      group
    rw [e]
    refine K'.mul_mem (hI'K' ?_) (K'.zpow_mem hmK' _)
    exact Subgroup.Normal.conj_mem i hi _
  intro s
  have hs : s ∈ (((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ⊔ Subgroup.zpowers φ).topologicalClosure :
      Set (Dec (F := ℚ) B)) := by rw [hcl]; trivial
  rw [Subgroup.topologicalClosure_coe] at hs
  exact Subgroup.mem_subgroupOf.1 (closure_minimal hsub hS hs)

end GlobalTheory.Ord2
end

