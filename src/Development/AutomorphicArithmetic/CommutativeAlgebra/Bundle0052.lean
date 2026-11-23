module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointsNonemptyUnitaryGaussian
public import Development.AutomorphicArithmetic.RealSpanData.RealData
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ArithmeticGroupCongruenceSubgroupProperty
section
set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem actOn_comm_mulF (x : 𝓞 D.F) (y : AfP p ⊗[ℚ] G.C) :
    actOn L.rep (AfP p) y * mulF D x = mulF D x * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), add_mul, mul_add, ha, hb]
  | tmul a c =>
    have hc : L.rep c * actQ D (algebraMap (𝓞 D.F) D.O x) = actQ D (algebraMap (𝓞 D.F) D.O x) * L.rep c :=
      (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ _
    have hb : (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) * mulF D x =
        mulF D x * (Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c)) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) hc
      rw [map_mul, map_mul] at this
      exact this
    have ht : actOn L.rep (AfP p) (a ⊗ₜ[ℚ] c) = algebraMap (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) a *
        Module.End.baseChangeHom ℚ (AfP p) (VQ D) (L.rep c) :=
      Algebra.TensorProduct.lift_tmul _ _ _ a c
    rw [ht, mul_assoc, hb, ← mul_assoc, ← mul_assoc, Algebra.commutes]

private theorem actG_mulF (g : G.GAf) (x : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D x v) = mulF D x (L.actG g v) :=
  congrArg (fun f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) => f v) (actOn_comm_mulF L x _)

private theorem actG_idHat {g : G.GAf} (hg : Integ L g) (𝔟 : Ideal (𝓞 D.F)) {z : AfP p ⊗[ℚ] VQ D}
    (hz : z ∈ idHat D 𝔟) : L.actG g z ∈ idHat D 𝔟 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨x, hx, v, hv, rfl⟩ := hz
    rw [actG_mulF]
    exact AddSubgroup.subset_closure ⟨x, hx, _, hg v hv, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end UpperTheory.Gal.Int.Geo

open UpperTheory.Gal.Int.Geo in
theorem UpperTheory.arithmeticGroup_congruenceSubgroupProperty : UpperTheory.Gal.Int.Geo.GrpCong := by
  intro p _ D G L 𝔫 K₀ hK h u _ hc hu hg
  refine (hK _).2 ⟨hg, fun v hv => ?_⟩
  obtain ⟨huK, huC⟩ := (hK u).1 hu
  have huv : L.actG u v ∈ LaHat D := integ_of_mem huK v hv
  have e1 := hc _ huv
  have e2 := huC v hv
  have e3 := actG_idHat L (integ_of_mem hg) 𝔫 (hc v hv)
  have hcomp : L.actG (h * u * h⁻¹) (L.actG h v) = L.actG h (L.actG u v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  have key : L.actG (h * u * h⁻¹) v - v = (L.actG h (L.actG u v) - L.actG u v) + (L.actG u v - v)
      - L.actG (h * u * h⁻¹) (L.actG h v - v) := by
    rw [map_sub, hcomp]; abel
  rw [key]
  exact sub_mem (add_mem e1 e2) e3

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseExtensionHolds
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory

private theorem card_quot_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (h : ∀ a, a ∈ I ↔ f a = 0) :
    Nat.card (A ⧸ I) = Nat.card B := by
  have hk : I = RingHom.ker f := by
    ext a
    rw [RingHom.mem_ker]
    exact h a
  exact Nat.card_congr ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

section Local

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

private def iota : 𝓞 E →+* Gal.Int.Geo.Ow w :=
  (algebraMap (𝓞 E) E).codRestrict (w.valuation E).valuationSubring
    (fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one a)

private theorem iota_mem_max (a : 𝓞 E) :
    iota w a ∈ IsLocalRing.maximalIdeal (Gal.Int.Geo.Ow w) ↔ a ∈ w.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.valuationSubring.integers (w.valuation E)).isUnit_iff_valuation_eq_one,
    ← w.valuation_lt_one_iff_mem (K := E) a]
  exact ⟨fun h => lt_of_le_of_ne (w.valuation_le_one a) h, ne_of_lt⟩

private theorem res_surj :
    Function.Surjective ((IsLocalRing.residue (Gal.Int.Geo.Ow w)).comp (iota w)) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : E) ∈ w.valuationSubringAtPrime E := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact x.2
  haveI : IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj w.asIdeal.primeCompl
    (⟨x, hx⟩ : w.valuationSubringAtPrime E)
  have hxs : x * iota w (s : 𝓞 E) = iota w a :=
    Subtype.ext (congrArg (fun z : w.valuationSubringAtPrime E => (z : E)) h)
  obtain ⟨c, i, hi, hc⟩ := w.isMaximal.exists_inv s.2
  refine ⟨a * c, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hc' : iota w c * iota w (s : 𝓞 E) + iota w i = 1 := by
    rw [← map_mul, ← map_add (f := _), hc, map_one]
  have e1 : iota w (a * c) - x = -(x * iota w i) := by
    rw [map_mul, ← hxs]
    linear_combination x * hc'
  rw [e1]
  exact neg_mem (Ideal.mul_mem_left _ _ ((iota_mem_max w i).2 hi))

private theorem card_res :
    Nat.card (IsLocalRing.ResidueField (Gal.Int.Geo.Ow w)) = Nat.card (𝓞 E ⧸ w.asIdeal) :=
  (card_quot_of _ (res_surj w) w.asIdeal (fun a => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, iota_mem_max])).symm

private theorem card_pow (q : ℕ) (hq : q.Prime) (h : (q : 𝓞 E) ∈ w.asIdeal) :
    ∃ f : ℕ, Nat.card (𝓞 E ⧸ w.asIdeal) = q ^ f :=
  by apply _root_.UpperTheory.Reformulated.B.Qi54.card_pow <;> assumption

end Local

theorem baseExtension_holds : Gal.Int.Geo.BaseEx := by
  intro q _ D ha hm E _ _ e gb hstd w 𝔴 r hpl hu N₀ h3 hcop
  haveI : Subsingleton (Fin D.a) := by
    rw [ha]
    infer_instance
  have hq : q.Prime := Fact.out
  let j : 𝓞 D.F ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hj : ∀ c : 𝓞 D.F, ((j c : 𝓞 E) : E) = e (c : D.F) := fun c => rfl
  have hpl' : ∀ c : 𝓞 D.F, c ∈ 𝔴 ↔ j c ∈ w.asIdeal := fun c => hpl c (j c) (hj c)
  have hqm : (q : 𝓞 E) ∈ w.asIdeal := by
    have h := (hpl' (q : 𝓞 D.F)).1 (hu (ES.p_mem_uIdeal D r))
    rwa [map_natCast] at h
  obtain ⟨f, hf⟩ := card_pow w q hq hqm
  have hnw : Ideal.absNorm w.asIdeal = q ^ f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hf]
  have hroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  let t : 𝓞 D.F →+* Gal.Int.Geo.Ow w := (iota w).comp j.toRingHom
  have hunit : ∀ k : ℕ, k.Coprime q → IsUnit (k : Gal.Int.Geo.Ow w) := by
    intro k hk
    have hkw : (k : 𝓞 E) ∉ w.asIdeal := by
      intro hmem
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
      have h1 : (u : 𝓞 E) * (k : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hqm)
    by_contra hn
    refine hkw ((iota_mem_max w _).1 ?_)
    rw [map_natCast]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let b : Base D (Gal.Int.Geo.Ow w) :=
    { unit := hunit
      ρ := t D.ω
      ρ_root := by
        have h := congrArg t hroot
        simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] using h
      t := fun _ => t
      t_ω := fun _ => rfl
      comax := fun i j h => absurd (Subsingleton.elim i j) h
      apart := fun i j h => absurd (Subsingleton.elim i j) h }
  refine ⟨f, b, ⟨?_, ?_⟩, ?_, hqm, hnw⟩
  · exact hstd.1
  · exact fun i => RingHom.ext fun c => hstd.2 i c
  · have hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp j.toRingHom) :=
      Ideal.Quotient.mk_surjective.comp j.surjective
    refine
      { pmem := ?_
        card := by rw [card_res, hf]
        three := h3
        cop := hcop
        m1 := hm
        a1 := ha
        ule := hu
        norm := ?_
        tw := fun i x hx => (iota_mem_max w _).2 ((hpl' x).1 hx) }
    · rw [← map_natCast (iota w)]
      exact (iota_mem_max w _).2 hqm
    · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        card_quot_of _ hsurj 𝔴 (fun a => by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
          exact hpl' a), hf]

end UpperTheory
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CardFiberEqRelIndexOfNormalQuotient
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.card_fiber_eq_relIndex_of_normal_quotient :
    ∀ (Γ : Type) [Group Γ] (K₀ H KN Km : Subgroup Γ), Count → Km ≤ KN → KN ≤ K₀ → Km ≤ H → H ≤ K₀ → (∀ k ∈ K₀, ∀ u ∈ Km, k * u * k⁻¹ ∈ Km) → Km.relIndex K₀ ≠ 0 → ∀ (V F : Type) (act : KN → V), Function.Surjective act → (∀ u u' : KN, act u = act u' ↔ (u : Γ)⁻¹ * u' ∈ Km) → ∀ (κ : (K₀ ⧸ KN.subgroupOf K₀) → V → F), Nat.card F = H.relIndex K₀ → (∀ (c₁ c₂ : K₀ ⧸ KN.subgroupOf K₀) (u₁ u₂ : KN), κ c₁ (act u₁) = κ c₂ (act u₂) → ((c₁.out : Γ) * u₁) * ((c₂.out : Γ) * u₂)⁻¹ ∈ H) → ∀ ζ : F, Nat.card {x : (K₀ ⧸ KN.subgroupOf K₀) × V // κ x.1 x.2 = ζ} = Km.relIndex H := by
  intro Γ _ K₀ H KN Km hC hmN hNK hmH hHK hn hidx V F act hs he κ hF sep ζ
  classical
  let cl : K₀ → (K₀ ⧸ KN.subgroupOf K₀) := fun x => ((x⁻¹ : K₀) : K₀ ⧸ KN.subgroupOf K₀)
  have hmem : ∀ x : K₀, ((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹ ∈ KN := by
    intro x
    have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (cl x))
    simpa [Subgroup.mem_subgroupOf] using h
  let uu : K₀ → KN := fun x => ⟨((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹, hmem x⟩
  have key : ∀ x : K₀, ((cl x).out : Γ) * (uu x : Γ) = (x : Γ)⁻¹ := by
    intro x
    show ((cl x).out : Γ) * (((cl x).out : Γ)⁻¹ * (x : Γ)⁻¹) = (x : Γ)⁻¹
    group
  have hcleq : ∀ x y : K₀, cl x = cl y → (uu x : Γ)⁻¹ * (uu y : Γ) = (x : Γ) * (y : Γ)⁻¹ := by
    intro x y h
    have hx := key x
    have hy := key y
    rw [h] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx, eq_inv_mul_iff_mul_eq.mpr hy]
    group

  have hwd : ∀ x y : K₀, (x : Γ)⁻¹ * (y : Γ) ∈ Km → (cl x, act (uu x)) = (cl y, act (uu y)) := by
    intro x y h
    have h1 : (x : Γ) * (y : Γ)⁻¹ ∈ Km := by
      have := hn x x.2 _ (Km.inv_mem h)
      have e : (x : Γ) * ((x : Γ)⁻¹ * (y : Γ))⁻¹ * (x : Γ)⁻¹ = (x : Γ) * (y : Γ)⁻¹ := by group
      rwa [e] at this
    have hc : cl x = cl y := by
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using hmN h1
    refine Prod.ext hc ?_
    show act (uu x) = act (uu y)
    rw [he, hcleq x y hc]
    exact h1
  let f : K₀ → (K₀ ⧸ KN.subgroupOf K₀) × V := fun x => (cl x, act (uu x))
  let Φ : (K₀ ⧸ Km.subgroupOf K₀) → (K₀ ⧸ KN.subgroupOf K₀) × V :=
    Quotient.lift f (fun a b hab => hwd a b (by
      have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this))
  have hΦ : ∀ x : K₀, Φ (x : K₀ ⧸ Km.subgroupOf K₀) = (cl x, act (uu x)) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hΦ, hΦ] at hab
    have hc : cl x = cl y := congrArg Prod.fst hab
    have ha : act (uu x) = act (uu y) := congrArg Prod.snd hab
    rw [he, hcleq x y hc] at ha
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have := hn _ (K₀.inv_mem x.2) _ (Km.inv_mem ha)
    have e : (x : Γ)⁻¹ * ((x : Γ) * (y : Γ)⁻¹)⁻¹ * ((x : Γ)⁻¹)⁻¹ = (x : Γ)⁻¹ * (y : Γ) := by group
    rwa [e] at this
  have hsurj : Function.Surjective Φ := by
    rintro ⟨c, v⟩
    obtain ⟨u, rfl⟩ := hs v
    let x : K₀ := (c.out * (⟨u, hNK u.2⟩ : K₀))⁻¹
    refine ⟨(x : K₀ ⧸ Km.subgroupOf K₀), ?_⟩
    rw [hΦ]
    have hc : cl x = c := by
      have h1 : cl x = ((c.out * (⟨u, hNK u.2⟩ : K₀) : K₀) : K₀ ⧸ KN.subgroupOf K₀) := by
        show (((x⁻¹ : K₀)) : K₀ ⧸ KN.subgroupOf K₀) = _
        simp [x]
      rw [h1, ← QuotientGroup.out_eq' c]
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      simp [Subgroup.mem_subgroupOf]
    refine Prod.ext hc ?_
    show act (uu x) = act u
    congr 1
    apply Subtype.ext
    have hx := key x
    rw [hc] at hx
    rw [eq_inv_mul_iff_mul_eq.mpr hx]
    simp [x]
  let E := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hcount := hC Γ K₀ H Km hmH hHK hidx F (fun a => κ (Φ a).1 (Φ a).2) hF (by
    intro x y h
    rw [hΦ, hΦ] at h
    have := sep _ _ _ _ h
    rw [key x, key y] at this
    simpa using this) ζ
  rw [← hcount]
  exact Nat.card_congr (Equiv.subtypeEquiv E (fun a => Iff.rfl)).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CommutantEqRangeActOnAndInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem actOn_tmul {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (s ⊗ₜ v) = (r * s) ⊗ₜ rep c v := by
  have e : actOn rep R (r ⊗ₜ c) = Algebra.ofId R _ r * (Module.End.baseChangeHom ℚ R V) (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r c
  rw [e]
  change r • ((rep c).baseChange R (s ⊗ₜ v)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private theorem actOn_inj {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) :
    Function.Injective (actOn rep R) := by
  classical
  have main : ∀ z : R ⊗[ℚ] C, actOn rep R z = 0 → z = 0 := by
    intro z hz
    let bR := Module.Basis.ofVectorSpace ℚ R
    let bC := Module.Basis.ofVectorSpace ℚ C
    let Ψ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] C →ₗ[ℚ] C :=
      fun f => (TensorProduct.lid ℚ C).toLinearMap ∘ₗ LinearMap.rTensor C f
    let Φ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] V →ₗ[ℚ] V :=
      fun f => (TensorProduct.lid ℚ V).toLinearMap ∘ₗ LinearMap.rTensor V f
    have hΦ : ∀ f (w : R ⊗[ℚ] C) (v : V), Φ f (actOn rep R w (1 ⊗ₜ v)) = rep (Ψ f w) v := by
      intro f w v
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Φ, Ψ, actOn_tmul]
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    have hΨ : ∀ f, Ψ f z = 0 := by
      intro f
      apply hrep
      rw [map_zero]
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.zero_apply, ← hΦ, hz, LinearMap.zero_apply, map_zero]
    have hrepr : ∀ (w : R ⊗[ℚ] C) i j,
        (bR.tensorProduct bC).repr w (i, j) = bC.repr (Ψ (bR.coord i) w) j := by
      intro w i j
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Ψ, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]
    apply (bR.tensorProduct bC).repr.injective
    ext ⟨i, j⟩
    rw [hrepr, hΨ]
    simp
  intro x y hxy
  rw [← sub_eq_zero]
  apply main
  rw [map_sub, hxy, sub_self]

theorem UpperTheory.commutant_eq_range_actOn_and_injective :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R], (∀ A : Module.End R (R ⊗[ℚ] VQ D), (∀ b : D.O, A ∘ₗ (actQ D b).baseChange R = (actQ D b).baseChange R ∘ₗ A) → ∃ c : R ⊗[ℚ] G.C, actOn L.rep R c = A) ∧ Function.Injective (actOn L.rep R) := by
  intro p _ D G L R _ _
  haveI : Module.Finite ℤ D.La := D.finLa
  refine ⟨fun A hA => ?_, actOn_inj L.rep L.rep_inj⟩
  obtain ⟨k, r, h, hh, hA'⟩ := UpperTheory.exists_sum_baseChange_of_commute_baseChange D.O (VQ D) (VQ D) R (actQ D) (actQ D) A hA
  have hx : ∀ l, ∃ x, L.rep x = h l := fun l => (L.rep_range (h l)).2 (fun b => hh l b)
  choose x hx using hx
  refine ⟨∑ l, r l ⊗ₜ[ℚ] x l, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hA', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring (LinearMap.ext fun v => ?_))
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply,
    TensorProduct.curry_apply, actOn_tmul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    hx, _root_.mul_one, TensorProduct.smul_tmul', smul_eq_mul]
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceSubgroupIsLatticeStatement
section
open UpperTheory.Gal.Int.Geo
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem UpperTheory.grpLat_half {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {M : ℕ}
    (hM : 0 < M) (hc : M.Coprime p) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (s₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = M • v)
    (e : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG h₂ (inAf D x) = M • v) →
      ∃ v ∈ LaHat D, L.actG h₁ (inAf D x) = M • v) :
    ∀ v ∈ LaHat D, L.actG (h₁ * h₂⁻¹) v ∈ LaHat D := by
  intro v hv
  obtain ⟨v', hv', e₁⟩ := s₂ v hv
  obtain ⟨x, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D M hM hc v' hv'
  obtain ⟨u, hu, e₃⟩ := e x ⟨v - L.actG h₂ w, sub_mem hv (i₂ w hw), by
    have h : L.actG h₂ v' = L.actG h₂ (inAf D x) + M • L.actG h₂ w := by
      rw [e₂, map_add (f := _), map_nsmul]
    rw [smul_sub, ← e₁, h]
    abel⟩
  have e₄ : M • L.actG (h₁ * h₂⁻¹) v = M • (u + L.actG h₁ w) := by
    have h : L.actG h₂⁻¹ (M • v) = v' := by
      rw [← e₁, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [← map_nsmul, map_mul, Module.End.mul_apply, h, e₂, map_add (f := _), map_nsmul, e₃, smul_add]
  have e₅ : L.actG (h₁ * h₂⁻¹) v = u + L.actG h₁ w := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at e₄
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hM.ne' : (M : ℚ) ≠ 0) e₄
  rw [e₅]
  exact add_mem hu (i₁ w hw)

theorem UpperTheory.congruenceSubgroup_isLattice_statement :
    GrpLat := by
  intro p _ D G L M hM hc h₁ h₂ i₁ i₂ s₁ s₂ e
  have a := UpperTheory.grpLat_half L hM hc i₁ i₂ s₂ (fun x => (e x).2)
  have b := UpperTheory.grpLat_half L hM hc i₂ i₁ s₁ (fun x => (e x).1)
  refine ⟨fun v hv => ⟨L.actG (h₁ * h₂⁻¹) v - v, sub_mem (a v hv) hv, by simp⟩,
    fun v hv => ⟨L.actG (h₁ * h₂⁻¹)⁻¹ v - v, sub_mem ?_ hv, by simp⟩⟩
  rw [mul_inv_rev, inv_inv]
  exact b v hv
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
section
set_option autoImplicit false

namespace UpperTheory

open UpperTheory.Gal.Int.Geo

theorem exists_generic_moduli_point : GenEx := by
  intro A _ _ _ 𝔞 N hN
  have hN0 : (N : A) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine ⟨fun hmem => ?_, fun a t h => ?_⟩
  · have hdvd : 𝔞 ∣ Ideal.span {(N : A)} :=
      Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    obtain ⟨𝔟, h𝔟⟩ := hdvd
    have hle : Ideal.span {(N : A)} ≤ 𝔟 := by
      rw [h𝔟]; exact Ideal.mul_le_right
    have hne : Ideal.span {(N : A)} ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hN0
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
    refine ⟨a, ?_⟩
    unfold IsGen
    rw [sup_comm, ha, mul_comm, ← h𝔟]
  · unfold IsGen at h ⊢
    have hs : Ideal.span {(t : A) * a} ⊔ Ideal.span {((N * t : ℕ) : A)}
        = Ideal.span {(t : A)} * (Ideal.span {a} ⊔ Ideal.span {(N : A)}) := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]
    rw [hs, mul_assoc, h, Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, mul_comm (N : A)]

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.GroupSchemePullbackExists
section
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.group_scheme_pullback_exists :
    GPull := by
  intro G R _ _ gb N X X' s e o
  exact GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o
end

