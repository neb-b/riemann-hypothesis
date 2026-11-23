module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValCmp

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω]

theorem pt_eq_comp (M : RatModel k Ω) (z : M.Z) :
    M.pt = spMap (M.O z).val.toRingHom ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z) := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine h1.symm.trans ?_
  rw [← h2, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem hasDiv_of_forall_cDvr : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (J J' : Type) [Fintype J] (th : J → Ω) (e : J' → Ω) (D : ℕ), 1 ≤ D → Geo.Tor.IsNormalScheme M.Z → M.HasDiv e → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V), jK V ≫ ξ = spMap emb ≫ M.pt → ∀ j₀, e j₀ ≠ 0 → (∀ j, emb (e j / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V))) → M.HasDiv th := by
  intro k Ω _ _ _ _ _ M J J' _ th e D hD hN he H z
  obtain ⟨j₀, hj₀, hej⟩ := he z
  haveI : IsNoetherianRing (M.O z) := RatModel.isNoetherianRing_O M z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z
  haveI : CharZero (M.O z) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
      ∀ φ : M.O z →+* V, Function.Injective φ →
      ∃ emb : Ω →+* FractionRing V,
        (∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r)) ∧
        (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧
        ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V)) := by
    intro V _ _ _ hV φ hφ
    have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
      (IsFractionRing.injective V (FractionRing V)).comp hφ
    let emb : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O z) hg
    have hemb : ∀ r : M.O z, emb (algebraMap (M.O z) Ω r) = algebraMap V (FractionRing V) (φ r) := fun r =>
      IsFractionRing.lift_algebraMap (A := M.O z) hg r
    have e1 : jK V ≫ spMap φ = spMap emb ≫ spMap (M.O z).val.toRingHom := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      exact (hemb r).symm
    have hcomp : jK V ≫ (spMap φ ≫ (spMap (M.stalkEquiv z).toRingHom ≫ M.Z.fromSpecStalk z)) = spMap emb ≫ M.pt := by
      rw [pt_eq_comp M z, ← Category.assoc, e1, Category.assoc]
    refine ⟨emb, hemb, H V hV _ emb hcomp j₀ hj₀ fun j => ⟨φ ⟨_, hej j⟩, (hemb ⟨_, hej j⟩).symm⟩⟩
  have hmem : ∀ b, th b ^ D / e j₀ ∈ M.O z := by
    intro b
    obtain ⟨a, s, hs, hx⟩ := IsFractionRing.div_surjective (A := M.O z) (th b ^ D / e j₀)
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hdvd : s ∣ a := _root_.GlobalTheory.DvrDiv.dvd_of_forall_cDvr (M.O z) a s hs0 (fun V _ _ _ hV φ hφ => by
      obtain ⟨emb, hemb, h1, -⟩ := key V hV φ hφ
      obtain ⟨v, hv⟩ := h1 b
      rw [← hx, map_div₀, hemb, hemb] at hv
      have hs' : algebraMap V (FractionRing V) (φ s) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ((map_ne_zero_iff φ hφ).2 hs0)
      refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
      rw [map_mul, hv, mul_div_cancel₀ _ hs'])
    obtain ⟨c, hc⟩ := hdvd
    have hs1 : algebraMap (M.O z) Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    rw [← hx, hc, map_mul, mul_div_cancel_left₀ _ hs1]
    exact c.2
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.O z)
  obtain ⟨emb, hemb, -, b, hb, w, hw⟩ := key V hV φ hφ
  have hu : IsUnit (⟨th b ^ D / e j₀, hmem b⟩ : M.O z) := by
    apply isUnit_of_map_unit φ
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
    rw [map_mul, map_one, hw, ← hemb, ← map_mul]
    have e2 : algebraMap (M.O z) Ω ⟨th b ^ D / e j₀, hmem b⟩ * (e j₀ / th b ^ D) = 1 := by
      change th b ^ D / e j₀ * (e j₀ / th b ^ D) = 1
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      field_simp
    rw [e2, map_one]
  have hinv := ((RatModel.isUnit_O_iff _).1 hu).2
  refine ⟨b, hb, fun b' => ?_⟩
  have hp : (th b' / th b) ^ D ∈ M.O z := by
    have h3 := mul_mem (hmem b') hinv
    have e3 : th b' ^ D / e j₀ * (th b ^ D / e j₀)⁻¹ = (th b' / th b) ^ D := by
      have : th b ^ D ≠ 0 := pow_ne_zero _ hb
      rw [inv_div, div_pow]
      field_simp
    simpa only [e3] using h3
  have hint : IsIntegral (M.O z) (th b' / th b) := by
    refine IsIntegral.of_pow (n := D) (by omega) ?_
    have := isIntegral_algebraMap (R := M.O z) (A := Ω) (x := ⟨_, hp⟩)
    simpa using this
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.DimBasic

theorem dim_image {W T : Type*} [TopologicalSpace W] [TopologicalSpace T] {e : W → T}
    (he : Topology.IsEmbedding e) (S : Set W) :
    topologicalKrullDim (e '' S) = topologicalKrullDim S := by
  have h := topologicalKrullDim_eq_of_isEmbedding (he.comp Topology.IsEmbedding.subtypeVal)
    (Z := e '' S) (by rw [Set.range_comp, Subtype.range_coe])
  exact h

theorem dim_closure_eq_zero_iff {T : Type*} [TopologicalSpace T] [T0Space T] (x : T) :
    topologicalKrullDim (closure ({x} : Set T)) = 0 ↔ IsClosed ({x} : Set T) := by
  constructor
  · intro h
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.1
      (show Order.krullDim (IrreducibleCloseds (closure ({x} : Set T))) ≤ 0 from h.le)
    refine closure_subset_iff_isClosed.1 fun w hw => ?_
    let s : closure ({x} : Set T) := ⟨x, subset_closure rfl⟩
    let t : closure ({x} : Set T) := ⟨w, hw⟩
    have hst : s ⤳ t := Topology.IsInducing.subtypeVal.specializes_iff.1
      (specializes_iff_mem_closure.2 hw)
    let A : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {t}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds (closure ({x} : Set T)) :=
      ⟨closure {s}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A ≤ B := specializes_iff_closure_subset.1 hst
    have hBA : B ≤ A := hmax A hAB
    have hts : t ⤳ s := specializes_iff_closure_subset.2 hBA
    have e := (hst.antisymm hts).eq
    exact Set.mem_singleton_iff.2 (congrArg Subtype.val e).symm
  · intro h
    rw [h.closure_eq]
    have : Subsingleton ({x} : Set T) := Set.subsingleton_singleton.coe_sort
    let pt : ({x} : Set T) := ⟨x, rfl⟩
    have : Nonempty (IrreducibleCloseds ({x} : Set T)) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    refine le_antisymm (Order.krullDim_nonpos_iff_forall_isMax.2 fun a b _ => ?_) Order.krullDim_nonneg
    intro y _
    have ha : (a : Set ({x} : Set T)) = Set.univ := a.isIrreducible.nonempty.eq_univ
    show y ∈ (a : Set ({x} : Set T))
    rw [ha]; trivial

theorem ringKrullDim_le_one (k : Type) [CommRing k] [Module.Finite ℤ k] : ringKrullDim k ≤ 1 := by
  have : Algebra.IsIntegral ℤ k := inferInstance
  calc ringKrullDim k ≤ ringKrullDim ℤ :=
        Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap ℤ k))
          fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h
    _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField

theorem dim_pspace_le (k : Type) [CommRing k] [Module.Finite ℤ k] (N : ℕ) :
    topologicalKrullDim (PSpace k N) ≤ (N + 1 : ℕ) := by
  have := IsNoetherianRing.of_finite ℤ k
  have hk := ringKrullDim_le_one k
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k N x
  refine ⟨_, (ProjSpace.chart k N i).isOpen, hi, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding (ProjSpace.chartι k N i).isOpenEmbedding.isEmbedding
    (congrArg SetLike.coe (ProjSpace.opensRange_chartι k N i))]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    (R := MvPolynomial {j // j ≠ i} k)).trans_le ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp
  exact (add_le_add_left hk _).trans_eq (add_comm _ _)

theorem finite_residueField (k : Type) [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) (hp : IsProjOver p) {x : X} (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨N, j, _, hj⟩ := hp
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hf : IsFinite (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (X.fromSpecResidueField x ≫ p ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ (X.residueField x)), RingHom.finite_algebraMap] at hf
  obtain ⟨ℓ, _⟩ := CharP.exists (X.residueField x)
  rcases CharP.char_is_prime_or_zero (X.residueField x) ℓ with hℓ | rfl
  · have := Fact.mk hℓ
    let := ZMod.algebra (X.residueField x) ℓ
    have := Module.Finite.of_restrictScalars_finite ℤ (ZMod ℓ) (X.residueField x)
    exact Module.finite_of_finite (ZMod ℓ)
  · have := CharP.charP_to_charZero (X.residueField x)
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := X.residueField x)
      (RingHom.injective_int _) (Field.toIsField _)) Int.not_isField

theorem hasDim_map_iff {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ) :
    HasDim (i y) d ↔ HasDim y d := by
  unfold HasDim
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq,
    dim_image i.isClosedEmbedding.isEmbedding]

theorem hasDim_genericPoint_iff (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ) :
    HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  unfold HasDim
  rw [(genericPoint_spec Y).def]
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]

end GlobalTheory.MixHt.DimBasic

namespace GlobalTheory.MixHt


open DimBasic in
theorem hasDim_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p →
    (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧
    (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧
    (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧
    (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
    (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  intro k _ X p h
  have := h.finite
  refine ⟨?_, fun x d d' hd hd' => ?_, fun x => ?_, fun x hx => finite_residueField k p h.isProjOver hx,
    fun Y i _ y d => hasDim_map_iff i y d, fun Y _ d => hasDim_genericPoint_iff Y d⟩
  · obtain ⟨N, j, _, -⟩ := h.isProjOver
    refine ⟨N + 1, fun x => ?_⟩
    have h₁ : topologicalKrullDim (closure ({x} : Set X)) ≤ (N + 1 : ℕ) :=
      (topologicalKrullDim_subspace_le X _).trans
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans (dim_pspace_le k N))
    let pt : closure ({x} : Set X) := ⟨x, subset_closure rfl⟩
    have : Nonempty (IrreducibleCloseds (closure ({x} : Set X))) :=
      ⟨⟨closure {pt}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h₂ : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set X)) := Order.krullDim_nonneg
    unfold HasDim
    generalize topologicalKrullDim (closure ({x} : Set X)) = a at *
    induction a with
    | bot => exact absurd h₂ (by simp)
    | coe a =>
      induction a with
      | top => exact absurd h₁ (by rw [not_le]; exact WithBot.coe_lt_coe.2 (ENat.coe_lt_top _))
      | coe a => exact ⟨a, by exact_mod_cast h₁, rfl⟩
  · unfold HasDim at hd hd'
    exact_mod_cast hd.symm.trans hd'
  · unfold HasDim
    exact_mod_cast dim_closure_eq_zero_iff x

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDim
section
set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD : Module.finrank K (G.dual.A 1) = p ^ G.dual.height := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have e := G.dual.rank_eq 1 q
    rw [Module.rankAtStalk_eq_finrank_of_free] at e
    simpa using e
  have hhD : G.dual.height = G.height := by simp
  have hord := finrank_eq_ker_mul_range K (G.dual.A 1) _ ((relFrob h G.dual).app 1)
  have hD : Module.finrank K (G.dual.A 1 ⧸ kerIdeal ((relFrob h G.dual).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.dual.A 1)) := by
    rw [← _root_.GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob p K h G.dual 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.dual.A 1)
  have hA : Module.finrank K (G.A 1 ⧸ kerIdeal ((relFrob h G).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by
    rw [← _root_.GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob p K h G 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.A 1)
  have hker : (kerIdeal ((relFrob h G).app 1)).restrictScalars K ≤
      LinearMap.ker ((verschiebung h G).app 1 :
        G.A 1 →ₐ[K] (frobTwist h G).A 1).toLinearMap := fun a ha =>
    _root_.GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) a ha
  have hV := _root_.GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung p K h G
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob h G).app 1)).restrictScalars K)
  rw [(Submodule.Quotient.restrictScalarsEquiv K (kerIdeal ((relFrob h G).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hr : Module.finrank K (LinearMap.range ((relFrob h G.dual).app 1 :
        (frobTwist h G.dual).A 1 →ₐ[K] G.dual.A 1).toLinearMap) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by omega
  have key : p ^ G.height ≤
      p ^ (Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1))) := by
    rw [pow_add, mul_comm, ← hhD, ← hdimD, hord]
    exact Nat.mul_le_mul hD hr
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBoundStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (M b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → ![0, ((M * l ^ b : ℕ) : F)] ∈ L → (∀ v ∈ L, ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ)) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → QAll (Sz l lam ρ) N Ch → QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.sz_hfun_coef | exact GlobalTheory.HilbFam.sz_hfun_coef | (intros; apply GlobalTheory.HilbFam.sz_hfun_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeToOmegaCanonicalExtensionBaseChange
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem psi_baseChange (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R] [CommRing R']
    [Algebra R R'] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ)
    (_hA : IsAbelianScheme A) (hA' : IsAbelianScheme A')
    (G : PDivGroup p R) (G' : PDivGroup p R')
    (t : PDivGroup.TorsionTower G A) (t' : PDivGroup.TorsionTower G' A')
    (ψ : PrimitiveSubmodule A →ₗ[R] G.omega) (ψ' : PrimitiveSubmodule A' →ₗ[R'] G'.omega)
    (hψ : ∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c)))
    (hψ' : ∀ c : PrimitiveSubmodule A', IsCan t' c.1 (G'.rigOfOmega (ψ' c)))
    (c : PrimitiveSubmodule A)
    (hc : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c.1 ∈ PrimitiveSubmodule A') :
    ψ' ⟨_, hc⟩ = (t'.semiHom t (grpMor_of_isGrpPullback h)).omega (ψ c) := by
  have hN' : (p : R') ^ N = 0 := by
    have := congrArg (algebraMap R R') hN
    simpa using this
  have h1 := GlobalTheory.PtExtNat.isCan_pull p R R' A A' G G' t t' (algebraMap R R') φ
    (grpMor_of_isGrpPullback h) c.1 _ (hψ c)
  rw [PDivGroup.SemiHom.rig_rigOfOmega] at h1
  have h2 := hψ' ⟨_, hc⟩
  exact PDivGroup.rigOfOmega_injective_of_pow p R' N hN' G'
    (isCan_unique R' A' p G' t' _ hA' _ _ h2 h1)

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem pullback_eq_chart : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α →
    ∀ (x : A'.Pt) (i : A.ι) (h : f x.pt ∈ (A.e i).source),
      A.pullback A' f α x = pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
  intro M M' _ _ n n' A A' f α hf hα x i h
  have key : ∀ (j : A.ι) (hj : f x.pt ∈ (A.e j).source),
      pull (fderiv ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd) (α ⟨(j, f x.pt), hj⟩) =
        pull (fderiv ℂ (A.e i ∘ f ∘ x.ch.symm) x.crd) (α ⟨(i, f x.pt), h⟩) := by
    intro j hj
    have hc := hα.compat ⟨(j, f x.pt), hj⟩ ⟨(i, f x.pt), h⟩ rfl
    rw [hc, ← _root_.GlobalTheory.CxForm.pull_comp]
    have hx : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
    have hxt : x.crd ∈ x.ch.target := x.ch.map_source x.2
    have hopen : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source)) :=
      x.ch.isOpen_inter_preimage_symm ((A.e j).open_source.preimage hf.1)
    have hmem : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' (A.e j).source) := by
      refine ⟨hxt, ?_⟩
      simp only [Set.mem_preimage, hx]
      exact hj
    have hd1 : DifferentiableAt ℂ (A.e j ∘ f ∘ x.ch.symm) x.crd :=
      (hf.2 x.1.1 j).differentiableAt (hopen.mem_nhds hmem)
    have hopen2 : IsOpen ((A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source) :=
      (A.e j).isOpen_inter_preimage_symm (A.e i).open_source
    have hmem2 : A.e j (f x.pt) ∈ (A.e j).target ∩ (A.e j).symm ⁻¹' (A.e i).source := by
      refine ⟨(A.e j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.e j).left_inv hj]
      exact h
    have hd2 : DifferentiableAt ℂ (A.e i ∘ (A.e j).symm) (A.e j (f x.pt)) :=
      (A.holo j i).differentiableAt (hopen2.mem_nhds hmem2)
    have hpt : (A.e j ∘ f ∘ x.ch.symm) x.crd = A.e j (f x.pt) := by
      simp only [Function.comp, hx]
    have hcomp := fderiv_comp x.crd (hpt ▸ hd2) hd1
    rw [hpt] at hcomp
    have hev : (A.e i ∘ (A.e j).symm) ∘ (A.e j ∘ f ∘ x.ch.symm) =ᶠ[𝓝 x.crd] A.e i ∘ f ∘ x.ch.symm := by
      filter_upwards [hopen.mem_nhds hmem] with v hv
      have hv' : f (x.ch.symm v) ∈ (A.e j).source := hv.2
      simp only [Function.comp, (A.e j).left_inv hv']
    rw [← hev.fderiv_eq, hcomp]
  exact key _ (A.cover (f x.pt)).choose_spec

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdChart

theorem pCrd_chart : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  intro o K _ _ n x v a hx ha
  obtain ⟨c, hc⟩ := CrdUniq.exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (CrdUniq.pCrd_iff x c hc.symm v).1 hx
  subst e
  have hu : IsUnit (v a) := (Points.le_pt_preimage_chart_iff c v hv a).1 ha
  refine ⟨hu.ne_zero, fun b => ?_⟩
  rw [Points.valR_pt_ratio c v hv hu b, Ring.inverse_eq_inv', div_eq_mul_inv]

end GlobalTheory.UMin.CrdChart
end
end

