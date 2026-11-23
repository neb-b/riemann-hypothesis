module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPTypicalTangent
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.TwistFiltered

theorem ring_eq_later {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) {j : J} {x y : D.obj j} (h : c.ι.app j x = c.ι.app j y) :
    ∃ (k : J) (f : j ⟶ k), D.map f x = D.map f y :=
  (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget CommRingCat.{0}) hc) x y).1 h

def primSys (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) : J ⥤ Type where
  obj j := Prim q (D.obj j)
  map f := TypeCat.ofHom (Prim.map (q := q) (D.map f).hom)
  map_id j := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]
  map_comp f g := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]

end GlobalTheory.EtC.TwistFiltered

namespace GlobalTheory.EtC.TwistFiltered

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Prim.map (q := q) g ∘ Prim.map f = Prim.map (g.comp f) := by
  funext ζ
  rfl

theorem twF_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  intro q i
  rw [(GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} (ZMod q)) (twF q i)).2]
  intro J _ _ D c hc
  obtain ⟨hon, hinj⟩ := GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit q J D c hc
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : (twF q i).obj (D.obj j)),
      ((twF q i).map (c.ι.app k)).hom (((twF q i).map (D.map f)).hom y) = ((twF q i).map (c.ι.app j)).hom y := by
    intro j k f y
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, c.w]
  have hwP : ∀ {j k : J} (f : j ⟶ k), Prim.map (q := q) (c.ι.app k).hom ∘ Prim.map (D.map f).hom = Prim.map (c.ι.app j).hom := by
    intro j k f
    rw [prim_map_comp, ← CommRingCat.hom_comp, c.w]
  have hwP' : ∀ {j k : J} (f : j ⟶ k) (ζ : Prim q (D.obj j)), Prim.map (q := q) (c.ι.app k).hom (Prim.map (D.map f).hom ζ) = Prim.map (c.ι.app j).hom ζ :=
    fun f ζ => congrFun (hwP f) ζ
  refine ⟨?_, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
    induction f using Finsupp.induction_linear with
    | zero =>
      obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
      exact ⟨j, 0, by rw [map_zero]; rfl⟩
    | add f g hf hg =>
      obtain ⟨j, y, hy⟩ := hf
      obtain ⟨j', y', hy'⟩ := hg
      refine ⟨IsFiltered.max j j', ((twF q i).map (D.map (IsFiltered.leftToMax j j'))).hom y + ((twF q i).map (D.map (IsFiltered.rightToMax j j'))).hom y', ?_⟩
      rw [map_add (f := _), hw, hw, hy, hy']
      rfl
    | single ζ a =>
      obtain ⟨j, ξ, hξ⟩ := hon ζ
      refine ⟨j, Submodule.Quotient.mk (Finsupp.single ξ a), ?_⟩
      change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
      rw [Finsupp.mapDomain_single, hξ]
  · intro j y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (c.ι.app j).hom) x) = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    have hlift : ∀ r ∈ twRel q i c.pt, ∃ (k : J) (s : Prim q (D.obj k) →₀ ULift.{1} (ZMod q)),
        s ∈ twRel q i (D.obj k) ∧ Finsupp.mapDomain (Prim.map (c.ι.app k).hom) s = r := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨ζ, ξ, a, hrel, rfl⟩ := hr
        obtain ⟨j1, ζ1, hζ1⟩ := hon ζ
        obtain ⟨j2, ξ1, hξ1⟩ := hon ξ
        obtain ⟨ζm, hζm⟩ : ∃ ζm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ζm = ζ :=
          ⟨_, (hwP' (IsFiltered.leftToMax j1 j2) ζ1).trans hζ1⟩
        obtain ⟨ξm, hξm⟩ : ∃ ξm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ξm = ξ :=
          ⟨_, (hwP' (IsFiltered.rightToMax j1 j2) ξ1).trans hξ1⟩
        have heq : c.ι.app (IsFiltered.max j1 j2) ξm.1 = c.ι.app (IsFiltered.max j1 j2) (ζm.1 ^ (a : ZMod q).val) := by
          rw [map_pow]
          have h1 := congrArg Subtype.val hζm
          have h2 := congrArg Subtype.val hξm
          simp only [Prim.map] at h1 h2
          rw [h1, h2, hrel]
        obtain ⟨n, g, hg⟩ := ring_eq_later hc heq
        refine ⟨n, Finsupp.single (Prim.map (D.map g).hom ξm) 1 - Finsupp.single (Prim.map (D.map g).hom ζm) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)), Submodule.subset_span ⟨_, _, a, ?_, rfl⟩, ?_⟩
        · simp only [Prim.map]
          rw [hg, map_pow]
        · rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hwP' g ξm, hwP' g ζm, hζm, hξm]
      | zero =>
        obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
        exact ⟨j, 0, zero_mem _, by simp⟩
      | add r r' _ _ hr hr' =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        obtain ⟨k', s', hs', rfl⟩ := hr'
        refine ⟨IsFiltered.max k k', Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax k k')).hom) s +
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax k k')).hom) s',
          add_mem (twRel_le q i _ hs) (twRel_le q i _ hs'), ?_⟩
        rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP]
      | smul a r _ hr =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        exact ⟨k, a • s, Submodule.smul_mem _ a hs, by rw [Finsupp.mapDomain_smul]⟩
    obtain ⟨k, s, hs, hsr⟩ := hlift _ hy
    have hz : Finsupp.mapDomain (Prim.map (c.ι.app (IsFiltered.max j k)).hom)
        (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k)).hom) x -
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax j k)).hom) s) = 0 := by
      rw [Finsupp.mapDomain_sub, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP, hsr, sub_self]
    have key := GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage (ULift.{1} (ZMod q)) J (primSys q D) (Prim q c.pt) (fun j => Prim.map (c.ι.app j).hom)
      (fun j k f ζ => hwP' f ζ) hinj (IsFiltered.max j k) _ hz
    obtain ⟨n, h, hn⟩ := key
    refine ⟨n, IsFiltered.leftToMax j k ≫ h, ?_⟩
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k ≫ h)).hom) x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change Finsupp.mapDomain (Prim.map (D.map h).hom) _ = 0 at hn
    rw [Finsupp.mapDomain_sub, sub_eq_zero, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, prim_map_comp, prim_map_comp] at hn
    rw [Functor.map_comp, CommRingCat.hom_comp, hn]
    have := twRel_le q i (D.map (IsFiltered.rightToMax j k ≫ h)).hom hs
    rwa [Functor.map_comp, CommRingCat.hom_comp] at this

end GlobalTheory.EtC.TwistFiltered
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OpenDim

theorem ringKrullDim_affineOpen (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] {U : Y.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ d : ℕ, ringKrullDim Γ(Y, U) = d ∧ Algebra.trdeg F Y.functionField = d := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra F Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη =
      Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : FaithfulSMul F Γ(Y, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(Y, U)).injective
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(Y, U)
  exact ⟨d, h₁, (trdeg_eq_of_isAlgebraic_top F Γ(Y, U) Y.functionField).trans h₂⟩

theorem topologicalKrullDim_open (F : Type) [Field F] {Y : Scheme.{0}} [IsIntegral Y]
    (f : Y ⟶ Sp F) [LocallyOfFiniteType f] (V : Y.Opens) (hne : (V : Set Y).Nonempty) :
    topologicalKrullDim (V : Set Y) = topologicalKrullDim Y := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra

  have chart : ∀ (V : Y.Opens) (x : Y), x ∈ V → ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ V :=
    fun V x hx ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
      exact ⟨U, hU, hxU, hUV⟩
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨U₀, hU₀, hx₀U₀, -⟩ := chart V x₀ hx₀
  obtain ⟨d₀, -, hd₀⟩ := ringKrullDim_affineOpen F f hU₀ ⟨x₀, hx₀U₀⟩
  have affDim : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      topologicalKrullDim (U : Set Y) = d₀ := fun U hU hUne ↦ by
    obtain ⟨d, h₁, h₂⟩ := ringKrullDim_affineOpen F f hU hUne
    obtain rfl : d = d₀ := by exact_mod_cast h₂.symm.trans hd₀
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have openDim : ∀ V : Y.Opens, (V : Set Y).Nonempty → topologicalKrullDim (V : Set Y) = d₀ :=
    fun V hV ↦ topologicalKrullDim_eq_of_forall_exists_isOpen hV fun x hx ↦ by
      obtain ⟨U, hU, hxU, hUV⟩ := chart V x hx
      refine ⟨U, U.isOpen, hxU, ?_⟩
      rw [Set.inter_eq_left.mpr hUV]
      exact affDim U hU ⟨x, hxU⟩
  have htop := openDim ⊤ ⟨x₀, trivial⟩
  rw [openDim V ⟨x₀, hx₀⟩, ← htop]
  exact (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Z := ((⊤ : Y.Opens) : Set Y)) (by simp))

theorem topologicalKrullDim_eq_of_isIso_restrict : ∀ (F : Type) [Field F] (W W' : Scheme.{0})
    [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W),
    LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens,
    (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by
  intro F _ W W' _ _ p q h hp hq _ U hU hiso
  have hsurj : Function.Surjective (h ∣_ U) := (h ∣_ U).surjective
  have e₁ : topologicalKrullDim (U : Set W) = topologicalKrullDim (h ⁻¹ᵁ U) := by
    refine topologicalKrullDim_eq_of_isEmbedding ((h ∣_ U) ≫ U.ι).isOpenEmbedding.isEmbedding ?_
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
  have e₂ : topologicalKrullDim ((h ⁻¹ᵁ U : W'.Opens) : Set W') =
      topologicalKrullDim (h ⁻¹ᵁ U) :=
    topologicalKrullDim_eq_of_isEmbedding (h ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding
      (Scheme.Opens.range_ι _)
  have hne : ((h ⁻¹ᵁ U : W'.Opens) : Set W').Nonempty := by
    obtain ⟨u, hu⟩ := hU
    obtain ⟨y, -⟩ := hsurj ⟨u, hu⟩
    exact ⟨(h ⁻¹ᵁ U).ι y, by rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩⟩
  rw [← topologicalKrullDim_open F q (h ⁻¹ᵁ U) hne, ← topologicalKrullDim_open F p U hU, e₁, e₂]

end GlobalTheory.OpenDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceWedgePairingPerfectRationalFormsStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ p q : ℕ, p + q = d → (∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ ⋀[K]^p Ω[K⁄k], Algebra.trace F K (τ (a * y)) = 0) → y = 0) ∧ Module.finrank K (⋀[K]^p Ω[K⁄k]) = Module.finrank K (⋀[K]^q Ω[K⁄k]) ∧ FiniteDimensional K (⋀[K]^p Ω[K⁄k]) := by
  first | (exact @GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (exact GlobalTheory.PD.IsFinCover.trace_wedge_perfect) | (intros; apply GlobalTheory.PD.IsFinCover.trace_wedge_perfect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportAlg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.HT.TateTransportO

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul_left hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

theorem transport_alg :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p)
    {R k k' QR Q Q' : Type} [CommRing R] [Field k] [Field k'] [Group QR] [Group Q] [Group Q'],
    (∀ a b : QR, a * b = b * a) →
    ∀ (actR : D.O → QR → QR) (act : D.O → Q → Q) (act' : D.O → Q' → Q')
    (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → k'ˣ → Prop)
    (ρ : QR →* Q) (ρ' : QR →* Q') (φ : Rˣ →* kˣ) (φ' : Rˣ →* k'ˣ),
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q', x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ' g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ u = φ v → u = v) →
    (∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ φ u = z) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ' u = φ' v → u = v) →
    (∀ c g h, actR c (g * h) = actR c g * actR c h) →
    (∀ c g, ρ (actR c g) = act c (ρ g)) → (∀ c g, ρ' (actR c g) = act' c (ρ' g)) →
    (∀ c, act' c 1 = 1) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rˣ, u ^ n = 1 ∧ e n (ρ g) (ρ h) (φ u) ∧ e' n (ρ' g) (ρ' h) (φ' u)) →
    (∀ n, 0 < n → n.Coprime p → ∀ x y c c', e n x y c → e n x y c' → c = c') →
    ∀ (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e),
    ∃ I' : GlobalTheory.UPel.HT.TateIsoO D k' Q' act' e', ∀ n, 0 < n → n.Coprime p → ∀ a (g : QR), g ^ n = 1 →
      ρ g = I.ev n a → ρ' g = I'.ev n a := by
  intro p _ D R k k' QR Q Q' _ _ _ _ _ _ hcomm actR act act' e e' ρ ρ' φ φ' hρi hρs hρ'i hρ's hφi hφs hφ'i
    hactR hρact hρ'act hact'1 hpair huniq I
  obtain ⟨L, hL⟩ := exists_torsLift p ρ hρi
  obtain ⟨W, hW⟩ := exists_torsLift p φ hφi
  have hLx : ∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → L x ^ n = 1 ∧ ρ (L x) = x := by
    intro n hn hnp x hx
    obtain ⟨g, hg, rfl⟩ := hρs n hn hnp x hx
    rw [hL n hn hnp g hg]; exact ⟨hg, rfl⟩
  have hWx : ∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → W z ^ n = 1 ∧ φ (W z) = z := by
    intro n hn hnp z hz
    obtain ⟨u, hu, rfl⟩ := hφs n hn hnp z hz
    rw [hW n hn hnp u hu]; exact ⟨hu, rfl⟩
  have hLmul : ∀ n, 0 < n → n.Coprime p → ∀ x y : Q, x ^ n = 1 → y ^ n = 1 → L (x * y) = L x * L y := by
    intro n hn hnp x y hx hy
    obtain ⟨hx1, hx2⟩ := hLx n hn hnp x hx
    obtain ⟨hy1, hy2⟩ := hLx n hn hnp y hy
    have := hL n hn hnp (L x * L y)
      (by rw [(show Commute (L x) (L y) from hcomm _ _).mul_pow, hx1, hy1, _root_.one_mul])
    rwa [map_mul, hx2, hy2] at this
  have hevt : ∀ n, 0 < n → n.Coprime p → ∀ a, I.ev n a ^ n = 1 :=
    fun n hn hnp a => (I.onto n hn hnp _).2 ⟨a, rfl⟩
  have hζt : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 :=
    fun n hn hnp => (I.ζ_prim n hn hnp).pow_eq_one
  have hactR1 : ∀ c, actR c 1 = 1 := fun c => by
    have := hactR c 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have hactRpow : ∀ c g (n : ℕ), actR c (g ^ n) = actR c g ^ n := by
    intro c g n
    induction n with
    | zero => simp [hactR1]
    | succ n ih => rw [pow_succ, hactR, ih, pow_succ]
  have hLact : ∀ n, 0 < n → n.Coprime p → ∀ c x, x ^ n = 1 → L (act c x) = actR c (L x) := by
    intro n hn hnp c x hx
    obtain ⟨h1, h2⟩ := hLx n hn hnp x hx
    have := hL n hn hnp (actR c (L x)) (by rw [← hactRpow, h1, hactR1])
    rwa [hρact, h2] at this
  refine ⟨{ ζ := fun n => φ' (W (I.ζ n)),
             ζ_prim := ?_,
             ζ_pow := ?_,
             ev := fun n a => if 0 < n ∧ n.Coprime p then ρ' (L (I.ev n a)) else 1,
             add := ?_,
             lin := ?_,
             ker := ?_,
             onto := ?_,
             tower := ?_,
             isom := ?_ }, ?_⟩
  · intro n hn hnp
    obtain ⟨hw1, hw2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    refine ⟨by rw [← map_pow, hw1, map_one], fun l hl => ?_⟩
    rw [← map_pow] at hl
    have : W (I.ζ n) ^ l = 1 := hφ'i n hn hnp _ _
      (by rw [← pow_mul, mul_comm, pow_mul, hw1, one_pow]) (one_pow n) (by rw [hl, map_one])
    exact (I.ζ_prim n hn hnp).dvd_of_pow_eq_one l (by rw [← hw2, ← map_pow, this, map_one])
  · intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    obtain ⟨a1, a2⟩ := hWx (n * m) (Nat.mul_pos hn hm) hnm _ (hζt _ (Nat.mul_pos hn hm) hnm)
    obtain ⟨b1, b2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    show φ' (W (I.ζ (n * m))) ^ m = φ' (W (I.ζ n))
    rw [← map_pow, hφi n hn hnp (W (I.ζ (n * m)) ^ m) (W (I.ζ n))
      (by rw [← pow_mul, mul_comm m n, a1]) b1 (by rw [map_pow, a2, b2, I.ζ_pow n m hn hm hnm])]
  · intro n a b
    split_ifs with h
    · rw [I.add, hLmul n h.1 h.2 _ _ (hevt n h.1 h.2 a) (hevt n h.1 h.2 b), map_mul]
    · rw [_root_.mul_one]
  · intro n c a
    split_ifs with h
    · rw [I.lin, hLact n h.1 h.2 c _ (hevt n h.1 h.2 a), hρ'act]
    · rw [hact'1]
  · intro n hn hnp a
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    rw [← I.ker n hn hnp a]
    obtain ⟨h1, h2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    constructor
    · intro h
      have := hρ'i n hn hnp _ 1 h1 (one_pow n) (by rw [h, map_one])
      rw [← h2, this, map_one]
    · intro h
      rw [h, ← map_one ρ, hL n hn hnp 1 (one_pow n), map_one]
  · intro n hn hnp y
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    constructor
    · intro hy
      obtain ⟨g, hg1, rfl⟩ := hρ's n hn hnp y hy
      obtain ⟨a, ha⟩ := (I.onto n hn hnp (ρ g)).1 (by rw [← map_pow, hg1, map_one])
      exact ⟨a, by rw [ha, hL n hn hnp g hg1]⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (hLx n hn hnp _ (hevt n hn hnp a)).1, map_one]
  · intro n m hn hm hnm a
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    have hnm0 : 0 < n * m := Nat.mul_pos hn hm
    have hg1 : 0 < n * m ∧ (n * m).Coprime p := ⟨hnm0, hnm⟩
    have hg2 : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg1, if_pos hg2]
    obtain ⟨h1, h2⟩ := hLx (n * m) hnm0 hnm _ (hevt _ hnm0 hnm a)
    have := hL n hn hnp (L (I.ev (n * m) a) ^ m) (by rw [← pow_mul, mul_comm m n, h1])
    rw [map_pow, h2, I.tower n m hn hm hnm] at this
    rw [← map_pow, ← this]
  · intro n hn hnp a b
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    obtain ⟨ga1, ga2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    obtain ⟨gb1, gb2⟩ := hLx n hn hnp _ (hevt n hn hnp b)
    obtain ⟨u, hu, he, he'⟩ := hpair n hn hnp _ _ ga1 gb1
    rw [ga2, gb2] at he
    obtain ⟨w1, w2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    have hk := huniq n hn hnp _ _ _ _ he (I.isom n hn hnp a b)
    have hu' : u = W (I.ζ n) ^ (2 * D.EF a b) := hφi n hn hnp _ _ hu
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm (2 * D.EF a b), zpow_mul, zpow_natCast, w1, one_zpow])
      (by rw [hk, map_zpow, w2])
    rw [hu', map_zpow] at he'
    exact he'
  · intro n hn hnp a g hg hρg
    have hgd : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hgd]
    rw [← hρg, hL n hn hnp g hg]

end GlobalTheory.UPel.HT.TateTransportO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBases
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.TypicalCurveBases

theorem typical_curves_tangent_and_bases : TypicalCurveEigenspace ∧ TypicalCurveBasisExists :=
  have h2 : TypicalCurveEigenspace :=
    GlobalTheory.TypicalCurve.typicalCurves_of_type_of_typical_tangents GlobalTheory.PTypicalTangent.exists_pTypical_tangent
  ⟨h2, GlobalTheory.typicalBasis_coordinates h2⟩

end GlobalTheory.TypicalCurveBases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDivLeOneCofinite
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.LocGenVal

theorem valuation_div_le_one_cofinite : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  intro K _ _ I u
  classical
  have h1 := Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K) I)
  have h2 := Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (K := K) (FractionalIdeal.spanSingleton (𝓞 K)⁰ u))
  refine ⟨(h1.union h2).toFinset, ?_⟩
  intro p hp a ha hu
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
  obtain ⟨hpI, hpu⟩ := hp
  have hau : a / u ≠ 0 := div_ne_zero ha.1 hu
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsu : FractionalIdeal.spanSingleton (𝓞 K)⁰ u ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hu
  have hc : FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / u)) = 0 := by
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_mul K p hsa (inv_ne_zero hsu), FractionalIdeal.count_inv, ha.2, hpI, hpu]
    simp
  rw [Formalism.L2.LamCM.valuation_eq_exp_neg_count p hau, hc, neg_zero, WithZero.exp_zero]

end GlobalTheory.LocGenVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChangeStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sign_iMulti_D_chart_change : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i : Fin (d + 1), ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) = ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  first | (exact @GlobalTheory.PD.volume_chart_change) | (exact GlobalTheory.PD.volume_chart_change) | (intros; apply GlobalTheory.PD.volume_chart_change <;> assumption)
end

