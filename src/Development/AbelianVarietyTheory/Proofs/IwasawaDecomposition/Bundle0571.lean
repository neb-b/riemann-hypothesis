module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_V_of_forall (W : ValuationSubring ℂ) (h : ∀ p : ℕ, p.Prime → (p : ℂ) ∉ W.nonunits) (x : c.F) :
    x ∈ c.V W := by
  have hv1 : ∀ n : ℕ, n ≠ 0 → W.valuation (n : ℂ) = 1 := by
    intro n hn
    induction n using Nat.recOnMul with
    | zero => exact absurd rfl hn
    | one => simp
    | prime p hp =>
      refine le_antisymm ((W.valuation_le_one_iff _).2 (natCast_mem W p)) (not_lt.1 fun hlt => h p hp ?_)
      exact (W.mem_nonunits_iff).2 hlt
    | mul a b iha ihb =>
      have ha : a ≠ 0 := left_ne_zero_of_mul hn
      have hb : b ≠ 0 := right_ne_zero_of_mul hn
      rw [Nat.cast_mul, map_mul, iha ha, ihb hb, one_mul]
  have hvi : ∀ n : ℤ, n ≠ 0 → ((n : ℂ))⁻¹ ∈ W := by
    intro n hn
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have e : W.valuation (n : ℂ) = 1 := by
      rcases Int.natAbs_eq n with h1 | h1
      · rw [h1, Int.cast_natCast]; exact hv1 _ hn'
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact hv1 _ hn'
    refine (W.valuation_le_one_iff _).1 ?_
    rw [map_inv₀, e, inv_one]
  haveI := c.fin
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := x)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).mpr (Algebra.IsAlgebraic.isAlgebraic _))
  let i : c.F →+* ℂ := c.F.val.toRingHom
  have h1 : _root_.IsIntegral ℤ (i (n • x)) := hint.map i.toIntAlgHom
  have h2 : _root_.IsIntegral W (i (n • x)) := h1.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : i (n • x) ∈ W := by
    have hw' : (w : ℂ) = i (n • x) := hw
    rw [← hw']; exact w.2
  have h4 : i x = ((n : ℂ))⁻¹ * i (n • x) := by
    have hn0 : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [zsmul_eq_mul, map_mul, map_intCast, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  change i x ∈ W
  rw [h4]
  exact W.mul_mem _ _ (hvi n hn) h3

theorem isOpenImmersion_j (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ (p : ℂ) ∈ W.nonunits
  · obtain ⟨p, hp, hW⟩ := h
    exact GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  · push_neg at h
    have hbij : Function.Bijective (c.V W).subtype :=
      ⟨Subtype.val_injective, fun x => ⟨⟨x, mem_V_of_forall W h x⟩, rfl⟩⟩
    have h1 : IsIso (CommRingCat.ofHom (c.V W).subtype) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    have : IsIso (spMap (c.V W).subtype) := by
      unfold spMap; infer_instance
    have := Y.jQ_open
    unfold Model.j
    infer_instance

end GlobalTheory.TriplesAlong

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.TriplesAlong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConePullOfSurjective
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem apply_eq_zero_of_diag {X : Type} [AddCommGroup X] {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hp : ∀ y, 0 ≤ β y y) {y : X} (hy : β y y = 0) (z : X) : β y z = 0 := by
  by_contra hb
  have hA := hp z
  have h := hp (z + (-(β z z + 1) * β y z) • y)
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hy, hs z y] at h
  have hb2 : 1 ≤ β y z * β y z := mul_self_pos.2 hb
  have h3 := mul_nonneg (by linarith : 0 ≤ β z z + 1) (sub_nonneg.2 hb2)
  nlinarith [h3]

theorem exists_pull_eq {O : Type} [CommRing O] {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]
    {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y)
    (hk : ∀ y, r y = 0 → ∀ z, β y z = 0) : ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = β := by
  have key1 : ∀ a a' b, r a = r a' → β a b = β a' b := fun a a' b h => by
    have := hk (a - a') (by rw [map_sub, h, sub_self]) b
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  have key : ∀ a a' b b', r a = r a' → r b = r b' → β a b = β a' b' := fun a a' b b' h h' => by
    rw [key1 a a' b h, hs a' b, key1 b b' a' h', hs]
  have hs' : ∀ a, r (Function.surjInv hr a) = a := Function.surjInv_eq hr
  refine ⟨LinearMap.mk₂ ℤ (fun a b => β (Function.surjInv hr a) (Function.surjInv hr b)) ?_ ?_ ?_ ?_,
    LinearMap.ext₂ fun a b => ?_⟩
  · intro a a' b
    rw [← LinearMap.add_apply, ← map_add (f := _)]
    exact key _ _ _ _ (by rw [map_add (f := _), hs', hs', hs']) rfl
  · intro n a b
    rw [← LinearMap.smul_apply, ← map_smul]
    exact key _ _ _ _ (by rw [map_zsmul r, hs', hs']) rfl
  · intro a b b'
    rw [← map_add (f := _)]
    exact key _ _ _ _ rfl (by rw [map_add (f := _), hs', hs', hs'])
  · intro n a b
    rw [← map_smul]
    exact key _ _ _ _ rfl (by rw [map_zsmul r, hs', hs'])
  · simpa using key _ _ _ _ (hs' (r a)) (hs' (r b))

theorem isCone_pull_of_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (φ : InvFun O) (X₁ : Type) [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₁), IsPolFanOn bar φ X → Function.Surjective r → IsCone bar φ γ → IsCone bar φ (fun i => pull r (γ i)) := by
  intro O _ _ _ _ bar X _ _ _ φ X₁ _ _ _ r m γ hF hr hγ
  classical
  have hx := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X m (fun i => pull r (γ i)) (fun _ => 1) (fun i => pull_mem r (hγ.mem i))
    (fun i y => hγ.nonneg i _) (fun _ => zero_le_one)
  obtain ⟨m₂, σ, c, hσ, hc, hsum⟩ := hF.cover _ hx
  let J : Finset (Fin m₂) := Finset.univ.filter fun j => c j ≠ 0
  let t : Fin J.card ↪ Fin m₂ := (J.orderEmbOfFin rfl).toEmbedding
  have hpos : ∀ k, c (t k) ≠ 0 := fun k => (Finset.mem_filter.1 (J.orderEmbOfFin_mem rfl k)).2
  have hout : ∀ j, j ∉ Set.range t → c j = 0 := fun j hj => by
    by_contra h0
    refine hj ?_
    have : j ∈ Set.range (J.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩)
    exact this
  have hδ := hF.face _ _ σ t hσ
  have hsum' : ∑ i, (1 : ℝ) • toReal (pull r (γ i)) = ∑ k, c (t k) • toReal (σ (t k)) :=
    hsum.trans (Fintype.sum_of_injective t t.injective _ _ (fun j hj => by simp [hout j hj]) fun _ => rfl).symm
  have hvan : ∀ k y, r y = 0 → σ (t k) y y = 0 := fun k y hy => by
    have h1 := LinearMap.congr_fun₂ hsum' y y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply, hy, map_zero, LinearMap.zero_apply,
      Int.cast_zero, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hc (t k))
      (by exact_mod_cast hσ.nonneg (t k) y : (0 : ℝ) ≤ (σ (t k) y y : ℝ))).1 h1.symm k (Finset.mem_univ _)
    exact_mod_cast (mul_eq_zero.1 h2).resolve_left (hpos k)
  have hex : ∀ k, ∃ β' : LinearMap.BilinForm ℤ X₁, pull r β' = σ (t k) := fun k =>
    exists_pull_eq hr (hσ.mem (t k)).1 fun y hy z =>
      apply_eq_zero_of_diag (hσ.mem (t k)).1 (hσ.nonneg (t k)) (hvan k y hy) z
  choose δ hδ' using hex
  have hδc : IsCone bar φ δ := GlobalTheory.PolFan.isCone_of_pull O bar φ X X₁ r _ δ hr (by simpa only [hδ'] using hδ)
  have hsum₁ : ∑ i, (1 : ℝ) • toReal (γ i) = ∑ k, c (t k) • toReal (δ k) := LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    have h1 := LinearMap.congr_fun₂ hsum' a b
    simp only [← hδ'] at h1
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, pull_apply] using h1
  have hmeet := GlobalTheory.PolFan.cone_meet O bar φ X₁ m _ γ δ (fun _ => 1) (fun k => c (t k)) hγ hδc (fun _ => zero_le_one)
    (fun k => hc _) hsum₁
  choose j hj using fun i => hmeet i one_ne_zero
  have hinj : Function.Injective j := fun i i' h =>
    hγ.injective ((hj i).1.trans ((congrArg δ h).trans (hj i').1.symm))
  have hfin := hF.face _ _ _ ⟨j, hinj⟩ hδ
  have heq : (fun i => pull r (γ i)) = fun i => σ (t (j i)) := funext fun i => by rw [(hj i).1, hδ']
  rw [heq]
  exact hfin

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpenGlobal

theorem exists_unit (S : Scheme.{0}) (s : S) :
    ∃ n : ℕ, 2 ≤ n ∧ s ∈ S.basicOpen (n : Γ(S, ⊤)) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (R := S.presheaf.stalk s) (a := (3 : S.presheaf.stalk s)) (b := -2)
      (by norm_num) with h | h
  · refine ⟨3, by norm_num, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast h
  · refine ⟨2, le_rfl, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast (IsUnit.neg_iff _).1 h

theorem isOpen_connectedComponent_of_noetherian {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  rw [← isClosed_compl_iff, show (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z from
    Set.ext fun y => ⟨fun h => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, fun k => h (k mem_irreducibleComponent)⟩
      mem_irreducibleComponent, fun h k => by
      obtain ⟨Z, ⟨a, b⟩, c⟩ := Set.mem_iUnion₂.1 h
      exact b ((a.1.isConnected.isPreconnected.subset_connectedComponent c).trans (connectedComponent_eq k).ge)⟩]
  exact (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion fun Z h =>
    isClosed_of_mem_irreducibleComponents Z h.1

theorem exists_connected_open {S : Scheme.{0}} [IsLocallyNoetherian S] (N : S.Opens) (s : S) (hs : s ∈ N) :
    ∃ (V : Scheme.{0}) (w : V ⟶ S), IsOpenImmersion w ∧ ConnectedSpace V ∧ s ∈ Set.range w ∧
      Set.range w ⊆ (N : Set S) := by
  obtain ⟨U, hU, hsU, hUN⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := N) (x := s) hs
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace U.toScheme := inferInstance
  let V : U.toScheme.Opens := ⟨_, isOpen_connectedComponent_of_noetherian (X := U.toScheme) ⟨s, hsU⟩⟩
  have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, this, ⟨⟨⟨s, hsU⟩, mem_connectedComponent⟩, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hUN (V.ι v).2

theorem isOpen_abLocus_of_locallyNoetherian {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨n, h2, hn⟩ := exists_unit S s
  obtain ⟨V, w, hw, hV, ⟨v, rfl⟩, hle⟩ := exists_connected_open _ s hn
  have hG' : IsSemiAbelian ((Over.pullback w).obj G) := IsSemiAbelian.pullback w G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback w).obj G).left := GeometricallyConnected.connectedSpace ((Over.pullback w).obj G).hom ((Over.pullback w).obj G).hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty ((Over.pullback w).obj G).left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected ((Over.pullback w).obj G).hom x₀
  have hu : IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
    have h₀ := RingedSpace.isUnit_res_basicOpen S.toRingedSpace ((n : ℕ) : Γ(S, ⊤))
    have h₁ : (⊤ : V.Opens) ≤ w ⁻¹ᵁ S.basicOpen ((n : ℕ) : Γ(S, ⊤)) := fun y _ => hle ⟨y, rfl⟩
    have h₀' : IsUnit ((n : ℕ) : Γ(S, S.basicOpen ((n : ℕ) : Γ(S, ⊤)))) := by
      simp only [map_natCast] at h₀
      exact h₀
    have := h₀'.map (w.appLE _ ⊤ h₁).hom
    rwa [map_natCast] at this
  have hU := AbLocusOpen.isOpen_abLocus ((Over.pullback w).obj G) hG' hg h2 hu
  have key : ∀ y : V, w y ∈ abLocus G ↔ y ∈ abLocus ((Over.pullback w).obj G) := fun y =>
    abLocus_pullback abLocusOne hG (isGrpPullback_pullback G w).1 y
  refine ⟨w '' abLocus ((Over.pullback w).obj G), ?_, w.isOpenEmbedding.isOpenMap _ hU, ⟨v, (key v).1 hs, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (key y).2 hy

end GlobalTheory.AbLocusOpenGlobal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw TopologicalSpace

namespace GlobalTheory.ProperFinite

theorem finite_coh_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (f : X ⟶ Sp R)
    [IsProper f] (F : X.Modules) [QCoh.IsFiniteQC F] (p : ℕ) :
    letI := algebraΓOfHom f; Module.Finite R (coh F p) :=
  finite_coh_of_forall_modification f (fun Z _ ι _ => GlobalTheory.ChowLemma.exists_isProjOver_isIso_morphismRestrict R Z (ι ≫ f)) F p

theorem nonempty_perf_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) : Nonempty (Perf f M) := by
  let := algebraΓOfHom f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := Y) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have := Twist.isFiniteQC_twist (F := structureModule Y) hM
  obtain ⟨K, φ, -, h2, -, h4, -, -, h7⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} (cechLB f M D) m
      (fun p hp => isZero_cechLB_X f M _ (by rw [Fintype.card_fin]; exact hp.le))
      (flat_cechLB_X f hM hD') (fun n => by
        obtain ⟨e⟩ := FieldChangeInter.nonempty_coh_equiv f hM hc hD' n
        have := finite_coh_of_isProper f (twist (structureModule Y) M) n
        exact Module.Finite.equiv e.symm)
  exact perf_of_projective_model R Y f M (Fin m) _ K φ hM hc hD' ⟨fun p => ⟨h2 p, h4 p⟩, h7⟩


open FibreLift in
theorem exists_pull_eq_smul {R : Type} [CommRing R] [IsNoetherianRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R)
    [IsProper f] [Flat f] {M : LB Y} (hM : M.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) {Y₀ : Scheme.{0}} {π : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ Sp K}
    (h : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g))) (hH : FirstCohomologyVanishes (M.pull π))
    (x₀ : SecOnR f₀ (M.pull π) ⊤) :
    ∃ (c : R) (x : SecOnR f M ⊤), g c ≠ 0 ∧ SecOnR.pull M h.w ⊤ ⊤ le_top x = g c • x₀ := by
  obtain ⟨P⟩ := nonempty_perf_of_isProper f hM
  obtain ⟨r, n, B, hr, hB, hu⟩ := exists_matrix_basis_ker_of_exact_at_point R K g _ _ _ P.D₀ P.D₁
    P.comp (P.exact K g Y₀ π f₀ h hH)
  obtain ⟨E, hE⟩ := P.sec K g Y₀ π f₀ h
  obtain ⟨v₀, hv₀⟩ := E.surjective (SecOnR.topEquiv f₀ _ x₀)
  obtain ⟨z, hz, -⟩ := hu K g hr.isUnit v₀.1 v₀.2
  obtain ⟨c, w, hc, hw⟩ := exists_common_denominator g hg z
  have hv : g ∘ B.mulVec w = g c • v₀.1 := by
    rw [← hz, ← Matrix.mulVec_smul, ← hw]
    exact funext fun j => RingHom.map_mulVec g _ _ j
  obtain ⟨s, hs⟩ := exists_sec_of_ker P (B.mulVec w)
    (by rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec])
  refine ⟨c, (SecOnR.topEquiv f M).symm s, hc, (SecOnR.topEquiv f₀ _).injective ?_⟩
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i)
    (fun i => le_pull M π (P.le i)) (fun y => Seesaw.exists_mem P (π y)) fun i => ?_
  have e₁ := Seesaw.loc_comp P h (B.mulVec w) i
  rw [hv, Seesaw.loc_smul, ← hs] at e₁
  have e₂ : Seesaw.loc P π f₀ v₀.1 i = _ := (hE v₀ i).symm
  rw [e₂, hv₀] at e₁
  refine Eq.trans ?_ ((rs_topEquiv_smul f₀ _ (g c) x₀ _ _).trans e₁).symm
  refine (rs_rs _ _ _).trans ?_
  refine (congrArg (rs Y₀ _) (SecOn.coord_pullLE π le_top _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  refine (GlobalTheory.LB.appLE_resG π inf_le_right _ (s.f (P.ch i))).trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  exact (GlobalTheory.LB.appLE_resG π (P.le i) le_rfl _).symm


open AmpleNear in
theorem relAmple_near_fibre {R : Type} [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [IsProper B.hom]
    [Flat B.hom] {L : LB B.left} (hL : L.IsLB) {K : Type} [Field K] (g : R →+* K)
    (hg : ∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a)
    (hA : RelAmple ((Over.pullback (spMap g)).obj B) (L.pull (pullback.fst B.hom (spMap g)))) :
    ∃ r : R, g r ≠ 0 ∧
      RelAmple ((Over.pullback (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r))).obj B)
        (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)))) := by
  have h := IsPullback.of_hasPullback B.hom (spMap g)
  obtain ⟨d, hd, h0, hv⟩ := exists_pw_h1Zero K _ _ (LB.isLB_pull hL _) hA
  have hv' : FirstCohomologyVanishes ((pw L d).pull (pullback.fst B.hom (spMap g))) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec ((pw L d).pull (pullback.fst B.hom (spMap g)))),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [pw_pull]
    obtain ⟨n, s, hs⟩ := hv
    exact ⟨h0, n, s, hs.1, fun i => (hs.2 i).1⟩
  obtain ⟨h1, n, s₀, hs₀, hs₀'⟩ := hv'
  choose c x hc hx using fun i => exists_pull_eq_smul B.hom (isLB_pw hL d) g hg h h1
    ((SecOnR.topEquiv _ _).symm (s₀ i))
  have e := fun i => preimage_nonzeroLocus_of_pull_eq h.w (pw L d) (x i) _ (hc i) (hx i)
  simp only [LinearEquiv.apply_symm_apply] at e
  obtain ⟨r, hr, hr'⟩ := exists_affine_loci_near B.hom (pw L d) (isLB_pw hL d)
    (fun i => SecOnR.topEquiv B.hom _ (x i)) g _ _ h (by simpa only [e] using hs₀)
    (by simpa only [e] using hs₀')
  refine ⟨r, hr, ?_⟩
  let j := Scheme.Opens.ι (X := Sp R) (PrimeSpectrum.basicOpen r)
  have : IsAffine (Scheme.Opens.toScheme (X := Sp R) (PrimeSpectrum.basicOpen r)) :=
    IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) r
  have hv : ∃ s : Fin (n + 1) → LB.Sec (pw (L.pull (pullback.fst B.hom j)) d),
      ⨆ i, nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) := by
    rw [← pw_pull]
    refine ⟨fun i => secPull (SecOnR.topEquiv B.hom _ (x i)) _, ?_⟩
    simp only [nonzeroLocus_secPull]
    exact hr' _ _ _ (IsPullback.of_hasPullback B.hom j)
  obtain ⟨s, hs, hs'⟩ := hv
  have : IsProper ((Over.pullback j).obj B).hom := inferInstanceAs (IsProper (pullback.snd B.hom j))
  exact relAmple_of_affine_loci ((Over.pullback j).obj B) _ (LB.isLB_pull hL _) hd s hs hs'


open FibreAmple in
theorem relAmple_of_geometricFibres {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [IsProper A.hom]
    [Flat A.hom] {M : LB A.left} (hM : M.IsLB)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), IsAmpleLB (M.pull (pullback.fst A.hom y))) :
    RelAmple A M := by
  refine AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Sp Γ(S, V) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback A.hom t
  have hL := pull_isLB hM (pullback.fst A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  have : IsProper (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : Flat (Over.mk (pullback.snd A.hom t)).hom := inferInstanceAs (Flat (pullback.snd A.hom t))
  have : IsProper (Over.mk (pullback.snd A.hom (spMap i ≫ spMap g ≫ t))).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom _))
  obtain ⟨r, hr, hA⟩ := relAmple_near_fibre (Over.mk (pullback.snd A.hom t)) hL g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _)
      ((relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)).2 (hfib _ _)))
  let D : (Sp Γ(S, V)).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.ProperFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
section
noncomputable section

open Matrix

namespace GlobalTheory.RedTh

structure IsSiegel {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Prop where

  nonneg : ∀ i, 0 ≤ d i

  step : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q

  diag : ∀ i, u i i = 1

  lower : ∀ i j, j < i → u i j = 0

  upper : ∀ i j, i < j → |u i j| ≤ 1 / 2

def gram {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := uᵀ * diagonal d * u

section Act

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {n : ℕ}

def actMat (b : Module.Basis (Fin n) ℤ X) : O →+* Matrix (Fin n) (Fin n) ℤ :=
  ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (Module.toModuleEnd ℤ X)

theorem actMat_apply (b : Module.Basis (Fin n) ℤ X) (c : O) (i j : Fin n) : actMat b c i j = b.repr (c • b j) i := by
  show LinearMap.toMatrixAlgEquiv b (Module.toModuleEnd ℤ X c) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end Act

end GlobalTheory.RedTh
end
end

