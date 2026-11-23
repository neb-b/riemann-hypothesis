module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceOrdEqAlongEtaleTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderDifferentialFormEtTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.GaussBC

theorem two_le_coheight_of_chain {X : Scheme.{0}} {x e g : X} (h₁ : e ⤳ x) (h₂ : g ⤳ e) (n₁ : e ≠ x)
    (n₂ : g ≠ e) : (2 : ℕ∞) ≤ Order.coheight x := by
  have l₁ : x < e := lt_of_le_not_ge h₁ (fun h => n₁ (h₁.antisymm h).eq)
  have l₂ : e < g := lt_of_le_not_ge h₂ (fun h => n₂ (h₂.antisymm h).eq)
  have a₁ := Order.coheight_add_one_le l₁
  have a₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight g + 1 + 1 := by gcongr; exact zero_le
    _ ≤ Order.coheight e + 1 := by gcongr
    _ ≤ Order.coheight x := a₁

theorem not_two_le_coheight_of_ringKrullDim_eq_one {X : Scheme.{0}} (x : X)
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : ¬ (2 : ℕ∞) ≤ Order.coheight x := by
  intro h₂
  rw [ringKrullDim_stalk_eq_coheight] at h
  have : Order.coheight x = 1 := by exact_mod_cast h
  rw [this] at h₂
  exact absurd h₂ (by decide)

theorem apply_genericPoint_ne_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp R) [Flat f] : f (genericPoint X) ≠ closedPoint R := by
  intro h
  let p₀ : Sp R := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : p₀ ⤳ f (genericPoint X) := by
    rw [h]; exact (PrimeSpectrum.le_iff_specializes p₀ (closedPoint R)).mp bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hs
  have hw' : w = genericPoint X := (hw.antisymm (genericPoint_specializes w)).eq
  rw [hw', h] at hfw
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal hfw)

theorem apply_eq_of_closedFibre_dim_one : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hG hpb _ y y' hy hy' hdy hdy'
  haveI : Smooth H.hom := hG.smooth
  haveI : Flat H'.hom := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat H.hom))
  haveI : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ha
  haveI : Flat π := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat (spMap a)))
  have hsq : ∀ z, H.hom (π z) = spMap a (H'.hom z) := fun z => by
    have := congrArg (fun f => f.base z) hpb.w
    simpa using this
  have hcl : spMap a (closedPoint D) = closedPoint T := by
    apply PrimeSpectrum.ext
    show Ideal.comap a (maximalIdeal D) = maximalIdeal T
    have hle : maximalIdeal T ≤ Ideal.comap a (maximalIdeal D) := Ideal.map_le_iff_le_comap.mp hm.le
    exact ((maximalIdeal.isMaximal T).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hback : ∀ p : Sp D, spMap a p = closedPoint T → p = closedPoint D := by
    intro p hp
    by_contra hne
    have hbot : p.asIdeal = ⊥ := by
      by_contra hb
      exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hb)))
    have hker : Ideal.comap a ⊥ = maximalIdeal T := by
      rw [← hbot]; exact congrArg PrimeSpectrum.asIdeal hp
    apply IsDiscreteValuationRing.not_a_field D
    rw [← hm, ← hker]
    exact le_antisymm Ideal.map_comap_le bot_le
  set F : Set H.left := H.hom ⁻¹' {closedPoint T} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint T).preimage H.hom.continuous
  have hFi : IsIrreducible F := by
    haveI := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ H hG _ ((Sp T).fromSpecResidueField (closedPoint T))
    haveI : IrreducibleSpace (H.hom.fiber (closedPoint T)) := this
    have hr := (IrreducibleSpace.isIrreducible_univ (H.hom.fiber (closedPoint T))).image _
      (Scheme.Hom.fiberι H.hom (closedPoint T)).continuous.continuousOn
    rw [Set.image_univ] at hr
    convert hr using 1
    exact (Scheme.Hom.range_fiberι H.hom (closedPoint T)).symm
  have hξ₀ := hFi.isGenericPoint_genericPoint_closure
  rw [hFc.closure_eq] at hξ₀
  set ξ₀ := hFi.genericPoint
  have hgH := apply_genericPoint_ne_closedPoint H.hom
  have hgH' := apply_genericPoint_ne_closedPoint H'.hom
  have hyξ₀ : y = ξ₀ := by
    by_contra hne
    refine not_two_le_coheight_of_ringKrullDim_eq_one y hdy
      (two_le_coheight_of_chain (hξ₀.specializes hy) (genericPoint_specializes ξ₀) (Ne.symm hne) ?_)
    intro h; apply hgH; rw [h]; exact hξ₀.mem
  have hzξ₀ : π y' = ξ₀ := by
    by_contra hne
    have hz : π y' ∈ F := by
      show H.hom (π y') = closedPoint T
      rw [hsq, hy', hcl]
    obtain ⟨w, hw, hπw⟩ := Flat.generalizingMap π (hξ₀.specializes hz)
    refine not_two_le_coheight_of_ringKrullDim_eq_one y' hdy'
      (two_le_coheight_of_chain hw (genericPoint_specializes w) ?_ ?_)
    · rintro rfl; exact hne hπw
    · intro h; apply hgH'; apply hback; rw [← hsq, h, hπw]; exact hξ₀.mem
  rw [hzξ₀, hyξ₀]

end GlobalTheory.Desc.GaussBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEffectiveUpEtaleTowerNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem effAt_etTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) (φ : R →₀ ℚ) (θ : T →₀ ℚ),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) → (∀ g ∈ φ.support, g ≠ 0) →
  (∀ g ∈ θ.support, (g : L) ≠ 0 ∧ 0 ≤ θ g) →
  EffAt cK n R (dForm cK (fun i => (x i : K))) (Finsupp.mapDomain (fun g : R => (g : K)) φ) →
  EffAt cL (r + n) T (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))))
    (Finsupp.mapDomain (fun g : R => (ι g : L)) φ + Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
  intro K L _ _ cK cL n r R T ι ψ τ x φ θ hT hx hφ hθ hE
  have hinj : Function.Injective ι := fun a b h => by
    have := congrArg ψ h
    rwa [hT.retr, hT.retr] at this
  have hi : Function.Injective (fun g : R => (ι g : L)) := Subtype.val_injective.comp hinj
  have hι0 : ∀ g : R, g ≠ 0 → (ι g : L) ≠ 0 := fun g hg h =>
    hg (hinj (Subtype.ext (by simpa using h)))
  refine ⟨fun h => ?_, ?_, fun P hP => ?_⟩
  · have hC := _root_.GlobalTheory.FieldPair.isFreeGen_dForm_tower cK cL n r R T ι ψ τ x hT hx
    exact one_ne_zero (hC.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  · rw [Finsupp.add_apply]
    have h1 : Finsupp.mapDomain (fun g : R => (ι g : L)) φ 0 = 0 := by
      have e := Finsupp.mapDomain_apply_of_injective hi φ 0
      simp only [map_zero, ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => hφ 0 h rfl
    have h2 : Finsupp.mapDomain (fun g : T => (g : L)) θ 0 = 0 := by
      have e := Finsupp.mapDomain_apply_of_injective Subtype.val_injective θ 0
      simp only [ZeroMemClass.coe_zero] at e
      rw [e]
      exact Finsupp.notMem_support_iff.1 fun h => (hθ 0 h).1 rfl
    rw [h1, h2, add_zero]
  · have hq : ∀ {M : Type} [Field M] (c : ℂ →+* M) (E : Place c) {A : Type} (f : A → M)
        (ξ : A →₀ ℚ), E.ordQ (Finsupp.mapDomain f ξ) = ξ.sum fun g t => t * (E.ord (f g) : ℚ) := by
      intro M _ c E A f ξ
      rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply]
      rfl
    have hθ' : 0 ≤ P.ordQ (Finsupp.mapDomain (fun g : T => (g : L)) θ) := by
      rw [hq]
      refine Finset.sum_nonneg fun g hg => mul_nonneg (hθ g hg).2 ?_
      exact_mod_cast (P.ord_nonneg_iff (hθ g hg).1).2 (hP.1 _ g.2)
    rw [hq] at hθ'
    rw [Place.disc, map_add (f := _)]
    rcases _root_.GlobalTheory.FieldPair.centre_of_isEtTower cK cL r R T ι ψ τ P hT hP with h0 | ⟨P0, hP0, h0⟩
    · have ho := _root_.GlobalTheory.FieldPair.formOrd_dForm_append_eq_zero cK cL n r R T ι ψ τ x P hT hx hP h0
      change P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = 0 at ho
      rw [ho, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) = 0 :=
        Finset.sum_eq_zero fun g hg => by dsimp only; rw [h0 g (hφ g hg)]; simp
      rw [this]
      push_cast
      linarith
    · have h1 := _root_.GlobalTheory.FieldPair.UnramOrd.ord_eq_of_etTower cK cL r R T ι ψ τ P P0 hT hP hP0 h0
      have hd := hE.2.2 P0 hP0
      rw [Place.disc, hq] at hd
      have ho := _root_.GlobalTheory.FieldPair.formOrd_append_of_ord_eq cK cL n r R T ι ψ τ x P P0 hT hx hP hP0 h1
      change P.formOrd (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) = P0.formOrd (dForm cK (fun i => (x i : K))) at ho
      rw [ho, hq, hq]
      have : (φ.sum fun g t => t * (P.ord (ι g : L) : ℚ)) =
          φ.sum fun g t => t * (P0.ord (g : K) : ℚ) :=
        Finset.sum_congr rfl fun g hg => by dsimp only; rw [h1 g (hφ g hg)]
      rw [this]
      linarith

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem convMul_includeLeft_includeRight {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] :
    (toConv (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] D) *
      toConv (Algebra.TensorProduct.includeRight : D →ₐ[R] D ⊗[R] D)).ofConv = Bialgebra.comulAlgHom R D := by
  ext a
  rw [AlgHom.convMul_apply]
  simp only [Bialgebra.comulAlgHom_apply]
  induction (Coalgebra.comul (R := R) a) with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul u v => simp

theorem cobOne_algebraMap {R : Type} [CommRing R] {D : Type} [CommRing D] [Bialgebra R D] (r : R) :
    cobOne R D (algebraMap R D r) = -algebraMap R (D ⊗[R] D) r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, cobOne_apply, Algebra.algebraMap_eq_smul_one]
  simp [Algebra.TensorProduct.one_def]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isCan_unique (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' := by
  obtain ⟨d, z, w, hz, hw, rfl⟩ := hx
  obtain ⟨d', z', w', hz', hw', rfl⟩ := hx'
  obtain ⟨k, hk⟩ := H1.mk_eq_mk.1 (d.cl.trans d'.cl.symm)
  let κ : Fn0 A := fun D _ _ y ↦ k (trivAt y)
  have hκ : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (y : Pt A D), fv d.f D D' φ y - fv d'.f D D' φ y = κ D' (spOver φ ≫ y) - φ (κ D y) := by
    intro D _ _ D' _ _ φ y
    have := congrFun (congrFun (congrFun hk (trivAt y)) (trivAt (spOver φ ≫ y))) (trivMap φ y)
    exact this.symm
  let e : Fn0 (A ⊗ A) := fun D _ _ u ↦
    d.g D (u ≫ fst A A) (u ≫ snd A A) - d'.g D (u ≫ fst A A) (u ≫ snd A A) -
      (κ D ((u ≫ fst A A) * (u ≫ snd A A)) - κ D (u ≫ fst A A) - κ D (u ≫ snd A A))
  have hcob : IsCob (whole (A ⊗ A)) (Fn1.zero _) e := by
    intro D _ _ D' _ _ φ u _
    have h1 := d.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h2 := d'.add D D' φ (u ≫ fst A A) (u ≫ snd A A)
    have h3 := hκ D D' φ ((u ≫ fst A A) * (u ≫ snd A A))
    have h4 := hκ D D' φ (u ≫ fst A A)
    have h5 := hκ D D' φ (u ≫ snd A A)
    rw [comp_mul] at h3
    simp only [e, Fn1.zero, Category.assoc, map_sub]
    linear_combination -h1 + h2 - h3 + h4 + h5
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.PtExt.NatConst.const_of_natural R (A ⊗ A) Unit (whole _) (by simp [whole]) (globalFns_holds _ (A ⊗ A)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 e hcob
  have he : ∀ (D : Type) [CommRing D] [Algebra R D] (y y' : Pt A D),
      d.g D y y' - d'.g D y y' - (κ D (y * y') - κ D y - κ D y') = algebraMap R D r := by
    intro D _ _ y y'
    have := hr D (lift y y') (sm_whole _)
    simpa [e] using this
  let b : ∀ n, G.A n := fun n ↦ d.h n - d'.h n - κ _ (t.y n) + algebraMap R (G.A n) r
  have hb : b ∈ G.funs := by
    intro n
    have h1 := d.res n
    have h2 := d'.res n
    have h3 := hκ _ _ (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1))
    rw [t.res] at h3
    have h4 : (G.res n : G.A (n + 1) →ₐ[R] G.A n) (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ _
    change (G.res n : G.A (n + 1) →ₐ[R] G.A n) (b (n + 1)) = b n
    have e1 : ∀ a, (G.res n : G.A (n + 1) →ₐ[R] G.A n) a = G.res n a := fun _ ↦ rfl
    simp only [b, map_sub, map_add (f := _), e1] at h3 h4 ⊢
    linear_combination h1 - h2 - h3 + h4
  refine (Submodule.Quotient.eq _).2 ⟨-⟨b, hb⟩, Prod.ext (Subtype.ext (funext fun n ↦ ?_))
    (Subtype.ext (funext fun n ↦ ?_))⟩
  · change cobOne R _ (-b n) = z.1 n - z'.1 n
    rw [hz, hz']
    have hXY := t.mul n (G.A n ⊗[R] G.A n) (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [convMul_includeLeft_includeRight] at hXY
    have h0 := he _ (spOver (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
      (spOver (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) ≫ t.y n)
    rw [← hXY] at h0
    have hc := hκ _ _ (Bialgebra.comulAlgHom R (G.A n)) (t.y n)
    have hL := hκ _ _ (Algebra.TensorProduct.includeLeft : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hR := hκ _ _ (Algebra.TensorProduct.includeRight : G.A n →ₐ[R] G.A n ⊗[R] G.A n) (t.y n)
    have hk1 := cobOne_apply (O := R) (κ _ (t.y n))
    have hk2 := cobOne_algebraMap (R := R) (D := G.A n) r
    simp only [Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply] at hc hL hR
    simp only [Dat.coc, b, map_neg, map_add (f := _), map_sub]
    linear_combination hk1 - hk2 - h0 + hc - hL - hR
  · change dUnit (R := R) (-b n) = w.1 n - w'.1 n
    rw [hw, hw']
    have h0 := GlobalTheory.T.cotVal_sub_eq_dUnit_of_d0_eq_sub R A (G.A n) (t.y n) d.f d'.f k hk
    have h1 : dUnit (R := R) (algebraMap R (G.A n) r) = 0 := AugCot.d_algebraMap _ r
    simp only [Dat.om, b]
    change AugCot.d _ _ = _
    simp only [map_neg, map_add (f := _), map_sub]
    change -(dUnit (R := R) _ - dUnit (R := R) _ - dUnit (R := R) _ + dUnit (R := R) _) = _
    rw [h1]
    change _ = cotVal d.f (t.y n) - dUnit (R := R) _ - (cotVal d'.f (t.y n) - dUnit (R := R) _)
    rw [show cotVal d.f (t.y n) - dUnit (R := R) (d.h n) - (cotVal d'.f (t.y n) - dUnit (R := R) (d'.h n)) =
      (cotVal d.f (t.y n) - cotVal d'.f (t.y n)) - dUnit (R := R) (d.h n) + dUnit (R := R) (d'.h n) by abel, h0]
    abel

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionsCrossRelationOfHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.Two

theorem whisker_comm₂ {C : Type*} [Category C] [CartesianMonoidalCategory C] (T : C) {X₁ X₂ Y₁ Y₂ : C}
    (g₁ : X₁ ⟶ Y₁) (g₂ : X₂ ⟶ Y₂) (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (h : a ≫ g₂ = g₁ ≫ b) :
    T ◁ a ≫ lift (fst _ _) (snd _ _ ≫ g₂) = lift (fst _ _) (snd _ _ ≫ g₁) ≫ T ◁ b := by
  ext <;> simp [h]

theorem crossH_at {R : Type} [CommRing R] [IsDomain R] {A₁ A₂ : PolAV (Sp (FractionRing R))} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {c : A₁.A ⟶ A₂.A} {j j' : ℕ} {t₁ t₂ : SecA A₂ F j} {t₁' t₂' : SecA A₁ F j'}
    (h : CrossH c t₁ t₂ t₁' t₂') {Z : Scheme.{0}} (r : Z ⟶ (TFK (R := R) F ⊗ A₁.A).left) (z : Z) {J₁ J₂}
    (hJ₁ : Good A₁.L z J₁) (hJ₂ : Good A₂.L z J₂) :
    sA t₁ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₂' r z J₁ =
      sA t₂ (r ≫ (TFK (R := R) F ◁ c).left) z J₂ * sA t₁' r z J₁ := by
  have e : ∀ t : SecA A₁ F j', sA t r z J₁ = (r.stalkMap z).hom (sA t (𝟙 _) (r z) (fun ψ => J₁ (r ≫ ψ))) :=
    fun t => by
      have := GlobalTheory.UU.IntExp.sval_comp (L := A₁.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₁.A).left)
        (ε := fun _ => ((j' : ℕ) : ℤ)) t (𝟙 _) r z J₁ hJ₁
      rw [Category.comp_id] at this
      exact this
  have e' : ∀ t : SecA A₂ F j, sA t (r ≫ (TFK (R := R) F ◁ c).left) z J₂ =
      (r.stalkMap z).hom (sA t (TFK (R := R) F ◁ c).left (r z) (fun ψ => J₂ (r ≫ ψ))) :=
    fun t => GlobalTheory.UU.IntExp.sval_comp (L := A₂.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A₂.A).left)
        (ε := fun _ => ((j : ℕ) : ℤ)) t _ r z J₂ hJ₂
  rw [e, e, e', e', ← map_mul, ← map_mul, h (r z) _ _ (fun ψ => hJ₁ (r ≫ ψ)) (fun ψ => hJ₂ (r ≫ ψ))]

theorem carried_cross_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a c hc F _ _ w₁ w₂ _ _ j j' t₁ t₂ t₁' t₂' σ₁ σ₂ σ₁' σ₂'
    h₁ h₂ h₁' h₂' h y J₁ J₂ hJ₁ hJ₂
  have hm : (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left ≫ (U₂.genF F).left =
      (U₁.genF F).left ≫ (TFK (R := R) F ◁ c).left :=
    congrArg (fun q => q.left) (whisker_comm₂ (TFK (R := R) F) U₁.gen.hom U₂.gen.hom _ _ hc)
  obtain ⟨J'₁, hJ'₁⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₁.isLB y
  obtain ⟨J'₂, hJ'₂⟩ := GlobalTheory.UT.CoefBasic.exists_good' A₂.isLB y
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val h₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₂ := GlobalTheory.BoxExpansion.isoRel_val h₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y hJ'₂ hJ₂
  have a₃ := GlobalTheory.BoxExpansion.isoRel_val h₁' (𝟙 _) y hJ'₁ hJ₁
  have a₄ := GlobalTheory.BoxExpansion.isoRel_val h₂' (𝟙 _) y hJ'₁ hJ₁
  have a₅ := crossH_at h (U₁.genF F).left y hJ'₁ hJ'₂
  rw [Category.comp_id, hm] at a₁ a₂
  rw [Category.comp_id, Category.id_comp (U₁.genF F).left] at a₃ a₄
  rw [a₁, a₂, a₃, a₄]
  exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg (_ * ·) a₅).trans (_root_.mul_mul_mul_comm _ _ _ _))

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesUnitSectionRigidificationUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem stalkOf_cpt_bijective (W : Type) [CommRing W] [IsLocalRing W] : Function.Bijective (stalkOf (cpt W)) := by
  have e : stalkOf (cpt W) = (stalkClosedPointIso (.of W)).inv.hom := by
    have h := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of W)
    have h' : (stalkClosedPointIso (.of W)).inv = (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫
        (Sp W).presheaf.germ ⊤ (cpt W) trivial := by
      rw [Iso.eq_inv_comp]; exact h
    rw [h']; rfl
  rw [e]
  exact (stalkClosedPointIso (.of W)).symm.commRingCatIsoToRingEquiv.bijective

theorem exists_unit_stalkOf (W : Type) [CommRing W] [IsLocalRing W] (x : ((Sp W).presheaf.stalk (cpt W))ˣ) :
    ∃ ε : Wˣ, stalkOf (cpt W) (ε : W) = x.val := by
  let e := RingEquiv.ofBijective _ (stalkOf_cpt_bijective W)
  exact ⟨Units.map e.symm.toMonoidHom x, e.apply_symm_apply x.val⟩

theorem gs_scal_section {W : Type} [CommRing W] {Y : Scheme.{0}} (p : Y ⟶ Sp W) (e : Sp W ⟶ Y) (he : e ≫ p = 𝟙 _)
    (z : Sp W) (u : W) : gs e z ⊤ (scal p u) = stalkOf z u := by
  have h := gs_pull e p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom u)
  rw [he] at h
  exact h.trans (gs_eq (𝟙 _) z ⊤ trivial _)

theorem gw_val_indep {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (hw : w.IsGen) {s : Y ⟶ X} {s' : Y' ⟶ X'} (t : LB.Gen (L.pull s)) (ht : t.IsGen) (t' : LB.Gen (L'.pull s'))
    (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y') (e : Z ⟶ X') (he' : r' ≫ s' = e) (he : r ≫ s = e ≫ F) (z : Z)
    {I J : (Z ⟶ X) → L.ι} {I' J' : (Z ⟶ X') → L'.ι} (hI : Good L z I) (hJ : Good L z J) (hI' : Good L' z I')
    (hJ' : Good L' z J') :
    gw w e z (J (e ≫ F)) (J' e) * val t' r' z J' * (val t r z J)⁻¹ =
      gw w e z (I (e ≫ F)) (I' e) * val t' r' z I' * (val t r z I)⁻¹ := by
  have a := (isGen_iff w).1 hw Z e z (J (e ≫ F)) (I (e ≫ F)) (J' e) (I' e) (hJ (e ≫ F)) (hI (e ≫ F)) (hJ' e) (hI' e)
  have b : val t r z J = _ * val t r z I := gen_trans ht r z (hJ.mem _ r) (hI.mem _ r)
  have c : val t' r' z J' = _ * val t' r' z I' := gen_trans ht' r' z (hJ'.mem _ r') (hI'.mem _ r')
  rw [trF, Fintype.prod_unique, zpow_one] at b c
  subst he'
  rw [he] at b
  rw [a, b, c]
  generalize gm ((r' ≫ s') ≫ F) z _ _ = A
  generalize gm (r' ≫ s') z _ _ = B
  rw [mul_inv]
  generalize gw w _ _ _ _ = C
  generalize val t' r' z I' = D
  generalize (val t r z I)⁻¹ = E
  have : A * B⁻¹ * C * (B * D) * (A⁻¹ * E) = (A * A⁻¹) * (B * B⁻¹) * (C * D * E) := by ac_rfl
  rw [this]; simp

theorem Trait.carries_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W) (σ' : H0 T.U.LG.L k) (σ : SecK C.P.L.L T.β k), T.Carries u σ' σ → ∃ ε : Wˣ, ∀ J J', Good C.P.L.L (cpt W) J → Good T.U.LG.L (cpt W) J' → sval σ (unitW T.G) (cpt W) J * (val T.U.LG.rig (idW W) (cpt W) J').val ^ k = stalkOf (cpt W) (u * ε) * sval σ' (unitW T.G) (cpt W) J' * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ D C W _ _ _ T k u σ' σ h
  obtain ⟨I, hI, -⟩ := exists_good C.P.L.L C.P.L.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨I', hI', -⟩ := exists_good T.U.LG.L T.U.LG.isLB (cpt W) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have he : T.ξ ≫ eSec C.G = unitW T.G ≫ T.β := (PullGtPf.IsGrpPullback.one_left T.cart).symm
  obtain ⟨ε, hε⟩ := exists_unit_stalkOf W ((gw T.ℓ (unitW T.G) (cpt W) (I (unitW T.G ≫ T.β)) (I' (unitW T.G)) *
    val T.U.LG.rig (idW W) (cpt W) I' * (val C.P.L.rig T.ξ (cpt W) I)⁻¹) ^ k)
  refine ⟨ε, fun J J' hJ hJ' => ?_⟩
  have key := gw_val_indep T.ℓ T.ℓ_gen C.P.L.rig C.P.L.rigGen T.U.LG.rig T.U.LG.rigGen T.ξ (idW W) (unitW T.G)
    (Category.id_comp _) he (cpt W) hI hJ hI' hJ'
  rw [← key] at hε
  rw [h _ (unitW T.G) (cpt W) J J' hJ hJ', gs_scal_section T.G.hom (unitW T.G) (Over.w η[T.G]), map_mul, hε]
  generalize gw T.ℓ _ _ _ _ = A
  generalize val T.U.LG.rig _ _ _ = B
  generalize val C.P.L.rig _ _ _ = E
  have : (A * B * E⁻¹) ^ k * E ^ k = A ^ k * B ^ k := by rw [← mul_pow, ← mul_pow, inv_mul_cancel_right]
  have := congrArg Units.val this
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  linear_combination (-(stalkOf (cpt W) u * sval σ' (unitW T.G) (cpt W) J')) * this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianSchemeStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A), tanVal (a * b) f = tanVal a f + tanVal b f := by
  first | exact @GlobalTheory.TanAdd.tanVal_mul_all | exact GlobalTheory.TanAdd.tanVal_mul_all | (intros; apply GlobalTheory.TanAdd.tanVal_mul_all <;> assumption)
end

