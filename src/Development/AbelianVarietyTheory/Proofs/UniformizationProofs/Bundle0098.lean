module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyQuasiFiniteOfFiniteStabiliser
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteStabiliser

theorem apply_eq_of_range_subset_affine {K : Type} [Field K] {F Z : Scheme.{0}} [IsIntegral F]
    (q : F ⟶ Spec (.of K)) [UniversallyClosed q] (h : F ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (hh : ∀ a, h a ∈ W) (a b : F) : h a = h b := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hh c
  have : IsAffine W := hW
  let l := IsOpenImmersion.lift W.ι h hr
  have e : l ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  have e' : l = F.toSpecΓ ≫ Spec.map l.appTop ≫ W.toScheme.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  letI := (isField_of_universallyClosed K q).toField
  have hab : F.toSpecΓ a = F.toSpecΓ b :=
    Subsingleton.elim (α := PrimeSpectrum Γ(F, ⊤)) _ _
  rw [← e, e']
  simp only [Scheme.Hom.comp_apply, hab]

theorem slice_eq {K : Type} [Field K] [IsAlgClosed K] {F B Z : Over (Spec (CommRingCat.of K))}
    [IsIntegral F.left] [UniversallyClosed F.hom] [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (g : F ⊗ B ⟶ Z) (b : 𝟙_ _ ⟶ B) (z : Z.left)
    (hz : ∀ a, (lift (𝟙 F) (toUnit F ≫ b) ≫ g).left a = z) (f f' : 𝟙_ _ ⟶ F) :
    lift (toUnit B ≫ f) (𝟙 B) ≫ g = lift (toUnit B ≫ f') (𝟙 B) ≫ g := by
  have huc : UniversallyClosed (snd F B).left := by
    change UniversallyClosed (pullback.snd F.hom B.hom); infer_instance
  let j : (𝟙_ _ ⟶ B) → (F ⟶ F ⊗ B) := fun x ↦ lift (𝟙 F) (toUnit F ≫ x)
  have hpb (x : 𝟙_ _ ⟶ B) : IsPullback (j x).left F.hom (snd F B).left x.left := by
    have hw : x.left ≫ B.hom = 𝟙 _ := Over.w x
    have hr : IsPullback (fst F B).left (snd F B).left F.hom B.hom := .of_hasPullback F.hom B.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : (j x).left ≫ (fst F B).left = 𝟙 F.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hcl : IsClosed ((snd F B).left '' ((g.left ⁻¹ᵁ W : (F ⊗ B).left.Opens) : Set _)ᶜ) :=
    (snd F B).left.isClosedMap _ (g.left ⁻¹ᵁ W).isOpen.isClosed_compl
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hlft : LocallyOfFiniteType ((lift (toUnit B ≫ f) (𝟙 B) ≫ g).left ≫ Z.hom) := by
    rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Z.hom _ hcl.isOpen_compl.isLocallyClosed
    (hcl.isOpen_compl.dense ⟨b.left pt, ?_⟩) (fun x hxV hx ↦ ?_) (by rw [Over.w, Over.w]))
  · rintro ⟨w, hw, hwb⟩
    obtain ⟨a, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hpb b) w pt hwb
    apply hw
    change g.left ((j b).left a) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hz]
    exact hzW
  · let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
      Over.homMk (pointOfClosedPoint (K := K) B.hom x hx)
        (pointOfClosedPoint_comp (K := K) B.hom x hx)
    have hp (s) : p.left s = x := pointOfClosedPoint_apply (K := K) B.hom x hx s
    have hin (a : F.left) : (j p ≫ g).left a ∈ W := by
      by_contra hn
      refine hxV ⟨(j p).left a, ?_, ?_⟩
      · rw [Over.comp_left, Scheme.Hom.comp_apply] at hn
        exact hn
      · rw [← Scheme.Hom.comp_apply, (hpb p).w, Scheme.Hom.comp_apply, hp]
    have key (u : 𝟙_ _ ⟶ F) :
        (lift (toUnit B ≫ u) (𝟙 B) ≫ g).left x = (j p ≫ g).left (u.left pt) := by
      have e : p ≫ lift (toUnit B ≫ u) (𝟙 B) ≫ g = u ≫ j p ≫ g := by
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext1
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
      rw [← hp pt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        ← Over.comp_left, e]
    rw [key, key]
    exact apply_eq_of_range_subset_affine (K := K) F.hom _ hW hin _ _

theorem finite_closedPoints_of_contracted {K : Type} [Field K] [IsAlgClosed K]
    {B Z : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsIntegral B.left] [IsProper B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z)
    (hφ : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite)
    (S : TopologicalSpace.Closeds B.left) (hS : IsIrreducible (S : Set B.left)) (z : Z.left)
    (hz : ∀ y ∈ S, φ.left y = z) : ((S : Set B.left) ∩ closedPoints B.left).Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let F : Over (Spec (CommRingCat.of K)) := Over.mk (I.subschemeι ≫ B.hom)
  let i : F ⟶ B := Over.homMk I.subschemeι rfl
  have hemb := I.subschemeι.isClosedEmbedding
  have : IsReduced F.left := ReducedSubgroup.isReduced_subscheme_vanishingIdeal S
  have : IrreducibleSpace F.left := by
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hrange]; exact Subtype.irreducibleSpace hS
    exact hemb.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  have : IsIntegral F.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper F.hom := by change IsProper (I.subschemeι ≫ B.hom); infer_instance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : B.left) (hy : y ∈ (S : Set B.left) ∩ closedPoints B.left) :
      ∃ u : 𝟙_ _ ⟶ F, (u ≫ i).left pt = y := by
    obtain ⟨a, rfl⟩ : y ∈ Set.range I.subschemeι := hrange ▸ hy.1
    have ha : IsClosed ({a} : Set F.left) := by
      refine hemb.isClosed_iff_image_isClosed.mpr ?_
      rw [Set.image_singleton]
      exact hy.2
    refine ⟨Over.homMk (pointOfClosedPoint (K := K) F.hom a ha)
      (pointOfClosedPoint_comp (K := K) F.hom a ha), ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg I.subschemeι (pointOfClosedPoint_apply (K := K) F.hom a ha pt)
  rcases ((S : Set B.left) ∩ closedPoints B.left).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨u₀, -⟩ := hpt y₀ hy₀
  refine (hφ.image fun s ↦ (s * (u₀ ≫ i)).left pt).subset fun y hy ↦ ?_
  obtain ⟨u, rfl⟩ := hpt y hy
  refine ⟨(u ≫ i) * (u₀ ≫ i)⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩
  have key := slice_eq (((fst F B ≫ i) * snd F B) ≫ φ) (1 : 𝟙_ _ ⟶ B) z (fun a ↦ by
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one,
      _root_.mul_one, Category.id_comp, Over.comp_left, Scheme.Hom.comp_apply]
    exact hz _ (hrange.le ⟨a, rfl⟩)) u u₀
  have key' := congrArg (fun t ↦ ((toUnit B ≫ u₀ ≫ i)⁻¹ * 𝟙 B) ≫ t) key
  have hu (t : B ⟶ B) : t ≫ toUnit B = toUnit B := toUnit_unique _ _
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, hu, Category.comp_id,
    mul_inv_cancel_left, Category.id_comp] at key'
  change (toUnit B ≫ ((u ≫ i) * (u₀ ≫ i)⁻¹) * 𝟙 B) ≫ φ = φ
  simp only [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc, ← Category.assoc]
  exact key'

theorem locallyQuasiFinite_of_finite_stabiliser :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z), {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite → LocallyQuasiFinite φ.left := by
  intro K _ _ B _ _ hB Z _ _ φ hφ
  have := hB.proper
  have := hB.smooth
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsProper (φ.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsProper φ.left := .of_comp _ Z.hom
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : IsNoetherian B.left := {}
  refine locallyQuasiFinite_of_finite_fibres_closedPoints φ.left fun y hy ↦ ?_
  have hc : IsClosed (φ.left ⁻¹' {φ.left y}) := by
    refine IsClosed.preimage φ.left.continuous ?_
    simpa using φ.left.isClosedMap _ hy
  refine finite_of_isClosed_of_finite_inter_closedPoints hc ?_
  obtain ⟨T, hT, hTc, hTi, hTU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hc
  rw [hTU, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]
  refine hT.biUnion fun S hS ↦ ?_
  refine finite_closedPoints_of_contracted φ hφ ⟨S, hTc S hS⟩ (hTi S hS) (φ.left y) fun w hw ↦ ?_
  exact hTU.ge ⟨S, hS, hw⟩

end GlobalTheory.FiniteStabiliser
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKLIffMemKLPush
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem memKL_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} (x : T' ⟶ A') (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst T' A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T' A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T' A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

end

theorem memKL_iff_memKL_push : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) (A' : Over S') [GrpObj A] [GrpObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left) (L' : LB A'.left) (h : IsGrpPullback A' A f φ), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (T' : Over S') (x : T' ⟶ A'), GlobalTheory.MemKL A' L' x ↔ GlobalTheory.MemKL A L (pushPt h.1.w x) :=
  fun _ _ _ _ _ _ _ _ _ _ h hL hL' hw _ x => ⟨memKL_push h hL hL' hw x, memKL_of_push h hL hL' hw x⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SquareOfCubical
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Square

section General
variable {X Y : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

private theorem map_zpow_zpow {M N : Type} [Group M] [Group N] (F : M →* N) (x : M) (n e : ℤ) :
    F (x ^ n) ^ e = F x ^ (n * e) := by
  rw [map_zpow, ← zpow_mul]

theorem linComb_pw (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℤ) :
    LB.LinComb (pw L n) φ ε = LB.LinComb L φ (fun k => n * ε k) := by
  unfold LB.LinComb GlobalTheory.AbLaw.pw
  congr 1
  funext j j'
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact map_zpow_zpow _ _ _ _

private theorem sameSum_of_prod_pow_eq' {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U), ∏ k, f (φ₁ k) ^ ε₁ k = ∏ k, f (φ₂ k) ^ ε₂ k) :
    LB.SameSum φ₁ ε₁ φ₂ ε₂ := by
  classical
  intro ψ
  have e := congrArg Multiplicative.toAdd
    (h (Multiplicative ℤ) (fun χ => Multiplicative.ofAdd (if χ = ψ then (1 : ℤ) else 0)))
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_ite, mul_zero] at e
  convert e <;> simp

theorem triv_mul (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (h₁ : Triv (LB.LinComb L φ ε)) (h₂ : Triv (LB.LinComb L φ' ε'))
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (φ k) ^ ε k) * ∏ k, f (φ' k) ^ ε' k = ∏ k, f (φ'' k) ^ ε'' k) : Triv (LB.LinComb L φ'' ε'') := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have hs : LB.SameSum (Sum.elim φ φ') (Sum.elim ε ε') φ'' ε'' := sameSum_of_prod_pow_eq' fun U _ f => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact h U f
  obtain ⟨t, ht, -⟩ := DVR.gen_transport hL hs (LB.mulGen L φ ε φ' ε' t₁ t₂)
    (DVR.mulGen_isGen L φ ε φ' ε' t₁ t₂ ht₁ ht₂)
  exact ⟨t, ht⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B}
  {A : Type} [CommRing A] [IsLocalRing A] {t : Spec (CommRingCat.of A) ⟶ S}


omit [IsCommMonObj B] in
theorem triv_const {K : Type} [Fintype K] (x : K → (Over.mk t ⟶ B)) (ε : K → ℤ) :
    Triv (LB.LinComb L.L (fun k => (fst (Over.mk t) B ≫ x k).left) ε) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := A) L.L L.isLB (fun k => (x k).left) ε
  exact ⟨LB.pullGen L.L (fun k => (x k).left) ε e (fst (Over.mk t) B).left,
    DVR.pullGen_isGen L.L _ ε e he _⟩

private theorem translPt_eq_fst_comp_mul_snd {T : Over S} (w : T ⟶ B) : translPt B w = (fst T B ≫ w) * snd T B := by
  unfold translPt
  rw [Hom.mul_def]

private theorem over_comp_mul {T T' : Over S} (f : T' ⟶ T) (g h : T ⟶ B) : f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem over_comp_one {T T' : Over S} (f : T' ⟶ T) : f ≫ (1 : T ⟶ B) = 1 := by
  simp [Hom.one_def]

theorem triv_square (c : CubicalStr B L) (x y : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left,
      (translPt B y).left] ![1, 1, -1, -1]) := by
  have h₁ : Triv (LB.LinComb L.L (fun k => (lift (fst (Over.mk t) B ≫ x)
      (lift (fst (Over.mk t) B ≫ y) (snd (Over.mk t) B))).left ≫ thφ B (x3 B) k) thε) :=
    ⟨LB.pullGen L.L (thφ B (x3 B)) thε c.t _, DVR.pullGen_isGen L.L _ _ c.t c.isGen _⟩
  have h₂ := triv_const (L := L) (t := t) (K := Fin 4) ![x * y, x, y, 1] ![1, -1, -1, 1]
  refine triv_mul L.isLB h₁ h₂ fun U _ f => ?_
  rw [Geo.Tor.prod_cub]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zpow_one, zpow_neg]
  simp only [translPt_eq_fst_comp_mul_snd, over_comp_mul, over_comp_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem triv_pow (c : CubicalStr B L) (r : ℕ) (x : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 3) ![(translPt B (x ^ r)).left, (translPt B x).left, (snd (Over.mk t) B).left]
      ![1, -r, r - 1]) := by
  induction r with
  | zero =>
    have h₀ := triv_const (L := L) (t := t) (K := Fin 0) ![] ![]
    refine triv_mul L.isLB h₀ h₀ fun U _ f => ?_
    rw [pow_zero, translPt_eq_fst_comp_mul_snd, over_comp_one, _root_.one_mul]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    push_cast
    module
  | succ r ih =>
    have hs := triv_square c (x ^ r) x
    refine triv_mul L.isLB hs ih fun U _ f => ?_
    rw [pow_succ]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    push_cast
    module

theorem square_of_cubical : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (L : RigLB B) (_ : CubicalStr B L) (A : Type) [CommRing A] [IsLocalRing A] (t : Spec (CommRingCat.of A) ⟶ S), (∀ x y : Over.mk t ⟶ B, Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left, (translPt B y).left] ![1, 1, -1, -1])) ∧ ∀ (r : ℕ) (x : Over.mk t ⟶ B), Triv (translDiff B (pw L.L r) x) ↔ Triv (translDiff B L.L (x ^ r)) := by
  intro S B _ _ L c A _ _ t
  refine ⟨fun x y => triv_square c x y, fun r x => ?_⟩
  have hP := triv_pow c r x
  unfold translDiff
  rw [linComb_pw]
  simp only [← Hom.mul_def]
  simp only [translPt_eq_fst_comp_mul_snd] at hP
  constructor
  · intro h
    refine triv_mul L.isLB h hP fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · intro h
    refine triv_mul L.isLB h (triv_inv hP) fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module

end GlobalTheory.Square
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

open TopologicalSpace GlobalTheory.AmpleLocal

theorem gs_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (D : X.Opens) (c : R)
    (z : X) (hz : z ∈ D) : gs (𝟙 X) z D (AbLaw.cst f D c) = gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ c) := by
  rw [← rs_cst f (le_top : D ≤ ⊤) c]
  exact gs_res (𝟙 X) z le_top hz _

theorem veryAmpleBy_pw : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X)
    (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, 1 ≤ d →
    ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s' := by
  intro R _ X f H n s hH ⟨cov, hs⟩ d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  choose aff r hr surj using hs
  choose c hc using fun z : X => exists_chart hH z
  let G : H.ι → Fn X := fun i z => (gm (𝟙 X) z _ (H.g i (c z))).val
  let φ : R → Fn X := fun a z => gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ a)
  have hU : ∀ z, ∃ i, z ∈ H.U i := fun z => ⟨c z, hc z⟩
  have hG : ∀ i z, IsUnit (G i z) := fun _ _ => Units.isUnit _
  let σ : Fin (n + 1) → Fn X := fun i => sv c (s i)
  have hσ : ∀ i, Sc H.U G ⊤ 1 (σ i) := fun i =>
    sc_sv (P := H) (κ := id) (fun _ => le_rfl) hc (fun _ _ _ => (pow_one _).symm) (s i)
  have gen : ∀ i, Gen (nonzeroLocus (s i)) (Set.range φ ∪ Set.range fun m => σ m * AmpleLocal.inv (σ i)) := fun i =>
    (gen_iff _ (r i) _ _ (fun a z hz => gs_cst f _ a z hz)
      (fun m => (ratio_iff hc (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := Fin (n + 1) × Fin (n + 1))).ne'
  let ε := Fintype.equivFinOfCardEq hM
  let τ : Fin (M + 1) → Fn X := fun m => σ (ε.symm m).2 * σ (ε.symm m).1 ^ e
  have hτ : ∀ m, Sc H.U G ⊤ (1 * (e + 1)) (τ m) := fun m => by
    rw [mul_add, _root_.mul_one, add_comm]
    exact (hσ _).mul ((hσ _).pow _)
  have hγ : ∀ y, y ∈ (pw H ((e + 1 : ℕ) : ℤ)).U (c y) := hc
  choose t ht using fun m => exists_sv (P := pw H ((e + 1 : ℕ) : ℤ)) (κ := id) (N := 1 * (e + 1)) (G := G)
    (fun _ => le_rfl) hc (fun i y _ => by
      show (gm (𝟙 X) y _ (H.g i (c y) ^ ((e + 1 : ℕ) : ℤ))).val = _
      rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val, _root_.one_mul]) (isLB_pw hH _) (hτ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (t m)) ⊤ (τ m) := fun m => ht m ▸ loc_sv hγ (t m)
  have main := fun m => extra_section hU hG hσ (fun i => loc_sv hc (s i))
    (fun z _ => Opens.mem_iSup.1 (cov.ge trivial)) aff (S₀ := Set.range φ)
    (by rintro _ ⟨a, rfl⟩; exact mem_reg_iff.2 ⟨_, fun _ _ => rfl⟩) gen (hτ m) (loc m)
  refine ⟨M, t, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i).1, ?_⟩⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (cov.ge (Set.mem_univ z))
    have hu : IsUnit (σ j z) := (loc_sv hc (s j)).unit hj
    refine Opens.mem_iSup.2 ⟨ε (j, j), (loc _ z).2 ⟨trivial, ?_⟩⟩
    simp only [τ, Equiv.symm_apply_apply]
    exact hu.mul (hu.pow e)
  · choose ρ hρ using fun m => mem_reg_iff.1 (Sc.ratio hU hG (hτ m) (hτ i) (loc i))
    refine ⟨ρ, fun m => (ratio_iff hγ (t i) (t m) (ρ m)).2 ?_, ?_⟩
    · have e₁ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t i) = τ i := ht i
      have e₂ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t m) = τ m := ht m
      rw [e₁, e₂]
      exact hρ m
    · refine (gen_iff _ ρ φ _ (fun a z hz => gs_cst f _ a z hz) hρ).1 ((main i).2.mono ?_)
      rintro x (hx | ⟨p, rfl⟩)
      · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
      · refine ⟨_, Subring.subset_closure (Or.inr ⟨ε p, ?_⟩), fun _ _ => rfl⟩
        simp only [τ, Equiv.symm_apply_apply]

end GlobalTheory.AbLaw
end

