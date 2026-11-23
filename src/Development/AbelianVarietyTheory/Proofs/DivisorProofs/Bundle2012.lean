module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.RigRescale

variable {X Y : Scheme.{0}}

theorem germ_id_pull (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by
  rw [gm_pull (𝟙 Y) f y U h a, Category.id_comp]

theorem germ_pull_g (L : LB X) (f : Y ⟶ X) (y : Y) (P P' : PUnit → L.ι)
    (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') ((L.pull f).g P P') =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (L.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) ⟨hp, hp'⟩ _)

theorem germ_linCombIso {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) (y : Y) (P : PUnit → M.ι)
    (Q : PUnit → L.ι) (hp : f y ∈ M.U (P PUnit.unit)) (hq : f y ∈ L.U (Q PUnit.unit)) :
    gm (𝟙 Y) y ((M.pull f).U P ⊓ (L.pull f).U Q)
        ((LB.linCombIso w (K := PUnit) (fun _ => f) (fun _ => 1)).s (P, Q)) =
      gm f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit)) (w.s (P PUnit.unit, Q PUnit.unit)) := by
  have hm : y ∈ (M.pull f).U P ⊓ (L.pull f).U Q := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (w.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (show f y ∈ M.U (P PUnit.unit) ⊓ L.U (Q PUnit.unit) from ⟨hp, hq⟩) _)

theorem germ_iso_isGen {L M : LB X} (w : LB.Iso L M) (hw : w.IsGen) (f : Y ⟶ X) (y : Y)
    (p p' : M.ι) (q q' : L.ι) (hp : f y ∈ M.U p) (hp' : f y ∈ M.U p') (hq : f y ∈ L.U q)
    (hq' : f y ∈ L.U q') :
    gm f y ((LB.div M L).U (p, q)) (w.s (p, q)) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ *
        gm f y ((LB.div M L).U (p', q')) (w.s (p', q')) := by
  have hm : f y ∈ M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') := ⟨⟨hp, hq⟩, hp', hq'⟩
  have h := (congrArg (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) (hw (p, q) (p', q'))).trans
    (map_mul (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) ((LB.div M L).g (p, q) (p', q'))
      (res inf_le_right (w.s (p', q'))))
  have hg : gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) ((LB.div M L).g (p, q) (p', q')) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ := by
    show gm f y _ (res _ (M.g p p') * (res _ (L.g q q'))⁻¹) = _
    rw [map_mul, map_inv]
    exact congrArg₂ (· * ·) (gm_res f y _ hm _) (congrArg _ (gm_res f y _ hm _))
  calc gm f y ((LB.div M L).U (p, q)) (w.s (p, q))
      = gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) (res inf_le_left (w.s (p, q))) :=
        (gm_res f y _ hm _).symm
    _ = _ := h
    _ = _ := congrArg₂ (· * ·) hg (gm_res f y _ hm _)

theorem germ_gen_isGen (L : LB X) (f : Y ⟶ X) (t : LB.Gen (L.pull f)) (ht : t.IsGen) (y : Y)
    (P P' : PUnit → L.ι) (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P) (t.s P) =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) *
        gm (𝟙 Y) y ((L.pull f).U P') (t.s P') := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  have h := congrArg (gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P')) (ht P P')
  rw [map_mul] at h
  calc gm (𝟙 Y) y ((L.pull f).U P) (t.s P)
      = gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') (res inf_le_left (t.s P)) :=
        (gm_res (𝟙 Y) y _ hm _).symm
    _ = _ := h
    _ = _ := by rw [germ_pull_g L f y P P' hp hp']; exact congrArg _ (gm_res (𝟙 Y) y _ hm _)

theorem alg₁ {M : Type*} [CommGroup M] (a b E A B : M) :
    a * A * (a * b⁻¹ * E * (b * B))⁻¹ = A * (E * B)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg₂ {M : Type*} [CommGroup M] (A E B : M) : A = E * (A * (E * B)⁻¹) * B := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem proj_comp : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G],
    eSec G ≫ (toUnit G).left = 𝟙 (𝟙_ (Over S)).left := by
  intro S G _
  show (η[G] ≫ toUnit G).left = 𝟙 _
  rw [toUnit_unique (η[G] ≫ toUnit G) (𝟙 _)]
  rfl

theorem exists_isGen_maps_rig {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
    (L₁ L₂ : RigLB G) (e : LB.Iso L₁.L L₂.L) (he : e.IsGen) : ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  let W : (PUnit → L₂.L.ι) × (PUnit → L₁.L.ι) → (𝟙_ (Over S)).left.Opens :=
    fun i => (L₂.L.pull (eSec G)).U i.1 ⊓ (L₁.L.pull (eSec G)).U i.2
  let u : ∀ i, Γ((𝟙_ (Over S)).left, W i)ˣ := fun i =>
    res inf_le_left (L₂.rig.s i.1) *
      ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s i *
        res inf_le_right (L₁.rig.s i.2))⁻¹
  have key : ∀ i, ∀ x ∈ W i, gm (𝟙 _) x (W i) (u i) =
      gm (𝟙 _) x ((L₂.L.pull (eSec G)).U i.1) (L₂.rig.s i.1) *
        (gm (eSec G) x ((LB.div L₂.L L₁.L).U (i.1 PUnit.unit, i.2 PUnit.unit))
            (e.s (i.1 PUnit.unit, i.2 PUnit.unit)) *
          gm (𝟙 _) x ((L₁.L.pull (eSec G)).U i.2) (L₁.rig.s i.2))⁻¹ := by
    intro i x hx
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) x _ hx _)
      ((map_inv _ _).trans (congrArg _ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (germ_linCombIso e (eSec G) x i.1 i.2 (mem_pull.1 hx.1) (mem_pull.1 hx.2))
        (gm_res (𝟙 _) x _ hx _))))))
  obtain ⟨c, hc⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨p, hp⟩ := exists_chart L₂.isLB ((eSec G) x)
      obtain ⟨q, hq⟩ := exists_chart L₁.isLB ((eSec G) x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => p, fun _ => q), mem_pull.2 hp, mem_pull.2 hq⟩) u
    (fun i j x hx => by
      rw [key i x hx.1, key j x hx.2,
        germ_gen_isGen L₂.L (eSec G) L₂.rig L₂.rigGen x i.1 j.1 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1),
        germ_gen_isGen L₁.L (eSec G) L₁.rig L₁.rigGen x i.2 j.2 (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2),
        germ_iso_isGen e he (eSec G) x _ (j.1 PUnit.unit) _ (j.2 PUnit.unit) (mem_pull.1 hx.1.1)
          (mem_pull.1 hx.2.1) (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)]
      exact alg₁ _ _ _ _ _)
  let C := pullU (toUnit G).left ⊤ c
  let e' : LB.Iso L₁.L L₂.L := ⟨fun i => e.s i * res (U := (toUnit G).left ⁻¹ᵁ ⊤) (fun _ _ => trivial) C⟩
  have hC : ∀ i, ∀ x ∈ (LB.div L₂.L L₁.L).U i,
      gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e'.s i) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e.s i) * gm (𝟙 _) x ((toUnit G).left ⁻¹ᵁ ⊤) C :=
    fun i x hx => (map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 _) x _ hx _))
  refine ⟨e', ?_, ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    apply unit_ext
    intro x hx
    have hE : gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q)) (e.s (p, q)) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q) ⊓ (LB.div L₂.L L₁.L).U (p', q'))
            ((LB.div L₂.L L₁.L).g (p, q) (p', q')) *
          gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p', q')) (e.s (p', q')) :=
      (gm_res (𝟙 _) x _ hx _).symm.trans (((congrArg (gm (𝟙 _) x _) (he (p, q) (p', q'))).trans
        (map_mul _ _ _)).trans (congrArg _ (gm_res (𝟙 _) x _ hx _)))
    exact (gm_res (𝟙 _) x _ hx _).trans ((hC _ x hx.1).trans ((congrArg (· * _) hE).trans
      ((mul_assoc _ _ _).trans ((congrArg _ ((hC _ x hx.2).symm.trans
        (gm_res (𝟙 _) x _ hx _).symm)).trans (map_mul _ _ _).symm))))
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hx₁ := mem_pull.1 hx.1
    have hx₂ := mem_pull.1 hx.2
    have hcx : gm (𝟙 _) x ⊤ c = gm (𝟙 _) x (W (P, Q)) (u (P, Q)) := by
      rw [← hc (P, Q)]; exact (gm_res (𝟙 _) x _ hx _).symm
    have hσ : gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
        (e'.s (P PUnit.unit, Q PUnit.unit)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
          (e.s (P PUnit.unit, Q PUnit.unit)) * gm (𝟙 _) x ⊤ c := by
      refine (map_mul _ _ _).trans (congrArg _ ?_)
      refine (gm_res (eSec G) x _ (show (eSec G) x ∈ L₂.L.U _ ⊓ L₁.L.U _ from ⟨hx₁, hx₂⟩) _).trans ?_
      refine (gm_pull (eSec G) (toUnit G).left x ⊤ trivial c).trans ?_
      rw [proj_comp]
    have hEq : gm (𝟙 _) x (W (P, Q))
        ((LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
            (e.s (P PUnit.unit, Q PUnit.unit)) *
          (gm (𝟙 _) x ((L₂.L.pull (eSec G)).U P) (L₂.rig.s P) *
            (gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
                (e.s (P PUnit.unit, Q PUnit.unit)) *
              gm (𝟙 _) x ((L₁.L.pull (eSec G)).U Q) (L₁.rig.s Q))⁻¹) := by
      rw [germ_linCombIso e' (eSec G) x P Q hx₁ hx₂, hσ, hcx, key (P, Q) x hx]
    exact (gm_res (𝟙 _) x _ hx _).trans ((alg₂ _ _ _).trans
      ((congrArg₂ (· * ·) hEq.symm (gm_res (𝟙 _) x _ hx _).symm).trans (map_mul _ _ _).symm))

end GlobalTheory.RigRescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.SiegLev GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegSharpCover

theorem smoothDim {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) (hu : IsUnit (k : o)) : SmoothOfRelativeDimension h c.A.hom := by
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ S := spMap (algebraMap κ K) ≫ S.fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast (Spec.preimage (x ≫ s)).hom k
    rw [← this]
    exact (hu.map _).ne_zero
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (SiegDim.dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegSharpCover

namespace GlobalTheory.SiegSharpCover

end GlobalTheory.SiegSharpCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectDeeperLevelOfSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp GlobalTheory.SiegLevCalc

section Sec

variable {S V : Scheme.{0}} {A : Over S} {A' : Over V} [GrpObj A] [GrpObj A'] {π : V ⟶ S} {φ : A'.left ⟶ A.left}

def secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : 𝟙_ (Over V) ⟶ A' :=
  Over.homMk (hp.1.lift x.left (𝟙 V) ((Over.w x).trans (Category.id_comp π).symm)) (hp.1.lift_snd _ _ _)

theorem secOf_left (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) : (secOf hp x).left ≫ φ = x.left :=
  hp.1.lift_fst _ _ _

theorem push_secOf (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (T : Over V) :
    pushHom hp T (toUnit T ≫ secOf hp x) = (Over.homMk T.hom rfl : Over.mk (T.hom ≫ π) ⟶ Over.mk π) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secOf hp x).left) ≫ φ = T.hom ≫ x.left
  rw [Category.assoc, secOf_left, Over.toUnit_left]

theorem push_secOf' (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) :
    pushHom hp _ (secOf hp x) =
      (Over.homMk (𝟙_ (Over V)).hom rfl : Over.mk ((𝟙_ (Over V)).hom ≫ π) ⟶ Over.mk π) ≫ x := by
  have e := push_secOf hp x (𝟙_ (Over V))
  rwa [toUnit_unit, Category.id_comp] at e

theorem secOf_mul (hp : IsGrpPullback A' A π φ) (x y : Over.mk π ⟶ A) :
    secOf hp (x * y) = secOf hp x * secOf hp y :=
  push_injective hp _ (by rw [map_mul, push_secOf', push_secOf', push_secOf', MonObj.comp_mul])

theorem secOf_pow (hp : IsGrpPullback A' A π φ) (x : Over.mk π ⟶ A) (k : ℕ) :
    secOf hp (x ^ k) = secOf hp x ^ k :=
  push_injective hp _ (by rw [map_pow, push_secOf', push_secOf', MonObj.comp_pow])

theorem secOf_one (hp : IsGrpPullback A' A π φ) : secOf hp (1 : Over.mk π ⟶ A) = 1 :=
  push_injective hp _ (by rw [map_one, push_secOf', MonObj.comp_one])

end Sec

section Rel

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem comp_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {ψ : c''.A.left ⟶ c'.A.left}
    {ψ₂ : (G2 c''.A).left ⟶ (G2 c'.A).left} (hψ : IsGrpPullback c''.A c'.A f' ψ) (hs' : IsSquare ψ ψ₂)
    (hw' : LBIso c''.P (c'.P.pull ψ₂)) :
    IsGrpPullback c''.A c.A (f' ≫ f) (ψ ≫ φ) ∧
      ∃ χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left, IsSquare (ψ ≫ φ) χ₂ ∧ LBIso c''.P (c.P.pull χ₂) := by
  refine ⟨hψ.comp hφ, ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)

theorem cancel_with {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hφ : IsGrpPullback c'.A c.A f φ)
    (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) {χ : c''.A.left ⟶ c.A.left}
    {χ₂ : (G2 c''.A).left ⟶ (G2 c.A).left} (hχ : IsGrpPullback c''.A c.A (f' ≫ f) χ) (hs' : IsSquare χ χ₂)
    (hw' : LBIso c''.P (c.P.pull χ₂)) (hl : ∀ a, (c''.lev a).left ≫ χ = f' ≫ (c'.lev a).left ≫ φ) :
    SiegPB c'' c' f' := by
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, hl a, Category.assoc]
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

end Rel

section Cover

variable {h n N : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {S V : Scheme.{0}} {s : S ⟶ Sp B}

def pair (c : SiegPre h n ζ s) (π : V ⟶ S) : ReciprocityTheory.ChartRestriction.G.Pdiv.SiegPairPB c π :=
  Classical.choice (siegPairPB_nonempty c π)

def cover (c : SiegPre h n ζ s) (sV : V ⟶ Sp B') (ζ' : B') (π : V ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A))
    (hadd : ∀ a a', e (a + a') = e a * e a') (htor : ∀ a, e a ^ N = 1)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) :
    SiegPre h N ζ' sV where
  A := (pair c π).A
  ab := (pair c π).ab
  P := (pair c π).P
  isLB := (pair c π).isLB
  rig₁ := (pair c π).rig₁
  rig₂ := (pair c π).rig₂
  symm := (pair c π).symm
  lev a := secOf (pair c π).pb (e a)
  lev_add a b := by rw [hadd, secOf_mul]
  lev_tors a := by rw [← secOf_pow, htor, secOf_one]
  geom k _ _ x β z hx hz := by
    obtain ⟨g₁, g₂, g₃⟩ := hgeom k x β z hx hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective (pair c π).pb (Over.mk x)).eq_iff, push_secOf, map_one]
      try rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom (pair c π).pb (Over.mk x) g) (by
        have := congrArg (pushHom (pair c π).pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective (pair c π).pb _ ((push_secOf _ _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S V c.A (pair c π).A π (pair c π).φ _ _ (pull_isLB c.isLB _)
        (pull_isLB (pair c π).isLB _) (pair c π).pb (diag_iso (pair c π).sq (pair c π).iso) (Over.mk x) N _ _ _ _ _
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secOf (pair c π).pb (e b) (Over.mk x)).symm)).2 (g₃ a b)

end Cover

end GlobalTheory.SiegCover

namespace GlobalTheory

open SiegCover SiegLevCalc

theorem siegCover_build : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := by
  intro h n N d B B' _ _ ζ ζ' S V s sV π c e hadd htor hd hgeom
  have levd : ∀ a, ((cover c sV ζ' π e hadd htor hgeom).lev a ^ d).left ≫ (pair c π).φ = π ≫ (c.lev a ^ 1).left := by
    intro a
    show (secOf (pair c π).pb (e a) ^ d).left ≫ _ = _
    rw [← secOf_pow, secOf_left, hd a, pow_one, Over.comp_left, Over.toUnit_left]
    try rfl
  refine ⟨cover c sV ζ' π e hadd htor hgeom, (pair c π).φ,
    ⟨(pair c π).pb, ⟨(pair c π).φ₂, (pair c π).sq, (pair c π).iso⟩, levd⟩, fun a => secOf_left (pair c π).pb (e a), ?_⟩
  intro T t B'' _ ζ'' sT C'
  constructor
  · rintro ⟨ψ, ψ₂, hψ, hs', hw', hl'⟩
    obtain ⟨hc, χ₂, hsq, hiso⟩ := comp_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq
      (pair c π).iso hψ hs' hw'
    refine ⟨ψ ≫ (pair c π).φ, ⟨hc, ⟨χ₂, hsq, hiso⟩, fun a => ?_⟩, fun a => ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (pow_section hψ _ _ (hl' a) d)).trans
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (levd a)).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (pair c π).φ) (hl' a)).trans
        ((Category.assoc _ _ _).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a)))))
  · rintro ⟨φ', ⟨hχ, ⟨χ₂, hs', hw'⟩, -⟩, hl'⟩
    exact cancel_with (c' := cover c sV ζ' π e hadd htor hgeom) (pair c π).pb (pair c π).sq (pair c π).iso hχ hs' hw'
      fun a => (hl' a).trans (congrArg (t ≫ ·) (secOf_left (pair c π).pb (e a))).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkMapIdentityModMaximalOfFixedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.FixStalk

theorem fixes_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  intro X _ b x hb
  have hx : b.hom x = x := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (X.residueField x)) := ⟨IsLocalRing.closedPoint _⟩
    have h2 := Scheme.fromSpecResidueField_apply x p
    have h3 : b.hom (X.fromSpecResidueField x p) = X.fromSpecResidueField x p := by
      rw [← Scheme.Hom.comp_apply, hb]
    rwa [h2] at h3
  have hs : b.hom x ⤳ x := by rw [hx]
  have hs' : x ⤳ b.hom x := by rw [hx]
  let st : X.presheaf.stalk x ⟶ X.presheaf.stalk x :=
    X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x
  have h0 : X.fromSpecStalk x ≫ b.hom = Spec.map st ≫ X.fromSpecStalk x := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom =
      spMap st.hom ≫ X.fromSpecStalk x := by
    simpa only [spMap, CommRingCat.ofHom_hom] using h0
  haveI : IsIso (X.presheaf.stalkSpecializes hs) :=
    ⟨⟨X.presheaf.stalkSpecializes hs', by simp, by simp⟩⟩
  haveI : IsLocalHom st.hom := by
    show IsLocalHom (X.presheaf.stalkSpecializes hs ≫ b.hom.stalkMap x).hom
    rw [CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom (X.residue x).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
  haveI : IsLocalHom (st ≫ X.residue x).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  refine ⟨st.hom, h1, ?_, ?_⟩
  · have e : Spec.map (X.residue x) ≫ X.fromSpecStalk x =
        Spec.map (st ≫ X.residue x) ≫ X.fromSpecStalk x := by
      rw [Spec.map_comp, Category.assoc, ← h0, ← Category.assoc]
      exact hb.symm
    have e2 := (SpecToEquivOfLocalRing X (X.residueField x)).symm.injective
      (a₁ := ⟨x, ⟨X.residue x, inferInstance⟩⟩) (a₂ := ⟨x, ⟨st ≫ X.residue x, inferInstance⟩⟩) e
    obtain ⟨_, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] at e3
    intro a
    exact (congr($e3 a)).symm
  · intro a
    have e4 : algebraMap (X.presheaf.stalk x) X.functionField a =
        algebraMap (X.presheaf.stalk (b.hom x)) X.functionField (X.presheaf.stalkSpecializes hs a) := by
      simp only [RingHom.algebraMap_toAlgebra]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [e4, GlobalTheory.functionFieldMap_algebraMap]
    rfl

end GlobalTheory.FixStalk
end

