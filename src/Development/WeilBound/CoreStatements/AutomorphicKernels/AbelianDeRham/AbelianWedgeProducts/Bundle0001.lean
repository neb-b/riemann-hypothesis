module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.CompositeRestrictionPullInjective

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.POOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]

theorem pO_one {Y : Over (Sp R)} (x : HO1 A.hom) : AXO.pO (1 : Y ⟶ A) x = 0 := by
  rw [Hom.one_def, AXO.pO_comp, AXO.HO1_base_eq_zero (AXO.pO _ x), map_zero]

theorem pO_mul (hAx : AxOSt) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    AXO.pO (fst A A * snd A A) = AXO.pO (fst A A) + AXO.pO (snd A A) := by
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ (fst A A * snd A A) = 𝟙 A := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst, lift_snd, ← Hom.mul_def, _root_.one_mul]
  apply LinearMap.ext
  intro x
  rw [LinearMap.add_apply]
  have hc := hAx R A g hA hg
    (AXO.pO (fst A A * snd A A) x - AXO.pO (fst A A) x - AXO.pO (snd A A) x)
    ((AXO.pO_spec (lift (𝟙 A) (1 : A ⟶ A)) _ _).2 ?_) ((AXO.pO_spec (lift (1 : A ⟶ A) (𝟙 A)) _ _).2 ?_)
  · rw [sub_sub, sub_eq_zero] at hc
    exact hc
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e1, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← AXO.pO_comp, ← AXO.pO_comp, ← AXO.pO_comp, e2, lift_fst, lift_snd,
      AXO.pO_id, pO_one A, sub_zero, sub_self]

theorem r11 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (fst A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, AXO.pO_id]; rfl

theorem r12 : AXO.pO (lift (𝟙 A) (1 : A ⟶ A)) ∘ₗ AXO.pO (snd A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, pO_one]; rfl

theorem r21 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (fst A A) = 0 :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_fst, pO_one]; rfl

theorem r22 : AXO.pO (lift (1 : A ⟶ A) (𝟙 A)) ∘ₗ AXO.pO (snd A A) = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, ← AXO.pO_comp, lift_snd, AXO.pO_id]; rfl

end MainStatements.Hodge.Pf.WedgeProjections
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.PairInj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

theorem affInf {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

@[reducible] def pairSL {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (hX : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hX' : ∀ U V : X'.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) :
    SemilatticeInf (Pair φ) :=
  { (inferInstance : PartialOrder (Pair φ)) with
    inf := fun p q ↦ ⟨(⟨p.1.1.1 ⊓ q.1.1.1, hX' _ _ p.1.1.2 q.1.1.2⟩, ⟨p.1.2.1 ⊓ q.1.2.1, hX _ _ p.1.2.2 q.1.2.2⟩),
      by
        show p.1.1.1 ⊓ q.1.1.1 ≤ φ ⁻¹ᵁ (p.1.2.1 ⊓ q.1.2.1)
        rw [Scheme.Hom.preimage_inf]
        exact inf_le_inf p.2 q.2⟩
    inf_le_left := fun p q ↦ ⟨(inf_le_left : p.1.1.1 ⊓ q.1.1.1 ≤ p.1.1.1), (inf_le_left : p.1.2.1 ⊓ q.1.2.1 ≤ p.1.2.1)⟩
    inf_le_right := fun p q ↦ ⟨(inf_le_right : p.1.1.1 ⊓ q.1.1.1 ≤ q.1.1.1), (inf_le_right : p.1.2.1 ⊓ q.1.2.1 ≤ q.1.2.1)⟩
    le_inf := fun a b c hab hac ↦ ⟨(le_inf hab.1 hac.1 : a.1.1.1 ≤ b.1.1.1 ⊓ c.1.1.1),
      (le_inf hab.2 hac.2 : a.1.2.1 ≤ b.1.2.1 ⊓ c.1.2.1)⟩ }

theorem pair_cover {X X' : Scheme.{0}} (φ : X' ⟶ X) : ⨆ p : Pair φ, p.1.1.1 = ⊤ := by
  refine eq_top_iff.2 (fun x _ => ?_)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens)
    (show x ∈ φ ⁻¹ᵁ V from hxV)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩

theorem pairRes_pull2_injective (hD : DescentSt) (hL : LowSt) {R : Type} [CommRing R] {X X' : Scheme.{0}}
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (hs : IsSeparated s) (hs' : IsSeparated s') :
    Function.Injective (pairRes φ s').pull2 := by
  letI : SemilatticeInf (Pair φ) := pairSL φ (affInf s hs) (affInf s' hs')
  let S : Sys X' (Pair φ) := ⟨fun p => p.1.1, fun _ _ => rfl, pair_cover φ⟩
  have hq : AllQIso (pairRes φ s') := hD R X' s' hs' (Pair φ) S
  exact (hL R _ _ _ _ (pairRes φ s') hq).2.1.1

end MainStatements.Hodge.Pf.WedgeProjections
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.PullbackWedgeCupSquare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

variable {R : Type} [CommRing R]

theorem pullback_wedge_cup_square {Y Z : Over (Sp R)} (f : Y ⟶ Z)
    (eZ : ⋀[R]^2 (HO1 Z.hom) ≃ₗ[R] H2 (OAff Z.hom))
    (hZ : ∀ a b, eZ (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Z.hom) a b)
    (eY : ⋀[R]^2 (HO1 Y.hom) ≃ₗ[R] H2 (OAff Y.hom))
    (hY : ∀ a b, eY (exteriorPower.ιMulti R 2 ![a, b]) = cup (OAff Y.hom) a b) (t : ⋀[R]^2 (HO1 Z.hom)) :
    IsPullbackH2Structure (wOver f) (eZ t) (eY (exteriorPower.map 2 (AXO.pO f) t)) := by
  unfold IsPullbackH2Structure
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := HO1 Z.hom))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by
      ext i
      fin_cases i <;> rfl
    have hv2 : (⇑(AXO.pO f) ∘ ![v 0, v 1]) = ![AXO.pO f (v 0), AXO.pO f (v 1)] := by
      ext i
      fin_cases i <;> rfl
    have h0 : (pairPull (wOver f)).pull1 (v 0) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 0)) :=
      (AXO.pO_spec f (v 0) _).2 rfl
    have h1 : (pairPull (wOver f)).pull1 (v 1) = (pairRes f.left Y.hom).pull1 (AXO.pO f (v 1)) :=
      (AXO.pO_spec f (v 1) _).2 rfl
    rw [hv, exteriorPower.map_apply_ιMulti, hv2, hZ, hY, CoefMap.pullCohomologyTwo_cup, CoefMap.pullCohomologyTwo_cup, h0, h1]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | smul a x _ hx =>
    simp only [map_smul, map_smulₛₗ, RingHom.id_apply]
    rw [hx]

end MainStatements.Hodge.Pf.WedgeProjections
end
end

