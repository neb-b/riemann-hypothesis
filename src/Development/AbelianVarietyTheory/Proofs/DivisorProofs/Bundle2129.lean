module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefInductionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CatCoh.Desc

universe v u

section Retract

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
  {T : C} (P : ∀ S, (T ⟶ S) → Prop) (Q : C → Prop) (hQ : ∀ S, (T ⟶ S) → Q S)
  (G : ∀ S, Q S → C) (θ : ∀ S h, S ⟶ G S h)
  (p : ∀ S (u : T ⟶ S), G T (hQ T (𝟙 T)) ⟶ G S (hQ S u))
  (m : ∀ S S' (h : Q S) (h' : Q S'), (S ⟶ S') → (G S h ⟶ G S' h'))
  (hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u))
  (hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h')
  (hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ))
  (hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
    m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ))
  (bij : ∀ S h, Function.Bijective (mp F (θ S h)))
  (h0 : P _ (θ T (hQ T (𝟙 T))))


include hQ bij h0 in
theorem sep_of_retract : Sep F P := by
  intro x hx
  refine (bij T (hQ T (𝟙 T))).1 ?_
  rw [hx _ _ h0, map_zero]


include hp bij h0 in
theorem glue_of_retract : Glue F P := by
  intro s hs
  obtain ⟨x, hx⟩ := (bij T (hQ T (𝟙 T))).2 (s _ (θ T (hQ T (𝟙 T))))
  refine ⟨x, fun S u hu ↦ (bij S (hQ S u)).1 ?_⟩
  rw [← mp_comp, ← hp, mp_comp, hx, ← hs _ _ _ _ h0, hp, hs _ _ _ _ hu]


include hp hθ hpm bij h0 in
theorem cocycleOne_vanishing_of_natural_additive_retract : Van1 F P := by
  intro a ha
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S u ↦ Function.surjInv (bij S (hQ S u)).2
    (a _ _ (θ T (hQ T (𝟙 T))) (p S u) - a _ _ u (θ S (hQ S u))), fun S S' u ψ hu ↦ ?_⟩
  refine (bij S' (hQ S' (u ≫ ψ))).1 ?_
  rw [map_sub, e, ← mp_comp, ← hθ S S' (hQ S u) (hQ S' (u ≫ ψ)) ψ, mp_comp, e]
  have k1 := ha _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ) h0
  have k2 := ha _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) hu
  have k3 := ha _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) hu
  rw [hpm, hp] at k1
  rw [hθ] at k3
  simp only [map_sub]
  linear_combination k1 - k3 + k2


include hp hθ hpm hmm bij h0 in
theorem cocycleTwo_vanishing_of_natural_additive_retract : Van2 F P := by
  intro z hz
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S S' u ψ ↦ Function.surjInv (bij S' (hQ S' (u ≫ ψ))).2
    (z _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) - z _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) +
      z _ _ _ (θ T (hQ T (𝟙 T))) (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)),
    fun S S' S'' u ψ χ hu ↦ ?_⟩
  refine (bij S'' (hQ S'' (u ≫ ψ ≫ χ))).1 ?_
  rw [map_add (f := _), map_sub, e, e, ← mp_comp,
    ← hθ S' S'' (hQ S' (u ≫ ψ)) (hQ S'' (u ≫ ψ ≫ χ)) χ, mp_comp, e]
  have c1 := hz _ _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) h0
  have c2 := hz _ _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c3 := hz _ _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c4 := hz _ _ _ _ u ψ χ (θ S'' (hQ S'' (u ≫ ψ ≫ χ))) hu
  rw [hpm, hmm, hp] at c1
  rw [hθ, hmm] at c2
  rw [hθ] at c3
  simp only [map_add (f := _), map_sub]
  linear_combination c3 - c4 - c2 + c1

end Retract

end GlobalTheory.CatCoh.Desc

namespace GlobalTheory.PDForm

open KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
  GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift GlobalTheory.CatCoh.Desc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem le_preimage_of_hom {T S : (IsSm κ t i).FullSubcategory} (u : T ⟶ S) {V : Y.Opens}
    (hV : ⊤ ≤ (T.obj.T.x ≫ i) ⁻¹ᵁ V) : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V := by
  intro z _
  rw [← u.hom.1.pt, Category.assoc, Scheme.Hom.comp_preimage]
  exact hV trivial

def cutPr (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    (IsSm κ t i).FullSubcategory :=
  ⟨⟨S.obj.T, S.obj.U ⊓ V.1, Or.inl (by
    rcases S.obj.hU with hU | hU
    · exact hY _ _ hU V.2
    · rw [hU, top_inf_eq]; exact V.2), fun z _ ↦ ⟨S.obj.mem trivial, h trivial⟩⟩, ⟨V, h⟩⟩

theorem cutPr_aff (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    IsAffineOpen (cutPr hY V S h).obj.U := by
  rcases S.obj.hU with hU | hU
  · exact hY _ _ hU V.2
  · change IsAffineOpen (S.obj.U ⊓ V.1)
    rw [hU, top_inf_eq]; exact V.2

def prHom {S S' : (IsSm κ t i).FullSubcategory} (φ : S.obj.T ⟶ S'.obj.T) (h : S'.obj.U ≤ S.obj.U) :
    S ⟶ S' :=
  ObjectProperty.homMk ⟨φ, h⟩

theorem prHom_ext {S S' : (IsSm κ t i).FullSubcategory} {f g : S ⟶ S'} (h : f.hom.1 = g.hom.1) :
    f = g :=
  ObjectProperty.hom_ext _ (Subtype.ext h)

theorem isSm_acyclic (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (T : (IsSm κ t i).FullSubcategory) :
    Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  obtain ⟨V, hV⟩ := T.property
  have hQ : ∀ S (u : T ⟶ S), ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1 := fun S u ↦ le_preimage_of_hom u hV
  let θ : ∀ (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1), S ⟶ cutPr hY V S h := fun S h ↦ prHom (𝟙 S.obj.T) inf_le_left
  let p : ∀ S (u : T ⟶ S), cutPr hY V T (hQ T (𝟙 T)) ⟶ cutPr hY V S (hQ S u) :=
    fun S u ↦ prHom u.hom.1 (inf_le_inf_right _ u.hom.2)
  let m : ∀ (S S' : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1)
      (h' : ⊤ ≤ (S'.obj.T.x ≫ i) ⁻¹ᵁ V.1), (S ⟶ S') → (cutPr hY V S h ⟶ cutPr hY V S' h') :=
    fun S S' h h' ψ ↦ prHom ψ.hom.1 (inf_le_inf_right _ ψ.hom.2)
  have hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u) :=
    fun S u ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h' :=
    fun S S' h h' ψ ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ) :=
    fun S S' u ψ ↦ prHom_ext rfl
  have hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
      m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ) :=
    fun S S' S'' h h' h'' ψ χ ↦ prHom_ext rfl
  have bij : ∀ S h, Function.Bijective (mp ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (θ S h)) :=
    fun S h ↦ ⟨fun a b hab ↦ hab, fun y ↦ ⟨y, rfl⟩⟩
  have h0 := cutPr_aff hY V T (hQ T (𝟙 T))
  exact ⟨sep_of_retract _ _ _ hQ _ θ bij h0, glue_of_retract _ _ _ hQ _ θ p hp bij h0,
    cocycleOne_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm bij h0,
    cocycleTwo_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm hmm bij h0⟩

theorem isSm_acyclic_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧
    ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R)
      (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) :=
  ⟨fun _ _ _ _ _ _ _ _ hY T ↦ ⟨(isSm_acyclic hY T).1, (isSm_acyclic hY T).2.1, (isSm_acyclic hY T).2.2.1⟩,
    fun _ _ _ _ _ _ _ _ hY T ↦ (isSm_acyclic hY T).2.2.2⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsFiniteType
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.CovTop GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovLift

theorem exists_lift_of_locallyOfFiniteType : ∀ (V Y : Scheme.{0}) (π : V ⟶ Y), LocallyOfFiniteType π → ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Y) (u : V), π u = y (IsLocalRing.closedPoint K) → ∃ w : Sp K ⟶ V, w ≫ π = y := by
  intro V Y π hπ K _ _ y u hu
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := y) u (IsLocalRing.closedPoint K) hu
  have : JacobsonSpace ↥(pullback π y : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π y)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback π y : Scheme.{0})) (Z := Set.univ) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π y) c hc ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory.CovLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastInverseDifferentElement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.DiffSize

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_intCast (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ‖((m : ℤ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
  have e : ((m : ℤ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((m : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_intCast, map_intCast]
  rw [e]
  refine (PadicComplex.norm_extends' (p := p) _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast; rfl

theorem pow_mem {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ I ^ k := by
  induction k with
  | zero => simpa using FractionalIdeal.one_mem_one (R := 𝓞 K) (K := K)
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

theorem exists_int_mul_pow {F : Type} [Field F] [NumberField F] [IsGalois ℚ F] {y : F}
    (hy : y ∈ latM (1 : Frac F)) : ∃ c : 𝓞 F, (c : F) = (discr F : F) * y ^ Module.finrank ℚ F := by
  have hd : (discr F : F) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have h1 : latM (1 : Frac F) = ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simp [latM]
  rw [h1] at hy
  have h2 := pow_mem hy (Module.finrank ℚ F)
  rw [inv_pow, ← FractionalIdeal.coeIdeal_pow, _root_.GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr F, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv] at h2
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton _).1 h2
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, map_intCast] at hc
  rw [← hc]; field_simp

theorem sz_invDiff : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F] (y : F) (i : Emb F), y ∈ latM (1 : Frac F) → Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F) ((i y : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ _ y i hy
  obtain ⟨c, hc⟩ := exists_int_mul_pow hy
  let φ : F →+* ℂ := Complex.ofRealHom.comp i
  have hmem : ∀ x : F, φ x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom φ.toRatAlgHom
  let ψ : F →+* algebraicClosure ℚ ℂ := φ.codRestrict (algebraicClosure ℚ ℂ) hmem
  let χ : F →+* ℂ_[l] := lam.comp ψ
  refine ⟨hmem y, ?_⟩
  change ‖χ y‖ ≤ _
  have hd0 : discr F ≠ 0 := discr_ne_zero F
  have hcint : ‖χ (c : F)‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int χ (RingOfIntegers.isIntegral_coe c); exact Subsingleton.elim _ _)
  have hdn : ‖χ (discr F : F)‖ = (l : ℝ) ^ (-(padicValInt l (discr F) : ℤ)) := by
    rw [map_intCast]; exact norm_intCast l _ hd0
  set n := Module.finrank ℚ F
  set v := padicValInt l (discr F)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hkey : ‖χ y‖ ^ n * (l : ℝ) ^ (-(v : ℤ)) ≤ 1 := by
    rw [← hdn, ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, mul_comm, ← hc]; exact hcint
  have hpow : ‖χ y‖ ^ n ≤ (l : ℝ) ^ (v : ℝ) := by
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(v : ℤ)) := zpow_pos hl0 _
    have := (le_div_iff₀ hpos).2 hkey
    rw [one_div, ← zpow_neg, neg_neg, zpow_natCast] at this
    rwa [Real.rpow_natCast]
  have hn : 0 < n := Module.finrank_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ‖χ y‖ = (‖χ y‖ ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne').symm
    _ ≤ ((l : ℝ) ^ (v : ℝ)) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (l : ℝ) ^ ((v : ℝ) / n) := by rw [← Real.rpow_mul hl0.le, div_eq_mul_inv]

end GlobalTheory.DiffSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.SizeRat

theorem norm_ratCast (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = (padicNorm l q : ℝ) := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]

theorem sz_ratCast (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) (r : ℝ)
    (hr : -(padicValRat l q : ℝ) ≤ r) : Sz l lam r (q : ℂ) := by
  have hmem : (q : ℂ) ∈ algebraicClosure ℚ ℂ := SubfieldClass.ratCast_mem _ q
  refine ⟨hmem, ?_⟩
  have e : (⟨(q : ℂ), hmem⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
    apply Subtype.ext; simp
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  rw [e, map_ratCast, norm_ratCast]
  by_cases hq : q = 0
  · subst hq; simp only [padicNorm.zero, Rat.cast_zero]; exact Real.rpow_nonneg (by linarith) r
  · rw [padicNorm.eq_zpow_of_nonzero hq, Rat.cast_zpow, Rat.cast_natCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le hl (by push_cast; exact hr)

theorem sz_exp (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) := by
  set ζ := Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) with hζ
  have hpow : ζ ^ q.den = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (q.den : ℂ) * ((2 * Real.pi * Complex.I) * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      have hq : (q : ℂ) = (q.num : ℂ) / (q.den : ℂ) := by exact_mod_cast (Rat.num_div_den q).symm
      have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [hq]; field_simp
    rw [this]; exact Complex.exp_int_mul_two_pi_mul_I q.num
  have hmem : ζ ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow q.den_pos (by rw [hpow]; exact isIntegral_one)).isAlgebraic
  refine ⟨hmem, ?_⟩
  have h1 : (⟨ζ, hmem⟩ : algebraicClosure ℚ ℂ) ^ q.den = 1 := by
    apply Subtype.ext; simp [hpow]
  have h2 : ‖lam ⟨ζ, hmem⟩‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  have h3 : ‖lam ⟨ζ, hmem⟩‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).mp h2
  rw [h3, Real.rpow_zero]

theorem sz_rat_exp : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    (∀ (q : ℚ) (r : ℝ), (-(padicValRat l q : ℝ) ≤ r) → Sz l lam r (q : ℂ)) ∧
      ∀ q : ℚ, Sz l lam 0 (Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ))) :=
  fun l _ lam => ⟨sz_ratCast l lam, sz_exp l lam⟩

end GlobalTheory.SizeRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStep
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
    QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I →
    (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  intro R _ _ I W f hsep hlft hqc W' π U hπ hiso K hK hA' hAK t ht hp
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f

  have hsys' : IsSystem (π ≫ f) I (fun e => (t e).comap π) := fun e => by
    simp only
    rw [ht e, Scheme.IdealSheafData.comap_sup, (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1]
  have hp' : ∀ e, IsProper (((t e).comap π).subschemeι ≫ π ≫ f) := fun e => by
    have h1 : ((t e).comap π).subschemeι ≫ π ≫ f =
        ((t e).comapIso π).hom ≫ pullback.snd π (t e).subschemeι ≫ (t e).subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [h1]
    infer_instance
  obtain ⟨T', hT'p, hT'r⟩ := hA' _ hsys' hp'

  have hcov : ∀ x : W, ∃ V : W.affineOpens, x ∈ (V.1 : Set W) := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : W.affineOpens => (V.1 : Set W))
    (fun V => V.1.2) (fun x _ => Set.mem_iUnion.2 (hcov x))
  choose k₀ hk₀ using _root_.GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine R I W W' f π U hπ hiso K hK t ht
  let k := s.sup k₀
  obtain ⟨T'', hT''p, hT''r⟩ := _root_.GlobalTheory.FormalAlg.alg_of_closedSubscheme R I W f (K ^ k) (hAK k) t ht hp
  refine ⟨T'.map π ⊓ T'', GlobalTheory.T.isProper_inf_ideal_sheaf_image _ W W' f π hsep hlft T' T'' (by simpa using hT'p) hT''p, fun e => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := s) (fun V => V.1) ?_ fun V =>
    hk₀ V.1 k (Finset.le_sup V.2) T' T'' hT'r hT''r e
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le (k : Type) [Field k] [Infinite k] : ∀ d : ℕ,
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro d
  induction d with
  | zero => exact isAmpleLB_tens_of_isNef_of_dim_le_zero k
  | succ d ih => exact GlobalTheory.T.ample_plus_nef_induction k d ih

theorem isAmpleLB_of_cls_eq_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  intro k _ _ X p hp A N P hA hN hP hcls
  letI := algebraΓOfHom p
  have hs : strHom k X = p := strHom_eq fun _ => rfl
  have hp' : IsProjOver (strHom k (X := X)) := hs ▸ hp
  obtain ⟨n, i, hi, -⟩ := hp
  have hd : topologicalKrullDim X ≤ (n : ℕ) :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (ProjSpace.topologicalKrullDim_eq k n).le
  have hT : IsAmpleLB (tens A N) := isAmpleLB_tens_of_isNef_of_dim_le k n X hp' hd A N hA hN
  refine IsAmpleLB.of_lbIso hT hP ((cls_eq_iff hP hT.isLB).1 ?_)
  rw [hcls, cls_tens hA.isLB hN.isLB hT.isLB]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyCoverRefinementStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hyper_cohomology_cover_refinement : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (U : J → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) (Monotone.functor (f := (Subtype.val : {V : X.affineOpens // ∃ i, V.1 ≤ U i} → X.affineOpens)) fun _ _ h ↦ h).op)) := by
  first | exact @GlobalTheory.CechDR.restrict_cover_affine_bijective | exact GlobalTheory.CechDR.restrict_cover_affine_bijective | (intros; apply GlobalTheory.CechDR.restrict_cover_affine_bijective <;> assumption)
end

