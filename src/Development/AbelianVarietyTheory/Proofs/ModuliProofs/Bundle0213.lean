module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8Sharp
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevel
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam.KerSch

theorem exists_lift_of_finite {k : Type} [Field k] [IsAlgClosed k] {Y Z : Scheme.{0}} (q : Y ⟶ Z)
    [IsFinite q] [Surjective q] (x : Sp k ⟶ Z) : ∃ y : Sp k ⟶ Y, y ≫ q = x := by
  have : CompactSpace ↥(pullback q x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  obtain ⟨p, -⟩ := (pullback.snd q x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z hz ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_lift_ext {k : Type} [Field k] {Y Z : Scheme.{0}} (f : Y ⟶ Z) (u : Sp k ⟶ Z) (t : Sp k) (y₀ : Y)
    (h : f y₀ = u t) : ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (a : Sp k' ⟶ Sp k) (y : Sp k' ⟶ Y),
      Epi a ∧ y ≫ f = a ≫ u := by
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₀ t h
  obtain ⟨k', _, _, z, -⟩ := exists_geomPt_range_eq (pullback f u) w
  refine ⟨k', inferInstance, inferInstance, z ≫ pullback.snd f u, z ≫ pullback.fst f u, ?_, ?_⟩
  · generalize z ≫ pullback.snd f u = a
    have : Surjective a := ⟨fun x => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    have : Flat a := inferInstance
    exact Flat.epi_of_flat_of_surjective a
  · rw [Category.assoc, Category.assoc, pullback.condition]

section

variable {A X G₁ Z GY Y : Scheme.{0}} {α : A ⟶ X} {g₁ : G₁ ⟶ Z} {gY : GY ⟶ Y} {φ : G₁ ⟶ A} {ψ : GY ⟶ G₁}
  {π : Z ⟶ X} {q : Y ⟶ Z} {n : ℕ} {σ : Fin n → (Y ⟶ GY)}

theorem range_subset_iff (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y : Sp k ⟶ Y) (u : Sp k ⟶ G₁) (hu : u ≫ g₁ = y ≫ q) :
    Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) ↔ ∃ j, u = y ≫ σ j ≫ ψ := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := h ⟨(default : PrimeSpectrum k), rfl⟩
    obtain ⟨j, y₀, rfl⟩ := Set.mem_iUnion.1 hw
    obtain ⟨k', _, _, a, y', ha, e'⟩ := exists_lift_ext (σ j ≫ ψ) u _ y₀ (by rw [Scheme.Hom.comp_apply]; exact e)
    have e₁ : y' ≫ q = (a ≫ y) ≫ q := by
      rw [Category.assoc, ← hu, ← reassoc_of% e', hs j]
    have e₂ : y' ≫ σ j ≫ ψ ≫ φ ∈ Set.range (fun j => (a ≫ y) ≫ σ j ≫ ψ ≫ φ) := hfib k' _ _ e₁ ▸ ⟨j, rfl⟩
    obtain ⟨j', e₃⟩ := e₂
    refine ⟨j', h₁.hom_ext ?_ ?_⟩
    · rw [← cancel_epi a, ← reassoc_of% e']
      simpa using e₃.symm
    · simp only [Category.assoc, hs, hu]
  · rintro ⟨j, rfl⟩ _ ⟨t, rfl⟩
    exact ⟨σ j (y t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, by simp⟩

theorem preimage_eq (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {GT T : Scheme.{0}} {gT : GT ⟶ T} {ν : GT ⟶ G₁} {h : T ⟶ Y} (h₃ : IsPullback ν gT g₁ (h ≫ q))
    {τ : Fin n → (T ⟶ GT)} (hτ : ∀ j, τ j ≫ gT = 𝟙 T) (hh : ∀ j, τ j ≫ ν = h ≫ σ j ≫ ψ) :
    (⋃ j, Set.range (τ j)) = ν ⁻¹' (ψ '' (⋃ j, Set.range (σ j))) := by
  ext w
  constructor
  · intro hw
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.1 hw
    refine ⟨σ j (h t), Set.mem_iUnion.2 ⟨j, _, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hh]
  · intro hw
    obtain ⟨k, _, _, z, hz⟩ := exists_geomPt_range_eq GT w
    have hzw : ∀ t, z t = w := fun t => by
      have : z t ∈ Set.range z := ⟨_, rfl⟩
      rwa [hz] at this
    obtain ⟨t₀⟩ : Nonempty (Sp k) := ⟨(default : PrimeSpectrum k)⟩
    obtain ⟨j, e⟩ := (range_subset_iff h₁ h₂ hσ hfib (z ≫ gT ≫ h) (z ≫ ν) (by simp [h₃.w])).1 (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply, hzw]
      exact hw)
    have e' : z = z ≫ gT ≫ τ j := h₃.hom_ext (by simp [e, hh]) (by simp [hτ])
    refine Set.mem_iUnion.2 ⟨j, gT w, ?_⟩
    rw [← hzw t₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← e']

theorem range_subset_range (h₁ : IsPullback φ g₁ α π) (h₂ : IsPullback ψ gY g₁ q) (hσ : ∀ j, σ j ≫ gY = 𝟙 Y)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q →
      Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) = Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ))
    {k : Type} [Field k] (y y' : Sp k ⟶ Y) (e : y ≫ q ≫ π = y' ≫ q ≫ π)
    (H : ∀ u u' : Sp k ⟶ G₁, u ≫ g₁ = y ≫ q → u' ≫ g₁ = y' ≫ q → u ≫ φ = u' ≫ φ →
      Set.range u ⊆ ψ '' (⋃ j, Set.range (σ j)) → Set.range u' ⊆ ψ '' (⋃ j, Set.range (σ j))) :
    Set.range (fun j => y ≫ σ j ≫ ψ ≫ φ) ⊆ Set.range (fun j => y' ≫ σ j ≫ ψ ≫ φ) := by
  have hs : ∀ j, σ j ≫ ψ ≫ g₁ = q := fun j => by rw [h₂.w, reassoc_of% hσ j]
  rintro _ ⟨j, rfl⟩
  have w : (y ≫ σ j ≫ ψ ≫ φ) ≫ α = (y' ≫ q) ≫ π := by
    simp only [Category.assoc, h₁.w, reassoc_of% hs, e]
  have hu : (y ≫ σ j ≫ ψ) ≫ g₁ = y ≫ q := by simp only [Category.assoc, hs]
  have := H (y ≫ σ j ≫ ψ) (h₁.lift _ _ w) hu (h₁.lift_snd _ _ _) (by simp)
    ((range_subset_iff h₁ h₂ hσ hfib y _ hu).2 ⟨j, rfl⟩)
  obtain ⟨j', e'⟩ := (range_subset_iff h₁ h₂ hσ hfib y' _ (h₁.lift_snd _ _ w)).1 this
  refine ⟨j', ?_⟩
  have := h₁.lift_fst _ _ w
  rw [e'] at this
  simpa using this

end

end GlobalTheory.HkFam.KerSch

namespace GlobalTheory.HkFam

open KerSch

theorem exists_heckeKernelScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ (Hk : Scheme.{0}) (π₁ : Hk ⟶ Xo.X) (o₁ : Ob D l (π₁ ≫ Xo.s)) (m₁ : ObjMap o₁ Xo.univ π₁) (K : Set o₁.t.G.left), IsFinite π₁ ∧ Etale π₁ ∧ HeckeSet D o₁.t 𝔓 p i K ∧ EtSet o₁.t.G K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Hk) (z' : Sp k ⟶ Hk), z ≫ π₁ = z' ≫ π₁ → (∀ (u : Over.mk z ⟶ o₁.t.G) (u' : Over.mk z' ⟶ o₁.t.G), u.left ≫ m₁.toSABMap.φ = u'.left ≫ m₁.toSABMap.φ → (Set.range u.left ⊆ K ↔ Set.range u'.left ⊆ K)) → z = z') ∧ ∀ (T : Scheme.{0}) (s : T ⟶ Sp (KA l)) (o : Ob D l s) (f : T ⟶ Xo.X) (mu : ObjMap o Xo.univ f) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over T) ⟶ o.t.G)) (K' : Set o.t.G.left), Lists (p ^ 2) τ K' → HeckeSet D o.t 𝔓 p i K' → ∃ (h : T ⟶ Hk) (n : ObjMap o o₁ h), h ≫ π₁ = f ∧ n.toSABMap.φ ≫ m₁.toSABMap.φ = mu.toSABMap.φ ∧ K' = n.toSABMap.φ ⁻¹' K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  obtain ⟨Y, Hk, q, π₁, oY, m, σ, K, hqf, hqe, hqs, hπf, hπe, hL, hK, hfib, huniv⟩ :=
    _root_.GlobalTheory.HkPerm.exists_lists_mod_perm E H D l Xo 𝔓 p i (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) hA
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (π₁ ≫ Xo.s) π₁ rfl rfl
    (by simp [spMap]) Xo.univ
  obtain ⟨m', hm'⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ oY).2 π₁ q m₁).2 m
  have h₁ := m₁.cart.1
  have h₂ := m'.cart.1
  have hσ : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w (σ j)
  rw [hm'] at hfib
  have hfib' := fun (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y) e => ((hfib k y y').1 e).1
  have hKσ := hL.2.1
  have hpre : K = m'.toSABMap.φ ⁻¹' (m'.toSABMap.φ '' K) := by
    have := preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' (h := 𝟙 Y) (ν := m'.toSABMap.φ)
      (gT := oY.t.G.hom) (by simpa using h₂) (τ := fun j => (σ j).left) hσ (fun j => by simp)
    rw [hKσ]; exact this
  refine ⟨Hk, π₁, o₁, m₁, m'.toSABMap.φ '' K, hπf, hπe, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.heckeSet_descends E H D l 𝔓 p i _ _ _ _ q o₁ oY m' _ hA hqs (hpre ▸ hK)
  · refine etSet_of_lists _ _ q _ _ m'.toSABMap.φ (p ^ 2) _ σ _ (ObjDim.isAbelianScheme o₁) m'.cart ?_ hqf hqe hqs
      (hpre ▸ hL)
    have := ((baseKA l).unit (p ^ 2) (pow_pos hA.2.2.1.pos 2)).map
      ((Scheme.ΓSpecIso (CommRingCat.of (KA l))).inv ≫ (π₁ ≫ Xo.s).appTop).hom
    rwa [map_natCast] at this
  · intro k _ _ z z' e h
    obtain ⟨y, rfl⟩ := exists_lift_of_finite q z
    obtain ⟨y', rfl⟩ := exists_lift_of_finite q z'
    rw [Category.assoc, Category.assoc] at e
    rw [hKσ] at h
    refine (hfib k y y').2 ⟨subset_antisymm ?_ ?_, e⟩
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y y' e fun u u' hu hu' e' =>
        (h (Over.homMk u hu) (Over.homMk u' hu') e').1
    · exact range_subset_range (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' y' y e.symm fun u u' hu hu' e' =>
        (h (Over.homMk u' hu') (Over.homMk u hu) e'.symm).2
  · intro T s o f mu τ K' hL' hK'
    obtain ⟨h, hf, hh⟩ := huniv T f o.t mu.toSABMap τ K' hL' hK'
    rw [← Category.assoc] at hf
    subst hf
    obtain ⟨n, hn⟩ := ((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ (h ≫ q) m₁).2 mu
    have h₃ := n.cart.1
    have hτ : ∀ j, (τ j).left ≫ o.t.G.hom = 𝟙 T := fun j => Over.w (τ j)
    refine ⟨h ≫ q, n, rfl, hn.symm, ?_⟩
    rw [hL'.2.1, hKσ]
    refine preimage_eq (σ := fun j => (σ j).left) h₁ h₂ hσ hfib' h₃ (τ := fun j => (τ j).left) hτ fun j => ?_
    refine h₁.hom_ext ?_ ?_
    · have := hh j
      rw [hm', hn] at this
      simpa using this.symm
    · have e₁ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (h ≫ q)) (hτ j))
      have e₂ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) (hσ j))
      simp only [Category.assoc, h₃.w, h₂.w]
      exact (e₁.trans (Category.id_comp _)).trans (congrArg (h ≫ ·) (e₂.trans (Category.id_comp _)).symm)

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GenTorsMap

theorem exists_factor {K : Type} [Field K] (X : Over (Sp K)) (hX : IsFinite X.hom) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra K F] (x : Sp F ⟶ X.left) (hx : x ≫ X.hom = spMap (algebraMap K F)) :
    ∃ (σ : AlgebraicClosure K →ₐ[K] F) (x' : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X),
      x = spMap σ.toRingHom ≫ x'.left := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ X.left.isoSpec.hom)
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
  have hfin : c.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hc]; infer_instance
  have e : c ≫ φ = CommRingCat.ofHom (algebraMap K F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hc, Category.assoc, Iso.hom_inv_id_assoc, hx]
  let σ : AlgebraicClosure K →ₐ[K] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ b, φ.hom b ∈ σ.range := fun b => by
    have hi : IsIntegral K (φ.hom b) := by
      obtain ⟨p, hp, h0⟩ := hfin.to_isIntegral b
      refine ⟨p, hp, ?_⟩
      have := congrArg φ.hom h0
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e' : φ.hom.comp c.hom = algebraMap K F := congrArg CommRingCat.Hom.hom e
      rwa [e'] at this
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) σ
  have hσ : Function.Injective σ := σ.toRingHom.injective
  let φ' : Γ(X.left, ⊤) →+* AlgebraicClosure K :=
    (AlgEquiv.ofInjective σ hσ).symm.toRingEquiv.toRingHom.comp (φ.hom.codRestrict σ.range hr)
  have h1 : ∀ b, σ (φ' b) = φ.hom b := fun b =>
    congrArg Subtype.val ((AlgEquiv.ofInjective σ hσ).apply_symm_apply ⟨φ.hom b, hr b⟩)
  refine ⟨σ, Over.homMk (Spec.map (CommRingCat.ofHom φ') ≫ X.left.isoSpec.inv) ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ?_
    erw [← hc]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    apply hσ
    refine (h1 _).trans ?_
    refine Eq.trans ?_ (σ.commutes a).symm
    exact congrArg (fun g => CommRingCat.Hom.hom g a) e
  · show x = _ ≫ _ ≫ _
    rw [← Category.assoc, Iso.eq_comp_inv, ← hφ, ← Spec.map_comp]
    congr 1
    ext b
    exact (h1 b).symm

theorem hom_ext_points {K : Type} [Field K] {X Y : Over (Sp K)} (hX : IsFinite X.hom) (hE : Etale X.hom)
    (hY : IsSeparated Y.hom) (u v : X ⟶ Y)
    (h : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ X, x ≫ u = x ≫ v) : u = v := by
  haveI : IsAffine X.left := isAffine_of_isAffineHom X.hom
  haveI : IsReduced X.left := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (X.left.isoSpec.inv ≫ X.hom)
    have he : c.hom.Etale := by
      rw [← HasRingHomProperty.Spec_iff (P := @Etale), hc]; infer_instance
    letI := c.hom.toAlgebra
    haveI : Algebra.Etale K Γ(X.left, ⊤) := he
    haveI : _root_.IsReduced Γ(X.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact isReduced_of_isAffine_isReduced _
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ Y.hom Set.univ dense_univ (fun z _ => ?_) (by simp)
  let F := AlgebraicClosure (X.left.residueField z)
  let i := spMap (algebraMap (X.left.residueField z) F)
  obtain ⟨c, hc⟩ := Spec.map_surjective ((i ≫ X.left.fromSpecResidueField z) ≫ X.hom)
  letI : Algebra K F := c.hom.toAlgebra
  obtain ⟨σ, x', e⟩ := exists_factor X hX F _ hc.symm
  have : Epi i := by
    have : Flat i := inferInstance
    have : Surjective i :=
      ⟨fun _ => ⟨(default : PrimeSpectrum F), Subsingleton.elim (α := PrimeSpectrum (X.left.residueField z)) _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  erw [e]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun g => _ ≫ g.left) (h x')

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.GenTorsMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem desc_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (h : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [h]; simp [spMap]) o

theorem desc_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') :
    ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem desc_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (m : ObjMap o' o f)
    (m'' : ObjMap o'' o g) (e : f' ≫ f = g) :
    ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  subst e
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem desc_cocycle (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S']
    {s : S ⟶ Sp (KA l)} (π : S' ⟶ S) [Etale π] (o : Ob D l s) (o' o₂' : Ob D l (π ≫ s)) (m : ObjMap o' o π)
    (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K) (ψ' : o'.t.G ⟶ o₂'.t.G)
    (hψ : IsIsog o' o₂' p ψ') (hker : KerSet ψ' (m.toSABMap.φ ⁻¹' K)) (f' : S' ⟶ Xo.X) (hf' : f' ≫ Xo.s = π ≫ s)
    (n' : ObjMap o₂' Xo.univ f') :
    (∀ {Z : Scheme.{0}} (x y : Z ⟶ S'), x ≫ π = y ≫ π → x ≫ f' = y ≫ f') ∧
    ∀ {Z : Scheme.{0}} (x y : Z ⟶ o'.t.G.left), x ≫ m.toSABMap.φ = y ≫ m.toSABMap.φ →
      x ≫ ψ'.left ≫ n'.toSABMap.φ = y ≫ ψ'.left ≫ n'.toSABMap.φ := by
  have hab : pullback.fst π π ≫ π = pullback.snd π π ≫ π := pullback.condition
  haveI : IsReduced (pullback π π) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  obtain ⟨oT, ⟨mT⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π ≫ π) (by simp) o
  obtain ⟨ma, hma⟩ := desc_cancel (f' := pullback.fst π π) m mT rfl
  obtain ⟨mb, hmb⟩ := desc_cancel (f' := pullback.snd π π) m mT hab.symm
  obtain ⟨oa, ⟨na⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π) rfl o₂'
  obtain ⟨ob, ⟨nb⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.snd π π)
    (by rw [reassoc_of% hab]) o₂'
  obtain ⟨⟨ψa, hψa, -⟩, Ha⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT oa ma na ψ'
  obtain ⟨⟨ψb, hψb, -⟩, Hb⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT ob mb nb ψ'
  obtain ⟨ia, ka⟩ := Ha ψa hψa
  obtain ⟨ib, kb⟩ := Hb ψb hψb
  have ka' : KerSet ψa (mT.toSABMap.φ ⁻¹' K) := by
    have := ka _ hψ.1.1 hker
    rw [hma]; simpa [Set.preimage_comp] using this
  have kb' : KerSet ψb (mT.toSABMap.φ ⁻¹' K) := by
    have := kb _ hψ.1.1 hker
    rw [hmb]; simpa [Set.preimage_comp] using this
  have hKT : HeckeSet D oT.t 𝔓 p i (mT.toSABMap.φ ⁻¹' K) :=
    ((GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t oT.t _ mT.toSABMap o.proper).2 K).1 hK
  obtain ⟨na', hna⟩ := desc_comp n' na
  obtain ⟨nb', hnb⟩ := desc_comp n' nb
  obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.heckeQuot_unique E H D l Xo 𝔓 p i _ _ oT oa ob ψa ψb _ _ _ na' nb' hA hKT
    (by rw [Category.assoc, hf']) (by rw [Category.assoc, hf', reassoc_of% hab]) (ia hψ) (ib hψ) ka' kb'
  rw [hna, hnb, reassoc_of% hψa, reassoc_of% hψb] at e₂
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have := pullback.lift x y hxy ≫= e₁
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  · have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
    have pa : IsPullback ma.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.fst π π) := ma.cart.1
    have pb : IsPullback mb.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.snd π π) := mb.cart.1
    have h₀ : (x ≫ o'.t.G.hom) ≫ π = (y ≫ o'.t.G.hom) ≫ π := by
      simp only [Category.assoc, ← pm.w, reassoc_of% hxy]
    let w := pa.lift x (pullback.lift _ _ h₀) (pullback.lift_fst _ _ _).symm
    have wa : w ≫ ma.toSABMap.φ = x := pa.lift_fst _ _ _
    have wb : w ≫ mb.toSABMap.φ = y := by
      apply pm.hom_ext
      · rw [Category.assoc, ← hmb, hma, reassoc_of% wa, hxy]
      · rw [Category.assoc, pb.w, pa.lift_snd_assoc, pullback.lift_snd]
    rw [← wa, ← wb, Category.assoc, Category.assoc, e₂]

theorem hasQuot_descend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S S' _ s π o o' m K hA hK hE hS hQ ⟨o₂', ψ', hψ, hker⟩
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  obtain ⟨f', ⟨hf', ⟨n'⟩⟩, -⟩ := Xo.rep S' (π ≫ s) inferInstance o₂'
  obtain ⟨c₁, c₂⟩ := desc_cocycle Xo 𝔓 p i π o o' o₂' m K hA hK ψ' hψ hker f' hf' n'
  have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
  have pn' : IsPullback n'.toSABMap.φ o₂'.t.G.hom Xo.univ.t.G.hom f' := n'.cart.1
  haveI : Flat m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip (inferInstance : Flat π)
  haveI : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hS
  haveI : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hQ
  haveI : EffectiveEpi π := inferInstance
  haveI : EffectiveEpi m.toSABMap.φ := inferInstance
  obtain ⟨f, hf⟩ : ∃ f : S ⟶ Xo.X, π ≫ f = f' := ⟨_, EffectiveEpi.fac π f' c₁⟩
  obtain ⟨h, hh⟩ : ∃ h, m.toSABMap.φ ≫ h = ψ'.left ≫ n'.toSABMap.φ := ⟨_, EffectiveEpi.fac _ _ c₂⟩
  have hfs : f ≫ Xo.s = s := by rw [← cancel_epi π, reassoc_of% hf, hf']
  obtain ⟨o₂, ⟨n⟩⟩ := desc_pull s f hfs Xo.univ
  obtain ⟨n₂, hn₂⟩ := desc_cancel n n' hf
  have pn : IsPullback n.toSABMap.φ o₂.t.G.hom Xo.univ.t.G.hom f := n.cart.1
  have pn₂ : IsPullback n₂.toSABMap.φ o₂'.t.G.hom o₂.t.G.hom π := n₂.cart.1
  have hw : h ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ f := by
    rw [← cancel_epi m.toSABMap.φ, reassoc_of% hh, pn'.w, pm.w_assoc, hf, Over.w_assoc]
  let ψ : o.t.G ⟶ o₂.t.G := Over.homMk (pn.lift h _ hw) (pn.lift_snd _ _ _)
  have hψn : ψ.left ≫ n.toSABMap.φ = h := pn.lift_fst _ _ _
  have sq : ψ'.left ≫ n₂.toSABMap.φ = m.toSABMap.φ ≫ ψ.left := by
    apply pn.hom_ext
    · rw [Category.assoc, Category.assoc, ← hn₂, hψn, hh]
    · rw [Category.assoc, Category.assoc, pn₂.w, Over.w_assoc, Over.w, pm.w]
  have P : IsPullback m.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact pm) sq.symm pn₂
  have q : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) n₂.toSABMap.φ :=
    ⟨⟨MorphismProperty.of_isPullback pn₂.flip hS,
      MorphismProperty.of_isPullback pn₂.flip (inferInstance : Flat π)⟩,
      MorphismProperty.of_isPullback pn₂.flip hQ⟩
  have hEt : Etale ψ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) P.flip q hψ.1.2.2.1
  haveI : IsFinite ψ'.left := hψ.1.2.1
  haveI : IsAffineHom ψ.left := by
    refine GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ ψ.left n₂.toSABMap.φ q.1.1 q.1.2 q.2 ?_
    rw [← P.isoPullback_inv_snd]
    infer_instance
  haveI := o₂.proper
  haveI : IsProper (ψ.left ≫ o₂.t.G.hom) := by rw [Over.w]; exact o.proper
  haveI : IsProper ψ.left := IsProper.of_comp ψ.left o₂.t.G.hom
  have hFin : IsFinite ψ.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨r₁, r₂⟩ := GlobalTheory.isIsog_of_surjective_baseChange E H D l p S S' s _ π o o₂ o' o₂' m n₂ ψ ψ' hS sq hψ hFin hEt
  exact ⟨o₂, ψ, r₁, r₂ K hker⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassE8SharpStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodThetaComplexClass_E8Sharp : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), GoodClass em (SharpClass (b := b) W a bas em) Mat κ w w' (h * (h + 1) / 2) := by
  first | exact @GlobalTheory.SharpGood.goodClass_sharpClass | exact GlobalTheory.SharpGood.goodClass_sharpClass | (intros; apply GlobalTheory.SharpGood.goodClass_sharpClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → GoodClass em (PELClass (b := b) D a bas ρ em) Mat κ w w' D.dim := by
  first | exact @GlobalTheory.PelGood.goodClass_pelClass | exact GlobalTheory.PelGood.goodClass_pelClass | (intros; apply GlobalTheory.PelGood.goodClass_pelClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LN


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
theorem _root_.GlobalTheory.LN.pelSt_holds : _root_.GlobalTheory.LN.PelSt := by
  obtain ⟨hLaws, hTwist, hTheta, hTorsion, hRank⟩ := _root_.GlobalTheory.lawsAndExpansions
  exact _root_.GlobalTheory.PELOfUnif.main hLaws hTwist hTheta hTorsion hRank

end GlobalTheory.LN
end

