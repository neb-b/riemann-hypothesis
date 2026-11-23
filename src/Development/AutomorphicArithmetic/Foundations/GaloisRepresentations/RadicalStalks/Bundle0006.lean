module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RankV
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.FrobAdjoint

theorem UpperTheory.Gal.Ord.rankV :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k) (V : A.left ⟶ A.left) (m : SMor A σ V), (∀ x, σ x ^ p = x) →
      GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ V = ((𝟙 A) ^ p : A ⟶ A).left → ∀ y, m.pull y = 0 → ∃ z, frobDR p k hk A z = y := by
  intro p _ k _ _ hk A _ _ hA σ V m hσ hV y hy
  obtain ⟨e, he, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hn : IsNilpotent (p : k) := ⟨1, by rw [pow_one, hk]⟩
  obtain ⟨g, hg⟩ : ∃ g, SmoothOfRelativeDimension g A.hom := GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension k A hA
  obtain ⟨G, t, -⟩ := GlobalTheory.AbelianTower.exists_pDivGroup_tower p k hn A g hA hg
  let A₁ := (Over.pullback (spMap (frobR p k hk))).obj A
  have hπ : IsGrpPullback A₁ A _ _ := isGrpPullback_pullback A (spMap (frobR p k hk))
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj _ A hA
  obtain ⟨F, hFm, hF⟩ := _root_.GlobalTheory.RelFrobGrp.main p k hk A A₁ _ hπ
  obtain ⟨t₁, ht⟩ := exists_tower hk t hπ
  have mπ := grpMor_of_isGrpPullback hπ
  have hid : (frobR p k hk).comp σ = RingHom.id k := RingHom.ext fun x => (frobR_apply p k hk _).trans (hσ x)
  have hb : spMap (frobR p k hk) ≫ spMap σ = 𝟙 _ := by rw [← GlobalTheory.Cris.spMap_comp, hid, GlobalTheory.Cris.spMap_id]
  have mc := m.comp mπ
  let V₁ : A₁ ⟶ A := Over.homMk (_ ≫ V) (mc.w.trans (by rw [hb, Category.comp_id]))
  have hm : IsMonHom V₁ := isMonHom_of_mul _ fun T x x' => by
    have hw : (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) = T.hom := by rw [hb, Category.comp_id]
    let j : Over.mk (T.hom ≫ spMap (frobR p k hk) ≫ spMap σ) ⟶ T := Over.homMk (𝟙 _) (by simpa using hw.symm)
    have h := mc.mul T x x' (j ≫ x ≫ V₁) (j ≫ x' ≫ V₁) (by simp [j, V₁]) (by simp [j, V₁])
    rw [← MonObj.comp_mul] at h
    refine Over.OverMorphism.ext ?_
    simpa [j, V₁] using h.symm
  have hFV : F ≫ V₁ = 𝟙 A ^ p := Over.OverMorphism.ext (by
    change F.left ≫ _ ≫ V = _
    rw [← Category.assoc, hF, hV])
  have h0 : primPull (dp0 k) (𝟙 _) V₁ y = 0 := by
    have h1 := GrpMor.pull_pull m mπ (homMor (dp0 k) (𝟙 _) V₁) (fun r => RingHom.congr_fun hid r) rfl y
    rw [hy, map_zero] at h1
    exact h1.symm
  have h1 : rigExtMap (verschiebung hk G) (e hn hA t y) = 0 := by
    rw [← map_eq_verschiebung hk t t₁ ht F V₁ hF hFV, ← he.primPull hn hA₁ hA t₁ t, h0, (e hn hA₁ t₁).map_zero]
  obtain ⟨-, -, -, -, -, h2, h3⟩ := rigExt_field_of_charP p k hk G
  have h4 : e hn hA t y ∈ Submodule.span k (Set.range (absFrob hk G).rig) := h3 ▸ h2 ▸ h1
  have h5 : ∀ z, e hn hA t (frobDR p k hk A z) = (absFrob hk G).rig (e hn hA t z) := fun z => by
    rw [(t.eq_semiOf_iff t (frobMor p k hk A (cast_left p k hk A)) (absFrob hk G)).2 (absFrob_y hk t)]
    exact he hn hn hA hA t t _ z
  have h6 : ∀ u ∈ Submodule.span k (Set.range (absFrob hk G).rig), ∃ z, e hn hA t (frobDR p k hk A z) = u := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨v, rfl⟩ := hu
      exact ⟨(e hn hA t).symm v, by rw [h5]; exact congrArg (absFrob hk G).rig ((e hn hA t).apply_symm_apply v)⟩
    | zero => exact ⟨0, by rw [map_zero (f := frobDR p k hk A), (e hn hA t).map_zero]⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _)]⟩
    | smul l u _ hu =>
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq l (Fact.out : p.Prime).pos
      exact ⟨r • a, by rw [map_smulₛₗ, map_smul, frobR_apply]⟩
  obtain ⟨z, hz⟩ := h6 _ h4
  exact ⟨z, (e hn hA t).injective hz⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Root
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.root :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (σ : k →+* k), Function.Bijective σ → ∀ (ψ : A.left ⟶ A.left) (m : SMor A σ ψ), (∀ x ∈ PrimitiveSubmodule A, m.pull x = 0) →
      ∃ (σ' : k →+* k) (ψ' : A.left ⟶ A.left), Function.Bijective σ' ∧ SMor A σ' ψ' ∧ (∀ x, σ' x ^ p = σ x) ∧ GlobalTheory.VB.frob A.left p (cast_left p k hk A) ≫ ψ' = ψ := by
  intro p _ k _ _ hk A _ _ hab σ hσ ψ m hm
  haveI : IsAbelianScheme A := hab
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr hk
  haveI : AlgebraicGeometry.IsIntegral A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field A hab
  haveI : Smooth A.hom := IsAbelianScheme.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hab
  have hLie : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hab hg).1
  have hT : ∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ) := by
    intro v hv
    refine (tan k A hab σ ψ m hσ.2 v hv).mp ?_
    intro f hf
    obtain ⟨h, hh⟩ := hLie.2 v hv
    have hcl : Form.cl _ ((GrpMor.isMor m).pullForm f) = 0 := by
      rw [IsMor.cl_pullForm]
      have hF : (⟨Form.cl _ f, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
        show Form.cl _ f ∈ F1 _
        rw [hodgeFiltration_eq_range]
        exact ⟨f, rfl⟩
      exact congrArg Subtype.val (hm _ hF)
    have hmem : Form.cl _ ((GrpMor.isMor m).pullForm f) ∈ primDR A := hcl ▸ (primDR A).zero_mem
    rw [← hh.2 _ hmem]
    have he : (⟨Form.cl _ ((GrpMor.isMor m).pullForm f), hmem⟩ : primDR A) = 0 := Subtype.ext hcl
    rw [he]
    exact map_zero h
  have hall := transl k A σ ψ m hT
  have hroot := dzero p k hk A.left A.left A.hom ψ (fun v hv => hall (Over.homMk v hv))
  obtain ⟨ψ', hψ'⟩ := root0 p A.left A.left (cast_left p k hk A) ψ hroot
  refine ⟨((frobeniusEquiv k p).symm : k →+* k).comp σ, ψ', ?_, ?_, ?_, hψ'⟩
  · exact (frobeniusEquiv k p).symm.bijective.comp hσ
  · exact rootMor p k hk A hab σ _ ψ ψ' m (fun x => frobeniusEquiv_symm_pow_p k p (σ x)) hψ'
  · exact fun x => frobeniusEquiv_symm_pow_p k p (σ x)
end

