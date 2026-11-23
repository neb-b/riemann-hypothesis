module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ


open GlobalTheory.CompanionTheory.MixZ.PtDictProof in
theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (_root_.GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePointOfNonvanishingCoords
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem mem_blockChart_iff (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i : Bk n k) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔
      GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y ∈
        ptsIn (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) :=
  Iff.rfl

theorem ev_pullRatio (y : CxPts (mpStr ℤ m n) σ₀) (k : Fin (m + 1)) (i j : Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y =
      CxPts.ev (PSpace.str ℤ (n k)) σ₀ (chart ℤ (n k) i) (ratio ℤ (n k) i j)
        (GlobalTheory.Points.PtsOver.map (prB n k) (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) _ y) := by
  have e : pullRatio (prB n k) (blockChart n k i) i le_rfl j = (prB n k).app (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
    rw [Scheme.Hom.app_eq_appLE]
    rfl
  rw [e]
  exact CxPts.ev_app (p := PSpace.str ℤ (n k)) (q := mpStr ℤ m n) (prB n k)
    (GroundTheory.Arith.SchemeCoh.ProjSpace.pr_toSpecBase ℤ m n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) y

theorem isUnder_ptMP (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    IsUnder (GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z) z ∧ GlobalTheory.CompanionTheory.MPSmooth.multiprojectivePoint c z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  have H : IsUnder (multiprojectivePoint c z) z := fun k i => by
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.projective_point_chart_ratio (n k) (c k) (fun i => z ⟨k, i⟩) (hz k)
    have e := map_prB_ptMP c z k
    refine ⟨?_, fun j hy => ?_⟩
    · rw [mem_blockChart_iff, e]
      exact h₁ i
    · rw [ev_pullRatio, e]
      exact h₂ i j (by rw [← e]; exact (mem_blockChart_iff _ k i).1 hy)
  refine ⟨H, CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)⟩
  exact CxPts.mem_ptsIn.1 ((H k (c k)).1.2 (hz k))

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMemNormGroup
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormClassNorm

theorem norm_mem_normGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k]
    [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r)
    (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k →
    Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := by
  intro E _ _ _ k _ _ r Q x hx
  obtain ⟨z, hz⟩ : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hθ : IsCMField.complexConj E (z - IsCMField.complexConj E z) =
      -(z - IsCMField.complexConj E z) := by
    rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  obtain ⟨b, B, hB⟩ := GlobalTheory.TraceClasses.exists_bases Q (sub_ne_zero.2 hz.symm) hθ
  have h1 : Isometric Q k (GlobalTheory.TraceClasses.gramRat Q B 1)
      ((1 : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) := by
    have := (GlobalTheory.TraceClasses.isometric_tmul_iff Q B k (GlobalTheory.TraceClasses.gramRat Q B 1) 1).2
      (GlobalTheory.HermLocal.CongrOver.of_congr ⟨1, by simp, by simp⟩)
    simpa [Algebra.TensorProduct.one_def] using this
  have h2 := Isometric.of_norm Q k hx h1
  rw [one_mul] at h2
  have h3 := GlobalTheory.TraceClasses.norm_div_mem Q hB k (δ := 1) (by simp) h2
  have h4 : GlobalTheory.QuadSymbol.toUnits (maximalRealSubfield E) k 1 = 1 := map_one _
  rwa [h4, div_one] at h3

end GlobalTheory.CompanionTheory.NormClassNorm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMapEqMOm
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

section Alg

variable {K : Type} [CommRing K] {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

theorem omMap_eq_mOm (φ : A →ₐ[K] B) (h : SemiHom (RingHom.id K) (φ : A →+* B)) (a : ℕ) (ω : CrystallineSemistableComparison.Onto.Om K A a) :
    CrystallineSemistableComparison.Onto.omMap φ a ω = h.mOm a ω := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  have hs : ∀ (c : A) (x : CrystallineSemistableComparison.Onto.Om K A a), CrystallineSemistableComparison.Onto.omMap φ a (c • x) = φ c • CrystallineSemistableComparison.Onto.omMap φ a x := by
    intro c x
    have h' := map_smul (exteriorPower.alternatingMapLinearEquiv
      { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
          fun _ => KaehlerDifferential.map K K A B with
        map_eq_zero_of_eq' := fun v i j h hij =>
          (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq (fun k => KaehlerDifferential.map K K A B (v k))
            (congrArg _ h) hij } : CrystallineSemistableComparison.Onto.Om K A a →ₗ[A] CrystallineSemistableComparison.Onto.Om K B a) c x
    exact h'.trans (algebraMap_smul B c _)
  have hι : ∀ g : Fin a → Ω[A⁄K], CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
      h.mOm a (exteriorPower.ιMulti A a g) := by
    intro g
    have e1 : CrystallineSemistableComparison.Onto.omMap φ a (exteriorPower.ιMulti A a g) =
        exteriorPower.ιMulti B a fun k => KaehlerDifferential.map K K A B (g k) :=
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    rw [e1]
    refine Subtype.ext ?_
    rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext k
    exact (congrArg ι1 (SemiHom.oneFormMap_eq_kaehlerDifferential_map h (fun _ => rfl) (g k))).symm.trans (SemiHom.mDR_ι h (g k)).symm
  have hmem : ω ∈ (⊤ : Submodule A (CrystallineSemistableComparison.Onto.Om K A a)) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact hι g
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul c x _ hx => rw [hs, SemiHom.mOm_smul, hx]; rfl

end Alg

section Sch

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev omSheaf (a : ℕ) : TopCat.Sheaf Ab X := ⟨(Omega q a).presheaf, (Omega q a).isSheaf⟩

theorem glue_core [IsAffine X] {ι : Type} (U : ι → X.Opens) (hcov : (⨆ α, U α) = ⊤) (a : ℕ) :
    (∀ ω ω' : OmU q ⊤ a, (∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) =
      toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω')) → ω = ω') ∧
    ∀ y : ∀ α, OmU q (U α) a,
      (∀ α β, formRes q (inf_le_left : U α ⊓ U β ≤ U α) a (y α) = formRes q (inf_le_right : U α ⊓ U β ≤ U β) a (y β)) →
      ∃ ω : OmU q ⊤ a, ∀ α, toOm q a (U α) (formRes q (le_top : U α ≤ ⊤) a ω) = toOm q a (U α) (y α) := by
  have hT : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  refine ⟨fun ω ω' h => toOm_injective hT ?_, fun y hy => ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge _ _ fun α => ?_
    exact (res_toOm q a le_top ω).trans ((h α).trans (res_toOm q a le_top ω').symm)
  · have hc : TopCat.Presheaf.IsCompatible (omSheaf q a).1 U (fun α => toOm q a (U α) (y α)) := fun α β =>
      (res_toOm q a inf_le_left (y α)).trans ((congrArg _ (hy α β)).trans (res_toOm q a inf_le_right (y β)).symm)
    obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (omSheaf q a) U ⊤ (fun α => homOfLE le_top) hcov.ge
      (fun α => toOm q a (U α) (y α)) hc
    obtain ⟨ω, rfl⟩ := toOm_surjective hT t
    exact ⟨ω, fun α => (res_toOm q a le_top ω).symm.trans (ht α)⟩

theorem omMap_res {V W : X.Opens} (h : W ≤ V) (φ : CrystallineSemistableComparison.Onto.Sec q V →ₐ[K] CrystallineSemistableComparison.Onto.Sec q W)
    (hφ : ∀ g, φ g = (X.presheaf.map (homOfLE h).op).hom g) (a : ℕ)
    (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q V) a) : CrystallineSemistableComparison.Onto.omMap φ a ω = formRes q h a ω := by
  have e : φ = (Sec.res q h : GlobalTheory.CechDR.Sec q V →ₐ[K] GlobalTheory.CechDR.Sec q W) := AlgHom.ext hφ
  subst e
  exact omMap_eq_mOm _ (SemiHom.of_algHom (Sec.res q h)) a ω

end Sch

end GlobalTheory.CompanionTheory.FormsGlue

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.FormsGlue

theorem forms_glue : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] {ι : Type}
    (U : ι → X.Opens), (∀ α, IsAffineOpen (U α)) → (⨆ α, U α) = ⊤ →
    ∀ (φ : ∀ α, CrystallineSemistableComparison.Onto.Sec q ⊤ →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α))
      (ψ₁ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U α) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β))
      (ψ₂ : ∀ α β, CrystallineSemistableComparison.Onto.Sec q (U β) →ₐ[K] CrystallineSemistableComparison.Onto.Sec q (U α ⊓ U β)),
    (∀ α g, φ α g = (X.presheaf.map (homOfLE (le_top : U α ≤ ⊤)).op).hom g) →
    (∀ α β g, ψ₁ α β g = (X.presheaf.map (homOfLE (inf_le_left : U α ⊓ U β ≤ U α)).op).hom g) →
    (∀ α β g, ψ₂ α β g = (X.presheaf.map (homOfLE (inf_le_right : U α ⊓ U β ≤ U β)).op).hom g) → ∀ a : ℕ,
    Function.Injective (fun (ω : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a) α => CrystallineSemistableComparison.Onto.omMap (φ α) a ω) ∧
    ∀ y : ∀ α, CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q (U α)) a,
      (∀ α β, CrystallineSemistableComparison.Onto.omMap (ψ₁ α β) a (y α) = CrystallineSemistableComparison.Onto.omMap (ψ₂ α β) a (y β)) →
      ∃ ω, ∀ α, CrystallineSemistableComparison.Onto.omMap (φ α) a ω = y α := by
  intro K _ X q _ ι U hU hcov φ ψ₁ ψ₂ hφ hψ₁ hψ₂ a
  have hc := glue_core q U hcov a
  refine ⟨fun ω ω' h => hc.1 ω ω' fun α => ?_, fun y hy => ?_⟩
  · have e := congrFun h α
    simp only [] at e
    rw [omMap_res q le_top (φ α) (hφ α), omMap_res q le_top (φ α) (hφ α)] at e
    exact congrArg _ e
  · obtain ⟨ω, hω⟩ := hc.2 y fun α β => by
      have e := hy α β
      rw [omMap_res q inf_le_left (ψ₁ α β) (hψ₁ α β), omMap_res q inf_le_right (ψ₂ α β) (hψ₂ α β)] at e
      exact e
    refine ⟨ω, fun α => ?_⟩
    rw [omMap_res q le_top (φ α) (hφ α)]
    exact toOm_injective (hU α) (hω α)

end GlobalTheory.CompanionTheory.FormsGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdIrrEquivOfOrdered
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.SplitRead GlobalTheory.ProdReorder

noncomputable section

namespace GlobalTheory.CompanionTheory.SegReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem famCongr {u : ℕ} {f g : Fin u → IrrGL (k := k)} (hfg : ∀ i, f i = g i) {T : ℕ}
    (e : (Σ i, Fin (f i).1) ≃ Fin T) (e' : (Σ i, Fin (g i).1) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (f i).rep).Equiv (multiProd e' fun i => (g i).rep)) := by
  obtain rfl : f = g := funext hfg
  exact multiProd_placing e e' _

end GlobalTheory.CompanionTheory.SegReorder
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictPullBijectiveOfForall
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.OmRes

theorem restrict_pull_bijective_of_forall :
    ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
      (Q : ObjectProperty C), (∀ T, Q T) →
      ∀ n : ℕ, Function.Bijective ((CH.Mor.restrict F Q.ι).pull n) := by
  intro R _ C _ F Q h n
  haveI : Q.ι.EssSurj := ⟨fun Y => ⟨⟨Y, h Y⟩, ⟨Iso.refl _⟩⟩⟩
  haveI : Q.ι.IsEquivalence := { }
  exact CrystallineSemistableComparison.P.adj F Q.ι Q.ι.inv Q.ι.asEquivalence.toAdjunction n

end GlobalTheory.CompanionTheory.OmRes
end

