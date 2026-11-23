module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExt
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.FiniteData

def Pair {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (m : ℕ) : Prop :=
  ∃ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i ∧ IsMonHom r ∧ r ≫ i = 𝟙 B ^ m

theorem Pair.of_iso {S : Scheme.{0}} {A B A' B' : Over S} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] {m : ℕ}
    (a : A' ≅ A) (b : B' ≅ B) [IsMonHom a.hom] [IsMonHom b.hom] (h : Pair A B m) : Pair A' B' m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨a.hom ≫ i ≫ b.inv, b.hom ≫ r ≫ a.inv, inferInstance, inferInstance, ?_⟩
  have : (b.hom ≫ r ≫ a.inv) ≫ a.hom ≫ i ≫ b.inv = b.hom ≫ (r ≫ i) ≫ b.inv := by simp
  rw [this, e, MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem isMonHom_symm {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (a : A ≅ B) [IsMonHom a.hom] :
    IsMonHom a.symm.hom := inferInstanceAs (IsMonHom a.inv)

theorem isMonHom_refl {S : Scheme.{0}} (A : Over S) [GrpObj A] : IsMonHom (Iso.refl A).hom :=
  inferInstanceAs (IsMonHom (𝟙 A))

attribute [local instance] isMonHom_symm isMonHom_refl

theorem relDim_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Over S) {g : ℕ} (h : SmoothOfRelativeDimension g X.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj X).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) h

theorem Pair.pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] {m : ℕ}
    (h : Pair A B m) : Pair ((Over.pullback f).obj A) ((Over.pullback f).obj B) m := by
  obtain ⟨i, r, hi, hr, e⟩ := h
  refine ⟨(Over.pullback f).map i, (Over.pullback f).map r, inferInstance, inferInstance, ?_⟩
  rw [← Functor.map_comp, e, ← CategoryTheory.Functor.map_id]
  exact map_pow ((Over.pullback f).homMonoidHom) _ _

theorem spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃)
    (h : R₁ →+* R₃) (e : ∀ x, g (f x) = h x) : spMap g ≫ spMap f = spMap h := by
  obtain rfl : h = g.comp f := RingHom.ext fun x => (e x).symm
  rw [← Spec.map_comp]; rfl

theorem Pair.descend {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (h : Pair A' B' m) : ∃ (L : IntermediateField F Ω), FiniteDimensional F L ∧
      ∀ (L' : IntermediateField F Ω), L ≤ L' → ∀ (A'' B'' : Over (Sp L')) [GrpObj A''] [GrpObj B'']
        (φ' : A''.left ⟶ A.left) (ψ' : B''.left ⟶ B.left), IsGrpPullback A'' A (spMap (algebraMap F L')) φ' →
        IsGrpPullback B'' B (spMap (algebraMap F L')) ψ' → Pair A'' B'' m := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A _) pA
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback B _) pB
  obtain ⟨i, r, hi, hr, e⟩ := h.of_iso a b
  obtain ⟨L, hL, i', r', hi', hr', e'⟩ := GlobalTheory.homPair_descends_to_finite F Ω A B hA hB i r hi hr
  refine ⟨L, hL, fun L' hle A'' B'' _ _ φ' ψ' qA qB => ?_⟩
  have h₁ : Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m :=
    ⟨i', r', hi', hr', (e' m).2 e⟩
  let τ : L →+* L' := (IntermediateField.inclusion hle).toRingHom
  have hτ : spMap τ ≫ spMap (algebraMap F L) = spMap (algebraMap F L') := spMap_comp _ _ _ fun x => rfl
  obtain ⟨a', ha', -⟩ := grpPullback_iso qA
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback A _)).congr hτ rfl)
  obtain ⟨b', hb', -⟩ := grpPullback_iso qB
    (((isGrpPullback_pullback _ (spMap τ)).comp (isGrpPullback_pullback B _)).congr hτ rfl)
  exact (h₁.pullback (spMap τ)).of_iso a' b'

theorem finite_of_fg {o Ω₀ : Type} [Field o] [Field Ω₀] [Algebra o Ω₀] [Algebra.IsAlgebraic o Ω₀] (R₀ : Subalgebra o Ω₀)
    (hfg : R₀.FG) (hfr : ∀ x : Ω₀, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) : FiniteDimensional o Ω₀ := by
  have ht : R₀ = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr x
    rw [div_eq_mul_inv]
    exact R₀.mul_mem ha (R₀.inv_mem_of_algebraic (x := ⟨b, hb⟩) (Algebra.IsAlgebraic.isAlgebraic _))
  have : Algebra.FiniteType o Ω₀ := ⟨ht ▸ hfg⟩
  exact Algebra.IsIntegral.finite

theorem exists_pol_baseChange {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S)
    (h : letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧
      (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := polBaseChange_holds S S' f P
  have gp : IsGrpPullback P'.A P.A f φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl⟩
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact ⟨P', φ, gp, GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f φ P.L P'.L P.isLB P'.isLB gp
    (LBIso.symm ⟨t, ht⟩) h⟩

theorem exists_finite_pairs {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    {A B : Over (Sp F)} {A' B' C' : Over (Sp Ω)} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] [GrpObj C']
    (Q : Out.PolAV (Sp F)) (hQ : letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {m : ℕ} {φ : A'.left ⟶ A.left} {ψ : B'.left ⟶ B.left}
    {χ : C'.left ⟶ Q.A.left}
    (pA : IsGrpPullback A' A (spMap (algebraMap F Ω)) φ) (pB : IsGrpPullback B' B (spMap (algebraMap F Ω)) ψ)
    (pC : IsGrpPullback C' Q.A (spMap (algebraMap F Ω)) χ)
    (h : Pair A' B' m) (h' : Pair C' B' 1) : ∃ (L : IntermediateField F Ω) (Q' : Out.PolAV (Sp L)),
      FiniteDimensional F L ∧ (letI := Q'.isAb.comm; GlobalTheory.ZH.HypS Q'.A Q'.L) ∧
      Pair ((Over.pullback (spMap (algebraMap F L))).obj A) ((Over.pullback (spMap (algebraMap F L))).obj B) m ∧
      Pair Q'.A ((Over.pullback (spMap (algebraMap F L))).obj B) 1 := by
  obtain ⟨L₁, f₁, h₁⟩ := h.descend hA hB pA pB
  obtain ⟨L₂, f₂, h₂⟩ := h'.descend Q.isAb hB pC pB
  obtain ⟨Q', χ', gp, hS⟩ := exists_pol_baseChange (spMap (algebraMap F (L₁ ⊔ L₂ : IntermediateField F Ω))) Q hQ
  exact ⟨L₁ ⊔ L₂, Q', inferInstance, hS,
    h₁ _ le_sup_left _ _ _ _ (isGrpPullback_pullback _ _) (isGrpPullback_pullback _ _),
    h₂ _ le_sup_right _ _ _ _ gp (isGrpPullback_pullback _ _)⟩

theorem exists_finite_data (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (L : Type) (_ : Field L) (c : K →+* L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (m : ℕ),
      c.Finite ∧ SmoothOfRelativeDimension g B.hom ∧ 1 ≤ m ∧ Pair ((Over.pullback (spMap c)).obj A) B m ∧
      Pair Q.A B 1 ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  let Ω := AlgebraicClosure K
  obtain ⟨B, _, M, i, r, m, hB, hgB, hM, hM₁, hM₂, hi, hr, hm, e⟩ :=
    GlobalTheory.SS.PrincIsog.exists_isogeny_kTriv Ω ((Over.pullback (spMap (algebraMap K Ω))).obj A) g (isAbelianScheme_pullback_obj _ A hA) (relDim_pullback _ A hg)
  obtain ⟨Q, i', r', hQ, hi', hr', e'⟩ := GlobalTheory.EighthPowerFactor.exists_polAV_hypS_retract Ω B g hB hgB M hM hM₁ hM₂
  obtain ⟨L₁, f₁, B₁, _, eB, hB₁, heB⟩ := GlobalTheory.exists_finite_isAbelianScheme_descends K Ω B hB
  have lev := GlobalTheory.nonempty_level_of_isAlgClosed Ω Q 1 (Units.map (algebraMap L₁ Ω).toMonoidHom 1) (by simp)
    (by rw [map_one]; exact IsPrimitiveRoot.one)
  obtain ⟨F, _, _, j, R₀, Q₀, χ, hfg, hfr, -, pC, hQ₀, -⟩ := GlobalTheory.SymLevelDescent.descends_to_fg_field L₁ Ω Q 1 1 hQ lev
  letI : Algebra F Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₁ F Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) L₁
  haveI : Algebra.IsAlgebraic L₁ F := Algebra.IsAlgebraic.of_injective j j.toRingHom.injective
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := L₁) F
  have f₂ : FiniteDimensional L₁ F := finite_of_fg R₀ hfg hfr
  let c₀ : K →+* F := (algebraMap L₁ F).comp (algebraMap K L₁)
  have pB₁ : IsGrpPullback B B₁ (spMap (algebraMap L₁ Ω)) _ :=
    ((isGrpPullback_of_iso eB.symm).comp (isGrpPullback_pullback B₁ _)).congr (Category.id_comp _) rfl
  have hgB₁ : SmoothOfRelativeDimension g B₁.hom :=
    (GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend L₁ Ω _ B₁ B _ pB₁ hB).2 g hgB
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K Ω)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => j.commutes (algebraMap K L₁ x)) rfl)
  obtain ⟨b, hb, -⟩ := grpPullback_iso pB₁
    (((isGrpPullback_pullback _ (spMap (algebraMap F Ω))).comp
      (isGrpPullback_pullback B₁ (spMap (algebraMap L₁ F)))).congr (spMap_comp _ _ _ fun x => j.commutes x) rfl)
  have P₁ : Pair _ B m := ⟨i, r, hi, hr, e⟩
  have P₂ : Pair Q.A B 1 := ⟨r', i', hr', hi', by rw [e', pow_one]⟩
  obtain ⟨L, Q', f₃, hQ', P₃, P₄⟩ := exists_finite_pairs Q₀ hQ₀ (isAbelianScheme_pullback_obj (spMap c₀) A hA)
    (isAbelianScheme_pullback_obj (spMap (algebraMap L₁ F)) B₁ hB₁) (isGrpPullback_pullback _ _)
    (isGrpPullback_pullback _ _) pC (P₁.of_iso a.symm b.symm) (P₂.of_iso (Iso.refl _) b.symm)
  obtain ⟨a', ha', -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap ((algebraMap F L).comp c₀)))
    (((isGrpPullback_pullback _ (spMap (algebraMap F L))).comp (isGrpPullback_pullback A (spMap c₀))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  exact ⟨L, inferInstance, (algebraMap F L).comp c₀, _, inferInstance, Q', m,
    (RingHom.finite_algebraMap.2 f₃).comp ((RingHom.finite_algebraMap.2 f₂).comp (RingHom.finite_algebraMap.2 f₁)),
    relDim_pullback _ _ (relDim_pullback _ _ hgB₁), hm, P₃.of_iso a' (Iso.refl _), P₄, hQ'⟩

theorem exists_isogenous_retract : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  intro K _ _ A _ hA
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨L₀, _, _, f₀, hP⟩ := GlobalTheory.ProjFinite.exists_finite_isProjBy K A hA
  haveI : CharZero L₀ := charZero_of_injective_algebraMap (algebraMap K L₀).injective
  obtain ⟨L, _, c, B, _, Q, m, hc, hgB, hm, P₁, ⟨r', i', hr', hi', e'⟩, hQ⟩ := exists_finite_data L₀ _
    (isAbelianScheme_pullback_obj (spMap (algebraMap K L₀)) A hA) g
    (relDim_pullback _ _ hg)
  letI : Algebra K L := (c.comp (algebraMap K L₀)).toAlgebra
  have f : FiniteDimensional K L := hc.comp (RingHom.finite_algebraMap.2 f₀)
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_pullback A (spMap (algebraMap K L)))
    (((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback A (spMap (algebraMap K L₀)))).congr
      (spMap_comp _ _ _ fun x => rfl) rfl)
  obtain ⟨i, r, hi, hr, e⟩ := P₁.of_iso a (Iso.refl _)
  have gp := ((isGrpPullback_of_iso a).comp (isGrpPullback_pullback _ (spMap c))).congr (Category.id_comp _) rfl
  exact ⟨L, inferInstance, inferInstance, f, B, inferInstance, Q, g, m, i, r, i', r',
    GlobalTheory.AbLaw.isProjBy_baseChange L₀ L c _ _ _ _ _ gp.1 hP,
    relDim_pullback _ _ hg, hgB, hi, hr, hm, e, hi', hr',
    by rw [e', pow_one], hQ⟩

end GlobalTheory.FiniteData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFami
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitValue
open GlobalTheory.TorusExt GlobalTheory.UT.WeightValue GlobalTheory.UT.CoefBasic

theorem not_all_ne_zero {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {v : AddValuation F (WithTop ℚ)} {X : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} (hn : 2 ≤ n) (hvn : v (n : F) = 0) {a : X → F}
    (ha : NullV v a) (h0 : ∀ χ, 0 ≤ v (a χ)) {α : X} (hα : v (a α) = 0)
    (H : ∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) →
      ∃ S, SumV v (fun χ => (t (Multiplicative.ofAdd χ)).val * a χ) S ∧ v S ≠ 0) : False := by
  classical
  choose! S hS hS0 using H
  have hroot : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → ∀ χ, v (t χ).val = 0 ∧ v ((t χ)⁻¹).val = 0 := by
    intro t k ht χ
    have e : t χ ^ n ^ k = 1 := by rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
    have hN : 0 < n ^ k := pow_pos (by omega) k
    exact ⟨GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]),
      GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, inv_pow, e, inv_one, Units.val_one])⟩
  have hpos : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → 0 < v (S t) := fun t k ht =>
    lt_of_le_of_ne (le_of_sumV (q := 0) (hS t ⟨k, ht⟩) fun χ => by
      rw [v.map_mul, (hroot t k ht _).1, zero_add]; exact h0 χ) (hS0 t ⟨k, ht⟩).symm
  obtain ⟨k, hk⟩ := GlobalTheory.coeff_recovery_by_torsion_averages F v X n hn hvn a ha S hS (fun _ => α)
    (fun _ => ⟨0, by simp⟩) (a α) (Or.inl ⟨α, fun _ => ⟨0, by simp⟩, rfl⟩) 1
  have h1 := hk k le_rfl
  have hN : 0 < n ^ k := pow_pos (by omega) k
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : 0 < v (((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
      ((t.1 (Multiplicative.ofAdd α))⁻¹).val * S t.1) := by
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hvn, zero_add]
    refine v.map_lt_sum WithTop.zero_ne_top fun t _ => ?_
    rw [v.map_mul, (hroot t.1 k t.2 _).2, zero_add]
    exact hpos t.1 k t.2
  have h3 := v.map_lt_add (lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) h1) h2
  rw [sub_add_cancel, hα] at h3
  exact lt_irrefl _ h3

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem exists_frm_zero (k : ℕ) (g : GtPtF D.toPre F) : ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ GenV hϖ hv w 0 := by
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F k g).1
  obtain ⟨r, φ₀, hφ, t₀, ht₀, x, hx, e⟩ := CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hx0 : x ≠ 0 := v.ne_top_iff.1 (by rw [hx]; exact WithTop.coe_ne_top)
  obtain ⟨w', hw', e'⟩ := TorsionValue.exists_frm_scale w hw (inv_ne_zero hx0)
  refine ⟨w', hw', φ₀, hφ, t₀, ht₀, 1, v.map_one, fun z J hJ => ?_⟩
  rw [e' z J hJ, e z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, cst_eq, ← map_mul, inv_mul_cancel₀ hx0]

theorem exists_frm_cast {k : ℕ} {b b' : TF (R := V) F ⟶ D.toPre.P.A} (hb : b' = b) (w : Frm D.toPre F k b) (hw : w.IsGen)
    (h0 : GenV hϖ hv w 0) : ∃ w' : Frm D.toPre F k b', w'.IsGen ∧ GenV hϖ hv w' 0 ∧
      ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J := by
  subst hb
  exact ⟨w, hw, h0, fun _ _ _ => rfl⟩

end


attribute [local instance] gtGroup in
theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN k n hk hn hnV t s α hts hint hprim
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have : CharZero (FractionRing V) := IsFractionRing.charZero V
  have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
  obtain ⟨i, g, o, ho, hgo, hg⟩ := _root_.GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k n hk hn hnV s α
    (hint α) hprim
  have hgi : n ^ i • g = 0 := ((isNsmul_iff_eq _ _ _).1 hgo).symm.trans ((isZero_iff_eq _).1 ho)
  obtain ⟨w, hw, hw0⟩ := exists_frm_zero (hϖ := hϖ) (hv := hv) k g
  have hB := D.tau_bimult
  have hiota0 : ∀ (h : GtPtF D.toPre F), h.IsZero → h.IsIota 0 := by
    intro h hh
    obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
    refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have face : ∀ x z, th D.toPre (T := TF (R := V) F) y J 1 x z = 1 := by
      intro x z
      have e := val_corr hJ (D.toPre.cub.face 0) (lift x z).left
      rw [val_one] at e
      refine Eq.trans ?_ e
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x z) hJ (pzero _ _) (x2 _ 0) (x2 _ 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let qkMk (g : GtPtF D.toPre F) {k : ℕ} (h : k • g = 0) : QkPt D.toPre F k :=
    ⟨0, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, hiota0 _ ((isZero_iff_eq _).2 h)⟩
  have hgV : ∀ χ, GenV hϖ hv (g.s χ) 0 := fun χ => by
    have e := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (Nat.one_le_pow i n hn.pos)
      (qkMk g hgi) χ
    simpa only [qkMk, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div] using e
  have hvn : v (n : F) = 0 := by
    have e := GC.v_alg_unit hv hnV.unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at e
  refine not_all_ne_zero (v := v) (a := coef s g w) (α := α) hn.two_le hvn
    (((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv g).2.2.2.2.2.2 k hk1 w s hw).1)
    (fun χ => by simpa using CoefVal.le_v_coef hw (hint χ) (hgV χ) hw0) (hg w hw hw0) ?_
  rintro τ ⟨m, hm⟩
  have hj : 1 ≤ n ^ (i + m + 2) := Nat.one_le_pow _ n hn.pos
  let p : QkPt D.toPre F (n ^ (i + m + 2)) := qkMk (g + torusPt D.toPre F (Additive.ofMul τ)) (by
    have e₁ : n ^ (i + m + 2) • g = 0 := by rw [add_assoc, pow_add, mul_comm, mul_smul, hgi, smul_zero]
    have e₂ : τ ^ n ^ (i + m + 2) = 1 := by
      rw [show i + m + 2 = m + (i + 2) by ring, pow_add, pow_mul, hm, one_pow]
    rw [smul_add, e₁, ← map_nsmul, ← ofMul_pow, e₂, ofMul_one, map_zero, add_zero])
  obtain ⟨f, hf, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA D A G hG U F _ hj
  have hx : QkToAkU U.toUnifPre F _ p (f p) := (hf p _).2 rfl
  have hex : ∃ e c, IsTorsFrame A ρ (n ^ (i + m + 2)) (f p) e ∧ ValAt t (f p) e c ∧ v c ≠ 0 := by
    by_contra h
    refine hcon ⟨i + m + 2, f p, by omega, ⟨p, rfl, hx⟩, fun e c he hc => ?_⟩
    by_contra h'
    exact h ⟨e, c, he, hc, h'⟩
  obtain ⟨e, c, he, hc, hc0⟩ := hex
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN _ hj p _ hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / ((n ^ (i + m + 2) : ℕ) : ℚ) ^ 2) = 0 := by
      rw [show p.y = 0 from by simp only [p, qkMk], QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w₂, hw₂, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw₂0 : GenV hϖ hv w₂ 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w₂) c := hsum k hk1 w₂ ⟨hw₂, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hb : p.g.b = g.b := by
    simp only [p, qkMk, add_b, torusPt_b, _root_.mul_one]
  obtain ⟨w', hw', hw'0, hww⟩ := exists_frm_cast hb w hw hw0
  obtain ⟨u, hu, huv, huc⟩ := ((coef_basic V D.toPre F k p.g).2.2 w₂ hw₂).2.2.1 w' hw'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hu)
  have r0 : r = 0 := by
    have := CoefVal.sep D
    exact CoefVal.genV_unique D.toPre.P.isLB (genV_smul hw₂0 hr.symm huv) hw'0
  have hu0 : v u = 0 := by rw [← hr, r0]; rfl
  have htr := ((coef_basic V D.toPre F k g).2.2 w hw).2.2.2 τ _ p.g w'
    ((isTor_iff _ _).2 (isTorusPtF_torusPt τ)) ((isAdd_iff_eq _ _ _).2 (by simp only [p, qkMk])) hww s
  refine ⟨u * c, ?_, by rwa [v.map_mul, hu0, zero_add]⟩
  have := sumV_mul hS hu0
  simpa only [← huc, htr] using this

end GlobalTheory.OneBasis.UnitValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralFamilyValuesTorsionTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis

theorem integral_value_at_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk x e t s c hp he hts hs hc
  obtain ⟨p, hy, hx⟩ := hp
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ :=
    GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / (n : ℚ) ^ 2) = 0 := by rw [hy, QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w, hw, hwv⟩ := WeightValue.exists_pow k (WeightValue.line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := WeightValue.genV_pow k (WeightValue.line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w) c := hsum k hk w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hg := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ hn p
  refine WeightValue.le_of_sumV (q := 0) hS fun β => ?_
  have h := CoefVal.le_v_coef hw (hs β) (hg β) hw0
  have b0 : QForm.bOf D.toPre Q p.y β = 0 := by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  simpa [b0] using h

end GlobalTheory.OneBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExistsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) := by
  first | exact @GlobalTheory.TestFibre.CombValue.valIs_linear | exact GlobalTheory.TestFibre.CombValue.valIs_linear | (intros; apply GlobalTheory.TestFibre.CombValue.valIs_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  first | exact @GlobalTheory.TestFibre.act_normPull_smul | exact GlobalTheory.TestFibre.act_normPull_smul | (intros; apply GlobalTheory.TestFibre.act_normPull_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  first | exact @GlobalTheory.TestFibre.perp_torus_point | exact GlobalTheory.TestFibre.perp_torus_point | (intros; apply GlobalTheory.TestFibre.perp_torus_point <;> assumption)
end

