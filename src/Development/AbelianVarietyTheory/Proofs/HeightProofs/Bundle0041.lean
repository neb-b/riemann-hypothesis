module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmExistsOnOfPointCarriesObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

theorem exists_cmObj_extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ p q) (j : K →+* K') (σ' : K' →+* ℂ)
    (h : σ'.comp j = σ) :
    ∃ (X' : CMObj H K' (RingOfIntegers.mapRingHom j ρ) σ' p q)
      (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
      (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
      X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := by
  set f := RingOfIntegers.mapRingHom j with hf
  have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
  choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
  obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
  have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
  choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
  have hpt := spMap_int j h
  refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K' j X.split |>.1
            ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
            A := A', B := B'
            typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
            typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
            typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
            hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
  · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
    have e := congrArg Over.Hom.left ((X.lin i).2 c)
    simp only [Over.comp_left] at e
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
      (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
  · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
    choose pA hA using fun b => exists_ptEquiv (a b) hpt
    obtain ⟨x, hx⟩ := X.onto (pB y)
    refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
    rw [hx, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    apply Over.OverMorphism.ext
    simp only [Function.comp_apply]
    rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
    erw [hφ]
    rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
  · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
      (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
      ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
    rw [hpt]
    exact X.weil i

end Extend

section Conclusions

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe}

variable {Xo} {Z : CMLat hP D.p D.q} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
  {K' : Type} [Field K'] [NumberField K'] {κ : KA l →+* K'} {σ' : K' →+* ℂ} {k : IntermediateField ℚ ℂ}

end Conclusions

section ChangeOfExp

variable {D₁ D₂ : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)}

end ChangeOfExp

section Point

end Point

section Tensor

end Tensor

end GlobalTheory.CMExistsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFinsetContainsRayField
section
open NumberField IsDedekindDomain GlobalTheory.Mem

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RayOnto

theorem containsRayField_comp {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

theorem exists_finset_containsRayField : GlobalTheory.NT.RayField → ∀ (P : Pre) (M : ℕ), M ≠ 0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (φ : P.host.K →+* L), σ.comp φ = P.host.φ₀.comp (algebraMap P.host.K P.host.E) → (∀ z ∈ S, ∃ x, σ x = z) → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ M := by
  intro hR P M hM
  let φK : P.host.K →+* ℂ := P.host.φ₀.comp (algebraMap P.host.K P.host.E)
  obtain ⟨Rf, hRf⟩ := GlobalTheory.Mem.Fld.exists_isRayFieldIn φK hR (GlobalTheory.Mem.Fld.natIdeal_ne_bot (E := P.host.K) hM)
  haveI : NumberField Rf := hRf.numberField
  let b := Module.finBasis ℚ Rf
  refine ⟨Finset.univ.image (fun i => (b i : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    have h : IsAlgebraic ℚ (b i) := Algebra.IsAlgebraic.isAlgebraic _
    exact h.algHom Rf.val
  · intro L _ _ σ φ hσφ hS
    obtain ⟨hm, hNF, hray⟩ := hRf
    letI := GlobalTheory.Mem.Fld.algOf φK Rf hm
    obtain ⟨hab, hun, -, hart⟩ := hray
    haveI : IsGalois P.host.K Rf := hab.toIsGalois
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.K Rf) M :=
      GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (K := P.host.K) (L := Rf) M hun
        (fun I hI hc hχ => (hart I hI hc).1 hχ)
    have hle : Rf ≤ σ.toRatAlgHom.fieldRange := by
      intro z hz
      have hsum := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
      rw [IntermediateField.coe_sum] at hsum
      simp only [IntermediateField.coe_smul] at hsum
      rw [← hsum]
      refine sum_mem fun i _ => IntermediateField.smul_mem _ ?_
      obtain ⟨y, hy⟩ := hS (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact ⟨y, hy⟩
    let e : L ≃ₐ[ℚ] σ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField σ.toRatAlgHom
    let τ : Rf →+* L := (e.symm : σ.toRatAlgHom.fieldRange →+* L).comp
      (IntermediateField.inclusion hle : Rf →+* σ.toRatAlgHom.fieldRange)
    have key : ∀ w, σ (e.symm w) = (w : ℂ) := fun w => by
      conv_rhs => rw [← e.apply_symm_apply w]
      rfl
    have hτ : τ.comp (algebraMap P.host.K Rf) = φ := by
      ext x
      apply σ.injective
      have h1 : σ (φ x) = φK x := RingHom.congr_fun hσφ x
      rw [h1]
      exact key _
    rw [← hτ]
    exact containsRayField_comp _ τ M hc

end GlobalTheory.RayOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FrobeniusFixesOfSplitsCompletelyIntermediateStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_fixes_of_splitsCompletely_intermediate : ∀ (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K)), {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard = Module.finrank K M → ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x := by
  first | exact @GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | exact GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank | (intros; apply GlobalTheory.SplitCriterion.frob_fix_of_ncard_primes_eq_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ImHermFormEqCurveForm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

namespace GlobalTheory.CMPointCompare

section Dictionary

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} {B G' : Over Y} [GrpObj C] [GrpObj G] [GrpObj B] [GrpObj G']
  {f : Y ⟶ S} {x : Y ⟶ X} {β : B.left ⟶ C.left} {π : G'.left ⟶ G.left}

variable (hβ : IsGrpPullback B C f β) (hπ : IsGrpPullback G' G x π)

end Dictionary

section Intertwine

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} [GrpObj C] [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}
  {Φ : MapOver C G f x}

end Intertwine

section General

open GlobalTheory.CM

theorem hom_ext_of_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {B G : Over (Sp R)} [Smooth B.hom] [IsSeparated G.hom] {a b : B ⟶ G}
    (h : ∀ p : Over.mk (spMap σ) ⟶ B, p ≫ a = p ≫ b) : a = b := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom σ) hσ
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback B.hom (spMap σ)) ?_
  have : IsReduced (pullback B.hom (spMap σ)) :=
    isReduced_of_smooth_complex _ (pullback.snd B.hom (spMap σ)) inferInstance
  refine ComplexPoints.hom_ext_of_points (pullback.snd B.hom (spMap σ)) G.hom (by simp) fun x hx => ?_
  have e := congrArg (fun z => z.left) (h (Over.homMk (x ≫ pullback.fst _ _) (by
    show (x ≫ _) ≫ _ = spMap σ
    rw [Category.assoc, pullback.condition, reassoc_of% hx])))
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

end General

section Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

end Linear

end GlobalTheory.CMPointCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndefiniteUnitaryLieOrthonormalBasesProps
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasBasisFacts

variable {n : ℕ}

lemma inG_iff_entry (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j = true then (1:ℂ) else -1) +
      (if ε i = true then (1:ℂ) else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using this
  · intro h
    ext i j
    simpa [mul_diagonal, diagonal_mul, conjTranspose_apply] using h i j

lemma i_smul_diag_casimir_unit_mem_indefinite_lie (ε : Fin n → Bool) (a : Fin n) : inG ε (Complex.I • unitE a a) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> grind

lemma same_sign_casimir_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε (invSqrtTwo • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma same_sign_casimir_i_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a = ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_sym_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε (invSqrtTwo • (unitE a b + unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma opp_sign_casimir_i_skew_sum_mem_indefinite_lie (ε : Fin n → Bool) (a b : Fin n) (hab : a ≠ b) (he : ε a ≠ ε b) :
    inG ε ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) := by
  rw [inG_iff_entry]
  intro i j
  simp only [unitE, invSqrtTwo, Matrix.single_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma i_smul_diag_casimir_unit_skewHermitian (a : Fin n) : (Complex.I • unitE a a)ᴴ = -(Complex.I • unitE a a) := by
  simp [unitE, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_skew_diff_skewHermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b - unitE b a))ᴴ = -(invSqrtTwo • (unitE a b - unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma casimir_unit_i_sym_sum_skewHermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))ᴴ =
      -((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  ext i j
  simp [Matrix.single_apply]
  split_ifs <;> simp

lemma casimir_unit_sym_sum_hermitian (a b : Fin n) :
    (invSqrtTwo • (unitE a b + unitE b a))ᴴ = invSqrtTwo • (unitE a b + unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single, add_comm]

lemma casimir_unit_i_skew_diff_hermitian (a b : Fin n) :
    ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a))ᴴ =
      (invSqrtTwo * Complex.I) • (unitE a b - unitE b a) := by
  simp [unitE, invSqrtTwo, Matrix.conjTranspose_single]
  module

lemma i_smul_diag_casimir_unit_hs_le_one (a : Fin n) : hs (Complex.I • unitE a a) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(Complex.I • unitE a a) i j‖ ^ 2 = if a = i then (if a = j then 1 else 0) else 0 := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  simp only [this]
  simp

lemma pair_hs (a b : Fin n) (hab : a ≠ b) (c : ℂ) (hc : ‖c‖ ^ 2 = 1 / 2) (t : ℂ) (ht : ‖t‖ = 1) :
    hs (c • (unitE a b + t • unitE b a)) ≤ 1 := by
  unfold hs
  have : ∀ i j, ‖(c • (unitE a b + t • unitE b a)) i j‖ ^ 2 =
      (if a = i then (if b = j then 1 / 2 else 0) else 0) +
        (if b = i then (if a = j then 1 / 2 else 0) else 0) := by
    intro i j
    simp only [unitE, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [norm_mul, mul_pow]
  simp only [this]
  simp [Finset.sum_add_distrib]
  norm_num

lemma norm_sq_invSqrtTwo : ‖invSqrtTwo‖ ^ 2 = 1 / 2 := by
  simp [invSqrtTwo, norm_inv, inv_pow]

lemma casimir_unit_skew_diff_hs_le_one (a b : Fin n) (hab : a ≠ b) : hs (invSqrtTwo • (unitE a b - unitE b a)) ≤ 1 := by
  have e : unitE a b - unitE b a = unitE a b + (-1 : ℂ) • unitE b a := by
    simp [sub_eq_add_neg]
  rw [e]
  exact pair_hs a b hab _ norm_sq_invSqrtTwo _ (by simp)

lemma casimir_unit_i_sym_sum_hs_le_one (a b : Fin n) (hab : a ≠ b) :
    hs ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) ≤ 1 := by
  have e : unitE a b + unitE b a = unitE a b + (1 : ℂ) • unitE b a := by simp
  rw [e]
  exact pair_hs a b hab _ (by rw [norm_mul, mul_pow, norm_sq_invSqrtTwo]; simp) _ (by simp)

lemma mem_pairs {ε : Fin n → Bool} {same : Bool} {a b : Fin n} (h : (a, b) ∈ pairs ε same) :
    a ≠ b ∧ ((ε a = ε b) ↔ same = true) := by
  simp only [pairs, List.mem_filter, List.pair_mem_product, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨ne_of_lt h.1, ?_⟩
  have h2 := h.2
  cases same <;> cases hx : ε a <;> cases hy : ε b <;> simp_all

end GlobalTheory.TypeSum.CasBasisFacts


open GlobalTheory.TypeSum.CasBasisFacts in
theorem GlobalTheory.TypeSum.CasBasis.bases_mem_lie : ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ i, kB ε i ∈ lieSet ε ∧ (kB ε i)ᴴ = -kB ε i ∧ hs (kB ε i) ≤ 1) ∧
      ∀ b, pB ε b ∈ lieSet ε ∧ (pB ε b)ᴴ = pB ε b := by
  intro n ε
  constructor
  · intro i
    have hm : kB ε i ∈ kList ε := List.get_mem _ _
    generalize kB ε i = X at hm ⊢
    simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨a, -, rfl⟩ | ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · exact ⟨i_smul_diag_casimir_unit_mem_indefinite_lie ε a, i_smul_diag_casimir_unit_skewHermitian a, i_smul_diag_casimir_unit_hs_le_one a⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_skew_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_skew_diff_skewHermitian a b, casimir_unit_skew_diff_hs_le_one a b hab⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨same_sign_casimir_i_sym_sum_mem_indefinite_lie ε a b hab (he.2 rfl), casimir_unit_i_sym_sum_skewHermitian a b, casimir_unit_i_sym_sum_hs_le_one a b hab⟩
  · intro i
    have hm : pB ε i ∈ pList ε := List.get_mem _ _
    generalize pB ε i = X at hm ⊢
    simp only [pList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨⟨a, b⟩, hp, rfl | rfl⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_sym_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_sym_sum_hermitian a b⟩
    · obtain ⟨hab, he⟩ := mem_pairs hp
      exact ⟨opp_sign_casimir_i_skew_sum_mem_indefinite_lie ε a b hab (fun h => by simpa using he.1 h), casimir_unit_i_skew_diff_hermitian a b⟩
end

