module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem flat_cohomology_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {A B C H H' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R' H']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : ∀ a, g (f a) = 0)
    (θ : LinearMap.ker (g.baseChange R) →ₗ[R] H) (θ' : LinearMap.ker (g.baseChange R') →ₗ[R'] H')
    (hs : Function.Surjective θ) (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R))
    (hs' : Function.Surjective θ') (hk' : ∀ z, θ' z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R'))
    (p : H → H')
    (hp : ∀ z z', z'.1 = (Algebra.ofId R R').toLinearMap.rTensor B z.1 → θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  let Z := LinearMap.ker g
  let f' : A →ₗ[R] Z := f.codRestrict Z hfg
  let i : Z →ₗ[R] LinearMap.ker (g.baseChange R) :=
    ((TensorProduct.mk R R B 1) ∘ₗ Z.subtype).codRestrict _ (fun z ↦ by
      have : g z.1 = 0 := z.2
      simp [this])
  have hi : ∀ z : Z, (i z).1 = (1 : R) ⊗ₜ[R] z.1 := fun z ↦ rfl
  have his : Function.Surjective i := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := (TensorProduct.lid R B).symm.surjective x
    have hb : g b = 0 := by
      have h1 : (1 : R) ⊗ₜ[R] g b = 0 := by simpa using hx
      have := congrArg (TensorProduct.lid R C) h1
      simpa using this
    exact ⟨⟨b, hb⟩, Subtype.ext (by simp [hi])⟩
  let τ : Z →ₗ[R] H := θ ∘ₗ i
  have hτs : Function.Surjective τ := hs.comp his
  have hex : Function.Exact f' τ := by
    intro z
    change θ (i z) = 0 ↔ _
    rw [hk, hi]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (TensorProduct.lid R A).symm.surjective x
      refine ⟨a, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid R B) hx
      change f a = z.1
      simpa using this
    · rintro ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, rfl⟩
  have hexZ : Function.Exact (Z.subtype.baseChange R') (g.baseChange R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective (Z.subtype.baseChange R') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') Z.subtype Z.subtype_injective
  let j : R' ⊗[R] Z →ₗ[R'] LinearMap.ker (g.baseChange R') :=
    (Z.subtype.baseChange R').codRestrict _ (fun x ↦ hexZ.apply_apply_eq_zero x)
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (hexZ x).1 hx
    exact ⟨y, rfl⟩
  let a : R' ⊗[R] Z →ₗ[R'] R' ⊗[R] H := τ.baseChange R'
  let b : R' ⊗[R] Z →ₗ[R'] H' := θ' ∘ₗ j
  have has : Function.Surjective a := LinearMap.lTensor_surjective R' hτs
  have hbs : Function.Surjective b := hs'.comp hjs
  have hexa : Function.Exact (f'.baseChange R') a := lTensor_exact R' hex hτs
  have hcomp : ∀ y, Z.subtype.baseChange R' (f'.baseChange R' y) = f.baseChange R' y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hexa x]
    change _ ↔ θ' (j x) = 0
    rw [hk']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hcomp y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj ((hcomp y).trans hy)⟩
  refine ⟨(a.quotKerEquivOfSurjective has).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    b.quotKerEquivOfSurjective hbs, fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hτs c
  have h1 : (a.quotKerEquivOfSurjective has).symm ((1 : R') ⊗ₜ[R] τ z) =
      Submodule.Quotient.mk ((1 : R') ⊗ₜ[R] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  change θ' (j (1 ⊗ₜ z)) = p (θ (i z))
  apply hp
  rw [hi, LinearMap.rTensor_tmul]
  change (1 : R') ⊗ₜ[R] z.1 = (algebraMap R R' 1) ⊗ₜ[R] z.1
  rw [map_one]

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

theorem flat_baseChange_HO : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  intro R R' _ _ _ _ X X' s s' φ h hsep hqc
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affine_cover s
  obtain ⟨M⟩ := _root_.GlobalTheory.CechPoset.model_cechLB R X s (Fin n) D hsep hD hcov
  generalize GlobalTheory.AbLaw.cechLB s (LB.triv X) D = K at M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    have e : spMap (algebraMap R R) = 𝟙 _ := spMap_id R
    rw [e]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdd : ∀ i j k a, (K.d j k).hom ((K.d i j).hom a) = 0 := by
    intro i j k a
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  obtain ⟨a1, a2, a3, a4⟩ := M.exact h0
  obtain ⟨b1, b2, b3, b4⟩ := M.exact h
  obtain ⟨c1, c2⟩ := M.nat h0 h (Algebra.ofId R R') φ h.w (Category.comp_id φ)
  exact ⟨flat_cohomology_baseChange _ _ (hdd 0 1 2) (M.θ1 h0) (M.θ1 h) a1 a2 b1 b2 _ c1,
    flat_cohomology_baseChange _ _ (hdd 1 2 3) (M.θ2 h0) (M.θ2 h) a3 a4 b3 b4 _ c2⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.DvrAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar
section
open GlobalTheory.UT.CoefUnit GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallPoint GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallZero GlobalTheory.UT.CoefBasic GlobalTheory.UT.SmallPoint

end
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar GlobalTheory.UT.MixedConv GlobalTheory.FieldBaseChange
section CoreAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end CoreAny
section FieldAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

end FieldAny

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

theorem qkToAkU_level_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN p q x hy hg hx
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
  have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
    (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
  obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk p x x₀ hx a
  exact (indAtTransl_any hL R I hI D A G hG U F N hN1 q x).1 (h₀ n N hn hN q hy hg)

end GlobalTheory.DvrAnyChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivations
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem surjective_pi_liftKaehler_of_pointwise {K B J : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype J] [DecidableEq J]
    (d : J → Derivation K B B)
    (h : ∀ m : Ideal B, m.IsMaximal → ∃ e : B →ₐ[K] K, (∀ b, e b = 0 → b ∈ m) ∧
      ∀ w : J → K, (∀ x, ∑ a, e (d a x) * w a = 0) → w = 0) :
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  rw [← LinearMap.range_eq_top]
  by_contra hN
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom
    (LinearMap.range (LinearMap.pi fun a => (d a).liftKaehlerDifferential))).resolve_left hN
  have hs : IsSimpleModule B ((J → B) ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨e, he, hw⟩ := h (Module.annihilator B ((J → B) ⧸ M)) IsSimpleModule.annihilator_isMaximal
  let φ : B →ₗ[K] (J → K) := LinearMap.pi fun a => e.toLinearMap ∘ₗ (d a).toLinearMap
  have hφ : LinearMap.range φ = ⊤ := by
    by_contra hφ
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hφ)
    have hfy : ∀ y : J → K, f y = ∑ a, y a * f (Pi.single a 1) := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ' y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    have h0 := hw (fun a => f (Pi.single a 1)) fun x => by
      have : f (φ x) = 0 := hf ⟨x, rfl⟩
      rw [hfy] at this
      exact this
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfy]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [congrFun h0 a]
    simp
  apply hM.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hφ fun a => e (y a)
  have h1 : (fun a => d a x) ∈ M := by
    refine hle ⟨KaehlerDifferential.D K B x, ?_⟩
    funext a
    simp
  have h2 : y - (fun a => d a x) ∈ M := by
    rw [pi_eq_sum_univ' (y - fun a => d a x)]
    refine M.sum_mem fun a _ => ?_
    have hm : (y - fun a => d a x) a ∈ Module.annihilator B ((J → B) ⧸ M) := by
      apply he
      have : e (d a x) = e (y a) := congrFun hx a
      simp [this]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hm _
  simpa using M.add_mem h2 h1

theorem surjective_pi_liftKaehler_coord : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)),
    (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) →
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  intro A _ g L u hA U d hd
  refine surjective_pi_liftKaehler_of_pointwise d fun m hm => ?_
  obtain ⟨z, hz, hm'⟩ := _root_.GlobalTheory.MaxPoints.main A g L u hA U.1 U.2 m hm
  obtain ⟨e, he⟩ := (_root_.GlobalTheory.CechPer.pre_val_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
  refine ⟨e, fun b hb => (hm' b).2 ((he b).trans hb), fun w hw => ?_⟩
  refine _root_.GlobalTheory.CechPerImm.main A g L u hA U.1 U.2 z hz w fun b => ?_
  rw [← hw b]
  conv_lhs => rw [pi_eq_sum_univ' w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (· * w a) ((hd a b z hz).symm.trans (he _))

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackPrimitiveCrystallineClassEpsPartI
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem snd_epsHom {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z : DualNumber D) : (epsHom φ z).snd = φ z.snd := by
  simp only [epsHom, DualNumber.lift_apply_apply, AlgHom.comp_apply,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_add, DualNumber.snd_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, DualNumber.fst_eps, DualNumber.snd_eps,
    _root_.mul_one, mul_zero, add_zero, zero_add]

theorem epsHom_comp_inl {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ := by
  exact DualNumber.lift_comp_inlHom _

theorem epsHom_comp_epsMap {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') :
    (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' := by
  apply DualNumber.algHom_ext
  simp only [AlgHom.comp_apply, epsHom, EpsWeil.epsMap, DualNumber.lift_apply_eps]

theorem ptV_eq {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B) {D : Type} [CommRing D] [Algebra R D]
    (x : Pt A D) : ptV v x =
      (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x : Pt (A ⊗ B) (DualNumber D)) *
      (spOver (EpsWeil.epsMap R D) ≫ CartesianMonoidalCategory.lift 1 v) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [ptV, pt0, MonObj.mul_comp, comp_lift, MonObj.comp_one]

theorem specOverOfAlgHom_comp_pointWithZeroSecondCoord {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {D D' : Type} [CommRing D] [Algebra R D] [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver φ ≫ pt0 B x : Pt (A ⊗ B) D') = pt0 B (spOver φ ≫ x : Pt A D') := by
  simp [pt0, comp_lift]

theorem cohom_sndPull_zero : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) →
    ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  intro R _ A B _ _ f hf v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R (A ⊗ B) f hf
  have hc := (fv_isCoc_and_ev_eq R (A ⊗ B) f).1
  let V1 : Pt (A ⊗ B) (DualNumber R) := CartesianMonoidalCategory.lift 1 v
  refine ⟨fun D _ _ x ↦ (g (DualNumber D) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
      (spOver (EpsWeil.epsMap R D) ≫ V1) +
      fv f D (DualNumber D) (TrivSqZeroExt.inlAlgHom R D D) (pt0 B x) +
      fv f (DualNumber R) (DualNumber D) (EpsWeil.epsMap R D) V1).snd, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := hg (DualNumber D) (DualNumber D') (epsHom φ) (spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x)
    (spOver (EpsWeil.epsMap R D) ≫ V1)
  rw [← ptV_eq] at e1
  have hX : (spOver (epsHom φ) ≫ spOver (TrivSqZeroExt.inlAlgHom R D D) ≫ pt0 B x :
      Pt (A ⊗ B) (DualNumber D')) =
      spOver (TrivSqZeroExt.inlAlgHom R D' D') ≫ pt0 B (spOver φ ≫ x : Pt A D') := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_inl, ← spOver_comp, Category.assoc, specOverOfAlgHom_comp_pointWithZeroSecondCoord]
  have hV : (spOver (epsHom φ) ≫ spOver (EpsWeil.epsMap R D) ≫ V1 :
      Pt (A ⊗ B) (DualNumber D')) = spOver (EpsWeil.epsMap R D') ≫ V1 := by
    rw [← Category.assoc, spOver_comp, epsHom_comp_epsMap]
  rw [hX, hV] at e1
  have c1 := hc D (DualNumber D) (DualNumber D') (TrivSqZeroExt.inlAlgHom R D D) (epsHom φ) (pt0 B x)
    (sm_whole _)
  have c2 := hc D D' (DualNumber D') φ (TrivSqZeroExt.inlAlgHom R D' D') (pt0 B x) (sm_whole _)
  rw [epsHom_comp_inl, c2, specOverOfAlgHom_comp_pointWithZeroSecondCoord] at c1
  have c3 := hc (DualNumber R) (DualNumber D) (DualNumber D') (EpsWeil.epsMap R D) (epsHom φ) V1 (sm_whole _)
  rw [epsHom_comp_epsMap] at c3
  have s1 := congrArg TrivSqZeroExt.snd e1
  have s2 := congrArg TrivSqZeroExt.snd c1
  have s3 := congrArg TrivSqZeroExt.snd c3
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, snd_epsHom,
    TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.snd_inl, zero_add] at s1 s2 s3
  simp only [Fn1.add, Fn1.neg, Fn1.zero, sndPull, neg_zero, add_zero, TrivSqZeroExt.snd_add, map_add (f := _)]
  linear_combination -s1 - s2 - s3

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBasePeriodsFactorMulGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautologicalBase_periods_factor_mul_generator : ∀ {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : GlobalTheory.PolDeg.TautBase o W) (iw : W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → ∀ a b : Q.X, ∃ k : (FractionRing V)ˣ, (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧ Q.TauCoord a b k := by
  first | exact @GlobalTheory.TautTau.tauCoord_of_dataFrom | exact GlobalTheory.TautTau.tauCoord_of_dataFrom | (intros; apply GlobalTheory.TautTau.tauCoord_of_dataFrom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (S : Over (Spec (CommRingCat.of R))) (z : S.left) (J : (S.left ⟶ D.P.A.left) → D.P.L.ι) (J' : (S.left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ x x' y : S ⟶ D'.P.A, (let om := fun p : S ⟶ D'.P.A => gm p.left z _ (T.w.s (fun k => J (p.left ≫ tensφ T.pr k), J' p.left)); cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ k : (Fin r × Fin r) × Fin 4, cubV D.cub z J (x ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (x' ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) (y ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2) ^ tensε W k) := by
  first | exact @GlobalTheory.TensCub.cubV_tens | exact GlobalTheory.TensCub.cubV_tens | (intros; apply GlobalTheory.TensCub.cubV_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_preimage_eq_closedImmersion_preimage : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0}) (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y), (∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e) → ∀ (V : G'.left.Opens) (W : Y.Opens), φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V → ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  first | exact @GlobalTheory.Mum.thick_preimage_eq | exact GlobalTheory.Mum.thick_preimage_eq | (intros; apply GlobalTheory.Mum.thick_preimage_eq <;> assumption)
end

