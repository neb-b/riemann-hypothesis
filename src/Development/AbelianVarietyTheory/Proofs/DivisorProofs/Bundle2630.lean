module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNegStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitFibreIso_comm_neg : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  first | exact @GlobalTheory.ThetaMove.negT_fibre_comm | exact GlobalTheory.ThetaMove.negT_fibre_comm | (intros; apply GlobalTheory.ThetaMove.negT_fibre_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitFibreIso_comm_translation : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  first | exact @GlobalTheory.Mum.trait_transl_comm | exact GlobalTheory.Mum.trait_transl_comm | (intros; apply GlobalTheory.Mum.trait_transl_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLeadValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.trait_lead_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ hB D C Y W _ _ _ T
  obtain ⟨κ, e, h1, h2, h3⟩ := _root_.GlobalTheory.Mum.closedFibre_iso R hB D C Y W T
  refine ⟨κ, e, h1, h2, fun Z p p' y hp hy k u z J J' hJ hJ' => ?_⟩
  obtain ⟨g, ξ', hg, hξ, hP⟩ := h3 Z p p' y hp hy
  exact _root_.GlobalTheory.Mum.RedVal.closedFibre_val R hB D C Y W T Z p' y g ξ' hg hξ hP k u z J J' hJ hJ'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesaw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed_of_relAmple : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  _root_.GlobalTheory.TrivLocus.trivLocus_closed

end GlobalTheory.TrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExpansion_adicSums_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F := by
  first | exact @GlobalTheory.TwFam.texp_sum | exact GlobalTheory.TwFam.texp_sum | (intros; apply GlobalTheory.TwFam.texp_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExpansion_mul_of_memberProducts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  first | exact @GlobalTheory.TwFam.texp_mul_of_prod | exact GlobalTheory.TwFam.texp_mul_of_prod | (intros; apply GlobalTheory.TwFam.texp_mul_of_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  exact @GlobalTheory.TwFac.fac_exists_unique_const
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianPar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.Gen0

section General

variable {X Y : Scheme.{0}}

def fs {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : FreeAbelianGroup (Y ⟶ X) :=
  ∑ k, ε k • FreeAbelianGroup.of (φ k)

theorem formEq_of_fs {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : fs φ ε = fs φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ g
  have e := congrArg (FreeAbelianGroup.lift (fun ψ => Additive.ofMul (g ψ))) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fs, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at e
  apply Additive.ofMul.injective
  simpa [ofMul_prod, ofMul_zpow] using e

theorem oneGen_isGen' (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

def genSub (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAbelianGroup (Y ⟶ X)) where
  carrier := {f | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fs φ ε = f ∧
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp [fs], LB.oneGen L, oneGen_isGen' L⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, rfl, t, ht⟩ ⟨K', _, φ', ε', rfl, t', ht'⟩
    exact ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', by simp [fs, Fintype.sum_sum_type],
      LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, rfl, t, ht⟩
    exact ⟨K, inferInstance, φ, fun k => - ε k, by simp [fs, neg_smul, Finset.sum_neg_distrib],
      LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

variable {L : LB X}

theorem mem_of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : fs φ ε ∈ genSub L Y := ⟨K, inferInstance, φ, ε, rfl, t, ht⟩

theorem gen_of_mem (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : fs φ ε ∈ genSub L Y) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', e, t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL (formEq_of_fs e) t ht
  exact ⟨t', ht'⟩

theorem exists_cl (hL : L.IsLB) (Y : Scheme.{0}) : ∃ (U : Type) (_ : CommGroup U) (c : (Y ⟶ X) → U),
    ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ),
      (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∏ k, c (φ k) ^ ε k = 1 := by
  refine ⟨Multiplicative (FreeAbelianGroup (Y ⟶ X) ⧸ genSub L Y), inferInstance,
    fun ψ => Multiplicative.ofAdd (QuotientAddGroup.mk' _ (FreeAbelianGroup.of ψ)), fun K _ φ ε => ?_⟩
  have e : ∏ k, Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (FreeAbelianGroup.of (φ k))) ^ ε k =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (fs φ ε)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fs, map_sum, map_zsmul, ofAdd_sum, ofAdd_zsmul]
  rw [e, ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨t, ht⟩ => mem_of_gen t ht, gen_of_mem hL⟩

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_gen_twist [IsLocalRing R] (a : D.P.A ⟶ D.P.A) [IsMonHom a] (n j : ℤ) (mu ν δ β : D.X)
    (hν : D.c ν = D.c mu ≫ a) (u : LB.Gen (IotaLB D a ν δ)) (hu : u.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a (β + (n • mu + j • δ)))
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a β k)) (dε n j)), u₀.IsGen := by
  obtain ⟨U, _, c, hc⟩ := exists_cl D.P.isLB D.P.A.left
  have k₀ : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, c (toUnit D.P.A ≫ q).left = 1 := fun q => by
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := PUnit) (fun _ => q.left) (fun _ => 1)
    have h := (hc PUnit (fun _ => (toUnit D.P.A).left ≫ q.left) (fun _ => 1)).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩
    rw [Fintype.prod_unique, zpow_one] at h
    exact h
  have k₁ : c (1 : D.P.A ⟶ D.P.A).left = 1 := k₀ _
  have k₂ : ∀ χ, c (DVR.cP D D.P.A χ).left = 1 := fun χ => k₀ _
  have sq : ∀ χ χ', c (𝟙 _ * DVR.cP D D.P.A (χ + χ')).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
      c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (c (𝟙 _ * DVR.cP D D.P.A χ').left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ χ' => by
    have h := (prod_cub (𝟙 D.P.A) (DVR.cP D _ χ) (DVR.cP D _ χ') c).symm.trans ((hc thK _ thε).1
      ⟨LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t _, DVR.pullGen_isGen _ _ _ _ D.cub.isGen _⟩)
    rw [_root_.mul_assoc (𝟙 D.P.A), ← DVR.cPoint_add, k₂, k₂, k₂, k₁] at h
    rw [← div_eq_one, ← h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
    abel
  let Φ : D.X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul
    (c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)) (fun χ χ' => congrArg Additive.ofMul (sq χ χ'))
  have e : ∀ χ, Additive.ofMul (c (𝟙 _ * DVR.cP D D.P.A χ).left) =
      Φ χ + Additive.ofMul (c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ =>
    congrArg Additive.ofMul (div_mul_cancel _ _).symm
  clear_value Φ
  have e₃ : Additive.ofMul (c (a * DVR.cP D _ ν).left) = Φ δ + Additive.ofMul (c a.left) := by
    have h := (hc _ _ _).1 ⟨u, hu⟩
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four] at h
    have h' : c (𝟙 _ * DVR.cP D D.P.A δ).left ^ (1 : ℤ) * c (DVR.cP D D.P.A δ).left ^ (-1 : ℤ) *
        c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        (c (a * DVR.cP D D.P.A ν).left ^ (-1 : ℤ) * c (DVR.cP D D.P.A ν).left ^ (1 : ℤ) * c a.left ^ (1 : ℤ) *
          c (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = 1 := h
    have h'' := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, ofMul_one] at h''
    rw [eq_comm, ← sub_eq_zero, ← h'']
    module
  let T : D.P.A ⟶ D.P.A := 𝟙 _ * DVR.cP D _ mu
  have i₀ : T ≫ 𝟙 _ = 𝟙 _ * DVR.cP D _ mu := Category.comp_id _
  have i₁ : T ≫ (𝟙 _ * DVR.cP D _ β) = 𝟙 _ * DVR.cP D _ (mu + β) := by
    rw [MonObj.comp_mul, DVR.comp_cP, i₀, DVR.cPoint_add, _root_.mul_assoc]
  have i₂ : T ≫ DVR.cP D _ β = DVR.cP D _ β := DVR.comp_cP D _ _
  have i₃ : T ≫ (1 : D.P.A ⟶ D.P.A) = 1 := MonObj.comp_one _
  have i₄ : T ≫ a = a * DVR.cP D _ ν := by
    rw [MonObj.mul_comp, Category.id_comp, DVR.cP, DVR.cP, hν, Category.assoc]
  have h : c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * c (𝟙 _ * DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (1 : ℤ) *
      c (DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * c a.left ^ j *
      (c (T ≫ 𝟙 _).left ^ (-(n - 1)) * c (T ≫ (𝟙 _ * DVR.cP D _ β)).left ^ (-1 : ℤ) *
        c (T ≫ DVR.cP D _ β).left ^ (-(-1) : ℤ) * c (T ≫ (1 : D.P.A ⟶ D.P.A)).left ^ (-1 : ℤ) * c (T ≫ a).left ^ (-j)) = 1 := by
    rw [i₀, i₁, i₂, i₃, i₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, e₃, ofMul_one, map_add (f := _), map_zsmul]
    module
  refine (hc _ _ _).2 ?_
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_five]
  exact h

end Deg

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  intro R _ _ _ hR D a a' h h' hE n j mu β β' hβ
  obtain ⟨u, hu, -⟩ := exists_iota R hR D a a' h h' hE (h mu)
  haveI := hE.1
  subst hβ
  exact exists_gen_twist D.toPre a n j mu (h mu) (h' (h mu)) β (hE.2.2.2.1 mu) u hu

end GlobalTheory.TwFam.Gen0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericCube

theorem exists_iso_section {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X} (g : H ⟶ Y)
    (hg : g ≫ f = 𝟙 H) (w : LB.Iso (M.pull f) (L.pull ψ)) (hw : w.IsGen) :
    ∃ w' : LB.Iso M (L.pull (g ≫ ψ)), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) := by
  have mm : ∀ (y : H) (k : M.ι), y ∈ M.U k → g y ∈ (M.pull f).U (fun _ => k) := fun y k hy => mem_pull.2 (by
    have e : (g ≫ f) y = y := by rw [hg]; rfl
    exact (congrArg (· ∈ M.U k) e).mpr hy)
  have le : ∀ (j : L.ι) (k : M.ι), (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k ≤
      g ⁻¹ᵁ ((L.pull ψ).U (fun _ => j) ⊓ (M.pull f).U (fun _ => k)) := fun j k y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.1), mm y k hy.2⟩
  let w' : LB.Iso M (L.pull (g ≫ ψ)) :=
    ⟨fun p => res (le (p.1 PUnit.unit) p.2) (pullU g _ (w.s (fun _ => p.1 PUnit.unit, fun _ => p.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) :=
    fun Z r z j k hj hk => by
      have m : r z ∈ (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k := ⟨mem_pull₂.2 hj, hk⟩
      exact (gm_res r z (le j k) m _).trans (gm_pull r g z _ (le j k m) _)
  refine ⟨w', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z (r ≫ g) z j j' (fun _ => k) (fun _ => k') hj hj' (mm _ k hk) (mm _ k' hk')
  rw [Geo.Tor.gm_pull_g M f (r ≫ g) z _ _ (mm _ k hk) (mm _ k' hk'), Category.assoc r g f, hg, Category.comp_id,
    Category.assoc] at e
  rw [hv Z r z j k hj hk, hv Z r z j' k' hj' hk']
  exact e

theorem cube_through_iso : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  intro V _ _ _ _ D A G _ _ _ U w₀ hw₀ ρ hρ c x h x0 x01 x02 x12 x012 h0 h01 h02 h12 h012 hE z JA JG hJA hJG
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  obtain ⟨w, hw, hv⟩ := exists_iso_section U.gen.inv.left (congrArg (fun q => q.left) U.gen.inv_hom_id) w₀ hw₀
  have e := cub_w U.cubG c GlobalTheory.abelianSchemeLaws_all.1.globalFns A.isAb gp w hw
    (s' := jFK (R := V) (FractionRing V)) (s := jFK (R := V) (FractionRing V) ≫ jK V) (z := z) hJG hJA
    (x {0}) (x {1}) (x {2}) _ _ _ (hE {0}) (hE {1}) (hE {2})
  have k : ∀ S, Om w (s' := jFK (R := V) (FractionRing V)) z JG JA (x S) =
      Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
        (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h S).left) (fun _ => JA (x S).left) := fun S => by
    refine (hv _ (x S).left z _ _ (hJG ((x S).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V))) (hJA _)).trans ?_
    exact congrArg (fun q => Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
      (JG q) (fun _ => JA (x S).left)) (hE S)
  rw [← x012, ← x01, ← x02, ← x12, ← x0, k, k, k, k, k, k, k, k] at e
  refine Eq.trans ?_ (congrArg (· * _) e.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, id]
  abel

end GlobalTheory.GenericCube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationSectionsExtendingPointsMultiply
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem ext_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (x x' : TFK (R := V) (FractionRing V) ⟶ A.A) (h h' h'' : (𝟙_ (Over (Sp V))) ⟶ G), IntTerm.Ext U.toUnifPre x h → IntTerm.Ext U.toUnifPre x' h' → IntTerm.Ext U.toUnifPre (x * x') h'' → h'' = h * h' := by
  intro V _ _ _ _ D A G _ _ _ U x x' h h' h'' hx hx' hx''
  have := U.gen_hom
  have := U.separated
  have hmon : IsMonHom U.gen.inv := inferInstance
  have hpb := isGrpPullback_pullback G (jK V)
  have e₁ := hpb.2 (TFK (R := V) (FractionRing V)) (x ≫ U.gen.inv) (x' ≫ U.gen.inv)
    (toUnit (TF (R := V) (FractionRing V)) ≫ h) (toUnit (TF (R := V) (FractionRing V)) ≫ h')
    (hx.symm.trans (Category.assoc _ _ _).symm) (hx'.symm.trans (Category.assoc _ _ _).symm)
  have e₂ : (x * x') ≫ U.gen.inv = (x ≫ U.gen.inv) * (x' ≫ U.gen.inv) := MonObj.mul_comp _ _ _
  have e₃ : toUnit (TF (R := V) (FractionRing V)) ≫ (h * h') =
      (toUnit (TF (R := V) (FractionRing V)) ≫ h) * (toUnit (TF (R := V) (FractionRing V)) ≫ h') :=
    MonObj.comp_mul _ _ _
  have e : (toUnit (TF (R := V) (FractionRing V)) ≫ h'').left =
      (toUnit (TF (R := V) (FractionRing V)) ≫ (h * h')).left := by
    rw [e₃]
    refine Eq.trans ?_ e₁.symm
    rw [← e₂]
    exact hx''.symm.trans (Category.assoc _ _ _).symm
  have hj : (toUnit (TF (R := V) (FractionRing V))).left = jK V := by
    have h₁ : jFK (R := V) (FractionRing V) = 𝟙 _ := Spec.map_id _
    have h₂ : (toUnit (TF (R := V) (FractionRing V))).left ≫ 𝟙 _ = jFK (R := V) (FractionRing V) ≫ jK V :=
      Over.w (toUnit (TF (R := V) (FractionRing V)))
    rw [Category.comp_id, h₁] at h₂
    exact h₂.trans (Category.id_comp _)
  have hd : IsDominant (jK V) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap V (FractionRing V))).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]; exact bot_le)
  refine Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w h'').trans (Over.w (h * h')).symm) (jK V) ?_)
  rw [← hj]
  exact e

end GlobalTheory.Poinc.Tors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedEighthPower_bundleClass_eq_sum : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  exact @GlobalTheory.SharpBundle.cls_eq_sum_lam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndependeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedFrame_ratio_integralFrame_chart_independent : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  first | exact @GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | exact GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | (intros; apply GlobalTheory.Poinc.FrameIndep.frame_ratio_indep <;> assumption)
end

