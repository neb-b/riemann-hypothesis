module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SqHorizontal

theorem exists_of_atPrime {C S : Type} [CommRing C] [CommRing S] [Algebra C S] (p : Ideal C) [p.IsPrime]
    [IsLocalization.AtPrime S p] (H : C) (T W : S) (hW : IsUnit W) (e : T ^ 2 = W * algebraMap C S H) :
    ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * H = c * a ^ 2 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj p.primeCompl T
  obtain ⟨⟨d, t⟩, hd⟩ := IsLocalization.surj p.primeCompl W
  dsimp only at ha hd
  have hdu : d ∈ p.primeCompl := by
    rw [← IsLocalization.AtPrime.isUnit_to_map_iff S p, ← hd]
    exact hW.mul (IsLocalization.map_units S t)
  have key : algebraMap C S (d * (s : C) ^ 2 * H) = algebraMap C S ((t : C) * a ^ 2) := by
    simp only [map_mul, map_pow]
    rw [← ha, ← hd, mul_pow, e]
    ring
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).1 key
  refine ⟨a, u * (d * (s : C) ^ 2), u * t, ?_, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem hdu (p.primeCompl.pow_mem s.2 2))
  · exact p.primeCompl.mul_mem u.2 t.2
  · linear_combination hu

theorem isIso_stalkMap {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem exists_of_stalk {X Y : Scheme.{0}} (f : Y ⟶ X) (x : X) (q : Spec (X.presheaf.stalk x)) (y : Y)
    [IsIso (f.stalkMap y)] (hy : X.fromSpecStalk x q = f y) (U : X.Opens) (hx : x ∈ U) (hyU : f y ∈ U)
    (h : Γ(X, U)) (T W : Y.presheaf.stalk y) (hW : IsUnit W)
    (e : T ^ 2 = W * (Y.presheaf.germ (f ⁻¹ᵁ U) y hyU).hom ((f.app U).hom h)) :
    ∃ a b c : X.presheaf.stalk x, b ∉ q.asIdeal ∧ c ∉ q.asIdeal ∧
      b * (X.presheaf.germ U x hx).hom h = c * a ^ 2 := by
  let ψ : Y.presheaf.stalk y ⟶ (Spec (X.presheaf.stalk x)).presheaf.stalk q :=
    inv (f.stalkMap y) ≫ X.presheaf.stalkSpecializes (specializes_of_eq hy) ≫ (X.fromSpecStalk x).stalkMap q
  have hψ : f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) y hyU ≫ ψ =
      X.presheaf.germ U x hx ≫ StructureSheaf.toStalk (X.presheaf.stalk x) q := by
    rw [← Category.assoc, ← Scheme.Hom.germ_stalkMap f U y hyU]
    simp only [ψ, Category.assoc, IsIso.hom_inv_id_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  letI : Algebra (X.presheaf.stalk x) ((Spec (X.presheaf.stalk x)).presheaf.stalk q) :=
    (StructureSheaf.toStalk (X.presheaf.stalk x) q).hom.toAlgebra
  have hl : IsLocalization.AtPrime ((Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (X.presheaf.stalk x) q
  refine exists_of_atPrime (S := (Spec (X.presheaf.stalk x)).presheaf.stalk q) q.asIdeal _
    (ψ.hom T) (ψ.hom W) (hW.map ψ.hom) ?_
  rw [← map_pow, e, map_mul]
  congr 1
  exact congrArg (fun k => k.hom h) hψ

theorem horizontal : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (L2 : LB G₁.left) (h : L2.Sec) (Lθ : LB (pullback G₁.hom (jK R'))), Lθ.IsLB → ∀ θ : Lθ.Sec, (∀ j i, ∃ w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)ˣ, ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_right).op).hom (θ.f i) ^ 2 = (w : Γ(pullback G₁.hom (jK R'), pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i)) * ((pullback G₁.hom (jK R')).presheaf.map (homOfLE inf_le_left).op).hom (((pullback.fst G₁.hom (jK R')).app (L2.U j)).hom (h.f j))) → ∀ x : G₁.left, ∀ j (hx : x ∈ L2.U j), ∀ p : Ideal (G₁.left.presheaf.stalk x), p.IsPrime → Ideal.comap ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) p = ⊥ → ∃ a b c : G₁.left.presheaf.stalk x, b ∉ p ∧ c ∉ p ∧ b * (G₁.left.presheaf.germ (L2.U j) x hx).hom (h.f j) = c * a ^ 2 := by
  intro R' _ _ _ _ G₁ _ _ _ L2 h Lθ hL θ hθ x j hx p hp hc
  have : IsPreimmersion (jK R') := IsPreimmersion.of_isLocalization (nonZeroDivisors R') (S := FractionRing R')
  have : Flat (jK R') := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (FractionRing R') (nonZeroDivisors R'))
  let q : Spec (G₁.left.presheaf.stalk x) := ⟨p, hp⟩
  have e₁ : G₁.left.fromSpecStalk x ≫ G₁.hom = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      G₁.hom.appTop ≫ G₁.left.presheaf.germ ⊤ x trivial) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R')).inv, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  have e₂ : G₁.hom (G₁.left.fromSpecStalk x q) = jK R' (⊥ : PrimeSpectrum (FractionRing R')) := by
    rw [← Scheme.Hom.comp_apply, e₁]
    apply PrimeSpectrum.ext
    refine hc.trans ?_
    exact (Ideal.comap_bot_of_injective (algebraMap R' (FractionRing R'))
      (IsFractionRing.injective R' (FractionRing R'))).symm
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e₂
  have hs : SurjectiveOnStalks (pullback.fst G₁.hom (jK R')) :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback _ _).flip inferInstance
  have := isIso_stalkMap (pullback.fst G₁.hom (jK R')) y
  have hyU : pullback.fst G₁.hom (jK R') y ∈ L2.U j := by
    rw [hy]
    have : G₁.left.fromSpecStalk x q ∈ Set.range (G₁.left.fromSpecStalk x) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open this (L2.U j).isOpen hx
  obtain ⟨i, hi⟩ : ∃ i, y ∈ Lθ.U i := by
    have : y ∈ ⨆ i, Lθ.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨w, hw⟩ := hθ j i
  have hm : y ∈ pullback.fst G₁.hom (jK R') ⁻¹ᵁ L2.U j ⊓ Lθ.U i := ⟨hyU, hi⟩
  have hw' := congrArg ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom hw
  rw [map_pow, map_mul] at hw'
  refine exists_of_stalk (pullback.fst G₁.hom (jK R')) x q y hy.symm (L2.U j) hx hyU (h.f j) _ _
    (w.isUnit.map ((pullback G₁.hom (jK R')).presheaf.germ _ y hm).hom) (hw'.trans ?_)
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end GlobalTheory.SqHorizontal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBound
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

theorem GlobalTheory.spanShortSize : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  intro E _ _ _ H Dw a n la n₀ hp hla hn₀
  have hS : ∀ τ, |(n₀ τ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1) := by
    intro τ
    have h1 : (n₀ τ : ℝ) = 1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ) := by
      rw [hn₀ τ]; simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast]
    have h2 : |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(la τ k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have h3 : (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [h1]
    calc |1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ)|
        ≤ |1 + ((n / 2 : ℕ) : ℝ)| + |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsum : ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
    calc ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, (∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1)) := Finset.sum_le_sum (fun τ _ => hS τ)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  refine ⟨?_, hsum⟩
  have hK : sizeK Dw a n = ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))| := by
    unfold sizeK
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hla]
    simp [GlobalTheory.FlatLine.parWt]
  have hT : sizeK Dw a n ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ τ, |(n₀ τ : ℝ)| := by
    rw [hK, Finset.mul_sum]
    calc ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))|
        ≤ ∑ τ, ∑ k : Fin (Dw.p + Dw.q), (|(la τ k : ℝ)| + |(n₀ τ : ℝ)|) :=
          Finset.sum_le_sum (fun τ _ => Finset.sum_le_sum (fun k _ => abs_add_le _ _))
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpq : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hsum hpq]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningOpenImmersionPullbackSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum.ThickChart

theorem isPushout_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (Ideal.Quotient.mk K))
      (CommRingCat.ofHom (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (CommRingCat.ofHom (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map)) := by
  refine ⟨⟨by ext x; rfl⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
    (Ideal.Quotient.lift (K.map (algebraMap R C)) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro a ha
    have : K.map (algebraMap R C) ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h
      rw [Ideal.mem_comap, RingHom.mem_ker, h, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact this ha
  · intro s
    ext x
    rfl
  · intro s
    ext x
    exact congrArg (fun f => f.hom x) s.condition
  · intro s m h1 _
    ext x
    exact congrArg (fun f => f.hom x) h1

theorem isPullback_quotMap (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (K : Ideal R) :
    IsPullback (spMap (Ideal.Quotient.mk (K.map (algebraMap R C))))
      (spMap (Ideal.quotientMap (K.map (algebraMap R C)) (algebraMap R C) Ideal.le_comap_map))
      (spMap (algebraMap R C)) (spMap (Ideal.Quotient.mk K)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotMap R C K)

theorem thick_chart : ∀ (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (C' : Type) [CommRing C'] [Algebra R' C'] (j : Sp C' ⟶ G'.left) [IsOpenImmersion j], j ≫ G'.hom = spMap (algebraMap R' C') → ∀ (e : ℕ), ∃ (je : Sp (C' ⧸ (I ^ (e + 1)).map (algebraMap R' C')) ⟶ (thickObj R' I e G').left) (_ : IsOpenImmersion je), je.opensRange = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ j.opensRange ∧ IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (pullback.fst G'.hom (thick R' I e)) j ∧ je ≫ (thickObj R' I e G').hom = spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) := by
  intro R' _ I G' C' _ _ j _ hj e
  have outer := isPullback_quotMap R' C' (I ^ (e + 1))
  have right : IsPullback (pullback.snd G'.hom (thick R' I e)) (pullback.fst G'.hom (thick R' I e))
      (thick R' I e) G'.hom := (IsPullback.of_hasPullback G'.hom (thick R' I e)).flip
  have hw : (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j) ≫ G'.hom =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) ≫
        thick R' I e := by
    rw [Category.assoc, hj]
    exact outer.w
  let je := pullback.lift _ _ hw
  have hje1 : je ≫ pullback.fst G'.hom (thick R' I e) = spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))) ≫ j :=
    pullback.lift_fst _ _ _
  have hje2 : je ≫ pullback.snd G'.hom (thick R' I e) =
      spMap (Ideal.quotientMap ((I ^ (e + 1)).map (algebraMap R' C')) (algebraMap R' C') Ideal.le_comap_map) :=
    pullback.lift_snd _ _ _
  have big : IsPullback (je ≫ pullback.snd G'.hom (thick R' I e))
      (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C')))) (thick R' I e) (j ≫ G'.hom) := by
    rw [hje2, hj]
    exact outer.flip
  have sq : IsPullback je (spMap (Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R' C'))))
      (pullback.fst G'.hom (thick R' I e)) j := IsPullback.of_right big hje1 right
  haveI hoi : IsOpenImmersion je := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  refine ⟨je, hoi, ?_, sq, hje2⟩
  have h1 : sq.isoPullback.hom ≫ pullback.fst (pullback.fst G'.hom (thick R' I e)) j = je := sq.isoPullback_hom_fst
  have h2 : Set.range je = Set.range (pullback.fst (pullback.fst G'.hom (thick R' I e)) j) := by
    rw [← h1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, h2, IsOpenImmersion.range_pullbackFst]

end GlobalTheory.Mum.ThickChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningPreimageEqClosedImmersionPreimage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ThickPre

lemma thickTrans_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ)
    (t : Spec (CommRingCat.of (R' ⧸ I ^ (e + 1 + 1)))) : ∃ t', (thickTrans R' I e) t' = t := by
  have hs : Function.Surjective (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1)) := Ideal.Quotient.factor_surjective _
  have hr := _root_.range_comap_of_surjective _ _ hs
  have ht : (t : PrimeSpectrum _) ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
        R' ⧸ I ^ (e + 1 + 1) →+* R' ⧸ I ^ (e + 1))) := by
    rw [hr]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ I ^ (e + 1) := by
      rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
      exact hx
    have h2 : (Ideal.Quotient.mk (I ^ (e + 1 + 1)) a) ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have : a ^ 2 ∈ I ^ ((e + 1) * 2) := by rw [pow_mul]; exact Ideal.pow_mem_pow ha 2
      exact Ideal.pow_le_pow_right (by omega) this
    exact t.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  obtain ⟨t', ht'⟩ := ht
  exact ⟨t', ht'⟩

lemma thickMap_surj (R' : Type) [CommRing R'] (I : Ideal R') (e : ℕ) (G' : Over (Sp R')) :
    Function.Surjective (thickMap R' I e G') := by
  intro y
  obtain ⟨t', ht'⟩ := thickTrans_surj R' I e (pullback.snd G'.hom (thick R' I (e + 1)) y)
  have hc : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) = thick R' I e t' := by
    have h1 : G'.hom (pullback.fst G'.hom (thick R' I (e + 1)) y) =
        thick R' I (e + 1) (pullback.snd G'.hom (thick R' I (e + 1)) y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [h1, ← ht', ← Scheme.Hom.comp_apply, thickTrans_comp]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hc
  refine ⟨z, (pullback.fst G'.hom (thick R' I (e + 1))).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, thickMap, pullback.lift_fst, Category.comp_id, hz]

end GlobalTheory.Mum.ThickPre

theorem GlobalTheory.Mum.thick_preimage_eq (R' : Type) [CommRing R'] (I : Ideal R') (G' : Over (Sp R')) (Y : Scheme.{0})
    (φ : ∀ e : ℕ, (thickObj R' I e G').left ⟶ Y) (hφ : ∀ e, thickMap R' I e G' ≫ φ (e + 1) = φ e)
    (V : G'.left.Opens) (W : Y.Opens)
    (h0 : φ 0 ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I 0)) ⁻¹ᵁ V) :
    ∀ e, φ e ⁻¹ᵁ W = (pullback.fst G'.hom (thick R' I e)) ⁻¹ᵁ V := by
  intro e
  induction e with
  | zero => exact h0
  | succ e ih =>
    have h1 : thickMap R' I e G' ⁻¹ᵁ (φ (e + 1) ⁻¹ᵁ W) =
        thickMap R' I e G' ⁻¹ᵁ ((pullback.fst G'.hom (thick R' I (e + 1))) ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ, ih, thickMap, pullback.lift_fst,
        Category.comp_id]
    ext y
    obtain ⟨x, rfl⟩ := GlobalTheory.Mum.ThickPre.thickMap_surj R' I e G' y
    have := congrArg (fun U : Scheme.Opens _ => x ∈ U) h1
    simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  first | (exact @GlobalTheory.HTSympCover.onto_tors_iff) | (exact GlobalTheory.HTSympCover.onto_tors_iff) | (intros; apply GlobalTheory.HTSympCover.onto_tors_iff  <;> assumption)
end

