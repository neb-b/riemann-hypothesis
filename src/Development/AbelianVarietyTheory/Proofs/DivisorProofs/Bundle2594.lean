module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem hRed_pGl {U : UnifPre I D A G} {h : 𝟙_ (Over (Sp R)) ⟶ G} {g : GtPt D.toPre (𝟙_ (Over (Sp R)))}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g) (e : ℕ) : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
  have a : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e :=
    (hRed_fst _ e).trans (Category.comp_id _)
  have b : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    have := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
    rw [← cancel_mono (fstG I e G).left, hRed_fst, Category.assoc]
    have c : ((Over.pullback (thick R I e)).map h).left ≫ (fstG I e G).left =
        (fstG I e (𝟙_ (Over (Sp R)))).left ≫ h.left := pullback.lift_fst _ _ _
    rw [c, ← Category.assoc, a]
  exact (congrArg (· ≫ pGl U e) b).symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (hg e).1.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.b.left) a))))

theorem exists_tRel [IsLocalRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) {U : UnifPre I D A G}
    {h : 𝟙_ (Over (Sp R)) ⟶ G} {b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A}
    (hb : ∀ e, hRed I h e ≫ pGl U e = thick R I e ≫ b.left)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1)),
      t.IsGen ∧ ∀ e : ℕ, TRel U h b f t e := by
  obtain ⟨ν, ν', hν, hν', v⟩ := GlobalTheory.TorsionTranslate.exists_matching U hI (K := Fin 1) (fun _ => 1)
    (fun _ => b.left) (fun _ => h.left) (fun e _ => hRed I h e) (fun e _ => hb e) (fun e _ => hRed_fst h e)
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio U.LG.isLB rfl f ν' hf hν'
  obtain ⟨μ₁, hμ, vμ⟩ := GlobalTheory.TorsionTranslate.exists_scale ν hν ρ
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := ![(η[D.toPre.P.A]).left, b.left]) (ε' := DegPre.lineε 1)
    (fun W _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      rfl)
    (LB.mulGen D.toPre.P.L (K := PUnit) _ _ _ _ D.toPre.rig (LB.invGen D.toPre.P.L _ _ μ₁))
    (mulGen_isGen _ _ _ _ _ _ _ D.toPre.rig_gen (invGen_isGen _ _ _ _ hμ))
  refine ⟨t, ht, fun e Z r z J JG hJ hJG => ?_⟩
  have k := v e Z r z J JG hJ hJG
  rw [Fintype.prod_unique, zpow_one] at k
  have w : wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) =
      GlobalTheory.TorusInvariance.wVal U e z J JG (r ≫ hRed I h e) := by
    rw [← Category.assoc, ← Category.assoc]; rfl
  have k₁ := (vt _ (r ≫ thick R I e) z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (_ * ·)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((vμ _ _ z J hJ).trans (congrArg (_ * ·) k))))))
  have k₂ := hρ _ (r ≫ thick R I e) z JG hJG
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) k₁ w) k₂).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end

theorem exists_integral_frame : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  intro V _ _ _ hV D A G _ _ U h g hg f hf
  have := hV.2.2.1
  exact exists_tRel (maximalIdeal.isMaximal V).ne_top (hRed_pGl hg) f hf

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOne
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FiniteNearCodimOne

theorem le_one_of_add_eq {c : ℕ∞} {s t : WithBot ℕ∞} {D : ℕ} (h₁ : (c : WithBot ℕ∞) + s = D)
    (h₂ : ((1 : ℕ∞) : WithBot ℕ∞) + t = D) (hts : t ≤ s) : c ≤ 1 := by
  induction t using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h₂; exact absurd h₂.symm (WithBot.natCast_ne_bot _)
  | coe t =>
    have h₃ : (c : WithBot ℕ∞) + t ≤ ((1 : ℕ∞) : WithBot ℕ∞) + t :=
      (add_le_add le_rfl hts).trans (h₁.trans h₂.symm).le
    have h₄ : 1 + t = (D : ℕ∞) := by exact_mod_cast h₂
    have ht : t ≠ ⊤ := by rintro rfl; rw [add_top] at h₄; exact ENat.natCast_ne_top _ h₄.symm
    have h₅ : c + t ≤ 1 + t := by exact_mod_cast h₃
    exact (ENat.add_le_add_iff_right ht).1 h₅

theorem coheight_eq_zero_iff {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Order.coheight x = 0 ↔ x = genericPoint X := by
  rw [Order.coheight_eq_zero]
  constructor
  · intro h
    have h' : x ⤳ genericPoint X := h (show x ≤ genericPoint X from genericPoint_specializes x)
    exact (h'.antisymm (genericPoint_specializes x)).eq
  · rintro rfl b _
    exact genericPoint_specializes b

theorem exists_isFinite_restrict_of_coheight_eq_one : ∀ (F : Type) [Field F] (X Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (D : ℕ), IsProjOver p →
    topologicalKrullDim X = (D : ℕ) → IsProjOver q → topologicalKrullDim Y = D →
    ∀ π : Y ⟶ X, π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ z : X,
    Order.coheight z = 1 → ∃ U : X.Opens, z ∈ U ∧ IsFinite (π ∣_ U) := by
  intro F _ X Y _ _ p q D hp hX hq hY π hπ hη z hz
  have : IsProper p := by
    obtain ⟨N, c, hc, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : IsProper q := by
    obtain ⟨N, c, hc, rfl⟩ := hq
    have := isProper_str F N
    infer_instance
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian Y := {}
  have hzne : z ≠ genericPoint X := fun h => by
    rw [(coheight_eq_zero_iff z).2 h] at hz
    exact zero_ne_one hz
  have hw : ∀ w : Y, π w = z → Order.coheight w = 1 := by
    intro w hwz
    have h₁ := (FieldDimCoheight.coheight_add_dim_closure_eq F Y q w).trans hY
    have h₂ := (FieldDimCoheight.coheight_add_dim_closure_eq F X p z).trans hX
    rw [hz] at h₂
    have h₃ := PosBaseChange.dim_image_le π.isClosedMap (isClosed_closure (s := ({w} : Set Y)))
    rw [← π.isClosedMap.closure_image_eq_of_continuous π.continuous, Set.image_singleton, hwz] at h₃
    refine le_antisymm (le_one_of_add_eq h₁ h₂ h₃) (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [(coheight_eq_zero_iff w).1 h0] at hwz
    exact hzne (hwz.symm.trans hη)
  have hfin : (π ⁻¹' {z}).Finite := by
    let U : Y.Opens := π ⁻¹ᵁ ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
    have hU : genericPoint Y ∈ U := by
      show π (genericPoint Y) ∈ (closure ({z} : Set X))ᶜ
      rw [hη]
      intro hc
      exact hzne ((specializes_iff_mem_closure.2 hc).antisymm (genericPoint_specializes z)).eq
    refine (Mix.finite_coheight_one_notMem_open Y U hU).subset fun w hwz => ⟨hw w hwz, fun hwU => ?_⟩
    have hwU' : π w ∈ (closure ({z} : Set X))ᶜ := hwU
    exact hwU' (by rw [show π w = z from hwz]; exact subset_closure rfl)
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton π z hfin

end GlobalTheory.FiniteNearCodimOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem spMap_comp_tf {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) {F₀ F : Type}
    [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (hj : Ext f j) :
    spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

theorem tr_base {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {f : R →+* V} {D₀ : DegPre R}
    {D : DegPre V} {hD : IsPullDeg f D₀ D} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F]
    [Algebra (FractionRing V) F] {j : F₀ →+* F} (hj : Ext f j) {g₀ : GtPtF D₀ F₀} {g : GtPtF D F}
    (h : Tr f hD j g₀ g) {X : Scheme.{0}} (m : D₀.P.A.left ⟶ X) (k : Sp R ⟶ X)
    (hg₀ : g₀.b.left ≫ m = (TF (R := R) F₀).hom ≫ k) :
    g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f)) ≫ m = (TF (R := V) F).hom ≫ spMap f ≫ k := by
  obtain ⟨g₁, ⟨hb, -⟩, hp⟩ := h
  rw [← Category.assoc, hp.1, hb, Category.assoc, hg₀, ← Category.assoc, spMap_comp_tf f j hj, Category.assoc]

theorem exists_level_pairs : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  intro o _ ζ n L hn R _ _ V _ _ J J' D₀ D₁ D₂ ω β hβ f₁ f₂ hD₁ hD₂ F₀ _ _ _ F _ _ j₁ j₂ b φ hj₁ hj₂ H l
  have hc := IsGrpPullback.comp hβ L.cart
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.SiegelPull.push_surjective hc (TF (R := R) F₀) (toUnit _ ≫ L.F.univ.lev l)
  have hb₀' : b₀.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left := by
    have e := congrArg (fun z => z.left) hb₀
    simp only [pushHom, pushPt, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at e
    rw [e]
    simp
  have hpow : b₀ ^ n = 1 := by
    apply GlobalTheory.SiegelPull.push_injective hc
    rw [map_pow, hb₀, ← MonObj.comp_pow, L.F.univ.lev_tors, MonObj.comp_one, map_one]
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.TInj.exists_qk_zero_over R D₀.toPre D₀.tau_bimult F₀ n hn b₀ hpow
  obtain ⟨p₁, p₂, h1y, htr1, h2y, htr2, hq⟩ := H p₀
  have hg₀ : p₀.g.b.left ≫ β ≫ L.β = (TF (R := R) F₀).hom ≫ (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫
      (L.F.univ.lev l).left) := by rw [hp₀b, hb₀']
  have hsp : ∀ f : R →+* V, spMap (f.comp ω) = spMap f ≫ spMap ω := fun f => by
    simp only [spMap, ← Spec.map_comp]; rfl
  refine ⟨p₁, p₂, by rw [h1y, hp₀y, map_zero], ?_, by rw [h2y, hp₀y, map_zero], ?_, hq⟩
  · have e := tr_base hj₁ htr1 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e
  · have e := tr_base hj₂ htr2 _ _ hg₀
    rw [hsp]
    simpa only [Category.assoc] using e

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenA
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lineBundle_section_nonzeroLocus_eq_affineOpen :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
      (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V →
      (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) →
      ∃ M : LB A.left, M.IsLB ∧ ∃ s : LB.Sec M, Out.nonzeroLocus s = V := by
  intro R _ _ _ _ A _ hA V hV hs
  obtain ⟨c, L, hL, s, -, e⟩ := _root_.GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres R A hA V hV hs
  exact ⟨L, hL, s, e⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CanMap

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}

def ext (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) : G.RigExt :=
  G.rigMk (⟨d.coc, fun n ↦ ⟨GlobalTheory.T.rigidifiedPresentation_cocycle_mem_bialgebraSymmetricCocycles R A p G t c d hs n, GlobalTheory.T.bialgebraPullbackTwoVariables_res_cocycle_eq R A p G t c d n⟩⟩,
    ⟨d.om, fun n ↦ _root_.GlobalTheory.PtExt.OmRes.cotMap_res_om R A p G t c d n⟩)

theorem ext_isCan (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hs : IsSymCoc d.g) :
    IsCan t c (ext t c d hs) :=
  ⟨d, _, _, fun _ ↦ rfl, fun _ ↦ rfl, rfl⟩

theorem exists_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : ∃ x, IsCan t c x := by
  obtain ⟨d⟩ := _root_.GlobalTheory.PtExt.nonempty_dat R A p G t c
  exact ⟨_, ext_isCan t c d (_root_.GlobalTheory.PtExt.isSymCoc_of_isAdd R A hA (fv d.f) d.g d.add)⟩

def canFun (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) : G.RigExt :=
  (exists_isCan t hA c).choose

theorem canFun_isCan (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) :
    IsCan t c (canFun t hA c) :=
  (exists_isCan t hA c).choose_spec

theorem isCan_iff (t : G.TorsionTower A) (hA : IsAbelianScheme A) (c : primDR A) (x : G.RigExt) :
    IsCan t c x ↔ canFun t hA c = x :=
  ⟨fun h ↦ GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique R A p G t c hA _ _ (canFun_isCan t hA c) h, fun h ↦ h ▸ canFun_isCan t hA c⟩

def canMap (t : G.TorsionTower A) (hA : IsAbelianScheme A) : primDR A →ₗ[R] G.RigExt where
  toFun := canFun t hA
  map_add' c c' := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).1 c c' _ _ (canFun_isCan t hA c) (canFun_isCan t hA c'))
  map_smul' r c := (isCan_iff t hA _ _).1
    ((GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul R A p G t).2 r c _ (canFun_isCan t hA c))

end GlobalTheory.PtExt.CanMap

theorem GlobalTheory.PtExt.exists_canMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A), IsAbelianScheme A →
      ∃ L : primDR A →ₗ[R] G.RigExt, ∀ c x, IsCan t c x ↔ L c = x :=
  fun _ _ _ _ _ _ t hA ↦ ⟨GlobalTheory.PtExt.CanMap.canMap t hA, GlobalTheory.PtExt.CanMap.isCan_iff t hA⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.exists_logKS_div | exact GlobalTheory.LogKSDiv.exists_logKS_div | (intros; apply GlobalTheory.LogKSDiv.exists_logKS_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLuSubring
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagLU

theorem det_lead {K : Type} [CommRing K] {s : ℕ} (g : Matrix (Fin s) (Fin s) K) (l : ℕ) (hl : l ≤ s) :
    (g.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
  let e : Fin l ≃ {a : Fin s // (a : ℕ) < l} :=
    { toFun := fun i => ⟨Fin.castLE hl i, i.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem exists_lu_subring : ∀ (K : Type) [Field K] (O : Subring K) (s : ℕ) (g : Matrix (Fin s) (Fin s) K), (∀ i j, g i j ∈ O) → (∀ k : ℕ, (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det ≠ 0 ∧ ((g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < k} → Fin s) Subtype.val).det)⁻¹ ∈ O) → ∃ (y : Low s → K) (b : Matrix (Fin s) (Fin s) K), (∀ j, y j ∈ O) ∧ (∀ i j, b i j ∈ O) ∧ (∀ i j, i < j → b i j = 0) ∧ g = b * upU y := by
  intro K _ O s g hg hmin
  let A : Matrix (Fin s) (Fin s) O := Matrix.of fun i j => ⟨g j i, hg j i⟩
  have hA : A.map O.subtype = gᵀ := by ext i j; rfl
  have hu : ∀ l : Fin (s + 1), IsUnit (A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det := by
    intro l
    have h1 : ((A.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det : K) =
        (g.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < l} → Fin s) Subtype.val).det := by
      have h2 := det_lead g l l.is_le
      rw [← O.coe_subtype, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, hA,
        ← Matrix.transpose_submatrix, Matrix.det_transpose, h2]
    obtain ⟨h0, hi⟩ := hmin l
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, h1]
    exact mul_inv_cancel₀ h0
  obtain ⟨n, M, hM, -, hAe⟩ := GlobalTheory.FlagCell.exists_lu O s A hu
  refine ⟨fun j => n j, (M.map O.subtype)ᵀ, fun j => (n j).2, fun i j => (M j i).2, ?_, ?_⟩
  · intro i j hij
    show ((M j i : O) : K) = 0
    rw [hM (i := j) (j := i) hij]; rfl
  · have key : A.map O.subtype = (GlobalTheory.FlagCell.uniR n * M).map O.subtype := by rw [← hAe]
    rw [hA, Matrix.map_mul, GlobalTheory.FlagCell.map_uniR] at key
    have h3 : (upU fun j => (n j : K)) = (GlobalTheory.FlagCell.uniR fun j => O.subtype (n j))ᵀ := by
      ext a b
      simp only [upU, Matrix.of_apply, Matrix.transpose_apply, GlobalTheory.FlagCell.uniR_apply, eq_comm]
      rfl
    rw [h3, ← Matrix.transpose_mul, ← key, Matrix.transpose_transpose]

end GlobalTheory.FlagLU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedBundleFrameFromPartFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X) (j j' : ℕ) (g : GtPtF D₁ F) (b' : TF (R := R) F ⟶ D₂.P.A), b' = g.b ≫ b → ∀ (w : Frm D₂ F j b') (w' : Frm D₁ F j' g.b), w.IsGen → w'.IsGen → ∃ τ : LB.Gen (LB.LinComb (JN D₁ D₂) (fun i => g.b.left ≫ mixφ D₁ D₂ b α i) (MixedConv.mixε j j')), τ.IsGen ∧ ∀ z J, Good (JN D₁ D₂) z J → val τ (𝟙 _) z J = rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s α) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹ := by
  first | exact @GlobalTheory.Mum.Two.Mix.exists_frame_hom | exact GlobalTheory.Mum.Two.Mix.exists_frame_hom | (intros; apply GlobalTheory.Mum.Two.Mix.exists_frame_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordMultiplierExponentNonzeroSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordMultiplier_exponent_nonzero_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ N : ℕ, 1 ≤ N ∧ GlobalTheory.MumMult.PosN D a h h' N ∧ ∃ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])) (x : D.toPre.P.A.left), D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧ GlobalTheory.MumMult.NonzeroAt D a N σ₀ x := by
  first | exact @GlobalTheory.MumMult.exists_N_sec | exact GlobalTheory.MumMult.exists_N_sec | (intros; apply GlobalTheory.MumMult.exists_N_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  first | exact @GlobalTheory.MumTerm.exists_term | exact GlobalTheory.MumTerm.exists_term | (intros; apply GlobalTheory.MumTerm.exists_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openImmersion_spec_ringOn_affine : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (W : M.Z.Opens), IsAffineOpen W → (W : Set M.Z).Nonempty → ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧ spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  first | exact @GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | exact GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn | (intros; apply GlobalTheory.Div.AffChart.exists_openImm_spec_ringOn <;> assumption)
end

