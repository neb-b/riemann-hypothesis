module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConstantHeatOperatorSymbolInMaximalId
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat.AbConstAlong

theorem abelian_part_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) :=
  GlobalTheory.Heat.AbConst.abelian_part_const

end GlobalTheory.Heat.AbConstAlong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsEqOpen

theorem exists_open_eqLocus {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion (pullback.diagonal f)]
    (u v : S ⟶ X) (huv : u ≫ f = v ≫ f) :
    ∃ U : S.Opens, (∀ V : S.Opens, V ≤ U → V.ι ≫ u = V.ι ≫ v) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S), g ≫ u = g ≫ v → Set.range g.base ⊆ (U : Set S) := by
  refine ⟨(pullback.lift u v huv) ⁻¹ᵁ (pullback.diagonal f).opensRange, ?_, ?_⟩
  · intro V hV
    have hr : Set.range (V.ι ≫ pullback.lift u v huv).base ⊆ Set.range (pullback.diagonal f).base := by
      rintro _ ⟨p, rfl⟩
      have hp : V.ι.base p ∈ V := by
        have h0 : V.ι.base p ∈ Set.range V.ι.base := ⟨p, rfl⟩
        rwa [Scheme.Opens.range_ι] at h0
      have := hV hp
      simpa using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (V.ι ≫ pullback.lift u v huv) hr
    have h1 := congrArg (· ≫ pullback.fst f f) hl
    have h2 := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id] at h1 h2
    rw [← h1, ← h2]
  · intro T g hg
    rintro _ ⟨p, rfl⟩
    have e : g ≫ pullback.lift u v huv = g ≫ u ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    have e2 := congrArg (fun h => h.base p) e
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2
    show (pullback.lift u v huv).base (g.base p) ∈ (pullback.diagonal f).opensRange
    rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
    exact ⟨_, e2.symm⟩

end GlobalTheory.TorsEqOpen

namespace GlobalTheory.TorsEqOpen

theorem comp_pow_pt {S : Scheme.{0}} {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem eq_of_eq_single {S : Scheme.{0}} {κ : Type} [Fintype κ] [DecidableEq κ] {A Z W : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : (κ → ℤ) → (W ⟶ A)) (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b)
    (φ : Z ⟶ W) (hφ : ∀ i, φ ≫ x (Pi.single i 1) = φ ≫ y (Pi.single i 1)) (a : κ → ℤ) :
    φ ≫ x a = φ ≫ y a := by
  let F : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ x a)) (fun a b => by
      rw [hx, MonObj.comp_mul]; rfl)
  let G : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ y a)) (fun a b => by
      rw [hy, MonObj.comp_mul]; rfl)
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ F G fun i k => ?_
    have e : (Pi.single i k : κ → ℤ) = k • Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e, map_zsmul, map_zsmul]
    congr 1
    simpa [F, G] using congrArg Additive.ofMul (hφ i)
  exact congrArg Additive.toMul (DFunLike.congr_fun hFG a)

end GlobalTheory.TorsEqOpen

namespace GlobalTheory

theorem torsFamily_eq_isOpen : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M))
    (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M →
    ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) →
    (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) →
    ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) →
        Set.range g.base ⊆ (U : Set S') := by
  intro m M S' _ t A _ _ hA hM x y hx hy hxM hyM
  have hu : IsUnit (M : Γ(S', ⊤)) := by
    have h1 : IsUnit (M : cycAway M) := isUnit_natCast (by omega)
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv.hom
    have h3 := h2.map t.appTop.hom
    simpa using h3
  haveI := hA.smooth
  haveI : Etale (𝟙 A ^ M).left := GlobalTheory.GrpTangent.etale_id_pow A hu
  have hpow : ∀ z : 𝟙_ (Over S') ⟶ A, z ^ M = 1 →
      z.left ≫ (𝟙 A ^ M).left = (1 : 𝟙_ (Over S') ⟶ A).left := by
    intro z hz
    rw [← Over.comp_left, TorsEqOpen.comp_pow_pt, Category.comp_id, hz]
  choose U hU1 hU2 using fun i : Fin m ⊕ Fin m =>
    TorsEqOpen.exists_open_eqLocus (S := S') (𝟙 A ^ M).left (x (Pi.single i 1)).left (y (Pi.single i 1)).left
      ((hpow _ (hxM _)).trans (hpow _ (hyM _)).symm)
  refine ⟨⟨⋂ i, (U i : Set S'), isOpen_iInter_of_finite fun i => (U i).2⟩, ?_, ?_⟩
  · intro V hV a
    have hVi : ∀ i, V ≤ U i := fun i => (show (V : Set S') ⊆ U i from
      (show (V : Set S') ⊆ ⋂ i, (U i : Set S') from hV).trans (Set.iInter_subset _ i))
    have key := TorsEqOpen.eq_of_eq_single x y hx hy (toUnit (Over.mk V.ι)) (fun i =>
      Over.OverMorphism.ext (by
        rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
        exact hU1 i V (hVi i))) a
    have := congrArg Over.Hom.left key
    rwa [Over.comp_left, Over.comp_left, Over.toUnit_left] at this
  · intro T g hg
    exact Set.subset_iInter fun i => hU2 i T g (hg _)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (exact GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_ample_pos  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpecStatement
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  first | exact @GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | exact GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | (intros; apply GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arFormExists_of_isMix : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q →
    ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  intro hA hT k _ X _ p D hX ι _ L
  obtain ⟨T, hT⟩ := hT k X p (isAmb_of_isArithVar hX) (D + 1)
  have hg : HasDim (genericPoint X) (D + 1) :=
    ((_root_.GlobalTheory.MixHt.hasDim_basic k X p (isAmb_of_isArithVar hX)).2.2.2.2.2 X (D + 1)).2 hX.dim_eq
  obtain ⟨Φ, hΦ, hΦ0⟩ := _root_.GlobalTheory.MixHt.exists_linear_of_multiadditive k X p D (fun M => T (D + 1) M (genericPoint X))
    (fun M N h => hT.iso (D + 1) M N _ le_rfl hg h)
    (fun M e => hT.symm (D + 1) M e _ le_rfl hg)
    (fun A B M => hT.add D A B M _ le_rfl hg) ι L
  refine ⟨Φ, fun n => ?_, hΦ0⟩
  obtain ⟨h, hh, hx⟩ := _root_.GlobalTheory.MixHtDiag.exists_isArithHeight hA k X p D hX T hT (comb L n)
  refine ⟨h, hh, ?_⟩
  rw [hx _ _ hg, ← Fin.prod_const (D + 1) (lin fun i => (n i : ℝ)), hΦ (fun _ => n)]

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeights
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem isometric_pull_id {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) :
    (L.pull (𝟙 X) (Category.id_comp p)).Isometric L := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  exact hiso.symm

theorem hasDim_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) : HasDim (genericPoint X) (D + 1) :=
  (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq

theorem hasDim_of_coheight_eq_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {z : X} (hz : Order.coheight z = 1) : HasDim z D := by
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  unfold HasDim
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  exact PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz

theorem lin_intCast {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun i => (n i : ℝ)) = ∑ i, n i • (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  simp only [lin, zsmul_eq_mul, map_intCast]

theorem arMix_of_mixHt : ArchInteg →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) →
    GlobalTheory.Published.ArMix := by
  intro hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  refine ⟨hAI k X p D hX M (comb L n) r hr, ?_⟩
  obtain ⟨T, hT⟩ := hEx k X p (isAmb_of_isArithVar hX) (D + 1)
  have hgen := hasDim_genericPoint hX
  set F' : Option ι → HermLB p := fun o => o.elim M L with hF'
  let F : (Fin (D + 1) → HermLB p) → ℝ := fun K => T (D + 1) K (genericPoint X)
  obtain ⟨Φ₀, hΦ₀, -⟩ := _root_.GlobalTheory.MixHt.exists_linear_of_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK)
    (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'

  have hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) =
      Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1)) := by
    intro m
    obtain ⟨g, hg, hg'⟩ := _root_.GlobalTheory.MixHtDiag.exists_isArithHeight hAI k X p D hX T hT (comb F' m)
    have h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X)) :=
      ⟨g, hg, hg' _ _ hgen⟩
    have h₂ := hΦ₀ (fun _ => m)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
    rw [HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]
    exact h₂.symm
  have hpol := GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n
  rw [hpol]

  let m₀ : Option ι → ℤ := fun o => o.elim 1 0
  let m₁ : Option ι → ℤ := fun o => o.elim 0 n
  have hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none =
      ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast,
      Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]
    ring
  have hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D *
      MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X) := by
    rw [LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]
    refine hT.iso _ _ _ _ le_rfl hgen fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₀, F']
    · simp only [Fin.cons_succ]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₁, F']
  rw [hval]

  set N := comb L n
  have hrec := hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N)
    (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr
  have e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X := by simp
  rw [e₁] at hrec
  rw [hrec, recVal, (_root_.GlobalTheory.MixAdd.mixArch_add_diag hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨g, hg, hg'⟩ := _root_.GlobalTheory.MixHtDiag.exists_isArithHeight hAI k X p D hX T hT N
  obtain rfl : h = g := hh.unique hX hg
  have e₂ : (𝟙 X : X ⟶ X) z = z := by simp
  rw [e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUpper

theorem log_ncard_smallSec {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) :
    Real.log (P.L.smallSec.ncard : ℝ) = P.lc 1 0 1 := by
  have h := SmallBall.encard_eq_Bl P (Pair.rep_base k X p P).1 P.L.smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  unfold Pair.lc
  rw [Set.ncard_def, Set.ncard_def, h]

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro HC HA HS k _ X _ p D hX L N a hL ha ε hε
  obtain ⟨⟨x, hx⟩, -⟩ := _root_.GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField k X p D hX
  obtain ⟨H, hNH, hbox⟩ := _root_.GlobalTheory.HSNef.BoxTwist.exists_twist HC k X p D hX N x
  set G := N.tens H with hG

  have hnef : ∀ m : ℕ, ((L.pow m).tens G).IsNef D := fun m =>
    _root_.GlobalTheory.NefTens.isNef_tens HC k X p D hX _ _ (GlobalTheory.NefPow.isNef_pow HC k X p D hX L m hL) hNH
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.SelfInterGrowth.main HC k X p D hX L G a ha
  have hα0 : ∀ m, 0 ≤ α m := fun m => by
    obtain ⟨h, Hh, e⟩ := hα m
    rw [← e]
    exact (_root_.GlobalTheory.KleimanNef.htNef_of_isNef HC HA HS k X p D hX _ (hnef m)).2 h Hh _
  have hg0 : ∀ m, 0 ≤ gdeg ((L.pow m).tens G) D := fun m =>
    _root_.GlobalTheory.HSNef.gdeg_nonneg_of_semiPos k X p D hX _ (hnef m).semiPos
  have hglim := _root_.GlobalTheory.DegGrowth.main HC k X p D hX L G
  refine _root_.GlobalTheory.HSNefAsymp.eventually_le_of_bound D (fun m => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ)) α
    (fun m => gdeg ((L.pow m).tens G) D) a (gdeg L D) hα0 hg0 hαlim hglim (fun m q hq => ?_) ε hε
  obtain ⟨P, hPL, hPA, hPbox⟩ := hbox ((L.pow m).tens N)
  have hiso : (P.L.tens P.A).Isometric ((L.pow m).tens G) := by
    rw [hPL, hPA]
    exact HermLB.isometric_tens_assoc _ _ _
  have T := _root_.GlobalTheory.HSNef.isometric_keeps HC k X p D hX _ _ hiso.symm
  have hb := _root_.GlobalTheory.HSNef.lc_le_bound HC HA HS k X p D hX P x (α m) q hx.1 hPbox (T.2.1 (hnef m)) (T.2.2.2.1 _ (hα m)) hq
  rw [hiso.gdeg_eq, ← log_ncard_smallSec] at hb
  have e : Real.log (P.L.smallSec.ncard : ℝ) = Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
    rw [hPL]
  simpa only [e] using hb

end GlobalTheory.NefUpper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_trivial_of_translate_difference_trivial : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.PicBilin.triv_pow_of_translDiff) | (exact GlobalTheory.PicBilin.triv_pow_of_translDiff) | (intros; apply GlobalTheory.PicBilin.triv_pow_of_translDiff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleExistsNonzero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFormula.ClassSumMonotone
open GlobalTheory.SqTop

theorem gbig_mono' {Q Q' : GP} (h : GBig Q) (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ), Q G μ₀ C x b → Q' G μ₀ C x b) : GBig Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  exact ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => H _ _ _ _ _ (h C hC D large₂ he hx hR T Lc μ₀ hL G)⟩

theorem gbig_and' {Q Q' : GP} (h : GBig Q) (h' : GBig Q') : GBig fun G μ₀ C x b => Q G μ₀ C x b ∧ Q' G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C0', x₀', h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C0', max x₀ x₀', fun C hC D large₂ he hx hR T Lc μ₀ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G,
      h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G⟩⟩

end GlobalTheory.BotFormula.ClassSumMonotone

end
end

