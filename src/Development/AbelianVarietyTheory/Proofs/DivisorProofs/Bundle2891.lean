module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOne
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

theorem hO_single_of_gram_one {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (p : Fin T.rank) (q : Fin S.rank)
    (x : AE D) (y : WO S T) : hO S T (Matrix.single p q x) y = cA D (y p q) * x := by
  unfold hO
  rw [hS, hT, inv_one, Finset.sum_eq_single q, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.single_apply_same, map_one, one_mul, mul_one]
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases h : d = p
    · subst h; simp [Matrix.one_apply_ne hb]
    · simp [Matrix.single_apply_of_row_ne (Ne.symm h)]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem fe_incA_mul (a : D.host.E) (z : AE D) : fe D (incA D a * z) = algebraMap D.host.E (FA D) a * fe D z := by
  rw [map_mul, fe_apply (incA D a), GlobalTheory.LatVac.finPart_incA, GlobalTheory.FinIdlRead.finAdEquiv_one_tmul]

theorem inHat_one_fe_iff (z : AE D) : InHat 1 (fe D z) ↔ finPart D z ∈ intAE D := by
  rw [inHat_one_iff, GlobalTheory.FinIdlRead.mem_intAE_iff_finAdEquiv]
  rfl

theorem inHat_of_char_dual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  intro D ψ S T r LB n hψ hS hT hΛS hΛT hr hL p q c hc h
  have hmem : (Matrix.single p q (incA D (n : D.host.E) * c) : WO S T) ∈
      latO S T (stdLat S) LB fun _ => True := by
    refine GlobalTheory.LatVac.mem_of_char hψ hΛS hΛT ?_ fun u' hu' => ?_
    · rw [Matrix.map_single, map_mul, hc, mul_zero, Matrix.single_zero]
    · obtain ⟨h0, h1⟩ := hL u' hu'
      have h0' : infPart D (u' p q) = 0 := congrFun (congrFun h0 p) q
      have ht := h (cA D (incA D ((n : D.host.E) * r) * u' p q))
        (by rw [(GlobalTheory.IdemSupport.parts_cA _).1, map_mul, h0', mul_zero, map_zero])
        (by
          rw [inHat_one_fe_iff]
          refine GlobalTheory.IdemSupport.finPart_cA_mem ?_
          rw [← inHat_one_fe_iff, fe_incA_mul]
          exact h1 p q)
      have e : incA D (star r⁻¹) * (cA D (incA D ((n : D.host.E) * r) * u' p q) * c) =
          cA D (u' p q) * (incA D (n : D.host.E) * c) := by
        have e1 : incA D (star r⁻¹) * incA D (star ((n : D.host.E) * r)) = incA D (n : D.host.E) := by
          rw [← map_mul, ← star_mul, mul_assoc, mul_inv_cancel₀ hr, mul_one, star_natCast]
        rw [map_mul, GlobalTheory.IdemSupport.cA_incA, ← e1]
        ring
      rw [e] at ht
      unfold symplO
      rw [hO_single_of_gram_one hS hT]
      exact ht
  have h2 := (hL _ hmem).2 p q
  rw [Matrix.single_apply_same, fe_incA_mul, ← mul_assoc, ← map_mul] at h2
  rw [mul_right_comm]
  exact h2

end GlobalTheory.CosetOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldCommutesPointTranslation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.HeatTrans

namespace GlobalTheory.Heat

theorem IsInv.pbT_tr_preimage {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G)
    (O : G.left.Opens) (f : Γ(G.left, O)) :
    dd (tr G x ⁻¹ᵁ O) (pbT (tr G x) f (tr G x ⁻¹ᵁ O)) = pbT (tr G x) (dd O f) (tr G x ⁻¹ᵁ O) := by
  set T := tr G x with hTdef
  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ T ⁻¹ᵁ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) =
        (G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O)) := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ (T ⁻¹ᵁ O) := hgU.trans (g.preimage_mono hle)
    have hgTO : ⊤ ≤ (g ≫ T) ⁻¹ᵁ O := hgO
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O)) hφ hgO htr

    have hT' : (g ≫ T) ≫ G.hom = g ≫ G.hom := by rw [Category.assoc, hTdef, tr_hom]
    have hφ₁ : (g ≫ T) ≫ G.hom = spMap φ := hT'.trans hφ
    have eo : tEpsG ((g ≫ T) ≫ G.hom) = tEpsG (g ≫ G.hom) := congrArg tEpsG hT'
    let g'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ (g' * (toUnit _ ≫ x))
    let v'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ v'
    have hl : ∀ k : tEpsG (g ≫ G.hom) ⟶ G, (eqToHom eo ≫ k).left = k.left := by
      intro k; rw [Over.comp_left]; simp
    have hg'T : g' ≫ (𝟙 G * (toUnit G ≫ x)) = g' * (toUnit _ ≫ x) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (g' ≫ toUnit G) (toUnit _)]
    have hwT : (g' * v') ≫ (𝟙 G * (toUnit G ≫ x)) = (g' * (toUnit _ ≫ x)) * v' := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique ((g' * v') ≫ toUnit G) (toUnit _), _root_.mul_assoc, _root_.mul_comm v',
        ← _root_.mul_assoc]
    have htr₁ : IsTr G φ (g ≫ T) v ((g' * v').left ≫ T) := by
      refine ⟨g'₁, v'₁, ?_, ?_, ?_⟩
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x))).left = _
        rw [hl, ← hg'T, Over.comp_left]
        rfl
      · show (eqToHom eo ≫ v').left = _
        rw [hl]
        rfl
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x)) * (eqToHom eo ≫ v')).left = _
        rw [← MonObj.comp_mul, hl, ← hwT, Over.comp_left]
        rfl
    have hval₁ := hinv.2 _ φ (g ≫ T) _ O f hφ₁ hgTO htr₁

    have hpb : ∀ s : Γ(G.left, O), pbT T s (T ⁻¹ᵁ O) = (T.app O).hom s := fun s => by
      rw [GlobalTheory.KS.pbT_of_le T le_rfl, Scheme.Hom.app_eq_appLE]
    have hL : valR g (T ⁻¹ᵁ O) (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) = valR (g ≫ T) O (dd O f) := by
      rw [← hval, ← hval₁, GlobalTheory.HolHom.valR_comp, hpb]
    have hR : valR g (T ⁻¹ᵁ O) (pbT T (dd O f) (T ⁻¹ᵁ O)) = valR (g ≫ T) O (dd O f) := by
      rw [GlobalTheory.HolHom.valR_comp, hpb]
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom _),
      ← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O))),
      GlobalTheory.HolHom.valR_res g hle _ hgU, GlobalTheory.HolHom.valR_res g hle _ hgU]
    exact hL.trans hR.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ T ⁻¹ᵁ O} => k.1) _
    (fun k => homOfLE k.2.2) ?_ _ _ fun k => ?_
  · intro y hy
    obtain ⟨U, hU, hyU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hyU⟩
  · exact key k.1 k.2.1 k.2.2

theorem IsInv.pbT_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens)
    (hO' : O' ≤ tr G x ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    dd O' (pbT (tr G x) f O') = pbT (tr G x) (dd O f) O' := by
  rw [← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' f, ← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' (dd O f),
    GlobalTheory.KS.rsT_of_le hO', GlobalTheory.KS.rsT_of_le hO', hinv.1.2.2 _ _ hO' le_top,
    IsInv.pbT_tr_preimage G v dd hinv x O f]

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldConstFnEqZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_constFn_eq_zero : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (r : R), dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.IsInv.apply_constFn | exact GlobalTheory.Heat.IsInv.apply_constFn | (intros; apply GlobalTheory.Heat.IsInv.apply_constFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPreservesRaynaudTorusWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Heat.GlueWt

theorem isWt_of_isInv : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (W : Y.H.left.Opens) (f : Γ(Y.H.left, W)), IsWt Y α W f → IsWt Y α W (dd W f) :=
  fun Y v dd h α W f hf => GlobalTheory.Heat.IsInv.isWt Y v dd h α W f hf

end GlobalTheory.Heat.GlueWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldsBasisTangent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DlogBasis

section Coch

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kap (r : A) : C1 U := fun i j => constFn q (U i ⊓ U j) r

theorem rsT_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := by simp [rsT, h]

theorem resG_constFn' {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) : resG Y h (constFn q O₀ r) = constFn q O r := by
  simp only [constFn, resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  first
    | (erw [Scheme.Hom.appLE_map])
    | (simp only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp]; rfl)

theorem rsT_add' {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg' {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mulc {O₀ O : Y.Opens} (h : O ≤ O₀) (r : A) (s : Γ(Y, O₀)) :
    rsT (constFn q O₀ r * s) O = constFn q O r * rsT s O := by
  rw [rsT_le h, rsT_le h, map_mul, resG_constFn' q h]

theorem kap_add (r s : A) : kap q U (r + s) = kap q U r + kap q U s := by funext i j; simp [kap, constFn]

theorem kap_mul (r s : A) : kap q U (r * s) = kap q U r * kap q U s := by funext i j; simp [kap, constFn]

theorem kap_zero : kap q U 0 = 0 := by funext i j; simp [kap, constFn]

variable {q U}

theorem isCob_zero : IsCob U 0 := ⟨0, fun i j => by simp only [Pi.zero_apply]; unfold rsT; split_ifs <;> simp⟩

theorem isCob_add {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c + d) := by
  obtain ⟨b, hb⟩ := hc
  obtain ⟨b', hb'⟩ := hd
  refine ⟨b + b', fun i j => ?_⟩
  simp only [Pi.add_apply, hb, hb', rsT_add']
  ring

theorem isCob_neg {c : C1 U} (hc : IsCob U c) : IsCob U (-c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨-b, fun i j => ?_⟩
  simp only [Pi.neg_apply, hb, rsT_neg']
  ring

theorem isCob_sub {c d : C1 U} (hc : IsCob U c) (hd : IsCob U d) : IsCob U (c - d) := by simpa [sub_eq_add_neg] using isCob_add hc (isCob_neg hd)

theorem isCob_kap_mul (r : A) {c : C1 U} (hc : IsCob U c) : IsCob U (kap q U r * c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun i => constFn q (U i) r * b i, fun i j => ?_⟩
  simp only [Pi.mul_apply, hb, kap, rsT_mulc q inf_le_right, rsT_mulc q inf_le_left]
  ring

theorem isCob_sum {n : ℕ} (c : Fin n → C1 U) (hc : ∀ a, IsCob U (c a)) : IsCob U (∑ a, c a) := Finset.sum_induction _ (fun x => IsCob U x) (fun _ _ => isCob_add) isCob_zero (fun a _ => hc a)

theorem isCob_congr {c d : C1 U} (h : c = d) (hc : IsCob U c) : IsCob U d := h ▸ hc

end Coch

section Coc

theorem pbT_id {X : Scheme.{0}} {O₀ : X.Opens} (s : Γ(X, O₀)) {O : X.Opens} (h : O ≤ O₀) :
    pbT (𝟙 X) s O = resG X h s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ 𝟙 X ⁻¹ᵁ O₀ from h)]
  simp [resG, Scheme.Hom.appLE]
  (erw [Category.id_comp]) <;> rfl

theorem dlg_res {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {T : B.left.Opens} (hT : T ≤ L.U i ⊓ L.U j) :
    rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T =
      δ T (res hT (L.g i j)).val * (res hT (L.g i j))⁻¹.val := by
  have e : ∀ s : Γ(B.left, L.U i ⊓ L.U j), pbT (𝟙 _) s (L.U i ⊓ L.U j) = s := fun s => by
    rw [pbT_id s le_rfl]; simp [resG]
  simp only [dlg, e]
  rw [rsT_le hT, map_mul, ← hδ.2.2 _ _ hT le_top]
  rfl

theorem s1 : ∀ (A : Type) [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left), L.IsLB → ∀ δ : Fld B.left, IsField ⊤ δ → IsCoc L.U (fun i j => dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) := by
  intro A _ B _ _ L hL δ hδ i j k
  have h1 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j := inf_le_left
  have h2 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have h3 : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  dsimp only
  rw [dlg_res B L δ hδ i j h1, dlg_res B L δ hδ j k h2, dlg_res B L δ hδ i k h3, ← hL.cocycle i j k]
  generalize res h1 (L.g i j) = a
  generalize res h2 (L.g j k) = b
  simp only [Units.val_mul, mul_inv_rev, hδ.2.1 _ le_top]
  linear_combination (-(δ _ ↑b * ↑b⁻¹)) * a.mul_inv + (-(δ _ ↑a * ↑a⁻¹)) * b.mul_inv

end Coc

theorem s2 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := _root_.GlobalTheory.CechFree.cech_free

theorem s3 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ (c : Fin g → A) (N : ℕ) (t : Fin N → A) (z : Fin N → C1 L.U), (∀ k, t k ∈ maximalIdeal A) → IsCob L.U (fun i j => ∑ a, constFn B.hom _ (c a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j) - ∑ k, constFn B.hom _ (t k) * z k i j) → ∀ a, c a ∈ maximalIdeal A := _root_.GlobalTheory.Heat.DlogIndep.mem_maximalIdeal_of_isCob

section Main

variable {A : Type} [CommRing A] {Y : Scheme.{0}} {I : Type} (q : Y ⟶ Sp A) (U : I → Y.Opens)

def kapH : A →+* C1 U where
  toFun := kap q U
  map_one' := by funext i j; simp [kap, constFn]
  map_mul' := kap_mul q U
  map_zero' := kap_zero q U
  map_add' := kap_add q U

theorem kapH_apply (r : A) (i j : I) : kapH q U r i j = constFn q (U i ⊓ U j) r := rfl

theorem lin_eq {n : ℕ} (c : C1 U) (cc : Fin n → A) (b : Fin n → C1 U) :
    (fun i j => c i j - ∑ a, constFn q (U i ⊓ U j) (cc a) * b a i j) = c - ∑ a, kapH q U (cc a) * b a := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem cechCochain_sum_sub_sum_constFn_eq_ringHom {n N : ℕ} (c : Fin n → A) (φ : Fin n → C1 U) (t : Fin N → A) (z : Fin N → C1 U) :
    (fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j - ∑ k, constFn q (U i ⊓ U j) (t k) * z k i j) =
      ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U (t k) * z k := by funext i j; simp [Finset.sum_apply, kapH_apply]

theorem comb_eq {n : ℕ} (φ b : Fin n → C1 U) (P : Matrix (Fin n) (Fin n) A) (c : Fin n → A) :
    ∑ a, kapH q U (c a) * φ a - ∑ k, kapH q U ((c ᵥ* P) k) * b k =
      ∑ a, kapH q U (c a) * (φ a - ∑ k, kapH q U (P a k) * b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

end Main


open Classical in
theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∀ i, IsAffineOpen (L.U i)) → Finite L.ι → ∀ (v : Fin g → TanM (𝟙 (Sp A)) B) (dd : Fin g → Fld B.left), (∀ a, IsInv B (v a) (dd a)) → (∀ w : TanM (𝟙 (Sp A)) B, ∃! cf : Fin g → A, w = ∑ a, cf a • v a) → ∀ c : C1 L.U, IsCoc L.U c → ∃! cc : Fin g → A, IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)) := by
  intro A _ _ _ B _ _ g L hab hsm hL hamp hK haff hfin v dd hinv hbasis c hc
  haveI := hfin
  let φ : Fin g → C1 L.U := fun a i j => dlg B (𝟙 _) L (dd a) i j (L.U i ⊓ L.U j)
  obtain ⟨b, -, hb⟩ := s2 A B g L.ι L.U hab hsm hL.cover haff
  have hφ : ∀ a, IsCoc L.U (φ a) := fun a => s1 A B L hL (dd a) (hinv a).1
  choose P hP using fun a => (hb (φ a) (hφ a)).exists
  have key : ∀ y : Fin g → A, IsCob L.U
      (∑ a, kapH B.hom L.U (y a) * φ a - ∑ k, kapH B.hom L.U ((y ᵥ* Matrix.of P) k) * b k) := by
    intro y
    rw [comb_eq]
    exact isCob_sum _ fun a => isCob_kap_mul _ (isCob_congr (lin_eq B.hom L.U (φ a) (P a) b) (hP a))
  have hmem : ∀ y : Fin g → A, (∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A) → ∀ a, y a ∈ maximalIdeal A := by
    intro y hy
    exact s3 A B g L hab hsm hL hamp hK haff hfin v dd hinv hbasis y g (y ᵥ* Matrix.of P) b hy
      (isCob_congr (cechCochain_sum_sub_sum_constFn_eq_ringHom B.hom L.U y φ (y ᵥ* Matrix.of P) b).symm (key y))
  have hdet : IsUnit (Matrix.of P).det := by
    by_contra hnd
    have h0 : IsLocalRing.residue A (Matrix.of P).det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnd))
    rw [RingHom.map_det] at h0
    obtain ⟨ybar, hy0, hyP⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    obtain ⟨y, rfl⟩ : ∃ y : Fin g → A, (fun a => IsLocalRing.residue A (y a)) = ybar :=
      ⟨fun a => (IsLocalRing.residue_surjective (ybar a)).choose,
        funext fun a => (IsLocalRing.residue_surjective (ybar a)).choose_spec⟩
    apply hy0
    funext a
    have hk : ∀ k, (y ᵥ* Matrix.of P) k ∈ maximalIdeal A := by
      intro k
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrFun hyP k
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.vecMul, dotProduct, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    simpa [IsLocalRing.residue_eq_zero_iff] using hmem y hk a
  obtain ⟨e, he, heu⟩ := hb c hc
  refine ⟨e ᵥ* (Matrix.of P)⁻¹, ?_, ?_⟩
  · have h1 := key (e ᵥ* (Matrix.of P)⁻¹)
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one] at h1
    have h2 := isCob_sub (isCob_congr (lin_eq B.hom L.U c e b) he) h1
    exact isCob_congr (lin_eq B.hom L.U c _ φ).symm (isCob_congr (sub_sub_sub_cancel_right _ _ _) h2)
  · intro cc' hcc'
    have h3 := isCob_add (isCob_congr (lin_eq B.hom L.U c cc' φ) hcc') (key cc')
    have h4 : IsCob L.U (fun i j => c i j - ∑ a, constFn B.hom (L.U i ⊓ L.U j) ((cc' ᵥ* Matrix.of P) a) * b a i j) :=
      isCob_congr (lin_eq B.hom L.U c _ b).symm (isCob_congr (sub_add_sub_cancel _ _ _) h3)
    have h5 := heu _ h4
    rw [← h5, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]

end GlobalTheory.DlogBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], IsSemiAbelian G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ E : TorusExtension (GlobalTheory.SS.spFibre G), (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 → IsAbelianScheme G := by
  first | exact @GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero | exact GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero | (intros; apply GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero <;> assumption)
end

