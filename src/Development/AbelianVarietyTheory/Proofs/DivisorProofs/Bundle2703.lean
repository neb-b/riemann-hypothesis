module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiCoordinateNormChartEqCoordinateNormPadicDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiNormCoord

open Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R]

theorem valF_eq {D : DegPre R} {χ : D.X} {r : R} (j : PUnit → D.P.L.ι)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) :
    valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  unfold valF
  rw [dite_eq_left (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

theorem exists_unit_valF {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (j : PUnit → D.P.L.ι)
    (hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    ∃ u : Rˣ, valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) (u * r) := by
  obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
  have h := PsiCoordLocal.generic_le D χ j hj
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀
  let φ := RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e₀]
  exact (congrArg Units.val hu).symm

theorem norm_unit {S C : Type} [CommRing S] [NormedField C] (f : S →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Sˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  intro p _ W _ _ _ _ hball D y
  haveI : CharZero W :=
    ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero
  have hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1 :=
    fun a => (hball _).2 ⟨a, rfl⟩
  refine ⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
    have := h j₀ hj₀
    rwa [valF_eq j₀ h₀ e₀] at this
  · intro j hj
    obtain ⟨u, hu⟩ := exists_unit_valF hr j hj
    rw [hu, map_mul, map_mul, norm_mul]
    have := norm_unit _ hf u
    simp only [RingHom.comp_apply] at this
    rw [this, _root_.one_mul, h]

end GlobalTheory.PsiNormCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBaseFormFlagCellCoordinates
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u n ε α hα x hx
  have hs : ptMap σ f hf x.pt ∈ ((atlas X σ).e c).source := hx.2
  rw [GlobalTheory.CxForm.pullback_eq_chart _ _ _ _ (atlas X σ) (atlas Y σ) (ptMap σ f hf) α (_root_.GlobalTheory.ChernCalc.ptMap_isHolo F σ X Y f hf) hα x c hs]
  have hb : bsL ε (cellMap ε f hf c u x.pt) = c.e (ptMap σ f hf x.pt) := bsL_pt _ _ _
  have hloc : (atlas X σ).loc α c (c.e (ptMap σ f hf x.pt)) = α ⟨(c, ptMap σ f hf x.pt), hs⟩ :=
    (atlas X σ).loc_crd α ⟨(c, ptMap σ f hf x.pt), hs⟩
  rw [hb, hloc, ← _root_.GlobalTheory.FlagCell2.pull_comp_linear]
  congr 1
  have he : (atlas X σ).e c ∘ ptMap σ f hf ∘ x.ch.symm = bsL ε ∘ (cellMap ε f hf c u ∘ x.ch.symm) := by
    funext w
    simp only [Function.comp_apply, cellMap, bsL_pt]
    rfl
  have hd : DifferentiableAt ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd :=
    (_root_.GlobalTheory.FlagCell2.cellMap_contDiffAt F σ X Y ι m E E' φ f hf hR c A u n ε x hx).differentiableAt (by norm_num)
  rw [he, fderiv_comp x.crd (bsL ε).differentiableAt hd, ContinuousLinearMap.fderiv]

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefForm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def satSpanFamily {H : Type} [AddCommGroup H] {n : ℕ} (u : Fin n → H) : AddSubgroup H where
  carrier := {h | ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u)}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨m, hm, hb⟩
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm k m a]
    exact add_mem (Submodule.smul_mem _ m ha) (Submodule.smul_mem _ k hb)
  neg_mem' := by
    rintro a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_neg]; exact neg_mem ha⟩

theorem rank_le_finrank_of_injective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  intro l _ H T _ _ _ _ _ Q hpar hnn hdef φ hφ n u hu
  classical
  set M := satSpanFamily u with hMdef
  have memM : ∀ h, h ∈ M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u) :=
    fun h => Iff.rfl
  have hbound : ∀ (m : ℕ) (v : Fin m → M), LinearIndependent ℤ v → m ≤ n := by
    intro m v hv
    choose k hk hks using fun j => (memM (v j : H)).1 (v j).2
    let w : Fin m → Submodule.span ℤ (Set.range u) := fun j => ⟨k j • (v j : H), hks j⟩
    have hw : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg j
      have h1 : ∑ i, (g i * k i) • v i = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val hg
        simpa [w, mul_smul] using this
      exact (mul_eq_zero.1 (hv _ h1 j)).resolve_right (hk j)
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range u)
    have := hw.fintype_card_le_finrank
    rw [finrank_span_eq_card hu] at this
    simpa using this
  obtain ⟨hfin, hfree, -⟩ := GlobalTheory.finite_free_of_definite_form_of_rank_le M (fun x => Q x)
    (fun f g => by simpa using hpar f g) (fun f => hnn f) (fun f hf => Subtype.ext (hdef _ hf)) n hbound
  haveI := hfin
  haveI := hfree
  let ψ : M →+ T := φ.comp M.subtype
  have hlne : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hψ : ∀ (h : M) (t : T), ψ h = (l : ℤ_[l]) • t → ∃ h' : M, h = l • h' := by
    intro h t ht
    obtain ⟨h', hh'⟩ := hφ (h : H) t ht
    obtain ⟨k, hk, hks⟩ := (memM (h : H)).1 h.2
    refine ⟨⟨h', k * l, mul_ne_zero hk (by exact_mod_cast hlne), ?_⟩, Subtype.ext ?_⟩
    · rw [mul_smul, natCast_zsmul, ← hh']
      exact hks
    · simp [hh']
  have htor : ∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0 := by
    intro t ht
    have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hlne
    exact (smul_eq_zero.1 ht).resolve_left hl
  obtain ⟨hinj, -⟩ := GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL l M T htor ψ hψ
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_baseChange] at h1
  let v : Fin n → M := fun i => ⟨u i, 1, one_ne_zero, by
    simpa using Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℤ v :=
    LinearIndependent.of_comp M.subtype.toIntLinearMap (by
      have e : (M.subtype.toIntLinearMap : M →ₗ[ℤ] H) ∘ v = u := funext fun i => rfl
      rw [e]; exact hu)
  have h2 := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h2
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTorsionPointLiftSectionTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.TorsLift

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem gtTors_toT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D F) (h : k • g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT g) := by
  obtain ⟨gs, h0, hs, hl⟩ := (GlobalTheory.TorusExt.isNsmul_iff_eq k g (k • g)).2 rfl
  refine ⟨GlobalTheory.FieldRestrictionTest.toT (k • g),
    ⟨fun i => GlobalTheory.FieldRestrictionTest.toT (gs i), h0, fun i => hs i, congrArg GlobalTheory.FieldRestrictionTest.toT hl⟩, ?_⟩
  exact (GlobalTheory.FieldRestrictionTest.isZero_toT _).2 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h)

theorem inj (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hR : GlobalTheory.Mum.Base V)
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (D : DegData V (maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp V))
    (g₀ : GtPt D.toPre N) (x₀ : N ⟶ G) (hfin : IsFinite N.hom) (hg₀ : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g₀)
    (huniv : ∀ (T : Over (Sp V)) (g : GtPt D.toPre T), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g)
    (htors : x₀ ^ k = 1) (hform : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (n n' : TF (R := V) F ⟶ N)
    (h : n.left ≫ x₀.left = n'.left ≫ x₀.left) : n = n' := by
  have hB := D.tau_bimult
  haveI : IsNoetherianRing V := hR.1.1
  have : CharZero V := hR.2
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hR.1 D A G hG U F k hk
  have key : ∀ m : TF (R := V) F ⟶ N, ∃ q : GtPtF D.toPre F, GtPt.IsPullF F m.left g₀ q ∧
      ∃ hq : k • q = GlobalTheory.TorusExt.iota hB F 0,
        (f (GlobalTheory.TorusExt.qkMk hB 0 q hq)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = m.left ≫ x₀.left := by
    intro m
    obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m g₀
    obtain ⟨h0, hn, hz⟩ := hg₀
    obtain ⟨h0', hh0'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF m h0
    have hk' : k • q = GlobalTheory.TorusExt.iota hB F 0 := by
      rw [map_zero, ← (GlobalTheory.TorusExt.isNsmul_iff_eq k q h0').1 (GlobalTheory.FieldRestrictionTest.isNsmul_restrict hq hh0' hn)]
      exact (GlobalTheory.TorusExt.isZero_iff_eq _).1 (GlobalTheory.FieldRestrictionTest.isZero_restrict hh0' hz)
    obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U k hk N g₀ x₀ hfin htors hform F m.left
      (Over.w m) (GlobalTheory.TorusExt.qkMk hB 0 q hk') rfl hq
    exact ⟨q, hq, hk', by rw [← (hf.1 _ a).1 hqa]; exact ha⟩
  obtain ⟨q, hq, hk1, e1⟩ := key n
  obtain ⟨q', hq', hk2, e2⟩ := key n'
  have hff : f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) = f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) := by
    rw [← cancel_mono U.gen.inv]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, e1, h, e2]
    · exact (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q hk1) ≫ U.gen.inv)).trans
        (Over.w (f (GlobalTheory.TorusExt.qkMk hB 0 q' hk2) ≫ U.gen.inv)).symm
  obtain ⟨z, hz1, hz2⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 ((hf.2.2.1 _ _).1 hff)
  have hz : z = 0 := by
    have h1 : k • z = 0 := by
      have := hz1.symm
      simpa using this
    have h2 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact h1
    exact (smul_eq_zero.1 h2).resolve_left (by omega)
  have hqq : q' = q := by
    have := hz2
    simpa [hz] using this
  subst hqq
  have ht : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors k (GlobalTheory.FieldRestrictionTest.toT q') :=
    GlobalTheory.TorsionFormCompare.tors_of_isPull n hq hg₀
  obtain ⟨_, _, hu⟩ := huniv _ _ ht
  exact (hu n hq).trans (hu n' hq').symm

theorem lift : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A) (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N), xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ x.left → p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → ∃ (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), h ^ N = 1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.GtTors N g ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g ∧ IntTerm.Ext U.toUnifPre x h ∧ GtPt.IsPullF (AlgebraicClosure (FractionRing V)) (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))).left g p.g := by
  intro V _ _ _ hV D A G _ _ hG U N hN x xb p hxb hy hp
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hB := D.tau_bimult
  have hkg : N • p.g = 0 := by rw [GlobalTheory.TorusExt.qk_nsmul hB p, hy, map_zero]
  obtain ⟨nb, hnb, -⟩ := huniv _ _ (gtTors_toT p.g hkg)
  obtain ⟨a, ha, hqa⟩ := GlobalTheory.ToricTorsionUnif.generic V hR G hG D A U N hN M g₀ x₀ hfin hx₀ hform
    (AlgebraicClosure (FractionRing V)) nb.left (Over.w nb) p hy hnb
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) (admissibleBase_of_completeNormalLocalCharZero hV) D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  have hax : a = xb := ((hf.1 p a).1 hqa).trans ((hf.1 p xb).1 hp).symm
  have hnx : nb.left ≫ x₀.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫
      x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) := by
    rw [← ha, hax, hxb, Category.assoc]
  have hfix : ∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V),
      spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    let n' : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
      Over.homMk (spMap σ.toAlgHom.toRingHom ≫ nb.left) (by
        rw [Category.assoc, Over.w nb]
        show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jK V = _
        rw [reassoc_of% hσ]; rfl)
    have e := inj V hR G hG D A U N hN M g₀ x₀ hfin hg₀ huniv hx₀ hform (AlgebraicClosure (FractionRing V)) n' nb
      (by
        show (spMap σ.toAlgHom.toRingHom ≫ nb.left) ≫ x₀.left = _
        rw [Category.assoc, hnx, reassoc_of% hσ])
    exact congrArg (·.left) e
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_invariant_point_descends_to_section V hV.2.1 M hfin nb hfix
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  refine ⟨s ≫ x₀, g, ?_, GlobalTheory.TorsionFormCompare.tors_of_isPull s hg hg₀,
    (GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).2 (((GlobalTheory.TorsionFormCompare.formalEq_iff _ _ _).1 hform).pull s hg),
    ?_, ?_⟩
  · rw [← MonObj.comp_pow, hx₀, MonObj.comp_one]
  · show x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ s ≫ x₀).left
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    rw [← hnx, hs, Over.comp_left, Over.comp_left, Over.comp_left]
    simp only [← Category.assoc]
    congr 2
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc]
    congr 1
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (AlgebraicClosure (FractionRing V)))) g
    have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
    rw [← Over.comp_left, ← hs] at h2
    rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hnb] at hq

end GlobalTheory.Poinc.TorsLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTerms
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

theorem eval_at_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF D.toPre (FractionRing V)) (l : FractionRing V), l ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.FrRel U.toUnifPre w₀ x e h l → ∃ w : Frm D.toPre (FractionRing V) 1 g'.b, w.IsGen ∧ IntTerm.IntFrm D.toPre g.b w l ∧ IntTerm.Lies U.toUnifPre w₀ g' w x e := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ x e h g g' l hl hF hExt hP hR
  obtain ⟨f, hf, hfv⟩ := hR
  obtain ⟨t, ht, htl⟩ := GlobalTheory.T.exists_integral_generator_rigidification_all_levels V hV D A G U.toUnifPre h g hF f hf
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g'.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g'.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w, hw, hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl, map_one, _root_.one_mul]
  refine ⟨w, hw, ⟨t, ht, hwt⟩, ?_⟩
  intro k hk wk hwk hwkg s s' v hExp hVal
  obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
  choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
    (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
  have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
      sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
    fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
  choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g t ht k α (fs i α)
  have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x e h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
  have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
    intro z J hJ
    rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
  have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g g' hP t l hl k wk hwkg hwk' s' n c fs hs a ha
  have hI := admissibleBase_of_completeNormalLocalCharZero hV
  have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
    EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
      GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
        (a i) (ha i)
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl
  convert (preTransparency := .reducible) key using 1
  · funext α
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  · simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
        (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  first | exact @GlobalTheory.TInj.low_eq_of_match | exact GlobalTheory.TInj.low_eq_of_match | (intros; apply GlobalTheory.TInj.low_eq_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningProductIso_preserves_cubicalStructure : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  first | exact @GlobalTheory.ProdUnif.cubAlong_prod | exact GlobalTheory.ProdUnif.cubAlong_prod | (intros; apply GlobalTheory.ProdUnif.cubAlong_prod <;> assumption)
end

