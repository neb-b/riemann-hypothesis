module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RefTauCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem gm_stalk {X Y Z : Scheme.{0}} (κ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  refine (gm_val (κ ≫ r) z U h a).trans (Eq.trans ?_ (congrArg (κ.stalkMap z).hom (gm_val r (κ z) U h a)).symm)
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : Z ⟶ Y) (r : Y ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    val t (κ ≫ r) z J = Units.map (κ.stalkMap z).hom.toMonoidHom (val t r (κ z) fun ψ => J (κ ≫ ψ)) := by
  rw [val_of t (κ ≫ r) z J (fun k => J (κ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalk κ r z _ (Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)) _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_good_over (ξ : Spec (CommRingCat.of (FractionRing R))) {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ S) [IsSeparated s] (f : Spec (CommRingCat.of R) ⟶ S) :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = f →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = f})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem gm_unitOn {A : Type} [CommRing A] (σ : A →+* FractionRing R) (ξ : Spec (CommRingCat.of (FractionRing R)))
    (k : Aˣ) : (gm (spMap σ) ξ ⊤ (unitOn k)).val = kst ξ (σ k) := by
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) k.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact (congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  intro R _ _ R' _ _ _ Q ρ D e hρ href a b k hk x hx
  letI := D.P.isAb.comm
  obtain ⟨β, β₂, w, h₁, h₂, -, -, h₅⟩ := href
  have hσ : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (ρ r) := fun r => IsFractionRing.lift_algebraMap _ r
  generalize IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) = σ at hσ ⊢
  have hκ : spMap σ ≫ jK R = jK R' ≫ spMap ρ := by
    have : σ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := RingHom.ext hσ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  obtain ⟨J, hJ, hc⟩ := exists_good_over ξ Q.M.isLB Q.B.hom (spMap ρ)
  have E := h₅ (spMap σ) hκ a b ξ J J' hJ hJ'
  obtain ⟨u₁, e₁⟩ := GlobalTheory.TauShift.coord_val D ξ hJ' hc' hx
  obtain ⟨u₂, e₂⟩ : ∃ u : R'ˣ, (lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ξ J J').val =
      cst ξ u := by
    have hp : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left = jK R' ≫ (lift (D.c a) (D.c b)).left := by
      simp [← CartesianMonoidalCategory.comp_lift]
    rw [hp]
    refine unit_gm' ξ (lift (D.c a) (D.c b)).left _ ?_ _
    refine And.intro (mem_pull.2 (Set.mem_iInter.2 fun I => ?_)) (Set.mem_iInter.2 fun I => ?_)
    · have := hc ((lift (D.c a) (D.c b)).left ≫ β₂ ≫ (psum Q.B (x2 Q.B) I.down).left) (by
        rw [Category.assoc, Category.assoc, Over.w, ← Over.w (fst Q.B Q.B), reassoc_of% h₂.1, h₁.1.w,
          Over.w_assoc, Over.w_assoc]
        exact Category.id_comp _)
      exact this
    · have := hc' ((lift (D.c a) (D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left) (by
        rw [Category.assoc, Over.w, Over.w]; rfl)
      exact this
  obtain ⟨u, -, hu⟩ := hk
  obtain ⟨u₃, e₃⟩ : ∃ v : R'ˣ, (val u (jK R' ≫ spMap ρ) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun i => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, lamPts (Q.c (e a)) (Q.c (e b)) i = q.left := by
      fin_cases i <;> exact ⟨_, rfl⟩
    have := hc (spMap ρ ≫ lamPts (Q.c (e a)) (Q.c (e b)) i) (by
      rw [hq, Category.assoc, Over.w q]; exact Category.comp_id _)
    exact this
  have hT := congrArg (Units.map ((spMap σ).stalkMap ξ).hom.toMonoidHom)
    (hu (spMap σ ξ) (fun ψ => J (spMap σ ≫ ψ)) fun ψ => hJ (spMap σ ≫ ψ))
  have v₁ := val_stalk (Q.tau (e a) (e b)) (spMap σ) (𝟙 (TK R).left) ξ hJ
  have v₂ := val_stalk u (spMap σ) (toUnit (TK R)).left ξ hJ
  have v₃ := gm_stalk (spMap σ) (𝟙 (TK R).left) ξ ⊤ trivial (unitOn k)
  have hh : spMap σ ≫ (toUnit (TK R)).left = jK R' ≫ spMap ρ := by
    rw [show (toUnit (TK R)).left = jK R by simpa using Over.w (toUnit (TK R))]; exact hκ
  have hT' := v₁.trans (hT.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) v₃.symm v₂.symm)))
  rw [hh] at hT'
  rw [show spMap σ ≫ 𝟙 (TK R).left = spMap σ from Category.comp_id _] at hT'
  have F : (val (Q.tau (e a) (e b)) (spMap σ) ξ J).val = kst ξ (σ k) * cst ξ u₃ :=
    (congrArg Units.val hT').trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (gm_unitOn σ ξ k) e₃))
  have G : kst ξ x.val = cst ξ u₁ * (cst ξ u₂ * (kst ξ (σ k) * cst ξ u₃)) :=
    (congrArg Units.val e₁).trans ((Units.val_mul _ _).trans (congrArg (cst ξ u₁ * ·)
      ((congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) e₂ F)))))
  refine ⟨u₁ * u₂ * u₃, kst_injective ξ ?_⟩
  rw [G, map_mul, kst_algebraMap, Units.val_mul, Units.val_mul, map_mul, map_mul]
  ring

end GlobalTheory.RefTauCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.RegCodimOne

theorem regAt_iff_ord_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {g : X.functionField} (hg : g ≠ 0) :
    RegAt z g ↔ 0 ≤ Scheme.ord g z := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 g
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_le_coe] at h
  have e : Scheme.ord g z = WithZero.log (Ring.ordFrac (X.presheaf.stalk z) g) :=
    (Scheme.ord_eq_iff hz hg).2 (WithZero.exp_log ((map_ne_zero _).2 hg)).symm
  rw [e]
  refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩⟩ h.symm

theorem regularAt_iff_forall_specializes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  intro X _ _ _ D x f
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  have hne : (f : X.functionField) * (g : X.functionField) ≠ 0 := mul_ne_zero f.ne_zero g.ne_zero
  have key : ∀ z, z ⤳ x → Scheme.ord (f : X.functionField) z + D.mult z =
      Scheme.ord ((f : X.functionField) * (g : X.functionField)) z := fun z hz => by
    rw [(hgU z (hz.mem_open U.isOpen hU)).mult_eq, Scheme.ord_mul f.ne_zero g.ne_zero]
  rw [hg.regularAt_iff]
  refine ⟨fun h z hz => ?_, fun h => regAt_of_forall_coheight_eq_one fun z hz h1 => ?_⟩
  · rw [key z hz]
    by_cases h1 : Order.coheight z = 1
    · exact (regAt_iff_ord_nonneg h1 hne).1 (GlobalTheory.Discrepancy.regAt_of_specializes hz h)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
  · exact (regAt_iff_ord_nonneg h1 hne).2 (key z hz ▸ h z hz)

end GlobalTheory.RegCodimOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisors
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_under (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 1 4).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt (p := p) (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequenceExtendCoords
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParamFrame

theorem linearIndependent_toCotangent {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m : ℕ} (r : Fin m → R) (hrsp : FinalTheorems.Rsp R m r) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R) :
    LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
  classical
  haveI : IsRegularLocalRing R := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hrsp.2, ← hrsp.1]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range r)
    have h2 : (Set.range r).ncard ≤ m := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
    rw [← hrsp.2] at this
    exact_mod_cast this
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
  have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hrsp.1
  rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
  rw [← Set.range_comp] at hsp
  exact hsp.ge


open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.AdaptedFrame in
theorem exists_frame_of_rsp : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) (c : ℕ) (a : Fin c → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U.1 y hy (a i)) → ∃ (V : Y.Opens) (hV : V ≤ U.1) (_ : y ∈ V) (z : Fin n → Γ(Y, V)) (e : Fin c ↪ Fin n), (∀ j, z (e j) = resG Y hV (a j)) ∧ IsFrame (dOn q z) := by
  classical
  intro k _ _ X _ _ p n _ y O hyO m s hrsp
  let f : Fin m → X.presheaf.stalk y := fun i => X.presheaf.germ O.1 y hyO (s i)
  have hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := linearIndependent_toCotangent f hrsp hf
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : Fin m → Γ(X, U) := fun j => resG X hUO (s j)
  have hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]

  let a : Fin m → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra k (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := k) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄k] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D k (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at e1
      change KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := _root_.GlobalTheory.extend_linearIndependent_rows_by_standard_basis ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hWU.trans hUO, hyW, fun i => resG X hWU (z i), ⟨e, he⟩, fun j => ?_, ?_⟩
  · simp only [z, z₀, Function.Embedding.coeFn_mk, he.extend_apply]
    exact resG_resG _ _ _
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.ParamFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.QuadIff

variable {R : Type} [CommRing R] [IsDomain R]

def germU (z : (TK R).left) : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 (TK R).left) z ⊤).comp (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom.toMonoidHom)

theorem bimult_iff (D : DegPre R) : D.TauBimult ↔ ∀ (a a' b : D.X) z J, Good D.P.L z J →
    val (D.tau (a + a') b) (𝟙 _) z J *
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J :=
  ⟨fun h a a' b _ _ hJ => (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h a a' b) (𝟙 _)).trans (val_mul hJ _ _ _)),
    fun h a a' b => corr_of_val D.P.isLB fun y J hJ =>
      (val_mul hJ _ _ _).trans ((h a a' b y J hJ).trans (val_mul hJ _ _ _).symm)⟩

theorem val_tau_eq (D : DegPre R) {z : (TK R).left} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_psi_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (χ : D.X) : val ((rescale D g).psi χ) (𝟙 (TK R).left) z J =
      germU z (g χ) * val (D.psi χ) (𝟙 (TK R).left) z J :=
  GlobalTheory.UU.val_scaleGen (Y := (TK R).left) (L := D.P.L) (unitOn (g χ)) (D.psi χ) (𝟙 _) hJ

theorem val_tau_rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val ((rescale D g).tau a b) (𝟙 (TK R).left) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * val (D.tau a b) (𝟙 (TK R).left) z J := by
  have key : ∀ (A B C p q r s : ((TK R).left.presheaf.stalk z)ˣ),
      A * p * (B * q)⁻¹ * (C * r)⁻¹ * s = A * B⁻¹ * C⁻¹ * (p * q⁻¹ * r⁻¹ * s) := fun A B C p q r s => by
    simp only [_root_.mul_inv]
    ac_rfl
  refine (val_tau_eq (rescale D g) hJ a b).trans (Eq.trans ?_ (congrArg (_ * ·) (val_tau_eq D hJ a b)).symm)
  refine Eq.trans ?_ (key _ _ _ _ _ _ _)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (val_psi_rescale D g hJ (a + b))
    (congrArg (·⁻¹) (val_psi_rescale D g hJ a))) (congrArg (·⁻¹) (val_psi_rescale D g hJ b))) rfl

end GlobalTheory.PolDeg.QuadIff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVectorStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianCoordinate_dual_basisVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec <;> assumption)
end

