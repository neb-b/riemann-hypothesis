module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMemVanIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompactModelAboveFullLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Top.exists_cpt_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l : Level H) (h : l.A = N) (S e : ℕ) (β : RZ H S N →+* KA l) (b : RZ H n N →+* RZ H S N), 0 < S → n ∣ S → N ∣ S ^ e → IsInc (RZ H S N).subtype (KA l).val.toRingHom β → IsInc (RZ H n N).subtype (RZ H S N).subtype b → ∃ (C : Cpt (Xo l).s (Xo l).univ.t β) (q : C.X ⟶ T.Z) (hq : q ≫ T.s = C.s ≫ spMap b) (qm : SABMap C.t T.t q), IsFinite (pullback.lift q C.s hq) ∧ C.j ≫ q = T.a l h ∧ C.m.φ ≫ qm.φ = (T.m l h).φ ∧ IsQProjOver (C.t.G.hom ≫ C.s) := by
  intro E _ _ _ H D Xo n N T l h S e β b hS _ hN hβ hb
  subst h
  obtain ⟨⟨_, _⟩, _, hfr⟩ := (GlobalTheory.BaseRing.isDedFrac_RZ E H l S e hS hN).2.2 β hβ
  let _ := β.toAlgebra
  obtain ⟨W, f₀, hW₀, hfin, -, fa, fs⟩ := T.fin l rfl (β.comp b) (fun x => (hβ (b x)).trans (hb x))
  have hsm := (Xo l).smooth
  have hnor : Geo.Tor.IsNormalScheme (Xo l).X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let s₁ := pullback.snd T.s (spMap b)
  have hp : IsPullback (pullback.fst s₁ (spMap β) ≫ pullback.fst T.s (spMap b)) (pullback.snd s₁ (spMap β)) T.s
      (spMap (β.comp b)) := by
    rw [spMap_comp]
    exact (IsPullback.of_hasPullback s₁ (spMap β)).paste_horiz (IsPullback.of_hasPullback T.s (spMap b))
  let g := W.ι ≫ hp.isoPullback.inv
  have g₁ : (g ≫ pullback.fst _ _) ≫ pullback.fst _ _ = W.ι ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, hp.isoPullback_inv_fst]
  have g₂ : g ≫ pullback.snd _ _ = W.ι ≫ pullback.snd _ _ := by
    rw [Category.assoc, hp.isoPullback_inv_snd]
  have hW : (f₀ ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = f₀ ≫ g := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open _ (KA l) _ (Xo l).X s₁ (Xo l).s (f₀ ≫ g ≫ pullback.fst _ _) g.opensRange (f₀ ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b T.proj) hnor inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans (Category.assoc _ _ _))
      (by
        rw [← Category.assoc]
        exact (congrArg (· ≫ _) hW).trans ((Category.assoc _ _ _).trans ((congrArg (f₀ ≫ ·) g₂).trans fs)))
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst T.s (spMap b)) T.t
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b) = T.a l rfl := by
    rw [← fa, ← g₁, ← Category.assoc f₀, ← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap (Xo l).univ.t T.t
      ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β)) ≫ π ≫ pullback.fst T.s (spMap b)), n'.φ = (T.m l rfl).φ := by
    rw [hj]; exact ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) ∈ abLocus T.t.G := by
    intro p
    have e : pullback.fst T.s (spMap b) (pullback.fst s₁ (spMap β) p) =
        pullback.fst T.s (spMap (β.comp b)) (hp.isoPullback.hom p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hp.isoPullback_hom_fst]
    rw [e]
    change p ∈ Set.range g ↔ hp.isoPullback.hom p ∈ pullback.fst T.s (spMap (β.comp b)) ⁻¹' abLocus T.t.G
    rw [← hW₀]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact z.2
    · intro hz
      refine ⟨⟨_, hz⟩, ?_⟩
      refine (Scheme.Hom.comp_apply _ _ _).trans ?_
      change hp.isoPullback.inv (hp.isoPullback.hom p) = p
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩, π ≫ pullback.fst _ _, ?_, mu, ?_, hj,
    hm.symm.trans hn', ?_⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne T.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β) ⟶ pullback s₁ (spMap β) :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β) (w y) = π (pullback.fst (π ≫ s₁) (spMap β) y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst T.s (spMap b) z ∈ abLocus T.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst T.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _
  · have P₁ := IsPullback.of_hasPullback T.t.G.hom (pullback.fst T.s (spMap b))
    have Q := GlobalTheory.isQProjOver_of_isPullback (P₁.paste_vert (IsPullback.of_hasPullback T.s (spMap b))) T.qproj
    have P₀ := IsPullback.of_hasPullback T.t.G.hom (π ≫ pullback.fst T.s (spMap b))
    let ψ := P₁.lift (pullback.fst T.t.G.hom (π ≫ pullback.fst T.s (spMap b))) (pullback.snd _ _ ≫ π)
      (by rw [Category.assoc]; exact P₀.w)
    have ψ₁ : ψ ≫ _ = _ := P₁.lift_fst _ _ _
    have ψ₂ : ψ ≫ _ = _ := P₁.lift_snd _ _ _
    have P₂ : IsPullback ψ (pullback.snd T.t.G.hom (π ≫ pullback.fst T.s (spMap b)))
        (pullback.snd T.t.G.hom (pullback.fst T.s (spMap b))) π :=
      IsPullback.of_right (by rw [ψ₁]; exact P₀) ψ₂ P₁
    have : IsFinite ψ := MorphismProperty.of_isPullback (P := @IsFinite) P₂.flip hπ
    have R := GlobalTheory.isQProjOver_comp_of_isFinite ψ Q
    rw [← Category.assoc, ψ₂, Category.assoc] at R
    exact R

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFlatProjectiveThroughPointsGoodFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FlatFamily


open MvPolynomial in
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
  have hh : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro G ⟨hG, -⟩
    exact ⟨d, (mem_homogeneousSubmodule d G).2 hG⟩
  exact (MvPolynomial.mem_iff_homogeneousComponent_mem (h := hh) (p := F)).1 hF e


open MvPolynomial in
theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  classical
  have key : ∀ n e (F : MvPolynomial σ K), F.IsHomogeneous e → d ≤ e + n → F ∈ I → eval₂ β v F = 0 := by
    intro n
    induction n with
    | zero =>
      intro e F hFe hd hFI
      exact hJ F (hle e (by omega) F hFe hFI)
    | succ n ih =>
      intro e F hFe hd hFI
      have hmul : ∀ i, v i * eval₂ β v F = 0 := by
        intro i
        have h := ih (1 + e) (X i * F) ((isHomogeneous_X K i).mul hFe) (by omega) (I.mul_mem_left _ hFI)
        simpa [eval₂_mul, eval₂_X] using h
      have hall : ∀ y ∈ Ideal.span (Set.range v), y * eval₂ β v F = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact hmul i
        | zero => simp
        | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
        | smul a b _ hb => rw [smul_eq_mul, _root_.mul_assoc, hb, mul_zero]
      have h1 : (1 : T) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
      simpa using hall 1 h1
  intro F hF
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key d e _ (homogeneousComponent_isHomogeneous e F) (by omega) (hI F hF e)

theorem exists_flat_projRep_vanIdeal : ∀ (R σ Hh : Type) [CommRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), Ideal (MvPolynomial σ K) → Prop), (∀ (K : Type) [Field K] (x : R →+* K) I, G K x I → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p h i))) → VeryDense {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : _), RingHom.ker x = q ∧ G K x I} → ∃ (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d p) Z.hom M th ∧ IsProjOver Z.hom ∧ Flat Z.hom ∧ LocallyOfFinitePresentation Z.hom ∧ ∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), G K x I → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ p Q d G hG hVD
  classical
  have bc : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := fun R R' σ _ _ φ I Z Z' s s' π M th h hpb => RepBC.projRep_baseChange R R' σ φ I Z Z' s s' π M th h hpb
  obtain ⟨hproj, hfg, hbase⟩ := GlobalTheory.FamAlg.forms_through_points R σ Hh p Q d _ hVD (by
    rintro q ⟨K, _, x, I, rfl, hGx⟩
    exact ⟨K, _, x, I, rfl, (hG K x I hGx).2⟩)
  have hhom : ∀ F ∈ vanIdeal d p, ∀ e, MvPolynomial.homogeneousComponent e F ∈ vanIdeal d p :=
    fun F hF e => homogeneousComponent_mem_vanIdeal d p F hF e
  obtain ⟨Z₀, s, M, th, -, hrep, hlfp, hflat⟩ := GlobalTheory.ProjFlat.exists_projRep_flat R σ (vanIdeal d p) d hhom
  have hZ := GlobalTheory.ZM.projRep_projective_ample R σ (vanIdeal d p) (Over.mk s) M th hrep
  refine ⟨Over.mk s, M, th, hrep, hZ.1, hflat (fun e he => by haveI := hproj e he; infer_instance), hlfp hfg, ?_⟩
  intro K _ x I' X s' M' th' hGx hrep'
  obtain ⟨hI'hom, hcut⟩ := hG K x I' hGx
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hsec₁⟩ := bc R K σ x (vanIdeal d p) Z₀ (pullback s (spMap x)) s
    (pullback.snd s (spMap x)) (pullback.fst s (spMap x)) M th hrep hpb
  rw [hbase K x] at hrep₁
  have heqv : ∀ (R' : Type) [CommRing R'] (β : K →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ →
      ((∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) ↔
        ∀ F ∈ vanIdeal d (fun h i => x (p h i)), MvPolynomial.eval₂ β v F = 0) := by
    intro R' _ β v hv
    constructor
    · intro h
      exact eval₂_eq_zero_of_forms_le (fun F hF e => homogeneousComponent_mem_vanIdeal d _ F hF e)
        (fun e he F hFe hF => ((hcut e he).2 F hFe).2 hF) β v hv h
    · intro h
      exact eval₂_eq_zero_of_forms_le hI'hom (fun e he F hFe hF => ((hcut e he).2 F hFe).1 hF) β v hv h
  obtain ⟨e, hes, hlb, hsc⟩ := GlobalTheory.RepUniq.exists_iso_of_projRep K σ I' _ X _ s' _ M' _ th' th₁ hrep' hrep₁ heqv
  have hsc' : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ e.hom ≫ pullback.fst s (spMap x)) w := by
    intro T _ y w
    rw [hsc, hsec₁, Category.assoc]
  have hsame : GlobalTheory.RepUniq.Same M' th' (𝟙 X) M th (e.hom ≫ pullback.fst s (spMap x)) := by
    refine GlobalTheory.RepUniq.same_of_local fun t => ?_
    obtain ⟨W, hW, j, hj, htW, hW'⟩ := GlobalTheory.RepUniq.exists_affine_secCoord hrep'.1 th' (𝟙 X) t
    refine ⟨W, htW, ?_⟩
    have h1 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep'.1 hW'
    have h2 := GlobalTheory.RepUniq.locCoord_of_secCoord hrep.1 ((hsc' _ _ _).1 hW')
    have h3 := (h1.same h2).comp hW.isoSpec.hom
    have h4 : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := GlobalTheory.RepUniq.isoSpec_hom_fromSpec hW
    simp only [Category.comp_id, ← Category.assoc, h4] at h3 ⊢
    exact h3
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, GlobalTheory.RepUniq.lbIso_of_same hrep' hsame, hsc'⟩
  · have sq1 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hes, Category.comp_id]⟩
    simpa using sq1.paste_horiz hpb

end GlobalTheory.ZM.FlatFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace QuotModel

theorem isProjOver_comp_spMap {O O' : Type} [CommRing O] [CommRing O'] (b : O' →+* O) {X : Scheme.{0}}
    (s : X ⟶ Sp O) (hb : IsFinite (spMap b)) (hs : IsProjOver s) : IsProjOver (s ≫ spMap b) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N b
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N b) := MorphismProperty.of_isPullback P.flip hb
  have := _root_.GlobalTheory.isProjOver_comp_of_finite O' (PSpace O' N) X (i ≫ GlobalTheory.ProjSpace.baseChange N b) (PSpace.str O' N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  rwa [Category.assoc, P.w, ← Category.assoc] at this

theorem isPullback_fractionField {O O' F F' : Type} [CommRing O] [CommRing O'] [Field F] [Field F'] [IsDomain O]
    [Algebra O F] [IsFractionRing O F] [Algebra O' F'] [IsFractionRing O' F'] (b : O' →+* O) (k : F' →+* F)
    (h : (algebraMap O F).comp b = k.comp (algebraMap O' F')) (hb : IsFinite (spMap b)) :
    Function.Injective b ∧
      IsPullback (spMap (algebraMap O F)) (spMap k) (spMap b) (spMap (algebraMap O' F')) := by
  have hinj : Function.Injective b := by
    have : Function.Injective ((algebraMap O F).comp b) := by
      rw [h]; exact k.injective.comp (IsFractionRing.injective O' F')
    exact Function.Injective.of_comp (f := algebraMap O F) this
  refine ⟨hinj, ?_⟩
  have hfin : b.Finite := (IsFinite.SpecMap_iff _).mp hb
  letI := b.toAlgebra
  letI := ((algebraMap O F).comp b).toAlgebra
  have : IsScalarTower O' O F := .of_algebraMap_eq' rfl
  have : Module.Finite O' O := hfin
  have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Nontrivial O' := b.domain_nontrivial
  have : Algebra.IsAlgebraic O' O := inferInstance
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors O')) F := inferInstance
  have h2 : IsLocalization ((nonZeroDivisors O').map b) F := h1
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization b k h.symm (nonZeroDivisors O'))

theorem exists_isOpenImmersion_quotient (Γ : Type) [Group Γ] [Finite Γ] (Y Y' U U' : Scheme.{0}) (τ : Γ →* Aut Y)
    (ρ₀ : Γ →* Aut U) (φ : Y ⟶ Y') (r : U ⟶ U') (j : U ⟶ Y) [IsOpenImmersion j]
    (hφ : (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom))
    (hr : (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom))
    (hj : ∀ g, j ≫ (τ g).asIso.hom = (ρ₀ g).asIso.hom ≫ j) :
    ∃ j' : U' ⟶ Y', IsOpenImmersion j' ∧ r ≫ j' = j ≫ φ ∧ φ ⁻¹' Set.range j' = Set.range j := by
  have hst : ∀ g (y : Y), y ∈ j.opensRange → (τ g).asIso.hom y ∈ j.opensRange := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨(ρ₀ g).asIso.hom u, by rw [← Scheme.Hom.comp_apply, ← hj, Scheme.Hom.comp_apply]⟩
  obtain ⟨V, hV⟩ := (quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ).2.2.2.2 j.opensRange (by
    intro g
    ext y
    refine ⟨fun h => ?_, hst g y⟩
    have h1 := hst g⁻¹ _ h
    have e : (τ g).asIso.hom ≫ (τ g⁻¹).asIso.hom = 𝟙 Y := by
      rw [map_inv]; exact (τ g).asIso.hom_inv_id
    rwa [← Scheme.Hom.comp_apply, e] at h1)
  let φ' : U ⟶ V := IsOpenImmersion.lift V.ι (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : j u ∈ φ ⁻¹ᵁ V := by rw [hV]; exact ⟨u, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact this)
  have e : φ' ≫ V.ι = j ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback φ' j V.ι φ := IsOpenImmersion.isPullback _ _ _ _ e.symm (by
    rw [Scheme.Opens.opensRange_ι, hV])
  have hφ' := (quotient_flat_baseChange Γ Y Y' U V τ φ φ' j V.ι hφ P inferInstance).2 ρ₀ fun g =>
    ⟨by rw [← cancel_mono V.ι, Category.assoc, e, ← Category.assoc, ← hj, Category.assoc, hφ.2.1], (hj g).symm⟩
  obtain ⟨a, ha, -⟩ := quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr V φ' hφ'.2.1
  obtain ⟨a', ha', -⟩ := quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' U' r hr.2.1
  have : IsIso a := ⟨a', (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr U' r hr.2.1).unique
    (by rw [← Category.assoc, ha, ha']) (Category.comp_id _),
    (quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' V φ' hφ'.2.1).unique
    (by rw [← Category.assoc, ha', ha]) (Category.comp_id _)⟩
  refine ⟨a ≫ V.ι, inferInstance, by rw [← Category.assoc, ha, e], ?_⟩
  have hr' : Set.range (a ≫ V.ι) = V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, a.surjective.range_comp, Scheme.Opens.range_ι]
  rw [hr']
  exact congrArg SetLike.coe hV

end QuotModel

theorem exists_quotient_model_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (β' : O' →+* F') (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ρ₀ : Γ →* Aut U) (ρ : Γ →* Aut C.X), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → (∀ g, C.j ≫ (ρ g).asIso.hom = (ρ₀ g).asIso.hom ≫ C.j) → ∃ (X' : Scheme.{0}) (π : C.X ⟶ X') (s' : X' ⟶ Sp O') (jQ : U' ⟶ pullback s' (spMap β')), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(C.X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) ∧ IsFinite π ∧ π ≫ s' = C.s ≫ spMap b ∧ Geo.Tor.IsNormalScheme X' ∧ IsProjOver s' ∧ Flat s' ∧ jQ ≫ pullback.snd _ _ = c' ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ r ≫ jQ ≫ pullback.fst _ _ = C.j ≫ π ∧ ∀ x : C.X, π x ∈ Set.range (jQ ≫ pullback.fst s' (spMap β')) ↔ x ∈ Set.range C.j := by
  intro E _ _ _ H U F O _ _ c t β Γ _ _ C U' F' O' _ _ c' β' b k r ρ₀ ρ hβ hβ' hbk hb hrc hr hρ
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, _⟩, -, hF'⟩ := hβ'
  letI := β.toAlgebra
  letI := β'.toAlgebra
  obtain ⟨hN, hC, hS, hpre, hfl, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hdom' : IsDominant C.j := hdom
  obtain ⟨hinj, Pb⟩ := QuotModel.isPullback_fractionField (F := F) (F' := F') b k hbk hb
  replace Pb : IsPullback (spMap β) (spMap k) (spMap b) (spMap β') := Pb
  have hred : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s ≫ spMap b = r ≫ c' ≫ spMap β' := by
    rw [Cpt.j, Category.assoc, pullback.condition_assoc, ← Category.assoc, C.jQ_over, Pb.w, reassoc_of% hrc]
  have hinv : ∀ g, (ρ g).asIso.hom ≫ C.s ≫ spMap b = C.s ≫ spMap b := fun g =>
    ext_of_isDominant C.j (by rw [← Category.assoc, hρ, Category.assoc, hjs, ← Category.assoc, hr.2.1])
  have hproj := QuotModel.isProjOver_comp_spMap b C.s hb C.proj
  have hq : IsQProjOver C.s := by
    obtain ⟨N, i, hi, e⟩ := C.proj
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨X', π, hπ⟩ := exists_quotient_of_finite_group Γ C.X ρ fun x => by
    obtain ⟨V, hV, h, -⟩ := exists_isAffineOpen_le_of_isQProjOver O C.X C.s hq
      (Set.range fun g => (ρ g).asIso.hom x) ⊤ (Set.finite_range _) (Set.subset_univ _)
    exact ⟨V, hV, fun g => h ⟨g, rfl⟩⟩
  obtain ⟨s', hs', -⟩ := quotient_existsUnique_comp_eq Γ C.X X' ρ π hπ _ _ hinv
  have hprop : IsProper (π ≫ s') := by
    obtain ⟨N, i, hi, e⟩ := hproj
    have := isProper_str O' N
    rw [hs', ← e]; infer_instance
  have hfin := (_root_.GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend Γ C.X X' ρ π hπ _ s' inferInstance).1
  obtain ⟨-, hnorm, hflat⟩ := _root_.GlobalTheory.quotient_isReduced_isNormal_flat Γ C.X X' ρ π hπ
  have hbf : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    letI := b.toAlgebra
    have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat O' O)
  have hs'f : Flat s' := hflat O' s' (by rw [hs']; have := C.flat; infer_instance)
  have hβf : Flat (spMap β') := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F' (nonZeroDivisors O'))
  have hβm : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  let p := pullback.fst C.s (spMap β)
  let p' := pullback.fst s' (spMap β')
  have hpm : IsPreimmersion p :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβm
  let φ : pullback C.s (spMap β) ⟶ pullback s' (spMap β') :=
    pullback.lift (p ≫ π) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, hs', pullback.condition_assoc, Pb.w, Category.assoc])
  have e1 : φ ≫ p' = p ≫ π := pullback.lift_fst _ _ _
  have e2 : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have P : IsPullback φ p p' π := by
    refine IsPullback.of_right ?_ e1 (IsPullback.of_hasPullback s' (spMap β')).flip
    rw [e2, hs']
    exact ((IsPullback.of_hasPullback C.s (spMap β)).paste_vert Pb).flip
  obtain ⟨⟨τ, hτ⟩, hφ⟩ := quotient_flat_baseChange Γ C.X X' _ _ ρ π φ p p' hπ P inferInstance
  replace hφ := hφ τ hτ
  have := C.jQ_open
  obtain ⟨j', hj', e3, e4⟩ := QuotModel.exists_isOpenImmersion_quotient Γ _ _ U U' τ ρ₀ φ r C.jQ hφ hr fun g => by
    rw [← cancel_mono p, Category.assoc, (hτ g).2, ← Category.assoc, Category.assoc (ρ₀ g).asIso.hom]
    exact hρ g
  have e5 : r ≫ j' ≫ p' = C.j ≫ π := by
    rw [reassoc_of% e3, e1, Cpt.j, Category.assoc]
  refine ⟨X', π, s', j', hπ, hfin, hs', hnorm hN C.normal, _root_.GlobalTheory.isProjOver_quotient Γ C.X X' ρ π hπ O' s' (hs' ▸ hproj), hs'f,
    ?_, hj', ?_, e5, fun x => ⟨?_, ?_⟩⟩
  · refine (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr _ (r ≫ c') fun g => ?_).unique ?_ rfl
    · rw [← Category.assoc, hr.2.1]
    · rw [reassoc_of% e3, e2, ← Category.assoc, C.jQ_over, hrc]
  · have hsurj := (quotient_isIntegral_surjective_orbits Γ _ _ τ φ hφ).2.1
    have hd : Dense (φ '' Set.range C.jQ) := φ.surjective.denseRange.dense_image φ.continuous C.jQ_dense
    exact hd.mono (by rw [← e4]; exact Set.image_preimage_subset _ _)
  · rintro ⟨u, hu⟩
    obtain ⟨y, hy, rfl⟩ := Scheme.exists_preimage_of_isPullback P (j' u) x
      (by rw [← hu, Scheme.Hom.comp_apply])
    have : y ∈ Set.range C.jQ := by rw [← e4]; exact ⟨u, hy.symm⟩
    obtain ⟨v, rfl⟩ := this
    exact ⟨v, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, rfl⟩
    exact ⟨r u, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e5]⟩

end GlobalTheory
end

