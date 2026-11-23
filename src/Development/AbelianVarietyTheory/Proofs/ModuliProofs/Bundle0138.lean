module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Amp
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {Z : Scheme.{0}} {T : Type} [CommRing T]

def ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(Z, U) ⟶ CommRingCat.of T :=
  x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom

theorem inv_ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((ev x U h).hom a) = (x.appLE U ⊤ h).hom a := by
  have : ev x U h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv = x.appLE U ⊤ h := by
    rw [ev, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun q => q.hom a) this

theorem comp_str {R : Type} [CommRing R] (s : Z ⟶ Sp R) (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x ≫ s = spMap (baseRingHom s U ≫ ev x U h).hom := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE s x U ⊤ h, baseRingHom_top, spMap, CommRingCat.ofHom_hom,
    ← Scheme.ΓSpecIso_inv_naturality, ev]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem comp_toSpecΓ (U : Z.Opens) (y : Sp T ⟶ U.toScheme) (h : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U) :
    y ≫ U.toSpecΓ = Spec.map (ev (y ≫ U.ι) U h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ev, Spec.map_comp,
    ← Spec.map_comp (U.topIso.inv)]
  congr 2
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

theorem eq_zero_of_ev {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z) (h : ⊤ ≤ x ⁻¹ᵁ U), (ev x U h).hom a = 0) : a = 0 := by
  refine ext_germ fun z hz => ?_
  have ht : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ U := fun p _ => by
    have : Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hz
  have e : ev (T := Z.presheaf.stalk z) (Z.fromSpecStalk z) U ht = Z.presheaf.germ U z hz := by
    change (Z.fromSpecStalk z).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hz]
    simp only [Category.assoc]
    have e : (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  rw [map_zero, ← e]
  exact H _ _ ht

variable {M : LB Z} {σ : Type} {th : σ → M.Sec}

theorem secCoord_ratio (x : Sp T ⟶ Z) (i : σ) (h : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (th i)) :
    SecCoord M th x fun j => (ev x _ h).hom (secRatio (th i) (th j)) := by
  have hu : ∀ k, IsUnit ((secPull (th i) x).f k) := fun k => by
    have := isUnit_resG_sec (secPull (th i) x) k
      (le_top.trans (h.trans (nonzeroLocus_secPull (th i) x).ge)) le_rfl
    rwa [resG_self] at this
  refine ⟨⟨fun k => (hu k).unit⟩, fun k l => Units.ext ((secPull (th i) x).compat k l), fun j k e => ?_⟩
  have e' : (M.pull x).U k ≤ x ⁻¹ᵁ (nonzeroLocus (th i) ⊓ M.U (k ⟨⟩)) := le_inf (le_top.trans h) e
  have := congrArg (x.appLE _ _ e').hom (secRatio_spec (th i) (th j) (k ⟨⟩))
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  rw [inv_ev, resG_appLE]
  exact this

theorem secCoord_chart (hM : M.IsLB) (x : Sp T ⟶ Z) (k : M.ι) (h : ⊤ ≤ x ⁻¹ᵁ M.U k) :
    SecCoord M th x fun j => (ev x _ h).hom ((th j).f k) := by
  have hle : ∀ l : PUnit → M.ι, (M.pull x).U l ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U k) := fun l =>
    le_inf (pull_U M x l).le (le_top.trans h)
  refine ⟨⟨fun l => Units.map (x.appLE _ _ (hle l)).hom.toMonoidHom (M.g (l ⟨⟩) k)⟩,
    (RepBC.isGen_val _).2 fun l l' => ?_, fun j l e => ?_⟩
  · have e' : (M.pull x).U l ⊓ (M.pull x).U l' ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U (l' ⟨⟩) ⊓ M.U k) :=
      le_inf (RepBC.pull_inf_le M x l l') (le_top.trans h)
    have := congrArg (fun u => (x.appLE _ _ e').hom (Units.val u)) (hM.cocycle (l ⟨⟩) (l' ⟨⟩) k)
    simp only [Units.val_mul, val_res, map_mul] at this
    rw [appLE_resG, appLE_resG, appLE_resG] at this
    rw [RepBC.pull_g M x l l' (RepBC.pull_inf_le M x l l')]
    exact (resG_appLE x (hle l) _ _).trans (this.symm.trans (congrArg _ (resG_appLE x (hle l') _ _).symm))
  · have := congrArg (x.appLE _ _ (hle l)).hom ((th j).compat (l ⟨⟩) k)
    rw [map_mul] at this
    erw [appLE_resG, appLE_resG] at this
    rw [inv_ev, resG_appLE, mul_comm]
    exact this

theorem mem_locus (hM : M.IsLB) {x : Sp T ⟶ Z} {v : σ → T} (h : SecCoord M th x v) {i : σ} {p : Sp T}
    (hp : v i ∉ p.asIdeal) : x p ∈ nonzeroLocus (th i) := by
  obtain ⟨τ, -, h⟩ := h
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  have e := congrArg (Sp T).basicOpen (h i (fun _ => k) (pull_U M x _).le)
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    (Sp T).basicOpen_of_isUnit (Units.isUnit _)] at e
  have hp' : p ∈ (M.pull x).U fun _ => k := (pull_U M x fun _ => k).ge hk
  have h2 : p ∈ (Sp T).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) :=
    (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).ge hp
  exact Opens.mem_iSup.2 ⟨k, (e.ge ⟨⟨hp', h2⟩, hp'⟩).2⟩

variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : Z ⟶ Sp R}

theorem iSup_locus (H : ProjRep I s M th) : ⨆ i, nonzeroLocus (th i) = ⊤ := by
  refine top_le_iff.1 fun z _ => ?_
  obtain ⟨k, hk⟩ := exists_chart H.1 z
  have ht : ⊤ ≤ Z.fromSpecResidueField z ⁻¹ᵁ M.U k := fun p _ => by
    change Z.fromSpecResidueField z p ∈ M.U k
    rwa [Scheme.fromSpecResidueField_apply]
  have hc := secCoord_chart (th := th) (T := Z.residueField z) H.1 (Z.fromSpecResidueField z) k ht
  have hs := (H.2.1 _ _ _ _ (comp_str s _ _ ht) hc).1
  let p : Sp (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  by_contra hz
  refine p.isPrime.ne_top (top_le_iff.1 (hs.ge.trans (Ideal.span_le.2 ?_)))
  rintro _ ⟨i, rfl⟩
  by_contra hi
  have := mem_locus H.1 hc hi
  erw [Scheme.fromSpecResidueField_apply] at this
  exact hz (Opens.mem_iSup.2 ⟨i, this⟩)

theorem chart_affine (H : ProjRep I s M th) (i : σ) : IsAffineOpen (nonzeroLocus (th i)) ∧ Function.Surjective
    (MvPolynomial.eval₂Hom (baseRingHom s (nonzeroLocus (th i))).hom fun j => secRatio (th i) (th j)) := by
  set D := nonzeroLocus (th i) with hD
  let c : MvPolynomial σ R →+* Γ(Z, D) :=
    MvPolynomial.eval₂Hom (baseRingHom s D).hom fun j => secRatio (th i) (th j)
  let J : Ideal (MvPolynomial σ R) := I ⊔ Ideal.span {MvPolynomial.X i - 1}
  have hJ : ∀ F ∈ J, c F = 0 := by
    change J ≤ RingHom.ker c
    refine sup_le (fun F hF => eq_zero_of_ev _ fun T _ x h => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    · have := (H.2.1 _ _ _ _ (comp_str s x D h) (secCoord_ratio x i h)).2 F hF
      exact (MvPolynomial.eval₂_comp_left (ev x D h).hom _ _ F).trans this
    · simp [c, RingHom.mem_ker]
  let ρ : CommRingCat.of (MvPolynomial σ R ⧸ J) ⟶ Γ(Z, D) := CommRingCat.ofHom (Ideal.Quotient.lift J c hJ)
  have hXi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 :=
    Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨φ, ⟨hφ, hv⟩, -⟩ := H.2.2 _ ((Ideal.Quotient.mk J).comp MvPolynomial.C)
    (fun j => Ideal.Quotient.mk J (MvPolynomial.X j))
    ((Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨i, hXi⟩)) fun F hF => by
      have := MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk J) MvPolynomial.C MvPolynomial.X F
      rw [MvPolynomial.eval₂_eta] at this
      exact this.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
  have hφD : ⊤ ≤ φ ⁻¹ᵁ D := fun p _ => mem_locus H.1 hv (by
    rw [hXi]; exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  let φ' : Sp (MvPolynomial σ R ⧸ J) ⟶ D.toScheme := IsOpenImmersion.lift D.ι φ (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hφD trivial)
  have hφ' : φ' ≫ D.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hin : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), ⊤ ≤ (y ≫ D.ι) ⁻¹ᵁ D := fun T _ y p _ => (y p).2
  have e₁ : φ' ≫ D.toSpecΓ ≫ Spec.map ρ = 𝟙 _ := by
    rw [← Category.assoc, comp_toSpecΓ D φ' (hin _ φ'), ← Spec.map_comp, ← Spec.map_id]
    congr 1
    have hc := secCoord_ratio (φ' ≫ D.ι) i (hin _ φ')
    have hs := comp_str s (φ' ≫ D.ι) D (hin _ φ')
    generalize hin _ φ' = w at hc hs ⊢
    rw [hφ'] at w
    simp only [hφ'] at hc hs ⊢
    obtain ⟨u, hu⟩ := Coord.unique H.1 hv hc
    have hu1 : (u : MvPolynomial σ R ⧸ J) = 1 := by
      have := hu i
      rw [secRatio_self, map_one, hXi, _root_.mul_one] at this
      exact this.symm
    have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective (hs.symm.trans hφ))
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_))
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_C _ _ a)).trans (DFunLike.congr_fun hb a)
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_X' _ _ j)).trans
        ((hu j).trans (by rw [hu1, _root_.one_mul]; rfl))
  have e₂ : (D.toSpecΓ ≫ Spec.map ρ) ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono D.ι, Category.assoc, hφ', Category.id_comp]
    refine D.toScheme.affineCover.hom_ext _ _ fun a => ?_
    have key : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme),
        y ≫ (D.toSpecΓ ≫ Spec.map ρ) ≫ φ = y ≫ D.ι := fun T _ y => by
      have hc := secCoord_ratio (y ≫ D.ι) i (hin _ y)
      have hs := comp_str s (y ≫ D.ι) D (hin _ y)
      obtain ⟨h₁, h₂⟩ := H.2.1 _ _ _ _ hs hc
      refine (H.2.2 _ _ _ h₁ h₂).unique ?_ ⟨hs, hc⟩
      rw [← Category.assoc, ← Category.assoc, comp_toSpecΓ D y (hin _ y), ← Spec.map_comp]
      constructor
      · rw [Category.assoc, hφ, ← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
        exact congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_C _ _ a)
      · have e : (fun j => (ev (y ≫ D.ι) D (hin _ y)).hom (secRatio (th i) (th j))) = fun j =>
            (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom (Ideal.Quotient.mk J (MvPolynomial.X j)) := funext fun j =>
          congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_X' (baseRingHom s D).hom (fun j => secRatio (th i) (th j)) j).symm
        exact e ▸ Coord.baseChange hv (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom
    exact key _ (D.toScheme.affineCover.f a)
  have hiso : IsIso (D.toSpecΓ ≫ Spec.map ρ) := ⟨φ', e₂, e₁⟩
  have ha : IsAffine D.toScheme := .of_isIso (D.toSpecΓ ≫ Spec.map ρ)
  have ha' : IsAffineOpen D := ha
  refine ⟨ha', ?_⟩
  have h1 : IsIso D.toSpecΓ := inferInstanceAs (IsIso ha'.isoSpec.hom)
  have h2 : IsIso (Spec.map ρ) := IsIso.of_isIso_comp_left D.toSpecΓ _
  exact (isIso_SpecMap_iff.1 h2).2.comp Ideal.Quotient.mk_surjective

end GlobalTheory.ZM.Amp

namespace GlobalTheory.ZM
open GlobalTheory.ProjSpace Amp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem projRep_projective_ample : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  intro R σ _ _ I Z M th H
  have hp : IsProjOver Z.hom := by
    cases isEmpty_or_nonempty σ with
    | inl h => exact isProjOver_of_disjoint_cover Z.hom _ (iSup_locus H) (fun i => isEmptyElim i) fun i => isEmptyElim i
    | inr h =>
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
      obtain _ | m := n
      · exact (h.elim fun i => (e i).elim0)
      have hs : ⨆ i, nonzeroLocus (th (e.symm i)) = ⊤ :=
        (e.symm.iSup_comp (g := fun i => nonzeroLocus (th i))).trans (iSup_locus H)
      refine ⟨m, toProj Z.hom (fun i => th (e.symm i)) hs, (isClosedImmersion_toProj_iff _ _ hs).2 fun i =>
        ⟨(chart_affine H _).1, fun a => by
          obtain ⟨F, hF⟩ := (chart_affine H (e.symm i)).2 a
          refine ⟨MvPolynomial.rename e F, ?_⟩
          simpa only [MvPolynomial.eval₂Hom_rename, Function.comp_def, Equiv.symm_apply_apply] using hF⟩, toProj_str _ _ _⟩
  have hpr : IsProper Z.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨hp, hpr, (relAmple_iff_isAmpleLB_of_isAffine Z H.1).2 ?_⟩
  have e : ∀ i, nonzeroLocus (secToPow (th i) 1) = nonzeroLocus (th i) := fun i =>
    nonzeroLocus_secToPow (th i) le_rfl
  exact isAmpleLB_of_cover H.1 le_rfl (fun i => secToPow (th i) 1) ((iSup_congr e).trans (iSup_locus H))
    fun i => (e i).symm ▸ (chart_affine H i).1

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperZeroTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Fin.ext (by have := i.isLt; omega)⟩
  haveI : IsIso (PSpace.str R 0) := by
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      rw [GlobalTheory.ProjSpace.opensRange_chartι, ← GlobalTheory.ProjSpace.iSup_chart R 0]
      apply le_antisymm (le_iSup _ 0)
      apply iSup_le
      intro i
      rw [Subsingleton.elim i 0]
    haveI : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
    haveI : IsIso (GlobalTheory.ProjSpace.chartι R 0 0 ≫ PSpace.str R 0) := by
      rw [GlobalTheory.ProjSpace.chartι_str]
      exact inferInstanceAs (IsIso (Spec.map
        (MvPolynomial.isEmptyRingEquiv R {j : Fin (0 + 1) // j ≠ 0}).toCommRingCatIso.inv))
    exact IsIso.of_isIso_comp_left (GlobalTheory.ProjSpace.chartι R 0 0) _
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

end GlobalTheory.Models.Point

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_of_isPullback_spMap {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {Y Y' : Scheme.{0}}
    {s : Y ⟶ Sp R} {p : Y' ⟶ Y} {s' : Y' ⟶ Sp R'} (sq : IsPullback p s' s (spMap j)) (h : IsQProjOver s) :
    IsQProjOver s' := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have P := ProjSpace.isPullback_baseChange N j
  have w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j := by rw [Category.assoc]; exact sq.w
  have Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j) :=
    IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P
  exact ⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi,
    MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩

theorem isQProjOver_comp_spMap_of_finiteType {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}
    (hj : j.FiniteType) {Y : Scheme.{0}} {s' : Y ⟶ Sp R'} (h : IsQProjOver s') : IsQProjOver (s' ≫ spMap j) := by
  obtain ⟨N, i, _, _, rfl⟩ := h
  have := isProper_str R' N
  have : LocallyOfFiniteType (spMap j) := HasRingHomProperty.Spec_iff.2 hj
  exact ((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _

theorem isQProjOver_baseChange_and_finite_restrict :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : R →+* R') (Y : Scheme.{0}) (s : Y ⟶ Sp R),
      (IsQProjOver s → IsQProjOver (pullback.snd s (spMap j))) ∧
        ∀ s' : Y ⟶ Sp R', j.Finite → IsQProjOver s' → IsQProjOver (s' ≫ spMap j) :=
  fun _ _ _ _ j _ _ => ⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h,
    fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (s : X ⟶ Sp R) :
    IsQProjOver s ↔ LocallyOfFiniteType s ∧ ∃ L : LB X, IsAmpleLB L := by
  constructor
  · rintro ⟨N, i, hi, hq, rfl⟩
    haveI := hi
    haveI := hq
    haveI : IsProper (PSpace.str R N) :=
      ((isProjOver_iff_isProper_and_exists_isAmpleLB (PSpace.str R N)).1
        ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩).1
    exact ⟨inferInstance, _, IsAmpleLB.pull_of_isImmersion (isAmpleLB_basic.2.2.2.2.2.2.1 R N) i⟩
  · rintro ⟨hs, L, hL⟩
    haveI := hs
    exact hL.isQProjOver s

theorem isQProjOver_comp_of_isAffineHom (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFiniteType f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  haveI := hs
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (f ≫ s)).2 ⟨inferInstance, L.pull f, ?_⟩
  exact isAmpleLB_basic.2.2.1 f inferInstance hL

theorem isQProjOver_comp_of_isFinite (f : Y ⟶ X) [IsFinite f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := isQProjOver_comp_of_isAffineHom f h

theorem isQProjOver_of_isPullback {R' : Type} [CommRing R'] {b : R →+* R'} {s : X ⟶ Sp R} {π : Y ⟶ X}
    {s' : Y ⟶ Sp R'} (H : IsPullback π s' s (spMap b)) (h : IsQProjOver s) : IsQProjOver s' := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s').2 ⟨?_, L.pull π, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H hs
  · exact hL.pull_of_isPullback H

theorem isQProjOver_finite_and_baseChange :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      (∀ (Y : Scheme.{0}) (f : Y ⟶ X), IsFinite f → IsQProjOver (f ≫ s)) ∧
        ∀ (R' : Type) [CommRing R'] (b : R →+* R'), IsQProjOver (pullback.snd s (spMap b)) := by
  intro R _ _ X s h
  refine ⟨fun Y f hf => ?_, fun R' _ b => ?_⟩
  · haveI := hf
    exact isQProjOver_comp_of_isFinite f h
  · exact isQProjOver_of_isPullback (IsPullback.of_hasPullback s (spMap b)) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := open GlobalTheory.ObjPull in by
  let o : Obj D l _ (r ≫ _) :=
    have hL : LBIso t.PP.L (Y.oF.t.PP.L.pull ν.cm.F) := by
      obtain ⟨w, hw, -⟩ := ν.lin
      exact ⟨w, hw⟩
    have hpr := Y.oF.proper
    have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
      (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
      (AbelianSchemeGerms.isAbelianScheme_of_proper Y.oF.t.G Y.oF.t.semi) ν.cart hL
    { t := t
      proper := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 hpr
      ample := hp.2.1 Y.oF.ample
      ktriv := hp.2.2 Y.oF.ktriv
      eta := fun a => GlobalTheory.ObjPull.secPull ν.cart (Y.oF.eta a)
      eta_add := fun a c => by rw [Y.oF.eta_add, map_mul]
      eta_ker := fun a ha => by rw [Y.oF.eta_ker a ha, map_one]
      etaA := fun a => GlobalTheory.ObjPull.secPull ν.cart (Y.oF.etaA a)
      etaA_add := fun a c => by rw [Y.oF.etaA_add, map_mul]
      etaA_ker := fun a => by rw [Y.oF.etaA_ker a, map_one]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI, hA, hM⟩ := Y.oF.geom k (x ≫ r) β (by rw [Category.assoc, hx])
        refine ⟨fun τ => ?_, tateMove (pushEquiv ν.cart (Over.mk x)) (fun c g => ?_) (fun n g g' u hc => ?_) I,
          hI, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ,
            GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ]
          exact hdet τ
        · apply Over.OverMorphism.ext
          show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
          rw [Category.assoc, ν.act, Category.assoc]
        · exact (GlobalTheory.weilIs_grpPullback_of_comm (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
            ν.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hA a))
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hM a ha)) }
  let n : ObjMap o Y.oF r := ⟨ν, fun _ => secPull_left ν.cart _, fun _ => secPull_left ν.cart _⟩
  have sec_eq {e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} {e' : 𝟙_ (Over S) ⟶ t.G}
      (h : e'.left ≫ ν.φ = r ≫ e.left) : e' = GlobalTheory.ObjPull.secPull ν.cart e := by
    apply Over.OverMorphism.ext
    apply ν.cart.1.hom_ext
    · exact h.trans (secPull_left ν.cart _).symm
    · rw [Over.w, Over.w]
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
end
end

