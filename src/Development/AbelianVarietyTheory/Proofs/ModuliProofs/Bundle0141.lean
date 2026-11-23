module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FirstOrderRigidityLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PowEqOneIffOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.TorsionSection

theorem pow_eq_one_iff_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] (y : T ⟶ G) (n : ℕ) :
    y ^ n = 1 ↔ y.left ≫ (mulN G n).left = T.hom ≫ η[G].left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  rw [← e, ← Over.comp_left, GrpTangent.comp_mulN]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem pow_eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' T : Over S'} [GrpObj G]
    [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) (y : T ⟶ G')
    (n : ℕ) :
    y ^ n = 1 ↔ (y.left ≫ F) ≫ (mulN G n).left = (T.hom ≫ f) ≫ η[G].left := by
  let φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' (Out.toBase h.1.w)
    fun a b => Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  have hφ : Function.Injective φ := fun a b hab => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg Over.Hom.left hab) ((Over.w a).trans (Over.w b).symm))
  rw [← map_eq_one_iff φ hφ, map_pow]
  exact pow_eq_one_iff_left (φ y) n

theorem exists_section_extending_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X U : Scheme.{0}) (j : U ⟶ X) (s : U ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (μ₀ : SABMap o.t t j), IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsUnit (l.A : Γ(X, ⊤)) → ∀ (k : Type) [Field k] (x : Sp k ⟶ X) (p : Over.mk x ⟶ t.G), p ^ l.A = 1 → ∃ (a : D.La) (V : Scheme.{0}) (v : V ⟶ X) (_ : IsOpenImmersion v) (σ : V ⟶ t.G.left) (xV : Sp k ⟶ V), xV ≫ v = x ∧ σ ≫ t.G.hom = v ∧ pullback.fst v j ≫ σ = pullback.snd v j ≫ (o.etaA a).left ≫ μ₀.φ ∧ xV ≫ σ = p.left := by
  intro E _ _ _ H D l B _ b X U j s o t μ₀ hX hN h₁ h₂ h₃ h₄ hA k _ x p hp
  have := t.semi.smooth
  have := t.semi.separated
  have hP := GrpTangent.isPullback_torsion t.G l.A
  have hEt := GrpTangent.etale_torsion t.G hA
  have hι : (torsion.ι t.G l.A).left ≫ t.G.hom = (torsion t.G l.A).hom := Over.w _
  have hsep : IsSeparated (torsion t.G l.A).hom := by
    have : IsSeparated ((mulN t.G l.A).left ≫ t.G.hom) := by rw [Over.w]; infer_instance
    exact MorphismProperty.of_isPullback (P := @IsSeparated) hP (IsSeparated.of_comp _ t.G.hom)
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp this
  let K : AddSubgroup D.La := (nsmulAddMonoidHom (α := D.La) l.A).range
  have : K.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg _ l.A_pos.ne'
  let e : Multiplicative D.La →* (𝟙_ (Over U) ⟶ o.t.G) :=
    MonoidHom.mk' (fun a => o.etaA a.toAdd) fun a c => o.etaA_add _ _
  have hpow (a : D.La) : o.etaA a ^ l.A = 1 :=
    (map_pow e (.ofAdd a) l.A).symm.trans (o.etaA_ker a)
  have hout (a : D.La) : o.etaA (QuotientAddGroup.mk (s := K) a).out = o.etaA a := by
    obtain ⟨⟨_, c, rfl⟩, hc⟩ := QuotientAddGroup.mk_out_eq_add K a
    rw [hc, o.etaA_add]
    exact (congrArg (o.etaA a * ·) (o.etaA_ker c)).trans (_root_.mul_one _)
  have hw (a : D.La) : ((o.etaA a).left ≫ μ₀.φ) ≫ (mulN t.G l.A).left = j ≫ η[t.G].left :=
    ((pow_eq_one_iff_of_isGrpPullback μ₀.cart (o.etaA a) l.A).mp (hpow a)).trans
      (congrArg (· ≫ _) (Category.id_comp j))
  let σ (a : D.La) : U ⟶ (torsion t.G l.A).left := hP.lift _ _ (hw a)
  have hσ (a : D.La) : σ a ≫ (torsion.ι t.G l.A).left = (o.etaA a).left ≫ μ₀.φ := hP.lift_fst _ _ _
  let p' : Sp k ⟶ (torsion t.G l.A).left := hP.lift p.left x ((pow_eq_one_iff_left p l.A).mp hp)
  obtain ⟨i, W, hW, hW₁, hW₂⟩ := exists_opens_isOpenImmersion_extending_section X U j hN h₁ h₂ h₃ h₄
    (torsion t.G l.A).left (torsion t.G l.A).hom (D.La ⧸ K) (fun i => σ i.out) hEt hsep
    (fun i => hP.lift_snd _ _ _) (fun Ω _ _ u y hy => by
      have hy' : (y ≫ (torsion.ι t.G l.A).left) ≫ t.G.hom = u ≫ j := by
        rw [Category.assoc, hι, hy]
      let z : Over.mk u ⟶ o.t.G := Over.homMk (μ₀.cart.1.lift _ _ hy') (μ₀.cart.1.lift_snd _ _ _)
      have hz : z.left ≫ μ₀.φ = y ≫ (torsion.ι t.G l.A).left := μ₀.cart.1.lift_fst _ _ _
      have hzA : z ^ l.A = 1 := by
        refine (pow_eq_one_iff_of_isGrpPullback μ₀.cart z l.A).mpr ?_
        rw [hz, Category.assoc, hP.w, reassoc_of% hy]
        exact (Category.assoc _ _ _).symm
      obtain ⟨β, hβ⟩ := Spec.map_surjective (u ≫ s)
      obtain ⟨-, I, -, hI, -⟩ := o.geom Ω u β.hom hβ.symm
      obtain ⟨a, ha⟩ := (I.onto l.A l.A_pos z).mp hzA
      refine ⟨QuotientAddGroup.mk a, hP.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hσ, hout, ← hz, ← ha, ← hI, Over.comp_left, Category.assoc]
        rfl
      · rw [hy, Category.assoc, hP.lift_snd])
    (p' (IsLocalRing.closedPoint k))
  have hr : Set.range p' ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint k), Scheme.Opens.range_ι]
    exact hW
  refine ⟨i.out, W, W.ι ≫ (torsion t.G l.A).hom, hW₁, W.ι ≫ (torsion.ι t.G l.A).left,
    IsOpenImmersion.lift W.ι p' hr, ?_, ?_, ?_, ?_⟩
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_snd _ _ _
  · rw [Category.assoc, hι]
  · rw [reassoc_of% hW₂, hσ]
  · rw [IsOpenImmersion.lift_fac_assoc]; exact hP.lift_fst _ _ _

end GlobalTheory.TorsionSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanning
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FibreEmbed

open GlobalTheory.AmpleSpan GlobalTheory.SegreCoord GlobalTheory.ProjSpace GlobalTheory.Cartier TopologicalSpace

theorem embedsBy_fibre (hA : Out.AmpleSt) (hB : Out.PolBaseChangeSt) {S : Scheme.{0}} (P : Out.PolAV S) {K : Type}
    [Field K] (x : Sp K ⟶ S) {N : ℕ} (hN : 4 ≤ N) {I : Type} [Fintype I]
    (t : I → LB.Sec (Out.LPow P.A P.L N (Over.mk x)))
    (ht : Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Over.mk x))) = ⊤) :
    EmbedsBy (fst (Over.mk x) P.A).left t := by
  obtain ⟨P', g, hg, -, -, w⟩ := hB S _ x P
  have h : IsPullback (snd (Over.mk x) P.A).left (fst (Over.mk x) P.A).left P.A.hom x :=
    (IsPullback.of_hasPullback x P.A.hom).flip
  let e := h.isoIsPullback _ _ hg
  have he : e.hom ≫ g = (snd (Over.mk x) P.A).left := h.isoIsPullback_hom_fst _ _ hg
  have he' : e.hom ≫ P'.A.hom = (fst (Over.mk x) P.A).left := h.isoIsPullback_hom_snd _ _ hg
  have haff : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Sp K))
  have sq : IsPullback e.hom (fst (Over.mk x) P.A).left P'.A.hom
      ((𝟙 (Sp K) ≫ (Sp K).topIso.inv) ≫ Scheme.Opens.ι (⊤ : (Sp K).Opens)) := by
    rw [comp_topIso_inv_ι]
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id (Sp K))
      ⟨he'.trans (Category.comp_id _).symm⟩
  obtain ⟨M, s, hs⟩ := exists_embedsBy_of_isPullback P'.A P'.isLB (hA _ P' N hN).2 (isAffineOpen_top _) sq
    (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  obtain ⟨w', hw'⟩ := LBIso.symm w
  have hP := DVR.linComb_isLB P'.L P'.isLB (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))
  have hQ : (Out.LPow P.A P.L N (Over.mk x)).IsLB := DVR.linComb_isLB P.L P.isLB _ _
  obtain ⟨W, hW⟩ : LBIso (Out.LPow P.A P.L N (Over.mk x))
      ((LB.LinComb P'.L (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullSame P.L _ _ _ (𝟙 _) fun _ => he.symm.trans (Category.id_comp _).symm)
      (Geo.Tor.chartPullPull _ _ _ rfl)
      (LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => e.hom) (fun _ => (N : ℤ))))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hQ (s i)
  have hs₂ : EmbedsBy (fst (Over.mk x) P.A).left s' := by
    refine hs.pull (ψ := 𝟙 _) (g := 𝟙 _) IsPullback.of_id_fst fun y => ?_
    obtain ⟨j, hj⟩ := exists_chart hP y
    obtain ⟨k, hk⟩ := exists_chart hQ y
    refine ⟨j, k, hj, hk, gw W (𝟙 _) y j k, fun i => ?_⟩
    have := hs' i _ (𝟙 _) y j k hj hk
    rwa [Category.id_comp] at this
  have := P.isAb.proper
  have : UniversallyClosed (fst (Over.mk x) P.A).left :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h inferInstance
  exact hs₂.of_inSpan fun j => (inSpan_iff_mem_span P.A t _).2 (by rw [ht]; trivial)

variable {X : Scheme.{0}} {A B : LB X} {σ : Type} {a : σ → A.Sec} {b : σ → B.Sec} {T : Type} [CommRing T]
  {x : Sp T ⟶ X} {v : σ → T}

theorem gs_of_secMaps {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) (y : Sp T) {p : B.ι} {q : A.ι}
    (hp : x y ∈ B.U p) (hq : x y ∈ A.U q) :
    ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((b i).f p) = u * gs x y _ ((a i).f q) := by
  have hm : x y ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  refine ⟨gm x y (B.U p ⊓ A.U q) (w.s (p, q)), fun i => ?_⟩
  exact (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (hw i (p, q))).trans ((gs_mul x y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit x y _ hm _) (gs_res x y _ hm _))))

theorem loc_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) :
    Loc A a x v ↔ Loc B b x v := by
  refine ⟨fun h y p hp => ?_, fun h y q hq => ?_⟩
  · obtain ⟨q, hq⟩ := exists_chart hA (x y)
    obtain ⟨u, hu⟩ := h y q hq
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u' * u, fun i => by rw [hu', hu, Units.val_mul, mul_left_comm]⟩
  · obtain ⟨p, hp⟩ := exists_chart hB (x y)
    obtain ⟨u, hu⟩ := h y p hp
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u'⁻¹ * u, fun i => by rw [Units.val_mul, mul_left_comm, ← hu, hu', Units.inv_mul_cancel_left]⟩

theorem span_eq_top_of_loc (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (h : Loc A a x v) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let y : Sp T := ⟨m, hm.isPrime⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hi
  obtain ⟨u, hu⟩ := h y k hk
  have h1 := (mem_nonzeroLocus_iff_gs (a i) x y hk).1 hi
  rw [hu] at h1
  have h2 := ((Sp T).mem_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) y trivial).2
    (isUnit_of_mul_isUnit_left h1)
  have h3 := (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).le h2
  exact h3 (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem secCoord_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i))
    (ha : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (hb : ⨆ i, Out.nonzeroLocus (b i) = ⊤) :
    SecCoord A a x v ↔ SecCoord B b x v :=
  ⟨fun h => secCoord_of_loc (span_eq_top_of_loc ha (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).1 (loc_of_secCoord h)),
    fun h => secCoord_of_loc (span_eq_top_of_loc hb (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).2 (loc_of_secCoord h))⟩

theorem projRep_bot (R : Type) [CommRing R] {N : ℕ} (e : σ ≃ Fin (N + 1)) :
    ProjRep (⊥ : Ideal (MvPolynomial σ R)) (PSpace.str R N) ((O1 R N).pull (𝟙 _))
      (fun c => secPull (coord R N (e c)) (𝟙 _)) := by
  refine ⟨pull_isLB (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩
  · obtain ⟨hv, -⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx) v).1 h
    rw [ProjCoord.range_comp_symm] at hv
    exact ⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩
  · rw [← ProjCoord.range_comp_symm e] at hv
    have pt_str : ∀ (c : R →+* R') (v : Fin (N + 1) → R')
        (hv : Ideal.span (Set.range v) = ⊤), pt c v hv ≫ PSpace.str R N = spMap c := by
      intro c v hv
      rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
    refine ⟨pt β _ hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩
    · exact (ProjCoord.secCoord_iff e (𝟙 _) β _ (by simpa using pt_str β _ hv) v).2 ⟨hv, Category.comp_id _⟩
    · obtain ⟨_, h⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx.1) v).1 hx.2
      exact (Category.comp_id _).symm.trans h

theorem projRep_of_embedsBy {R : Type} [CommRing R] (f : X ⟶ Sp R) (hA : A.IsLB) {N : ℕ} (e : σ ≃ Fin (N + 1))
    (h : EmbedsBy f (fun j => a (e.symm j))) : ProjRep (idealOf f A a (𝟙 X)) f A a := by
  have : Finite σ := Finite.of_equiv _ e.symm
  obtain ⟨hs, hcl⟩ := (veryAmpleBy_iff f (fun j => a (e.symm j))).1 ((embedsBy_spec_iff f _).1 h)
  have key := _root_.GlobalTheory.ZM.ClosedCoord.projRep_closed R σ ⊥ _ X (PSpace.str R N) _ _ (toProj f _ hs) A a (projRep_bot R e) hcl hA
    fun R' _ y v => by
      let c : R →+* R' := (Spec.preimage (y ≫ f)).hom
      have hc : (y ≫ toProj f _ hs) ≫ PSpace.str R N = spMap c := by
        rw [Category.assoc, toProj_str]
        exact (Spec.map_preimage (y ≫ f)).symm
      have h1 := ProjCoord.secCoord_iff e (toProj f _ hs) c y hc v
      have h2 := ProjCoord.secCoord_iff e (𝟙 _) c (y ≫ toProj f _ hs) (by rw [Category.comp_id]; exact hc) v
      rw [Category.comp_id] at h2
      refine Iff.trans ?_ (h1.trans h2.symm)
      refine (secCoord_iff_of_secMaps (pull_isLB (O1_isLB R N) _) hA (w := toProjIso f _ hs) (fun i => ?_) ?_ ?_).symm
      · simpa only [Equiv.symm_apply_apply] using secMaps_toProjIso f _ hs (e i)
      · exact (e.iSup_comp (g := fun j => Out.nonzeroLocus (secPull (coord R N j) (toProj f _ hs)))).trans
          (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) _)
      · exact (e.symm.iSup_comp (g := fun c => Out.nonzeroLocus (a c))).symm.trans hs
  rwa [toProj_str] at key

theorem projRep_fibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  intro hL _ S P K _ _ x k I _ σ hk hσ
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have hN : 4 ≤ N := by exact_mod_cast hk
  have := Fintype.ofFinite I
  have h₀ := embedsBy_fibre hL.ample hL.polBaseChange P x hN σ hσ
  have hne : Nonempty I := by
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨i, -⟩ := Opens.mem_iSup.1 (h₀.1.ge (Set.mem_univ
      ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ P.A)).left p)))
    exact ⟨i⟩
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card I = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  let e := Fintype.equivFinOfCardEq hM
  refine projRep_of_embedsBy _ (DVR.linComb_isLB P.L P.isLB _ _) e
    (embedsBy_fibre hL.ample hL.polBaseChange P x hN _ ?_)
  rw [← hσ]
  exact congrArg _ (e.symm.surjective.range_comp
    fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L N (Over.mk x)))

end GlobalTheory.FibreEmbed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def EndCharPolySt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A), IsMonHom ψ →
    ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * P.g ∧ ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 →
      ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ l ^ r = 1) →
        (∀ z : baseOver (Sp K) ⟶ P.A, z ^ l ^ r = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
        ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)),
          (∀ i, y i ≫ ψ = linComb y fun k => (B k i).val) → B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))

def RosatiPositiveSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (φ φ' : P.A ⟶ P.A), IsMonHom φ → IsMonHom φ' →
    RosatiAdj P.A P.L φ φ' → φ ≠ 1 → ∀ t : ℤ, IndefiniteRowSideFullHecke.FirstOrderRigidityLevel.HasTrace P (φ' ≫ φ) t → 0 < t

end GlobalTheory.Published

namespace GlobalTheory.ThetaDetCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section AdjRing

open CechPic MulOpposite

variable {K : Type} [Field K] {P : PolAV (Sp K)}





end AdjRing

section Trace

open ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)} {M : ℕ} {y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A)}
  {O : Type} [Ring O]

variable [IsAlgClosed K]

end Trace

section Positive

variable {K : Type} [Field K] [IsAlgClosed K] {P : PolAV (Sp K)} {O : Type} [Ring O] [StarRing O]

end Positive

end GlobalTheory.ThetaDetCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelRingChange

variable {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}}

theorem spMap_comp' {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (a : R₁ →+* R₂) (b : R₂ →+* R₃) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (x : Sp R₂ ⟶ Sp R₁) :
    ∃ a : R₁ →+* R₂, spMap a = x := by
  obtain ⟨a, ha⟩ := Spec.map_surjective x
  exact ⟨a.hom, ha⟩

theorem spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {a b : R₁ →+* R₂} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

def down (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ s')
      have e : β'.comp j = β := by
        apply spMap_inj
        rw [spMap_comp', hβ', Category.assoc, hx]
      refine c.geom K x β' z hβ'.symm ?_
      rw [hz, ← e, ← hj]; rfl }

def up (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ (s' ≫ spMap j)) : SiegPre h k ζ' s' :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      refine c.geom K x (β.comp j) z ?_ ?_
      · rw [spMap_comp', ← hx, Category.assoc]
      · rw [hz, ← hj]; rfl }

theorem siegPre_pull_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  intro h k B B' _ _ ζ ζ' j S S' s s' f hj hf
  refine ⟨fun c => ?_, fun c c' hc hp => ?_, fun c' => ?_⟩
  · obtain ⟨c₀, h₀⟩ := (_root_.GlobalTheory.siegPre_pullback h k B ζ S S' s _ f c hf).1
    exact ⟨up j hj c₀, h₀⟩
  · exact (_root_.GlobalTheory.siegPre_pullback h k B ζ S S' s _ f c hf).2 (down j hj c') hc hp
  · have e := (_root_.GlobalTheory.SiegelPullComp.id_comp_cancel h k B' B' B' ζ' ζ' ζ' S' S' S' s' s' s' c' c' c' (𝟙 _) (𝟙 _)).1
    exact ⟨down j hj c', e, e⟩

end GlobalTheory.SiegelRingChange
end
end

