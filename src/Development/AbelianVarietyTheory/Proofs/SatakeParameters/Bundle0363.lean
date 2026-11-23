module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPoints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPointsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
theorem _root_.GlobalTheory.T.exists_forms_transversal_at_complexPoints : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (N : ℕ)
    (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ S : Finset (CxPts p (RingHom.id ℂ)),
    ∃ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n ∧
      (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) ∧ (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)) ∧
      (∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) ∧ ∀ j : Fin d,
        CxPts.ev p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0)) (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) y = 0) ∧
      ∀ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι (f 0))),
        (∀ j : Fin d, CxPts.evHom hy (GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) = 0) →
        RingHom.ker (CxPts.evHom hy) ≤ Ideal.span (Set.range fun j : Fin d => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0)) ⊔
          RingHom.ker (CxPts.evHom hy) ^ 2 := by
  first | exact @GlobalTheory.EtProj.Transv.exists_forms_transversal | exact GlobalTheory.EtProj.Transv.exists_forms_transversal | exact @GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate | exact GlobalTheory.EtProj.Transv.exists_transversal_forms_first_separate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N)

theorem resG_fRatio {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {W : X.Opens} (hW : W ≤ fOpen ι g) {V : (PSpace ℂ N).Opens} (hV : V ≤ Proj.basicOpen (grading ℂ N) g)
    (hWV : W ≤ ι ⁻¹ᵁ V) :
    resG X hW (fRatio ι a g ha hg) = (ι.appLE V W hWV).hom (frac (grading ℂ N) V a g ha hg hV) := by
  have e : fRatio ι a g ha hg = (ι.appLE (Proj.basicOpen (grading ℂ N) g) (fOpen ι g) le_rfl).hom
      (frac (grading ℂ N) _ a g ha hg le_rfl) := by
    unfold fRatio; rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (resG_appLE ι _ hW _).trans (appLE_resG ι hV hWV _).symm

theorem basicOpen_fRatio_le {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n)
    (hg : g ∈ grading ℂ N n) : X.basicOpen (fRatio ι a g ha hg) ≤ fOpen ι a := by
  have e : X.basicOpen (fRatio ι a g ha hg) =
      ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ a g ha hg le_rfl) :=
    (Scheme.preimage_basicOpen ι _).symm
  rw [e, basicOpen_frac]
  exact ι.preimage_mono inf_le_right

variable {d n : ℕ} (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ grading ℂ N n)

theorem isCoordFamily_fRatio (hcov : ⨆ i, fOpen ι (f i) = ⊤) :
    IsCoordFamily (fun i => fOpen ι (f i)) (fun i j => fRatio ι (f j) (f i) (hf j) (hf i)) := by
  refine { cover := hcov
           self := fun i => fRatio_self ι (f i) (hf i)
           mul := ?_
           basicOpen_le := fun i j => basicOpen_fRatio_le ι (hf j) (hf i) }
  intro i j k
  have hWV : fOpen ι (f i) ⊓ fOpen ι (f j) ≤
      ι ⁻¹ᵁ (Proj.basicOpen (grading ℂ N) (f i) ⊓ Proj.basicOpen (grading ℂ N) (f j)) :=
    fun x hx => ⟨hx.1, hx.2⟩
  rw [resG_fRatio ι (hf j) (hf i) _ inf_le_left hWV, resG_fRatio ι (hf k) (hf j) _ inf_le_right hWV,
    resG_fRatio ι (hf k) (hf i) _ inf_le_left hWV, ← map_mul]
  exact congrArg _ (frac_mul_eq (by ring))

def formMap (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤) : X ⟶ PSpace ℂ d :=
  (isCoordFamily_fRatio ι f hf hcov).toHom p

variable (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤)

theorem formMap_preimage (i : Fin (d + 1)) : formMap ι f hf p hcov ⁻¹ᵁ chart ℂ d i = fOpen ι (f i) :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_preimage p i

theorem formMap_str : formMap ι f hf p hcov ≫ PSpace.str ℂ d = p :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_str p

theorem pullRatio_formMap (i j : Fin (d + 1)) :
    pullRatio (formMap ι f hf p hcov) (fOpen ι (f i)) i (formMap_preimage ι f hf p hcov i).ge j =
      fRatio ι (f j) (f i) (hf j) (hf i) :=
  (isCoordFamily_fRatio ι f hf hcov).pullRatio_toHom p i j

theorem isAffineOpen_fOpen [IsClosedImmersion ι] {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N n)
    (hn : 0 < n) : IsAffineOpen (fOpen ι g) :=
  (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg hn).preimage ι

theorem isFinite_formMap [IsClosedImmersion ι] (hp : ι ≫ PSpace.str ℂ N = p) (hn : 0 < n) :
    IsFinite (formMap ι f hf p hcov) := by
  haveI := isProper_str ℂ N
  haveI := isProper_str ℂ d
  have h1 : IsProper (formMap ι f hf p hcov ≫ PSpace.str ℂ d) := by
    rw [formMap_str, ← hp]; infer_instance
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp _ (PSpace.str ℂ d),
    isAffineHom_of_isAffineOpen_preimage_chart _ fun i => by
      rw [formMap_preimage]; exact isAffineOpen_fOpen ι (hf i) hn⟩

theorem germ_appLE {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ U) (x : X) (hx : x ∈ W)
    (s : Γ(Y, U)) : (X.presheaf.germ W x hx).hom ((φ.appLE U W h).hom s) =
      (X.presheaf.germ (φ ⁻¹ᵁ U) x (h hx)).hom ((φ.app U).hom s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ratioSec_eq (i j : Fin (d + 1)) : XCover.ratioSec d i j = ratio ℂ d i j :=
  (awayToSection_mk _ 1 _).trans (frac_eq (by ring))

theorem rat_formMap [IsIntegral X] (j : Fin (d + 1)) (hg : genericPoint X ∈ fOpen ι (f 0)) :
    XCover.rat (formMap ι f hf p hcov) 0 j =
      (X.presheaf.germ (fOpen ι (f 0)) (genericPoint X) hg).hom (fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  have hmem : genericPoint X ∈ formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d 0 :=
    (formMap_preimage ι f hf p hcov 0).ge hg
  rw [XCover.rat, dite_eq_left hmem, ← pullRatio_formMap ι f hf p hcov 0 j, pullRatio, germ_appLE, ratioSec_eq]


open XCover in
theorem exists_finCover_of_isFinite {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField] (hinst : inst = ffAlg p) (φ : X ⟶ PSpace ℂ d) [IsFinite φ]
    (hφ : φ ≫ PSpace.str ℂ d = p) (hgen : ∀ i, genericPoint X ∈ φ ⁻¹ᵁ XCover.chart d i) :
    IsFinCover ℂ X.functionField (crd φ) ∧ IsAffCover p (fun i => φ ⁻¹ᵁ XCover.chart d i) (rB ℂ X.functionField (crd φ)) := by
  have hrat := GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d X φ
  have h00 : rat φ 0 0 = 1 := by
    obtain ⟨h1, h2⟩ := hrat 0 0 0 (hgen 0) (hgen 0)
    rw [div_self h1] at h2
    exact h2
  have hch := GlobalTheory.T.projective_chart_affine_cover d X φ
  have hne : ∀ I : Finset (Fin (d + 1)), genericPoint X ∈ I.inf fun i => φ ⁻¹ᵁ XCover.chart d i := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hgen a, ih⟩
  have hring : ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ y, y ∈ rB ℂ X.functionField (crd φ) I ↔
      ∃ f : Γ(X, I.inf fun i => φ ⁻¹ᵁ XCover.chart d i), (X.presheaf.germ _ (genericPoint X) (hne I)).hom f = y := by
    intro I hI y
    constructor
    · exact GlobalTheory.T.chart_function_field_integral d X p hinst φ hφ hgen I hI (hne I) y
    · rintro ⟨f, rfl⟩
      exact GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios d X p hinst φ hφ hgen I hI (hne I) f
  have h1 : crd φ 0 = 1 := Subtype.ext h00
  haveI : CharZero (fld φ) := charZero_of_injective_algebraMap (algebraMap ℂ (fld φ)).injective
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  refine ⟨IsFinCover.of_charZero ⟨?_, ?_, ?_⟩ (GlobalTheory.T.finite_projection_function_field d X p hinst φ hφ hgen) ?_,
    ⟨?_, fun I hI => hch.2 I hI, hch.1, hne, hring⟩⟩
  · intro i h
    exact (hrat 0 i i (hgen 0) (hgen i)).1 (by simpa [crd_val] using congrArg (fun z : fld φ => (z : X.functionField)) h)
  · simp only [h1, div_one]
    exact AlgebraicIndependent.of_comp (fld φ).val (GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios d X p hinst φ hφ hgen)
  · simp only [h1, div_one]
    rw [eq_top_iff]
    intro z _
    have hle : fld φ ≤ (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => crd φ j.succ)).map (fld φ).val := by
      show IntermediateField.adjoin ℂ _ ≤ _
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨j, rfl⟩
      induction j using Fin.cases with
      | zero => rw [h00]; exact one_mem _
      | succ k => exact (IntermediateField.mem_map _).2 ⟨crd φ k.succ, IntermediateField.subset_adjoin ℂ _ ⟨k, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).1 (hle z.2)
    have : w = z := Subtype.ext hwz
    rwa [← this]
  · intro i
    exact GlobalTheory.T.affine_germ_subalgebra_smooth X p hinst _ (hch.2 {i} (Finset.singleton_nonempty i)) (hne {i}) _
      (hring {i} (Finset.singleton_nonempty i))
  · subst hinst
    rfl

theorem isFinCover_of_forms : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι →
    ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) →
    ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField)
    (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧
    IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧
    ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom
      (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  intro X _ p d _ inst hinst N ι hι hp n f hf hn hcov hg
  haveI : IsFinite (formMap ι f hf p hcov) := isFinite_formMap ι f hf p hcov hp hn
  have hpre := formMap_preimage ι f hf p hcov
  obtain ⟨h1, h2⟩ := exists_finCover_of_isFinite p d hinst (formMap ι f hf p hcov) (formMap_str ι f hf p hcov)
    fun i => (hpre i).ge (hg i)
  have hU : (fun i => formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d i) = fun i => fOpen ι (f i) := funext hpre
  rw [hU] at h2
  exact ⟨_, _, h1, h2, fun j => rat_formMap ι f hf p hcov j (hg 0)⟩

end GlobalTheory.EtProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV


set_option maxHeartbeats 4000000 in
private theorem admissible_at_each_site : Lt.AdmAtEnt2 → AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => DV.Used D μ → OrbitPlaces.Stab0 D → admitted D (sysS H X std) S.Y) := by
  intro hA D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hU hS0
  have hDict := _root_.GlobalTheory.TwV.joint_dict t std J
  have hPair := _root_.GlobalTheory.pairOK_allSites S hDict
  have hPos := _root_.GlobalTheory.TwV.pos_at_site S
  have hMove := _root_.GlobalTheory.TwV.move_at_site S hDict
  have hAway := _root_.GlobalTheory.TwV.away_of_dict S hDict
  have hScal := _root_.GlobalTheory.TwV.scal_at_site S hDict
  have hK1 := _root_.GlobalTheory.TwV.kernelSite_seriesData_below_lastStep S hDict hPair hPos hScal
  obtain ⟨hLaw, hLawIn, hXi⟩ := _root_.GlobalTheory.TwV.site_law_xiIn S hPair hPos hMove hAway
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ S.lam
  haveI := Lt.fracAt Gl u w hg
  have key := hA D L hT Gi Gl Kc Dx cX ex t u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (kaAt X H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)
    S.E S.hfin S.hst S.g S.hLT
    (hT.gat_pos u w hg) ex.tw I (Formalism.L2.PairingIndexBounds.F.lev0At J.Gd u w hg) J.a ∅ t.cc t.δ t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
  have k2 := key S.curve hK1 hXi hLawIn
  refine k2 ⟨ι.toRingHom, Formalism.L2.KerInert.SecondKernelProjection.rdJ I X.onCh ι.toRingHom, Formalism.L2.KerInert.SecondKernelSeries.srOf S.Y, fun j hj => ⟨J.sharp j hj, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tieStab_kaAtAny X H hT (chainAt H hT) (chainMu_cmp_K _) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y hU hS0 j hj.le
    rw [kaAtAny_cls] at h1
    rw [kaAt_cls]
    exact h1
  · refine Formalism.L2.KerInert.SecondKernelProjection.series_reading_entries D L hT Gi Gl Kc Dx cX ex u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds hT (chainMu_cmp_K _) X.onCh std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y ι.toRingHom ?_ j
    intro r
    have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic r).algHom D.what₂.embLL.toRatAlgHom
    show ι (D.what₂.embLL r) = S.E.iK (ex.cmp.embW u w hg r)
    rw [S.hK r hz, ← hι]
  · exact Formalism.L2.KerInert.SecondKernelSeries.series_compatibility_of (D.what₂.places.resChar w) _ S.Y j
  · have hD : S.Del j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        exact _root_.GlobalTheory.TwV.StepZero.del_zero S hDict hPair hPos hLaw
      · exact _root_.GlobalTheory.TwV.StepDel.del_of_pos S hDict hPair hPos hLaw j hpos hj
    obtain ⟨cK, hn, hd⟩ := hD ι.toRingHom (fun z => hι z)
    refine ⟨cK, ?_, ?_, ?_, hd⟩
    · show ‖cK‖ ≤ 1
      rw [hn]
    · show ‖cK⁻¹‖ ≤ 1
      rw [norm_inv, hn, inv_one]
    · intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn

theorem site_cmpLite_siteAdm : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  intro hAdm hCur D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X J hU hS hk
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  refine ⟨⟨(kaAt X H hT).cmp, (kaAt X H hT).cmp_zero, (kaAt X H hT).cmp_K, (kaAt X H hT).rat, (kaAt X H hT).val⟩, ?_⟩
  have std : Lt.StdAtW D Gl u w hg := GlobalTheory.TwU.std_at_served D u w hg L hT Gi Gl J.tied hk
  obtain ⟨S⟩ := _root_.GlobalTheory.TwV.joint_at_nonempty hCur t std J
  have hA : admitted D (sysS H X std) S.Y := admissible_at_each_site hAdm S hU hS
  refine ⟨inferInstance, std, vpOf (D.gat u w hg), vpOf_irreducible (D.gat u w hg),
    eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    Lt.dGT D u (D.what₂.places.resChar w), Lt.dGT_spec (kaAt X H hT), _, S.Y, hA, Lt.dGT_zero _ _ _, fun j => ?_⟩
  unfold Lt.dGT
  split_ifs <;> simp

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SchemeCechComparisonNaturalRefinementStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_cechComparison_natural_refinement : ∀ (X X' : Scheme.{0}) (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)] (f : X' ⟶ X) (hσ : ∀ r, f.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) ((RingHom.id R) r)) (F : X.Modules) (G : X'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (Scheme.Modules.pushforward f).obj G) (ι κ : Type) [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ] (U : ι → X.Opens) (U' : κ → X'.Opens) (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hc' : ⨆ i, U' i = ⊤) (hU' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U' i)) (τ : κ → ι), (∀ k, U' k ≤ f ⁻¹ᵁ U (τ k)) → ∀ (n : ℕ) (x : LinearMap.ker (Cube.d (cechCube R F ⊤ U) (n + 1))) (x' : LinearMap.ker (Cube.d (cechCube R G ⊤ U') (n + 1))), (∀ (t : {t : Finset κ // t.card = n + 1}) (s : {s : Finset ι // s.card = n + 1}) (h : cechOpen ⊤ U' t.1 ≤ f ⁻¹ᵁ cechOpen ⊤ U s.1), Set.InjOn τ (t.1 : Set κ) → s.1 = t.1.image τ → x'.1 t = sortSign τ t.1 • sectionsOn.res R G h (sectionsOn.map R φ (cechOpen ⊤ U s.1) (x.1 s))) → (∀ t : {t : Finset κ // t.card = n + 1}, ¬ Set.InjOn τ (t.1 : Set κ) → x'.1 t = 0) → cechHEquivCoh R hc' hU' G n (cechClass (cechCube R G ⊤ U') n x') = cohOn.pull hσ φ (le_top : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ ⊤) n (cechHEquivCoh R hc hU F n (cechClass (cechCube R F ⊤ U) n x)) := by
  first | (exact @GlobalTheory.cechHEquivCoh_pull) | (exact GlobalTheory.cechHEquivCoh_pull) | (intros; apply GlobalTheory.cechHEquivCoh_pull  <;> assumption)
end

