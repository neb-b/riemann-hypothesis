module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverChern

open Set

section Cover

variable {n : ℕ} {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}

theorem exists_evenly_covered_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {x : A} (hx : x ∈ U) :
    ∃ W : Set A, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
      glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := by
  classical
  have hfin : ∀ y ∈ U, (m ⁻¹' {y}).Finite := fun y hy => finite_of_encard_eq_coe (hfib y hy)
  have hcard : ∀ y (hy : y ∈ U), (hfin y hy).toFinset.card = d := fun y hy => by
    have h := hfib y hy
    rw [← (hfin y hy).coe_toFinset, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h
  obtain ⟨V, hV, hVd⟩ := (hfin x hx).t2_separation
  have hFc := hcard x hx
  have hFm : ∀ z, z ∈ (hfin x hx).toFinset ↔ m z = x := fun z => by simp
  generalize (hfin x hx).toFinset = F at hFc hFm
  have hzF : ∀ z ∈ F, m z = x := fun z hz => (hFm z).1 hz
  have hzU : ∀ z ∈ F, m z ∈ U := fun z hz => by rwa [hzF z hz]
  have hsheet : ∀ z, z ∈ F → ∃ M : Set B, M ⊆ V z ∧ IsOpen M ∧ z ∈ M ∧ IsOpen (m '' M) ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ m '' M →
        glueMeas e' ρ' (M ∩ m ⁻¹' Q) = glueMeas e ρ Q := fun z hz =>
    GlueCover.exists_sheet hd hρ hd' hρ' hm (hch z (hzU z hz)) (hV z).2 (hV z).1
  choose! M hMV hMo hzM hMi hMQ using hsheet
  refine ⟨(⋂ z ∈ F, m '' M z) ∩ U, (isOpen_biInter_finset hMi).inter hU,
    ⟨mem_iInter₂.2 fun z hz => ⟨z, hzM z hz, hzF z hz⟩, hx⟩, inter_subset_right,
    fun Q hQ hQW => ?_⟩
  have hdisj : ∀ z₁ ∈ F, ∀ z₂ ∈ F, z₁ ≠ z₂ → Disjoint (M z₁) (M z₂) := fun z₁ h₁ z₂ h₂ hne =>
    Disjoint.mono (hMV z₁ h₁) (hMV z₂ h₂) (hVd (hzF z₁ h₁) (hzF z₂ h₂) hne)
  have key : m ⁻¹' Q = ⋃ z ∈ F, (M z ∩ m ⁻¹' Q) := by
    ext w
    constructor
    · intro hw
      have hWx := hQW hw
      have hpre : ∀ z ∈ F, ∃ z', z' ∈ M z ∧ m z' = m w := fun z hz => by
        obtain ⟨z', h₁, h₂⟩ := mem_iInter₂.1 hWx.1 z hz
        exact ⟨z', h₁, h₂⟩
      haveI : Nonempty B := ⟨w⟩
      choose! f hfM hfm using hpre
      have hinj : InjOn f F := fun z₁ h₁ z₂ h₂ h12 => by
        by_contra hne
        exact disjoint_left.1 (hdisj z₁ h₁ z₂ h₂ hne) (hfM z₁ h₁) (h12 ▸ hfM z₂ h₂)
      have hsub : F.image f ⊆ (hfin (m w) hWx.2).toFinset := fun v hv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
        simpa using hfm z hz
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_image_of_injOn hinj, hcard _ hWx.2, hFc])
      have hwm : w ∈ F.image f := by
        rw [heq]
        simp
      obtain ⟨z, hz, hzw⟩ := Finset.mem_image.1 hwm
      exact mem_iUnion₂.2 ⟨z, hz, hzw ▸ hfM z hz, hw⟩
    · intro hw
      obtain ⟨z, _, _, h⟩ := mem_iUnion₂.1 hw
      exact h
  rw [key, measure_biUnion_finset
    (fun z₁ h₁ z₂ h₂ hne => Disjoint.mono inter_subset_left inter_subset_left
      (hdisj z₁ h₁ z₂ h₂ hne))
    (fun z hz => (hMo z hz).measurableSet.inter (hm.measurable hQ)),
    Finset.sum_congr rfl fun z hz => hMQ z hz Q hQ
      fun y hy => mem_iInter₂.1 (hQW hy).1 z hz,
    Finset.sum_const, nsmul_eq_mul, hFc]

theorem glueMeas_preimage_of_cover_on
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (hd' : ∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j))
    (hρ' : ∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y)
    (hm : Continuous m) {U : Set A} (hU : IsOpen U) {d : ℕ}
    (hfib : ∀ x ∈ U, (m ⁻¹' {x}).encard = d)
    (hch : ∀ z, m z ∈ U → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source,
      m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w))
    {S : Set A} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    glueMeas e' ρ' (m ⁻¹' S) = d * glueMeas e ρ S := by
  have hW : ∀ x : U, ∃ W : Set A, IsOpen W ∧ x.1 ∈ W ∧ W ⊆ U ∧
      ∀ Q : Set A, MeasurableSet Q → Q ⊆ W →
        glueMeas e' ρ' (m ⁻¹' Q) = d * glueMeas e ρ Q := fun x =>
    exists_evenly_covered_on hd hρ hd' hρ' hm hU hfib hch x.2
  choose W hWo hxW hWU hWQ using hW
  obtain ⟨C, hC, hCW⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  haveI : Countable C := hC.to_subtype
  have key : (Measure.map m (glueMeas e' ρ')).restrict U =
      ((d : ℝ≥0∞) • glueMeas e ρ).restrict U := by
    refine Measure.ext_of_iUnion_eq_univ
      (s := fun o : Option C => o.elim Uᶜ fun c => W c.1) ?_ fun o => ?_
    · refine eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · have hmem : x ∈ ⋃ i ∈ C, W i := by
          rw [hCW]
          exact mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 hmem
        exact mem_iUnion.2 ⟨some ⟨c, hc⟩, hxc⟩
      · exact mem_iUnion.2 ⟨none, hx⟩
    · cases o with
      | none =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict Uᶜ =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict Uᶜ
        rw [Measure.restrict_restrict hU.measurableSet.compl,
          Measure.restrict_restrict hU.measurableSet.compl, compl_inter_self,
          Measure.restrict_empty, Measure.restrict_empty]
      | some c =>
        show ((Measure.map m (glueMeas e' ρ')).restrict U).restrict (W c.1) =
          (((d : ℝ≥0∞) • glueMeas e ρ).restrict U).restrict (W c.1)
        ext Q hQ
        have hQW := hQ.inter (hWo c.1).measurableSet
        have hQWU := hQW.inter hU.measurableSet
        rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ, Measure.restrict_apply hQW,
          Measure.restrict_apply hQW, Measure.map_apply hm.measurable hQWU,
          hWQ c.1 _ hQWU fun y hy => hy.1.2, Measure.smul_apply, smul_eq_mul]
  have h := congrArg (fun μ : Measure A => μ S) key
  simp only [Measure.restrict_apply hS, inter_eq_left.2 hSU,
    Measure.map_apply hm.measurable hS, Measure.smul_apply, smul_eq_mul] at h
  exact h

end Cover

theorem chernPart_preimage_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ}, IsArithVar p D → IsArithVar q D → ∀ {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} (φ : Weight p σ B), φ.IsCInf → ∀ (ε : ℤˣ) (U : Set (CxPts p σ)), IsOpen U → ∀ (n : ℕ), (∀ y ∈ U, (PtsOver.map π hπ (spMap σ)  ⁻¹' {y}).encard = (n : ℕ∞)) → (∀ y ∈ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) → (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → (∀ (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) → ∀ w ∈ c'.e.source, c'.chernDens (φ.pull π hπ) w = c.chernDens φ (PtsOver.map π hπ (spMap σ) w)) → ∀ (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ U → (φ.pull π hπ).chernPart D ε (PtsOver.map π hπ (spMap σ)  ⁻¹' S) = n * φ.chernPart D ε S := by
  intro k _ X Y _ _ p q D hp hq σ π hπ B φ hφ ε U hU n hfib hchart hlift hdens S hS hSU
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  have hφ' := hφ.pull π hπ
  unfold Weight.chernPart
  refine glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (PtsOver.continuous_map π hπ _) hU hfib (fun z hz => ?_) hS hSU
  · rw [c.chernDens_trans c' hφ hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [c.chernDens_trans c' hφ' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, hc⟩ := hchart _ hz
    obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
    exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by rw [hdens c c' hc' w hw]⟩⟩

end GlobalTheory.CoverChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibreVal

variable {X Y Z : Scheme.{0}}

theorem gs_pow (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by simp only [gs_eq f y U h, map_pow]

theorem gs_sum (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ) (a : κ → Γ(X, U)) :
    gs f y U (S.sum a) = S.sum (fun i => gs f y U (a i)) := by simp only [gs_eq f y U h, map_sum]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem mem_finset_inf {κ : Type} (S : Finset κ) (V : κ → X.Opens) (x : X) (h : ∀ i ∈ S, x ∈ V i) : x ∈ S.inf V :=
  Finset.inf_induction (p := fun W : X.Opens => x ∈ W) trivial (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) h

end GlobalTheory.Mum.FibreVal

theorem GlobalTheory.Mum.FibreVal.pG_app_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {V : D.P.A.left.Opens} (x : Γ(D.P.A.left, V))
    (h : ((pullback.fst D.P.A.hom (thick R I e)).app V).hom x = 0) : (g.pG.left.app V).hom x = 0 := by
  have h' := congrArg (g.q.left.app (pullback.fst D.P.A.hom (thick R I e) ⁻¹ᵁ V)).hom h
  rw [map_zero] at h'
  exact h'

theorem GlobalTheory.Mum.FibreVal.sval_comp_eq_zero {X W Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (g : Z ⟶ W) (p : W ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (h : (p.app (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k)))).hom (s.f (fun k => J ((g ≫ p) ≫ φ k))) = 0) :
    sval s (g ≫ p) z J = 0 := by
  have e1 := gs_pull g p z (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k))) (hJ.mem φ (g ≫ p)) (s.f (fun k => J ((g ≫ p) ≫ φ k)))
  rw [h, gs_zero] at e1
  exact e1.symm


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.FibreVal in
theorem GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  intro R _ _ _ D A G _ _ U Y T g y hP k z J J' hJ hJ'
  let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) := (fun _ => J' (g ≫ (U.gt 0).pG.left), fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left))
  have hpp : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG (maximalIdeal R) 0 G).left)).U pp :=
    ⟨Set.mem_iInter.2 fun _ => hJ' (g ≫ (U.gt 0).pG.left), Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩
  refine ⟨(gm g z _ ((U.w 0).s pp) ^ k)⁻¹, ?_⟩
  intro α b τ F s hT hL hE
  obtain ⟨S, h0, hS⟩ := hE
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB β i)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' (g ≫ D.toPre.Oφ (U.gt 0).pG β i)
  have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ c, (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) c =
        J' (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) c) := by
      rintro (a | a | a) <;> simp [jf, jt, pp]
    intro a c e
    rw [key, key, e]
  have e := hS pp j₁ jf jt rfl hcoh
  have hz : g z ∈ U.expW 0 pp j₁ S jf jt :=
    ⟨⟨hpp, hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩, mem_finset_inf _ _ _ fun β _ =>
      ⟨hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left), hJ'.mem (D.toPre.Oφ (U.gt 0).pG β) g⟩⟩
  have e' := congrArg (gs g z (U.expW 0 pp j₁ S jf jt)) e
  rw [gs_mul g z _ hz, gs_pow g z _ hz, gs_unit g z _ hz, gm_res g z _ hz, gs_res g z _ hz] at e'
  erw [gs_pull g (fstG (maximalIdeal R) 0 G).left z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁) (Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left))] at e'
  rw [gs_sum g z _ hz] at e'
  have hterm : ∀ (β : D.toPre.X) (hβ : β ∈ S),
      gs g z (U.expW 0 pp j₁ S jf jt)
        (((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 pp j₁ jf jt hβ)).op).hom
            (((U.gt 0).pG.left.app _).hom ((F.f β).f (jf β))) *
          (Semi.res (U.expWeight_le_chart_weight 0 pp j₁ jf jt hβ) (((U.gt 0).t β).s (jt β))).val) =
      sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val := by
    intro β hβ
    rw [gs_mul g z _ hz, gs_res g z _ hz, gs_unit g z _ hz]
    erw [gm_res g z _ hz]
    erw [gs_pull g (U.gt 0).pG.left z _ (hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left))]
    rfl
  replace e' := (e'.trans (Finset.sum_congr rfl fun (β : S) _ => hterm β.1 β.2)).trans
    (Finset.sum_attach S (fun β => sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val))
  have hsum : ∑ β ∈ S, sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val =
      sval (F.f α) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t α) g z J').val := by
    apply Finset.sum_eq_single α
    · intro β _ hne
      rw [sval_comp_eq_zero (F.f β) g (U.gt 0).pG.left z hJ' (pG_app_eq_zero (U.gt 0) _ (hL.2 β hne _)), zero_mul]
    · intro hα
      rw [sval_comp_eq_zero (F.f α) g (U.gt 0).pG.left z hJ' (h0 α hα _), zero_mul]
  rw [hsum] at e'
  have hq : (y ≫ Y.q).left = g ≫ (U.gt 0).pG.left := by
    have h1 := (Y.rep.1 T Y.H y (𝟙 Y.H)).1
    rw [Category.comp_id] at h1
    rw [Over.comp_left]
    exact h1.symm.trans hP.1
  have ht : val ((Y.Φ T y).s α) (𝟙 _) z J' = val ((U.gt 0).t α) g z J' :=
    (val_corr hJ' (hP.2 α) (𝟙 _)).trans ((val_pull hJ' _ g (𝟙 _)).trans (by rw [Category.id_comp]))
  rw [hT T y z J' hJ', hq, ht, ← hL.1, ← e',
    sval_of s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J j₁ (fun _ => by rw [Category.comp_id]),
    ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Emb.range_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') :
    (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧
    (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  constructor
  · intro g hg
    obtain ⟨p, hp⟩ : ∃ p, p = E.H.ι g := ⟨_, rfl⟩
    rw [← hp] at hg
    let Ω := G'.left.residueField p
    let x0 : Sp Ω ⟶ G'.left := G'.left.fromSpecResidueField p
    let x : Sp Ω ⟶ S := x0 ≫ G'.hom
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, x0, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hg
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    let w : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ x) :=
      pullback.lift (spMap io ≫ x0) (𝟙 _) (by simp [x])
    let w0 : Sp Ω' := closedPoint Ω'
    have hw : pullback.fst G'.hom (spMap io ≫ x) (w w0) = p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    have hlw : l (w w0) = g := by
      apply E.H.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hl1, ← hp]
      exact hw
    refine ⟨pullback.fst E.Y.hom (spMap (io.comp κ)) (e.hom.left (w w0)), ?_⟩
    rw [← hlw, ← Scheme.Hom.comp_apply, hl2]
    simp only [Scheme.Hom.comp_apply]
  · intro hπ y
    obtain ⟨s, hs⟩ := hπ.surj (closedPoint R)
    let Ω := S.residueField s
    let x : Sp Ω ⟶ S := S.fromSpecResidueField s
    have hx : ∀ w, (x ≫ π) w = closedPoint R := by
      intro w
      simp only [x, Scheme.Hom.comp_apply]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x ≫ π) hx
    obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω x κ hκ
    obtain ⟨w', hw'⟩ := (pullback.fst E.Y.hom (spMap (io.comp κ))).surjective y
    let w := e.inv.left w'
    have hew : e.hom.left w = w' := by
      simp only [w]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id]
      rfl
    refine ⟨l w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply l E.H.ι, hl1,
        ← Scheme.Hom.comp_apply (pullback.fst G'.hom (spMap io ≫ x)) G'.hom, pullback.condition]
      simp only [Scheme.Hom.comp_apply, x]
      rw [Scheme.fromSpecResidueField_apply]
      exact hs
    · rw [← Scheme.Hom.comp_apply, hl2]
      simp only [Scheme.Hom.comp_apply]
      rw [hew, hw']

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

def IsBC {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) : Prop :=
  ∃ (ev₀ : R →+* u.V) (_ : IsLocalHom ev₀) (hD : IsPullDeg ev₀ D.toPre u.D.toPre)
    (bc : u.G ≅ (Over.pullback (specOf ev₀)).obj G),
    IsMonHom bc.hom ∧ IsPullUnif ev₀ hD bc U u.U ∧ (∀ χ, hD.xe (ε χ) = χ) ∧
    (∀ r, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (ev₀ r)) = (ev r : PadicAlgCl p)) ∧
    ∃ t : u.A.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ pullback.fst _ _ = u.φ ∧
      t ≫ FinalForm.φ = genMap u.U ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) ≫ gm

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCoverStatement
section
public theorem GlobalTheory.T.pointwiseCocycle_local_sections_glue_basicOpen_cover :
    type_of% (@GlobalTheory.PtExt.glue_sections) :=
  @GlobalTheory.PtExt.glue_sections
end

