module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormValFUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianLocusEqTrivialTorusLocusProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.AbelianPart

theorem isProper_snd_iff {Z A B T : Scheme.{0}} (e : A ≅ B) (f : A ⟶ Z) (g : B ⟶ Z) (h : e.hom ≫ g = f)
    (t : T ⟶ Z) : IsProper (pullback.snd f t) ↔ IsProper (pullback.snd g t) := by
  subst h
  have P : IsPullback (pullback.fst g t ≫ e.inv) (pullback.snd g t) (e.hom ≫ g) t :=
    IsPullback.of_iso (IsPullback.of_hasPullback g t) (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  constructor
  · intro h
    rw [← P.isoPullback_hom_snd]
    infer_instance
  · intro h
    rw [← P.isoPullback_inv_snd]
    infer_instance

theorem abLocus_congr {Z : Scheme.{0}} (A B : Over Z) (e : A.left ≅ B.left) (h : e.hom ≫ B.hom = A.hom) :
    abLocus A = abLocus B := by
  ext z
  exact ⟨fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).1 (H K t ht),
    fun H K _ _ t ht => (isProper_snd_iff e _ _ h t).2 (H K t ht)⟩

theorem isProper_snd_of_le {Z A : Scheme.{0}} (f : A ⟶ Z) {U V : Z.Opens} (h : U ≤ V)
    [IsProper (pullback.snd f V.ι)] : IsProper (pullback.snd f U.ι) := by
  have P := (IsPullback.of_hasPullback (pullback.snd f V.ι) (Z.homOfLE h)).paste_horiz
    (IsPullback.of_hasPullback f V.ι)
  rw [Scheme.homOfLE_ι] at P
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem not_mem_abLocus (C : GlobalTheory.ZJ.Core) (L : C.Law) {p : ℕ} [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z)
    (τ : C.Test y) (h : ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) :
    y (GlobalTheory.ZJ.cPt p) ∉ abLocus C.GG := by
  intro hm
  obtain ⟨hsep, hlft, -⟩ := GlobalTheory.ZJ.core_basic C
  have hc : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀ := (L.test p y τ).1
  have P := (IsPullback.of_hasPullback τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)).paste_horiz hc
  rw [Category.assoc, τ.fac] at P
  refine h ((GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff C.GG P (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p))).1 ?_)
  have e : GlobalTheory.ZJ.rPt p (IsLocalRing.closedPoint (GlobalTheory.ZJ.kb p)) = GlobalTheory.ZJ.cPt p :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue (GlobalTheory.ZJ.OO p))
  rw [← e] at hm
  exact hm

theorem ab : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (Z : ZHPre ρ M U₀), (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) → Nonempty ex.core.Law → ex.core.HasTests → ex.core.HasCharts → IsOpen {z : M.Z | S.TT M z = ⊥} → (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j))) → Z.Ab := by
  rintro o Ω _ _ _ _ S ρ M U₀ EE Q ex Z ⟨e, he, -⟩ ⟨L⟩ hT hC hO h₁ h₂
  obtain ⟨hab, hpr⟩ := GlobalTheory.ZJ.AbelianLocus.abLocus_eq ex.core L hT hC ⟨_, hO⟩ h₁ (fun z hz hn => by
    obtain ⟨p, _, y, τ, rfl, h⟩ := h₂ z hz hn
    exact not_mem_abLocus ex.core L y τ h)
  have hE : abLocus Z.G = {z | S.TT M z = ⊥} := (abLocus_congr Z.G ex.core.GG e he).trans hab
  refine ⟨hE, fun W hW => ?_⟩
  rw [hE] at hW
  exact (isProper_snd_iff e _ _ he W.ι).2
    (@isProper_snd_of_le _ _ ex.core.GG.hom W ⟨_, hO⟩ hW hpr)

end GlobalTheory.ZH.AbelianPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLaws
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.ThetaInValues

theorem brUth_of_laws : Laws → BrUthSt := fun hL _ _ _ _ _ _ _ _ _ _ _ ν =>
  ⟨fun _ _ _ _ hb hb' => weilIs_weil ν hL.globalFns hb hb', fun _ hm hF _ _ hb =>
    ⟨isThetaPt_uth ν hL.globalFns hm hF hb, isCoordPt_uth ν hL.globalFns hm hF hb⟩⟩

end GlobalTheory.ThetaInValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointExtendsPowerSeriesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_generic_point_extends_powerSeries : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (m : ℕ) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (t : SAB H Z) (_ : SABMap t Y.t π), IsFinite π → Surjective π → Nonempty (AmpFrames t.G t.PP.L (m ^ 2)) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → ∀ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ → y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → (∃ θ, IsFrame Y.t.G Y.t.PP.L 1 (y₁ ≫ Y.j) (fun _ : Fin 1 => θ)) → (∃ (n : ℕ) (f : Fin n → _), IsFrame Y.t.G Y.t.PP.L (m ^ 2) (y₁ ≫ Y.j) f) → ∃ χ : Sp (PowerSeries O') ⟶ Y.X, jK _ ≫ χ = y ≫ Y.j := by
  first | exact @GlobalTheory.LN.ArcExtends.exists_extension | exact GlobalTheory.LN.ArcExtends.exists_extension | (intros; apply GlobalTheory.LN.ArcExtends.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositive
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitNorm

theorem norms_of_arc_input : AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing O') C], CExt O' ⊥ C → ∀ A : Lift a C, A.ν.IntN → (∀ χ, ‖(A.N.ψ χ : C)‖ = 1) ∧ (∀ m, Odd m → ∀ (p : A.N.QT (m ^ 2)) χ, ‖A.N.txT m p χ‖ ≤ 1) ∧ ∀ u : Cˣ, ‖(u : C)‖ < 1 → ∃ q : QuadraticMap ℤ A.N.X ℝ, (A.N.twist A.be u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (A.be.be y y / 2) := by
  intro E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ C _ _ _ hC A ⟨S, hS, hν⟩
  obtain ⟨s, hs⟩ := exists_base hS hC.1
  have hθ := norm_θ hS hν hs
  have hσ := norm_σ hS hν hs
  have hth := norm_th hS hν hs
  have hψ := fun χ => norm_ψ hS hν hs χ (a.gen _)
  exact ⟨hψ, fun m hm p χ => norm_txT A.N hθ hσ hψ hth hm.pos.ne' p χ, twist_int A.N hθ hσ hψ hth A.be⟩

end GlobalTheory.Ex.UnitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CharEqZeroOfIsProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AbelianLocus

theorem char_eq_zero_of_isProper {k : Type} [Field k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G]
    (D : E.GtDatum G) [IsProper G.hom] (a : E.X) : a = 0 := by
  have hi := D.i_hom
  have h1 := GlobalTheory.splitTorus_hom_proper_trivial_field k E.X G D.i hi
  have h2 : 𝟙 (splitTorus (Sp k) E.X) = toUnit _ ≫ η[splitTorus (Sp k) E.X] := by
    refine D.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.id_comp, Category.assoc, IsMonHom.one_hom]
    exact h1
  have h3 := Rosenlicht.torusGamma_chi k E.X a
  rw [Rosenlicht.chi, h2, Rosenlicht.coord_toUnit_comp, Rosenlicht.torusGamma_const] at h3
  by_contra ha
  have h4 := congrArg (fun f : AddMonoidAlgebra k E.X => f.coeff a) h3
  simp [Ne.symm ha] at h4

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem perp_top_eq_bot (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem proj_eq_one {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_crd_ne_zero (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {K : Type} [Field K]
    (x : Sp K ⟶ Q.P.left) {z : M.Z} (hz : Set.range (x ≫ Q.P.hom) = {z}) (hc : IsClosed ({z} : Set M.Z))
    (hT : S.TT M z = ⊥) : ∃ v, Crd Q.O1 Q.st x v ∧ v ≠ 0 := by
  have hxz : ∀ s, Q.P.hom (x s) = z := fun s => by
    have : (x ≫ Q.P.hom) s ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  obtain ⟨l, hl⟩ : ∃ l, z ∈ Q.W l := TopologicalSpace.Opens.mem_iSup.1 (by rw [Q.cover]; trivial)
  have hr : Set.range x ⊆ Set.range (Q.P.hom ⁻¹ᵁ Q.W l).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    change Q.P.hom (x s) ∈ Q.W l
    rwa [hxz]
  obtain ⟨x', rfl⟩ : ∃ x', x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ x hr⟩
  have hcov := (Q.imm l).1
  have hm : x' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (Q.σ l i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨w, hw⟩ : ∃ w, Crd _ (Q.σ l) x' w :=
    ⟨_, m, 1, (CrdCalc.top_le_iff x' _).2 (Scheme.basicOpen_le _ _ hm), fun _ => rfl⟩
  have hwi := ((CrdCalc.crd_isUnit_iff i hw).2 ((CrdCalc.top_le_iff x' _).2 hi)).ne_zero
  refine ⟨_, Q.rel l K x' _ hw, fun h0 => hwi ?_⟩
  have hBm : ∀ a b, Q.B l a b ∈ M.O z := fun a => hB.zero z hc _
    (by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨a, rfl⟩)
    (by rw [proj_eq_one hT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec])
  let B' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, hBm a b⟩
  let C' : Matrix S.J S.J (M.O z) := fun a b => ⟨_, RatModel.valF_mem_O hl (Q.c l a b)⟩
  have h1 : C' * B' = 1 := by
    apply Matrix.map_injective (f := (M.O z).val.toRingHom) Subtype.val_injective
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Q.c_inv l
  have h2 := congrArg (fun A => A.map (RatModel.valHom _ z hz)) (mul_eq_one_comm.1 h1)
  beta_reduce at h2
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  have h3 : C'.map (RatModel.valHom _ z hz) =
      (Q.c l).map (valR (x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (Q.W l)) := by
    ext a b
    rw [← Category.assoc]
    exact RatModel.val_valF (by rw [hz]; exact Set.singleton_subset_iff.2 hl) _
  have h4 : w = 0 := by
    rw [← Matrix.one_mulVec w, ← h2, ← Matrix.mulVec_mulVec, h3, h0, Matrix.mulVec_zero]
  rw [h4]; rfl

theorem mem_G [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (w : Q.P.left)
    (hw : IsClosed ({w} : Set Q.P.left)) (hT : S.TT M (Q.P.hom w) = ⊥) : w ∈ Q.G := by
  have := Q.proper
  have hc : IsClosed ({Q.P.hom w} : Set M.Z) := by
    rw [← Set.image_singleton]
    exact Q.P.hom.isClosedMap _ hw
  let x : Sp (Q.P.left.residueField w) ⟶ Q.P.left := Q.P.left.fromSpecResidueField w
  have hx : ∀ s, x s = w := fun s => Scheme.fromSpecResidueField_apply w s
  have hz : Set.range (x ≫ Q.P.hom) = {Q.P.hom w} := by
    rw [RatModel.range_eq_singleton _ (IsLocalRing.closedPoint _)]
    exact congrArg (fun a => {Q.P.hom a}) (hx _)
  obtain ⟨v, hv, hv0⟩ := exists_crd_ne_zero hB Q x hz hc hT
  have h := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q _ x _
    (Spec.preimage (x ≫ Q.P.hom ≫ M.s)).hom v hz (Or.inl hc) (Spec.map_preimage _).symm hv).2 (by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
      refine ⟨i, ?_⟩
      rw [proj_eq_one hT, Finset.sum_eq_single i]
      · simpa using hi
      · intro j _ hj
        simp [hj]
      · simp)
  rw [← hx (IsLocalRing.closedPoint _)]
  exact (CrdCalc.top_le_iff x _).1 h

theorem abelian_locus : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → IsOpen {z : M.Z | S.TT M z = ⊥} ∧ (∀ w : Q.P.left, IsClosed ({w} : Set Q.P.left) → S.TT M (Q.P.hom w) = ⊥ → w ∈ Q.G) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.TT M z ≠ ⊥ → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (τ : ex.core.Test y), y (GlobalTheory.ZJ.cPt p) = z ∧ ¬ IsProper (pullback.snd τ.H.hom (GlobalTheory.ZJ.rPt p ≫ spMap τ.j)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hbig hgeo _
  refine ⟨isOpen_iff_forall_mem_open.2 fun z hz => ⟨_, fun z' h => ?_, OpenPart.isOpen_supI_subset (S := S) z,
    fun _ h => h⟩, mem_G hB Q, fun z hz hT => ?_⟩
  · exact le_bot_iff.1 ((OpenPart.TT_le_TT h).trans (le_of_eq hz))
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hbig hgeo
  obtain ⟨p, hp, y, hy⟩ := h2 z hz
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := h1 p y hy.2
  obtain ⟨τ, e, he, -⟩ := _root_.GlobalTheory.ZH.Clos.exists_core_test_of_geoTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hbig
  refine ⟨p, hp, y, τ, hy.1, fun hpr => hT ?_⟩
  have : IsProper t.mod.Φ.G.hom := by
    rw [← he] at hpr
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).1 hpr
  have h0 := char_eq_zero_of_isProper t.mod.Φ.E t.mod.Φ.G t.mod.Φ.D
  obtain ⟨e', -⟩ := t.mt
  have hk : t.τ.yy.ker = ⊤ := by
    refine top_unique fun a _ => ?_
    obtain ⟨α, hα⟩ := QuotientAddGroup.mk_surjective (t.τ.yy a)
    have : α = 0 := (e'.trans t.mod.xe.symm).map_eq_zero_iff.1 (h0 _)
    rw [AddMonoidHom.mem_ker, ← hα, this]
    rfl
  rw [ThetaSys.TT, hB.atTest z p y y₀ t.τ hy c.at_, hk, perp_top_eq_bot]

end GlobalTheory.ZH.AbelianLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.CoreTests

theorem image_iff {T H B G B' F P : Scheme.{0}} (h : H ⟶ B) (s : T ⟶ B) (g : G ⟶ B') (s' : T ⟶ B')
    (r : F ⟶ G) (q : F ⟶ T) (cart : IsPullback r q g s') (u : H ⟶ P) (v : G ⟶ P)
    (e : pullback h s ≅ F) (e₁ : e.hom ≫ q = pullback.snd _ _) (e₂ : e.hom ≫ r ≫ v = pullback.fst _ _ ≫ u)
    (x : T ⟶ P) :
    (∃ c : T ⟶ H, c ≫ h = s ∧ c ≫ u = x) ↔ ∃ c' : T ⟶ G, c' ≫ g = s' ∧ c' ≫ v = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨pullback.lift c (𝟙 T) (by simpa using hc) ≫ e.hom ≫ r, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [cart.w, reassoc_of% e₁, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [e₂, pullback.lift_fst_assoc]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨cart.lift c (𝟙 T) (by simpa using hc) ≫ e.inv ≫ pullback.fst _ _, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [pullback.condition, ← reassoc_of% e₁, e.inv_hom_id_assoc, cart.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [← e₂, e.inv_hom_id_assoc, cart.lift_fst_assoc]

theorem exists_test (hL : GlobalTheory.UT.LL) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (hS : S.Big) (hG : ρ.HasGeo)
    (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (hy : ex.core.Cl y) :
    ∃ τ : ex.core.Test y, ∀ x : Sp (GlobalTheory.ZJ.kb p) ⟶ Q.P.left, x ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y →
      ((∃ c : Sp (GlobalTheory.ZJ.kb p) ⟶ τ.H.left, c ≫ τ.H.hom = GlobalTheory.ZJ.rPt p ≫ spMap τ.j ∧ c ≫ τ.f ≫ Q.G.ι = x) ↔
        (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := (_root_.GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hy
  obtain ⟨τ, e, e₁, e₂⟩ := _root_.GlobalTheory.ZH.Clos.exists_core_test_of_geoTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  refine ⟨τ, fun x hx => ?_⟩
  exact (image_iff _ _ _ _ _ _ t.mod.cart.1 _ _ e e₁ e₂ x).trans
    (_root_.GlobalTheory.ZH.TestFib.image_special_fibre_iff hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x hx)

end GlobalTheory.ZH.CoreTests

theorem GlobalTheory.ZH.Clos.Ext.hasTests_and_indep : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have key := GlobalTheory.ZH.CoreTests.exists_test hL o Ω S ρ M U₀ EE hB Q ex hS hG
  have hT : ex.core.HasTests := fun p _ y hy => ⟨(key p y hy).choose⟩
  refine ⟨hT, _root_.GlobalTheory.ZJ.Core.indep_of_special_fibres _ hT fun p _ y y' hy hy' hr => ?_⟩
  obtain ⟨τ, hτ⟩ := key p y hy
  obtain ⟨τ', hτ'⟩ := key p y' hy'
  refine ⟨τ, τ', fun c hc => ?_⟩
  have hx : (c ≫ τ.f ≫ Q.G.ι) ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y := by
    have h : c ≫ τ.f ≫ ex.core.GG.hom = GlobalTheory.ZJ.rPt p ≫ y := by
      rw [τ.f_over, reassoc_of% hc, τ.fac]
    simp only [Category.assoc]
    exact h
  obtain ⟨c', hc', hf⟩ := (hτ' _ (hx.trans hr)).2 ((hτ _ hx).1 ⟨c, hc, rfl⟩)
  refine ⟨c', hc', ?_⟩
  have : Mono ex.core.G.ι := inferInstance
  rw [← cancel_mono ex.core.G.ι, Category.assoc, Category.assoc]
  exact hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CrossIdentity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.FormalGeneric GlobalTheory.SectionRingIso GlobalTheory.FormalPoint in
theorem GlobalTheory.GenericIso.cross_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), ∀ (B : Type) [CommRing B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) → ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' → ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL → (∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g) → ∀ (k : ℕ) (σ τ : H0 U.LG.L k) (σ' τ' : H0 U'.LG.L k), GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k σ σ' → GlobalTheory.GenericIso.AgreeAll U.toUnifPre U'.toUnifPre hD j k τ τ' → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z), gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (τ'.f (fun _ => jL')) = gs (ρ ≫ g) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (τ.f (fun _ => jL)) * gs (ρ ≫ g') z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL')) := by
  intro R _ _ I _ D D' A A' G G' _ _ _ _ _ _ U U' hD j B _ _ g' g jL jL' hB hg' c' c hgg k σ τ σ' τ' hσ hτ Z ρ z
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have ex : ∀ s : H0 U.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g) z (fun _ => jL) := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g (ch U.LG.L fun _ => jL) ⊤ (fun _ _ => mem_ch.2 (c trivial)) ρ z trivial _⟩
  have ex' : ∀ s : H0 U'.LG.L k, ∃ a : Γ(Spec (CommRingCat.of B), ⊤),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl s (ρ ≫ g') z (fun _ => jL') := fun s =>
    ⟨_, fun Z ρ z => gs_appLE g' (ch U'.LG.L fun _ => jL') ⊤ (fun _ _ => mem_ch.2 (c' trivial)) ρ z trivial _⟩
  choose b hb using ex
  choose b' hb' using ex'
  have pr : ∀ (s : H0 U.LG.L k) (s' : H0 U'.LG.L k) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ (b s * b' s') = vl s (ρ ≫ g) z (fun _ => jL) * vl s' (ρ ≫ g') z (fun _ => jL') :=
    fun s s' Z ρ z => (gs_mul ρ z ⊤ trivial _ _).trans (congrArg₂ (· * ·) (hb s Z ρ z) (hb' s' Z ρ z))
  have key : ∀ {T : Type} [CommRing T] (u : Tˣ) (v x y x' y' : T), u.val * x = v * x' → u.val * y = v * y' →
      x * y' = y * x' := fun u v x y x' y' h₁ h₂ => by
    refine (Units.mul_right_inj u).1 ?_
    linear_combination y' * h₁ - x' * h₂
  have E : b σ * b' τ' = b τ * b' σ' := fn_ext_germs (I.map (algebraMap R B)) fun e z => by
    obtain ⟨jM, a₁⟩ := exists_chart D.toPre.P.isLB
      (GlobalTheory.FamFieldPull.prA hD ((U'.gt e).pG.left (reduction I y e z)))
    obtain ⟨jM', a₂⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left (reduction I y e z))
    have a₄ : (fstG I e G').left (reduction I y e z) ∈ U'.LG.L.U jL' :=
      (congrArg (fun q => q z ∈ U'.LG.L.U jL') (hy e)).mpr (c' trivial)
    have a₃ : (fstG I e G).left ((j e).hom.left (reduction I y e z)) ∈ U.LG.L.U jL :=
      (congrArg (fun q => q z ∈ U.LG.L.U jL) (hgg e _ _ _ (hy e))).mpr (c trivial)
    have H₁ := hσ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    have H₂ := hτ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    rw [pr, pr, ← hgg e _ _ _ (hy e), ← hy]
    exact key _ _ _ _ _ _ H₁ H₂
  exact (pr σ τ' Z ρ z).symm.trans ((congrArg (gs ρ z ⊤) E).trans (pr τ σ' Z ρ z))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationRecognitionOfAbelianPartsIsoLabels
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.Recognition

theorem urec_of_abelian : UrCSt → URecSt := by
  intro hC R _ _ D D' h1 h2 h3 h4 C _ _ _ _ _ N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt
  obtain ⟨hA, hg⟩ := _root_.GlobalTheory.MatchParts.match_parts C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt
  obtain ⟨e, hB, hT⟩ := _root_.GlobalTheory.MatchTerm.main C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA
  obtain ⟨I, hOB, hl, hG⟩ := hC R D D' h1 h2 h3 h4 C N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt hA hg e hB hT
  obtain ⟨J, hJ, hJe, hOG⟩ := _root_.GlobalTheory.Ex.RecPeriods.exists_iso_onG C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA e hB hT I hOB
  subst hJ hJe
  exact ⟨J, _root_.GlobalTheory.LabelsAgree.main C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA J hB hOG hl, hG⟩
end GlobalTheory.Ex.Recognition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelianStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  first | exact @GlobalTheory.ZJ.exists_extension_with_section | exact GlobalTheory.ZJ.exists_extension_with_section | (intros; apply GlobalTheory.ZJ.exists_extension_with_section <;> assumption)
end

