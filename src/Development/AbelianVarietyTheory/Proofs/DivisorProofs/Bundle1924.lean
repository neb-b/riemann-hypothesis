module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem interNumRed_pull_curve {k : Type} [Field k] {M W : Scheme.{0}} (p : W ⟶ Sp k)
    (f : M ⟶ W) [IsProper p] (C : Closeds M) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom (f ≫ p)
    IsCompleteCurve k C →
    (∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = 0) ∨
    ∃ C' : Closeds W, IsCompleteCurve k C' ∧ ∃ d : ℕ, ∀ L : LB W, L.IsLB →
      interNumRed k C ![L.pull f] = d * interNumRed k C' ![L] := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  have hcomp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
      (f : Y ⟶ X) (g : Z ⟶ Y) :
      cls ((L.pull f).pull g) (LB.isLB_pull (LB.isLB_pull hL f) g) =
        cls (L.pull (g ≫ f)) (LB.isLB_pull hL _) := by
    exact (cls_eq_iff _ _).2 (iso_of_chart (LB.isLB_pull hL _)
      (chartPullLinComb L f (fun _ : PUnit => g) (fun _ => g ≫ f) (fun _ => 1) (𝟙 _)
        fun _ => (Category.id_comp _).symm))
  intro hC
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red hC.isIrreducible
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) :=
    algebraΓOfHom (redι C ≫ f ≫ p)
  let g := redι C ≫ f
  have hsM : strHom k M = f ≫ p := strHom_eq (fun _ => rfl)
  have hsW : strHom k W = p := strHom_eq (fun _ => rfl)
  have hsZ : strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme = g ≫ p :=
    (strHom_eq (f := redι C ≫ f ≫ p) (fun _ => rfl)).trans (Category.assoc _ _ _).symm
  have hpZ : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal C).subscheme)) := by
    have := hC.isProper
    rw [hsM] at this
    rw [hsZ, Category.assoc]
    exact this
  have : IsProper (g ≫ p) := hsZ ▸ hpZ
  have : IsProper g := .of_comp g p
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = 1 :=
    (topologicalKrullDim_red C).trans hC.dim_eq
  have : CompactSpace (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (strHom k _)
  have := isNoetherian_of_locallyOfFiniteType_field
    (strHom k (Scheme.IdealSheafData.vanishingIdeal C).subscheme)
  have hdeg : ∀ L : LB W, L.IsLB → interNumRed k C ![L.pull f] = topSelfIntersection k (L.pull g) 1 := by
    intro L hL
    have hL' := LB.isLB_pull hL f
    refine (interNumOn_eq_interNum_pull (appTop_algebraΓOfHom (redι C) (f ≫ p) rfl)
      (isLB_vecOne hL')).trans ?_
    refine interNum_congr_cls k _ (fun i => by fin_cases i; exact LB.isLB_pull hL' _)
      (fun _ => LB.isLB_pull hL g) fun i => ?_
    fin_cases i
    exact hcomp hL f (redι C)
  by_cases hc : ∀ z, g z = g (genericPoint _)
  · left
    intro L hL
    rw [hdeg L hL]
    exact ArInt.topSelf_pull_eq_zero_of_const k hL g _ hc
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  right
  let φ := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint _) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint _) = genericPoint g.image := by
    have h₁ := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal C).subscheme).image
      φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 :=
    le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (ArInt.one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  letI : Algebra k Γ(g.image, ⊤) := algebraΓOfHom (g.imageι ≫ p)
  have hf : ∀ r : k, φ.appTop (algebraMap k Γ(g.image, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) r :=
    appTop_algebraΓOfHom φ (g.imageι ≫ p) (by rw [reassoc_of% e]; exact Category.assoc _ _ _)
  have hsI : strHom k g.image = g.imageι ≫ p := strHom_eq (fun _ => rfl)
  have : IsProper (strHom k (X := g.image)) := by rw [hsI]; infer_instance
  have hproj : IsProjOver (strHom k (X := g.image)) := ProperCurve.isProjOver_of_isProper _ hdZ
  have : IsProper (g.imageι ≫ strHom k W) := by rw [hsW]; infer_instance
  refine ⟨⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩,
    isCompleteCurve_range g.imageι hdZ, φ.residueDegree (genericPoint _), fun L hL => ?_⟩
  have hN := LB.isLB_pull hL g.imageι
  have h₁ := ProjFin.interNumOn_eq_residueDegree_mul k g.image _ φ hproj hdZ hgen
    (L.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := k) (L := ![L.pull g.imageι]) hf (isLB_vecOne hN)
  have h₃ : topSelfIntersection k (L.pull g) 1 = interNum k (structureModule _)
      fun i => (![L.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => LB.isLB_pull hL g)
      (fun i => by fin_cases i; exact LB.isLB_pull hN φ) fun i => ?_
    fin_cases i
    change cls (L.pull g) _ = cls ((L.pull g.imageι).pull φ) _
    simpa only [e] using (hcomp hL g.imageι φ).symm
  have h₄ : interNumRed k ⟨Set.range g.imageι, g.imageι.isClosedEmbedding.isClosed_range⟩ ![L] =
      interNum k (structureModule g.image) ![L.pull g.imageι] :=
    (InterModel.interNumRed_eq_interNumOn k g.imageι _ rfl _).trans
      ((interNumOn_eq_interNum_pull (appTop_algebraΓOfHom g.imageι p rfl) (isLB_vecOne hL)).trans
        (congrArg _ (funext fun j => by fin_cases j; rfl)))
  rw [hdeg L hL, h₃, ← h₂, h₁, h₄]

end GlobalTheory.NumPull

namespace GlobalTheory.NumPull

theorem interNumRed_pull_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  intro M W _ _ p f hp _
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (f ≫ p)
  intro L L' hL hL' a b H C hC
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  rcases interNumRed_pull_curve p f C hC with h | ⟨C', hC', d, hd⟩
  · rw [h L hL, h L' hL', mul_zero, mul_zero]
  · rw [hd L hL, hd L' hL']
    linear_combination (d : ℤ) * H C' hC'

end GlobalTheory.NumPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FibreCmp

theorem isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem valAt'_comp_app {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE _ _ _ _ _ _ h
  · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isDerivAt0_of_isDiff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {Y : Scheme.{0}}
    (φ : A.left ⟶ Y) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    (he : ∀ z, (u.ex z).left ≫ φ = e z) (hv : IsTangent v) (hd : u.IsDiff w v) :
    IsDerivAt0 e w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := by
  obtain rfl : (fun z => (show Sp ℂ ⟶ _ from (u.ex z).left) ≫ φ) = e := funext he
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc]
    refine congrArg (· ≫ φ) (hv.trans ?_)
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  · have := hd (φ ⁻¹ᵁ U) hU ((φ.app U).hom f)
    simp only [valAt'_comp_app] at this
    rw [← this, Scheme.Hom.comp_appLE]
    rfl


open FibreUnif in
theorem exists_equiv_of_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (FU.Di i) ty Pe) (P : Out.PolAV (Sp ℂ))
    (φ : P.A.left ⟶ Xo.univ.t.G.left) (hp : IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ)
    (hL : LBIso P.L (Xo.univ.t.PP.L.pull φ)) {g : ℕ} (u : HolUnif P.A P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hAH : u.IsAH Hm κ) :
    ∃ F : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧
      (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
      (∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b) ∧
      ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → (u.IsDiff (F w) v ↔
        IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)) := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨Ef, hEf, -, -, ht₁, ht₂, hweil⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all P g u Hm κ hAH
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have holG : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (FU.ex i Pe z).left) := by
    have h := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    exact isHolTo_slice h 0
  have hol : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L g g₀ u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z))
    (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range := fun z => by
    rw [← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Pe.range : Set (Fin g₀ → ℂ)).Countable := by
    have := hP.2.2.1
    exact (countable_of_Lindelof_of_discrete : Countable Pe.range)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := FU.ex_onto i Pe hP x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left := fun z => by rw [hF, hΦ]
  let F' := LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩
  have fwd : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → u.IsDiff (F' w) v →
      IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := fun w v hv hd => by
    have h1 := isDerivAt0_of_isDiff u φ (e := fun z => (FU.ex i Pe (F'.symm.toLinearMap z)).left)
      (fun z => by rw [← hex]; exact congrArg (fun t => (u.ex t).left ≫ φ) (F'.apply_symm_apply z).symm) hv hd
    have h2 := (isDerivAt0_comp_linear _ holG F'.symm.toLinearMap _ _).1 h1
    rwa [LinearEquiv.coe_coe, F'.symm_apply_apply] at h2
  refine ⟨F', hex, hΛ, fun a b => ?_, fun w v hv => ⟨fwd w v hv, fun hd => ?_⟩⟩
  · let a' : u.Λ := ⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩
    let b' : u.Λ := ⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩
    refine (hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))
    have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h₂ := FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    have h₃ := weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _)
      (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _
      (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
    exact congrArg Units.val (unitOn_injective h₃)
  · obtain ⟨w', hw', -⟩ := ht₁ v hv
    obtain ⟨w₁, rfl⟩ := F'.surjective w'
    have h1 := fwd w₁ v hv hw'
    let a : epsPt (FU.u i Pe) ⟶ Xo.univ.t.G := Over.homMk ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)
      (by rw [Category.assoc, hp.1.w, ← Category.assoc]; exact congrArg (· ≫ FU.u i Pe) (Over.w v))
    have e : w = w₁ := ((FU.ex_diff i Pe hP).2 a hd.1).unique hd h1
    rwa [e]

theorem exists_equiv_of_isAH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ' : KA l →+* ℂ) (g₀ : ℕ) (ty : Fin g₀ → (E →+* ℂ)) (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (s' : Sp ℂ ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s') (m : ObjMap o Xo.univ y₀) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ), IsPeriod (Fu.Di i) ty P → y₀ = Fu.u i P → u.IsAH Hm κ → ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) ∧ (∀ z, h z ∈ u.Λ ↔ z ∈ P.range) ∧ (∀ a b, (herm Hm (h (P a)) (h (P b))).im = (Fu.Di i).EF a b) ∧ ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔ IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)) := by
  intro E _ _ _ H D l Xo σ' g₀ ty Fu i P y₀ s' o m g u Hm κ hP hy hAH
  subst hy
  obtain ⟨w, hw, -⟩ := m.lin
  exact exists_equiv_of_polAV Fu i hP (GlobalTheory.Obj.toPolAV o) m.toSABMap.φ m.cart ⟨w, hw⟩ u hAH

end GlobalTheory.DetLine.FibreCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingLocalizationPowerSeriesUn
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowerSeriesUniformiser

theorem span_C_eq_ker {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) :
    Ideal.span {(PowerSeries.C ϖ : PowerSeries A)} =
      RingHom.ker (PowerSeries.map (IsLocalRing.residue A)) := by
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    ext n
    simp [PowerSeries.coeff_C_mul, hm, Ideal.mem_span_singleton']
  · intro hf
    have h : ∀ n, ∃ b : A, PowerSeries.coeff n f = ϖ * b := fun n => by
      have : IsLocalRing.residue A (PowerSeries.coeff n f) = 0 := by
        have := congrArg (PowerSeries.coeff n) hf
        simpa using this
      rw [IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at this
      exact this
    choose b hb using h
    refine ⟨PowerSeries.mk b, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hb]

theorem span_C_isPrime {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A}
    (hϖ : Irreducible ϖ) : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime := by
  rw [span_C_eq_ker hϖ]
  exact RingHom.ker_isPrime _

theorem isDiscreteValuationRing_atPrime_span {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (h0 : π ≠ 0) [(Ideal.span {π}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {π})) := by
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π})) =
      Ideal.span {algebraMap R _ π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {π}))) :=
    IsLocalization.injective _ (Ideal.span {π}).primeCompl_le_nonZeroDivisors
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {π})) := fun hf => by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot] at hf
    exact h0 (hinj (hf.trans (map_zero _).symm))
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {π}))).IsPrincipal := ⟨_, hm⟩
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).2 hp

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ →
    ∃ _ : (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)})) := by
  intro A _ _ _ ϖ hϖ
  haveI := span_C_isPrime hϖ
  refine ⟨this, isDiscreteValuationRing_atPrime_span ?_⟩
  intro h
  exact hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))

end GlobalTheory.PowerSeriesUniformiser
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmoothProjectiveModificationOfNonempty
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem isIntegral_of_nonempty_modif : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  intro F _ Y _ p U d M hU
  have hUi : IsIrreducible (U : Set Y) :=
    ⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have := M.iso
  let g : (U : Scheme) ⟶ M.X := inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι
  have hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have hs : Function.Surjective (inv (M.σ ∣_ U)).base := (inv (M.σ ∣_ U)).surjective
    simp only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    rw [← hrange, ← Set.image_univ]
    have : IrreducibleSpace (U : Scheme) := Subtype.irreducibleSpace hUi
    exact (IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn
  have hcl : IsIrreducible (Set.univ : Set M.X) := by
    rw [← M.dense.closure_eq]; exact hopn.closure
  have : IrreducibleSpace M.X := irreducibleSpace_def _ |>.mpr hcl
  have : Smooth M.str := SmoothOfRelativeDimension.smooth d _
  exact isIntegral_of_smooth_field M.str

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem isProjOver_locallyOfFiniteType : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → LocallyOfFiniteType s := by
  rintro R _ X s ⟨N, i, hi, rfl⟩
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFactorDepthEqSumFactorDepthsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  first | exact @GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP | exact GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP | (intros; apply GlobalTheory.IsoFactorDepth.nuH_vp_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.WeilThetaRat.thetaSum_om_rat | exact GlobalTheory.WeilThetaRat.thetaSum_om_rat | (intros; apply GlobalTheory.WeilThetaRat.thetaSum_om_rat <;> assumption)
end

