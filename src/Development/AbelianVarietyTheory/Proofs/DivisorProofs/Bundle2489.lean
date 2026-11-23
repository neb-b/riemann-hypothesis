module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.CubicForms.ImportsBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

theorem abelianPart_iso_of_twoUnif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  intro R _ _ _ hBase D A G _ _ hG U g _ a _ _ A₂ D₂ U₂ _
  have hR : AdmBase R (maximalIdeal R) := hBase.1
  have hN : IsNoetherianRing R := hR.1
  have hC : IsAdicComplete (maximalIdeal R) R := hR.2.2.2
  have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  obtain ⟨b₁, hb₁, h₁⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D₂ D A₂ A G G
    U₂.toUnifPre U.toUnifPre (𝟙 G) inferInstance
  obtain ⟨b₂, hb₂, h₂⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D D₂ A A₂ G G
    U.toUnifPre U₂.toUnifPre (𝟙 G) inferInstance

  have q₁ : ∀ e, (U.gt e).q = (U₂.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₁ := by
    intro e
    have := h₁ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have q₂ : ∀ e, (U₂.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₂ := by
    intro e
    have := h₂ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have epi : ∀ {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
      (V : UnifPre (maximalIdeal R) D' A' G) (e : ℕ), Epi (V.gt e).q := by
    intro D' A' V e
    have := (V.gt e).q_flat
    have := (V.gt e).q_surj
    have : Epi (V.gt e).q.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have k₁ : b₂ ≫ b₁ = 𝟙 _ := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U.toUnifPre n
    rw [← cancel_epi (U.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₂, ← q₁]
  have k₂ : b₁ ≫ b₂ = 𝟙 _ := by
    have := D₂.toPre.P.isAb.smooth
    have := D₂.toPre.P.isAb.geomConnected
    have := D₂.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U₂.toUnifPre n
    rw [← cancel_epi (U₂.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₁, ← q₂]
  refine ⟨⟨b₁, b₂, k₂, k₁⟩, hb₁, fun e => ?_⟩
  show (U₂.gt e).q.left ≫ (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left =
    (U.gt e).q.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left
  have m : ((Over.pullback (thick R (maximalIdeal R) e)).map b₁).left ≫
      (fstG (maximalIdeal R) e D.toPre.P.A).left = (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left :=
    pullback.lift_fst _ _ _
  rw [← m, q₁ e, Over.comp_left, Category.assoc]

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.WedgeSq

theorem exists_fin_sum_tmul {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (t : V ⊗[K] W) : ∃ (n : ℕ) (x : Fin n → V) (y : Fin n → W), t = ∑ i, x i ⊗ₜ[K] y i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | add s t hs ht =>
    obtain ⟨n, x, y, rfl⟩ := hs
    obtain ⟨m, x', y', rfl⟩ := ht
    exact ⟨n + m, Fin.append x x', Fin.append y y', by simp [Fin.sum_univ_add]⟩

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

variable {K : Type} [Field K]

theorem overPullbackStructureSheaf_cohomology_cup {Y A : Over (Sp K)} (f : Y ⟶ A) (a b : HO1 A.hom) :
    structureSheafH2Pullback f (cup (OAff A.hom) a b) = cup (OAff Y.hom) (pO1 f a) (pO1 f b) :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).2.1 K K A.left Y.left A.hom Y.hom (RingHom.id K) f.left (ovw f)).1 a b

variable (A : Over (Sp K)) [GrpObj A]

abbrev mixed : HO1 A.hom →ₗ[K] HO1 A.hom →ₗ[K] HO2 (A ⊗ A).hom :=
  (cup (OAff (A ⊗ A).hom)).compl₁₂ (pO1 (fst A A)) (pO1 (snd A A))

theorem defect_eq (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom) :
    structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t) - structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      - structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      = TensorProduct.lift (mixed A) (t - TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul, map_sub, overPullbackStructureSheaf_cohomology_cup, hp a, hp b, map_add (f := _),
      LinearMap.add_apply, LinearMap.compl₁₂_apply]
    rw [_root_.GlobalTheory.AbCoh.cup_anticomm K _ (OAff (A ⊗ A).hom) (pO1 (snd A A) a) (pO1 (fst A A) b)]
    abel
  | add s t hs ht =>
    have e : s + t - TensorProduct.comm K _ _ (s + t)
        = (s - TensorProduct.comm K _ _ s) + (t - TensorProduct.comm K _ _ t) := by
      rw [map_add (f := _)]; abel
    rw [e, map_add (TensorProduct.lift (mixed A)), ← hs, ← ht]
    simp only [map_add (f := _)]
    abel

theorem mixed_injective [IsSeparated A.hom] [QuasiCompact A.hom] (u : HO1 A.hom ⊗[K] HO1 A.hom)
    (hu : TensorProduct.lift (mixed A) u = 0) : u = 0 := by
  obtain ⟨n, x, y, rfl⟩ := exists_fin_sum_tmul u
  refine _root_.GlobalTheory.Kunneth.cup_tmul_injective K A A inferInstance inferInstance inferInstance inferInstance n x y ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using hu

theorem symm_of_prim [IsSeparated A.hom] [QuasiCompact A.hom] (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom)
    (ht : structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t)
      = structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
        + structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)) :
    TensorProduct.comm K _ _ t = t := by
  have h0 := defect_eq A hp t
  rw [ht, add_sub_cancel_left, sub_self] at h0
  exact (sub_eq_zero.1 (mixed_injective A _ h0.symm)).symm

end GlobalTheory.AbCoh.WedgeSq


open GlobalTheory.AbCoh.WedgeSq in
theorem GlobalTheory.AbCoh.wedgeO_noPrimO2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  intro K _ _ A _ g hab hsm
  haveI : IsProper A.hom := hab.proper
  haveI hsep : IsSeparated A.hom := inferInstance
  haveI hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨-, hprim, -⟩ := _root_.GlobalTheory.AbCoh.Axes.main K A g hab hsm
  obtain ⟨n, D, hD, hcov⟩ := GlobalTheory.AbCoh.WedgeSq.exists_fin_affine_cover A.hom
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := _root_.GlobalTheory.AbCoh.hO_equiv_cech K A.left A.hom (Fin n) D hsep hD hcov
  obtain ⟨hfin, h1, h2⟩ := _root_.GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two K A g hab hsm (Fin n) D hD hcov
  haveI := hfin 1
  haveI := hfin 2
  haveI : Module.Finite K (HO1 A.hom) := Module.Finite.equiv e1.symm
  haveI : Module.Finite K (HO2 A.hom) := Module.Finite.equiv e2.symm
  have hdim : Module.finrank K (HO2 A.hom) ≤ (Module.finrank K (HO1 A.hom)).choose 2 := by
    rw [e2.finrank_eq, e1.finrank_eq, h1]; exact h2
  have hrel : ∀ t : HO1 A.hom ⊗[K] HO1 A.hom, TensorProduct.lift (cup (OAff A.hom)) t = 0 →
      TensorProduct.comm K _ _ t = t := fun t ht ↦ symm_of_prim A hprim t (by simp [ht])
  obtain ⟨hw, hsurj, hsym⟩ := GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations K (HO1 A.hom) (HO2 A.hom) (cup (OAff A.hom)) hdim hrel
  refine ⟨hw, fun z hz ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hsurj z
  exact hsym t (symm_of_prim A hprim t hz)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPoint
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem frame_eventually_near : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (y : CxPts X.str σ), ∀ A ∈ E.S (under y), ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  intro F _ σ X ι _ m k E y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := E.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    (hP τ).2.2.2⟩

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFullFlagFrameChangeDiagonalUnits
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.FlagChange

theorem diag_unitAt_and_mul : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  intro F _ X ι m E B hB z A A' hA hA' x
  obtain ⟨τ, i⟩ := x
  have hP : Par m ((ratOf X).O z).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have hl : ∀ (C : Mat m X.Fn) (O : Subring X.Fn), Par m O C → (C τ).BlockTriangular OrderDual.toDual := by
    intro C O hC a b hab
    exact (hC τ).2.2.2 a b a.2 hab
  refine ⟨?_, ?_⟩
  · set P := A' * A⁻¹ with hPdef
    have hdet : (P τ).det = P τ i i * ∏ j ∈ Finset.univ.erase i, P τ j j := by
      rw [Matrix.det_of_lowerTriangular _ (hl P _ hP),
        Finset.mul_prod_erase Finset.univ (fun j => P τ j j) (Finset.mem_univ i)]
    have hne : (P τ).det ≠ 0 := hP.det_ne τ
    rw [hdet] at hne
    have hii : P τ i i ≠ 0 := left_ne_zero_of_mul hne
    have hR : ∏ j ∈ Finset.univ.erase i, P τ j j ≠ 0 := right_ne_zero_of_mul hne
    have hmem : ∀ a b, P τ a b ∈ (ratOf X).O z := fun a b => (hP τ).1 a b
    have hinv : (P τ i i)⁻¹ ∈ (ratOf X).O z := by
      have e : (P τ i i)⁻¹ = (P τ).det⁻¹ * ∏ j ∈ Finset.univ.erase i, P τ j j := by
        rw [hdet, _root_.mul_inv, mul_assoc, inv_mul_cancel₀ hR, mul_one]
      rw [e]
      refine ((ratOf X).O z).mul_mem (hP τ).2.2.1 (((ratOf X).O z).prod_mem fun j _ => hmem j j)
    exact (unitAt_iff hii).2 ⟨mem_O_ratOf.1 (hmem i i), mem_O_ratOf.1 hinv⟩
  · have hA'g : A' ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA'
    have hQ : Par m ((ratOf X).O (genericPoint X.X)).toSubring (B * A'⁻¹) := (Fr.mem_iff hA'g).1 hB
    have e : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
      rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
    rw [e]
    show ((B * A'⁻¹) τ * (A' * A⁻¹) τ) i i = _
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun l _ hl' => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [(hP τ).2.2.2 l i l.2 h, mul_zero]
    · rw [(hQ τ).2.2.2 i l i.2 h, zero_mul]

end GlobalTheory.FlagChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumFractionFieldEqMulIntegralCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.Poinc.AdicTerm

theorem eq_zero_of_mem_pow_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] (N : Submodule V E) (hN : N.FG) (w : E)
    (h : ∀ n : ℕ, w ∈ maximalIdeal V ^ n • N) : w = 0 := by
  have hw : w ∈ N := Submodule.smul_le_right (h 0)
  haveI : Module.Finite V N := Module.Finite.iff_fg.mpr hN
  have hb := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have hm : (⟨w, hw⟩ : N) ∈ (⨅ n : ℕ, maximalIdeal V ^ n • ⊤ : Submodule V N) := by
    rw [Submodule.mem_iInf]
    intro n
    exact (Submodule.mem_smul_top_iff _ N _).mpr (h n)
  rw [hb, Submodule.mem_bot] at hm
  exact congrArg Subtype.val hm

theorem sumI_smul {V E : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    [AddCommGroup E] [Module V E] {Ix : Type} (i₀ : Ix) (x : Ix → E) (y : Ix → V) (k v : E)
    (hx : ∀ i, x i = y i • k) (hy : ∀ i, i ≠ i₀ → y i ∈ maximalIdeal V)
    (hs : SumI (maximalIdeal V) x v) :
    ∃ S : V, v = S • k ∧ S - y i₀ ∈ maximalIdeal V := by
  classical
  obtain ⟨N, hN, -, -, hS⟩ := hs
  let P : Submodule V E := Submodule.map (LinearMap.toSpanSingleton V E k) (maximalIdeal V)
  have key : P.mkQ (v - y i₀ • k) = 0 := by
    refine eq_zero_of_mem_pow_smul (N.map P.mkQ) (hN.map _) _ fun n => ?_
    obtain ⟨S, hS⟩ := hS n
    have h1 := hS (insert i₀ S) (Finset.subset_insert _ _)
    have h2 : P.mkQ (v - ∑ i ∈ insert i₀ S, x i) ∈ maximalIdeal V ^ n • N.map P.mkQ := by
      rw [← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem h1
    have h3 : ∑ i ∈ (insert i₀ S).erase i₀, x i ∈ P := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact ⟨y i, hy i (Finset.ne_of_mem_erase hi), by simp [hx i]⟩
    have h4 : P.mkQ (∑ i ∈ (insert i₀ S).erase i₀, x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr h3
    have h5 : v - y i₀ • k =
        (v - ∑ i ∈ insert i₀ S, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i := by
      rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S), hx i₀]
      abel
    rw [h5, map_add (f := _), h4, add_zero]
    exact h2
  obtain ⟨a, ha, hak⟩ := (Submodule.Quotient.mk_eq_zero P).mp key
  refine ⟨y i₀ + a, ?_, by simpa using ha⟩
  have hak' : a • k = v - y i₀ • k := by simpa using hak
  rw [add_smul, hak']
  abel

theorem sumF_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Ix : Type) (i₀ : Ix) (x : Ix → FractionRing V) (y : Ix → V) (κ v : FractionRing V), (∀ i, x i = κ * algebraMap V (FractionRing V) (y i)) → (∀ i, i ≠ i₀ → y i ∈ maximalIdeal V) → SumF (maximalIdeal V) (FractionRing V) x v → ∃ S : V, v = κ * algebraMap V (FractionRing V) S ∧ S - y i₀ ∈ maximalIdeal V := by
  intro V _ _ _ _ Ix i₀ x y κ v hx hy hs
  have h := @sumI_smul V (FractionRing V) _ _ _ _
    (Module.compHom (FractionRing V) (algebraMap V (FractionRing V))) Ix i₀ x y κ v
    (fun i => (hx i).trans (mul_comm _ _)) hy hs
  obtain ⟨S, h1, h2⟩ := h
  exact ⟨S, h1.trans (mul_comm _ _), h2⟩

end GlobalTheory.Poinc.AdicTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  first | exact @GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | exact GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | (intros; apply GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineArithmeticCurveFinsumOrdLogEqLocalLengths
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.AffineCurveSum

theorem length_quot_eq {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (p : Submonoid B)
    [IsLocalization p S] (b : B) :
    Module.length S (S ⧸ Ideal.span {algebraMap B S b}) =
      Module.length (Localization p) (LocalizedModule p (B ⧸ Ideal.span {b})) := by
  let e := IsLocalization.algEquiv p (Localization p) S
  let : Algebra (Localization p) S := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower B (Localization p) S := .of_algebraMap_eq fun x => (e.commutes x).symm
  have h : Submodule.localized' S p (Algebra.linearMap B S) (Ideal.span {b}) =
      Ideal.span {algebraMap B S b} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  rw [← h, ← Module.length_eq_of_surjective (S := Localization p) (R := S) e.surjective]
  exact (((IsLocalizedModule.iso p (Submodule.toLocalizedQuotient' S p (Algebra.linearMap B S)
    (Ideal.span {b}))).extendScalarsOfIsLocalization p (Localization p)).length_eq).symm

theorem finsum_ord_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y] (q : Y ⟶ Sp k), IsArithVar q 0 → ∀ b : Γ(Y, ⊤), b ≠ 0 → ∑ᶠ z, (Scheme.ord (algebraMap Γ(Y, ⊤) Y.functionField b) z : ℝ) * Real.log (Nat.card (Y.residueField z)) = ∑ᶠ m : MaximalSpectrum Γ(Y, ⊤), ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl (Γ(Y, ⊤) ⧸ Ideal.span {b}))).toNat : ℝ) * Real.log (Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal)) := by
  intro k _ Y _ _ _ q hq b hb
  have hU := isAffineOpen_top Y
  have hd : ringKrullDim Γ(Y, ⊤) = 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have := (Scheme.homeoOfIso Y.isoSpec).isHomeomorph.topologicalKrullDim_eq
    exact this.symm.trans (hq.dim_eq.trans (by simp))
  have hc (z : Y) : (Order.coheight z : WithBot ℕ∞) =
      (hU.primeIdealOf ⟨z, trivial⟩).asIdeal.height := by
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨z, trivial⟩ : (⊤ : Y.Opens))
    have := hU.isLocalization_stalk ⟨z, trivial⟩
    exact (ringKrullDim_stalk_eq_coheight z).symm.trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height _ _)
  have hK : Ring.KrullDimLE 1 Γ(Y, ⊤) := Ring.krullDimLE_iff.2 (by simp [hd])
  have hmax (P : PrimeSpectrum Γ(Y, ⊤)) : P.asIdeal.height = 1 ↔ P.asIdeal.IsMaximal := by
    constructor
    · intro h
      refine Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hK _ (fun h0 => ?_) P.isPrime
      rw [h0, Ideal.height_bot] at h
      exact zero_ne_one h
    · intro h
      have h1 : P.asIdeal.height ≤ 1 := by
        have := (Ideal.height_le_ringKrullDim_of_ne_top h.ne_top).trans_eq hd
        exact_mod_cast this
      refine le_antisymm h1 (Order.one_le_iff_ne_zero.2 fun h0 => ?_)
      have h2 : P.asIdeal = ⊥ := by
        simpa [IsDomain.minimalPrimes_eq_singleton_bot] using Ideal.height_eq_zero_iff.1 h0
      have h3 : IsField Γ(Y, ⊤) := Ring.isField_iff_maximal_bot.2 (h2 ▸ h)
      rw [ringKrullDim_eq_zero_of_isField h3] at hd
      exact zero_ne_one hd
  let i : MaximalSpectrum Γ(Y, ⊤) → Y := fun m => hU.fromSpec m.toPrimeSpectrum
  have hi : Function.Injective i :=
    hU.fromSpec.isOpenEmbedding.injective.comp (MaximalSpectrum.toPrimeSpectrum_injective)
  have hp (m) : hU.primeIdealOf ⟨i m, trivial⟩ = m.toPrimeSpectrum :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [← finsum_mem_univ, ← finsum_mem_inter_support_eq' _ (Set.range i) Set.univ ?_, finsum_mem_range hi]
  · refine finsum_congr fun m => ?_
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨i m, trivial⟩ : (⊤ : Y.Opens))
    have hl : IsLocalization.AtPrime (Y.presheaf.stalk (i m)) m.asIdeal := by
      have := hU.isLocalization_stalk ⟨i m, trivial⟩
      convert this
      exact congrArg PrimeSpectrum.asIdeal (hp m).symm
    have h1 : Order.coheight (i m) = 1 := by
      have := hc (i m)
      rw [hp, (hmax _).2 m.isMaximal] at this
      exact_mod_cast this
    have hb' : algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ m.asIdeal.primeCompl_le_nonZeroDivisors)).2 hb
    have h2 := ord_algebraMap h1 hb'
    rw [length_quot_eq m.asIdeal.primeCompl] at h2
    have h3 : algebraMap Γ(Y, ⊤) Y.functionField b =
        algebraMap _ Y.functionField (algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (i m)) b) :=
      (algebraMap_germ (Opens.mem_top (i m)) b).symm
    have h4 : Nat.card (Y.residueField (i m)) = Nat.card (Γ(Y, ⊤) ⧸ m.asIdeal) :=
      Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m.asIdeal
        (Y.presheaf.stalk (i m))).symm.toEquiv
    rw [h3, h2, h4, Int.cast_natCast]
  · intro z hz
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have h1 : Order.coheight z = 1 := by
      by_contra h
      exact hz (by simp [Scheme.ord_eq_zero_of_coheight_neq_one h])
    have h2 := hc z
    rw [h1] at h2
    exact ⟨⟨_, (hmax (hU.primeIdealOf ⟨z, trivial⟩)).1 (by exact_mod_cast h2.symm)⟩,
      hU.fromSpec_primeIdealOf ⟨z, trivial⟩⟩

end GlobalTheory.AffineCurveSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
section
theorem GlobalTheory.CubeTop.cubeTheorem : GlobalTheory.Published.CubeTheorem := GlobalTheory.SpreadingModels.cubeTheorem_holds
end

