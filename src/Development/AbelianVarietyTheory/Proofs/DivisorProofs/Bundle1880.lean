module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.ImportsAlt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRing
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham


set_option maxHeartbeats 1000000 in
theorem IsKSValue.exists_of_isAbelianScheme_ring (P : AbelianDeRham) {K : Type} [CommRing K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme_ring : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [CommRing K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme_ring P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham


set_option maxHeartbeats 1000000 in
theorem IsKSValue.exists_of_isAbelianScheme (P : AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  have a₀ : Semi.IsAbelianScheme A := by
    have := hA.comm
    have hc : IsCommMonObj A := by
      open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 K A g a₀ g₀).1
  letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
  obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA hg K A i h
  obtain ⟨-, ⟨N, hN⟩, -⟩ := P.2.1 (DualNumber K) A' g hA hg
  obtain ⟨-, hproj, -⟩ := P.1.prim hA hg
  have su : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := P.2.2.2.1 _ A' g hA hg _ (epsDP K) (isDPNilpotent_squareZero _) K _ su rfl A i h
  have rB := P.2.2.2.1.crysToDR_bijective hA hg (κ := epsDP K) (isDPNilpotent_squareZero _) su rfl h
  let φL : primDR A' →ₗ[DualNumber K] K :=
    { toFun := fun c => f ((bcMor h).pull c)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  obtain ⟨u, hu⟩ := Module.projective_lifting_property (Algebra.linearMap (DualNumber K) K) φL
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)
  let d' : HdR A' := u ∘ₗ N.projection (PrimitiveSubmodule A') hN.symm
  have hd' : d' ∈ Fil A' := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro x hx
    change u (N.projection (PrimitiveSubmodule A') hN.symm x) = 0
    rw [Submodule.projection_apply_of_mem_right hN.symm hx, map_zero]
  have fd' : ∀ x, (d' x).fst = f ((bcMor h).pull x) := fun x => by
    have e1 : ∀ y, (u y).fst = f ((bcMor h).pull y) := fun y => LinearMap.congr_fun hu y
    have e2 := Submodule.projection_add_projection_eq_self hN.symm x
    have e3 : f ((bcMor h).pull ((PrimitiveSubmodule A').projection N hN.symm.symm x)) = 0 := by
      rw [Fil, hF] at hf
      exact (Submodule.mem_dualAnnihilator _).1 hf _
        (Submodule.subset_span ⟨_, Submodule.projection_apply_mem _ _, rfl⟩)
    change (u _).fst = _
    rw [e1, ← add_zero (f ((bcMor h).pull _)), ← e3, ← map_add (f := _), ← map_add (f := _), e2]
  obtain ⟨d, hd⟩ := rB.2 d'
  let k : HdR A :=
    { toFun := fun c => (d ((constMor A).pull c)).snd
      map_add' := fun x y => by simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun r c => by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul,
          TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]
        simp }
  obtain ⟨v, hv, -⟩ := hL.1 k
  refine ⟨v, k, ⟨d, by rw [liftFil, Submodule.mem_comap, hd]; exact hd', fun c => ?_⟩, hv⟩
  obtain ⟨x, hx⟩ := rA.2 ((constMor A).pull c)
  have red : (bcMor h).pull x = c := by
    rw [← GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (bcMor h) (fun _ => rfl) (by simp) x, hx,
      redMor_constMor]
  apply TrivSqZeroExt.ext
  · have e := fd' x
    rw [← hd, crysToDR_apply, hx, red] at e
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact e
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    rfl

theorem ksRegular_of_isAbelianScheme : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
section
open GlobalTheory.ShFam.Hor.LogCh

set_option autoImplicit false

open Topology

namespace GlobalTheory.LatReal

theorem isRealBasis_of_isLatFam : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ →
    LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) →
    LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  intro n g r B K b₀ lam hF hb hspan hli hK
  have hmemL : ∀ w, w ∈ Submodule.span ℤ (Set.range lam) ↔ w ∈ K b₀ := by
    intro w
    rw [Submodule.mem_span_range_iff_exists_fun, hK]
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.symm⟩
  have hsub : K b₀ ⊆ Submodule.span ℝ (Set.range lam) := by
    intro w hw
    obtain ⟨k, rfl⟩ := (hK w).1 hw
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have htop : Submodule.span ℝ (Set.range lam) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 hsub
  refine ⟨?_, htop⟩
  have h0 : (0 : Fin g → ℂ) ∈ K b₀ := (hK 0).2 ⟨0, by simp⟩
  obtain ⟨ζ, hζ0, -, hev⟩ := hF.2.2.2 b₀ hb 0 h0
  have ht : Filter.Tendsto (fun w : Fin g → ℂ => (b₀, w)) (𝓝 0) (𝓝 (b₀, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' 0 (b₀, 0) rfl
  have hev' : ∀ᶠ w in 𝓝 (0 : Fin g → ℂ), (w ∈ K b₀ ↔ w = 0) := by
    filter_upwards [ht.eventually hev] with w hw
    simpa [hζ0] using hw
  obtain ⟨U, hU, hUo, hU0⟩ := mem_nhds_iff.1 hev'
  set L := Submodule.span ℤ (Set.range lam) with hLdef
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [isOpen_induced_iff]
    refine ⟨U, hUo, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact Subtype.ext ((hU hx).1 ((hmemL x).1 x.2))
    · rintro rfl
      exact hU0
  have hLset : (L : Set (Fin g → ℂ)) = K b₀ := by
    ext w
    exact hmemL w
  haveI : IsZLattice ℝ L := ⟨by rw [hLset, hspan]⟩
  have hrank := ZLattice.rank ℝ L
  have hcard : Module.finrank ℤ L = r := by
    rw [Module.finrank_eq_card_basis (Module.Basis.span hli)]
    simp
  apply linearIndependent_of_top_le_span_of_card_eq_finrank htop.ge
  rw [Fintype.card_fin]
  omega

end GlobalTheory.LatReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum.SizeTZ

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem nCol_le (Dw : Datum H) :
    nCol Dw ≤ (2 * (Dw.p + Dw.q) + 8) * (Module.finrank ℚ E * (Dw.p + Dw.q)) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := GlobalTheory.FactorDepth.rk_le f
    have h' : Dw.mult f.1 ≤ Dw.p + Dw.q := by
      rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := card_Lt1_le_finrank_mul
  have h3 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q)) h2
  have h4 := Nat.mul_div_le (∑ f : Lt1 Dw, 2 * GlobalTheory.FactorDepth.rk f) 8
  unfold nCol
  nlinarith

end Free

variable {D : D7}

theorem two_le_f (D : D7) : 2 ≤ D.R.f := by
  have : 0 < D.R.ord := D.R.ord_pos
  show 2 ≤ 2 * D.R.ord
  omega

theorem six_le_r (D : D7) : 6 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  unfold Ranks.r; omega

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_zBase (L : SizeData₂ D) : 1 ≤ zBase L := by
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by have := six_le_r D; omega : 1 ≤ D.R.r)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr) (one_le_scL L)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem pow_le_PP (T : ParamsT D L P) : zBase L ^ 12 ≤ T.PP := by
  have hZ := one_le_zBase L
  have h1 : zBase L ^ 12 ≤ zBase L ^ T.eP := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by exact_mod_cast T.eP_ge)
  rw [T.PP_eq]
  exact h1.trans (le_mul_of_one_le_left (by positivity) T.one_le_CP)

theorem ceil_le_TO (T : ParamsT D L P) :
    ⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ ≤ T.TO := by
  refine Nat.ceil_le.2 (le_trans ?_ T.TO_ge)
  have hPP : 1 ≤ T.PP := (one_le_pow₀ (one_le_zBase L)).trans (pow_le_PP T)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by have := two_le_f D; omega : 1 ≤ D.R.f)
  have hD : (1 : ℝ) ≤ T.Dp := by
    have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos (by have := six_le_r D; omega)
    have h2 : 0 < T.Dp := by rw [T.Dp_eq]; exact Nat.mul_pos (by have := two_le_f D; omega) h1
    exact_mod_cast h2
  have hx : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  have hd := L.thickDensity_pos
  refine div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_of_le_one_right hm.le L.thickDensity_le_one)
  have e : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp =
      T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) * (T.PP ^ 2 * T.Dp * D.R.f * L.sc.x ^ T.Cp) := by ring
  rw [e]
  exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hPP) hD) hf) hx)

theorem ceil_mul_le_b (T : ParamsT D L P) :
    (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) * zBase L ^ 12 ≤ L.sc.b := by
  have hb : 1 ≤ L.sc.b := Real.one_le_exp (zero_le_one.trans (one_le_scL L))
  have hZ := one_le_zBase L
  have h1 : (⌈T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)⌉₊ : ℝ) ≤ T.TO := by exact_mod_cast ceil_le_TO T
  refine (mul_le_mul h1 (pow_le_PP T) (by positivity) (by positivity)).trans (T.TO_PP'.trans ?_)
  exact (Real.rpow_le_rpow_of_exponent_le hb (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans (Real.rpow_one _).le

theorem lrd_le (P : ParameterChoice' D L) : lrd D.host.E ≤ 3 * L.sc.L := by
  have h := log_rdE_le_scL P
  have e : lrd D.host.E = Real.log D.host.rdE := by
    rw [lrd, rootDiscr_def, Formalism.BasicNotions.Host.rdE, one_div, Int.cast_abs]
  have := one_le_scL L
  rw [e]; linarith

theorem nCol_le_of_pins {T : Par D} (h : T.Pins) {j : ℕ} (hj : InR D j) :
    (nCol (T.Dw j) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have h1 := nCol_le (T.Dw j)
  rw [hfr, (GlobalTheory.SlopeRec.sig_eq h hj).2.2] at h1
  have hf := two_le_f D
  have hr := six_le_r D
  have h2 : nCol (T.Dw j) ≤ 20 * D.R.f * D.R.r ^ 2 := by
    refine h1.trans ?_
    generalize D.R.f = f at *
    generalize D.R.r = r at *
    have a1 : f * r * 6 ≤ f * r * r := Nat.mul_le_mul_left _ hr
    have a2 : 2 * 6 ≤ f * r := Nat.mul_le_mul hf hr
    nlinarith
  exact_mod_cast h2

theorem lenT_mul_le_b {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
    (T : ParamsT D L P) :
    (lenT p i T.PP : ℝ) * zBase L ^ 12 ≤ L.sc.b ∧ (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpin : p.T.Q.Pins := p.fw.laws.pins
  have hD : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := by
    rw [T.Dp_eq]
    refine (GlobalTheory.SlopeRec.dimFlag_eq hpin hj).trans ?_
    simp only [placeRankTwoOne.dimY, Nat.choose_two_right]
  refine ⟨?_, nCol_le_of_pins hpin hj⟩
  rw [lenT, hD]
  exact ceil_mul_le_b T

end GlobalTheory.RefSum.SizeTZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterFiniteOrderDefiniteForms
section
set_option autoImplicit false

noncomputable section

open Formalism.L2.DIV NumberField
open scoped TensorProduct

namespace GlobalTheory.BaseCmp

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isOfFinOrder_hom_of_finite {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : IsOfFinOrder (f g) :=
  f.isOfFinOrder (isOfFinOrder_of_finite g)

theorem levFn_isOfFinOrder (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E ℂ n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : IsOfFinOrder (levFn β L x) := by
  classical
  have hPP : ∀ PP : Pl E, Finite (kP PP) := fun PP =>
    Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hU : ∀ PP : Pl E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  have hG : ∀ (PP : Pl E) (r : ℕ), Finite (GL (Fin r) (kP PP)) := fun PP r => Finite.of_injective _ Units.val_injective
  have hG0 : Finite (G0 L.Pg L.r) := Pi.finite
  rw [← CommGroup.mem_torsion]
  unfold levFn
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · rw [CommGroup.mem_torsion]
    unfold ext1
    split_ifs with h
    · exact isOfFinOrder_hom_of_finite L.P.chi _
    · exact IsOfFinOrder.one
  · refine Subgroup.prod_mem _ fun PP _ => Subgroup.prod_mem _ fun c _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
  · refine Subgroup.prod_mem _ fun PP _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
end

set_option maxHeartbeats 1600000 in
theorem levLamRoot : LevLamRoot := by
  intro D S T B t k
  have h : IsOfFinOrder (B.levLam t k) := by
    rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
    exact levFn_isOfFinOrder _ _ _
  obtain ⟨m, hm, hmo⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  exact ⟨m, hm.ne', by rw [← Units.val_pow_eq_pow_val, hmo, Units.val_one]⟩

end GlobalTheory.BaseCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
section
namespace GlobalTheory

theorem semiAbelianHomExtension_holds : GlobalTheory.Published.SemiAbelianHomExtension :=
  GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension

end GlobalTheory
end

