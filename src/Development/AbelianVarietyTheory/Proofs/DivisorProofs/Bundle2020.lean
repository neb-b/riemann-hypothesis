module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityRealHolds
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
  GlobalTheory.HoweD GlobalTheory.HoweR

namespace GlobalTheory

theorem howeDualityReal_holds : GlobalTheory.Published.HoweDualityReal := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 _ _ _ _ hWeil τ hcX hcW
  obtain ⟨P, Q, R, S, A, C, Φ, c, c', hfr, hinj, hrange, hact1, hact2⟩ :=
    _root_.GlobalTheory.HoweD.FockData.exists_fock_data F E σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 hWeil τ hcX hcW
  obtain ⟨-, hA, hC⟩ := hfr
  have hstab : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ w, Stab (actAt (V := fun w =>
      Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember F E σ n d X W M ψ om τ P Q R S Φ c' N hCM hN C hC hact2
  have hcoinv : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N →
      tensAny (fun w => coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ :=
    fun N hN => _root_.GlobalTheory.HoweD.tensAny_coinv_le_comap F E σ n d X W M ψ om τ P Q R S Φ c N hCM hN hrange A hA hact1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.T.howe_duality_characters_fock_tensor_product (InfinitePlace F) P Q R S (fun w => -c w)
  have hmap : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → (N.comap Φ).map Φ = N := by
    intro N hN
    rw [Submodule.map_comap_eq, hrange]
    exact inf_eq_right.mpr hN.1
  refine ⟨⟨L, fun m N hmono hN => hL m (fun i => (N i).comap Φ) ?_
    (fun k => ⟨hstab _ (hN k), hcoinv _ (hN k)⟩)⟩, ?_⟩
  · intro i j hij
    refine lt_of_le_of_ne (Submodule.comap_mono (hmono hij).le) ?_
    intro h
    have h' := congrArg (Submodule.map Φ) h
    rw [hmap _ (hN i), hmap _ (hN j)] at h'
    exact (hmono hij).ne h'
  · intro N N' hN hN' hne hne' heq
    refine hsum (N.comap Φ) (N'.comap Φ) (hstab _ hN) (hcoinv _ hN) ?_ (hstab _ hN') (hcoinv _ hN') ?_ ?_
    · intro h; apply hne; rw [← hmap _ hN, h, Submodule.map_top, hrange]
    · intro h; apply hne'; rw [← hmap _ hN', h, Submodule.map_top, hrange]
    · apply Submodule.map_injective_of_injective hinj
      rw [Submodule.map_sup, hmap _ hN, hmap _ hN', heq, Submodule.map_top, hrange]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.IdealSpread

theorem exists_of_map_eq_span {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Submonoid A)
    [IsLocalization M R] {J : Ideal A} (hJ : J.FG) (d : A)
    (h : J.map (algebraMap A R) = Ideal.span {algebraMap A R d}) :
    ∃ s ∈ M, s * d ∈ J ∧ ∀ j ∈ J, ∃ c, s * j = c * d := by

  obtain ⟨s₁, hs₁M, hs₁⟩ : ∃ s₁ ∈ M, s₁ * d ∈ J := by
    have hd : algebraMap A R d ∈ J.map (algebraMap A R) := h ▸ Ideal.subset_span rfl
    obtain ⟨⟨⟨a, ha⟩, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M R).1 hd
    simp only at hm
    rw [← map_mul] at hm
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) hm
    refine ⟨c * m, M.mul_mem c.2 m.2, ?_⟩
    have : (c : A) * (d * m) = c * a := hc
    rw [show (c : A) * m * d = c * (d * m) by ring, this]
    exact J.mul_mem_left _ ha

  have hone : ∀ g ∈ J, ∃ t ∈ M, ∃ c, t * g = c * d := by
    intro g hg
    have hg' : algebraMap A R g ∈ Ideal.span {algebraMap A R d} := h ▸ Ideal.mem_map_of_mem _ hg
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M r
    simp only at ham
    have : algebraMap A R (m * g) = algebraMap A R (a * d) := by
      rw [map_mul, map_mul, ← ham, ← hr]; ring
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) this
    exact ⟨c * m, M.mul_mem c.2 m.2, c * a, by linear_combination hc⟩
  have key : ∀ T : Finset A, (∀ g ∈ T, ∃ t ∈ M, ∃ c, t * g = c * d) → ∃ t ∈ M, ∀ g ∈ T, ∃ c, t * g = c * d := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, M.one_mem, by simp⟩
    | insert a S haS ih =>
      intro hT
      obtain ⟨t, htM, ht⟩ := ih (fun g hg => hT g (Finset.mem_insert_of_mem hg))
      obtain ⟨t', ht'M, c', hc'⟩ := hT a (Finset.mem_insert_self a S)
      refine ⟨t * t', M.mul_mem htM ht'M, fun g hg => ?_⟩
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact ⟨t * c', by rw [mul_assoc, hc', mul_assoc]⟩
      · obtain ⟨c, hc⟩ := ht g hg
        exact ⟨t' * c, by rw [mul_comm t t', mul_assoc, hc, mul_assoc]⟩
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨t, htM, ht⟩ := key S fun g hg => hone g (Ideal.subset_span hg)
  have hall : ∀ j ∈ Ideal.span (S : Set A), ∃ c, t * j = c * d := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem x hx => exact ht x hx
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [mul_add, ha, hb, add_mul]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      exact ⟨a * b, by rw [smul_eq_mul, mul_left_comm, hb, mul_assoc]⟩
  refine ⟨s₁ * t, M.mul_mem hs₁M htM, ?_, fun j hj => ?_⟩
  · rw [mul_comm s₁ t, mul_assoc]
    exact Ideal.mul_mem_left _ _ hs₁
  · obtain ⟨c, hc⟩ := hall j hj
    exact ⟨s₁ * c, by rw [mul_assoc, hc, mul_assoc]⟩

end GlobalTheory.IdealSpread

namespace GlobalTheory.IdealSpread

theorem ideal_eq_span_of_germ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1)
    (d : Γ(X, U.1)) (hN : IsNoetherianRing Γ(X, U.1))
    (h : (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d}) :
    ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s →
      I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x₀) := (X.presheaf.germ U.1 x₀ hx).hom.toAlgebra
  haveI hL : IsLocalization.AtPrime (X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x₀, hx⟩
  obtain ⟨s, hsM, hsd, hsJ⟩ := exists_of_map_eq_span (R := X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal.primeCompl (IsNoetherian.noetherian (I.ideal U)) d h
  refine ⟨s, (X.mem_basicOpen s x₀ hx).2 (IsLocalization.map_units (X.presheaf.stalk x₀) ⟨s, hsM⟩), fun t ht => ?_⟩
  have hu : IsUnit (resG X (X.basicOpen_le t) s) := by
    have h0 : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
    have h1 := h0.map (resG X ht)
    have e : resG X ht (resG X (X.basicOpen_le s) s) = resG X (X.basicOpen_le t) s := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    rwa [e] at h1
  rw [← I.map_ideal_basicOpen U t]
  change (I.ideal U).map (resG X (X.basicOpen_le t)) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    obtain ⟨c, hc⟩ := hsJ j hj
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨↑hu.unit⁻¹ * resG X (X.basicOpen_le t) c, ?_⟩
    have := congrArg (resG X (X.basicOpen_le t)) hc
    rw [map_mul, map_mul] at this
    rw [mul_assoc, ← this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm := Ideal.mem_map_of_mem (resG X (X.basicOpen_le t)) hsd
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Γ(X, X.basicOpen t)) hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

end GlobalTheory.IdealSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfFiniteOfRingKrullDimEqLocalDomain
section
open IsLocalRing

namespace GlobalTheory


open IsLocalRing in
theorem _root_.GlobalTheory.injective_of_finite_of_ringKrullDim_eq_of_local_domain :
    ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CommRing R]
      [IsLocalRing R] (ψ : B →+* R), ψ.Finite → ringKrullDim R = ringKrullDim B →
      Function.Injective ψ := by
  intro B R _ _ _ _ _ _ ψ hψ hdim
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hψ
  have hlt : ringKrullDim B < ⊤ := ringKrullDim_lt_top
  have hne : ringKrullDim B ≠ ⊥ := fun h =>
    (WithBot.bot_lt_coe (0 : ℕ∞)).not_ge (h ▸ (ringKrullDim_nonneg_of_nontrivial (R := B)))
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℕ∞) = m := by
    refine ENat.ne_top_iff_exists.mp ?_
    rintro rfl
    exact hlt.ne hm.symm
  exact _root_.GlobalTheory.CohenStructure.injective_of_ringKrullDim_eq (A := B) (S := R) hm.symm
    (hdim.trans hm.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_arcs_and_goodReduction_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  first | exact @GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good | exact GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good | (intros; apply GlobalTheory.ArcIntegralMixed.integral_of_arcs_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaSpecialise

namespace GlobalTheory.IntExpand

theorem gs_secPull {X Y Z : Scheme.{0}} {L : LB X} (s : L.Sec) (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z)
    (j : (L.pull φ).ι) (hz : r z ∈ (L.pull φ).U j) :
    gs r z ((L.pull φ).U j) ((GlobalTheory.Cartier.secPull s φ).f j) = gs (r ≫ φ) z (L.U (j PUnit.unit)) (s.f (j PUnit.unit)) := by
  unfold GlobalTheory.Cartier.secPull
  exact (gs_res r z _ hz _).trans (gs_pull r φ z _ (Set.mem_iInter.1 hz PUnit.unit) _)

theorem gs_secMaps {X Z : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} {a : A.Sec} {b : B.Sec}
    (h : GlobalTheory.Cartier.SecMaps w a b) (r : Z ⟶ X) (z : Z) (p : B.ι) (q : A.ι) (hp : r z ∈ B.U p)
    (hq : r z ∈ A.U q) :
    gs r z (B.U p) (b.f p) = ↑(gm r z ((B.div A).U (p, q)) (w.s (p, q))) * gs r z (A.U q) (a.f q) := by
  have e := congrArg (gs r z (B.U p ⊓ A.U q)) (h.on p q (W := B.U p ⊓ A.U q) inf_le_left inf_le_right)
  have hm : r z ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  rw [gs_mul r z _ hm] at e
  unfold resG at e
  rw [gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  rw [e, gs_unit r z _ (by exact hm)]
  rfl

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ (s : A.L.Sec) (σ : U.LG.L.Sec), GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull s U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) → ∀ (C : Type) [Field C] [Algebra (FractionRing V) C], ∃ (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (th : GlobalTheory.UT.SecA A C 1) (ϑ : Fam D.toPre C 1), (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) ∧ (∀ e, U.ExpandsAt e 1 σ₁ f) ∧ MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th ∧ U.ExpandsF C 1 w₀ th ϑ ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1 := by
  intro V _ _ _ _ hV D A G _ _ hG U w₀ hw s σ hS C _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let σ₁ : H0 U.LG.L 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.secOne U.LG.L σ
  have h1 : ∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i) := fun i h =>
    fn_ext fun x hx => (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ (𝟙 _) x _ hx).trans (by
      rw [Category.comp_id]; exact (gs_res (𝟙 _) x h hx (σ.f i)).symm)
  let sK : U.SecK 1 := genericSec U.toUnifPre 1 σ₁
  have hsK : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((1 : ℕ) : ℤ)) sK (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ₁ (pullback.fst G.hom (jK V)) 1 :=
    (secScal_one_iff U.LG.isLB).2 fun y J hJ => (sval_pullOver _ _ _ _ hJ).symm
  obtain ⟨E, hE, -⟩ := (U.expand 1 le_rfl).1 sK
  obtain ⟨f, hf, hEf⟩ := GlobalTheory.ExpInt.main V ϖ hϖ D A G U.toUnifPre 1 σ₁ sK hsK E hE
  obtain ⟨ϑ, hϑ⟩ := GlobalTheory.FamBaseChange.main GlobalTheory.globalFns_holds V _ D 1 E f hEf C
  let th : GlobalTheory.UT.SecA A C 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.pull1 A.L (snd (TFK (R := V) C) A.A).left s
  have hth : MBLow.IsPolAVSectionInverseImage A (TFK (R := V) C) s th := by
    refine fun i h => fn_ext fun x hx => ?_
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s (𝟙 _) x _ hx).trans (gs_appLE _ _ _ h (𝟙 _) x hx (s.f i)).symm
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := GlobalTheory.ThetaBaseChange.exists_unpull hw _ n₁ rfl
  have ht : PSec u (fun _ : Fin 1 => (snd (TFK (R := V) C) A.A).left) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))
      ((snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) th σ₁ := by
    intro Z r z p q hp hq
    obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun k => congrArg p (Subsingleton.elim k 0)⟩
    obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun k => congrArg q (Subsingleton.elim k 0)⟩
    have hp0 := hp 0
    have hq0 := hq 0
    have e1 := hu₁ Z (r ≫ (snd (TFK (R := V) C) A.A).left) z p0 q0 hp0 hq0
    have c2 : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left =
        r ≫ (snd (TFK (R := V) C) A.A).left := by
      rw [Category.assoc, n₁, Category.comp_id]
    have mB : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (U.LG.L.pull (pullback.fst G.hom (jK V))).U (fun _ => p0) := Set.mem_iInter.2 fun _ => hp0
    have mA : ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) z ∈
        (A.L.pull U.gen.hom.left).U (fun _ => q0) := Set.mem_iInter.2 fun _ => by
      show (((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ U.gen.hom.left) z ∈ A.L.U q0
      rw [c2]; exact hq0
    have e2 := GlobalTheory.IntExpand.gs_secMaps hS _ z (fun _ => p0) (fun _ => q0) mB mA
    rw [GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mB, GlobalTheory.IntExpand.gs_secPull _ _ _ _ _ mA, c2] at e2
    refine (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 U.LG.L (𝟙 _) σ
      (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) z (fun _ => p0)
      (Set.mem_iInter.2 fun _ => by exact hp0)).trans ?_
    refine Eq.trans ?_ (congrArg (fun t => _ * t)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.gs_pull1 A.L _ s r z (fun _ => q0) (Set.mem_iInter.2 fun _ => hq0)).symm)
    rw [Fin.prod_univ_one]
    dsimp only
    rw [Nat.cast_one, zpow_one, e1]
    have c1 : (r ≫ (snd (TFK (R := V) C) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V)) ≫ 𝟙 G.left =
        ((r ≫ (snd (TFK (R := V) C) A.A).left) ≫ U.gen.inv.left) ≫ pullback.fst G.hom (jK V) := by
      simp only [Category.assoc, Category.comp_id]
    rw [c1]
    exact e2
  refine ⟨σ₁, f, th, ϑ, h1, hf, hth, expandsF_of_integral U.toUnifPre C hu₁ σ₁ f hf ϑ ?_ th ht, hϑ⟩
  intro α y J hJ
  exact (((secScal_one_iff D.toPre.P.isLB).1 (hϑ α)) y J hJ).symm

end GlobalTheory.IntExpand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInv
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelMoveRestr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frPt_ptF {K : Type} [Field K] [Algebra c.F K] (t : Sp K ⟶ Xo.XF c)
    (ht : t ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) : ∃ y : FrPt Xo c K, ptF y = t := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (Xo := Xo) (c := c) (S := K) (t ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, sOf, ← Spec.map_comp]; rfl)
  refine ⟨y, pullback.hom_ext ?_ ?_⟩
  · simp only [ptF, pullback.lift_fst]; exact hy
  · simp only [ptF, pullback.lift_snd]; exact ht.symm

theorem restr_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ γ
  haveI : IsSeparated Xo.s := Formalism.L2.Pj.sepX Xo
  haveI : IsReduced (Xo.XF c) := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  refine ext_of_fromSpecResidueField_eq _ _ (pullback.snd _ _) Set.univ dense_univ (fun x _ => ?_) ?_
  · let t : Spec ((V₀ TF.Y Z).residueField x) ⟶ Sp c.F :=
      (V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z ≫ pullback.snd _ _
    letI : Algebra c.F ((V₀ TF.Y Z).residueField x) := (Spec.preimage t).hom.toAlgebra
    obtain ⟨y, hy⟩ := exists_frPt_ptF (K := (V₀ TF.Y Z).residueField x)
      ((V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z) (by
        rw [Category.assoc]
        exact (Spec.map_preimage t).symm)
    have h1 := hρ.2 γ ((V₀ TF.Y Z).residueField x) y ((V₀ TF.Y Z).fromSpecResidueField x) hy.symm
    rw [h1, GlobalTheory.CompLevelStab.ptF_move hpq hA Xo c, hy, Category.assoc]
  · have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    have h0 := hρ.1 γ
    rw [GlobalTheory.CompLevelStab.j₀_s₀, hid, Category.comp_id] at h0
    rw [Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_snd]
    exact h0

end GlobalTheory.LevelMoveRestr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvCompOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymSpread

theorem inv_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

end GlobalTheory.SymSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem isInv_constFn (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by
  refine TopCat.Presheaf.section_ext G.left.sheaf O _ _ fun y hy => ?_
  let g : Sp (G.left.presheaf.stalk y) ⟶ G.left := G.left.fromSpecStalk y
  let φ : R →+* G.left.presheaf.stalk y := (Spec.preimage (g ≫ G.hom)).hom
  have hφ : g ≫ G.hom = spMap φ := (Spec.map_preimage (g ≫ G.hom)).symm
  have ht : ⊤ ≤ g ⁻¹ᵁ O := by
    intro z _
    have hz : g z ∈ Set.range g := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open O.isOpen hy
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := by
    intro A B C _ _ _ f f'
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let g' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap _ (DualNumber (G.left.presheaf.stalk y))) ≫ g) (by simp)
  have hdual : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
      rw [Category.assoc, Over.w (tv v)]
      simp only [Over.mk_hom, Category.comp_id]
      rw [← hcomp, hdual, hcomp, hφ])
  have key := hv.2 _ φ g (g' * v').left O (constFn G.hom O r) hφ ht ⟨g', v', rfl, rfl, rfl⟩
  have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
    by_cases hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
    · rw [GlobalTheory.Points.valR_constFn_of_over G.hom ((algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ)
        _ ?_ O hw r]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Over.w (g' * v'), hcomp]
        simp only [Over.mk_hom]
        rw [hφ]
    · simp [valR, dif_neg hw]
  rw [h0] at key
  exact ((GlobalTheory.FormalValue.valR_fromSpecStalk y O hy _).symm.trans key.symm).trans
    (map_zero (G.left.presheaf.germ O y hy).hom).symm

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGeneratorTopFormsOfFormallyUnramifiedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified : ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  first | exact @GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | exact GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | (intros; apply GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified <;> assumption)
end

