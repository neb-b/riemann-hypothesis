module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFirstFromResolutionAndGaga
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsComplCrystalGluedHodgeGraphFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∃ M : Submodule (TrivSqZeroExt k (Fin d → k)) (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) o₀.A), IsCompl (GlobalTheory.HTGlue.glueFil o₀.A f) M := by
  first | (exact @GlobalTheory.HTGlue.exists_isCompl_glueFil) | (exact GlobalTheory.HTGlue.exists_isCompl_glueFil) | (intros; apply GlobalTheory.HTGlue.exists_isCompl_glueFil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEvaluationHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_evaluation_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∀ e : ℕ, ∃ ev : D.La → (Over.mk x ⟶ o.A), (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = ev y ≫ o.act.act c) ∧ (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  first | (exact @GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (exact GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (intros; apply GlobalTheory.UPel.HT.PTors.exists_ev_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPrincipalSymmetricBundleComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolLiftComplete

theorem exists_lift : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  intro K _ _ R₁ _ _ _ _ hc π hπ A _ _ hA P hP r₁ r₂ hs ha hker
  obtain ⟨L, hL, hΛ, haL⟩ := GlobalTheory.PolBundleLoc.exists_ample_root A hA hP r₁ r₂ hs ha
  have hKL : KTriv A L := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso (Sp K) A hA P hP hker L hL hΛ
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := GlobalTheory.SqStep.exists_lift (R₁ ⧸ I ^ (e + 1 + 1))
      (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (GlobalTheory.MumLift.ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* K :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp K := spMap (e₀.symm : K →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp K ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* K)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj A
  let g₀ : Y₀.left ⟶ A.left := pullback.fst A.hom s
  have G₀ : IsGrpPullback Y₀ A s g₀ := isGrpPullback_pullback A s
  have hL₀ : (L.pull g₀).IsLB := pull_isLB hL g₀
  have hA₀ : IsAbelianScheme Y₀ := by
    have hcomm : IsCommMonObj Y₀ := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (G₀.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← G₀.2 T x y (pushPt G₀.1.w x) (pushPt G₀.1.w y) rfl rfl,
        ← G₀.2 T y x (pushPt G₀.1.w y) (pushPt G₀.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm
            smooth := MorphismProperty.of_isPullback (P := @Smooth) G₀.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) G₀.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) G₀.1 hA.geomConnected }
  haveI := hA.proper
  have ha₀ : RelAmple Y₀ (L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL haL G₀.1
  have hK₀ : KTriv Y₀ (L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (L.pull g₀) (L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ hL hL₀ ((isGen_iff w).1 hw) hKL
  let y₀ : St 0 := ⟨Y₀, inferInstance, L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : A.left ⟶ Y₀.left := pullback.lift (𝟙 _) (A.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = A.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have n₀ : IsGrpPullback A A (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl A)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback A Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback A B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull hL, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M :=
    GlobalTheory.KTrivJacobson.kTriv_of_quotient R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hPf := GlobalTheory.AbDual.isPerfect_lam hM hK
  have hr : Out.Rigidified B M := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₁) (pull_isLB hM _)
  have hΘ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hM
  have w : (φ ≫ b 0) ≫ B.hom = A.hom ≫ spMap π := hi.1.w
  have sq := GlobalTheory.LamPull.exists_isSquare w
  have hlamA : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hlamB : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  refine ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, sq, hPf.isLB, hPf.zero_left, hPf.zero_right,
    GlobalTheory.FullSiegel.lam_symm hM, GlobalTheory.EighthPowerLocal.relAmple_diag_lam hB hM hΘ haM,
    fun T x h => GlobalTheory.FullSiegel.eq_one_of_lam_triv hM hr hK T x h, ?_⟩
  exact LBIso.trans hP hlamA (pull_isLB hlamB _) (LBIso.symm hΛ)
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM hL hLi sq)

end GlobalTheory.PolLiftComplete
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKernelKilledNearPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

theorem kerKilledOn_near : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, ∃ V : S'.Opens, g.base t ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hd hamp hker t
  obtain ⟨Ua, hUa, hUa'⟩ := GlobalTheory.T.diagonal_restriction_relAmple_locus_open S' G P hA hP
  obtain ⟨Ud, hUd, hUd'⟩ := GlobalTheory.T.natCast_unit_locus_open S' d
  have hsa : g.base t ∈ Ua := hUa' T g A' φ φ₂ P' hpb hsq hP' hiso hamp ⟨t, rfl⟩
  have hsd : g.base t ∈ Ud := hUd' T g hd ⟨t, rfl⟩
  exact GlobalTheory.T.kernelKilledOverOpen_near_of_fibre d S' G P hA hP hg₁ hg₂ hsym (Ua ⊓ Ud) (fun V hV => hUa V (hV.trans inf_le_left))
    (hUd _ inf_le_right) (g.base t) ⟨hsa, hsd⟩
    (GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat d S' G P hA hP hg₁ hg₂ hsym T g A' φ φ₂ P' hpb hsq hP' hiso hd hker t)

end GlobalTheory.KerKilledNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderAction_descent_along_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (exact GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (intros; apply GlobalTheory.UPel.HT.ES.exists_oAct_desc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryApproxPoincareSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_pos {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  set u := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hu
  have h0 : t.T.ϖ ≠ 0 := t.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective t.T.V (FractionRing t.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : t.ι u ≠ 0 := (map_ne_zero t.ι).2 hu0
  have hle : ‖t.ι u‖ ≤ 1 := (t.int u).2 ⟨_, rfl⟩
  have hlt : ‖t.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖t.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (t.int _).1 this
    apply t.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective t.T.V (FractionRing t.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖t.ι u‖ := norm_pos_iff.2 hι0
  unfold UCTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {φ : InvFun O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[O] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := StrictData.toReal_mem_psdCone hβ hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem posW_one : PosW (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![(1 : ℤ)] + (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) =
      Matrix.diagonal fun _ => (2 : ℝ) := by
    ext i j; fin_cases i; fin_cases j; norm_num [Matrix.vecHead, Function.swap]
  rw [this]
  exact Matrix.PosDef.diagonal (fun _ => by norm_num)

end GlobalTheory.UPoinc.GApprox

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_evalZ_eq {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun (𝓞 E)}
    (hpol : IsPolFan H.bar (min D.p D.q) φ)
    (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min D.p D.q) p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (t : UCTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) :
    Φ.sc y * φ.evalZ (Φ.β y) = t.sc * φ.evalZ t.T.be :=
  sc_evalZ_eq_of_equiv (hpol _ (Φ.rank_le y)) (Φ.bal y) (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos t) e he

theorem exists_hasSupports_cm (q : ℕ) (φ : InvFun (𝓞 E)) (hpol : IsPolFan H.bar q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) q φ d :=
  exists_hasSupports (𝓞 E) H.bar q φ hpol fun X _ _ _ _ hX r γ hγ => _root_.GlobalTheory.Poinc.exists_supports_cm E H φ X (hpol X hX) r γ hγ

end GlobalTheory.UPoinc.GApprox


open GlobalTheory.UPoinc.GApprox in
theorem GlobalTheory.UPoinc.exists_uApproxAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∃ d : ℕ, 1 ≤ d ∧ UApproxAt X₁ φ d := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_cm (H := H) (min Dw.p Dw.q) φ hpol
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  have hW1 : ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat = 1 := by simp
  refine ⟨((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀, by rw [hW1]; omega, ?_⟩
  intro p _ z₁ t₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := t₀.cen ▸ isClosed_singleton_cPt t₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := _root_.GlobalTheory.UPoinc.PreSys.main E H Dw hpq l Xo c C X₁ p z₁ hcl
  have hF := _root_.GlobalTheory.UPoinc.four_of_classical E H Dw hpq l Xo c C X₁ p z₁ Φ hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre (𝓞 E) H.bar (bddAct_int_and_cm.2 E H) (min Dw.p Dw.q) φ hpol d₀ hsup 0
    !![(1 : ℤ)] posW_one (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  set d := ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀ with hd
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM t₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (t : UCTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e' a) (e' b)) →
      Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by
    intro y t e' h
    have := sc_evalZ_eq hpol Φ y t e' h
    calc Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = (d : ℝ) * (Φ.sc y * φ.evalZ (Φ.β y)) := by ring
      _ = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by rw [this]; ring
  refine ⟨f, ?_, fun t => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ t₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM t
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y t e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  first | (exact @GlobalTheory.DualHomFlat.main) | (exact GlobalTheory.DualHomFlat.main) | (intros; apply GlobalTheory.DualHomFlat.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacterStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  first | (exact @GlobalTheory.HTRank.finrank_quot) | (exact GlobalTheory.HTRank.finrank_quot) | (intros; apply GlobalTheory.HTRank.finrank_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | (exact @GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (exact GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  first | (exact @GlobalTheory.HTLiftIso.liftFil_isotropic) | (exact GlobalTheory.HTLiftIso.liftFil_isotropic) | (intros; apply GlobalTheory.HTLiftIso.liftFil_isotropic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDegreeOneBiholomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.FinUnram

theorem formallyUnramified_of_dual_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R] [Module.Finite K R], (∀ (φ : R →ₐ[K] DualNumber K) (r : R), (φ r).snd = 0) → Algebra.FormallyUnramified K R := by
  intro K _ _ R _ _ _ H
  haveI : Algebra.FiniteType K R := inferInstance
  refine GlobalTheory.TangentCrit.formallyUnramified_of_dual_const_field (K := K) (A := K) (B := R)
    (fun φ hK _ b => ?_)
  exact H { φ with commutes' := hK } b

end GlobalTheory.FinUnram
end

