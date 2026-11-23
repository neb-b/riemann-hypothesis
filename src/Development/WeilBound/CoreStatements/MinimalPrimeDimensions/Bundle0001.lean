module

public import Mathlib
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0013

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.Points

namespace ChowFormHeightComparison₂.CF

namespace ModelEmbedding

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω} {m : ℕ}
  {σ : Fin m → H.Sec} {t : Fin m → Ω}

theorem emb (hM : M.IsCl t) (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hs : ⨆ k, nonzeroLocus (σ k) = ⊤) : Emb M.s σ := by
  refine ⟨hH, hs, fun i => ?_⟩
  have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
    have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
    subst this
    infer_instance
  have key' := mem_nonzeroLocus_iff_div hH hd hv (PositivityTheory.UnitarySelfGeneration.UnitProductCombination.exists_unit hd hv hs) i
  generalize nonzeroLocus (σ i) = W at key' ⊢
  by_cases hi : t i = 0
  · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
    subst hW
    refine ⟨isAffineOpen_bot _, fun _ => 0, fun f => ⟨0, Subsingleton.elim _ _⟩, fun j l => ?_⟩
    have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
    exact Subsingleton.elim _ _
  · obtain ⟨U, hUa, hUe, hR⟩ := hM.2 i hi
    have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
    subst hWU
    have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
    have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
      (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
    choose r hr using hr
    refine ⟨hUa, r, fun f => ?_, fun j l => ?_⟩
    · have h1 : valF M.pt W f ∈ M.ringOn W := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
      rw [hR, Algebra.adjoin_range_eq_range_aeval] at h1
      obtain ⟨q, hq⟩ := h1
      have e : (M.res W hne).comp (eval₂Hom (algX M.s W) r) =
          (aeval (R := o) fun j => t j / t i).toRingHom :=
        MvPolynomial.ringHom_ext (fun a => by
          simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
          exact (M.res_apply W hne _).trans (M.valF_constFn hne a)) fun j => by
          simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
          exact (M.res_apply W hne _).trans (hr j)
      exact ⟨q, M.res_injective W hne ((RingHom.congr_fun e q).trans (hq.trans (M.res_apply W hne f).symm))⟩
    · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
      · have hl' : (H.U l : Set M.Z).Nonempty := hl.mono fun z (hz : z ∈ W ⊓ H.U l) => hz.2
        apply M.res_injective _ hl
        rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
          hv j l hl', hv i l hl', hr]
        have hdl := hd.ne l
        field_simp
      · have := hempty _ hl
        exact Subsingleton.elim _ _

theorem desc_eval (U : M.Z.Opens) (hV : M.pt (IsLocalRing.closedPoint Ω) ∈ U) (f : Γ(M.Z, U)) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt)).hom
      ((M.Z.evaluation U _ hV).hom f) = valF M.pt U f := by
  rw [valF_eq_valR, valR_eq M.pt U (M.top_le_preimage_pt ⟨_, hV⟩), ← germ_stalkClosedPointTo_eq_valMap,
    ← CommRingCat.comp_apply, ← Scheme.germ_residue, Category.assoc, Scheme.residue_descResidueField]

end ModelEmbedding

open ModelEmbedding

attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem stModel : StModel := by
  intro K Ω _ _ _ _ m t Z hZ H hH e he s hv hs _
  refine ⟨emb hZ hH he hv hs, ?_⟩
  have key : ∀ (i : H.ι) (h : Z.pt (IsLocalRing.closedPoint Ω) ∈ H.U i),
      RingHom.ker (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := fun i h => by
    have hne : (H.U i : Set Z.Z).Nonempty := ⟨_, h⟩
    have e1 : (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom).comp (coneHom Z.s s _ i h) =
        (GlobalTheory.CompHt.coneMap K ((e i)⁻¹ • t)).toRingHom.comp (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      MvPolynomial.ringHom_ext (fun a => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_C, RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, Polynomial.algebraMap_apply]
        exact congrArg Polynomial.C ((desc_eval _ h _).trans ((Z.valF_constFn hne a).trans
          (IsScalarTower.algebraMap_apply (𝓞 K) K Ω a)))) fun k => by
        simp only [coneHom, GlobalTheory.CompHt.coneMap, eval₂Hom_X', RingHom.comp_apply, Polynomial.coe_mapRingHom,
          Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X]
        exact congrArg (fun c => Polynomial.X * Polynomial.C c) ((desc_eval _ h _).trans ((hv k i hne).trans
          (div_eq_inv_mul _ _)))
    rw [← GlobalTheory.CompHt.coneIdeal_smul (inv_ne_zero (he.ne i))]
    have hinj : Function.Injective (Polynomial.mapRingHom (Scheme.descResidueField
        (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Z.pt)).hom) :=
      Polynomial.map_injective _ (RingHom.injective _)
    exact (RingHom.ker_comp_of_injective (coneHom Z.s s _ i h) hinj).symm.trans
      ((congrArg RingHom.ker e1).trans (RingHom.comap_ker _ _).symm)
  have h2 : ptIdeal Z.s s (genericPoint Z.Z) =
      (GlobalTheory.CompHt.coneIdeal K t).comap (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [← Z.pt_apply (IsLocalRing.closedPoint Ω)]
    have hm : Z.pt (IsLocalRing.closedPoint Ω) ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hl⟩ := Opens.mem_iSup.1 hm
    exact le_antisymm ((iInf₂_le l hl).trans (key l hl).le) (le_iInf₂ fun i h => (key i h).ge)
  rw [genIdeal, h2]
  exact IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m))) (MvPolynomial (Fin m) K) _

end ChowFormHeightComparison₂.CF
end
end

-- bundled from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ResGAppLE
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace ChowFormHeightComparison₂.CF

namespace PullbackComparison

variable {Y Z : Scheme.{0}} (i : Y ⟶ Z)

theorem resG_appLE {U : Z.Opens} {V V' : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (h : V' ≤ V) (a : Γ(Z, U)) :
    resG Y h ((i.appLE U V e).hom a) = (i.appLE U V' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map i e (homOfLE h).op]
  rfl

theorem appLE_resG {U U' : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U') (h : U' ≤ U) (e' : V ≤ i ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (i.appLE U' V e).hom (resG Z h a) = (i.appLE U V e').hom a := by
  rw [← Scheme.Hom.map_appLE i e (homOfLE h).op]
  rfl

theorem algX_comp {R : Type} [CommRing R] (p : Z ⟶ Sp R) {U : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (a : R) :
    algX (i ≫ p) V a = (i.appLE U V e).hom (algX p U a) := by
  simp only [algX, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE i p ⊤ U V (by simp) e]
  rfl

theorem surj_appLE [IsClosedImmersion i] {U : Z.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (e : V = i ⁻¹ᵁ U) :
    Function.Surjective (i.appLE U V e.le).hom := by
  subst e
  rw [Scheme.Hom.appLE_eq_app]
  exact i.app_surjective U hU

theorem eval_appLE {U : Z.Opens} {V : Y.Opens} (e : V ≤ i ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) (a : Γ(Z, U)) :
    (Y.evaluation V y hy).hom ((i.appLE U V e).hom a) =
      (i.residueFieldMap y).hom ((Z.evaluation U (i y) (e hy)).hom a) := by
  refine Eq.trans ?_ (Scheme.evaluation_naturality_apply i y (e hy) a).symm
  simp only [Scheme.Hom.appLE, Scheme.evaluation, LocallyRingedSpace.evaluation, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

end PullbackComparison

open PullbackComparison

theorem stPull : StPull := by
  intro R _ Z Y p B m s i _ hE
  have hAR : ∀ {U U' : Z.Opens} {W : Y.Opens} (e : W ≤ i ⁻¹ᵁ U') (h : U' ≤ U) (a : Γ(Z, U)),
      (i.appLE U' W e).hom (resG Z h a) = (i.appLE U W (fun y hy => h (e hy))).hom a :=
    fun e h a => appLE_resG i e h _ a
  have hf : ∀ (t : B.Sec) (J : (B.pull i).ι), (GlobalTheory.secPull t i).f J =
      (i.appLE (B.U (J PUnit.unit)) ((B.pull i).U J) (GlobalTheory.LB.pull_U i J).le).hom (t.f (J PUnit.unit)) := by
    intro t J
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f]
    rfl
  refine ⟨⟨LB.isLB_pull hE.isLB i, ?_, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    have h : i y ∈ ⨆ k, nonzeroLocus (s k) := by rw [hE.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [GlobalTheory.nonzeroLocus_secPull]; exact hk⟩
  · intro k
    obtain ⟨hAff, t, hsurj, hrel⟩ := hE.chart k
    have hV : nonzeroLocus (GlobalTheory.secPull (s k) i) = i ⁻¹ᵁ nonzeroLocus (s k) := GlobalTheory.nonzeroLocus_secPull _ _
    refine ⟨by rw [hV]; exact hAff.preimage i, fun j => (i.appLE _ _ hV.le).hom (t j), ?_, ?_⟩
    · have hcomp : eval₂Hom (algX (i ≫ p) (nonzeroLocus (GlobalTheory.secPull (s k) i)))
          (fun j => (i.appLE _ _ hV.le).hom (t j)) =
          (i.appLE _ _ hV.le).hom.comp (eval₂Hom (algX p (nonzeroLocus (s k))) t) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          exact algX_comp i p hV.le a
        · intro j
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hcomp]
      exact (surj_appLE i hAff hV).comp hsurj
    · intro j J
      have hle : nonzeroLocus (GlobalTheory.secPull (s k) i) ⊓ (B.pull i).U J ≤
          i ⁻¹ᵁ (nonzeroLocus (s k) ⊓ B.U (J PUnit.unit)) := by
        intro y hy
        exact ⟨hV.le hy.1, (GlobalTheory.LB.pull_U i J).le hy.2⟩
      have key := congrArg (i.appLE _ _ hle).hom (hrel j (J PUnit.unit))
      simp only [map_mul, hAR] at key
      simp only [hf, resG_appLE]
      exact key
  · intro y
    have hker : ∀ (J : (B.pull i).ι) (h : y ∈ (B.pull i).U J),
        RingHom.ker (coneHom (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) y J h) =
          RingHom.ker (coneHom p s (i y) (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le h)) := by
      intro J h
      have heq : coneHom (i ≫ p) (fun k => GlobalTheory.secPull (s k) i) y J h =
          (Polynomial.mapRingHom (i.residueFieldMap y).hom).comp
            (coneHom p s (i y) (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le h)) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [coneHom, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, Polynomial.coe_mapRingHom,
            Polynomial.map_C]
          rw [algX_comp i p (GlobalTheory.LB.pull_U i J).le a]
          congr 1
          exact eval_appLE i (GlobalTheory.LB.pull_U i J).le y h _
        · intro k
          simp only [coneHom, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Polynomial.coe_mapRingHom,
            Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
          rw [hf]
          congr 2
          exact eval_appLE i (GlobalTheory.LB.pull_U i J).le y h _
      rw [heq]
      exact RingHom.ker_comp_of_injective _ (Polynomial.map_injective _ (i.residueFieldMap y).hom.injective)
    apply le_antisymm
    · refine le_iInf₂ fun j hj => ?_
      let J : (B.pull i).ι := fun _ => j
      have hJ : y ∈ (B.pull i).U J := (GlobalTheory.LB.pull_U i J).ge hj
      exact (iInf₂_le J hJ).trans_eq (hker J hJ)
    · refine le_iInf₂ fun J hJ => ?_
      rw [hker J hJ]
      exact iInf₂_le (J PUnit.unit) ((GlobalTheory.LB.pull_U i J).le hJ)
  · intro u su hc J
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, hc (J PUnit.unit), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← algX_comp, hf]

end ChowFormHeightComparison₂.CF
end
end

