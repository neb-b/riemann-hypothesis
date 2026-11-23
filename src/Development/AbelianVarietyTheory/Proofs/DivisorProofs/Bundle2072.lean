module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResolvedModification
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

namespace GlobalTheory.QuotSetup

theorem geometricallyConnected_of_surjective {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : ConnectedSpace ↥(pullback (p ≫ f) x) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  let q := (pullbackRightPullbackFstIso f x p).inv ≫ pullback.snd p (pullback.fst f x)
  have : Surjective q := inferInstance
  exact q.surjective.connectedSpace q.continuous

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem surjective_of_isProjOver {F : Type} [Field F] {Y Z : Scheme.{0}} [IsIntegral Z] (p : Y ⟶ Sp F)
    (pZ : Z ⟶ Sp F) (f : Y ⟶ Z) (hf : f ≫ pZ = p) (hp : IsProjOver p) (hZ : IsProjOver pZ) (y : Y)
    (hy : f y = genericPoint Z) : Surjective f := by
  have h₁ : IsProper (f ≫ pZ) := hf ▸ ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have : IsProper pZ := ((isProjOver_iff_isProper_and_exists_isAmpleLB pZ).1 hZ).1
  have : IsProper f := IsProper.of_comp f pZ
  have hc : closure {genericPoint Z} ⊆ Set.range f :=
    f.isClosedMap.isClosed_range.closure_subset_iff.2 (by rintro _ rfl; exact ⟨y, hy⟩)
  exact ⟨fun z => hc (by rw [(genericPoint_spec Z).def]; trivial)⟩

end GlobalTheory.QuotSetup

namespace GlobalTheory.QuotSetup

theorem exists_resolved_modification : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X X' W V : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral W] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (φ : X' ⟶ X) (q : X' ⟶ W) (sW : W ⟶ Sp F) (i : V ⟶ X) (ℓ : V ⟶ X'), IsProjOver sX → GeometricallyConnected sX → IsProjOver (φ ≫ sX) → IsProjOver sW → IsFinite q → Surjective q → q ≫ sW = φ ≫ sX → IsOpenImmersion i → IsOpenImmersion ℓ → ℓ ≫ φ = i → ∀ (δ : LB X) (hδ : δ.IsLB) (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = CechPic.pull φ (cls δ hδ) → ∀ (J : Type) (v : J → (Sp ℂ ⟶ V)), (∀ j j', v j ≫ ℓ ≫ q = v j' ≫ ℓ ≫ q) → (∃ j, ∀ s, (v j ≫ i) s = genericPoint X) → ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (pW : W' ⟶ Sp F) (U : X.Opens) (M : Modif sX U n) (f : M.X ⟶ W') (NW : LB W') (hNW : NW.IsLB), IsIntegral M.X ∧ SmoothOfRelativeDimension n pW ∧ IsProjOver pW ∧ GeometricallyConnected pW ∧ f ≫ pW = M.str ∧ Surjective f ∧ (U : Set X).Nonempty ∧ CechPic.pull f (cls NW hNW) = CechPic.pull M.σ (cls δ hδ) ∧ ∃ z : J → (Sp ℂ ⟶ M.X), (∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn) ∧ (∀ j, z j ≫ M.σ = v j ≫ i) ∧ (∀ j j', z j ≫ f = z j' ≫ f) ∧ (∀ j s, (z j ≫ f) s = genericPoint W') := by
  intro hP F _ _ X X' W V _ _ _ sX n _ φ q sW i ℓ hsX hgc hφ hsW hqf hqs hw hi hℓ hℓi δ hδ N hN hNδ J v hv hgen
  obtain ⟨j₀, hj₀⟩ := hgen
  obtain ⟨o₀⟩ : Nonempty (Sp ℂ) := inferInstance
  haveI : Nonempty V := ⟨v j₀ o₀⟩
  haveI : IsIntegral V := isIntegral_of_isOpenImmersion i
  haveI : Nonempty X := ⟨i (v j₀ o₀)⟩
  have hpX : IsProper sX := ((isProjOver_iff_isProper_and_exists_isAmpleLB sX).1 hsX).1
  have hpX' : IsProper (φ ≫ sX) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hφ).1
  have hpW : IsProper sW := ((isProjOver_iff_isProper_and_exists_isAmpleLB sW).1 hsW).1

  have hWgen : ∀ j o, (v j ≫ ℓ ≫ q) o = genericPoint W := fun j o => by
    rw [hv j j₀]
    have h₁ : v j₀ o = genericPoint V :=
      i.isOpenEmbedding.injective ((hj₀ o).trans (genericPoint_eq_of_isOpenImmersion i).symm)
    simp only [Scheme.Hom.comp_apply]
    rw [h₁, genericPoint_eq_of_isOpenImmersion ℓ, map_genericPoint q]

  have hdW : topologicalKrullDim W = n := by
    have hdX : topologicalKrullDim X = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth sX n inferInstance
    have hdV := _root_.GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X V sX i
    have hdV' := _root_.GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion F X' V (φ ≫ sX) ℓ
    have h₁ := PosBaseChange.dim_le_of_isClosedMap q.isClosedMap q.surjective
    have h₂ := PosBaseChange.dim_le_of_isDiscrete q.continuous q.isDiscrete_preimage_singleton
    rw [← hdX, ← hdV, hdV']
    exact le_antisymm h₁ h₂

  obtain ⟨W', s, UW, hW', hsm, hpj, hUW, hiso⟩ := _root_.GlobalTheory.WeakRes.weak_resolution hP F W sW n hsW hdW
  haveI := hW'
  haveI := hiso
  have hηUW : genericPoint W ∈ UW := genericPoint_mem UW hUW

  let O : V.Opens := (ℓ ≫ q) ⁻¹ᵁ UW
  have hvO : ∀ j o, v j o ∈ O := fun j o => by
    show (ℓ ≫ q) (v j o) ∈ UW
    rw [← Scheme.Hom.comp_apply, hWgen j o]
    exact hηUW
  let U : X.Opens := i ''ᵁ O
  have hUi : Set.range U.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  let e : U.toScheme ⟶ V := IsOpenImmersion.lift i U.ι hUi
  have he : e ≫ i = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hc : Set.range (e ≫ ℓ ≫ q) ⊆ Set.range UW.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : i (e x) ∈ U := by rw [← Scheme.Hom.comp_apply, he]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rw [i.isOpenEmbedding.injective hyx] at hy
    exact hy
  let c : U.toScheme ⟶ UW.toScheme := IsOpenImmersion.lift UW.ι (e ≫ ℓ ≫ q) hc
  have hcf : c ≫ UW.ι = e ≫ ℓ ≫ q := IsOpenImmersion.lift_fac _ _ _
  let b : UW.toScheme ⟶ W' := inv (s ∣_ UW) ≫ (s ⁻¹ᵁ UW).ι
  have hb : b ≫ s = UW.ι := by simp [b, ← morphismRestrict_ι]
  let r₀ : U.toScheme ⟶ pullback q s :=
    pullback.lift (e ≫ ℓ) (c ≫ b) (by rw [Category.assoc, Category.assoc, hb, hcf])
  have hUne : (U : Set X).Nonempty := ⟨i (v j₀ o₀), v j₀ o₀, hvO j₀ o₀, rfl⟩
  have ht : IsProjOver (pullback.snd q s ≫ s ≫ sW) := isProjOver_comp_of_isFinite _ hpj
  have hr₀ : r₀ ≫ pullback.snd q s ≫ s ≫ sW = U.ι ≫ sX := by
    simp only [r₀, pullback.lift_snd_assoc, Category.assoc]
    rw [reassoc_of% hb, reassoc_of% hcf, hw, reassoc_of% hℓi, reassoc_of% he]
  obtain ⟨M, r, hMi, hrt, hrM⟩ :=
    _root_.GlobalTheory.CompHS.exists_modif_map_of_open hP F X (pullback q s) sX n (pullback.snd q s ≫ s ≫ sW) U r₀ inferInstance hsX ht hUne hr₀
  haveI := hMi
  have hsep : IsSeparated sX := inferInstance
  haveI : IsDominant M.opn.ι := ⟨show Dense (Set.range M.opn.ι) by rw [Scheme.Opens.range_ι]; exact M.dense⟩
  have hσ : r ≫ pullback.fst q s ≫ φ = M.σ := by
    refine ext_of_isDominant_of_isSeparated sX ?_ M.opn.ι ?_
    · simp only [Category.assoc]
      rw [← hw, pullback.condition_assoc]
      exact hrt
    · rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_fst_assoc, Category.assoc]
      rw [hℓi, he, morphismRestrict_ι]
  let f : M.X ⟶ W' := r ≫ pullback.snd q s
  have hfs : f ≫ s = (r ≫ pullback.fst q s) ≫ q := by
    simp only [f, Category.assoc, pullback.condition]
  have hfp : f ≫ s ≫ sW = M.str := by
    simp only [f, Category.assoc]; exact hrt

  have hvU : ∀ j, ⊤ ≤ (v j ≫ i) ⁻¹ᵁ U := fun j o _ => by
    show (v j ≫ i) o ∈ U
    rw [Scheme.Hom.comp_apply]
    exact ⟨v j o, hvO j o, rfl⟩
  choose z hz using fun j => (M.existsUnique_lift (v j ≫ i) (hvU j)).exists
  have hzU : ∀ j, ⊤ ≤ z j ⁻¹ᵁ M.opn := fun j => by
    show ⊤ ≤ z j ⁻¹ᵁ (M.σ ⁻¹ᵁ U)
    rw [← Scheme.Hom.comp_preimage, hz j]
    exact hvU j
  have key : ∀ j, ∃ d : Sp ℂ ⟶ UW.toScheme, d ≫ UW.ι = v j ≫ ℓ ≫ q ∧ z j ≫ f = d ≫ b := fun j => by
    have hr : Set.range (z j) ⊆ Set.range M.opn.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨o, rfl⟩
      exact hzU j (Set.mem_univ o)
    let w := IsOpenImmersion.lift M.opn.ι (z j) hr
    have hw' : w ≫ M.opn.ι = z j := IsOpenImmersion.lift_fac _ _ _
    have hwe : w ≫ (M.σ ∣_ U) ≫ e = v j := by
      rw [← cancel_mono i, Category.assoc, Category.assoc, he, morphismRestrict_ι, reassoc_of% hw', hz j]
    refine ⟨w ≫ (M.σ ∣_ U) ≫ c, ?_, ?_⟩
    · rw [Category.assoc, Category.assoc, hcf, ← reassoc_of% hwe]
    · simp only [f, ← hw', Category.assoc]
      rw [reassoc_of% hrM]
      simp only [r₀, pullback.lift_snd, Category.assoc]
  choose d hd hzd using key
  haveI : Nonempty UW.toScheme := ⟨⟨_, hηUW⟩⟩
  haveI : IsIntegral UW.toScheme := isIntegral_of_isOpenImmersion UW.ι
  have hgen' : ∀ j o, (z j ≫ f) o = genericPoint W' := fun j o => by
    have h₁ : d j o = genericPoint UW.toScheme := by
      apply UW.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hd j, hWgen j o, genericPoint_eq_of_isOpenImmersion UW.ι]
    rw [hzd j, Scheme.Hom.comp_apply, h₁]
    exact genericPoint_eq_of_isOpenImmersion b
  have hfsurj : Surjective f :=
    surjective_of_isProjOver M.str (s ≫ sW) f hfp M.proj hpj (z j₀ o₀) (by rw [← Scheme.Hom.comp_apply]; exact hgen' j₀ o₀)
  have hgcM : GeometricallyConnected M.str := _root_.GlobalTheory.ModifGeomConn.geometricallyConnected_modif F X sX n U M hUne
  have hgcW : GeometricallyConnected (s ≫ sW) := by
    rw [← hfp] at hgcM
    exact geometricallyConnected_of_surjective f (s ≫ sW)
  refine ⟨W', hW', s ≫ sW, U, M, f, N.pull s, LB.isLB_pull hN s, hMi, hsm, hpj, hgcW, hfp, hfsurj, hUne, ?_,
    z, hzU, hz, fun j j' => ?_, hgen'⟩
  · rw [cls_pull hN s, ← pull_comp, hfs, pull_comp, hNδ, ← pull_comp, Category.assoc, hσ]
  · rw [hzd j, hzd j']
    congr 1
    rw [← cancel_mono UW.ι, hd j, hd j', hv j j']

end GlobalTheory.QuotSetup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowAmpleForallLocalCondition
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory

namespace SecLocalCondition

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {W : Scheme.{0}} [IsIntegral W] {H : LB W}

theorem gen_mem_nonzeroLocus_iff {n : ℕ} (s : (lbPow H n).Sec) {J : PUnit → H.ι}
    (hJ : genericPoint W ∈ powChart H J) :
    genericPoint W ∈ nonzeroLocus s ↔ fnOf _ hJ (powFn s J) ≠ 0 := by
  refine (mem_nonzeroLocus_iff_powFn s hJ).trans ((LBGerm.isUnit_gs_iff (𝟙 W) (genericPoint W) (powChart H J) hJ (powFn s J)).trans ?_)
  change genericPoint W ∈ W.basicOpen (powFn s J) ↔ _
  rw [← unitAt_fnOf_iff hJ hJ]
  exact ⟨UnitAt.ne_zero, unitAt_genericPoint⟩

theorem regAt_pow {x : W} {f : W.functionField} (h : RegAt x f) (k : ℕ) : RegAt x (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ k ih => rw [pow_succ]; exact ih.mul h

theorem exists_local (hA : IsAmpleLB H) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {y : W} {V : W.Opens} (hy : y ∈ V) (d : Γ(W, V))
    (hd : fnOf V (gen_mem hy) d ≠ 0) (hPd : ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) :
    ∃ m, 1 ≤ m ∧ ∃ u : (lbPow H m).Sec, ∃ O : W.Opens, y ∈ O ∧ genericPoint W ∈ nonzeroLocus u ∧
      ∀ y' ∈ O, ∀ (i : (lbPow H m).ι) (hi : y' ∈ (lbPow H m).U i), P y' (fnOf _ (gen_mem hi) (u.f i)) := by
  have := hA.compactSpace
  have := hA.quasiSeparatedSpace
  obtain ⟨q, hq, s, hys, hle, -⟩ := hA.exists_affine_le hy
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 0) hA.isLB s
    (fun J => resG W (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) d)
    (LBGerm.mem_secOn_of_germ (M := lbPow H 0) _ fun z J J' hs hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 W) z J J' hJ hJ', pow_zero, Units.val_one, one_mul]
      exact (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J ≤ V) ⟨hs, hJ⟩ d).trans
        (gs_res (𝟙 W) z (inf_le_left.trans hle : nonzeroLocus s ⊓ powChart H J' ≤ V) ⟨hs, hJ'⟩ d).symm)
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  have key : ∀ (J : PUnit → H.ι) (hJ : genericPoint W ∈ powChart H J),
      fnOf _ hJ (powFn u J) = fnOf _ hJ (powFn s J) ^ (N + 1) * fnOf V (gen_mem hy) d := by
    intro J hJ
    have hη : genericPoint W ∈ nonzeroLocus s ⊓ powChart H J := ⟨gen_mem hys, hJ⟩
    have e := congrArg (fnOf _ hη) (hu J)
    rwa [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at e
  refine ⟨0 + q * (N + 1), by nlinarith, u, _, hys, ?_, fun y' hy' i hi => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_chart (isLB_lbPow hA.isLB q) (genericPoint W)
    rw [gen_mem_nonzeroLocus_iff u hJ, key J hJ]
    exact mul_ne_zero (pow_ne_zero _ ((gen_mem_nonzeroLocus_iff s hJ).1 (gen_mem hys))) hd
  · have hr : RegAt y' (fnOf _ (gen_mem hi) (powFn s i) ^ (N + 1)) :=
      regAt_pow (regAt_fnOf hi (gen_mem hi) (powFn s i)) (N + 1)
    have e : fnOf _ (gen_mem hi) (u.f i) = _ := key i (gen_mem hi)
    rw [e]
    exact hP y' _ _ (hPd y' (hle hy')) hr

theorem exists_prod (hL : H.IsLB) (P : W → W.functionField → Prop)
    (hP : ∀ y c c', P y c → RegAt y c' → P y (c' * c)) {ι : Type} (m : ι → ℕ) (hm : ∀ a, 1 ≤ m a)
    (u : ∀ a, (lbPow H (m a)).Sec) (hu : ∀ a, genericPoint W ∈ nonzeroLocus (u a)) (Q : ι → W → Prop)
    (hQ : ∀ a y', Q a y' → ∀ (i : (lbPow H (m a)).ι) (hi : y' ∈ (lbPow H (m a)).U i),
      P y' (fnOf _ (gen_mem hi) ((u a).f i))) (T : Finset ι) :
    ∃ n, (T.Nonempty → 1 ≤ n) ∧ ∃ t : (lbPow H n).Sec, genericPoint W ∈ nonzeroLocus t ∧
      ∀ a ∈ T, ∀ y', Q a y' → ∀ (i : (lbPow H n).ι) (hi : y' ∈ (lbPow H n).U i),
        P y' (fnOf _ (gen_mem hi) (t.f i)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, fun h => absurd h Finset.not_nonempty_empty, secOfFn H 1, ?_, fun a ha => absurd ha (Finset.notMem_empty a)⟩
    rw [nonzeroLocus_secOfFn hL, Scheme.basicOpen_one]
    trivial
  | insert b T hb ih =>
    obtain ⟨n, -, t, ht, htP⟩ := ih
    refine ⟨m b + n, fun _ => le_add_right (hm b), secMul (u b) t,
      (nonzeroLocus_secMul (u b) t).ge ⟨hu b, ht⟩, fun a ha y' hy' i hi => ?_⟩
    have e : fnOf _ (gen_mem hi) ((secMul (u b) t).f i) =
        fnOf _ (gen_mem hi) ((u b).f i) * fnOf _ (gen_mem hi) (t.f i) :=
      map_mul (fnOf _ (gen_mem hi)) ((u b).f i) (t.f i)
    rw [e]
    rcases Finset.mem_insert.1 ha with rfl | ha
    · rw [mul_comm]
      exact hP y' _ _ (hQ a y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)
    · exact hP y' _ _ (htP a ha y' hy' i hi) (regAt_fnOf hi (gen_mem hi) _)

end SecLocalCondition


open SecLocalCondition in
theorem exists_sec_forall_local_condition : ∀ (W : Scheme.{0}) [IsIntegral W] (H : LB W), IsAmpleLB H →
    ∀ (P : W → W.functionField → Prop), (∀ y c c', P y c → RegAt y c' → P y (c' * c)) →
    (∀ y, ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, P y' (fnOf V (gen_mem hy) d)) →
    ∃ n, 1 ≤ n ∧ ∃ t : (lbPow H n).Sec, t ≠ 0 ∧
      ∀ (y : W) (i : (lbPow H n).ι) (hi : y ∈ (lbPow H n).U i), P y (fnOf _ (gen_mem hi) (t.f i)) := by
  intro W _ H hA P hP hloc
  have := hA.compactSpace
  choose V hy d hd hPd using hloc
  choose m hm u O hyO hu hQ using fun y => exists_local hA P hP (hy y) (d y) (hd y) (hPd y)
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top O hyO
  obtain ⟨n, hn, t, ht, htP⟩ := exists_prod hA.isLB P hP m hm u hu (fun a y' => y' ∈ O a) hQ T
  refine ⟨n, hn ?_, t, (sec_ne_zero_iff t).2 ht, fun y i hi => ?_⟩
  · obtain ⟨a, -⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (genericPoint W)))
    exact ⟨a, a.2⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ y))
    exact htP a a.2 y ha i hi

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.PullSecSq

theorem exists_sec_lbPow_two_nonzeroLocus : ∀ (Y X : Scheme.{0}) (f : Y ⟶ X) (M₀ : LB X), M₀.IsLB → ∀ (s₀ : M₀.Sec) (T₁ T₂ : Y ⟶ Y), (∃ t : LB.Gen (LB.LinComb (M₀.pull f) (K := Fin 3) ![T₁, T₂, 𝟙 Y] ![1, 1, -2]), t.IsGen) → ∃ s : (lbPow (M₀.pull f) 2).Sec, nonzeroLocus s = (T₁ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ ⊓ (T₂ ≫ f) ⁻¹ᵁ nonzeroLocus s₀ := by
  intro Y X f M₀ hM s₀ T₁ T₂ ⟨t, ht⟩
  have hN : (M₀.pull f).IsLB := LB.isLB_linComb hM _ _
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := Sum.elim (Sum.elim (fun _ : PUnit => T₁) (fun _ : PUnit => T₂)) (fun _ : PUnit => 𝟙 Y))
    (ε' := Sum.elim (Sum.elim (fun _ : PUnit => (1 : ℤ)) (fun _ : PUnit => (1 : ℤ)))
      (fun k => - (fun _ : PUnit => ((2 : ℕ) : ℤ)) k)) (by
      intro U _ h
      simp only [Fin.prod_univ_three, Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      simp) t ht
  have H := AdjointOfPairing.lbIso_of_gen (φ := fun _ : PUnit => 𝟙 Y) (ε := fun _ => ((2 : ℕ) : ℤ)) t' ht'
  obtain ⟨s, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2) (LB.isLB_linComb hN _ _) H
    (DVR.mulSec (M₀.pull f) (fun _ : PUnit => T₁) (fun _ => 1) (fun _ : PUnit => T₂) (fun _ => 1)
      (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₁) (GlobalTheory.secPull (GlobalTheory.secPull s₀ f) T₂))
  refine ⟨s, hs.trans ?_⟩
  simp only [GlobalTheory.nonzeroLocus_mulSec, GlobalTheory.nonzeroLocus_secPull]
  rfl

end GlobalTheory.PullSecSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.TransBaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]

theorem pullback_map_left_fst {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem mul_left_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    (u * v).left ≫ pullback.fst G.hom f =
      ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
        (μ[G]).left := by
  rw [Hom.mul_def, Functor.obj.μ_def]
  simp only [Over.comp_left, Category.assoc]
  rw [pullback_map_left_fst]

theorem lift_μ_fst {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (fst G G).left = u.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_fst, lift_fst]

theorem lift_μ_snd {X : Over S'} (u v : X ⟶ (Over.pullback f).obj G) :
    ((lift u v ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f) ≫
      (snd G G).left = v.left ≫ pullback.fst G.hom f := by
  rw [Category.assoc, ← pullback_map_left_fst, ← Category.assoc, ← Over.comp_left, Category.assoc,
    Functor.Monoidal.μ_snd, lift_snd]

theorem inv_left_fst {X : Over S'} (u : X ⟶ (Over.pullback f).obj G) :
    (u⁻¹).left ≫ pullback.fst G.hom f = u.left ≫ pullback.fst G.hom f ≫ (ι[G]).left := by
  rw [Hom.inv_def, Functor.obj.ι_def, Over.comp_left, Category.assoc, pullback_map_left_fst]

theorem toUnit_left (X : Over S') : (toUnit X).left = X.hom := Over.w (toUnit X)

theorem ext_tensor {Y : Scheme.{0}} (x y : Y ⟶ (G ⊗ G).left)
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) :
    x = y :=
  Over.tensorObj_ext _ _ h1 h2

theorem exists_section_translate : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R') (G : Over (Sp R)) [GrpObj G] (c : Sp R' ⟶ G.left), c ≫ G.hom = spMap ρ → ∃ (a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G) (Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left), IsPullback Φ (pullback.snd G.hom (spMap ρ)) (snd G G).left c ∧ Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * snd G G).left ∧ (𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ) = Φ ≫ (fst G G * (snd G G)⁻¹).left := by
  intro R R' _ _ ρ G _ c hc
  have hw : c ≫ G.hom = 𝟙 (Sp R') ≫ spMap ρ := by simpa using hc
  let a : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (spMap ρ)).obj G :=
    Over.homMk (pullback.lift c (𝟙 _) hw) (by dsimp; rw [pullback.lift_snd])
  have ha : a.left ≫ pullback.fst G.hom (spMap ρ) = c := pullback.lift_fst _ _ _
  have hcond : pullback.fst G.hom (spMap ρ) ≫ G.hom = (pullback.snd G.hom (spMap ρ) ≫ c) ≫ G.hom := by
    rw [Category.assoc, hc, pullback.condition]
  let Φ : pullback G.hom (spMap ρ) ⟶ (G ⊗ G).left :=
    (pullback.lift (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ) ≫ c) hcond :
      _ ⟶ pullback G.hom G.hom)
  have hΦ1 : Φ ≫ (fst G G).left = pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have hΦ2 : Φ ≫ (snd G G).left = pullback.snd G.hom (spMap ρ) ≫ c := pullback.lift_snd _ _ _
  have hu : ((toUnit ((Over.pullback (spMap ρ)).obj G)).left) = pullback.snd G.hom (spMap ρ) :=
    toUnit_left _
  refine ⟨a, Φ, ?_, hΦ1, ?_, ?_⟩
  · have outer : IsPullback (Φ ≫ (fst G G).left) (pullback.snd G.hom (spMap ρ)) G.hom (c ≫ G.hom) := by
      rw [hΦ1, hc]; exact IsPullback.of_hasPullback _ _
    have right : IsPullback (fst G G).left (snd G G).left G.hom G.hom :=
      IsPullback.of_hasPullback G.hom G.hom
    exact IsPullback.of_right outer hΦ2 right
  · rw [mul_left_fst, Hom.mul_def, lift_fst_snd, Category.id_comp]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, hΦ2, Over.comp_left, Category.assoc, ha, hu]
  · rw [mul_left_fst, Hom.mul_def (fst G G), Hom.inv_def (snd G G), Over.comp_left (f := lift (fst G G) (snd G G ≫ ι)),
      ← Category.assoc]
    congr 1
    apply ext_tensor
    · rw [lift_μ_fst, Category.assoc, ← Over.comp_left, lift_fst, hΦ1, Over.id_left, Category.id_comp]
    · rw [lift_μ_snd, Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        inv_left_fst, ← Category.assoc a.left, ha, hu, Over.comp_left, reassoc_of% hΦ2]

end GlobalTheory.TransBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Desc

theorem exists_smooth_nhds_of_smooth_fromSpecStalk :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  intro R _ _ P p x V W hWV hV hW z hz hle
  have : LocallyOfFinitePresentation (W.ι ≫ p) := inferInstance
  have : Flat ((Sp R).fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ x
  have : SurjectiveOnStalks ((Sp R).fromSpecStalk x) := inferInstance
  have e : W.ι ≫ p = P.homOfLE hWV ≫ V.ι ≫ p := by simp
  have h1 : Smooth (Limits.pullback.snd (P.homOfLE hWV ≫ V.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  have h2 : Smooth (Limits.pullback.snd (W.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [e]; exact h1
  have hs : p z ⤳ x := (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 hle
  obtain ⟨y, hy⟩ : p z ∈ Set.range ((Sp R).fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι ≫ p)
    (g := (Sp R).fromSpecStalk x) (⟨z, hz⟩ : W) y hy.symm
  have h3 := GlobalTheory.GenSpread.mem_smoothLocus_of_isPullback
    (IsPullback.of_hasPullback (W.ι ≫ p) ((Sp R).fromSpecStalk x)) w
  rw [hw] at h3
  have h4 : Smooth ((W.ι ≫ p).smoothLocus.ι ≫ W.ι ≫ p) := GlobalTheory.smooth_smoothLocus_ι_comp _
  refine ⟨W.ι ''ᵁ (W.ι ≫ p).smoothLocus, ⟨⟨z, hz⟩, h3, rfl⟩, W.ι_image_le _, ?_⟩
  rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc]
  infer_instance

end GlobalTheory.Desc
end

