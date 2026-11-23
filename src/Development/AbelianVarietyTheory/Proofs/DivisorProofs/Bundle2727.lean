module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hP : A.IsForm (A.fn χ * γ) :=
    ((_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).2 0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) :=
    (_root_.GlobalTheory.CxForm.isForm_del_dbar M n A _ hP).2

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [_root_.GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dite_eq_right ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_isogeny_eq_deg_mul : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
    inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hf J _ hJ c
  obtain ⟨hdim, hflat, -, hrank⟩ := isogeny_flat_finrank K A B f hf
  haveI : IsFinite f.hom.left := hf.1
  haveI : Surjective f.hom.left := hf.2
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (isIntegral_isLocallyNoetherian_compactSpace K B).1
  have hAproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2
  have hBproj := (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K B).2
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hXproj : IsProjOver (f.hom.left ≫ B.X.hom) := by rw [hw]; exact hAproj
  have hAd := topologicalKrullDim_eq_dim K A
  have hBd := topologicalKrullDim_eq_dim K B

  have hgen : f.hom.left (genericPoint A.X.left) = genericPoint B.X.left := by
    have h1 := (genericPoint_spec A.X.left).image f.hom.left.continuous
    rw [Set.image_univ_of_surjective f.hom.left.surjective, closure_univ] at h1
    exact h1.eq (genericPoint_spec B.X.left)
  obtain ⟨V, hgV, hV, hV', hfree⟩ := GlobalTheory.GenFree.exists_affine_finite_free K A.X.left B.X.left B.X.hom
    f.hom.left hXproj hBproj hgen (by rw [hAd, hBd, hdim]) (f.hom.left.residueDegree (genericPoint A.X.left)) rfl
  set n := f.hom.left.residueDegree (genericPoint A.X.left)

  have hn : deg f = n := by
    letI := (f.hom.left.app V).hom.toAlgebra
    obtain ⟨hfr, hfin, hrk⟩ := hfree
    haveI := hfr
    haveI := hfin
    haveI : Module.Flat Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) := inferInstance
    obtain ⟨z, -⟩ : genericPoint B.X.left ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
    have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ (GlobalTheory.isPullback_fromSpec_app f.hom.left hV hV') z
    rw [hrank] at e
    have e2 := (Scheme.Hom.finrank_SpecMap_algebraMap Γ(B.X.left, V) Γ(A.X.left, f.hom.left ⁻¹ᵁ V) z).symm.trans e
    rw [Module.rankAtStalk_eq_finrank_of_free, hrk] at e2
    exact e2.symm

  choose L hL hc using fun j => cls_surj (c j)
  obtain rfl : c = fun j => cls (L j) (hL j) := funext fun j => (hc j).symm
  let e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have key := GlobalTheory.FieldProj.interNum_pull_eq_mul K A.X.left B.X.left B.X.hom f.hom.left hXproj hBproj V n
    hgV hV hV' hfree A.dim (by rw [hBd, hdim]) (fun i => L (e i)) (fun i => hL (e i))
  rw [hw] at key
  rw [hn]
  have hL' : ∀ i, ((fun i => L (e i)) i).pull f.hom.left |>.IsLB := fun i => Semi.LB.isLB_pull (hL (e i)) _
  letI := GlobalTheory.algebraΓOfHom A.X.hom
  letI := GlobalTheory.algebraΓOfHom B.X.hom
  rw [interNum_eq_multiDiff K _ hL', interNum_eq_multiDiff K _ (fun i => hL (e i))] at key
  unfold inter
  rw [← multiDiff_comp_equiv e, ← multiDiff_comp_equiv e (fun j => cls (L j) (hL j))]
  convert key using 3
  · rename_i i
    exact (cls_pull (hL (e i)) f.hom.left _).symm
  · rfl

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfProperIsIsoOnReductions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isIso_of_isIso_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  intro R _ _ I hI T X φ f hφ hf Y c hpb hpb'
  have hc := fun e => _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) T (Y e).left (φ ≫ f) (c e) (Y e).hom (hpb e)
  have hc' := fun e => _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) X (Y e).left f (c e ≫ φ) (Y e).hom (hpb' e)

  have hK : (baseIdeal f I).comap φ = (c 0).ker := by
    rw [(hc 0).2.1, (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1 R X T f φ I, zero_add, pow_one]
  haveI : IsClosedImmersion (c 0) := (hc 0).1
  haveI : IsClosedImmersion (c 0 ≫ φ) := (hc' 0).1
  have hφc : IsClosedImmersion φ := by
    refine _root_.GlobalTheory.ClosedLev.isClosedImmersion_of_mod R I hI T X φ f hφ inferInstance ?_
    rw [hK]
    have he : (c 0).ker.subschemeι ≫ φ = inv (c 0).toImage ≫ (c 0 ≫ φ) := by
      rw [IsIso.eq_inv_comp]
      exact Scheme.Hom.toImage_imageι_assoc _ _
    rw [he]
    infer_instance
  haveI := hφc

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hker : φ.ker ≤ ⊥ := by
    refine _root_.GlobalTheory.FormalAlg.le_of_le_reductions R I hI X f φ.ker ⊥ inferInstance fun e => ?_
    rw [bot_sup_eq, ← (hc' e).2.1]
    exact Scheme.Hom.le_ker_comp (c e) φ
  have hbot : φ.ker = ⊥ := le_bot_iff.1 hker
  haveI : IsIso φ.imageι := by
    change IsIso φ.ker.subschemeι
    rw [hbot]
    infer_instance
  rw [← φ.toImage_imageι]
  infer_instance

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfAddFormalGroupLawEvalPoints
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem Chart.ev_X {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k} (c : Chart G d)
    (n : ℕ) (i : Fin d) : c.ev n (X i) = c.x n i := by
  have hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n))) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i
  show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i
  rw [coe_substAlgHom, subst_X hs, constantCoeff_C]

theorem Chart.isMapOf_add : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k)
    (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k)
    (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ →
    c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  intro p k _ d e G H c c' ν f g φ ψ hν hf hg n j
  have hφ := ((_root_.GlobalTheory.Katz.isMapOf_existsUnique_and p k d e G H c c' f).2 φ hf).1
  have hψ := ((_root_.GlobalTheory.Katz.isMapOf_existsUnique_and p k d e G H c c' g).2 ψ hg).1
  let L : H.A n ⊗[k] H.A n →ₐ[k] G.A n := Algebra.TensorProduct.lift
    (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)
  have hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a) := fun a => by
    have h := congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))
    simp only [toPts_ofConv] at h
    exact h.trans (AlgHom.convMul_apply _ _ a)
  have hy : ∀ i, IsNilpotent (L (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map L
  have ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0 := fun i => by
    cases i with
    | inl i => exact hφ i
    | inr i => exact hψ i
  have hnil : ∀ t, IsNilpotent (c.ev n (X t)) := fun t => by
    rw [Chart.ev_X]; exact c.nil n t
  have h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i) := fun i => by
    cases i with
    | inl i =>
      change c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)
      rw [hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    | inr i =>
      change c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)
      rw [hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have e1 := (_root_.GlobalTheory.evA_subst_and_map k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha
    (fun i => L (c'.x₂ n i)) hy h1 (ν j)
  have e2 := (_root_.GlobalTheory.evA_subst_and_map k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n)
    (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)
  change c.ev n (subst (Sum.elim φ ψ) (ν j)) = _
  rw [e1, ← e2, hadd]
  exact congrArg L (hν n j)

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_productOfLocalLevelsUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  first | exact @GlobalTheory.BCT.isOpen_globLev | exact GlobalTheory.BCT.isOpen_globLev | (intros; apply GlobalTheory.BCT.isOpen_globLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSlice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.KerTorsion

open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_pow_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (B : Type) [CommRing B] (y : Sp B ⟶ S) (x : Over.mk y ⟶ A), (∃ t : (P.pull (lift (snd A (Over.mk y) ≫ x) (fst A (Over.mk y))).left).Gen, t.IsGen) → ∃ M : ℕ, 0 < M ∧ x ^ M = 1 := by
  intro S A _ _ P ab hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ symm ample B _ y x ⟨t, ht⟩
  let A' := (Over.pullback y).obj A
  let φ := PullbackComparison.pφ y A
  let φ₂ := PullbackComparison.pφ₂ y A
  have pb : IsGrpPullback A' A y φ := PullbackComparison.isGrpPullback y A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare y A
  have hab : IsAbelianScheme A' :=
    { comm := inferInstance
      smooth := by have := ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  let P' : LB (G2 A').left := P.pull φ₂
  have hP' : P'.IsLB := pull_isLB hP φ₂
  have iso : LBIso P' (P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  obtain ⟨B₀, A₀, _, _, ψ, ψ₂, P₀, fin, ab₀, pb₀, sq₀, hP₀, iso₀, r₁, r₂, symm₀, ample₀⟩ :=
    GlobalTheory.T.polarised_abelian_scheme_descends_finite_type B A' P' hab hP'
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id y A)) t₁ ht₁)
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one y A)) t₂ ht₂)
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
        (chartPullLinComb P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap y A)) symm)
      ((pol_pull S _ A A' y φ _ _ (pull_isLB hP _) (pull_isLB hP' _) ab pb dg).2.1 ample)
  have : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing ℤ B₀
  obtain ⟨M, hM, hker⟩ := GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian B₀ A₀ P₀ ab₀ hP₀ r₁ r₂ symm₀ ample₀
  refine ⟨M, hM, ?_⟩
  let T : Over (Sp B) := Over.mk (𝟙 _)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb T y (Category.id_comp _).symm
  have hx : x.left = (e.symm x).left ≫ φ := by rw [← he, e.apply_symm_apply]
  have key : e.symm x ^ M = 1 := by
    refine GlobalTheory.HTPull.kernel_pullback pb₀ sq₀ hP₀ hP' iso₀ M hker T (e.symm x) ?_
    have w : ((fst A' T).left ≫ φ) ≫ A.hom = (snd A' T).left ≫ y := by
      rw [Category.assoc, pb.1.w, ← Category.assoc, Over.w (fst A' T), ← Over.w (snd A' T)]
      exact congrArg (· ≫ y) (Category.comp_id _)
    let χ : (A' ⊗ T).left ⟶ (A ⊗ Over.mk y).left := pullback.lift _ _ w
    have c₁ : χ ≫ (fst A (Over.mk y)).left = (fst A' T).left ≫ φ := pullback.lift_fst _ _ _
    have c₂ : χ ≫ (snd A (Over.mk y)).left = (snd A' T).left := pullback.lift_snd _ _ _
    refine gen_chartPull (chartPullLinComb P _ _ _ _ χ fun _ => ?_) t ht
    refine (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((A' ⊗ T).hom ≫ y))
      (T' := A' ⊗ T) (𝟙 _) _ _ (Z := A ⊗ Over.mk y) χ _ _ ?_ ?_)
    · rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← hx, ← Category.assoc χ, c₂]
    · rw [Category.id_comp, c₁]
  rw [← e.apply_symm_apply x, ← map_pow, key, map_one]

end GlobalTheory.KerTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem bcMap_isPullback (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L))) (bcMap L f).hom.left f.hom.left
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
  have h1 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)) =
      pullback.snd A.X.hom (spMap (algebraMap K L)) :=
    Over.w ((Over.pullback (spMap (algebraMap K L))).map f.hom)
  have h3 : ((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left :=
    pullback.lift_fst _ _ _
  have h2 : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have hout : IsPullback (pullback.fst A.X.hom (spMap (algebraMap K L)))
      (((Over.pullback (spMap (algebraMap K L))).map f.hom).left ≫ pullback.snd B.X.hom (spMap (algebraMap K L)))
      (f.hom.left ≫ B.X.hom) (spMap (algebraMap K L)) := by
    rw [h1, h2]
    exact IsPullback.of_hasPullback A.X.hom (spMap (algebraMap K L))
  exact IsPullback.of_bot hout h3.symm (IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L)))

theorem isIsogeny_bcMap_iff_and_deg_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K)
    (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  intro K _ L _ _ A B f
  have := GlobalTheory.LevelMap.isFinite_descendsAlong_fpqc
  have sq := bcMap_isPullback K L f
  have hB := IsPullback.of_hasPullback B.X.hom (spMap (algebraMap K L))
  have hs : Surjective (spMap (algebraMap K L)) := GlobalTheory.LevelMap.surjective_spMap _
  have hf : Flat (spMap (algebraMap K L)) := GlobalTheory.LevelMap.flat_spMap _
  have hq : QuasiCompact (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (pullback.fst B.X.hom (spMap (algebraMap K L))) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact MorphismProperty.of_isPullback (P := @Surjective) hB.flip hs
    · exact MorphismProperty.of_isPullback (P := @Flat) hB.flip hf
    · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hB.flip hq
  have hiso : IsIsogeny (bcMap L f) ↔ IsIsogeny f :=
    and_congr (MorphismProperty.iff_of_isPullback (P := @IsFinite) sq.flip hQ)
      (MorphismProperty.iff_of_isPullback (P := @Surjective) sq.flip hQ)
  refine ⟨hiso, ?_⟩
  by_cases h : IsIsogeny f
  · obtain ⟨-, hfl, -, hrk⟩ := _root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B f h
    have : IsFinite f.hom.left := h.1
    have e : deg (bcMap L f) = (bcMap L f).hom.left.finrank (baseChange L B).origin := if_pos (hiso.2 h)
    rw [e]
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq (baseChange L B).origin).trans (hrk _)
  · have e1 : deg (bcMap L f) = 0 := if_neg (fun h' => h (hiso.1 h'))
    have e2 : deg f = 0 := if_neg h
    rw [e1, e2]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_comp_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hf hg
  obtain ⟨-, hflf, -, hrf⟩ := _root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B f hf
  obtain ⟨-, hflg, -, -⟩ := _root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K B C g hg
  have : IsFinite f.hom.left := hf.1
  have : Surjective f.hom.left := hf.2
  have : IsFinite g.hom.left := hg.1
  have : Surjective g.hom.left := hg.2
  have hc : IsIsogeny (f ≫ g) := by
    refine ⟨?_, ?_⟩
    · rw [comp_hom, Over.comp_left]; infer_instance
    · rw [comp_hom, Over.comp_left]; infer_instance
  refine ⟨hc, ?_⟩
  have hdg : deg g = g.hom.left.finrank C.origin := if_pos hg
  have hdc : deg (f ≫ g) = (f ≫ g).hom.left.finrank C.origin := if_pos hc
  rw [hdc, hdg, comp_hom, Over.comp_left]
  exact GlobalTheory.FinrankComp.finrank_comp_of_const f.hom.left g.hom.left (deg f) hrf C.origin

end GlobalTheory.AV.AbVar
end

