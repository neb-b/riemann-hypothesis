module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def eulerDirs {n : ℕ} (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)}
  add_mem' := by
    rintro x x' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add (f := _), hc, hc']; funext p; simp [bsmul, add_mul]⟩
  zero_mem' := ⟨0, by rw [map_zero]; funext p; simp [bsmul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a • c, by rw [map_smul, hc]; funext p; simp [bsmul, mul_assoc]⟩

theorem eulerDirs_finrank (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (eulerDirs F y)
  have hsum := Submodule.finrank_add_eq_of_isCompl hU
  rw [Module.finrank_fin_fun] at hsum
  have hdm : d ≤ Module.finrank ℂ U := by omega
  set bU := Module.finBasis ℂ U
  let Mlin : (Fin (Module.finrank ℂ U) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
  let M : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Mlin
  have hMU : ∀ x, M x ∈ U := fun x => Submodule.coe_mem (bU.equivFun.symm x)
  have hMinj : Function.Injective M := fun a b h => bU.equivFun.symm.injective (Subtype.ext h)
  have hA : HasFDerivAt (fun y' => y + M y') M 0 := (M.hasFDerivAt).const_add y
  have hy : y + M 0 = y := by rw [map_zero, add_zero]
  have hF' : AnalyticAt ℂ F (y + M 0) := by rw [hy]; exact hF
  have hGa : AnalyticAt ℂ (fun y' => F (y + M y')) 0 :=
    hF'.comp (f := fun y' => y + M y') (analyticAt_const.add (M.analyticAt 0))
  have hGQ : ∀ᶠ y' in 𝓝 (0 : Fin (Module.finrank ℂ U) → ℂ), F (y + M y') ∈ mcPts Q := by
    have ht : Tendsto (fun y' => y + M y') (𝓝 0) (𝓝 y) := by
      have := hA.continuousAt.tendsto
      rwa [hy] at this
    exact ht.eventually hFQ
  obtain ⟨x, hx, c, hxc⟩ := hR K ι Q d _ (fun y' => F (y + M y')) 0 hQ hdm hGa hGQ
  have hFd : HasFDerivAt F (fderiv ℂ F y) (y + M 0) := by rw [hy]; exact hF.differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt (fun y' => F (y + M y')) ((fderiv ℂ F y).comp M) 0 :=
    hFd.comp (f := fun y' => y + M y') 0 hA
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hy] at hxc
  have hmem : M x ∈ eulerDirs F y ⊓ U := ⟨⟨c, hxc⟩, hMU x⟩
  rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hx (hMinj (by rw [hmem, map_zero]))

theorem map_star_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem PFIntZero.maDensity_eq_zero (hR : pointFormRank_holds.Statement)
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d r : ℕ}
    {L : Fin d → HermLine ι} {L' : Fin d → HermLine ι'} (N : Fin r → HermLine ι') (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (d + r + 1) → ℂ)} {y : Fin (d + r) → ℂ}
    {w : ((k : K') → ι' k) → ℂ} {γ : (Fin (d + r) → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((Fin.append L' N j).h (γ y'))) y = 0 := by
  set F : (Fin (d + r) → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  set A : Fin (d + r) → Matrix (Fin (d + r)) (Fin (d + r)) ℂ :=
    fun j => cxHessian (fun y' => Real.log ((Fin.append L' N j).h (γ y'))) y with hAdef
  have hker : ∀ k ∈ Finset.univ.map (Fin.castAddEmb r), ∀ x ∈ eulerDirs F y,
      (A k).map (starRingEnd ℂ) *ᵥ x = 0 := by
    intro k hk x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨c, hc⟩ := hx
    have hpot : (fun y' => Real.log ((Fin.append L' N (Fin.castAddEmb r j)).h (γ y'))) =
        fun y' => Real.log ((L j).h (F y')) := by
      funext y'
      rw [Fin.coe_castAddEmb, Fin.append_left, (hLL j).2]
    have h := pointFormEuler_holds.proof K ι (L j) (d + r) F y x c (hL j) hFa hFy hc
    rw [map_star_mulVec, hAdef]
    simp only
    rw [hpot, h, star_zero]
  have hmix := mixedDisc_eq_zero_of_ker (fun k => (A k).map (starRingEnd ℂ)) (eulerDirs F y) _
    (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact eulerDirs_finrank hR hQ hFa hFQ) hker
  rw [mixedDisc_map_star, map_eq_zero] at hmix
  show _ * _ * (mixedDisc A).re = 0
  rw [hmix, Complex.zero_re, mul_zero]

theorem PFIntZero.proof (hR : pointFormRank_holds.Statement) : PFIntZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N A s hv _ hQ hL hLL
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((Fin.append L' N j).h z)) (logNorm A s) y w
        = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (PFIntZero.maDensity_eq_zero hR N hv hQ hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem PFSecRed.exists_form_not_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s c ∧ s ∉ P :=
  ⟨∏ k, (X ⟨k, (hP.2.1.2.2 k).choose⟩ : MRing ι) ^ c k, AvoidRing.isMultiHomog_coordProd _ c,
    AvoidRing.coordProd_not_mem hP.2.1.1 _ (fun k => (hP.2.1.2.2 k).choose_spec) c⟩

theorem PFSecRed.proof
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      MultilinStatement F ι)
    (hDim : FibreDimStatement) : PFSecRed.Statement := by
  intro I hI r hsec K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' hN

  let c : K' → ℕ := fun k => (-(N (Fin.last r)).a k).toNat
  let H : HermLine ι' := HermLine.sqMetric c
  let A : HermLine ι' := (N (Fin.last r)).tensor H
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric c
  have hAs : IsSmoothHerm A := isSmoothHerm_tensor (hN _) hHs
  let a : K' → ℕ := fun k => ((N (Fin.last r)).a k + c k).toNat
  have hAa : ∀ k, A.a k = a k := by
    intro k
    show (N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ) =
      (((N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ)).toNat : ℤ)
    omega
  have hHa : ∀ k, H.a k = c k := fun k => rfl
  obtain ⟨sA, hsA, hsAP⟩ := PFSecRed.exists_form_not_mem hP' a
  obtain ⟨sH, hsH, hsHP⟩ := PFSecRed.exists_form_not_mem hP' c
  have hsnoc : ∀ B : HermLine ι', IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc (Fin.init N) B : Fin (r + 1) → HermLine ι') j) := by
    intro B hB j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hB
    · rw [Fin.snoc_castSucc]; exact hN _
  have e1 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) A) sA a hv hP' hP hJ hL hL'
    (hsnoc A hAs) (by simpa using hAa) hsA hsAP
  have e2 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) H) sH c hv hP' hP hJ hL hL'
    (hsnoc H hHs) (by simpa using hHa) hsH hsHP

  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact IsPullHerm.isSmoothHerm hv (hL' i) (hL i)
    | right i => rw [Fin.append_right]; exact hN _
  have hadd := (hI K' ι').2.1 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) H hP' hM (hN _) hHs
  rw [← Fin.append_snoc, ← Fin.append_snoc, ← Fin.append_snoc, Fin.snoc_init_self] at hadd

  have hV := hDim K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hJadd := hMult G.Φ (FibreBlock κ) (fibreIdx ι' κ) J hJ (fibreIdeal κ G) (r + 1)
    (Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a)) (Fin.last r)
    (fibreDeg κ (N (Fin.last r)).a) (fibreDeg κ H.a) hV
  simp only [Fin.update_snoc_last] at hJadd
  have f0 : (fun j => fibreDeg κ (N j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  have f1 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) A : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a + fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp [Fin.init]
  have f2 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) H : Fin (r + 1) → HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Fin.init]
  rw [f1] at e1
  rw [f2] at e2
  have key : I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) A)) -
        I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) H)) := by
    rw [eq_sub_iff_add_eq]
    exact hadd.symm
  rw [f0, key, e1, e2, hJadd]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

section Pull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P' J' : Ideal (MRing ι')} {n : ℕ}

def pullPt (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k')) (x : R.X) : (Σ k, ι k) → ℂ :=
  fun p => R.lift x x (v p)

def pullQ (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : Fin n → ℂ :=
  fun i => Ψ (segre (pullPt R v x)) i.succ / Ψ (segre (pullPt R v x)) 0

def pullW (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (pullPt R v x)) 0)⁻¹ • segre (pullPt R v x)

def pullBad (R : AnLogRes P' J' n) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0)}

end Pull

def pullbackPushforward_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ →
    (∀ j, volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0) ∧
      ∀ y, (pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ).Finite

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩

def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W

end Fibre

def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

end

end GroundTheory.Heights₂.Heights.Inter
end

