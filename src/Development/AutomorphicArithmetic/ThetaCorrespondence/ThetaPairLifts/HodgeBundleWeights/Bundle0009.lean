module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.Bundle0003
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0047
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0014
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
public import CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0013
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsModelOfImage
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo
namespace GlobalTheory.ImageModel
theorem exists_model_of_image : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  intro _ K V Ω _ _ _ _ _ _ _ _ Nm W ev D hK hG hcj hW hs hR hD
  classical
  obtain ⟨N, n, b, w, A, hF⟩ := GlobalTheory.CompHt.exists_isFrame hK hcj hG hW hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have hW0 : W = ⊥ := by rw [← hF.span]; simp
      have htop : (⊤ : Submodule K V) = ⊥ := by rw [← hs, hW0]; simp
      refine hR.1 (LinearMap.ext fun x => ?_)
      have hx : x ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx
      simp [hx]
    · exact ⟨m, rfl⟩
  set u : Fin (m + 1) → V := fun k => ∑ j, w j k • b j with hu_def
  have huW : ∀ k, u k ∈ W := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  let gw : Fin (m + 1) → W := fun k => ⟨u k, huW k⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    rw [← hs, ← hF.span, Submodule.span_span_of_tower]
  choose cc hcc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1
    (hspan ▸ Submodule.mem_top : b j ∈ Submodule.span K (Set.range u))
  let c : Matrix (Fin (m + 1)) (Fin N) K := Matrix.of fun k j => cc j k
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy0 : y ≠ 0 := fun h0 => hR.1 (LinearMap.ext_on_range hspan fun k => by
    simpa using congrFun h0 k)
  obtain ⟨Y, _, q, B₀, hB₀, t, ψ₀, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point K V Ω ev D m u hspan hR hD
  obtain ⟨X₀, _, p₀, g₀, ψ₁, e⟩ := _root_.GlobalTheory.SpreadModel.exists_spread K Ω D m y Y q B₀ hB₀ t ψ₀ h1 h2 h3 h4 h5 h6
  obtain ⟨X, _, p, g, ψ, hgp, har, hnorm, hbij, hbase, hrat⟩ := _root_.GlobalTheory.NormalModel.exists_normal_model K Ω D m y X₀ p₀ g₀ ψ₁ e
  let B := (ProjSpace.O1 (𝓞 K) m).pull g
  have hB : B.IsLB := LB.isLB_pull (ProjSpace.O1_isLB _ m) g
  let sk : Fin (m + 1) → B.Sec := fun k => secPull (ProjSpace.coord (𝓞 K) m k) g
  obtain ⟨hlin, hrel⟩ := _root_.GlobalTheory.PullCoordComb.linComb_ratio_and_vanish K Ω m y X p g ψ hbase hrat
  have hev : ∀ lam : Fin (m + 1) → 𝓞 K, ev (∑ k, lam k • u k) = ∑ k, algebraMap K Ω (lam k : K) * y k := by
    intro lam
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (lam k) (u k), LinearMap.map_smul, Algebra.smul_def]
  have hrelV : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • sk k = 0 :=
    fun lam h0 => hrel hy0 lam (by rw [← hev, h0, map_zero])
  choose coef hcoef using fun x : W => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1
    (hF.span.symm ▸ x.2 : (x : V) ∈ Submodule.span (𝓞 K) (Set.range u))
  let s : W → B.Sec := fun x => ∑ k, algX p ⊤ (coef x k) • sk k
  have sg : ∀ k, s (gw k) = sk k := by
    intro k
    have e1 : ∑ l, (Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l • u l = u k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, one_smul]
    have e3 : ∑ l, algX p ⊤ ((Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l) • sk l = sk k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, map_one, one_smul]
    have h0 := hrelV (coef (gw k) - Pi.single k 1) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcoef, e1]
      exact sub_eq_zero.2 (hcoef (gw k)))
    simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib, e3, sub_eq_zero] at h0
    exact h0
  have hbpf : ⨆ k, nonzeroLocus (sk k) = ⊤ :=
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  let A' : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin N) ℂ := fun τ =>
    c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)
  have hnz := _root_.GlobalTheory.FubiniStudyFrame.noCommonZero_comb K V m N X p g u b c A hgp hrelV (fun j => (hcc j).symm) hF.herm
  have hcU : ∀ τ : 𝓞 K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A' ((starRingEnd ℂ).comp τ) = (A' τ).map (starRingEnd ℂ) * U := by
    intro τ
    obtain ⟨U, hU, eU⟩ := _root_.GlobalTheory.ConjUnitary.conj_frame_unitary K N A hF.conj hF.herm (OfLattice.extEmb τ)
    have he : OfLattice.extEmb ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (OfLattice.extEmb τ) :=
      OfLattice.extEmb_eq (by rw [RingHom.comp_assoc, OfLattice.extEmb_comp])
    refine ⟨U, hU, ?_⟩
    simp only [A', he, eU, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
    rfl
  let L : HermLB p := OfLattice.combHerm hB sk A' hnz hcU
  refine ⟨X, inferInstance, p, L, ψ, s, har, hnorm, hbij, hbase, ?_, ?_, ?_⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k, y k ≠ 0 := by
      by_contra! h; exact hy0 (funext h)
    intro x x' i h
    have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
    have ha : ψ (y k₀) * fnOf _ h ((s x).f i) = ψ (ev x) * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x) k₀ i h
      rwa [← hev, hcoef] at this
    have hb : ψ (y k₀) * fnOf _ h ((s x').f i) = ψ (ev x') * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x') k₀ i h
      rwa [← hev, hcoef] at this
    refine mul_left_cancel₀ hψ ?_
    linear_combination (ψ (ev x)) * hb - (ψ (ev x')) * ha
  · refine top_le_iff.1 ?_
    rw [← hbpf]
    exact iSup_le fun k => by
      rw [← sg k]
      exact le_iSup (fun x => nonzeroLocus (s x)) (gw k)
  · refine ⟨N, m + 1, b, w, A, c, gw, hF, fun k => rfl, fun j => (hcc j).symm, fun σ i z => ?_⟩
    have he : OfLattice.extEmb (σ.comp (algebraMap (𝓞 K) K)) = σ := OfLattice.extEmb_eq rfl
    refine (OfLattice.combWeight_φ hB sk _ (hnz _) i z).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sg k]
    simp only [A', he, Matrix.mul_apply, Matrix.map_apply, c, Matrix.of_apply]
    rfl
end GlobalTheory.ImageModel
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_admits_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  first | exact @_root_.GlobalTheory.ImageModel.exists_model_of_image | exact _root_.GlobalTheory.ImageModel.exists_model_of_image | (intros; apply _root_.GlobalTheory.ImageModel.exists_model_of_image <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulUnitMemCusp
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CuspMulUnit
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end GlobalTheory.CuspMulUnit
namespace GlobalTheory.CuspMulUnit
set_option maxHeartbeats 800000 in
theorem pow_mul_mem_cusp_of_unit : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  intro _hP D T j Y e o hY hE la f hf u _u' _t eu hu _ht _huu
  refine ⟨0, fun k _ φ _φ' _t' w hφ _ht' _hφφ _hb a n hDom hF => ?_⟩
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  by_cases hF0 : f ^ (k + 1) * (u * φ) = 0
  · rw [hF0]; exact Submodule.zero_mem _
  set R := f ^ k * (u * φ) with hR
  have hFR : f ^ (k + 1) * (u * φ) = f * R := by rw [hR, pow_succ', mul_assoc]
  have hR0 : R ≠ 0 := fun h => hF0 (by rw [hFR, h, mul_zero])
  have hfsec : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) := GlobalTheory.AllWt.cuspW_le_secZ _ hf
  have hRsec := GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ' hfsec k) (GlobalTheory.AllWt.mul_mem_secZ hu hφ)
  have hFsec' := GlobalTheory.AllWt.mul_mem_secZ hfsec hRsec
  rw [← hR, ← hFR] at hFsec'
  have hFsec : f ^ (k + 1) * (u * φ) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) (wtZ a n)) := by
    rw [GlobalTheory.AllWt.exZ_wtZ, GlobalTheory.AllWt.secZ_nat]; exact hF
  have heq := eq_of_mem_secZ hFsec hFsec' hF0
  set G : WTZ D.host.E := wtZ a n - wtOf (T.Q.Dw j) la 0 with hG
  have hexG : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) (wtZ a n) - GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 := by
    funext i; cases i <;> rfl
  have hRG : R ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (exZ (T.Q.Dw j) G) := by
    rw [hexG, heq, add_sub_cancel_left]; exact hRsec
  have hGe : Even G.2 := by
    have h2 : G.2 = (n : ℤ) := by simp [hG, wtZ, GlobalTheory.AllWt.wtOf_snd]
    rw [h2]; exact (Int.even_coe_nat n).2 hDom.2
  have hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ → G.1 (τ, j') ≤ G.1 (τ, i) := by
    have hne : ∀ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ), G.1 (τ, m + 1) ≤ G.1 (τ, m) := by
      intro τ m hm
      by_contra hlt
      push_neg at hlt
      exact hR0 (GlobalTheory.NonDomVanish.eq_zero_of_lt hRG τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt)
    intro τ i j' hij hj'
    revert hj'
    induction j', hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ m hm ih => intro hj'; exact (hne τ m hj').trans (ih (by omega))
  rw [← GlobalTheory.AllWt.cuspW_wtZ, GlobalTheory.AllWt.mem_cuspW]
  refine ⟨hFsec, fun σ hσ => ?_⟩
  have hU := hY.unf σ hσ
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hr, -⟩ := hU
    have h1 : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Formalism.BasicNotions.Ranks.r
      omega
    omega
  have hK := GlobalTheory.HSApp.VanishingBound.keySec D T j Y e o hY σ hσ
  have hfh := (GlobalTheory.AllWt.mem_cuspW.1 hf).2 σ hσ
  refine holCusp_mem_holSub _ _ fun kk => ?_
  have hRs : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) G kk) (rdU (Y.U σ) R kk) :=
    GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (Y.U σ) hK hσ hU hpq G hGe hdec R hRG kk
  have hfS := (GlobalTheory.FlatTw.mem_holSub_model _ _ _).1 hfh kk
  have hw : GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk =
      GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) kk + GlobalTheory.AllWt.modelWt (Y.U σ) G kk := by
    rw [← GlobalTheory.AllWt.modelWt_add (Y.U σ) (GlobalTheory.AllWt.even_wtOf la 0) hGe kk, hG, add_sub_cancel]
  have hsecF : ((Y.U σ).X kk).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtZ a n) kk)
      (rdU (Y.U σ) (f ^ (k + 1) * (u * φ)) kk) := by
    rw [GlobalTheory.AllWt.modelWt_wtZ]; exact hU.2.2.2.2.1 a n hDom _ hF kk
  refine GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ hsecF (GlobalTheory.CuspFrom.isModerate _ hf1 hsecF) fun ξ hξ x hx => ?_
  rw [hFR, GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, hw]
  exact fj_mul_eq_zero _ hf1 hfS hRs ξ hξ x hx
end GlobalTheory.CuspMulUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), ∀ f ∈ Y.V (wtOf _ la 0), ∀ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F) (eu : Ix (T.Q.Dw j) → ℤ), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ eu → t ≠ 0 → u * u' = t • 1 → ∃ K : ℕ, ∀ k, K ≤ k → ∀ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t' : Y.d.c₂.F) (w : GlobalTheory.AllWt.Weight (T.Q.Dw j)), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) w 0) → t' ≠ 0 → φ * φ' = t' • 1 → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) w 0) kk) (rdU (Y.U σ) φ kk) y ≤ C) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → f ^ (k + 1) * (u * φ) ∈ sec Y.d.Xo₂ Y.d.c₂ a n → f ^ (k + 1) * (u * φ) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n := by
  first | exact @_root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | exact _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit | (intros; apply _root_.GlobalTheory.CuspMulUnit.pow_mul_mem_cusp_of_unit <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerIsoFlagTangentPsiSet
section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
theorem kodaira_spencer_iso_flag_tangent_psi_set : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := _root_.GlobalTheory.T.kodaira_spencer_universal_family hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => _root_.GlobalTheory.T.flag_deformations_eq_of_kodaira_spencer_eq hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩
end GlobalTheory.FlagTan
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightComparisonOfDegreeBound
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem PositivityTheory.Xj7N.weil_height_comparison_of_degree_bound (hA : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ) : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t) := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw σ y k hy hr
  exact ChowFormHeightComparison₂.GenericDenseBound.norm_le_of_emb hM (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) (8 * i) t
    (fun N m b g A hF σ' ρ hρ => hA hP D T j Y e o hY hE Z u t hGood hBir hNB hdg N m b g A hF σ' ρ hρ
      (8 * i) (by omega) f hf) w hw σ y k hy hr
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightInequality
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open PositivityTheory.UnitarySelfGeneration.UnitProductCombination
theorem PositivityTheory.UnitarySelfGeneration.weil_height_inequality : PositivityTheory.UnitarySelfGeneration.ChowFormHeight → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
  intro HP hP K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s t a _ _ _ _ hW hG hd hM ha
  obtain ⟨pt, h1, h2, h3, h4⟩ := exists_pt p ψ hM.bij hM.base
  have := GlobalTheory.CommonModel.isProper_of_isProjOver hM.arith.isProjOver
  let M : GlobalTheory.ZH.RatModel (𝓞 K) Ω :=
    { Z := X, s := p, sep := inferInstance, lft := inferInstance, qc := inferInstance, pt := pt, pt_s := h1,
      gen := h2, onto := h3 }
  obtain ⟨N, n, b, g, A, c, gw, hF, hgw, hcb, hφ⟩ := hM.fs
  obtain ⟨Mt, hdet, hcc, hMt⟩ := PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat K V Nm W N n b g A hF
  obtain ⟨e, he, hv, hs, hdiv⟩ := gen_all M L.B L.isLB ev W s
    (fun w w' i hi => by
      obtain ⟨z, hz⟩ := hi
      have hg := GlobalTheory.Cartier.gen_mem (X := X) hz
      refine hM.bij.1 ?_
      rw [map_mul, map_mul]
      exact (congrArg _ (h4 _ hg _)).trans ((hM.ratio w w' i hg).trans (congrArg _ (h4 _ hg _).symm)))
    hM.bpf hG.1 hW gw (by simp only [hgw]; exact hF.span)
  have h5 := _root_.PositivityTheory.UnitarySelfGeneration.volume_le_self_intersection HP hP K V Ω Nm W ev D N n b g A t hF hG hd M (by simpa only [hgw] using hdiv)
    hM.arith L.B L.isLB e he (fun k => s (gw k)) (fun k => hgw k ▸ hv (gw k)) hs Mt hdet hcc hMt
  have h6 := (isometric_fs M L ev s hv hW b g A c gw hgw hcb hφ hs Mt hdet hcc hMt t).isSelfInter hM.arith h5
  rw [ha.unique hM.arith h6]
  exact le_of_eq (by ring)
end
end

