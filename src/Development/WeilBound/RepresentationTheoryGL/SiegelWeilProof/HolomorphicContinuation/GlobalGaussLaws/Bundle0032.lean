module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0031
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add (f := _), psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add (f := _), finPart_insT, finPart_insT, finPart_insT, add_zero]

theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]


set_option synthInstance.maxHeartbeats 400000 in
def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add (f := _)]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DHol
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open DHolH

theorem dHol : DHol := by
  intro hP D n V hn hr θ hθ ν hν P _ _ U hU φ h1 h2 h3 h4 h5
  intro F

  have hfacts : ∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      Continuous M ∧ absThetaInt V ν M < ⊤ ∧ ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N, M, hN, hM, hb⟩ := h5 p₀ z₀ hz₀
    obtain ⟨hMc, hMf⟩ := sch_facts hP V hn hr θ hθ ν hν hM
    exact ⟨N, M, hN, hMc, hMf, hb⟩
  have hcontx : ∀ p, ∀ z ∈ U, Continuous (φ p z) := by
    intro p z hz
    exact (h4 p).comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩
  have hfin : ∀ p, ∀ z ∈ U, absThetaInt V ν (φ p z) < ⊤ := by
    intro p z hz
    obtain ⟨N, M, hN, -, hMf, hb⟩ := hfacts p z hz
    exact lt_of_le_of_lt (absThetaInt_mono V ν (hb (p, z) (mem_of_mem_nhds hN) hz)) hMf
  have hmeas : ∀ p, ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (φ p z))) (autMeasure V ν) :=
    fun p z hz => aestronglyMeasurable_thS V ν (hcontx p z hz) (hfin p z hz)
  have hfam : ∀ p, Fam V ν U (φ p) := by
    intro p
    refine ⟨h2 p, fun z₀ hz₀ => ?_, hmeas p⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p z₀ hz₀
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hv
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂, M, hMc, hMf, ?_⟩
    intro z hz x
    have hzv : z ∈ v := hb₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hzU : z ∈ U := hb₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hb (p, z) (huv ⟨mem_of_mem_nhds hu, hzv⟩) hzU x
  refine ⟨?_, fun p => ?_, fun p r z hz => ?_⟩
  ·
    rintro ⟨p₀, z₀⟩ ⟨-, hz₀⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p₀ z₀ hz₀
    have hfinq := ae_absTheta_lt V ν hMc hMf
    have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
      intro q hq
      refine Summable.of_enorm ?_
      simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
    have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ =
          (descend (GQ V) (absTheta V M) q).toReal := by
      intro q hq
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
      rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
      simp
    have hs : Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := self_mem_nhdsWithin
    have hNs : N ∩ Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := inter_mem (mem_nhdsWithin_of_mem_nhds hN) hs
    have hint : ContinuousWithinAt (fun pz : P × ℂ => ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν)
        (Set.univ ×ˢ U) (p₀, z₀) := by
      refine continuousWithinAt_of_dominated (bound := fun q => (descend (GQ V) (absTheta V M) q).toReal) ?_ ?_
        (integrable_absTheta_toReal V ν hMc hMf) ?_
      · exact Eventually.mono hs fun pz hpz => hmeas pz.1 pz.2 hpz.2
      · refine Eventually.mono hNs fun pz hpz => ?_
        filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hs' : Summable fun ξ => ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
        calc ‖∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
          _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ := hs'.tsum_le_tsum (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
          _ = _ := htsM q hq
      · filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hon : ContinuousOn (fun pz : P × ℂ => ∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)) (N ∩ Set.univ ×ˢ U) :=
          continuousOn_tsum (fun ξ => (h3 _).mono Set.inter_subset_right) hs1
            (fun ξ pz hpz => hb pz hpz.1 hpz.2.2 _)
        exact (hon.continuousWithinAt ⟨mem_of_mem_nhds hN, ⟨Set.mem_univ _, hz₀⟩⟩).mono_of_mem_nhdsWithin hNs
    have : (fun pz : P × ℂ => F pz.1 pz.2) = fun pz => ((autMeasure V ν) Set.univ).toReal⁻¹ •
        ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν := by
      funext pz
      simp only [F, average_eq]
      rfl
    rw [this]
    exact hint.const_smul ((autMeasure V ν) Set.univ).toReal⁻¹
  · exact differentiableOn_avg V ν hU (hfam p)
  · exact iteratedDeriv_avg V ν hU (hfam p) r z hz

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLawOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem compAt_zero' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j
  simp [compAt]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} : compAt θ τ (1 : Mx D n n) = 1 := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem compAt_J (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} :
    compAt θ τ (blk4 (0 : Mx D n n) 1 (-1) 0) = blk4 0 1 (-1) 0 := by
  rw [component_block_matrix, GlobalTheory.RealParamSize.compAt_neg, compAt_zero', compAt_one']

theorem fin_J {n : ℕ} : (blk4 (0 : Mx D n n) 1 (-1) 0).map (finPart D) = blk4 0 1 (-1) 0 := by
  rw [finite_part_block_matrix, Matrix.map_neg _ (map_neg (finPart D)), Matrix.map_zero _ (map_zero (finPart D)),
    Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))]

theorem iota_conj {θ : InfFam D} {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n} (hθ : IsInfFam θ)
    (hι : IsPlaceEmb θ τ ι) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (y yn : GR n) (c : Matrix (Fin n) (Fin n) ℂ)
    (hyc : mR y = nbar c) (hyn : mR yn = nU (-c)) : ι yn = w⁻¹ * ι y * w := by
  apply g_ext
  have hm : mat (w⁻¹ * ι y * w) = mat w⁻¹ * mat (ι y) * mat w := rfl
  rw [hm, mat_inv_w w hw, hw]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 yn).2.2, (hι.2 y).2.2, Matrix.map_neg _ (map_neg (finPart D)), fin_J, mul_one,
      neg_mul, jsq, neg_neg]
  · intro τ'
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.RealParamSize.compAt_neg, compAt_J]
    by_cases h : τ' = τ
    · subst h
      rw [(hι.2 yn).1, (hι.2 y).1, hyn, hyc]
      change blk4 1 (-c) 0 1 = -blk4 0 1 (-1) 0 * blk4 1 0 c 1 * blk4 0 1 (-1) 0
      rw [neg_block_matrix, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul]
      simp
    · rw [(hι.2 yn).2.1 τ' h, (hι.2 y).2.1 τ' h, mul_one, neg_mul, jsq, neg_neg]

end PositivityTheory.Rg.Sw.Glob.OG
end
end

