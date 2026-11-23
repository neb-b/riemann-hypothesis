module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstIffSecondAndResiduals

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
section
noncomputable section

namespace GlobalTheory.VolPairExists

section Vol

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix Topology
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def stab (V : HSp D) : Subgroup (GA D V) where
  carrier := {h : GA D V | ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
    (finMat D.sp.cm.sig V.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)}
  one_mem' := fun y => by
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, map_one, Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, GlobalTheory.SmoothForms.RealPts.finMat_eq V, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem mem_stab_of_real (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) : a ∈ stab V := fun y => by
  have ha' : finHom V a = 1 := ha
  rw [GlobalTheory.SmoothForms.RealPts.finMat_eq V, ha', Units.val_one, Matrix.one_mulVec]

theorem exists_volMeas (V : HSp D) (hs : V.SigOK) :
    ∃ μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun ρ => θ₀ (tauE D ρ)
  have hθ : IsInfFam θ := fun ρ => hθ₀ _
  have hsp := (GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1
  have hc : ∀ ρ, Continuous fun h => infMat D.sp.cm.sig V.gram (θ ρ) h := fun ρ => (hsp (tauE D ρ)).2.2.2.1
  have hmul : ∀ ρ g h, infMat D.sp.cm.sig V.gram (θ ρ) (g * h) =
      infMat D.sp.cm.sig V.gram (θ ρ) g * infMat D.sp.cm.sig V.gram (θ ρ) h := fun ρ => (hsp (tauE D ρ)).2.1
  have hu : ∀ ρ h, (infMat D.sp.cm.sig V.gram (θ ρ) h)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) h =
      gramAt D V ρ := fun ρ h => (GlobalTheory.Member.Arch.unit_iff _ _ _).1 ((hsp (tauE D ρ)).2.2.2.2 h)
  choose A L hA hl hr using fun ρ => exists_frame (hs (tauE D ρ))
  choose ψ hψ hψm using fun ρ => exists_hom _ (hc ρ) (hmul ρ) (hu ρ) (hA ρ) (hl ρ) (hr ρ)
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : ∀ P Q, IsTopologicalGroup (UpqT P Q) := fun P Q => inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  have : ∀ P Q, BorelSpace (UpqT P Q) := fun P Q => ⟨rfl⟩
  have : ∀ P Q, LocallyCompactSpace (UpqT P Q) := fun P Q =>
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : ∀ P Q, SecondCountableTopology (UpqT P Q) := fun P Q =>
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  have := D.cd.haar
  have := fun P Q => GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q (D.cd.cd P Q) (D.cd.haar P Q)
  have hback : ∀ ρ h, infMat D.sp.cm.sig V.gram (θ ρ) h = L ρ * UpqT.mat (ψ ρ h) * A ρ := fun ρ h => by
    rw [hψm]
    simp only [← Matrix.mul_assoc, hl, Matrix.one_mul]
    rw [Matrix.mul_assoc, hl, Matrix.mul_one]
  obtain ⟨μ, hμ, hμs⟩ := exists_haar_image (stab V) (_root_.GlobalTheory.StabOpen.isOpen_stab_latHat D V)
    (Measure.pi fun ρ => D.cd.cd (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) (MonoidHom.pi ψ)
    (continuous_pi hψ) (fun t => by
      obtain ⟨g, hg, hgu⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ => L ρ * UpqT.mat (t ρ) * A ρ)
        (fun ρ => conj_unitary_back (hA ρ) (hr ρ) (t ρ))
      refine ⟨g, mem_stab_of_real V hg, funext fun ρ => mat_injective ?_⟩
      show UpqT.mat (ψ ρ g) = _
      rw [hψm, hgu]
      simp only [← Matrix.mul_assoc, hr, Matrix.one_mul]
      rw [Matrix.mul_assoc, hr, Matrix.mul_one])
    (fun t => by
      let f : (∀ ρ, UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → ℝ :=
        fun s => ∑ ρ, ∑ i, ∑ j, ‖(L ρ * UpqT.mat (s ρ) * A ρ) i j‖
      have hf : Continuous f := continuous_finsetSum _ fun ρ _ => continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => (((continuous_const.matrix_mul
          (continuous_mat.comp (continuous_apply ρ))).matrix_mul continuous_const).matrix_elem i j).norm
      obtain ⟨K, hK, hKm⟩ := _root_.GlobalTheory.StabCompact.exists_compact_stab D V θ hθ (f t + 1)
      refine ⟨{s | f s < f t + 1}, (isOpen_lt hf continuous_const).mem_nhds (lt_add_one (f t)), K, hK, fun h hh => ?_⟩
      refine hKm h hh.1 fun ρ i j => le_trans ?_ (le_of_lt hh.2)
      rw [hback]
      refine le_trans ?_ (Finset.single_le_sum (f := fun ρ => ∑ i, ∑ j, ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ ρ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖(L ρ * UpqT.mat (ψ ρ h) * A ρ) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ j))
  refine ⟨μ, hμ, ⟨θ, hθ⟩, fun θ' hθ' => ?_⟩
  obtain rfl : θ = θ' := (GlobalTheory.SmoothForms.RealPts.realPoints D).1 _ _ hθ hθ'
  refine ⟨⟨A, hA⟩, fun A' hA' B hB => ?_⟩
  let u := fun ρ => mkU (A' ρ * L ρ) (change_unitary (hA ρ) (hr ρ) (hA' ρ))
  have hm : ∀ ρ, MeasurableSet ((fun b => b * (u ρ)⁻¹) ⁻¹' ((fun b => u ρ * b) ⁻¹' B ρ)) := fun ρ =>
    measurable_mul_const _ (measurable_const_mul _ (hB ρ))
  have h1 := hμs _ (MeasurableSet.univ_pi hm)
  rw [Measure.pi_pi] at h1
  simp only [measure_preimage_mul_right, measure_preimage_mul] at h1
  rw [← h1]
  congr 1
  ext h
  refine and_comm.trans (and_congr ?_ Iff.rfl)
  rw [Set.mem_preimage, Set.mem_univ_pi]
  exact forall_congr' fun ρ => read_iff (hl ρ) (hr ρ) (u ρ) rfl (ψ ρ h) (hψm ρ h) (B ρ)

theorem exists_volPair (V : HSp D) (hs : V.SigOK) :
    ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  obtain ⟨μ, hμ⟩ := exists_volMeas V hs
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := _root_.GlobalTheory.RationalDiscrete.discreteTopology_GQ D V
  obtain ⟨F, -, -, hF⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GQ V)
  exact ⟨(μ, F), hμ, hF μ⟩

end Vol

section Main

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem sum_toLp_ae {α : Type} [MeasurableSpace α] (μ : Measure α) {m : ℕ} (φ : Fin m → α → ℂ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (g : Fin m → ℂ) (s : Finset (Fin m)) :
    ((∑ i ∈ s, g i • (hφ i).toLp (φ i) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] ∑ i ∈ s, g i • φ i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact Lp.coeFn_zero ℂ 2 μ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.add ?_ ih)
    exact (Lp.coeFn_smul _ _).trans (((hφ i).coeFn_toLp).const_smul (g i))

-- Use the same module instance as the cuspidal L² constructions.
attribute [local instance 2000] Submodule.module

set_option maxHeartbeats 1000000 in
theorem phiJ_linearIndependent {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (b : Fin m → T.cuspA j a n)
    (hb : LinearIndependent T.Q.c.F b) : LinearIndependent ℂ fun i => T.phiJ j σ a (b i : T.R j) := by
  have hU : IsUnf (T.U j σ) := h.unf j hj σ hσ
  have hli : LinearIndependent T.Q.c.F (fun i => (b i : T.R j)) :=
    hb.map' (T.cuspA j a n).subtype (Submodule.ker_subtype _)
  have h1 := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) a n).1 m
    (fun i => (b i : T.R j)) (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (b i).2) hli
  replace h1 : LinearIndependent ℂ fun i => rdU (T.U j σ) (b i : T.R j) := h1
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro w hw
  refine h1 w ?_
  obtain ⟨th, hr, -, hd⟩ := h.dictU j hj σ hσ
  have hmem : (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) ∈ holSub (T.U j σ).X (laU (T.U j σ) a n) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (((mem_cusp _ _ _ a n _).1 (b i).2).2 σ hσ)
  have hEq := eqv_holSub (T.U j σ).X _ hmem
  have hz : ∀ g, (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) (T.dict j σ g).1 (T.dict j σ g).2 = 0 := by
    intro g
    have e := congrFun hw g
    have e2 : (∑ i, w i • T.phiJ j σ a (b i : T.R j)) g =
        ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) *
          (∑ i, w i • rdU (T.U j σ) (b i : T.R j)) (T.dict j σ g).1 (T.dict j σ g).2 := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CoreJ.phiJ, adel_muPin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2] at e
    refine (mul_eq_zero.1 e).resolve_left (mul_ne_zero ?_ (mul_ne_zero ?_ ?_))
    · exact_mod_cast (lieFac_pos _ _ _).ne'
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  funext k x
  by_cases hx : x ∈ ((T.U j σ).X k).dom
  · obtain ⟨g, γ, hγ, c, hc, hg⟩ := hd.2.2.2.2.1 k x hx
    have hdom := hd.2.2.2.1 g
    have h0 := hz g
    rw [hg] at h0 hdom
    exact eq_zero_of_orbit _ _ _ (hEq.1 k) (hEq.2 k) hx hγ hc hdom h0
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : rdU (T.U j σ) (b i : T.R j) k x = 0 := by
      classical
      exact dite_eq_right hx
    rw [this, mul_zero]


set_option maxHeartbeats 1000000 in
theorem adelic_linearIndependent : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), (∀ (m : ℕ) (b : Fin m → T.cuspA j a n), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun i => T.phiJ j σ a (b i : T.R j)) ∧ JInj (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (h.cuspidalL2Subspace j hj σ hσ a n hD) := by
  intro D T h j hj σ hσ a n hD
  refine ⟨phiJ_linearIndependent T h j hj σ hσ a n, fun m b hb => ?_⟩
  have h1 := phiJ_linearIndependent T h j hj σ hσ a n m b hb
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro w hw
  refine h1 w ?_
  have hs : (T.V j σ).SigOK := by rw [h.spaceW j hj σ hσ]; exact D.sp.W_sig j
  have hQ : QuotSupp (T.V j σ) := quotSupp_of _ (h.finVol j hj σ hσ) (exists_volPair _ hs)
  have had := fun i => _root_.GlobalTheory.AdelicCusp.phiJ_automorphic D T h j hj σ hσ a n hD (b i) (b i).2
  have hae := sum_toLp_ae (muQ1 (T.V j σ))
    (fun i => jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i))
    (fun i => h.cuspidalL2Subspace j hj σ hσ a n hD (b i)) w Finset.univ
  have hae2 : (∑ i, w i • jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) =ᵐ[muQ1 (T.V j σ)] 0 := by
    refine hae.symm.trans ?_
    have hw' : (∑ i, w i • (h.cuspidalL2Subspace j hj σ hσ a n hD (b i)).toLp
      (jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) : Lp ℂ 2 (muQ1 (T.V j σ))) = 0 := hw
    rw [hw']
    exact Lp.coeFn_zero ℂ 2 _
  funext g
  refine hQ _ ?_ (fun γ hγ g => ?_) ?_ g
  · rw [show (∑ i, w i • T.phiJ j σ a (b i : T.R j)) = fun g => ∑ i, w i * T.phiJ j σ a (b i : T.R j) g from
      funext fun g => by simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (had i).2.2.1
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [(had i).1 γ hγ g]
  · filter_upwards [hae2] with q hq
    have e : onQ (T.V j σ) (∑ i, w i • T.phiJ j σ a (b i : T.R j)) q =
        ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.cE j σ (T.dict j σ q.out).1) *
          (∑ i, w i • jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i)) q := by
      show (∑ i, w i • T.phiJ j σ a (b i : T.R j)) q.out = _
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CoreJ.phiJ, adel_muPin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show jFn (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (b i) q =
        T.mu j σ q.out * rdU (T.U j σ) (b i : T.R j) (T.dict j σ q.out).1 (T.dict j σ q.out).2 from rfl]
      ring
    rw [e, hq]
    exact mul_zero _

end Main

end GlobalTheory.VolPairExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.BcExAll
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.FramedBaseChange

theorem bcEx_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ σ : c.F →+* ℂ, BCEx Xo c σ :=
  fun E _ _ _ H Dw l Xo c σ p y ψ =>
    exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R (CAt σ) ψ y

end GlobalTheory.FramedBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem index_eq_of_marked_isometry {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0)
    (hty : IsTypeFn H Dw.p Dw.q ty) (k k' : Fin F.n) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La)
    (hEF : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b)
    (hM : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F.t k' a + l.M • x)
    (hA : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x) : k = k' := by
  obtain ⟨-, P', hP'⟩ := GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty
    (by rw [(F.sig k').1, (F.sig k').2]; exact hty)
  have hP := GlobalTheory.ClassUniq.isPeriod_comp_isometry gam hEF hP'
  set P := P'.comp gam.toLinearMap.toAddMonoidHom with hPdef
  refine F.disj k k' P P' hP hP' ?_
  exact (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H Dw l Xo σ' g ty
    hr hσ hty (F.Di k) (F.Di k')
    (F.t k) (F.t k') P P' (F.u k P) (F.u k' P') (F.ex k P) (F.ex k' P')
    ⟨F.over_σ k P hP, hP, ⟨F.ex_add k P hP, F.ex_onto k P hP, GlobalTheory.ClassUniq.isHolTo_ex F k P hP,
      (F.ex_diff k P hP).1, (F.ex_diff k P hP).2⟩, F.ex_ker k P hP, F.ex_lin k P hP, F.ex_weil k P hP,
      F.ex_eta k P hP, F.ex_etaA k P hP⟩
    ⟨F.over_σ k' P' hP', hP', ⟨F.ex_add k' P' hP', F.ex_onto k' P' hP', GlobalTheory.ClassUniq.isHolTo_ex F k' P' hP',
      (F.ex_diff k' P' hP').1, (F.ex_diff k' P' hP').2⟩, F.ex_ker k' P' hP', F.ex_lin k' P' hP',
      F.ex_weil k' P' hP', F.ex_eta k' P' hP', F.ex_etaA k' P' hP'⟩).2
    ⟨gam, LinearEquiv.refl ℂ _, hEF, hM, hA, fun a => rfl⟩

theorem UW.ik_injective {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (W : UW U) :
    Function.Injective W.ik := by
  obtain ⟨hr, hX, -, hfib, -⟩ := hU
  obtain ⟨g, e, F, ik, φ, hEF, hP⟩ := W
  intro k k' hk
  change ik k = ik k' at hk
  obtain ⟨x, hx⟩ := CompInj.dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := CompInj.dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := CompInj.exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2
    ψ hEF' x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := CompInj.frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨ga, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

theorem comp_eq_of_matched : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 hA W k k' hS ga hun hΛ hm
  apply W.ik_injective hσ hU h1
  have hinj : Function.Injective
      ((Matrix.toLin' (ga : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) := by
    intro u v huv
    have h : (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = (ga : Matrix (Fin r) (Fin r) E) *ᵥ v := huv
    have h2 := congrArg (fun w => ((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using h2
  let ψ : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ :=
    (Submodule.equivMapOfInjective _ hinj (U.X k).Λ).trans (LinearEquiv.ofEq _ _ hΛ)
  let gam : (W.F.Di (W.ik k)).La ≃ₗ[𝓞 E] (W.F.Di (W.ik k')).La := (W.φ k).trans (ψ.trans (W.φ k').symm)
  have hgam : ∀ a, (W.φ k' (gam a) : Fin r → E) = (ga : Matrix (Fin r) (Fin r) E) *ᵥ (W.φ k a : Fin r → E) := by
    intro a
    change (W.φ k' ((W.φ k').symm (ψ (W.φ k a))) : Fin r → E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  refine index_eq_of_marked_isometry W.F (hU.1 ▸ h1) hσ
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw W.g W.e) _ _ gam (fun a b => ?_) (fun a ha => ?_) fun a => ?_
  · have h := W.isom k' (gam a) (gam b)
    rw [hgam, hgam, ← hS.gm, ← hS.xi, hun, ← W.isom k a b] at h
    exact_mod_cast h
  · obtain ⟨w, hw, h⟩ := hm a ha
    refine ⟨(W.φ k').symm ⟨w, hw⟩, (W.φ k').injective (Subtype.ext ?_)⟩
    rw [hgam, map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
    exact h
  · exact ⟨gam (W.F.t _ a) - W.F.t _ a, by rw [hA, one_smul, add_sub_cancel]⟩

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfEqComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.NaturalValues

theorem eq_of_points {K R Ω : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] [Algebra.FiniteType K R]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] {x y : R} (h : ∀ φ : R →ₐ[K] Ω, φ x = φ y) : x = y := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  rw [← sub_eq_zero]
  have hb : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance ((Ideal.isRadical_iff_quotient_reduced _).2
      (isReduced_of_injective (RingEquiv.quotientBot R) (RingEquiv.quotientBot R).injective))
  rw [← Ideal.mem_bot, ← hb]
  refine Ideal.mem_sInf.2 fun {m} hm => ?_
  haveI := hm.2
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  let ψ : (R ⧸ m) →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have e := h (ψ.comp (Ideal.Quotient.mkₐ K m))
  rw [← sub_eq_zero, ← map_sub, AlgHom.comp_apply, map_eq_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.1 e

theorem eq_of_eq_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (u u' : ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u S y) = u T z) → (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' S y) = u' T z) → (∀ y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra, @u ℂ _ s.toAlgebra y = @u' ℂ _ s.toAlgebra y) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u S y = u' S y := by
  intro E _ _ _ H Dw l Xo c s u u' hu hu' hc S _ _ y
  have hF := GlobalTheory.RepCompare.frameLaws Xo c
  letI := s.toAlgebra
  refine eq_of_locM (K := c.F) fun m hm => ?_
  obtain ⟨A, v, cw, -, -, -, ⟨wm, h1, h2⟩, -⟩ := hF.cover S y y rfl m
  have e : u A.R v = u' A.R v := by
    refine eq_of_points (K := c.F) (Ω := ℂ) fun φ => ?_
    obtain ⟨z, hz⟩ := hF.bc _ _ φ v
    rw [hu _ _ φ v z hz, hu' _ _ φ v z hz]
    exact hc z
  rw [hu _ _ _ y wm h1, hu' _ _ _ y wm h1, ← hu _ _ cw v wm h2, ← hu' _ _ cw v wm h2, e]

end GlobalTheory.NaturalValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLattic
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.PushKeeps

theorem push_keeps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (h : Matrix (Fin n) (Fin n) E), IsUnitaryM h → (∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), pushLet c h P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) ∧ ∀ Λ : GenLat E n, (Λ.Unimod → (actLat h Λ).Unimod) ∧ Moves h Λ.La (actLat h Λ).La ∧ ccT h * h = 1 ∧ ∀ P ∈ harmL (Dw := Dw) c Λ a, pushLet c h P ∈ harmL (Dw := Dw) c (actLat h Λ) a := by
  intro E _ _ _ H Dw l c n a h hu
  refine ⟨fun P hP => ?_, fun Λ => ⟨GlobalTheory.RepCompare.unimod_act hu, fun v => ?_, hu,
    fun P hP => GlobalTheory.RepCompare.push_mem c hu hP⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hP
    exact ⟨GlobalTheory.PushHarm.push_mem_harmK E H Dw l c n h P hu h1,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).1 h2,
      (GlobalTheory.Proof.ColumnMapShift.push_rows E H Dw l c n h P fun τ i => a (τ, i)).2 h3⟩
  · have h' : adjM h * h = 1 := hu
    rw [GlobalTheory.RepCompare.mem_actLat]
    constructor
    · exact fun hv => ⟨v, hv, rfl⟩
    · rintro ⟨u, hu', e⟩
      have e' := congrArg (adjM h).mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', Matrix.one_mulVec, Matrix.one_mulVec] at e'
      exact e' ▸ hu'

end GlobalTheory.PushKeeps
end
end

