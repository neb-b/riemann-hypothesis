module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXHeadFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbEquiv2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0250
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0260
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0264
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0251
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0194
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteZeroMatrixEntry
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialWaveOrbital
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0227
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPEOm
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

private theorem continuousAt_w1_of_ne_zero (k r : ℕ) (l : Fin r) {c : ℂ} (hc : c ≠ 0) :
    ContinuousAt (w1 k r l) c := by
  refine continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => ?_
  show ContinuousAt (fun c => w1 k r l c p q) c
  simp only [w1]
  split_ifs
  · exact continuousAt_id
  · exact (continuous_star.continuousAt).inv₀ (star_ne_zero.mpr hc)
  · exact continuousAt_const
  · exact continuousAt_const
private theorem continuousAt_wCell_fst_of_mem_OmX (k r : ℕ) (x : (Fin r → ℂ) × Mx k r) (hx : x.1 ∈ OmX r)
    (i : Fin (r + 1)) : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => wCell k r i y.1) x := by
  induction i using Fin.induction with
  | zero =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_zero]
    exact continuousAt_const
  | succ l ih =>
    simp only [Formalism.FourierDecayAlt.P.Qx6.wCell_succ]
    refine ih.mul ?_
    have hf : ContinuousAt (fun y : (Fin r → ℂ) × Mx k r => y.1 l) x := by fun_prop
    exact (continuousAt_w1_of_ne_zero k r l (hx l)).comp (f := fun y : (Fin r → ℂ) × Mx k r => y.1 l) hf

theorem spectral_pairing_big_cell : RDSPEOm := by
  intro k r Wp Wq _ _ _ _ _ _ D
  have hmem : ∀ x ∈ DomR k r D.z D.z', eR k r x ∈ JF.Om k r D.z D.z' := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact Formalism.FourierDecayAlt.P.TLB.wCell_gv (Pa := M.Par.mk k r 0 0 0 0) D hx
    · exact Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  refine ⟨hmem, ?_, ?_⟩
  · intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_wCell_fst_of_mem_OmX k r x hx.1 (Fin.last r)).mul continuous_snd.continuousAt
  · intro g hg
    exact ⟨hg.1, hg.2.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPExh
section
open MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_exhaustion : RDSPExh := by
  intro k r Wp Wq _ _ _ _ _ _ D X hX C hC hCO
  have hX' : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
    rwa [rdb_ffl_om_eq] at hX
  have hqC : IsCompact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C) :=
    hC.image_of_continuousOn ((Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_contOn D.z D.z').mono fun g hg => (hCO hg).2)
  have hqQ : Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C ⊆ JF.QDom k r D.z D.z' := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D (hCO hg)).choose_spec.2.1
  obtain ⟨K', hK'c, hCK', hK'Q⟩ := exists_compact_between hqC (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hqQ
  obtain ⟨φ, hφ, ⟨C', hC'c, hC'O, hC'φ⟩, hint⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.average_one_cutoff_on_orbits k r Wp Wq D K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C' := by
    refine closure_minimal (fun g hg => ?_) hC'c.isClosed
    by_contra hgC
    exact hg (by simp [hC'φ g hgC])
  refine ⟨fun g => φ g • X g,
    Q.OmPlus k r D.z D.z' ∩ Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' ⁻¹' interior K', ?_, ?_, ?_,
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.isOpen_qOf D.z D.z' isOpen_interior, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨C'ᶜ, fun _ => 0, hC'c.isClosed.isOpen_compl, fun h => hO (hC'O h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hC'φ g hg]
  · exact hC'c.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · exact hsuppC.trans hC'O
  · intro g hg
    exact ⟨(hCO hg).2, hCK' ⟨g, hg, rfl⟩⟩
  · intro p hp g hg hs
    refine ⟨hg.2, ?_⟩
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2 ⊢
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_sgs D hp] at h2
  · intro g hg
    have hJ : B.JF D (fun g => φ g • X g) g = (∫ p, φ (B.sgs p g) ∂D.μSS) • X g := by
      change ∫ p, JF.xiP D p • B.rho D p (fun g => φ g • X g) g ∂D.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hr : B.rho D p (fun g => φ g • X g) g = φ (B.sgs p g) • B.rho D p X g := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, Formalism.FourierDecayAlt.P.CutMP.JA.SA.eqv_of_FFl D X hX' hp hg]
    refine ⟨fun hgU => ?_, fun h0 => by rw [hJ, h0, smul_zero]⟩
    obtain ⟨p₀, hp₀, -, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
    have h1 := hint p₀ hp₀ _ (interior_subset hgU.2)
    rw [← hge] at h1
    rw [hJ, h1, one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPIpSwap
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_pairing_inner_swap : RDSPIpSwap := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ Φ Ψ c
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _))
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) with he
  have happ : ∀ (c' : Cf r 0) (l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}), e c' l.1 = c' l := by
    intro c' l
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℂ)
      (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) c' l
  have hglue : ∀ c' : Cf r 0, glue 0 c c' = e c' := fun c' => funext fun l => by
    simp only [glue]
    rw [dite_eq_left (show ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) from Nat.zero_le _)]
    exact (happ c' ⟨l, Nat.zero_le _⟩).symm
  have hprod : ∀ c' : Cf r 0,
      (∏ l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}, ‖c' l‖ ^ (-2 : ℤ)) = ∏ l : Fin r, (‖e c' l‖ ^ 2)⁻¹ := by
    intro c'
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)) _ _ (fun l => ?_)
    show ‖c' l‖ ^ (-2 : ℤ) = (‖e c' l.1‖ ^ 2)⁻¹
    rw [happ c' l, zpow_neg]
    norm_cast
  unfold radIp LocFacts₂ pairAt dxc
  simp only [B.hsInner]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← hmp.integral_comp']
  refine integral_congr_ae (ae_of_all _ fun c' => ?_)
  simp only
  rw [hglue c', ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => by positivity), Complex.real_smul, hprod c']

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPJFMem
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPZeroR
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_zero_right : RDSPZeroR := by
  intro k r Wp Wq _ _ _ _ _ _ D X Y hX hY hxy g hg
  obtain ⟨p, hp, hq, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
  set q := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' g with hqdef
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨x, hxD, w, hw, hres⟩ := radial_group_residue k r Wp Wq D q hq
  have hxe : X (B.gq D q) = Y (B.gq D q) := by
    have e := rdsp_resG_congr X Y x (hxy x hxD)
    rw [hres X hX, hres Y hY] at e
    exact smul_right_injective _ hw e
  have hD : ∀ y ∈ JF.Om k r D.z D.z', y ∈ Q.Glev k r 0 ∩ JF.Om k r D.z D.z' := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  rw [hge]
  exact Formalism.FourierDecayAlt.P.CutMP.JA.LT.agree_sgs D X Y
    (fun y hy n hn => hX.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hX.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hX.2.2.2 y (hD y hy) h hh h' hh')
    (fun y hy n hn => hY.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hY.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hY.2.2.2 y (hD y hy) h hh h' hh')
    hp hgq hxe

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ F g = 0 := by
  intro g hg hgO
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO T.word_lie hz g hg hgO, map_zero]

theorem rdsp_adjFn_vanish (T : B.DTerm k r Wp Wq) {O : Set (B.Mat k r)}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → ap T.coefAdj F g = 0 := by
  intro g hg hgO
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
  rw [hz g hg hgO, map_zero]

theorem rdsp_lie_rev (T : B.DTerm k r Wp Wq) : ∀ X ∈ T.word.reverse, inLie k r X := by
  intro X hX
  exact T.word_lie X (List.mem_reverse.mp hX)

theorem rdsp_opAdj_eq (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opAdj Θ F = fun g => (Θ.map fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g).sum := rfl

theorem rdsp_opAdj_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ F g = 0 := by
  intro g hg hgO
  rw [rdsp_opAdj_eq]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO (rdsp_lie_rev T) (rdsp_adjFn_vanish T hz) g hg hgO, smul_zero]

theorem rdsp_opAdj_cc (Θ : B.DiffOp k r Wp Wq) (d : ℝ) (hG : CutMP.GlobCoef Θ d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (A : ℝ) (hFA : ∀ m : ℕ, B.InCC (A + d) m F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ ∀ m : ℕ, B.InCC A m (B.opAdj Θ F) := by
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hz0 : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) → F g = 0 := fun g _ hg => by simp at hg
  have hapck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coefAdj F) := fun T hT =>
    Pr.ck hO hcov ⟨(hG T hT).2.1, hF, hz0⟩
  have hRck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word.reverse (ap T.coefAdj F)) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) (rdsp_lie_rev T) x (by simpa [wL] using hx))
    simpa using hapck T hT
  have hapcc : ∀ T ∈ Θ, ∀ m : ℕ, B.InCC A m (ap T.coefAdj F) := by
    intro T hT m
    obtain ⟨hc1, hc2, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ := hFA m
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc2)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).2) hc hz0⟩
  rw [rdsp_opAdj_eq]
  refine ⟨?_, fun m => ?_⟩
  · clear hapcc
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) :=
        CkOn_smul _ (hRck T (by simp))
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hapck S (by simp [hS]))
        (fun S hS => hRck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · refine InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) ?_
    intro T hT
    obtain ⟨c, hc⟩ : B.InCC A m (B.Rw T.word.reverse (ap T.coefAdj F)) :=
      InCC_Rw (rdsp_lie_rev T) (hapcc T hT _)
    exact ⟨_, CCle_smul _ hc⟩

end

theorem spectral_polynomial_property : RDSPolyProp := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ hC
  obtain ⟨hS, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  refine ⟨hS _, hC, fun ε _ => ⟨κ, hκ, fun T hT => ?_⟩, fun F hF => ?_⟩
  · obtain ⟨-, -, hb⟩ := hG T hT
    obtain ⟨Cb, hCb⟩ := hb (B.opOrder Θ + 5)
    exact ⟨Cb, fun u v hu hv hl g hg _ => hCb u v hu hv hl g hg⟩
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    have := hFs g hg hne
    exact absurd hgO (not_lt.2 this)
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbHeadTopOfMkTop
section
namespace Formalism.FourierDecayAlt.P

theorem pb_exhPic_of_mkTop (hMk : CutEX.MkTop) : PBI.ExhPic :=
  CutEX.exhPic_of_leaves CutEX.exceptional_assumption_holds unipotent_weight_top slice_top_exhaustion pullback_smooth
    pullback_right_action pullback_support pullback_equivalence hMk compact_truncation_construction top_point_existence
    determinant_exceptional_holds head_family_exhaustion radial_slice_top radial_of_function_exceptional radial_extension_exceptional
    residue_top_exceptional_level frame_parameter_regularity (pb_radWordSliceOfHeadPic head_picture) level_zero_picture_of_slice

theorem pb_headTop_of_mkTop (hMk : CutEX.MkTop) : KB.HeadTop :=
  pb_headTop_of top_unipotent_integral (pb_exhPic_of_mkTop hMk)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfSpectralData
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_identity_of_spectral_data : RDRadIdOfSpec :=
  rDRadIdOfSpec_of_grpId_theta
    (rDGrpIdOfSpec_of_radIdAlg (rDRadIdAlg_of_collapse_gauge_rearr radial_collapse radial_gauge_identity radial_rearrangement)
      radial_start_coordinates radial_wave_radial Formalism.FourierDecayAlt.P5.waveCExists radial_residue_formula radial_wave_function_field radial_operator_function_field radial_group_residue)
    (Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds)
    radial_orbital_niceness radial_wave_orbital radial_operator_locality

theorem radDecay_of_spec (h : RDIdentSpec) : RadDecay :=
  radDecay_of_ABQ (rDIdentABQ_of_spec h radial_identity_of_spectral_data)

end Formalism.FourierDecayAlt.P.CutSE
end

