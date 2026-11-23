module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.K2Hermitian
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContractionIdentityFramesWithOperatorScalar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.DelB

theorem delPolAt_of_frames_scal : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (c : ℂ_[p]) (F g₀ : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]), letI := wittFractionAlgebraCp p; letI := algKfC E.toCEmb; FrInv fd → KapLawLt X ℂ_[p] (thFOf X pos F) → let Y := pendT X E hfin hst hLT pos F; ∀ (σ : D.what₂.LL →+* X.G.Kf) (cls : ∀ j, X.Lv.comp j → (X.Pj j).Tup → (D.chTw u μ).cls j) (cmp : ∀ j, ((ex.tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j) (κ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → (D.chTw u μ).cls (j + 1)) (ι : ℂ →+* Y.Kc) (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc) (τ : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → XspC (X.Pj (j + 1)) Y.Kc →ₗ[Y.Kc] XspC (X.Pj (j + 1)) Y.Kc) (sc : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup → Y.Kc) (sH : ∀ j, X.Lt j → X.Lt (j + 1) → Y.Kc) (sO : ∀ j, X.Lt j → Y.Kc) (Gm : ∀ j, X.Lt j → ((ex.tw.fm u μ).lat j).V → (X.Pj j).Xsp) (j : ℕ) (_ : j < X.mm) (cK : Y.Kc) (hN : RankTie X D j), (∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → F j La La' = linSub (fun x y => c * subBG E.toCEmb pos fd j La La' x y) (g₀ j La La')) → MoveH Y u μ cmp (fun j La => glInv X j (BOf fd j La)) Gm j → TieOpS (Y := Y) t u μ cls Gm sO j (eIdx X D pos j hN) (Φ₀ j) → KernelEntryDegreeCondition (Y := Y) t u μ cls j (eIdx X D pos j hN) → TieSerH Y t u μ cls κ ι (fun j La La' => resV (kapOf X pos j) (g₀ j La La')) sH j (eIdx X D pos j hN) → TieChiH Y t u μ cls κ ι sc sH (fun j La => Formalism.L2.G.Pend.cA X Y.Kc j (BOf fd j La) * sO j La) j cK → DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') τ j → DelPolAt (Y := Y) t u μ cls cmp κ (phiH D Φ₀ τ sc) (srOf Y) j cK := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ p _ X _ E hfin hst g hLT pos fd c F g₀
  intro hFr hK Y σ cls cmp κ ι Φ₀ τ sc sH sO Gm j hj cK hN hF hMv hOp hDeg hSer hChi hYEq
  intro La hLa x Q hQ c' L' hL'
  letI := Formalism.L2.G.Pend.wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  have hTh : Y.ThF j La (c', L') = Formalism.L2.G.Pend.thFOf X pos F j La (c', L') :=
    (GlobalTheory.TwU.pendT_ThF_lt_of_kapLawLt p X E hfin hst g hLT D.what₂.Tau pos F hK).1 j ‹_› La (c', L') (Y.Rep_lat j La hLa) hL'
  have hsr : srOf Y j La (c', L') = (Y.eS j La * (Y.eT j (c', L'))⁻¹ : X.G.Kf) •
      linSub (fun z y => ∑ w, VOf Y.Kc fd c j (c', L') z w * Formalism.L2.G.Pend.LkB X Y.Kc j (BOf fd j La) w y)
        (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) := by
    unfold srOf
    rw [hTh]
    congr 1
    show resV (Formalism.L2.G.Pend.kapOf X pos j) (F j La (c', L')) = _
    rw [hF La (c', L') (Y.Rep_lat j La hLa) hL']
    rw [rename_linear _ _ _ _ (kapOf_bij X pos j)]
    congr 1
    funext z y
    exact substitution_split p X D E.toCEmb pos fd _ hFr j La (c', L') z y
  obtain ⟨hMe, hG, hO⟩ := hMv La hLa x
  beta_reduce at hMe
  have hc := chain_core X Y.Kc j (VOf Y.Kc fd c j (c', L'))
    (blockDiag_VOf X Y.Kc j fd _ (c', L')) (glInv X j (BOf fd j La)) (Gm j La x) hG hO (τ j c' L')
    (hYEq c' L' hL' (Gm j La x) hG hO) (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  rw [glAt_glInv] at hc
  have hPD := pairing_dictionary p X Y.Kc j D (D.R.N j) (D.R.N (j + 1)) ι (eIdx X D pos j hN) (eIdx_injective X D pos j hN) (Φ₀ j)
    (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
    ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L'))) (sH j La (c', L'))
    (hDeg La hLa x Q hQ) (fun α hα => hSer La hLa c' L' hL' α (hDeg La hLa x Q hQ α hα))
  have hOS := pairD_lin X Y.Kc j (sO j La • LinearMap.id)
    (trDY X Y.Kc j D (eIdx X D pos j hN) (Φ₀ j) (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1))))
    (Formalism.L2.G.Pend.polDel X Y.Kc j (Gm j La x)) (fun n => hOp La hLa x Q hQ n)
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (g₀ j La (c', L')))
  show sc j c' L' • τ j c' L' (Φ₀ j (_ • pairR D (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
      ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')))) =
    cK • Formalism.L2.G.Pend.pairD X Y.Kc j (Formalism.L2.G.Pend.polDel X Y.Kc j (cmp j x La.1 La.2)) (srOf Y j La (c', L'))
  rw [hsr, Formalism.L2.G.Pend.pairD_smul_right, ← hMe, hc, hOS, hPD, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
    ← algebraMap_smul Y.Kc (Y.eS j La * (Y.eT j (c', L'))⁻¹), smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hChi La hLa c' L' hL']
  ring

end GlobalTheory.TwV.DelB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.LatDet

theorem det_isUnit_of_colSpan {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
    (hinj : Function.Injective (algebraMap W Qq)) {N : ℕ} (M : Matrix (Fin N) (Fin N) Qq)
    (h1 : ∀ i c, M i c ∈ (algebraMap W Qq).range) (h2 : ∀ i, Pi.single i (1 : Qq) ∈ colSpan W M) :
    ∃ y : Wˣ, M.det = algebraMap W Qq y := by
  choose M0' hM0 using h1
  let M0 : Matrix (Fin N) (Fin N) W := fun i c => M0' i c
  have hM : M = M0.map (algebraMap W Qq) := by
    ext i c; rw [Matrix.map_apply]; exact (hM0 i c).symm
  have h2' : ∀ i, ∃ c : Fin N → W, ∑ k, c k • (fun r => M r k) = Pi.single i (1 : Qq) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun W).1 (h2 i)
  choose C hC using h2'
  let C0 : Matrix (Fin N) (Fin N) W := fun k i => C i k
  have hMC : M * C0.map (algebraMap W Qq) = 1 := by
    ext r i
    have := congrFun (hC i) r
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    simp only [Algebra.smul_def] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h3 : ∑ k, M r k * (C0.map (algebraMap W Qq)) k i = ∑ k, algebraMap W Qq (C i k) * M r k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, mul_comm]
    rw [h3, this, Pi.single_apply]
  have h4 : (M0 * C0).map (algebraMap W Qq) = (1 : Matrix (Fin N) (Fin N) W).map (algebraMap W Qq) := by
    rw [Matrix.map_mul, ← hM, hMC, Matrix.map_one _ (map_zero _) (map_one _)]
  have h5 : M0 * C0 = 1 := by
    ext i c
    have := congrFun (congrFun h4 i) c
    exact hinj (by simpa using this)
  have h6 : M0.det * C0.det = 1 := by rw [← Matrix.det_mul, h5, Matrix.det_one]
  refine ⟨⟨M0.det, C0.det, h6, by rw [mul_comm, h6]⟩, ?_⟩
  show M.det = algebraMap W Qq M0.det
  rw [hM]
  exact (RingHom.map_det (algebraMap W Qq) M0).symm

theorem rho_int_mem {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) (x : 𝓞 E) : ρ x ∈ (algebraMap W Qq).range := by
  have hx : IsIntegral ℤ (x : E) := NumberField.RingOfIntegers.isIntegral_coe x
  have h1 : IsIntegral ℤ (ρ x) := hx.map ρ.toIntAlgHom
  have h2 : IsIntegral W (ρ x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨y, hy⟩

theorem mulVec_mem_locSp_mvL {E W Qq : Type} [Field E] [NumberField E] [StarRing E] [CommRing W] [Field Qq] [Algebra W Qq]
    (ρ : E →+* Qq) {N : ℕ} (g : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ L) : (g.1.map ρ) *ᵥ z ∈ locSp W ρ (mvL g L) := by
  let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((g.1.map ρ).mulVecLin).restrictScalars W
  have hle : locSp W ρ L ≤ (locSp W ρ (mvL g L)).comap f := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    change (g.1.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ (mvL g L)
    have h1 : (g.1.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((g.1 *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ g.1 x k).symm
    rw [h1]
    refine Submodule.subset_span ⟨g.1 *ᵥ x, ?_, rfl⟩
    exact Submodule.mem_map.2 ⟨x, hx, by simp [toLE_apply]⟩
  exact hle hz

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem locSp_std_int {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) {N : ℕ} {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))) (i : Fin N) :
    z i ∈ (algebraMap W Qq).range := by
  let P : Submodule W (Fin N → Qq) := Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap W Qq))
  have hle : locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E))) ≤ P := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩ k -
    have hk : x k ∈ (1 : Submodule (𝓞 E) E) := hx k trivial
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hk
    obtain ⟨w', hw⟩ := rho_int_mem (W := W) ρ y
    refine ⟨w', ?_⟩
    rw [Algebra.linearMap_apply, hw]
    show ρ ↑y = ρ (x k)
    rw [← hy]
  obtain ⟨w', hw⟩ := hle hz i trivial
  exact ⟨w', hw⟩

theorem det_unit_of_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] (ρ : E →+* Qq) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : IsUnit (T : W))
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb) (crd B : GL (Fin N) E)
    (hbase : mvL crd (compan (sp := sp) J a Lb) = Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))
    (hB : locSp W ρ Lb = colSpan W (B.1.map ρ)) :
    ∃ y : Wˣ, ρ (crd.1.det * B.1.det) = algebraMap W Qq y := by
  have hc := CompSp.locSp_compan_eq sp W Qq ρ J a T Lb hT hdual
  rw [hB] at hc
  let M : Matrix (Fin N) (Fin N) Qq := crd.1.map ρ * B.1.map ρ
  have hdet : ρ (crd.1.det * B.1.det) = M.det := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, Matrix.det_mul]
    rfl
  rw [hdet]
  have hcolM : ∀ c, (crd.1.map ρ) *ᵥ (fun r => (B.1.map ρ) r c) = fun r => M r c := fun c => by
    funext r
    rfl
  apply det_isUnit_of_colSpan (IsFractionRing.injective W Qq) M
  · intro i c
    have hcol : (fun r => (B.1.map ρ) r c) ∈ colSpan W (B.1.map ρ) := Submodule.subset_span ⟨c, rfl⟩
    rw [← hc] at hcol
    have h1 := mulVec_mem_locSp_mvL ρ crd _ hcol
    rw [hbase, hcolM] at h1
    exact locSp_std_int ρ h1 i
  · intro i
    have hei : Pi.single i (1 : E) ∈ Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)) := by
      intro k _
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    rw [← hbase] at hei
    obtain ⟨x, hx, hx'⟩ := Submodule.mem_map.1 hei
    have hx2 : crd.1 *ᵥ x = Pi.single i (1 : E) := by
      rw [← hx']
      simp [toLE_apply]
    have hρx : (fun k => ρ (x k)) ∈ colSpan W (B.1.map ρ) := hc ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun W).1 hρx
    unfold colSpan
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨cc, ?_⟩
    let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((crd.1.map ρ).mulVecLin).restrictScalars W
    have hf : ∀ c, f (fun r => (B.1.map ρ) r c) = fun r => M r c := hcolM
    have h3 : f (fun k => ρ (x k)) = Pi.single i (1 : Qq) := by
      show (crd.1.map ρ) *ᵥ (fun k => ρ (x k)) = _
      funext r
      have h4 := RingHom.map_mulVec ρ crd.1 x r
      rw [hx2] at h4
      rw [show (fun k => ρ (x k)) = ⇑ρ ∘ x from rfl, ← h4, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h3, ← hcc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hf]

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem latAd_one_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    latAd (1 : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb := by
  apply le_antisymm
  · rw [latAd, Submodule.span_le]
    intro x hx
    apply Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Lb hfin x
    simp only [Set.mem_setOf_eq, inv_one, Units.val_one, Matrix.one_mulVec] at hx
    exact hx
  · intro x hx
    apply Submodule.subset_span
    show _ ∈ {x | _}
    simp only [Set.mem_setOf_eq, inv_one, Units.val_one, Matrix.one_mulVec]
    exact (Submodule.subset_span ⟨x, hx, rfl⟩ : (fun i => inclE (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)

theorem crd_mul_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β B v hB
  have hbase := J.base j hj β
  unfold latCo at hbase
  rw [latAd_one_eq _ ((J.St j hj).K β).lev.Lb_fin] at hbase
  have hTe := J.tie.T_eq j hj
  have hdual := ((J.St j hj).K β).lev.Lb_dual
  have hset := ((sysS H X std).G.P.setting v)
  haveI := hset.frac_alt
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2)
  have hTu : IsUnit (((D.mem u).A.T : ℕ) : (sysS H X std).G.P.W v) := natCast_isUnit_localRing (sysS H X std) v _ hcop
  rw [← hTe] at hTu
  exact det_unit_of_base D.sp (J.rho std v) (gramN D j hj) J.a (J.St j hj).T _ hTu hdual (J.A.crd j hj) B hbase hB

end GlobalTheory.TwV.LatDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatrices
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem toLE_eq_mulVec (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ x = γ.1 *ᵥ x := rfl

theorem toStdCo_stdG_eq (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap =
      ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap ∘ₗ Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toLE co).surjective x
  have h1 : (co⁻¹ : GL (Fin N) E).1 * co.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (toLE (1 : GL (Fin N) E)) = LinearEquiv.refl E _ := by
    ext z : 1
    simp [toLE_eq_mulVec]
  have h3 : Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) (toLE co y) = toLE co (toLE γ y) := by
    rw [Matrix.toLin'_apply, toLE_eq_mulVec, toLE_eq_mulVec, toLE_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (co⁻¹).1, h1, Matrix.mul_one]
  rw [LinearMap.comp_apply, h3]
  simp [toStdCo, stdG, h2]

theorem det_toStdCo_stdG (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap).det =
      γ.1.det * (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by
  rw [toStdCo_stdG_eq, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_mul]
  have h : (co.1).det * ((co⁻¹ : GL (Fin N) E).1).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  calc _ = γ.1.det * ((co.1).det * ((co⁻¹ : GL (Fin N) E).1).det) *
        (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by ring
    _ = _ := by rw [h, mul_one]

theorem det_cT (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E) : (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_norm_of_UJ (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = G) (hγ : γ ∈ UJ σ G) : σ γ.1.det * γ.1.det = 1 := by
  have hγ' : cT σ γ.1 * G * γ.1 = G := hγ
  have hG : G.det ≠ 0 := by
    rw [← hco, Matrix.det_mul, det_cT]
    have hc : (co.1).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp co.isUnit |>.ne_zero
    exact mul_ne_zero ((map_ne_zero σ).mpr hc) hc
  have h := congrArg Matrix.det hγ'
  rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
  have h' : (σ γ.1.det * γ.1.det - 1) * G.det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hG

end Gen

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem gMat_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧
      ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk),
        (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S k hk
  have hs : ∀ y : D.host.E, (sigD D : D.host.E →+* D.host.E) y = D.host.conj y := fun y =>
    Formalism.BasicNotions.bridge_star_holds D.R D.host y
  have hco := J.pins.crd_orth k hk
  refine ⟨?_, fun γ hγ => ⟨?_, ?_⟩⟩
  · have h := GlobalTheory.TwV.cT_mul_self_toStdCo_stdG (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) 1 hco
      (Subgroup.one_mem _)
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, det_cT, Matrix.det_one, hs] at h2
    rw [mul_comm]
    exact h2
  · exact det_toStdCo_stdG _ _ _ _
  · have h := det_norm_of_UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) γ hco hγ
    rw [hs, mul_comm] at h
    exact h

end GlobalTheory.TwV.DelB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentia
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.XbEntire

theorem entire_of_pull : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a b : ℕ} (e : Matrix (Fin a) (Fin a) D.host.E) (e' : Matrix (Fin b) (Fin b) D.host.E) (Θ K : TaylorLogMetric.VC D a b → ℂ) (s : ℂ), e * star e = 1 → e' * star e' = 1 → s ≠ 0 → Differentiable ℂ K → (∀ z, K z = s * TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) e e' Θ z) → Differentiable ℂ Θ := by
  intro D cc δ a b e e' Θ K s he he' hs hK hKΘ
  have hinv : ∀ z, Θ z = s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := by
    intro z
    rw [hKΘ, ← mul_assoc, inv_mul_cancel₀ hs, one_mul, Formalism.L2.KerInert.PullbackComparison.tPullL_apply]
    show Θ z = Θ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) e e'
      (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (star e) (star e') z))
    rw [GlobalTheory.TwU.KerMove.tPull_tPull, mul_eq_one_comm.1 he, mul_eq_one_comm.1 he', GlobalTheory.TwU.KerMove.tPull_one]
  have hf : Θ = fun z => s⁻¹ * K (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e') z) := funext hinv
  rw [hf]
  exact ((hK.comp (Formalism.L2.KerInert.PullbackComparison.tPullL cc δ (star e) (star e')).differentiable).const_mul _)

end GlobalTheory.TwU.XbEntire
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.kapG_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hPos j hj c La γ g κ hr hLat hMove hFill
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  obtain ⟨hgU, -, hfr, r, hr1, hr2⟩ := hMove

  obtain ⟨-, hE⟩ := eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)
  obtain ⟨hEu, hEdet⟩ := hE g hgU
  have ha : g.1.det * D.host.conj g.1.det = 1 := by
    have h1 := congrArg Matrix.det hEu
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one, hEdet] at h1
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D]
    exact h1

  have hdet : ∀ v, (gamAt (sysS H X std) j c γ v : Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v)).det = J.rho std v g.1.det := by
    intro v
    have h1 := congrArg Matrix.det (hfr hr v)
    have hm : ((eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g).map (J.rho std v)).det = J.rho std v g.1.det := by
      rw [← hEdet]; exact (RingHom.map_det (J.rho std v) _).symm
    rw [Matrix.det_mul, Matrix.det_mul, hm] at h1
    have hu : IsUnit ((J.fd std).frM j (c, La) v).det := isUnit_det_frameMatrix_ofCharts _ _ _ j (c, La) v
    rw [mul_comm (J.rho std v _)] at h1
    exact hu.mul_left_cancel h1
  have ha0 : g.1.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at ha; exact zero_ne_one ha
  have hT0 : ∀ τ, TaylorLogMetric.embT D τ g.1.det ≠ 0 := fun τ => (map_ne_zero _).2 ha0
  have hkap := kapG_eq_char_inf D (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos j c γ
    g.1.det ha hdet

  obtain ⟨e, he, hmu⟩ := S.law.mu_rat j hj
  have hdetR : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) = ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [GlobalTheory.TwU.ratA, ratId, Formalism.UG.bc, RingHom.map_det]
  have hmuT : S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) = ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ := by
    rw [hdetR, hmu _ (by simpa using ha)]
    simp
  have hq1 : (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem_qbar D τ _) _
  have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral r).map D.what₂.embLL.toRatAlgHom
  have hχ : S.E.toCEmb.iK (algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O)) =
      TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := by
    rw [hr2, S.hK r hz]
    exact (lamC_qbar S.lam ⟨_, hz⟩).symm

  set A : ℤ := (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) with hA
  set B : ℤ := (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ) with hB
  have hfill := hFill e he
  have hq2 : (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) ∈ TaylorLogMetric.Qbar :=
    zpow_mem (prod_mem fun τ _ => embT_mem_qbar D τ _) _
  have hkey : (∏ v : (sysS H X std).Pl, ∏ s : Fin ((sysS H X std).G.P.n' v), TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) g.1.det ^ (sysS H X std).w v (j + 1) s) =
      (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) * (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) := by
    simp_rw [hfill]
    rw [← Fintype.prod_sigma (fun x => TaylorLogMetric.embT D (hT.gat_pos u w hg x) g.1.det ^ (e (hT.gat_pos u w hg x) - A - B))]
    rw [Fintype.prod_equiv (hT.gat_pos u w hg) _ (fun τ => TaylorLogMetric.embT D τ g.1.det ^ (e τ - A - B)) (fun _ => rfl)]
    rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (hT0 τ)]
    ring_nf
  have hlen : ∀ v, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La) =
      -((sysS H X std).vm v (j + 1) * ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v g.1.det)) := by
    intro v
    rw [len_smul_tup _ (sysS H X std) j c γ La hLat v, hdet v]
    ring
  refine ⟨hmuT ▸ hq1, ?_⟩
  rw [hkap, hχ, hkey, hmuT, ← hr1, Finset.sum_congr rfl fun v _ => hlen v, Finset.sum_neg_distrib,
    show -A - B = -(A + B) by ring, mul_assoc (D.what₂.embLL r), Formalism.L2.Ker.lamC_mul S.lam hz (mul_mem hq1 (by rw [show -(A + B) = -A - B by ring]; exact hq2))]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β κ g z hg
  exact (GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu t.m2 hi t.m2 hi.le β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.FramesDet.det_inFrame t.seam _ _ ((t.idx_ok μ).cst_ok.D_pos P) (hg P).2)).1
end

