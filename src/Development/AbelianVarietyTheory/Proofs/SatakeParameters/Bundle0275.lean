module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTranspor
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := _root_.GlobalTheory.TieBase.base_data t
  obtain ⟨hl, hS⟩ := _root_.GlobalTheory.BadPrimes.lev_pos_and_noConj A dtU a hP hTie
  exact _root_.GlobalTheory.TwU.SeamKer.seam_kerTh t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (_root_.GlobalTheory.TwV.adm_seam_lat_rd_pair t u μ i (i + 1) c c')
    (_root_.GlobalTheory.TwV.datLoc_classes A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelKeepsBaseCoset
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplCoset

theorem sameCoset_local {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (e₀ e D : ℕ) (c g : Sp E n ≃ₗ[E] Sp E n) (k : GLint E n P) (hc : c ∈ GLint E n P) (hg : g ∈ GLint E n P)
    (hk : k ∈ GlobalTheory.TopStep.prinCong n P D) (hck : c⁻¹ = g * k.1) (hD : e + e₀ ≤ D) (y₀ : Sp E n)
    (hy₀ : ∀ l, IntAt P ((qOf P : E) ^ e * y₀ l)) (hgy : ∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (g y₀ - y₀) l)) (y : Sp E n) :
    (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (c y - y₀) l)) ↔ (∀ l, IntAt P (((qOf P : E) ^ e₀)⁻¹ * (y - y₀) l)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set q : E := ((qOf P : ℕ) : E) with hqdef
  have hsm : ∀ (a : E) (v : Sp E n), (∀ l, IntAt P (a * v l)) ↔ a • v ∈ stdAt E n P := by
    intro a v
    rw [GlobalTheory.TopStep.mem_stdAt]
    rfl
  have hpow : ∀ (m : ℕ) (v : Sp E n), v ∈ stdAt E n P → q ^ m • v ∈ stdAt E n P := by
    intro m v hv
    have : q ^ m • v = ((qOf P : 𝓞 E) ^ m) • v := by
      rw [← algebraMap_smul E ((qOf P : 𝓞 E) ^ m) v]
      congr 1 <;> simp [hqdef]
    rw [this]
    exact Submodule.smul_mem _ _ hv
  have hw : q ^ e • y₀ ∈ stdAt E n P := (hsm _ _).1 hy₀
  have hkw := hk _ hw
  have hky : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) ∈ stdAt E n P := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + e + e₀ := ⟨D - e - e₀, by omega⟩
    have e1 : (q ^ e₀)⁻¹ • (k.1 y₀ - y₀) = q ^ d • ((q ^ D)⁻¹ • (k.1 (q ^ e • y₀) - q ^ e • y₀)) := by
      rw [map_smul, ← smul_sub, smul_smul, smul_smul]
      congr 1
      rw [hd, pow_add, pow_add]
      field_simp
    rw [e1]
    exact hpow _ _ hkw
  have hcy : (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀) ∈ stdAt E n P := by
    have e2 : c⁻¹ y₀ - y₀ = g (k.1 y₀ - y₀) + (g y₀ - y₀) := by
      rw [hck, LinearEquiv.mul_apply, map_sub]
      abel
    rw [e2, smul_add, ← map_smul]
    exact add_mem ((hg _).2 hky) ((hsm _ _).1 hgy)
  have hcc : ∀ x, c (c⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  rw [hsm, hsm]
  have e3 : (q ^ e₀)⁻¹ • (c y - y₀) = c ((q ^ e₀)⁻¹ • (y - y₀) - (q ^ e₀)⁻¹ • (c⁻¹ y₀ - y₀)) := by
    rw [← smul_sub, map_smul]
    simp only [map_sub, hcc]
    congr 1
    abel
  rw [e3, hc]
  exact Submodule.sub_mem_iff_left _ hcy

end GlobalTheory.CplCoset

namespace GlobalTheory.CplCoset

theorem sameCoset_kappa : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∀ P (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P ((κ'' P).1 y) (A.y0 β' P) ↔
      SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 β' P)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H β' κ' κ'' hF P y
  have hok := t.idx_ok μ
  have hU := (((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U_eq κ'.1).1 κ'.2
  obtain ⟨g, z, ⟨hmid, hsame⟩, hfr⟩ := (H.levCpl β').1 P (vUnder (t := t) P.1) (isOver_vUnder P.1) κ'.1 hU.1 (hU.2 _)
  have hgC := (exists_midLev_iff _ _ _ _ _ _ _ g).1 ⟨z, hmid⟩
  have hg : g ∈ GLint t.X.E _ P.1 := hok.int _ _ P hgC
  have hD1 := hok.cst_ok.D_pos P
  set k := g⁻¹ * ((κ'' P)⁻¹).1 with hk
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N (t.m2 + 1))) l)) := by
    intro s l
    have hc := GlobalTheory.FrameAway.frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD1 _ _ _ _ hfr (hF P) (fun _ _ => rfl) l s
    rw [← map_inv, ← map_mul, GlobalTheory.FrameAway.qOf_seamP, ← hk] at hc
    refine GlobalTheory.FrameAway.intAt_of_seamP t.seam P.1 _ ?_
    convert hc using 1
    have hm := congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N (t.m2 + 1))) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 ((t.cst μ).D P) k hD1 hcol
  have hy₀ := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H β' P
  unfold SameCoset
  refine sameCoset_local P.1 _ _ ((t.cst μ).D P) (κ'' P).1 g ⟨k, hkG⟩ (κ'' P).2 hg hkC ?_ ?_ (A.y0 β' P) hy₀ hsame y
  · show ((κ'' P).1)⁻¹ = g * (g⁻¹ * ((κ'' P)⁻¹).1)
    rw [mul_inv_cancel_left]
    rfl
  · by_cases h : P.1 ∈ t.Pr.vGs
    · simp only [h, if_true]
      have := hok.depthG P h
      omega
    · simp only [h, if_false]
      have := hok.depthQ P h
      omega

end GlobalTheory.CplCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (M Dd : ℕ) (hD : 2 * M ≤ Dd) (y0 V₀ V₁ : Sp E n) (g k : Sp E n →ₗ[E] Sp E n)
    (hgI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (g x l))
    (hkI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (k x l))
    (hkD : ∀ w : Sp E n, (∀ l, IntAt P (w l)) → ∀ l, IntAt P ((q ^ Dd)⁻¹ * (k w - w) l))
    (hgy : ∀ l, IntAt P ((q ^ M)⁻¹ * (g y0 - y0) l)) (hy0 : ∀ l, IntAt P (q ^ M * y0 l))
    (h0 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₀ - y0) l)) (h1 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₁ - y0) l)) :
    ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - V₀) l) := by
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)
  obtain ⟨s, hs⟩ : ∃ s, Dd = 2 * M + s := ⟨Dd - 2 * M, by omega⟩

  have hA : ∀ l, IntAt P ((q ^ M)⁻¹ * (k y0 - y0) l) := by
    intro l
    have h := hkD ((q ^ M) • y0) (fun l => by simpa [smul_eq_mul] using hy0 l) l
    have e : (q ^ M)⁻¹ * (k y0 - y0) l = q ^ s * ((q ^ Dd)⁻¹ * (k ((q ^ M) • y0) - (q ^ M) • y0) l) := by
      simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hs, pow_add, pow_mul]
      field_simp
      ring
    rw [e]
    exact mem_intS.1 ((intS P).mul_mem (mem_intS.2 (hqpow s)) (mem_intS.2 h))

  have hB : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - k y0) l) := by
    intro l
    have h := hkI ((q ^ M)⁻¹ • (V₁ - y0)) (fun l => by simpa [smul_eq_mul] using h1 l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  have hC : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - y0) l) := by
    intro l
    have e : (q ^ M)⁻¹ * (k V₁ - y0) l = (q ^ M)⁻¹ * (k V₁ - k y0) l + (q ^ M)⁻¹ * (k y0 - y0) l := by
      simp only [Pi.sub_apply]; ring
    rw [e]; exact (hB l).add (hA l)
  have hE : ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - g y0) l) := by
    intro l
    have h := hgI ((q ^ M)⁻¹ • (k V₁ - y0)) (fun l => by simpa [smul_eq_mul] using hC l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  intro l
  have e : (q ^ M)⁻¹ * (g (k V₁) - V₀) l =
      (q ^ M)⁻¹ * (g (k V₁) - g y0) l + (q ^ M)⁻¹ * (g y0 - y0) l + (-1 : E) * ((q ^ M)⁻¹ * (V₀ - y0) l) := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  exact mem_intS.1 ((intS P).add_mem ((intS P).add_mem (mem_intS.2 (hE l)) (mem_intS.2 (hgy l)))
    ((intS P).mul_mem ((intS P).neg_mem (intS P).one_mem) (mem_intS.2 (h0 l))))

end GlobalTheory.LocQCoset

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

theorem coset_agree : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hi β P hPG p p₁ g k hg hgy hk hkD hF
  have hok := t.idx_ok μ
  have hq := qOf_ne (E := t.X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : t.X.E) := intAt_nat (P := P.1) _
  have memS : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), x ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ↔ ∀ l, IntAt P.1 (x l) :=
    fun x => mem_localization_standardLattice P.1 x
  have rep : ∀ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p' P).symm (repY (cosetOf A (t.m2 + 1) hi β p')))
        (y0At A (t.m2 + 1) hi β P) := by
    intro p'
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.CosetApprox.exists_sameCoset t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p') (fun P => y0At A (t.m2 + 1) hi β P)
    have hrep : repY (cosetOf A (t.m2 + 1) hi β p') ∈ cosetOf A (t.m2 + 1) hi β p' :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p') ⟨r, hr⟩
    exact hrep P
  have unf : ∀ y y' : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y y' →
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M)⁻¹ * (y - y') l) := by
    intro y y' h
    unfold SameCoset at h
    simpa only [if_neg hPG] using h
  have bnd : ∀ y : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
      ∀ l, IntAt P.1 (((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M * y l) :=
    fun y h => (_root_.GlobalTheory.TwV.cplCoset_bound A dtU a hP hTie hi β P y h).2 hPG
  refine ⟨(memS _).2 fun l => ?_, (memS _).2 fun l => ?_, (memS _).2 fun l => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p) l
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p₁) l
  · have hW : (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) =
        g (k ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) := by
      apply (frsF t.sel (t.tup μ) p P).injective
      rw [LinearEquiv.apply_symm_apply, ← hF, LinearEquiv.apply_symm_apply]
    have hgI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (g.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hg x).2 ((memS x).2 hx))
    have hkI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (k.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hk x).2 ((memS x).2 hx))
    have hkD' : ∀ w : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (w l)) →
        ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k.toLinearMap w - w) l) := by
      intro w hw l
      simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using (memS _).1 (hkD w ((memS w).2 hw)) l
    have hrefl : SameCoset t.sel (t.tup μ) (t.cst μ) P (y0At A (t.m2 + 1) hi β P) (y0At A (t.m2 + 1) hi β P) := by
      unfold SameCoset
      intro l
      rw [sub_self, Pi.zero_apply, mul_zero]
      simpa using intAt_nat (E := t.X.E) (P := P.1) 0
    have hy0 := bnd _ hrefl
    have := core _ hq hqi (t.cst μ).M ((t.cst μ).D P) (hok.depthQ P hPG) (y0At A (t.m2 + 1) hi β P) _ _
      g.toLinearMap k.toLinearMap hgI hkI hkD' (unf _ _ hgy) hy0 (unf _ _ (rep p)) (unf _ _ (rep p₁)) l
    rw [hW]
    simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using this

end GlobalTheory.LocQCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1))
    (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ (Gg k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1) z, A.cplRel β P Gg.1 z →
    redGL _ P.1 k = redGL _ P.1 Gg → frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 →
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l)) ∧
    (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) l)) ∧
    k.1 ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁))) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E _ P.1) := by
  first | exact @GlobalTheory.CplCosetPt.cosetOf_frames_vG | exact GlobalTheory.CplCosetPt.cosetOf_frames_vG | (intros; apply GlobalTheory.CplCosetPt.cosetOf_frames_vG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalBaseChangeTransTower
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LiftTrans

open Matrix

section Places

variable {K M N : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field N] [NumberField N]
  [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N]

theorem under_under (w : HeightOneSpectrum (𝓞 N)) :
    (w.under (𝓞 M)).under (𝓞 K) = w.under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under w.asIdeal

theorem eq_under_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 N)}
    (i : v.adicCompletion K →+* w.adicCompletion N) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap N _ (algebraMap K N x)) : v = w.under (𝓞 K) := by
  have h1 : v.asIdeal ≤ (w.under (𝓞 K)).asIdeal := by
    intro x hx
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, GlobalTheory.DegOneLift.mem_iff_lt_one]
    rw [GlobalTheory.DegOneLift.mem_iff_lt_one] at hx
    have := GlobalTheory.DegOneLift.lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 K)).isPrime.ne_top h1)

end Places

end GlobalTheory.LiftTrans


open GlobalTheory.LiftTrans in
theorem GlobalTheory.LiftTrans.isLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), IsLift π P → IsLift P Q → IsLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro w f B hf hB
    obtain ⟨f1, hf1⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow K M (w.under (𝓞 M))
    obtain ⟨f2, hf2⟩ := GlobalTheory.AboveL.ResDeg.normV_eq_under_pow M N w
    rw [under_under] at hf1
    have hP := h1.sat (w.under (𝓞 M)) f1 B (by rw [under_under]; exact hf1) (by rw [under_under]; exact hB)
    have hQ := h2.sat w f2 _ hf2 hP
    have hff : f = f1 * f2 := by
      have h2le := GlobalTheory.DegOneLift.two_le_normV (w.under (𝓞 K))
      apply Nat.pow_right_injective h2le
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ (f1 * f2)
      rw [← hf, pow_mul, ← hf1, hf2]
    rw [Multiset.map_map] at hQ
    convert hQ using 2
    simp [Function.comp, hff, pow_mul]
  · intro τ
    rw [h2.inf τ, h1.inf, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · intro v w i hi hie σ σ' hσ hσ'
    have hv := eq_under_of_continuous i.toRingHom hi hie
    subst hv
    set u := w.under (𝓞 M) with hu
    haveI : w.asIdeal.LiesOver u.asIdeal := by rw [hu, HeightOneSpectrum.under_asIdeal]; infer_instance
    haveI : u.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by
      constructor
      rw [hu, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    haveI : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := by rw [HeightOneSpectrum.under_asIdeal]; infer_instance
    let φ1 := GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) u
    let φ2 := GroundTheory.Global.adicCompletionMap u w
    have hcomp : ∀ y, φ2 (φ1 y) = GroundTheory.Global.adicCompletionMap (w.under (𝓞 K)) w y := fun y =>
      congrFun (congrArg DFunLike.coe (GlobalTheory.BCChar.adicCompletionMap_comp_adicCompletionMap (w.under (𝓞 K)) u w)) y
    have hiφ : ∀ y, i y = φ2 (φ1 y) := fun y => by
      rw [hcomp]
      exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) (w.under (𝓞 K))).equalizer hi
        (GroundTheory.Global.continuous_adicCompletionMap _ _)
        (funext fun x => (hie x).trans (GroundTheory.Global.adicCompletionMap_algebraMap _ _ x).symm)) y
    have hb2 : Function.Bijective φ2 := ⟨φ2.injective, fun z => by
      obtain ⟨y, rfl⟩ := i.surjective z
      exact ⟨φ1 y, (hiφ y).symm⟩⟩
    have hb1 : Function.Bijective φ1 := ⟨φ1.injective, fun t => by
      obtain ⟨y, hy⟩ := i.surjective (φ2 t)
      exact ⟨y, hb2.1 (by rw [← hiφ, hy])⟩⟩
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
    obtain ⟨e1, he1⟩ := h1.loc (w.under (𝓞 K)) u (RingEquiv.ofBijective φ1 hb1)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) σ τ hσ hτ
    obtain ⟨e2, he2⟩ := h2.loc u w (RingEquiv.ofBijective φ2 hb2)
      (GroundTheory.Global.continuous_adicCompletionMap _ _) (fun x => GroundTheory.Global.adicCompletionMap_algebraMap _ _ x) τ σ' hτ hσ'
    refine ⟨e1.trans e2, fun g x => ?_⟩
    have hg : Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ2 hb2).toRingHom
        (Matrix.GeneralLinearGroup.map (RingEquiv.ofBijective φ1 hb1).toRingHom g) =
        Matrix.GeneralLinearGroup.map i.toRingHom g := by
      apply Units.ext
      ext j k
      simp only [Matrix.GeneralLinearGroup.map_apply]
      exact congrArg _ (hiφ _).symm
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he1, he2, hg]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.DenseInvFrob

theorem isSplitAt_of_inertiaDeg_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hf : w.asIdeal.inertiaDeg ℤ = 1)
    (he : w.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt w := by
  classical
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  set p : Ideal (𝓞 (maximalRealSubfield E)) := v.asIdeal with hp
  haveI : p.IsPrime := v.isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI hlo : w.asIdeal.LiesOver p := ⟨rfl⟩
  by_contra hns
  have hfin : (p.primesOver (𝓞 E)).Finite := Algebra.QuasiFinite.finite_primesOver p
  let _ : Fintype (p.primesOver (𝓞 E)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hrank : Module.finrank (𝓞 (maximalRealSubfield E)) (𝓞 E) = 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
    exact (IsFractionRing.finrank_eq (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) (𝓞 E) E).symm
  rw [hrank] at hsum
  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.inertiaDeg_tower (R := ℤ) p w.asIdeal
    rw [hf] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) p w.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hPmem : w.asIdeal ∈ p.primesOver (𝓞 E) := ⟨inferInstance, hlo⟩
  have huniq : ∀ q : p.primesOver (𝓞 E), q = ⟨w.asIdeal, hPmem⟩ := by
    intro q
    have hq : q.1.IsPrime := q.2.1
    have hql : q.1.LiesOver p := q.2.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1
    let u : HeightOneSpectrum (𝓞 E) := ⟨q.1, hq, hne⟩
    by_contra hqw
    apply hns
    refine ⟨u, fun h => hqw (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), ?_⟩
    ext1
    simp only [HeightOneSpectrum.under_asIdeal]
    exact hql.over.symm
  rw [Finset.sum_eq_single ⟨w.asIdeal, hPmem⟩ (fun b _ hb => absurd (huniq b) hb)
    (fun h => absurd (Finset.mem_univ _) h)] at hsum
  simp only [he1, hf1, mul_one] at hsum
  omega

end GlobalTheory.DenseInvFrob

namespace GlobalTheory.DenseInvFrob

end GlobalTheory.DenseInvFrob
end

