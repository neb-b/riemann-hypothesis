module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IsScalarOneOfComm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0052
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0065
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0054
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0066
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.CosBijPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0067
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0070
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpDatum
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem exists_isScalarF_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {χS χT : (AEF F E)ˣ →* Circle}
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    {p : GAF σ JS × GAF σ JT} (h1 : p.1 ∈ GQF σ JS) (h2 : p.2 ∈ GQF σ JT) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalarF B ξ₀ of oi p c := by
  have R := fun f h => _root_.PositivityTheory.ThKW.rat_subst_k C (inv_mem h1) (inv_mem h2) (f := f) h
  have R' := fun f h => _root_.PositivityTheory.ThKW.rat_subst_k C h1 h2 (f := f) h
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_partsF p
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth := _root_.GlobalTheory.T.theta_function_heisenberg_translate F E σ B C.good nS nT JS JT ξ₀
  obtain ⟨c, hc, h⟩ := _root_.PositivityTheory.ThKW.schur_norm_k C (of p * oi p * substF σ JS JT p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun u f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      have t2 : substF σ JS JT p⁻¹ (heisOF σ JS JT ξ₀ B.ψ u f) =
        heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT p.1⁻¹ p.2⁻¹ u) (substF σ JS JT p⁻¹ f) := (R f h).2.1 u
      simp only [Module.End.mul_apply]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← actOF_mul, ← actOF_mul, ← hof _ (hi.pres _ _ t1), ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, GlobalTheory.FinLatF.actOF_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      simp only [Module.End.mul_apply]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (substF σ JS JT p f) (R' f hf').1
  simp only [Module.End.mul_apply] at this
  rwa [← substF_mul, inv_mul_cancel, substF_one] at this
theorem IsScalarF.mul_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f)) {p q : GAF σ JS × GAF σ JT} {c c' : ℂ}
    (h : IsScalarF B ξ₀ of oi p c) (h' : IsScalarF B ξ₀ of oi q c') (h1 : q.1 ∈ GQF σ JS) (h2 : q.2 ∈ GQF σ JT) :
    IsScalarF B ξ₀ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT q f) := (_root_.PositivityTheory.ThKW.rat_subst_k C h1 h2 hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', substF_mul]
theorem half_add_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hε : IsHalfF σ ε) : (ε + cAF σ ε) * (ε + cAF σ ε) = ε + cAF σ ε := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  linear_combination hε.idem + h3 + 2 * hε.orth
theorem eta_cut_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) (u : Eˣ) :
    η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k hB hε) u) * η (cutRat ε hε.idem (Units.map (σ : E →* E) u)) = η (cutRat ε hε.idem u) := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  have e1 : cutRat _ (_root_.PositivityTheory.ThKW.half_add_k hB hε) u = cutRat ε hε.idem u * cutRat _ h3 u := Units.ext (by
    rw [Units.val_mul, cutRat_val, cutRat_val, cutRat_val]
    linear_combination (-(incAF F E u - 1) ^ 2) * hε.orth)
  have e2 := GlobalTheory.SplitDetCharF.char_norm hB.cm h2 (cutRat _ h3 u) (cutRat ε hε.idem (Units.map (σ : E →* E) u)) (by
    rw [cutRat_val, cutRat_val, map_add (f := _), map_sub, map_mul, map_one,
      GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm), cAF_incAF']
    rfl)
  rw [e1, map_mul, mul_assoc, e2, mul_one]
theorem real_data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s)
    (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume ∧
      GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v) * ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det =
        r * (-s).det * ((∏ v, tauB B v (b ⊗ₖ aᵀ).det) * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h))) := by
  obtain ⟨q1, q2⟩ := _root_.PositivityTheory.ThKW.det_mMF_k C ha hb
  have hH := _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  have hU := _root_.GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart (g⁻¹, h⁻¹)
  have c1 : s * mMF σ JS JT θ (g⁻¹, h⁻¹) = mMF σ JS JT θ (g⁻¹, h⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) hcm
    rwa [Prod.inv_mk] at this
  have c2 : mMF σ JS JT θ (g⁻¹, h⁻¹) * mMF σ JS JT θ (g, h) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  have c3 : (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det ≠ 0 := by
    rw [q2]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (map_ne_zero _).2 hd
  rw [← q1, ← q2]
  exact integral_gaussV hH.1 hs.sq hs.pos hU c1 c2 c3
theorem zF_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hε : ε * ε = ε) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) :
    zF σ JS JT η ε hε (g, h) * η (cutRat ε hε (Units.mk0 _ hΔ)) = 1 := by
  have da := ha.det_ne C.hS
  have db := hb.det_ne C.hT
  have e1 := cutDet_rat C.hT hb ε hε
  rw [map_inv, inv_eq_iff_eq_inv] at e1
  have e2 := cutDet_rat C.hS ha ε hε
  have u0 : Units.mk0 _ hΔ = Units.mk0 _ db ^ nS * Units.mk0 _ da ^ nT := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin])
  unfold zF
  rw [u0, e1, e2]
  simp only [MonoidHom.pow_apply, map_mul, map_pow, map_inv]
  generalize η (cutRat ε hε (Units.mk0 _ da)) = x
  generalize η (cutRat ε hε (Units.mk0 _ db)) = y
  rw [mul_comm (y ^ nS), mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, one_mul]
theorem phase_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) {Δ d N : E} (hΔ : Δ ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) {m : ℕ} (d1 : Δ * σ Δ = 1) (d2 : Δ * σ d = (-1) ^ m * d) {z : Circle}
    (v0 : z * η (cutRat ε hε.idem (Units.mk0 _ hΔ)) = 1) :
    (z : ℂ) * η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε) (Units.mk0 _ hN * Units.mk0 _ hΔ)) =
      η (cutRat ε hε.idem ((-1) ^ m)) * η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε) (Units.mk0 _ hN * Units.mk0 _ hd)) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have u1 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hd) = (-1) ^ m * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  exact congrArg _ (GlobalTheory.RatAut.phase_identity (η.comp (cutRat ε hε.idem)) (η.comp (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good hε)))
    (Units.map (σ : E →* E)) (_root_.PositivityTheory.ThKW.eta_cut_k C.good h2 hε) v0 u1 u2)
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModelW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_wired_k (hD : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hP : PartCharInv) (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_of_k hD _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sEv_k _root_.PositivityTheory.SiegelWeilFormula.Ald.bigT_k sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegelP
section
set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem siegelSmall_of_slice_k (hF : SliceFacts) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_k hF Ldx.adaptedChar
end PositivityTheory.SiegelWeilFormula.Ald
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCos
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem surj_k {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hS : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ ∃ g ∈ rat2 σ L.Y, γ = p * L.j g := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  obtain ⟨G0', hG0'⟩ := Afc.rat_frame (b := d.b) γ⁻¹ (inv_mem hγ)
  have hGG : G0' * G0 = 1 := kfour.incM_injective (F := F) (by
    rw [kfour.incM_mul', ← hG0, ← hG0', ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one,
      Afc.incM_one'])
  have hS0 : ∀ i, G0 (Sum.inr i) (Sum.inl L.i₀) = 0 := fun i => by
    have h1 := hS i
    rw [hG0] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  set v : Fin d.n → E := fun k => G0 (Sum.inl k) (Sum.inl L.i₀) with hv_def
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrFun (congrFun hGG (Sum.inl L.i₀)) (Sum.inl L.i₀)
    have h2 : ∀ k, G0 (Sum.inl k) (Sum.inl L.i₀) = 0 := fun k => congrFun h0 k
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at h1
    simp only [h2, hS0, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  obtain ⟨a, ha⟩ := exists_gl_col L.i₀ v hv
  obtain ⟨p1, hp1r, hp1⟩ := Afc.levi_ex hσ d.ok.frame a⁻¹
  have hp1P : p1 ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p1).2 (by rw [hp1, Matrix.toBlocks_fromBlocks₂₁])
  set P1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
    Matrix.fromBlocks (a⁻¹).1 0 0 ((((a⁻¹)⁻¹).1)ᵀ.map σ) with hP1_def
  have hP1 : inFrame d.b p1 = incM F P1 := by
    rw [hp1, hP1_def, Afc.incM_fromBlocks, show incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 from kfour.incM_zero]
  set M1 := P1 * G0 with hM1_def
  have hM1 : inFrame d.b (p1 * γ) = incM F M1 := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, hM1_def, kfour.incM_mul']
  have hγ1 : p1 * γ ∈ rat2 σ d.Y := mul_mem hp1r hγ
  have hx : ∀ r, M1 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    rw [hM1_def, Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | i
    · simp only [hP1_def, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul,
        Finset.sum_const_zero, add_zero]
      have e1 : ∀ j, G0 (Sum.inl j) (Sum.inl L.i₀) = a.1 j L.i₀ := fun j => (ha j).symm
      simp only [e1]
      rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp [Matrix.one_apply]
    · simp [hP1_def, hS0, Matrix.one_apply]
  have hform := form_E hε (p1 * γ) hM1
  have hy := yrow_zero hform hx
  set H := M1.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) with hH_def
  have hH := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.blockH_form_k L hform hx hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨h, hh⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hhr : h ∈ rat2 σ L.Y := kunf.rat_of_inFrame hh
  have hh' : inFrame L.b h⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hh]
    exact Matrix.inv_eq_right_inv hIA
  have hnF : inFrame d.b (p1 * γ * L.j h⁻¹) = incM F (M1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hP1, hG0, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hh', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k, hM1_def,
      kfour.incM_mul', kfour.incM_mul']
  have hnq : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (p1 * γ * L.j h⁻¹)) := by
    rw [hnF]
    exact NQ.map _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_E_k L hx hy hHH')
  have hnP : p1 * γ * L.j h⁻¹ ∈ par2 σ d.Y := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame _).2 hnq.projected_block_lower_sum
  have hnR : p1 * γ * L.j h⁻¹ ∈ rat2 σ d.Y := mul_mem hγ1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hhr))
  refine ⟨p1⁻¹ * (p1 * γ * L.j h⁻¹), mul_mem (inv_mem hp1P) hnP, mul_mem (inv_mem hp1r) hnR, h, hhr, ?_⟩
  rw [map_inv]
  group
theorem rep_mk_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (x : rat2 σ d.Y) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x) = p * x := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
    (Quotient.out_eq (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)).symm
  refine ⟨((γ : rat2 σ d.Y) : d.G), Subgroup.mem_subgroupOf.1 γ.2, (γ : rat2 σ d.Y).2, ?_⟩
  show (((Quotient.out (GlobalTheory.AutomorphicL2Unitary.mk ((par2 σ d.Y).subgroupOf (rat2 σ d.Y)) x)) : rat2 σ d.Y) : d.G) = _
  rw [← hγ]
  rfl
end Bq
theorem cos_bij_pf_k : ∃ e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ q', ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
    _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 = p * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') := by
  set H := (par2 σ d.Y).subgroupOf (rat2 σ d.Y) with hH
  set H' := (par2 σ L.Y).subgroupOf (rat2 σ L.Y) with hH'
  let jr : rat2 σ L.Y → rat2 σ d.Y := fun γ => ⟨L.j γ, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L γ.2⟩
  let e0 : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d := Quotient.lift (fun γ => GlobalTheory.AutomorphicL2Unitary.mk H (jr γ)) (by
    intro a b hab
    have hab' : b * a⁻¹ ∈ H' := QuotientGroup.rightRel_apply.1 hab
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨jr (b * a⁻¹), ?_⟩, ?_⟩
    · rw [hH', Subgroup.mem_subgroupOf] at hab'
      rw [hH, Subgroup.mem_subgroupOf]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L hab'
    · apply Subtype.ext
      show L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) * L.j a = L.j b
      rw [map_mul, map_inv, inv_mul_cancel_right])
  have he0 : ∀ γ, e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ) = GlobalTheory.AutomorphicL2Unitary.mk H (jr γ) := fun γ => rfl
  have hS : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 q')) := by
    intro q'
    induction q' using Quotient.inductionOn with
    | h γ =>
      obtain ⟨p, hp, -, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
      have e1 : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = p * L.j γ := by rw [he0]; exact hrep
      show _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)))
      rw [e1]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_parabolic_mul L hp (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.inStabilizer_smallerGroupEmbed L γ)
  let e : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun q' => ⟨e0 q', hS q'⟩
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h0 : e0 q1 = e0 q2 := congrArg Subtype.val h12
    induction q1 using Quotient.inductionOn with
    | h a =>
      induction q2 using Quotient.inductionOn with
      | h b =>
        change GlobalTheory.AutomorphicL2Unitary.mk H (jr a) = GlobalTheory.AutomorphicL2Unitary.mk H (jr b) at h0
        obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h0
        have hγv : ((γ : rat2 σ d.Y) : d.G) = L.j ((b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹) := by
          have := congrArg Subtype.val hγ
          simp only [Subgroup.coe_mul, jr] at this
          rw [map_mul, map_inv, ← this, mul_inv_cancel_right]
        have hP : (b : G2 σ L.Y) * (a : G2 σ L.Y)⁻¹ ∈ par2 σ L.Y := by
          apply _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.par_of_j_k L
          rw [← hγv]
          exact Subgroup.mem_subgroupOf.1 γ.2
        change GlobalTheory.AutomorphicL2Unitary.mk H' a = GlobalTheory.AutomorphicL2Unitary.mk H' b
        rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
        refine ⟨⟨b * a⁻¹, Subgroup.mem_subgroupOf.2 hP⟩, ?_⟩
        simp
  have hsurj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hpP, hpR, g, hg, hγ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.surj_k L (Quotient.out q).2 hq
    refine ⟨GlobalTheory.AutomorphicL2Unitary.mk H' ⟨g, hg⟩, Subtype.ext ?_⟩
    show GlobalTheory.AutomorphicL2Unitary.mk H (jr ⟨g, hg⟩) = q
    conv_rhs => rw [← Quotient.out_eq q]
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    refine ⟨⟨⟨p, hpR⟩, Subgroup.mem_subgroupOf.2 hpP⟩, Subtype.ext ?_⟩
    exact hγ.symm
  refine ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, fun q' => ?_⟩
  induction q' using Quotient.inductionOn with
  | h γ =>
    obtain ⟨p, hpP, hpR, hrep⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (jr γ)
    obtain ⟨p', hp'P, hp'R, hrep'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.rep_mk_k (d := L.sd) γ
    refine ⟨p * L.j p'⁻¹, mul_mem hpP (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (inv_mem hp'P)), mul_mem hpR (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (inv_mem hp'R)), ?_⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e0 (GlobalTheory.AutomorphicL2Unitary.mk H' γ)) = _
    rw [he0, hrep, hrep', map_mul, map_inv]
    simp only [jr]
    group
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLaw
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cOneLaw_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (w : InfinitePlace F)
    {nb' lam' 𝓖'} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' (R.ι w y * x) =
      Complex.exp (τ * (2 * z + d.n)) * _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x := by
  set c := Complex.exp (τ * (2 * z + d.n)) with hc
  have hterm : ∀ g : L.sd.G, ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x)) =
      c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := by
    intro g
    rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.AStep.j_comm_dil_k R L w τ y hy g, mul_assoc]
    obtain ⟨ha, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.a_dil_k R w L.i₀ τ y hy (L.j g * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.constantTerm_dilation H R w L.i₀ τ y hy hΦ]
    have e1 : ((d.Ht (R.ι w y * (L.j g * x)) : ℝ) : ℂ) = ((Real.exp (2 * τ) : ℝ) : ℂ) * ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ (by rw [ha]; exact mul_nonneg (Real.exp_pos _).le h0), ha, Complex.ofReal_mul]
    have e2 : ((d.Ht (L.j g * x) : ℝ) : ℂ) = ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht
      rw [Real.coe_toNNReal _ h0]
    rw [e1, e2, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos _).le h0, cpow_exp, hc]
    have e3 : Complex.exp (((2 * τ : ℝ) : ℂ) * (z - s0 d.m d.n)) * Complex.exp (τ * d.m) = Complex.exp (τ * (2 * z + d.n)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold s0
      push_cast
      ring
    rw [← e3]
    ring
  unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
  have hfun : (fun g : L.sd.G => ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y * x))) =
      fun g => c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := funext hterm
  rw [hfun]
  have hcs : ∀ (Ψ : L.sd.G → ℂ), GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => c * Ψ g) =
      fun g' => c * GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) Ψ g' := by
    intro Ψ
    funext g'
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    exact tsum_mul_left
  rw [hcs]
  simp only [fc, mul_assoc]
  exact integral_const_mul _ _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepHolW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem decW_pf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    ∃ (x' : d.G) (y : GR d.n), x = x' * R.ι w y ∧ ∀ y' : GR d.n, x' * R.ι w y' = R.ι w y' * x' := by
  obtain ⟨x', y, h, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w x
  exact ⟨x', y, h, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x' hx⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacTop
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem vacK_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) : _root_.PositivityTheory.SiegelWeilFormula.VacK_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_K'_k hT hF hO hI hA R, _root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R, fun L R' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vac_res'_k L hT hF R R'⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

