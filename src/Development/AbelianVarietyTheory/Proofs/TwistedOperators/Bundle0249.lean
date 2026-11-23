module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChain
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)

theorem exists_mulVec_eq_of_maps {K : Type} [Field K] {n : ℕ} (M : GL (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ u ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ S) :
    ∀ u ∈ S, ∃ u₀ ∈ S, (M : Matrix (Fin n) (Fin n) K) *ᵥ u₀ = u := by
  intro u hu
  let f : S →ₗ[K] S := (M : Matrix (Fin n) (Fin n) K).mulVecLin.restrict hS
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have e : (M : Matrix (Fin n) (Fin n) K) *ᵥ (a : Fin n → K) = (M : Matrix (Fin n) (Fin n) K) *ᵥ (b : Fin n → K) :=
      congrArg Subtype.val hab
    have e2 := congrArg (fun x => ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) e
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using e2
  obtain ⟨a, ha⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨u, hu⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitHom_mulVec_mem_wPart (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V}
    {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v} (hg : g ∈ parab hc V (Fv F v) W) {u : Fin V.rank → Fv F v}
    (hu : u ∈ wPart τ W) :
    ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u
      ∈ wPart τ W := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨act hc V g y, mem_parab_iff_maps.1 hg y hy, splitVec_matHom_mulVec τ g y⟩

theorem flagChain_eq_X (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨i, by omega⟩ = wPart τ (𝔉.X i) := by
  rw [flagChain_of_le 𝔉 τ (show (i : ℕ) ≤ 𝔉.k by omega)]

theorem flagChain_eq_perp (𝔉 : GlobalTheory.Cusp.IsoFlag V) (τ : E →ₐ[F] Fv F v) (i : Fin (𝔉.k + 1)) :
    flagChain 𝔉 τ ⟨2 * 𝔉.k + 1 - i, by omega⟩ = wPart τ (perp V (𝔉.X i)) := by
  rw [flagChain_of_lt 𝔉 τ (show 𝔉.k < 2 * 𝔉.k + 1 - (i : ℕ) by omega)]
  congr 3
  ext
  simp only
  omega

theorem mem_par_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
    · rw [flagChain_of_le 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (Subgroup.mem_iInf.1 hg _) hu
    · rw [flagChain_of_lt 𝔉 τ hj] at hu ⊢
      exact splitHom_mulVec_mem_wPart hc τ (parab_le_perp (Subgroup.mem_iInf.1 hg _)) hu
  · intro H
    refine Subgroup.mem_iInf.2 fun i => mem_parab_iff_maps.2 fun y hy => ?_
    have H1 := H ⟨i, by omega⟩
    rw [flagChain_eq_X] at H1
    have H2 := H ⟨2 * 𝔉.k + 1 - i, by omega⟩
    rw [flagChain_eq_perp] at H2
    have key : ∀ τ' : E →ₐ[F] Fv F v, splitVec τ' (act hc V g y) =
        ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ' g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v))
          *ᵥ splitVec τ' y := fun τ' => splitVec_matHom_mulVec τ' g y
    rw [mem_extSub_iff_split hc h τ] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, ?_⟩
    · rw [key]
      exact H1 _ hy1
    · rw [key, mem_wPart_comp_iff hc h hJ τ]
      intro u hu
      obtain ⟨u₀, hu₀, rfl⟩ := exists_mulVec_eq_of_maps _ _ H2 u hu
      rw [pairing_splitHom]
      exact (mem_wPart_comp_iff hc h hJ τ).1 hy2 u₀ hu₀

end GlobalTheory.SplitFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PhaseReal

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j
  rfl

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i

theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem hO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    hO V W (isoPart V W C κ) (isoPart V W C' (y.map (incA D))) =
      Matrix.trace ((adj D y * W.gram).map (incA D) * κ) := by
  have hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y := by
    rw [conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    rw [Matrix.map_mul]
    rfl
  have hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D) := by
    rw [hu, ← hz]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.cA_incA _
  have e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) =
      C'.map (incA D) * (adj D y * W.gram).map (incA D) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit,
      Matrix.mul_assoc]
  have e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D) := rfl
  rw [hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2,
    Matrix.mul_one]

theorem pairQ_map (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (pairQ W y).map (incA D) = incA D D.host.xi0 • (adj D y * W.gram).map (incA D) := by
  ext i j
  simp only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem symplO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    symplO V W (isoPart V W C' (y.map (incA D))) (isoPart V W C κ) =
      -Algebra.trace (AF D.host.F) (AE D) (Matrix.trace ((pairQ W y).map (incA D) * κ)) := by
  unfold symplO
  rw [← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem finPart_trace {m n : ℕ} (P : Matrix (Fin n) (Fin m) (AE D)) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) : finPart D (Matrix.trace (P * κ)) = 0 := by
  have h : ∀ i j, finPart D (κ i j) = 0 := fun i j => congrFun (congrFun hκ i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem trace_real {t : AE D} (h : finPart D t = 0) :
    Algebra.trace (AF D.host.F) (AE D) t =
      pairA D.host.F (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t)) 0 := by
  have h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t =
      Algebra.trace (AF D.host.F) (AE D) t := by
    conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]
  refine Prod.ext rfl ?_
  have := congrArg Prod.snd h3
  exact this.symm.trans (zero_mul _)

theorem theta_trace (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : AE D) :
    θ ρ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) := by
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t :=
    GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t
  have hB := congrArg (infPart D) hA
  rw [map_add (f := _), infPart_cA] at hB
  have hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) =
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [← hC, hB, map_add (f := _), GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]

theorem theta_pair (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) D.host.E) (κ : Mx D m n) :
    θ ρ (infPart D (Matrix.trace (P.map (incA D) * κ))) =
      Matrix.trace (P.map (tauE D ρ) * compAt θ ρ κ) := by
  have h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hθ ρ).1 e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]

end GlobalTheory.PhaseReal

theorem GlobalTheory.PhaseReal.phase_eq : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  intro D V W r C C' hC ψ hψ θ hθ y κ hκ
  unfold phase
  rw [GlobalTheory.PhaseReal.symplO_iso V W C C' hC]
  set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F T))
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht,
      GlobalTheory.PhaseReal.theta_pair θ hθ ρ]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermTranslate

variable {D : D7}

theorem symplOH_isoPart_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (b a : Mx D W.rank r) : symplOH V W (isoPart V W C b) (isoPart V W C a) = 0 := by
  have rat_mul {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E)
      (N : Matrix (Fin m) (Fin n) D.host.E) :
      GlobalTheory.MixModel.rat (M * N) = GlobalTheory.MixModel.rat M * GlobalTheory.MixModel.rat N := Matrix.map_mul
  have adj_mul {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
      GlobalTheory.MixModel.adj (x * y) = GlobalTheory.MixModel.adj y * GlobalTheory.MixModel.adj x :=
    Formalism.UG.cT_mul (cA D) x y
  have hO_eq_trace (x y : WO V W) :
      hO V W x y = (GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA W * x))).trace := by
    simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    rfl
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← rat_mul, ← rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, hO_eq_trace]
  have e2 : isoPart V W C b = b * X := rfl
  have e3 : isoPart V W C a = a * X := rfl
  rw [e2, e3, adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * (GlobalTheory.MixModel.gA W * (b * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b)
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X) * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * b) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_heisO_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (G : WO S T → ℂ) (u v a : WO S T)
    (hav : symplOH S T a v = 0) :
    heisO ψ S T u (heisO ψ S T v G) a =
      ψ (symplO S T u v) * (ψ (symplOH S T (a + v) u) * G (a + v + u)) := by
  simp only [heisO]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_right_comm a u v]
  congr 2
  rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_left, hav, symplO_eq_add,
    GlobalTheory.FinTranslate.symplOH_skew S T v u]
  ring

end GlobalTheory.MixedTermTranslate

namespace GlobalTheory.MixedTermTranslate

theorem term_heisO_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs ψ _ μ 𝓨 hμ G hG y κ
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have iso := symplOH_isoPart_isoPart V W C hs.frame
  obtain ⟨u, hu⟩ : ∃ u, u = isoPart V W C' (Matrix.map y (incA D)) := ⟨_, rfl⟩
  have hterm : ∀ F : WO V W → ℂ, term ψ V V' W C C' B μ 𝓨 F y =
      ∫ s in 𝓨, heisO ψ V W u F (isoPart V W C s) ∂μ := by
    intro F
    show ∫ s in 𝓨, heisO ψ V W _ F (isoPart V W C s + midPart V V' W B 0) ∂μ = _
    rw [hmid, hu]
    simp only [add_zero]
  let Ψ : Mx D W.rank r → ℂ := fun s => ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)
  have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ s, Ψ (γ + s) = Ψ s := by
    rintro _ ⟨q₀, rfl⟩ s
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    simp only [Ψ]
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc (isoPart V W C (q₀.map (incA D))),
      ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀, hG.quasi, GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀,
      GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right, iso, zero_add, AddChar.map_add_eq_mul]
    have h1 : ψ (symplOH V W (isoPart V W C (q₀.map (incA D))) u) *
        ψ (-(symplOH V W (isoPart V W C (q₀.map (incA D))) u)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)) * h1
  have hph : phase ψ V W C C' y κ = ψ (symplO V W u (isoPart V W C κ)) := by rw [hu]; rfl
  have key : ∀ s, heisO ψ V W u (heisO ψ V W (isoPart V W C κ) G) (isoPart V W C s) =
      phase ψ V W C C' y κ * Ψ (s + κ) := by
    intro s
    rw [heisO_heisO_apply ψ V W G u _ _ (iso s κ), hph]
    show _ = _ * (ψ (symplOH V W (isoPart V W C (s + κ)) u) * G (isoPart V W C (s + κ) + u))
    rw [GlobalTheory.TwistEquiRat.isoPart_add]
  rw [hterm, hterm]
  simp only [key]
  rw [integral_const_mul, GlobalTheory.MixModel.covolOne_integral_add hμ' Ψ hper κ]
  rfl

end GlobalTheory.MixedTermTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heisO_add_fun (S T : HSp D) (u : WO S T) (G H : WO S T → ℂ) :
    heisO ψ S T u (G + H) = heisO ψ S T u G + heisO ψ S T u H := by
  funext w
  simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_smul_fun (S T : HSp D) (u : WO S T) (c : ℂ) (G : WO S T → ℂ) :
    heisO ψ S T u (c • G) = c • heisO ψ S T u G := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem integrableOn_heisO (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (u a : WO V W) :
    IntegrableOn (fun z => heisO ψ V W u G (isoPart V W C z + a)) 𝓨 μ := by
  obtain ⟨-, -, hvol⟩ := h
  obtain ⟨c, hc⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hcont : Continuous (fun z => heisO ψ V W u G (isoPart V W C z + a)) :=
    (GlobalTheory.HeisOrtho.continuous_heisO hψ.1 hG.cont u).comp ((continuous_isoPart V W C).add continuous_const)
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound hcont.aestronglyMeasurable c (Filter.Eventually.of_forall fun z => ?_)
  rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  exact hc _

theorem term_linear : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h y
  have key : ∀ G, IsThetaFunO ψ V W G → IntegrableOn
      (fun z => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G (isoPart V W C z + midPart V V' W B 0)) 𝓨 μ :=
    fun G hG => integrableOn_heisO V W C hψ h hG _ _
  refine ⟨fun G H hG hH => ?_, fun c G hG => ?_⟩
  · simp only [term, res, heisO_add_fun, Pi.add_apply]
    exact integral_add (key G hG) (key H hH)
  · simp only [term, res, heisO_smul_fun, Pi.smul_apply, smul_eq_mul]
    first
      | exact integral_const_mul c _
      | exact integral_mul_left c _

end GlobalTheory.MixedTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesUnitaryDiagonalTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LatIdx

theorem relIndex_intMat_translate : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r n : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c r, ∀ k₂ ∈ KU c r, (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (q ^ 2) ^ (n * (∑ i, max (d i) 0).toNat) := by
  intro L _ _ ϖ c q hq r n d t ht k₁ hk₁ k₂ hk₂

  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hq.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num

  rw [GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant c r n t k₁ k₂ hk₁ hk₂, ht,
    _root_.GlobalTheory.DiagIdx.relIndex_intMat_diag ϖ (q ^ 2) h0 h1 (GlobalTheory.T.relIndex_uniformizer_pow_mul_integers_eq_sq_pow ϖ c q hq) r n d,
    GlobalTheory.T.diagonal_unitary_antidiagonalForm_exponent_balance ϖ c q hq r d t ht]

end GlobalTheory.LatIdx
end
end

