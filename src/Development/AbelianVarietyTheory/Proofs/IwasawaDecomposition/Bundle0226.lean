module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import ReciprocityTheory.NeutralLocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandOperatorCommutesIsometry
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem trace_pow_rect {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : ∀ a b, E' a b = ∑ c, ∑ d, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c, (Matrix.of E' ^ k) c c = ∑ c, (Matrix.of E ^ k) c c := by
  first
  | exact @_root_.GlobalTheory.TracePowEq.trace_pow_eq
  | exact _root_.GlobalTheory.TracePowEq.trace_pow_eq
  | (apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePowEq.trace_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePowEq.trace_pow_eq ..)

namespace IsoMat

variable {D : D7} {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

def trSm (hθ : IsInfFam θ) : GlobalTheory.Mem.AutSpace.SmFun θ V ≃ₗ[ℂ] GlobalTheory.Mem.AutSpace.SmFun θ V' where
  toFun φ := ⟨I.tr φ.1, I.tr_mem_SmFun hθ φ.2⟩
  invFun ψ := ⟨I.symm.tr ψ.1, I.symm.tr_mem_SmFun hθ ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => congrArg φ.1 (I.kapF_symm x))
  right_inv ψ := Subtype.ext (funext fun x => congrArg ψ.1 (I.symm.kapF_symm x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def conjSm (hθ : IsInfFam θ) :
    Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) →+* Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') where
  toFun f := (I.trSm hθ).toLinearMap ∘ₗ f ∘ₗ (I.trSm hθ).symm.toLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' f g := LinearMap.ext fun x => by simp
  map_zero' := LinearMap.ext fun x => by simp
  map_add' f g := LinearMap.ext fun x => by simp

theorem conjSm_apply (hθ : IsInfFam θ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) (x : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    I.conjSm hθ f (I.trSm hθ x) = I.trSm hθ (f x) := by
  show I.trSm hθ (f ((I.trSm hθ).symm (I.trSm hθ x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem conjSm_smul (hθ : IsInfFam θ) (c : ℂ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) :
    I.conjSm hθ (c • f) = c • I.conjSm hθ f := LinearMap.ext fun x => by simp [conjSm]

theorem derEnd_tr (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) :
    GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z = I.conjSm hθ (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (I.symm.adP τ Z)) := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (I.trSm hθ).surjective ψ
  rw [conjSm_apply]
  exact Subtype.ext (I.RderC_tr hθ τ Z φ.1)

theorem symm_adP_single (τ : D.what₂.Tau) (a b : Fin V'.rank) :
    I.symm.adP τ (Matrix.single a b 1) = ∑ c, ∑ d, (I.qT τ c a * I.pT τ b d) • (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
  rw [matrix_eq_sum_single (I.symm.adP τ _)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [adP, pT, qT, symm, Matrix.mul_apply, Matrix.single, ite_and]

theorem gelf_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V →
      gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  intro D V V' I θ hθ τ k φ hφ
  let E0 : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
    fun c d => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single c d 1)
  let E' : Fin V'.rank → Fin V'.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') :=
    fun a b => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single a b 1)
  have key := trace_pow_rect (fun c d => I.conjSm hθ (E0 c d)) E' (I.pT τ) (I.qT τ) (I.pT_qT τ) (I.qT_pT τ)
    (fun a b => by
      simp only [E', E0]
      rw [I.derEnd_tr hθ τ, I.symm_adP_single τ a b]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smul, conjSm_smul]) (k + 1)
  have hm : Matrix.of (fun c d => I.conjSm hθ (E0 c d)) = (I.conjSm hθ).mapMatrix (Matrix.of E0) := by
    ext c d; rfl
  have hs : ∑ c, (((I.conjSm hθ).mapMatrix (Matrix.of E0)) ^ (k + 1)) c c =
      I.conjSm hθ (∑ c, (Matrix.of E0 ^ (k + 1)) c c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← RingHom.map_pow, map_sum]; rfl
  rw [hm, hs, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have e1 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (I.trSm hθ ⟨φ, hφ⟩)
  have e2 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (⟨φ, hφ⟩ : GlobalTheory.Mem.AutSpace.SmFun θ V)
  refine e1.trans ?_
  change (GlobalTheory.SmoothForms.gelfA E' k (I.trSm hθ ⟨φ, hφ⟩)).1 = _
  rw [key, conjSm_apply]
  show I.tr _ = I.tr _
  rw [e2]

end IsoMat
end GlobalTheory.Mem.Isom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParDualPar
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.FrameModels

theorem card_signs {n p q : ℕ} (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p ∧
      (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = false).card = q := by
  have h1 : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
    have : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true) =
        Finset.univ.map (Fin.castLEEmb (by omega : p ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  refine ⟨h1, ?_⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => decide ((a : ℕ) < p) = true)
  simp only [Bool.not_eq_true] at h2
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega


open Formalism.L2.NTheta in
theorem goodPar_holPar {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    GoodPar n p q (holPar p q (kapW h p q)) := by
  have hs : StrictAnti fun a : Fin n => ((lamAt h a : ℚ) : ℝ) := fun a b hab => by
    have := GlobalTheory.HolDict.lamAt_strictAnti h hn hab
    show ((lamAt h b : ℚ) : ℝ) < ((lamAt h a : ℚ) : ℝ)
    exact_mod_cast this
  refine ⟨fun a => (lamAt h a : ℝ), fun a => decide ((a : ℕ) < p), ⟨hs, fun a => lamAt h a, fun a => rfl,
    GlobalTheory.HolDict.holPar_kapW_eq h hn hpq⟩, ⟨hs, fun a => ?_⟩, (card_signs hpq).1, (card_signs hpq).2⟩
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs'⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  have hn' : ((n : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs']; push_cast; rfl
  show ((lamAt h a : ℚ) : ℝ) - _ = _
  rw [hz, hn']
  push_cast
  ring

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hl, r, hr, hS⟩, ⟨-, hi⟩, hp, hq⟩ := h
  have hs : StrictAnti fun a => -lam (Fin.rev a) := fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab))
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a), ⟨hs, fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩,
    ⟨hs, fun a => ?_⟩, ?_, ?_⟩
  · rw [hS]
    ext z
    simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩
  · obtain ⟨m, hm⟩ := hi (Fin.rev a)
    refine ⟨-m - n + 1, ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by simp)

variable {D : D7}

theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) :
    ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := by
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _, D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  have := D.R.m_add_three_le_k
  have hi := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem goodPar_parAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    GoodPar (Wc D i).rank ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (parAt (Wc D i) σ ρ) := by
  have h := goodPar_holPar (D.hc (lab σ ρ)) (D.sp.W_rank _ (Nat.le_add_left _ _) i.2) (sig_add i ρ)
  unfold Links.parAt
  split_ifs
  · exact h
  · exact goodPar_dualPar h

theorem parAt_congr (W : HSp D) {σ σ' : D.what₂.LL →+* ℂ} (h : labE σ = labE σ') : parAt W σ = parAt W σ' := by
  have hl : lab σ = lab σ' := by
    funext ρ
    unfold lab
    rw [h]
  funext ρ
  unfold Links.parAt kapAt
  rw [h, hl]

theorem exists_frameKs : GlobalTheory.Published.DiscreteSeriesExists → ∀ (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x, D.embE x ∈ (algebraMap Ks D.what₂.LL).range) → ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ), FrameKs Ks MW := by
  intro hP D Ks _ _ hK
  classical
  have hne : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Nonempty (DSModel (Wc D i) (parAt (Wc D i) σ)) := fun i σ =>
    GlobalTheory.Published.dsExists_of_discreteSeriesExists hP D _ _ (D.sp.W_sig _) (goodPar_parAt i σ)
  have hx : ∀ (V : HSp D) (S S' : D.what₂.Tau → SPar) (h : Nonempty (DSModel V S)) (h' : Nonempty (DSModel V S')), S = S' →
      ∀ ρ, x0Mat (Classical.choice h) ρ = x0Mat (Classical.choice h') ρ := by
    intro V S S' h h' e ρ
    subst e
    rfl
  refine ⟨fun i σ => Classical.choice (hne i σ), fun i σ σ' hσ ρ => hx _ _ _ _ _ (parAt_congr _ ?_) ρ, fun i σ hσ τ a => ?_⟩
  · funext τ
    ext x
    obtain ⟨y, hy⟩ := hK (D.host.sigmaOf (D.eTau τ).1 x)
    show σ (D.embE (D.host.sigmaOf (D.eTau τ).1 x)) = σ' (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rw [← hy]
    exact RingHom.congr_fun hσ y
  · have he := (Classical.choice (hne i σ)).enum τ
    have e : parAt (Wc D i) σ τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ τ) := if_pos (hσ τ)
    rw [e] at he
    exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (D.sp.W_rank _ (Nat.le_add_left _ _) i.2) (sig_add i τ) he a).2

end GlobalTheory.RealGeo.FrameModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarInfiniteGLLtTopOfInfiniteGLHaarMeasureLtTop
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.HaarFinVol

open GlobalTheory.FlagMeas

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def entP (y : GL (Fin j) (Cinf E)) : InfinitePlace E → Fin j → Fin j → ℂ :=
  fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w

def ent (y : GL (Fin j) (Cinf E)) : MatInf E j := entP E j y

def swapH : Matrix (Fin j) (Fin j) (Cinf E) ≃ₜ (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun M w a b := M a b w
  invFun x := Matrix.of fun a b w => x w a b
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun w => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun w =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply w))

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin j) (Cinf E) → Matrix (Fin j) (Fin j) (Cinf E)) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin j) (α := Cinf E)
  let _ := Matrix.linftyOpNormedAlgebra (n := Fin j) (R := ℂ) (α := Cinf E)
  have : CompleteSpace (Matrix (Fin j) (Fin j) (Cinf E)) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

theorem isOpenEmbedding_entP : IsOpenEmbedding (entP E j) :=
  (swapH E j).isOpenEmbedding.comp (isOpenEmbedding_val E j)

theorem ent_mul (x y : GL (Fin j) (Cinf E)) : ent E j (x * y) = ent E j x * ent E j y := by
  funext w a b
  change (((x * y : GL (Fin j) (Cinf E)) : Matrix (Fin j) (Fin j) (Cinf E)) a b w) =
    (Matrix.of (ent E j x w) * Matrix.of (ent E j y w)) a b
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_apply]
  rfl

theorem detNorm_ent_pos (y : GL (Fin j) (Cinf E)) : 0 < detNorm E j (ent E j y) := by
  unfold detNorm
  refine Finset.prod_pos fun w _ => ?_
  have h1 : Matrix.of (ent E j y w) =
      (y : Matrix (Fin j) (Fin j) (Cinf E)).map (Pi.evalRingHom (fun _ => ℂ) w) := by
    ext a b; rfl
  have h2 : (Matrix.of (ent E j y w)).det = (y : Matrix (Fin j) (Fin j) (Cinf E)).det w := by
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  have hu : IsUnit (y : Matrix (Fin j) (Fin j) (Cinf E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have h3 : (y : Matrix (Fin j) (Fin j) (Cinf E)).det w ≠ 0 :=
    (hu.map (Pi.evalRingHom (fun _ => ℂ) w)).ne_zero
  rw [h2]
  positivity

theorem haarGL_lt_top_of_isCompact (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsCompact S)
    (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S < ⊤ := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; exact (measure_empty (μ := haarGL E j)).trans_lt ENNReal.zero_lt_top
  obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hd.continuousOn
  have hm := hpos x0 hx0
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S < ⊤
  rw [withDensity_apply _ hS.isClosed.measurableSet]
  refine (setLIntegral_mono' hS.isClosed.measurableSet
    (g := fun _ => ENNReal.ofReal ((detNorm E j x0)⁻¹ ^ j)) fun x hx => ?_).trans_lt ?_
  · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.2 (hpos x hx).le)
      (inv_anti₀ hm (hmin hx)) j)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.measure_lt_top

theorem haarGL_ne_zero_of_isOpen (S : Set (InfinitePlace E → Fin j → Fin j → ℂ)) (hS : IsOpen S)
    (hne : S.Nonempty) (hpos : ∀ x ∈ S, 0 < detNorm E j x) : haarGL E j S ≠ 0 := by
  have hd : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x :=
    GlobalTheory.HaarLeftInv.continuous_detNorm E j
  haveI := GlobalTheory.HaarLeftInv.isAddHaar_volume E j
  show Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    (fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) S ≠ 0
  have hf : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    ((hd.measurable.inv).pow_const j).ennreal_ofReal
  rw [Ne, withDensity_apply_eq_zero' hf.aemeasurable]
  have : {x : InfinitePlace E → Fin j → Fin j → ℂ | ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) ≠ 0} ∩ S = S :=
    Set.inter_eq_right.2 fun x hx => (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos x hx)) j)).ne'
  rw [this]
  exact hS.measure_ne_zero volume hne

theorem haarGL_image_mul (a : MatInf E j) (ha : 0 < detNorm E j a) (T : Set (MatInf E j)) :
    haarGL E j ((fun g => a * g) '' T) = haarGL E j T := by
  obtain ⟨hemb, hmp⟩ := GlobalTheory.HaarLeftInv.measurePreserving_mul_left E j a ha
  have := hemb.map_apply (haarGL E j) ((fun g => a * g) '' T)
  rw [hmp.map_eq, Set.preimage_image_eq T hemb.injective] at this
  exact this

variable [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))]

theorem measurableEmbedding_ent : MeasurableEmbedding (ent E j) :=
  (isOpenEmbedding_entP E j).measurableEmbedding

def nuGL : Measure (GL (Fin j) (Cinf E)) := (haarGL E j).comap (ent E j)

theorem nuGL_apply (s : Set (GL (Fin j) (Cinf E))) : nuGL E j s = haarGL E j (ent E j '' s) :=
  (measurableEmbedding_ent E j).comap_apply _ s

theorem isHaarMeasure_nuGL : (nuGL E j).IsHaarMeasure := by
  have he := isOpenEmbedding_entP E j
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [nuGL_apply]
    refine haarGL_lt_top_of_isCompact E j (entP E j '' K) (hK.image he.continuous) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y
  · intro g
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, nuGL_apply, nuGL_apply]
    have e1 : (fun h => g * h) ⁻¹' s = (fun h => g⁻¹ * h) '' s := by
      ext y; simp [Set.mem_image, eq_inv_mul_iff_mul_eq]
    have e2 : ent E j '' ((fun h => g⁻¹ * h) '' s) =
        (fun x : MatInf E j => ent E j g⁻¹ * x) '' (ent E j '' s) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => ent_mul E j g⁻¹ y
    rw [e1, e2, haarGL_image_mul E j _ (detNorm_ent_pos E j g⁻¹)]
  · intro U hU hne
    rw [nuGL_apply]
    refine haarGL_ne_zero_of_isOpen E j (entP E j '' U) (he.isOpenMap U hU) (hne.image _) ?_
    rintro _ ⟨y, -, rfl⟩
    exact detNorm_ent_pos E j y

end GlobalTheory.HaarFinVol

theorem GlobalTheory.haarGL_finite_pullback : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  intro E _ _ j _ _ ν _ D _ hD
  haveI := GlobalTheory.HaarFinVol.isHaarMeasure_nuGL E j
  have he := GlobalTheory.HaarFinVol.isOpenEmbedding_entP E j
  haveI : LocallyCompactSpace (GL (Fin j) (Cinf E)) := he.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin j) (Cinf E)) := he.isEmbedding.secondCountableTopology
  have h2 : GlobalTheory.HaarFinVol.nuGL E j {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w :
      GlobalTheory.FlagMeas.MatInf E j) ∈ D} ≤ GlobalTheory.FlagMeas.haarGL E j D :=
    (GlobalTheory.HaarFinVol.nuGL_apply E j _).trans_le (measure_mono fun _ ⟨_, hy, e⟩ => e ▸ hy)
  rw [Measure.isMulLeftInvariant_eq_smul ν (GlobalTheory.HaarFinVol.nuGL E j), Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (h2.trans_lt hD)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Neutral.B1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocDict

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Kbar (w : HeightOneSpectrum (𝓞 E)) : Type := AlgebraicClosure (w.adicCompletion E)

abbrev GalLoc (w : HeightOneSpectrum (𝓞 E)) : Type := Kbar w ≃ₐ[w.adicCompletion E] Kbar w

def IsLocEmb (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (ι : Ω →ₐ[E] Kbar w) : Prop :=
  ∀ z, z ∈ A ↔ IsIntegral (w.adicCompletionIntegers E) (ι z)

def Lifts {w : HeightOneSpectrum (𝓞 E)} (ι : Ω →ₐ[E] Kbar w) (g : GalLoc w) (σ : G E Ω) : Prop :=
  ∀ z, g (ι z) = ι (σ z)

theorem Lifts.eq {w : HeightOneSpectrum (𝓞 E)} {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ σ' : G E Ω}
    (H : Lifts ι g σ) (H' : Lifts ι g σ') : σ = σ' :=
  AlgEquiv.ext fun z => ι.toRingHom.injective ((H z).symm.trans (H' z))

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def HasNormGroups (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop :=
  ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), IsFiniteAbelian (w.adicCompletion E) L →
    ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ a σ ∈ normGroup (w.adicCompletion E) L)

end GlobalTheory.LocDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem iSup_range_weight_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  intro E _ _ _ n π τ lam h
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.exists_embRet E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  let F : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype))
      (π.rep.comp (embU n τ).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h0 =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))
  exact (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (embU n τ) π.V _ _ π.rep (embU n τ).subtype _ _
    π.isIrreducible_rep hσ hσ (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

end GlobalTheory.DefU
end

