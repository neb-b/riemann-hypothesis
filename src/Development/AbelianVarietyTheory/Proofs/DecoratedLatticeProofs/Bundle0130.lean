module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLineRatioTransportOfColumnsCarryLines
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RatioAA

variable {D : D7}

theorem incA_mul_tmul (b : D.host.E) (p : AF D.host.F) (z : D.host.E) :
    incA D b * (p ⊗ₜ[D.host.F] z) = p ⊗ₜ[D.host.F] (b * z) := by
  show (1 ⊗ₜ[D.host.F] b) * (p ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem colMul_add {m n : ℕ} (x : Mx D m n) (l : Fin n) (c c' : AE D) :
    colMul x l (c + c') = colMul x l c + colMul x l c' := by
  funext k; simp [colMul, add_mul]

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (l : Fin n) (b c : AE D) :
    (fun k => b * colMul x l c k) = colMul x l (b * c) := by
  funext k; simp [colMul, mul_assoc]

theorem mul_mem_latMul {S : HSp D} {𝔞 𝔟 : Set D.host.E} {L L' : Lat S} {P : Pl D → Prop} (b : D.host.E)
    (h : ∀ a ∈ 𝔞, ∀ x ∈ L, ∃ a' ∈ 𝔟, ∃ x' ∈ L', ∀ i, b * (a * x i) = a' * x' i)
    {y : Fin S.rank → AE D} (hy : y ∈ latMul S 𝔞 L P) : (fun i => incA D b * y i) ∈ latMul S 𝔟 L' P := by
  let f : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := (AddMonoidHom.mulLeft (incA D b)).compLeft (Fin S.rank)
  have hle : latMul S 𝔞 L P ≤ (latMul S 𝔟 L' P).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    obtain ⟨a', ha', x', hx', e⟩ := h a ha x hx
    refine AddSubgroup.subset_closure ⟨α, hα, hs, a', ha', x', hx', ?_⟩
    funext i
    show incA D b * _ = _
    rw [incA_mul_tmul, e]
  exact hle hy

theorem latV_to_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {α : D.host.E} (hα : α ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => incA D α * y i) ∈ latA S L P :=
  mul_mem_latMul α (fun a ha x hx => ⟨α, hα, x, hx, fun i => by rw [Set.mem_singleton_iff.1 ha]; ring⟩) hy

theorem latA_to_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} (hAA : D.host.AA ≠ 0) {β : D.host.E}
    (hβ : β ∈ D.host.AA⁻¹) {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : (fun i => incA D β * y i) ∈ latV S L P := by
  refine mul_mem_latMul β (fun a ha x hx => ?_) hy
  have hm : β * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← inv_mul_cancel₀ hAA]; exact FractionalIdeal.mul_mem_mul hβ ha
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  refine ⟨1, rfl, o • x, L.smul_mem o hx, fun i => ?_⟩
  rw [Pi.smul_apply, Algebra.smul_def, ho]; ring

theorem latA_eq_zero (hAA : D.host.AA = 0) {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latA S L P) : y = 0 := by
  have hle : latA S L P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hs, a, ha, x, hx, rfl⟩
    have ha0 : a = 0 := by
      have : a ∈ D.host.AA := ha
      rw [hAA] at this; exact (FractionalIdeal.mem_zero_iff _).1 this
    funext i
    simp [ha0]
  simpa using hle hy

theorem idAt_eq_zero_of_AA (hAA : D.host.AA = 0) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (LV : Lat V) (LW : Lat W) (v : Pl D) (hsdV : IsSelfDualC V LV) (hC : ColsAt dV dW.jX LV LW v) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = v)) : a = 0 := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  set ε := pairA D.host.F 0 (singleV D.host.F v 1) with hεdef
  obtain ⟨N, hN, -, hNL⟩ := GlobalTheory.LatAlmostStd.exists_commensurable LV
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V LV hsdV)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 D.host.E))
    (fun k => dV.e k i)
  choose o ho using hb
  set x : Fin V.rank → D.host.E := ∑ k, Pi.single k (N • ((o k : 𝓞 D.host.E) : D.host.E)) with hxdef
  have hx : x ∈ LV := sum_mem fun k _ => hNL k (o k)
  have hxk : ∀ k, x k = N • (((b : 𝓞 D.host.E) : D.host.E) * dV.e k i) := by
    intro k
    rw [hxdef, Finset.sum_apply, Finset.sum_eq_single k (fun l _ hl => Pi.single_eq_of_ne' hl _)
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same]
    congr 1
    rw [show ((o k : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (o k) from rfl, ho k]
    first | rfl | exact Algebra.smul_def _ _
  set t : D.host.E := N • ((b : 𝓞 D.host.E) : D.host.E) with htdef
  set c : AE D := ε ⊗ₜ[D.host.F] t with hcdef
  have hc : c ∈ idAt D (· = v) := GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _
  have hyc : colMul dV.jX i c ∈ latV V LV (· = v) := by
    refine AddSubgroup.subset_closure ⟨_, hs.1, hs.2, 1, rfl, x, hx, ?_⟩
    funext k
    rw [one_mul, hxk k]
    show c * incA D (dV.e k i) = _
    rw [mul_comm, incA_mul_tmul, htdef]
    congr 1
    rw [mul_smul_comm, mul_comm (dV.e k i)]
  have hW := latA_eq_zero hAA ((hC i c hc).1 hyc)
  have hc0 : c = 0 := by
    have hpX : dW.pX * dW.jX = 1 := by
      change (dW.e'ᴴ * W.gram).map (incA D) * dW.e.map (incA D) = 1
      rw [← Matrix.map_mul, dW.e'e]
      exact Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))
    have h1 := congrFun (congrFun hpX i) i
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h1
    rw [← mul_one c, ← h1, Finset.mul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrFun hW k
    simp only [colMul, Pi.zero_apply] at this
    rw [mul_comm (dW.pX i k), ← mul_assoc, this, zero_mul]
  have ht : t ≠ 0 := by
    rw [htdef]
    refine smul_ne_zero hN ?_
    exact_mod_cast nonZeroDivisors.coe_ne_zero b
  have hεc : algebraMap (AF D.host.F) (AE D) ε = c * incA D t⁻¹ := by
    rw [hcdef, mul_comm, incA_mul_tmul, inv_mul_cancel₀ ht]; rfl
  rw [← ((placeIdem_acts D v ε hp).1 a).1 ha, hεc, hc0, zero_mul, zero_mul]

end GlobalTheory.FinPl.RatioAA


open GlobalTheory.FinPl.RatioAA in
theorem GlobalTheory.FinPl.ratio_of_colsAt : ∀ (D : D7) (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : Pl D), Tame D v → IsSelfDualC V LV → IsSelfDualC W LW → MonoAt dV LV LV₀ v → MonoAt dW LW LW₀ v → ColsAt dV dW.jX LV LW v → ∀ (i j : Fin ρ) (r : AE D), r ∈ idAt D (· = v) → (∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (r * a) ∈ latV V LV (· = v)) → ∀ a ∈ idAt D (· = v), colMul dW.jX j a ∈ latV W LW (· = v) → colMul dW.jX i (r * a) ∈ latV W LW (· = v) := by
  intro D V V₀ W W₀ ρ dV dW LV LV₀ LW LW₀ v _ hsdV _ _ _ hC i j r hr H a ha hja
  by_cases hAA : D.host.AA = 0
  · rw [idAt_eq_zero_of_AA hAA dV dW LV LW v hsdV hC i a ha, mul_zero]
    have : colMul dW.jX i (0 : AE D) = 0 := by funext k; simp [colMul]
    rw [this]; exact zero_mem _
  · have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹, colMul dW.jX i (incA D t * (r * a)) ∈ latV W LW (· = v) := by
      intro t ht
      refine FractionalIdeal.mul_induction_on ht (fun α hα β hβ => ?_) (fun x y hx hy => ?_)
      · have h1 := latV_to_latA hα hja
        rw [colMul_mul] at h1
        have hαa : incA D α * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ha
        have h2 := (hC j _ hαa).2 h1
        have h3 := H _ h2
        have h4 := (hC i _ (Ideal.mul_mem_left _ r hαa)).1 h3
        have h5 := latA_to_latV hAA hβ h4
        rw [colMul_mul] at h5
        convert h5 using 2
        rw [map_mul]; ring
      · rw [map_add (f := _), add_mul, colMul_add]; exact add_mem hx hy
    have := key 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CentralGram

variable {D : D7}

theorem trace_incA_eq (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def qG {ρ : ℕ} (A c : Mx D ρ ρ) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) (A ⬝ c).trace

theorem qG_add_right {ρ : ℕ} (A c c' : Mx D ρ ρ) : qG A (c + c') = qG A c + qG A c' := by
  simp only [qG, Matrix.mul_add, Matrix.trace_add, map_add (f := _), mul_add]

theorem qG_sub_left {ρ : ℕ} (A A' c : Mx D ρ ρ) : qG (A - A') c = qG A c - qG A' c := by
  simp only [qG, Matrix.sub_mul, Matrix.trace_sub, map_sub, mul_sub]

theorem trace_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) : (rat M : Mx D ρ ρ).trace = incA D M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply, map_sum]

theorem qG_rat {ρ : ℕ} (M C : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    qG (rat M) (rat C) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (M * C).trace) := by
  rw [qG, ← rat_mul, trace_rat, trace_incA_eq, map_mul]

theorem map_cA_rat {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) : (rat N).map (cA D) = rat (N.map star) := by
  funext i j; exact GlobalTheory.DualPairCheck.cA_incA _

def gramE (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  (-D.host.xi0) • (Xᴴ * (T.gram * X))ᵀ

theorem gramSkew_rat (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X) = rat (gramE T X) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, ← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← map_neg (incA D), gramE, rat_smul]
  rfl

theorem gramE_skew (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    ((gramE T X).map star)ᴴ = -((gramE T X).map star) := by
  have hK : (Xᴴ * (T.gram * X))ᴴ = Xᴴ * (T.gram * X) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  funext i j
  have h := congrFun (congrFun hK i) j
  rw [Matrix.conjTranspose_apply] at h
  simp only [gramE, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul, star_star, star_mul', star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, h]
  ring

theorem central : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.CentralTerms D := by
  intro D
  have h1 := GlobalTheory.T.mixed_model_central_terms_gram_identities D
  have hq : ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ),
      d.qS T c x = -qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) c.1 :=
    fun S S₀ T ρ d c x => (h1.1 S S₀ T ρ d).2 c x
  refine ⟨fun S S₀ T ρ d => ⟨(h1.1 S S₀ T ρ d).1, (h1.1 S S₀ T ρ d).2, fun ψ hψ => ⟨?_, ?_, ?_⟩⟩, h1.2⟩
  · intro x c c'
    rw [hq, hq, hq, AddSubgroup.coe_add, qG_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro x hx c hc
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨C, hC⟩ := mem_ratMx.1 hc
    rw [hq, gramSkew_rat, map_cA_rat, ← hC, qG_rat, ← map_neg]
    exact hψ.1.2.2.1 _
  · intro x hx x' hx'
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨X', rfl⟩ := mem_ratMx.1 hx'
    constructor
    · intro h
      have hM := GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect D ψ hψ ρ ((gramE T X).map star - (gramE T X').map star)
        (by rw [Matrix.conjTranspose_sub, gramE_skew, gramE_skew, neg_sub, neg_sub_neg]) (fun c => by
          rw [rat_sub, ← map_cA_rat, ← map_cA_rat, ← gramSkew_rat, ← gramSkew_rat]
          change ψ (qG _ c.1) = 1
          have eA : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X)).map (cA D)) c.1 = -d.qS T c (rat X) := by
            rw [hq S S₀ T ρ d, neg_neg]
          have eA' : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X')).map (cA D)) c.1 = -d.qS T c (rat X') := by
            rw [hq S S₀ T ρ d, neg_neg]
          rw [qG_sub_left, eA, eA', sub_eq_add_neg, neg_neg, AddChar.map_add_eq_mul, ← h c, ← AddChar.map_add_eq_mul,
            neg_add_cancel, AddChar.map_zero_eq_one])
      rw [sub_eq_zero] at hM
      rw [gramSkew_rat, gramSkew_rat, Matrix.map_injective star_injective hM]
    · intro h c
      rw [hq, hq, h]

end GlobalTheory.CentralGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertibl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaPlace.GramBasis

variable {D : D7} {S : HSp D}

def cv {n : ℕ} (y : Fin n → AE D) : Fin n → AE D := fun i => cA D (y i)

theorem hermAt_eq (x y : Fin S.rank → AE D) : hermAt S x y = cv y ⬝ᵥ (gA S *ᵥ x) := by
  unfold hermAt cv
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cv_mulVec {m : ℕ} (N : Matrix (Fin S.rank) (Fin m) (AE D)) (b : Fin m → AE D) :
    cv (N *ᵥ b) = vecMul (cv b) (adj N) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cv, mulVec, vecMul, dotProduct, map_sum, map_mul, adj, transpose_apply, map_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem hermAt_mulVec {m n : ℕ} (M : Matrix (Fin S.rank) (Fin m) (AE D)) (a : Fin m → AE D)
    (N : Matrix (Fin S.rank) (Fin n) (AE D)) (b : Fin n → AE D) :
    hermAt S (M *ᵥ a) (N *ᵥ b) = cv b ⬝ᵥ ((adj N * (gA S * M)) *ᵥ a) := by
  rw [hermAt_eq, cv_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem cv_single {n : ℕ} (i : Fin n) : cv (Pi.single i (1 : AE D)) = Pi.single i 1 := by
  funext k
  by_cases h : k = i
  · subst h; simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (i : Fin m) (j : Fin n) :
    (M *ᵥ Pi.single j (1 : AE D)) i = M i j := by
  rw [mulVec_single_one]; rfl

theorem gram_basis : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ β β' hεε hcε hε hact hΛ hβ hβ' h1 h2 hmem
  have h0 : (0 : AE D) ∈ intAt D (· = v) := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  have hcs : ∀ j k, (β *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun j k => by
    rw [mulVec_single_apply]; exact hβ k j
  have hcol : ∀ j, β *ᵥ Pi.single j (1 : AE D) ∈ Λ := fun j => (hmem _ (hcs j)).2 fun i => by
    rw [mulVec_mulVec, mulVec_single_apply, h2, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs
    · rw [mul_one]; exact hε
    · rw [mul_zero]; exact h0
  have hadj : adj β * adj β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← adj_mul, h2, adj_smul, adj_one, hcε]
  have hz : adj β * (gA S * (giA S * adj β')) = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [gA_giA_cancel, hadj]
  refine ⟨fun i j => ?_, fun i j => ?_, β' * (giA S * adj β'), fun i j => ?_, ?_⟩
  · have h := (hΛ.2.2 _ (hcs j)).1 (hcol j) _ (hcol i)
    rwa [hermAt_mulVec, cv_single, single_dotProduct, one_mul, mulVec_single_apply] at h
  · have h : adj (adj β * (gA S * β)) = adj β * (gA S * β) := by
      rw [adj_mul, adj_mul, adj_gA, adj_adj, Matrix.mul_assoc]
    exact congrFun (congrFun h j) i
  · have hs : ∀ k, ((giA S * adj β') *ᵥ Pi.single j (1 : AE D)) k ∈ idAt D (· = v) := fun k => by
      rw [← mulVec_mulVec]
      refine mulVec_mem_idAt _ (fun l => ?_) k
      rw [mulVec_single_apply]
      change cA D (β' j l) ∈ _
      rw [← (hact _).1 (hβ' j l), RingHom.map_mul, hcε]
      exact Ideal.mul_mem_right _ _ hε.1
    have hin : (giA S * adj β') *ᵥ Pi.single j (1 : AE D) ∈ Λ := (hΛ.2.2 _ hs).2 fun x hx => by
      refine ⟨LocSD.hermAt_mem_idAt hs x, ?_⟩
      have hw := (hmem x (hΛ.1 x hx)).1 hx j
      have e : x = β *ᵥ (β' *ᵥ x) := by
        rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]
        funext k
        exact ((hact _).1 (hΛ.1 x hx k)).symm
      rw [e, hermAt_mulVec, hz, smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul,
        RingHom.map_mul]
      exact FrameLat.mul_mem_intAE hε.2 ((FrameLat.cA_int_iff _).2 hw.2)
    have h := (hmem _ hs).1 hin i
    rwa [mulVec_mulVec, mulVec_single_apply] at h
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc β, h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, hz, smul_smul, hεε]

end GlobalTheory.IwaPlace.GramBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionOrthogonalSumApproxFiniteSums
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ThetaSplitApprox

theorem exists_slices {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (F : X × Y → ℂ) (hF : Continuous F) {C : Set X} {K : Set Y} (hC : IsCompact C) (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) : ∃ (n : ℕ) (a : Fin n → X) (π : Fin n → C(X, ℝ)),
      ∀ x ∈ C, ∀ y ∈ K, ‖F (x, y) - ∑ i, (π i x : ℂ) * F (a i, y)‖ ≤ ε := by
  have hV : ∀ a : X, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∀ x ∈ V, ∀ y ∈ K, ‖F (x, y) - F (a, y)‖ < ε := by
    intro a
    have hn : IsOpen {p : X × Y | ‖F p - F (a, p.2)‖ < ε} :=
      isOpen_lt (hF.sub (hF.comp (continuous_const.prodMk continuous_snd))).norm continuous_const
    obtain ⟨u, v, hu, -, hau, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := a)) hK hn (by
      rintro ⟨x, y⟩ ⟨hx, -⟩
      obtain rfl : x = a := hx
      simpa using hε)
    exact ⟨u, hu, hau rfl, fun x hx y hy => @huv (x, y) ⟨hx, hKv hy⟩⟩
  choose V hVo hVm hVε using hV
  obtain ⟨t, -, hcov⟩ := hC.elim_nhds_subcover V fun x _ => (hVo x).mem_nhds (hVm x)
  have hcov' : C ⊆ ⋃ i : Fin t.card, V (t.equivFin.symm i) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcov hz)
    exact Set.mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, by simpa using hzx⟩
  obtain ⟨π, hπs, hπ1, hπ01, -⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun i => hVo _) hC hcov'
  refine ⟨t.card, fun i => t.equivFin.symm i, π, fun x hx y hy => ?_⟩
  have h1 : ∑ i, π i x = 1 := by simpa using hπ1 hx
  have h2 : F (x, y) - ∑ i, (π i x : ℂ) * F (t.equivFin.symm i, y) =
      ∑ i, (π i x : ℂ) * (F (x, y) - F (t.equivFin.symm i, y)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
  rw [h2]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun i => π i x * ε) fun i _ => ?_).trans ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hπ01 i x).1]
    by_cases h0 : π i x = 0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hVε _ x (hπs i (subset_tsupport _ h0)) y hy).le (hπ01 i x).1
  · rw [← Finset.sum_mul, h1, one_mul]

theorem norm_sub_sum_tsum_le {Γ ι : Type*} [Fintype ι] {c : Γ → ℝ} (hc0 : ∀ γ, 0 ≤ c γ) (hc1 : HasSum c 1)
    (hfin : {γ | c γ ≠ 0}.Finite) {φ G : Γ → ℂ} (hφ : ∀ γ, ‖φ γ‖ = 1) {z : ℂ} (hG : ∀ γ, φ γ * G γ = z)
    (p : ι → Γ → ℝ) (b : ι → ℂ) {ε : ℝ} (hε : ∀ γ, c γ ≠ 0 → ‖G γ - ∑ i, (p i γ : ℂ) * b i‖ ≤ ε) :
    ‖z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i‖ ≤ ε := by
  have h0 : ∀ γ ∉ hfin.toFinset, c γ = 0 := fun γ hγ => by simpa using hγ
  have h1 : ∑ γ ∈ hfin.toFinset, c γ = 1 := (hasSum_sum_of_ne_finset_zero h0).unique hc1
  have h2 : ∀ i, ∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ) = ∑ γ ∈ hfin.toFinset, φ γ * ((c γ * p i γ : ℝ) : ℂ) :=
    fun i => tsum_eq_sum fun γ hγ => by simp [h0 γ hγ]
  have h3 : z - ∑ i, (∑' γ, φ γ * ((c γ * p i γ : ℝ) : ℂ)) * b i =
      ∑ γ ∈ hfin.toFinset, (c γ : ℂ) * (φ γ * (G γ - ∑ i, (p i γ : ℂ) * b i)) := by
    simp only [h2, mul_sub, hG, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, h1, Complex.ofReal_one, one_mul]
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [h3]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun γ => c γ * ε) fun γ hγ => ?_).trans ?_)
  · rw [norm_mul, norm_mul, hφ, one_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 γ)]
    exact mul_le_mul_of_nonneg_left (hε γ (by simpa using hγ)) (hc0 γ)
  · rw [← Finset.sum_mul, h1, one_mul]

theorem exists_approx : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B)
    (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → WO A T → ℂ) (g : Fin n → WO B T → ℂ),
      (∀ i, Continuous (P i)) ∧
      (∀ i (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T),
        P i (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * P i u) ∧
      (∀ i, IsThetaFunO ψ B T (g i)) ∧
      ∀ w, ‖f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε := by
  intro D ψ hψ S A B T o f hf ε hε
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨-, a2, -, a4, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := lattice_Mx D T.rank B.rank
  have hFc : Continuous fun p : WO A T × WO B T => f ((o.resS T).symm p) := hf.cont.comp (o.continuous_resS_symm T)
  obtain ⟨hA, hB⟩ := (_root_.GlobalTheory.BoxSlice.main D ψ hψ S A B T o).2.2.2 f hf
  obtain ⟨χ, hχc, hχs, hχ0, hχ1⟩ := GlobalTheory.RatPartition.exists_partition_one D A T
  obtain ⟨n, a, π, hπ⟩ := exists_slices _ hFc (C := tsupport χ) hχs hK hε

  have hπ' : ∀ x ∈ tsupport χ, ∀ y,
      ‖f ((o.resS T).symm (x, y)) - ∑ i, (π i x : ℂ) * f ((o.resS T).symm (a i, y))‖ ≤ ε := by
    intro x hx y
    obtain ⟨γ, hγ, hγK⟩ := hKc y
    obtain ⟨γ₀, rfl⟩ := mem_ratMx.1 hγ
    have law : ∀ u, f ((o.resS T).symm (u, rat γ₀ + y)) =
        ψ (-(symplOH B T (ratW T B γ₀) y)) * f ((o.resS T).symm (u, y)) := fun u => (hB u).quasi γ₀ y
    have h := hπ x hx _ hγK
    simp only [law] at h
    simp only [mul_left_comm _ (ψ _)] at h
    rwa [← Finset.mul_sum, ← mul_sub, norm_mul, hn, one_mul] at h
  have hper := fun i => _root_.GlobalTheory.PoincareLaw.poincare_law D ψ hψ A T (fun z => ((χ z * π i z : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hχc.mul (π i).continuous))
    ((HasCompactSupport.mul_right (f' := fun z => π i z) hχs).comp_left Complex.ofReal_zero)
  have hfin := (_root_.GlobalTheory.PoincareLaw.poincare_law D ψ hψ A T (fun z => ((χ z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hχc)
    (hχs.comp_left Complex.ofReal_zero)).1
  refine ⟨n, _, fun i v => f ((o.resS T).symm (a i, v)), fun i => (hper i).2.1, fun i γ u => (hper i).2.2 γ u,
    fun i => hB (a i), fun w => ?_⟩
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective w
  rw [AddEquiv.apply_symm_apply]
  refine norm_sub_sum_tsum_le (c := fun γ => χ (ratW T A γ + u)) (fun _ => hχ0 _) (hχ1 u) (by simpa using hfin u)
    (G := fun γ => f ((o.resS T).symm (ratW T A γ + u, v))) (fun _ => hn _) (fun γ => ?_)
    (fun i γ => π i (ratW T A γ + u)) _ fun γ hγ => hπ' _ (subset_tsupport _ hγ) v
  have law := (hA v).quasi γ u
  beta_reduce at law ⊢
  rw [law, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaSplitApprox

end
end

