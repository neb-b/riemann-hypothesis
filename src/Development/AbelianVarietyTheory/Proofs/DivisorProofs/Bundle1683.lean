module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLine

theorem norm_psiAt_le {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ≤ 1 := by
  have hc := GlobalTheory.SchrSB.continuous_psiAt ψ hψ v
  have hK := (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (f := fun t : Fv F v => ‖GlobalTheory.LatVac.psiAt ψ v (y * t)‖) ((hc.comp (continuous_const.mul continuous_id)).norm)
  obtain ⟨C, hC⟩ := hK.bddAbove
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hle : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ^ n ≤ C := by
    refine hC ⟨(n : Fv F v), natCast_mem _ n, ?_⟩
    show ‖GlobalTheory.LatVac.psiAt ψ v (y * (n : Fv F v))‖ = _
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow]
  linarith

theorem norm_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ = 1 := by
  have h1 := norm_psiAt_le ψ hψ v y
  have h2 := norm_psiAt_le ψ hψ v (-y)
  have h3 : ‖GlobalTheory.LatVac.psiAt ψ v y‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-y)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v y), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-y))]

theorem star_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : star (GlobalTheory.LatVac.psiAt ψ v y) = GlobalTheory.LatVac.psiAt ψ v (-y) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Complex.star_def, Complex.conj_mul', norm_psiAt ψ hψ v y]
  simp

theorem symp_dbl_fromCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (w₁ w₂ : Matrix α β E) :
    symp (R := R) c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) =
      symp (R := R) c ξ JA JB w₁ w₁ - symp (R := R) c ξ JA JB w₂ w₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg,
    neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem at_symp_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v : Pl (F := F)) {w : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hw : At (evFin F v) w) :
    At (evFin F v) (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ JA JB w w) := by
  intro u hu
  have h1 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ u 1 w w
  have h0 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ 0 1 w w
  rw [hw u hu, mul_one] at h1
  rw [zero_smul, zero_mul, zero_mul] at h0
  change u * symp (cA σ) ξ JA JB w w = 0
  rw [← h1, h0]

end GlobalTheory.DblVacLine

namespace GlobalTheory.DblVacLine

theorem dbl_vac_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdd θ hθ hvac w₁ hw₁ w₂ hw₂
  have hψc : Continuous B.ψ := hT.base.std.1
  have hSB : G.M'.vac v ∈ SB _ := (hT.geo.hM'.vac v).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hloc : ∀ w ∈ latAtV G.V' G.W v, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo G.M'.co v w).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2)) *
      G.M'.vac v (ξ + (GlobalTheory.LatVac.locCo G.M'.co v w).1) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w w) *
          G.M'.vac v ξ := fun w hw ξ =>
    GlobalTheory.LatVac.heis_at_local_identity v G.M'.co B.ψ w _ _ (hat w hw) (hvac w hw) R (hR _ hSB) 0 hR0 ξ
  have hatd : At (evFin F v) (Matrix.fromCols w₁ w₂) := by
    intro u hu
    have h1 := hat w₁ hw₁ u hu
    have h2 := hat w₂ hw₂ u hu
    ext i j
    rcases j with j | j
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  have key := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hatd (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))

  set x₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).1 with hx₁
  set y₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).2 with hy₁
  set x₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).1 with hx₂
  set y₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).2 with hy₂
  have hdl : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂) = (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) := by
    simp only [hx₁, hx₂, hy₁, hy₂, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hdd w₁ w₂]
    ext k <;> rcases k with k | k <;> simp
  set s₁ := symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ with hs₁
  set s₂ := symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂ with hs₂
  have hb : At (evFin F v) (⅟(2 : AF F) * s₂) :=
    GlobalTheory.VacIndic.at_mul_left (at_symp_self σ _ _ _ v (hat w₂ hw₂))
  have hstarg : star (B.ψ (⅟(2 : AF F) * s₂)) = B.ψ (-(⅟(2 : AF F) * s₂)) := by
    have hb' : At (evFin F v) (-(⅟(2 : AF F) * s₂)) := fun u hu => by rw [smul_neg, hb u hu, neg_zero]
    rw [GlobalTheory.VacIndic.psi_of_at B.ψ hb, GlobalTheory.VacIndic.psi_of_at B.ψ hb', map_neg, ← GlobalTheory.LatVac.psiAt_apply,
      ← GlobalTheory.LatVac.psiAt_apply, star_psiAt B.ψ hψc v]
  have hcd : B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) = B.ψ (⅟(2 : AF F) * s₁) * star (B.ψ (⅟(2 : AF F) * s₂)) := by
    rw [symp_dbl_fromCols, ← hs₁, ← hs₂, hstarg, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have e : GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂))
      (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) := by
    funext x
    rw [hdl, hcd]
    simp only [GlobalTheory.WeilM.schr, boxFun, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    have hA : x ⬝ᵥ Sum.elim y₁ (-y₂) + (2 : Fv F v)⁻¹ * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ (-y₂)) =
        ((x ∘ Sum.inl) ⬝ᵥ y₁ + (2 : Fv F v)⁻¹ * (x₁ ⬝ᵥ y₁)) +
          -((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂)) := by
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply,
        mul_neg, Finset.sum_neg_distrib]
      ring
    have h1 : (x + Sum.elim x₁ x₂) ∘ Sum.inl = x ∘ Sum.inl + x₁ := by funext i; simp
    have h2 : (x + Sum.elim x₁ x₂) ∘ Sum.inr = x ∘ Sum.inr + x₂ := by funext i; simp
    rw [hA, AddChar.map_add_eq_mul, ← star_psiAt B.ψ hψc v, h1, h2]
    have l1 := hloc w₁ hw₁ (x ∘ Sum.inl)
    have l2 := congrArg star (hloc w₂ hw₂ (x ∘ Sum.inr))
    rw [star_mul', star_mul'] at l2
    linear_combination (star (GlobalTheory.LatVac.psiAt B.ψ v ((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂))) *
      star (G.M'.vac v (x ∘ Sum.inr + x₂))) * l1 + (B.ψ (⅟(2 : AF F) * s₁) * G.M'.vac v (x ∘ Sum.inl)) * l2
  rw [← e]
  exact key

end GlobalTheory.DblVacLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairs
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnRankAlg

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem exists_smul_mem_of_mem_span {A : Submodule (𝓞 K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.TargetLemmaCollection.target
  | exact _root_.GlobalTheory.TargetLemmaCollection.target
  | (apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetLemmaCollection.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetLemmaCollection.target ..)

theorem span_cut {A : Submodule (𝓞 K) Z} (hA : Submodule.span K (A : Set Z) = ⊤) (W : Submodule K Z) :
    Submodule.span K (Formalism.EigenvalueLevelCeiling.cut W A : Set Z) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.1 hx).2
  · intro w hw
    obtain ⟨d, hd, hm⟩ := exists_smul_mem_of_mem_span (A := A) (x := w) (by rw [hA]; trivial)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd
    have hmem : d • w ∈ Formalism.EigenvalueLevelCeiling.cut W A := by
      refine Submodule.mem_inf.2 ⟨hm, ?_⟩
      show d • w ∈ W
      rw [← algebraMap_smul K d w]
      exact W.smul_mem _ hw
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_le_span_sc {a : K} (ha : a ≠ 0) (A : Submodule (𝓞 K) Z) :
    Submodule.span K (A : Set Z) ≤ Submodule.span K (Formalism.EigenvalueLevelCeiling.sc a A : Set Z) := by
  rw [Submodule.span_le]
  intro y hy
  have hm : a • y ∈ Formalism.EigenvalueLevelCeiling.sc a A := Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hy' : y = a⁻¹ • (a • y) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem locP_subset_span (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) :
    (Formalism.HermitianLatticesTheory.localization₂ v.asIdeal L : Set Z) ⊆ Submodule.span K (L : Set Z) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs0
  have hx' : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

variable {P : Type} [Group P]

theorem mem_eig_iff (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (x : Z) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig ρ U ψ ↔ ∀ u : U, ρ u x = ((ψ u : 𝓞 K) : K) • x := by
  unfold Formalism.EigenvalueLevelCeiling.eig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem map_eig (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) :
    (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).map e = Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨(mem_eig_iff ρ U ψ _).2 fun u => ?_, by rw [← hp.2]; exact LinearMap.mem_range_self e x⟩
    have h := congrArg (fun f : Z →ₗ[K] Z => f x) (hc u)
    simp only [LinearMap.comp_apply] at h
    rw [← h, (mem_eig_iff ρ U ψ x).1 hx u, map_smul]
  · intro x hx
    obtain ⟨hx, hv⟩ := Submodule.mem_inf.1 hx
    rw [← hp.2] at hv
    obtain ⟨y, rfl⟩ := hv
    exact ⟨e y, hx, congrArg (fun f : Z →ₗ[K] Z => f y) hp.1⟩

theorem isLatIn_map (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) {A : Submodule (𝓞 K) Z}
    (hfg : A.FG) (hle : A ≤ (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).restrictScalars (𝓞 K))
    (hge : (Formalism.EigenvalueLevelCeiling.eig ρ U ψ : Set Z) ⊆ Submodule.span K (A : Set Z)) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀) (A.map (e.restrictScalars (𝓞 K))) := by
  refine ⟨hfg.map _, ?_⟩
  have hs : Submodule.span K (A : Set Z) = Formalism.EigenvalueLevelCeiling.eig ρ U ψ :=
    le_antisymm (Submodule.span_le.2 fun x hx => hle hx) hge
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hs, map_eig ρ U ψ e V₀ hp hc]

end Gen

theorem rankAtPlaces_alg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  intro K _ _ _ Bs Df S P _ _ c O hSp hD hPr hc hJ w hw
  have one : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v j) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v j)) →
      (∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.EigenvalueLevelCeiling.sc ((Nat.card O.U : ℕ) : K) (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j) →
      (∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) →
      ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
        Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := by
    intro v hs hd hj j
    have hU : ((Nat.card O.U : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h0 : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.Th0 v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      have h1 : x ∈ Submodule.span K (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j) : Set (Fin (O.nZ j) → K)) := by
        rw [span_cut (hs j).2.2]; exact hx
      exact Submodule.span_mono (fun y hy => (hd j).2.2 hy) (span_le_span_sc hU _ h1)
    have hJs : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.ThJ v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      exact Submodule.span_le.2 (fun y hy => locP_subset_span v _ ((hj j).2.2 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hy))) (h0 hx)
    exact ⟨isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hd j).1 (hd j).2.1 h0,
      isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hj j).1 (hj j).2.1 hJs, (hj j).2.2⟩
  exact ⟨one w (hSp w hw).1 (hD w hw).1 (hJ w hw).1, one _ (hSp w hw).2 (hD w hw).2 (hJ w hw).2⟩

end GlobalTheory.OnRankAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorNinth
section
noncomputable section

namespace GlobalTheory.GalOne.IoCmp

section Letters

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem letter_relab {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hm : ∀ τ, Formalism.L2.PjFree.relab c σ τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : Formalism.L2.Pj.LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = Formalism.L2.Pj.perFr X x v (Formalism.L2.PjFree.relab c σ τ) i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, Equiv.apply_symm_apply] at this
  rw [hi, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : Formalism.L2.PjFree.relab c σ τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    rw [h1] at hper
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, h1, by omega⟩
  · have h1 : Formalism.L2.PjFree.relab c σ τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    rw [h1] at hper
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm τ (by rw [h1]; exact (X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, h1, by omega⟩

end Letters

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
open GlobalTheory.OneMapRef.IoCmp

end GlobalTheory.GalOne.IoCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtCoord
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SplitCoord

theorem exists_at_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW t) = 0 ∧
      GlobalTheory.FlipMatch.coY σ X Y t 1 1 x = Z) ∧
    (∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧ x.map (piW (t.comp σ)) = 0 ∧
      GlobalTheory.FlipMatch.coX t 1 1 x = Z) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hdX hdY v t Z
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
      (-((X.J.map t)⁻¹ * Z * ((Y.J.map t)ᵀ)⁻¹))
    refine ⟨x, hat, h0, ?_⟩
    simp only [GlobalTheory.FlipMatch.coY, h1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t Z (0 : Matrix (Fin n) (Fin d) (Fv F v))
    refine ⟨x, hat, h1, ?_⟩
    simp only [GlobalTheory.FlipMatch.coX, h0, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponents
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.CondExps

theorem exists_condExps : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  intro D _ T Lc sc G s κ χ hχ
  let 𝔣 : Ideal (𝓞 D.host.F) := condF G.pl
  let 𝔐 : Ideal (𝓞 D.host.E) := 𝔣.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hrank : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E).symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have hnorm𝔣 : Ideal.absNorm 𝔣 = levQ G.pl := by
    simp only [𝔣, condF, levQ, map_prod, map_pow]
  have hlev : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have hnorm𝔐 : Ideal.absNorm 𝔐 = levQ G.pl ^ 2 := by
    rw [Ideal.absNorm_algebraMap, hrank, hnorm𝔣]
  have h𝔐0 : 𝔐 ≠ ⊥ := fun h => by
    have h' := hnorm𝔐
    rw [h, Ideal.absNorm_bot] at h'
    exact (pow_pos hlev 2).ne' h'.symm
  let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => expIn (condF G.pl) (P.under (𝓞 D.host.F))
  have hdvd : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal ^ f P ∣ 𝔐 := fun P => by
    have h1 : (P.under (𝓞 D.host.F)).asIdeal ^ f P ∣ 𝔣 := pow_multiplicity_dvd _ _
    have h2 : P.asIdeal ∣ (P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      Ideal.dvd_iff_le.2 Ideal.map_comap_le
    obtain ⟨c, hc⟩ := h1
    calc P.asIdeal ^ f P ∣ ((P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ^ f P :=
          pow_dvd_pow_of_dvd h2 _
      _ ∣ 𝔐 := by
          refine ⟨c.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), ?_⟩
          show 𝔣.map _ = _
          rw [hc, Ideal.map_mul, Ideal.map_pow]
  have hfin : (Function.support f).Finite := by
    refine (Ideal.finite_factors h𝔐0).subset fun P hP => ?_
    exact (dvd_pow_self _ hP).trans (hdvd P)
  refine ⟨Finsupp.ofSupportFinite f hfin, fun P => ?_, ?_⟩
  · exact (hχ.2.2.2 (P.under (𝓞 D.host.F)) P rfl).2 (Finset.notMem_empty _)
  · set a := Finsupp.ofSupportFinite f hfin
    have hJ : (a.prod fun P k => P.asIdeal ^ k) ∣ 𝔐 := by
      refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P _ => ?_
      · exact (Ideal.isCoprime_of_isMaximal fun h => hPQ (HeightOneSpectrum.ext h)).pow
      · exact hdvd P
    have e : (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) = Ideal.absNorm (a.prod fun P k => P.asIdeal ^ k) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [e, ← hnorm𝔐]
    exact Nat.le_of_dvd (hnorm𝔐 ▸ pow_pos hlev 2) (map_dvd Ideal.absNorm hJ)

end GlobalTheory.FunObj.SqNum.CondExps
end
end

