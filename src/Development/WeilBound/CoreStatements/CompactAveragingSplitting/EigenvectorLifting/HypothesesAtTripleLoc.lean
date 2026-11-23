module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0004
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

@[expose] public section

noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)
open Neutral.B1 (localIdele)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isField_Ev (hw : IsInertAt F E v w) : IsField (Ev E v) :=
  MulEquiv.isField (Field.toIsField _) (complEquiv hw ((under_eq_iff hw w).2 rfl)).toMulEquiv

theorem isQuad_Ev (hσ : IsCMExt F E σ) (v : Pl F) : ∃ ξ, IsQuad (cV σ v) ξ := by
  obtain ⟨δ, b, hδ, h0, h1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hσ.2.2.1 (conj_conj hσ) (not_forall.1 (conj_ne hσ))
  refine ⟨inclR (F := F) (Fv F v) (b 1), (b.ne_zero 1).isUnit.map _, ?_, Algebra.TensorProduct.basis (Fv F v) b, ?_, ?_⟩
  · change inclR (F := F) (Fv F v) (σ (b 1)) = _
    rw [h1, map_neg]
  · rw [Algebra.TensorProduct.basis_apply, h0]; rfl
  · rw [Algebra.TensorProduct.basis_apply]; rfl

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = cV σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem comp_incl (x : E) : compFin F E v (inclR (F := F) (AF F) x) = inclR (F := F) (Fv F v) x :=
  congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))

theorem psi_good {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (hu : PsiUnr ψ v) {ψv : AddChar (Fv F v) ℂ} (e : ∀ x, ψv x = psiLoc ψ v x) :
    Continuous ψv ∧ ψv ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [show (ψv : _ → ℂ) = psiLoc ψ v from funext e]
    exact h.1.comp (continuous_const.prodMk (continuous_singleFin v))
  · obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (1 : ℤ))
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hu x).1 fun y _ => by rw [← e, h1]; rfl)
    rw [hx] at this
    exact absurd this (by decide)

theorem locIdele_spec (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : (Ev E v)ˣ) :
    At (evFin F v) ((locIdele F w (Units.map (toCompl h).toMonoidHom y) : AE F E) - 1) ∧
      Units.map (compFin F E v).toMonoidHom (locIdele F w (Units.map (toCompl h).toMonoidHom y)) = y := by
  set x := Units.map (toCompl h).toMonoidHom y with hx
  have hf := finTens_locIdele (F := F) w x
  refine ⟨fun u hu => tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun P => ?_)),
    Units.ext ((toCompl_bijective hw h).1 ?_)⟩
  · rw [Algebra.smul_def, map_mul, map_sub, infTens_locIdele, map_one, sub_self, mul_zero, map_zero]
  · rw [Algebra.smul_def, map_mul, map_sub, map_one, map_mul, map_sub, hf, map_one, map_zero, map_zero]
    change (complMap rfl (u.2 (P.under (𝓞 F))) * algebraMap E _ 1) * (Neutral.B1.finiteSingle E w x.1 P - 1) = 0
    by_cases e : P = w
    · subst e
      subst h
      rw [show u.2 (P.under (𝓞 F)) = 0 from hu, map_zero, zero_mul, zero_mul]
    · rw [finSingle_ne e, sub_self, mul_zero]
  · have e1 := finAdEquiv_apply h (finTens F E (locIdele F w x))
    rw [hf] at e1
    have e2 : ∀ z : AE F E, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (finTens F E z) = compFin F E v z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [e2] at e1
    exact e1.symm.trans (finSingle_self w _)

theorem locChar_eq (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {χ : Chr F E} {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) (y : (Ev E v)ˣ) : χv y = χ (locIdele F w (Units.map (toCompl h).toMonoidHom y)) := by
  rw [← H _ (locIdele_spec hw h y).1, (locIdele_spec hw h y).2]


theorem det_loc {J : Matrix (Fin n) (Fin n) E} (h : IsUnit J.det) : IsUnit (locM (F := F) J v).det :=
  (RingHom.map_det (inclR (F := F) (Fv F v)) J) ▸ h.map _

theorem isHerm_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : IsHerm (cV σ v) (locM X.J v) :=
  ⟨fun i j => congrArg (inclR (F := F) (Fv F v)) (hX.herm i j), det_loc (Vac.herm_det hX)⟩

theorem isSkew_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsSkew σ B r s) : IsSkewM (cV σ v) (locM X.J v) :=
  ⟨fun i j => (congrArg (inclR (F := F) (Fv F v)) (hX.skew i j)).trans (map_neg _ _), det_loc (Vac.skew_det hX)⟩

theorem isLagr_loc [Invertible (2 : Fv F v)] {B : Base F E} (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {W : Spc F E d} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    IsLagr (cV σ v) (locM W.J v) (Cy.map (compFin F E v)) := by
  obtain ⟨ξ, hξ⟩ := isQuad_Ev hσ v
  refine isLagr_of_free (isField_Ev hw) hξ.invol hL.rank (isSkew_loc hW) ?_ fun t ht => ?_
  · have := congrArg (fun M => M.map (compFin F E v)) hL.iso
    simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
    have e1 : (incM F W.J).map (compFin F E v) = locM W.J v := Matrix.ext fun i j => comp_incl (F := F) (v := v) (W.J i j)
    have e2 : (Cy.map (cA σ)).map (compFin F E v) = (Cy.map (compFin F E v)).map (cV σ v) :=
      Matrix.ext fun i j => comp_cA (σ := σ) (v := v) (Cy i j)
    rwa [e1, e2, Matrix.transpose_map] at this
  · let t' : Fin m → AE F E := fun i => ThKH.Iwas.sgE E v (t i)
    have e : compFin F E v ∘ t' = t := funext fun i => ThKH.Iwas.comp_sgE _
    have ht' : At (evFin F v) t' := fun u hu => funext fun i => ThKH.Iwas.at_sgE _ u hu
    have := hL.free t' ht' (funext fun i => ThKH.Iwas.eq_zero_of_at
      (fun u hu => congrFun (ThKH.Iwas.at_mulVec_left hL.supp t' u hu) i) (by
        rw [RingHom.map_mulVec, e, ht]; rfl))
    rw [← e, this]
    exact funext fun i => map_zero _

end PositivityTheory.ThK.PT
