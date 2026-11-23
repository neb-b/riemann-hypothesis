module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0011
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapMemCSpanOfRat
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_blk_gFull (Tf : FormsTiedSym D u Ch chOf) (g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brTen D u (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Q) =
      (∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)) •
        blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Q) := by
  have e1 : (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) =
      fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ))) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  have e2 : (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) = fun τ => ⇑(Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ)) :=
    funext fun τ => (Formalism.L2.Ker.ta_sqActL_coe _ _).symm
  unfold Formalism.L2.Ker.brTen
  rw [e1, e2, Formalism.L2.Ker.ta_blk_comp, Formalism.L2.Ker.ta_blk_comp]
  have e3 : (fun τ => ⇑(Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) ∘ₗ
      Formalism.L2.Ker.ta_sqActL (lamTr D u τ) (gFull D u (g τ)))) =
      fun τ => ⇑((((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) • (Formalism.L2.Ker.ta_sqActL (sgTr D u τ) (g τ) ∘ₗ
        Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))) := by
    funext τ f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Formalism.L2.Ker.ta_sqActL_coe]
    exact brOne_gFull Tf τ (g τ) f
  rw [e3, Formalism.L2.Ker.blk_smul]
  rfl

theorem blkRow_mem_CSpan {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (m : ι → DomWeight k)
    (M : ι → Matrix (Fin k) (Fin k) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (p : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m) : blkRow M p ∈ Formalism.MainNotions.product_first_zeroth_parts.CSpan m := by
  have hT : ∀ τ, IsUnit ((M τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact hM τ
  let g : ι → GL (Fin k) ℂ := fun τ => ⟨(M τ)ᵀ, ((M τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have h := Formalism.L2.Ker.lc_blk_sqAct_mem m g p hp
  rw [blk_sqAct_eq] at h
  have hgT : (fun τ => ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)ᵀ) = M := funext fun τ => Matrix.transpose_transpose _
  rw [hgT] at h
  have hc : (∏ τ, detPow ℂ k (g τ) (m τ).detShift) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have h2 := Submodule.smul_mem _ (∏ τ, detPow ℂ k (g τ) (m τ).detShift)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem map_mem_CSpan_of_rat {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) (hF : map D.what₂.embLL F ∈ RatSpan D lam)
    (s : D.what₂.LL →+* ℂ) : map s F ∈ Formalism.L2.Forms.CSpan lam := by
  have hinj : Function.Injective (map (σ := D.what₂.Tau × Fin n × Fin n) D.what₂.embLL) :=
    MvPolynomial.map_injective _ D.what₂.embLL.injective
  have hten : ∀ (j : D.what₂.LL →+* ℂ) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
      map j (Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ))) =
        Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom ℂ) (f τ)) := by
    intro j f
    have hi : j.comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    unfold Formalism.L2.Forms.ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.map_rename, MvPolynomial.map_map, hi]
  have key : ∀ p ∈ RatSpan D lam, ∀ F : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      map D.what₂.embLL F = p → map s F ∈ Formalism.L2.Forms.CSpan lam := by
    intro p hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hf, rfl⟩ := hx
      intro F hF
      have hFe : F = r • Formalism.L2.Forms.ten (fun τ => map (Int.castRingHom D.what₂.LL) (f τ)) := by
        apply hinj
        rw [hF, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten]
      rw [hFe, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hten, ← MvPolynomial.smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩)
      exact Formalism.L2.G.Model.sw_weyl_map (Int.castRingHom ℂ) le_rfl _ (f τ) (hf τ)
    | zero =>
      intro F hF
      have : F = 0 := hinj (by rw [hF, map_zero])
      rw [this, map_zero]; exact Submodule.zero_mem _
    | add x y hx' hy' hx hy =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      obtain ⟨Fy, hFy⟩ := exists_map_of_ratSpan D hy'
      have : F = Fx + Fy := hinj (by rw [map_add (f := _), hFx, hFy, hF])
      rw [this, map_add (f := _)]
      exact Submodule.add_mem _ (hx Fx hFx) (hy Fy hFy)
    | neg x hx' hx =>
      intro F hF
      obtain ⟨Fx, hFx⟩ := exists_map_of_ratSpan D hx'
      have : F = -Fx := hinj (by rw [map_neg, hFx, hF])
      rw [this, map_neg]
      exact Submodule.neg_mem _ (hx Fx hFx)
  exact key _ hF F rfl

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricClausesOfFormsNorm
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain


set_option maxHeartbeats 1000000 in
theorem fvStab_holds {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) : FvStab Tf := by
  intro c γ hγ v x hx
  have hF := Tf.fv D.R.m le_rfl (Or.inr rfl)
  have hγ' := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI_range _ γ).1 hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ'
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 =
      ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κ *
        ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1⁻¹ := by
    rw [← hκe]; rfl
  have hκv := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq κ).1 hκ |>.2 (Tf.atT.eV v).1
  rw [(Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.UlocAlt (Tf.atT.eV v).1 (Tf.atT.eV v).2] at hκv
  obtain ⟨_, hfix⟩ := (Subgroup.mem_inf.mp hκv).2
  have hzx := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) x.1 x.2
  have hzg := dualLoc_of (Tf.cls D.R.m le_rfl (Or.inr rfl)) (Tf.atT.eV v).1 ((D.fm u).til c) _ hx
  have key := conj_stepA (Tf.atT.eV v).1 _ κ γ.1 hbc x.1
  exact (hF v ((D.fm u).til c) ⟨_, hx⟩ hzg).trans ((congrArg _ ((congrArg _ (Subtype.ext key)).trans (hfix ⟨_, hzx⟩))).trans
    (hF v ((D.fm u).til c) x hzx).symm)

theorem class_injective_holds : ClassMapInjective :=
  class_injective_of_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf)

theorem stabiliser_bijective_holds : StabiliserMapBijective :=
  stabiliser_bijective_self_dual (fun _ _ _ _ Tf => selfDualP_of_formsTiedSym Tf) (fun _ _ _ _ Tf => fvStab_holds Tf)

end Formalism.L2.GlobalTheoryTheory.Br
end
end

