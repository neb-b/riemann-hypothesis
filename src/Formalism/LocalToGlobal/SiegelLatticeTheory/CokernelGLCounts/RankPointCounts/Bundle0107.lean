module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0106
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FCInj
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem fC_inj : Function.Injective (fC M a πa hker g) := by
  intro X Y hXY
  induction X using Quotient.inductionOn with
  | h x =>
    induction Y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := Quotient.exact hXY
      have e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val := e1
      have e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ := e2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val
        rw [first_value_mul]
        have : (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1 := by
          rw [← first_value_mul, inv_mul_cancel]; rfl
        rw [e1', Matrix.mul_assoc]
        rw [show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by
          rw [← first_value_mul, mul_inv_cancel]; rfl, Matrix.mul_one]
        exact hl
      · show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val
        rw [second_value_mul, e2', ← Matrix.mul_assoc]
        rw [show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val *
            ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]
        exact hρ
      · show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one,
          mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOrthOf
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFib

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_orth_of {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : ∀ i, (VS D).hT (F.e i) x = 0) :
    x ∈ orth (VS D) F.X := by
  unfold orth
  refine Submodule.mem_iInf _ |>.2 fun y => Submodule.mem_iInf _ |>.2 fun hy => ?_
  rw [LinearMap.mem_ker]
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hx i
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
  | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]

theorem orth_e {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (x : (VS D).V) (hx : x ∈ orth (VS D) F.X) (i : Fin D.R.rS) :
    (VS D).hT (F.e i) x = 0 := by
  unfold orth at hx
  have h := (Submodule.mem_iInf _ |>.1 hx) (F.e i)
  have h2 := (Submodule.mem_iInf _ |>.1 h) (Submodule.subset_span ⟨i, rfl⟩)
  exact LinearMap.mem_ker.1 h2

theorem img_quot (L a₁ a₂ : MatR D) (hL : IsUnit L.det) (ha₁ : IsUnit a₁.det) (x₁ x₂ : GLR D)
    (hx₁ : (x₁ : MatR D) = L⁻¹ * a₁ * L) (hx₂ : (x₂ : MatR D) = L⁻¹ * a₂ * L) :
    ((x₁⁻¹ * x₂ : GLR D) : MatR D) = L⁻¹ * (a₂.conjTranspose * (a₁.conjTranspose)⁻¹).conjTranspose * L := by
  have hinv : ((x₁⁻¹ : GLR D) : MatR D) = L⁻¹ * a₁⁻¹ * L := by
    rw [Matrix.coe_units_inv, hx₁]
    refine Matrix.inv_eq_left_inv ?_
    calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₁ * L) = L⁻¹ * (a₁⁻¹ * (L * L⁻¹) * a₁) * L := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one, Matrix.nonsing_inv_mul _ ha₁, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hL]
  rw [Units.val_mul, hinv, hx₂, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc L⁻¹ * a₁⁻¹ * L * (L⁻¹ * a₂ * L) = L⁻¹ * a₁⁻¹ * (L * L⁻¹) * a₂ * L := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem act_quot (f : Fin (D.R.rS + 1) → (VS D).V) (t m₁ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (V₁ V₂ : MatR D)
    (hV₁ : IsUpUni V₁) (h₁ : ∀ b, m₁ (f b) = ∑ c, V₁ c b • f c) (h₂ : ∀ b, m₂ (f b) = ∑ c, V₂ c b • f c)
    (ht : ∀ b, t (m₁ (f b)) = m₂ (f b)) (b : Fin (D.R.rS + 1)) : t (f b) = ∑ c, (V₂ * V₁⁻¹) c b • f c := by
  have e : t = t * m₁ * m₁⁻¹ := (mul_inv_cancel_right t m₁).symm
  rw [e]
  exact act_mul f (t * m₁) m₁⁻¹ V₂ V₁⁻¹ (fun b => by show t (m₁ (f b)) = _; rw [ht, h₂]) (act_inv' f m₁ V₁ hV₁ h₁) b

end Formalism.L2.SG.Pf.ZsVolFib

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEFinal
section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdE

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem prodE_CZ_of_approxC (hap : ApproxC M δ u u' F0 what₂) (hst : Formalism.L2.SG.Pf.ProdEP2Cut.StepsU M δ u u' F0 what₂) :
    Formalism.L2.SG.Pf.ZsVolCut.ProdE M δ u u' F0 what₂ (Formalism.L2.SG.Pf.ZsVolCut.CZ M δ u u') :=
  prodE_of M δ u u' F0 what₂ hap (Formalism.L2.SG.Pf.ProdEP2Cut.locIdxC_of_count M δ u u' F0 what₂ hst)

end Formalism.L2.SG.Pf.ProdE
end
end

