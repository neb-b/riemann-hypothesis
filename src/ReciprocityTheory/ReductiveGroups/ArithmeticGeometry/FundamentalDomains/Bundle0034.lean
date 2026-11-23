module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpLatticeTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalChartNormControlHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthonormalChartNormControl_holds : OrthonormalChartNormControl (E := E) := by
  intro r X x hx ho ρ hρ0 hρ1
  refine ⟨fun Z hZ => ⟨OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_le_of_lt hZ (by linarith)),
    fun la w hw => OrthonormalChartBounds.nfac_xZ (X := X) hx ho hρ0 hρ1 hZ la w hw,
    fun τ v => OrthonormalChartBounds.maj_xZ (X := X) hx ho hρ0 hρ1 hZ τ v⟩, ?_⟩
  intro G hG

  have hd : Differentiable ℂ (fun Z : X.Coord => X.xZ x Z) := by
    refine differentiable_pi.mpr fun τ => ?_
    refine differentiable_pi.mpr fun a => ?_
    refine differentiable_pi.mpr fun b => ?_
    simp only [Data.xZ, Matrix.mul_apply, Data.lowBlock, Matrix.of_apply]
    have hsum : ∀ {f : Fin r → X.Coord → ℂ}, (∀ j, Differentiable ℂ (f j)) →
        Differentiable ℂ (fun Z => ∑ j, f j Z) := by
      intro f hf
      first
        | exact Differentiable.fun_sum fun j _ => hf j
        | simpa [Finset.sum_fn] using Differentiable.sum (u := Finset.univ) (fun j _ => hf j)
        | fun_prop
    refine hsum fun k => ?_
    refine Differentiable.const_mul ?_ _
    refine (differentiable_const _).add ?_
    by_cases h : X.p0 ≤ (k : ℕ) ∧ (b : ℕ) < X.p0
    · simp only [dif_pos h]
      first
        | fun_prop
        | exact (differentiable_pi.mp ((differentiable_pi.mp
            ((differentiable_pi.mp differentiable_id) τ)) _)) _
    · simp only [dif_neg h]
      exact differentiable_const _
  refine hG.comp hd.differentiableOn ?_
  intro Z hZ
  exact OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_lt_of_le hZ (by linarith))

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpComponentCombination
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def eps' (p : ℕ) {n : ℕ} (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

section Coord

variable (X : Data E r) (τ : X.Ψ) {n : ℕ} (p : ℕ) (f : Fin n → Fin r → ℂ)
  (hf : ∀ k l, hermC τ.1 X.Gm (f k) (f l) = if k = l then eps' p k else 0)
include hf

end Coord

def uc (X : Data E r) (z0 : Frame X.Ψ r) (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  v - (X.Hf z0 τ v (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
    Data.emb τ.1 ξ

section Uc

variable (X : Data E r) {z0 : Frame X.Ψ r} (ξ : Fin r → E) (τ : X.Ψ)

lemma uc_comb (hz : z0 ∈ X.dom) {n : ℕ} (a : Fin n → ℂ) (V : Fin n → Fin r → ℂ) :
    uc X z0 ξ τ (∑ k, a k • V k) = ∑ k, a k • uc X z0 ξ τ (V k) := by
  let L : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := X.ppos z0 τ, map_add' := X.ppos_add z0 τ,
      map_smul' := fun k u => X.ppos_smul_eq z0 τ k u }
  have hHf : ∀ u w, X.Hf z0 τ u w = hermC τ.1 X.Gm ((2 : ℂ) • L u - u) w := fun u w => rfl
  have hsum : X.Hf z0 τ (∑ k, a k • V k) (Data.emb τ.1 ξ) =
      ∑ k, a k * X.Hf z0 τ (V k) (Data.emb τ.1 ξ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHf, map_sum]
    simp only [map_smul]
    have e : (2 : ℂ) • ∑ k, a k • L (V k) - ∑ k, a k • V k =
        ∑ k, a k • ((2 : ℂ) • L (V k) - V k) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_sub, smul_comm]
    rw [e, hermC_sum_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hermC_smul_left, hHf]
  unfold uc
  rw [hsum]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_smul, smul_smul,
    mul_div_assoc]

lemma uc_perp (hξξ : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (v v' : Fin r → ℂ)
    (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) (hv' : hermC τ.1 X.Gm v' (Data.emb τ.1 ξ) = 0) :
    hermC τ.1 X.Gm (uc X z0 ξ τ v') (uc X z0 ξ τ v) = hermC τ.1 X.Gm v' v := by
  have hsubR : ∀ u w w' : Fin r → ℂ,
      hermC τ.1 X.Gm u (w - w') = hermC τ.1 X.Gm u w - hermC τ.1 X.Gm u w' := by
    intro u w w'
    simp only [hermC, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmulR : ∀ (c : ℂ) (u w : Fin r → ℂ),
      hermC τ.1 X.Gm u (c • w) = conj c * hermC τ.1 X.Gm u w := by
    intro c u w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hsym : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = 0 := by
    have hc : hermC τ.1 X.Gm (Data.emb τ.1 ξ) v = conj (hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hermC, map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← ReciprocityTheory.ChartRestriction.G.FD.emb_cc, X.Gm_herm]
      ring
    rw [hc, hv, map_zero]
  unfold uc
  simp only [hermC_sub_left, hsubR, hermC_smul_left, hsmulR, hv', hξξ, hsym, mul_zero, sub_zero]

end Uc

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
end

