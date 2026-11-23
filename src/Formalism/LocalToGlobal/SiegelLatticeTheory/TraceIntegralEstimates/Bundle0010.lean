module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameTop
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLaw
section
noncomputable section

open scoped Matrix
open Finset Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, Matrix.mulVec_zero, dotProduct_zero]

theorem hJ_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε x (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hJ_zero]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add, ih]

variable (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
  (hdual : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
include hdual

theorem span_expand (b : ℕ) (v : Fin n → ℂ) (hv : v ∈ spanLt e b) :
    v = ∑ c, hJ ε (f c) v • e c ∧ ∀ c : Fin r, b ≤ c.1 → hJ ε (f c) v = 0 := by
  unfold spanLt at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Set.mem_setOf_eq] at hd
    refine ⟨?_, fun c hc => ?_⟩
    · simp_rw [hdual, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' Finset.univ d (fun c => e c), if_pos (Finset.mem_univ d)]
    · rw [hdual, if_neg]
      intro h
      subst h
      omega
  | zero =>
    refine ⟨?_, fun c _ => hJ_zero ε _⟩
    simp_rw [hJ_zero, zero_smul, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    refine ⟨?_, fun c hc => by rw [hJ_add, hx.2 c hc, hy.2 c hc, add_zero]⟩
    simp_rw [hJ_add, add_smul]
    rw [Finset.sum_add_distrib, ← hx.1, ← hy.1]
  | smul a x _ hx =>
    refine ⟨?_, fun c hc => by rw [hJ_smul, hx.2 c hc, mul_zero]⟩
    simp_rw [hJ_smul, mul_smul]
    rw [← Finset.smul_sum, ← hx.1]

include hfz

theorem hJ_fam (c : Fin r) (b : Fin (r + 1)) (hcb : c.1 < b.1) : hJ ε (f c) (fam e z b) = 0 := by
  induction b using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last]; exact hfz c
  | cast b' =>
    simp only [fam, Fin.snoc_castSucc]
    rw [hdual, if_neg]
    intro h
    subst h
    simp at hcb

theorem sub_mem_spanLt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    (g - 1) *ᵥ fam e z b ∈ spanLt e b.1 := by
  induction b using Fin.lastCases with
  | last => simpa only [fam, Fin.snoc_last, Fin.val_last] using hg.2
  | cast b' => simpa only [fam, Fin.snoc_castSucc, Fin.coe_castSucc] using hg.1 b'

theorem expand {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    g *ᵥ fam e z b = fam e z b + ∑ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) • e c := by
  obtain ⟨hw, hw0⟩ := span_expand ε e f hdual b.1 _ (sub_mem_spanLt ε e f z hdual hfz hg b)
  have hgw : g *ᵥ fam e z b = fam e z b + (g - 1) *ᵥ fam e z b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hc : ∀ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) =
      hJ ε (f c) ((g - 1) *ᵥ fam e z b) := by
    intro c
    split_ifs with h
    · rw [hgw, hJ_add, hJ_fam ε e f z hdual hfz c b h, zero_add]
    · exact (hw0 c (not_lt.mp h)).symm
  simp_rw [hc]
  rw [← hw]
  exact hgw

theorem coef_diag {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : Fin r) :
    hJ ε (f a) (g *ᵥ e a) = 1 := by
  have hw0 := (span_expand ε e f hdual a.1 _ (hg.1 a)).2 a le_rfl
  have hgw : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_pos rfl, add_zero]

theorem coef_low {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a c : Fin r) (h : c.1 < a.1) :
    hJ ε (f a) (g *ᵥ e c) = 0 := by
  have hw0 := (span_expand ε e f hdual c.1 _ (hg.1 c)).2 a h.le
  have hgw : g *ᵥ e c = e c + (g - 1) *ᵥ e c := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_neg (fun h' => by subst h'; exact lt_irrefl _ h), add_zero]

theorem coef_mul {g₁ g₂ : Matrix (Fin n) (Fin n) ℂ} (h₁ : InS e z g₁) (h₂ : InS e z g₂) (a : Fin r)
    (b : Fin (r + 1)) (hab : a.1 < b.1) :
    hJ ε (f a) ((g₁ * g₂) *ᵥ fam e z b) = hJ ε (f a) (g₁ *ᵥ fam e z b) + hJ ε (f a) (g₂ *ᵥ fam e z b) +
      ∑ c : Fin r, if a.1 < c.1 ∧ c.1 < b.1 then hJ ε (f a) (g₁ *ᵥ e c) * hJ ε (f c) (g₂ *ᵥ fam e z b) else 0 := by
  have hx := expand ε e f z hdual hfz h₂ b
  conv_lhs => rw [← Matrix.mulVec_mulVec, hx]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, hJ_add, hJ_sum]
  simp_rw [Matrix.mulVec_smul, hJ_smul]
  rw [add_assoc]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    if_pos hab, coef_diag ε e f z hdual hfz h₁ a, mul_one, if_neg (by omega), zero_add]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hca : c ≠ a := Finset.ne_of_mem_erase hc
  rcases lt_or_gt_of_ne (fun h' : c.1 = a.1 => hca (Fin.ext h')) with h | h
  · rw [coef_low ε e f z hdual hfz h₁ a c h, mul_zero, if_neg (by omega)]
  · by_cases hcb : c.1 < b.1
    · rw [if_pos hcb, if_pos ⟨h, hcb⟩, mul_comm]
    · rw [if_neg hcb, if_neg (by omega), zero_mul]

end Formalism.L2.S.Pv.Chart

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.LatSpanLeSpan
section
noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_span (v : Fin r → S.V) {y : S.V} (h : ∀ a, S.hT (v a) y = 0) :
    ∀ x ∈ Submodule.span E (Set.range v), S.hT x y = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    exact h a
  | zero => simp
  | add x x' _ _ hx hx' => simp [hx, hx']
  | smul c x _ hx => simp [hx]

theorem latSpan_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpan aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  unfold latSpan
  rw [Submodule.span_le]
  rintro y ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

theorem coef_of_span (e f : Fin r → S.V) (hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0) {x : S.V}
    (hx : x ∈ Submodule.span E (Set.range e)) : x = ∑ a, S.hT (f a) x • e a := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hx
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp [hfe]

variable (Λ : Submodule (𝓞 E) S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (e f : Fin r → S.V)
  (L : Submodule (𝓞 E) S.V)

theorem mem_L_of_dual (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    {x : S.V} (hxe : ∀ a, S.hT (e a) x = 0) (hxf : ∀ a, S.hT (f a) x = 0)
    (hxL : ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y x) : x ∈ L := by
  have horth2 : ∀ (u : S.V) (w : Fin r → S.V), (∀ b, S.hT u (w b) = 0) →
      ∀ y ∈ Submodule.span E (Set.range w), S.hT u y = 0 := by
    intro u w hw y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact hw b
    | zero => simp
    | add x x' _ _ hx hx' => simp [hx, hx']
    | smul c x _ hx => simp [hx]
  have hfe : ∀ a b, S.hT (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← S.herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have hxd : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
    intro y hy
    rw [hΛ] at hy
    obtain ⟨y12, hy12, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨y1, hy1, yL, hyL, rfl⟩ := Submodule.mem_sup.mp hy12
    have h1 : S.hT y1 x = 0 := orth_span e hxe y1 (latSpan_le_span aa e hy1)
    have h2 : S.hT y2 x = 0 := orth_span f hxf y2 (latSpan_le_span _ f hy2)
    obtain ⟨o, ho⟩ := hxL yL hyL
    refine ⟨o, ?_⟩
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, h1, h2, ← ho]
    simp
  have hxΛ : x ∈ Λ := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular at hU
    rw [hU] at hxd
    exact hxd
  rw [hΛ] at hxΛ
  obtain ⟨x12, hx12, x2, hx2, hxeq⟩ := Submodule.mem_sup.mp hxΛ
  obtain ⟨x1, hx1, xL, hxL', rfl⟩ := Submodule.mem_sup.mp hx12
  have hx1' : x1 ∈ Submodule.span E (Set.range e) := latSpan_le_span aa e hx1
  have hx2' : x2 ∈ Submodule.span E (Set.range f) := latSpan_le_span _ f hx2
  have hf1 : ∀ a, S.hT (f a) x1 = 0 := by
    intro a
    have h := hxf a
    rw [← hxeq, map_add (f := _), map_add (f := _), (hL xL hxL' a).2, horth2 (f a) f (hff a) x2 hx2'] at h
    simpa using h
  have he2 : ∀ a, S.hT (e a) x2 = 0 := by
    intro a
    have h := hxe a
    rw [← hxeq, map_add (f := _), map_add (f := _), (hL xL hxL' a).1, horth2 (e a) e (hee a) x1 hx1'] at h
    simpa using h
  have h10 : x1 = 0 := by
    rw [coef_of_span e f hfe hx1']
    simp [hf1]
  have h20 : x2 = 0 := by
    rw [coef_of_span f e hef hx2']
    simp [he2]
  rw [← hxeq, h10, h20, zero_add, add_zero]
  exact hxL'

theorem exists_partner (z : S.V) (hzL : z ∈ L) (hzz : S.hT z z ≠ 0)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT x y)
    (hdual : ∀ c : E, (∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = S.hT y (c • z)) → c • z ∈ L)
    (hprim : ∀ c : E, c • z ∈ L → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ σ ∈ L, S.hT σ z = 1 := by
  classical
  have hstar : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, (o' : E) = star (o : E) := by
    intro o
    exact ⟨⟨star (o : E), (o.2).map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hsmul : ∀ (c : 𝓞 E) (y : S.V), c • y = (c : E) • y := fun c y => (algebraMap_smul E c y).symm
  let J : Ideal (𝓞 E) :=
    { carrier := {o | ∃ σ ∈ L, (o : E) = S.hT σ z}
      add_mem' := by
        rintro a b ⟨σ, hσ, ha⟩ ⟨τ, hτ, hb⟩
        exact ⟨σ + τ, L.add_mem hσ hτ, by simp [ha, hb]⟩
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨σ, hσ, ha⟩
        obtain ⟨c', hc'⟩ := hstar c
        refine ⟨c' • σ, L.smul_mem c' hσ, ?_⟩
        rw [hsmul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ← ha, hc']
        simp [starRingEnd_apply] }
  obtain ⟨o0, ho0⟩ := hint z hzL z hzL
  have hJ : J ≠ ⊥ := by
    intro h
    have hmem : o0 ∈ J := ⟨z, hzL, ho0⟩
    rw [h, Ideal.mem_bot] at hmem
    rw [hmem] at ho0
    exact hzz (by simpa using ho0.symm)
  have hI : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hinv : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1 := by
    intro x hx
    rw [FractionalIdeal.mem_inv_iff hI] at hx
    have hxz : x • z ∈ L := by
      apply hdual
      intro y hy
      obtain ⟨o, ho⟩ := hint y hy z hzL
      have hoJ : (o : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_coeIdeal _).mpr ⟨o, ⟨y, hy, ho⟩, rfl⟩
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).mp (hx _ hoJ)
      exact ⟨o', by rw [map_smul, smul_eq_mul, ← ho, ← ho']⟩
    obtain ⟨o, ho⟩ := hprim x hxz
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = J * (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ :=
          (mul_inv_cancel₀ hI).symm
      _ ≤ J * 1 := by gcongr
      _ = J := mul_one _
  have h1J : (1 : E) ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := h1 (FractionalIdeal.one_mem_one _)
  obtain ⟨j, ⟨σ, hσ, hj⟩, hj1⟩ := (FractionalIdeal.mem_coeIdeal _).mp h1J
  refine ⟨σ, hσ, ?_⟩
  rw [← hj]
  exact hj1

end Gen

end Formalism.L2.S.Pv.ClassCounting

end
end

