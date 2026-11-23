module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem translations_strongly_continuous :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod →
      ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧
        Continuous (fun y : G n => lT μ V y x) := by
  intro n _ _ μ _ V _ _ _ hU x
  have := (hU n μ).1
  have : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  constructor
  · let g : G n → C(G n, G n) := fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)
    have hm : ∀ h, MeasurePreserving (g h) μ μ := fun h => measurePreserving_mul_right μ h
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    refine key.congr fun h => ?_
    have hm' : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
    simp only [rR, dif_pos hm']
    rfl
  · let g : G n → C(G n, G n) := fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)
    have hm : ∀ y, MeasurePreserving (g y) μ μ := fun y => measurePreserving_mul_left μ y⁻¹
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact key

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootMapMemCompactOfIntegral
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.SwapRoot

section RootInt

variable {L : Type} [Field L]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hi : (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  simp only [partner, hi, hc, w2]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem val_cM_conj_le_one {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c).transpose) b d) ≤ 1 := by
  rw [cM_conj_apply]
  refine Valuation.map_sum_le _ fun p _ => Valuation.map_sum_le _ fun r _ => ?_
  split_ifs
  · exact hP p r
  · rw [map_zero]; exact zero_le

theorem blockM_int {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (hX : ∀ p r, Valued.v ((X - 1) p r) ≤ 1) (hY : ∀ p r, Valued.v ((Y - 1) p r) ≤ 1) :
    Formalism.UG.P.fIwasawaInt (blockM a h X Y) := by
  intro b d
  simp only [blockM, Matrix.add_apply]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (Formalism.UG.P.fIwasawa_int_one b d)
    (val_cM_conj_le_one _ _ hX b d)) (val_cM_conj_le_one _ _ hY b d)

theorem val_unip_sub_one_le {y : L} (hy : Valued.v y ≤ 1) (p r : Fin 2) :
    Valued.v (((!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) L) - 1) p r) ≤ 1 := by
  fin_cases p <;> fin_cases r <;> simp [hy]

theorem uR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h x hx
  have hσv := hU.2.1
  have hI : Formalism.UG.P.fIwasawaInt (((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.P.fIwasawaInt (blockM a h (nU x : GL (Fin 2) L).val (partner σ (nU x)))
    rw [partner_nU]
    refine blockM_int a h _ _ (val_unip_sub_one_le hx) (val_unip_sub_one_le ?_)
    rw [Valuation.map_neg, hσv]
    exact hx
  have hK := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) hI
  have he : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) = uR σ hU.1 a h x :=
    Subtype.ext (Units.ext (Formalism.UG.P.fIwasawa_mk_val σ _ _))
  rwa [he] at hK

end RootInt

end GlobalTheory.CompanionTheory.SwapRoot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionMemMaximalCompact
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have hw : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  have hc : cT σ (w2 L) = w2 L := by
    delta cT w2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  delta partner
  rw [hw, hc, weyl_mul_weyl, one_mul]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem cM_conj_int {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c)ᵀ) b d) ≤ 1 := by
  have hA : ∀ (x : Fin n) (p : Fin 2), Valued.v (cM L c x p) ≤ 1 := by
    intro x p
    show Valued.v (if x = c p then (1 : L) else 0) ≤ 1
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun r _ => ?_
  rw [Valuation.map_mul, Matrix.transpose_apply, Matrix.mul_apply]
  refine mul_le_one' ?_ (hA d r)
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun p _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA b p) (hP p r)

theorem weyl_sub_one_entries_integral (p r : Fin 2) : Valued.v ((w2 L - 1) p r) ≤ 1 := by
  delta w2
  fin_cases p <;> fin_cases r <;> simp [Matrix.one_apply]

theorem block_matrix_weyl_integral {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Formalism.UG.P.fIwasawaInt (blockM a h (w2 L) (w2 L)) := by
  delta blockM
  intro i j
  simp only [Matrix.add_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (cM_conj_int _ _ weyl_sub_one_entries_integral i j))
    (cM_conj_int _ _ weyl_sub_one_entries_integral i j)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem sR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    sR σ hU.1 a h ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h
  have hval : (((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (w2 L) := by
    show blockM a h (w2 L) (partner σ (wU L)) = _
    rw [partner_wU]
  have hwinv : (wU L)⁻¹ = wU L := Units.ext rfl
  have hginv : (sR σ hU.1 a h)⁻¹ = sR σ hU.1 a h := by
    show ((rootHom σ hU.1 a h) (wU L))⁻¹ = (rootHom σ hU.1 a h) (wU L)
    rw [← map_inv, hwinv]
  have hBB : blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L) = 1 := by
    have h1 := ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L).mul_inv
    rw [← Subgroup.coe_inv, hginv, hval] at h1
    exact h1
  have hint : ∀ i j, blockM a h (w2 L) (w2 L) i j ∈ intL L := fun i j => block_matrix_weyl_integral (L := L) a h i j
  let Bi : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨blockM a h (w2 L) (w2 L) i j, hint i j⟩
  have hBi : ∀ i j, ((Bi * Bi) i j : L) = (blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L)) i j := by
    intro i j
    simp [Bi, Matrix.mul_apply]
  have hy : Bi * Bi = 1 := by
    ext i j
    rw [hBi, hBB, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) ∈ GU σ n ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨(sR σ hU.1 a h).2, ⟨⟨Bi, Bi, hy, hy⟩, ?_⟩⟩
  apply Units.ext
  rw [hval]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SwapRoot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionRootBorelDecomp
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapFactor

section Local
variable {L : Type} [Field L]

def betaU (x : L) (hx : x ≠ 0) : GL (Fin 2) L where
  val := !![-x⁻¹, 1; 0, x]
  inv := !![-x, 1; 0, x⁻¹]
  val_inv := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
  inv_val := by
    ext p r; fin_cases p <;> fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem wU_mul_nU (x : L) (hx : x ≠ 0) :
    wU L * nU x = betaU x hx * (wU L * nU x⁻¹ * wU L) := by
  apply Units.ext
  ext p r
  fin_cases p <;> fin_cases r <;>
    simp [betaU, wU, nU, w2, Matrix.mul_apply, Fin.sum_univ_two, hx]

theorem partner_betaU_lower (σ : L →+* L) (x : L) (hx : x ≠ 0) : partner σ (betaU x hx) 1 0 = 0 := by
  have : ((betaU x hx)⁻¹ : GL (Fin 2) L).val = !![-x, 1; 0, x⁻¹] := rfl
  have hw : ∀ M : Matrix (Fin 2) (Fin 2) L, (w2 L * M * w2 L) 1 0 = M 0 1 := fun M => by
    simp [w2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  rw [partner, hw, this]
  simp [cT]

theorem arith (u v Q : ℂ) (hQ : Q ≠ 0) (o N : ℤ) :
    u ^ (-o) * Q ^ (-(-o) * N) * (v ^ o * Q ^ (-o * (N - 2))) = ((u / v) / Q ^ 2) ^ (-o) := by
  have h2 : (Q ^ 2) ^ (-o) = Q ^ (-(2 * o)) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have h3 : Q ^ (-(-o) * N) * Q ^ (-o * (N - 2)) = Q ^ (2 * o) := by
    rw [← zpow_add₀ hQ]; congr 1; ring
  have h4 : v ^ o = (v ^ (-o))⁻¹ := by rw [zpow_neg, inv_inv]
  rw [div_zpow, div_zpow, h2, zpow_neg Q (2 * o)]
  calc _ = u ^ (-o) * (v ^ (-o))⁻¹ * (Q ^ (-(-o) * N) * Q ^ (-o * (N - 2))) := by rw [h4]; ring
    _ = _ := by rw [h3]; simp [div_eq_mul_inv]

end Local

section Root
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {σ : L →+* L}

theorem ordL_neg' (x : L) (hx : x ≠ 0) : ordL (-x) = ordL x := by
  have h1 := v_eq_exp' (neg_ne_zero.2 hx)
  rw [Valuation.map_neg, v_eq_exp' hx] at h1
  have := WithZero.exp_injective h1
  omega

theorem ordL_one' : ordL (1 : L) = 0 := by simp [ordL]; rfl

theorem isBorel_root (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) :
    IsBorelU (rootHom σ hσ a h (betaU x hx)) := by
  intro i j hji
  rw [rootHom_val]
  by_cases hI : (∃ p, i = cI n a h p) ∧ ∃ r, j = cI n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hI
    rw [blockM_cI]
    have hlt : (cI n a h r : ℕ) < (cI n a h p : ℕ) := hji
    simp only [cI] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    rfl
  by_cases hJ : (∃ p, i = cJ n a h p) ∧ ∃ r, j = cJ n a h r
  · obtain ⟨⟨p, rfl⟩, r, rfl⟩ := hJ
    rw [blockM_cJ]
    have hlt : (cJ n a h r : ℕ) < (cJ n a h p : ℕ) := hji
    simp only [cJ] at hlt
    have hp : p = 1 := Fin.ext (by have := p.2; simp only [Fin.val_one]; omega)
    have hr : r = 0 := Fin.ext (by have := r.2; simp only [Fin.val_zero]; omega)
    subst hp hr
    exact partner_betaU_lower σ x hx
  rw [blockM_out]
  · exact Matrix.one_apply_ne (ne_of_gt hji)
  · by_contra hc
    push_neg at hc
    exact hI ⟨by simpa [eq_comm] using hc.1, by simpa using hc.2⟩
  · by_contra hc
    push_neg at hc
    exact hJ ⟨by simpa using hc.1, by simpa using hc.2⟩

theorem diag_a (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a, hk⟩ ⟨a, hk⟩ = -x⁻¹ := by
  have e : (⟨a, hk⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem root_hom_diag_entry_eq (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (hk : a + 1 < n) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨a + 1, hk⟩ ⟨a + 1, hk⟩ = x := by
  have e : (⟨a + 1, hk⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI])
  rw [e, rootHom_val, blockM_cI]
  rfl

theorem diag_other (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L) (hx : x ≠ 0) (k : Fin n)
    (hk : k.val < n / 2) (h1 : k.val ≠ a) (h2 : k.val ≠ a + 1) :
    (((rootHom σ hσ a h (betaU x hx) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k = 1 := by
  rw [rootHom_val, blockM_out]
  · exact Matrix.one_apply_eq k
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cI] at this
    omega
  · left
    intro p e
    have := congrArg Fin.val e
    have hp := p.2
    simp only [cJ] at this
    omega

end Root

theorem sR_uR_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj x hx
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact Nat.cast_ne_zero.2 (by omega)
  refine ⟨rootHom σ hU.1 a h (betaU x hx), isBorel_root hU.1 a h x hx, ?_, ?_⟩
  · have hij : i ≠ j := fun e => by
      have := congrArg Fin.val e
      omega
    have ha : a < n := by omega
    have ha1 : a + 1 < n := by omega
    have hin : i.val < n := by omega
    have hjn : j.val < n := by omega
    unfold chiDeltaU
    rw [Finset.prod_eq_mul i j hij ?_ (by simp) (by simp)]
    · rw [dite_eq_left hin, dite_eq_left hjn]
      have ei : (⟨i.val, hin⟩ : Fin n) = ⟨a, ha⟩ := Fin.ext hi
      have ej : (⟨j.val, hjn⟩ : Fin n) = ⟨a + 1, ha1⟩ := Fin.ext hj
      rw [ei, ej, diag_a, root_hom_diag_entry_eq, ordL_neg' _ (inv_ne_zero hx), ordL_inv' hx, hi, hj]
      have hN : ((n : ℤ) - 1 - 2 * ((a + 1 : ℕ) : ℤ)) = ((n : ℤ) - 1 - 2 * (a : ℤ)) - 2 := by
        push_cast; ring
      rw [hN]
      exact arith _ _ _ hq _ _
    · intro k _ hk
      have hkn : k.val < n := by omega
      rw [dite_eq_left hkn, diag_other hU.1 a h x hx ⟨k.val, hkn⟩ (by simpa using k.2)
        (fun e => hk.1 (Fin.ext (by simpa [hi] using e)))
        (fun e => hk.2 (Fin.ext (by simpa [hj] using e))), ordL_one']
      simp
  · simp only [sR, uR, ← map_mul]
    exact congrArg _ (wU_mul_nU x hx)

end GlobalTheory.CompanionTheory.SwapFactor

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevPointwiseBound
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.SupG

theorem norm_cls_sq_eq {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {K : Mat n → V}
    (h : MemLp (fun y : G n => K y.val) 2 μ) :
    ‖cls μ K‖ ^ 2 = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := integral_nonneg fun y => by positivity
  have hc : cls μ K = h.toLp _ := dif_pos h
  rw [hc, Lp.norm_toLp, h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem exists_unit {n : ℕ} {x : Mat n} (hx : x ∈ GLs n) : ∃ g : G n, g.val = x :=
  ⟨((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit, rfl⟩

theorem sup_sq_bound : SobG → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ (S : Finset (List (Bool × Fin n × Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (h : Mat n → V), ContDiffOn ℝ ∞ h (GLs n) → (∀ w, MemLp (fun y : G n => Rw w h y.val) 2 μ) → ∀ x ∈ GLs n, ‖h x‖ ^ 2 ≤ C * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 := by
  intro hS n _ _ μ _
  obtain ⟨S, r, C, hC⟩ := hS n μ
  refine ⟨S, max C 0, le_max_right _ _, fun V _ _ _ h hsm hL x hx => ?_⟩
  obtain ⟨g, rfl⟩ := exists_unit hx
  have h0 := hC V h hsm g.val hx
  have hw : ∀ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ ≤
      ‖cls μ (Rw w h)‖ ^ 2 := by
    intro w _
    set K := Rw w h with hK
    have hm : MemLp (fun y : G n => K y.val) 2 μ := hL w
    have hφ : Integrable (fun y : G n => ‖K y.val‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
    have hψ : Integrable (fun y : G n => ‖K (g.val * y.val)‖ ^ 2) μ := by
      simpa only [Units.val_mul] using hφ.comp_mul_left g
    have e1 : ∫ y : G n, ‖K (g.val * y.val)‖ ^ 2 ∂μ = ∫ y : G n, ‖K y.val‖ ^ 2 ∂μ := by
      simpa only [Units.val_mul] using
        integral_mul_left_eq_self (μ := μ) (fun y : G n => ‖K y.val‖ ^ 2) g
    rw [norm_cls_sq_eq hm, ← e1]
    exact setIntegral_le_integral hψ (Filter.Eventually.of_forall fun y => by positivity)
  have hI : 0 ≤ ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
    Finset.sum_nonneg fun w _ => integral_nonneg fun y => by positivity
  calc ‖h g.val‖ ^ 2
      ≤ C * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ := h0
    _ ≤ max C 0 * ∑ w ∈ S, ∫ y in {y : G n | lg y.val ≤ r}, ‖Rw w h (g.val * y.val)‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hI
    _ ≤ max C 0 * ∑ w ∈ S, ‖cls μ (Rw w h)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hw) (le_max_right _ _)

end GlobalTheory.CompanionTheory.PresSobA.SupG
end
end

