module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
public import ReciprocityTheory.SemistableReduction.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NoShortVectorLowerBoundHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module RealTangentSpace DiscreteLatticeMinimum
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem noShortVectorLowerBound_holds : NoShortVectorLowerBound (E := E) := by
  intro r X ξ ep0 hξ hep z hz hgap δ
  have hz' : z ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj z τ (Data.emb τ.1 ξ) = 1 := hz
  have hz1 : z ∈ X.dom := hz'.1
  haveI hzf : Fact (z ∈ X.dom) := ⟨hz1⟩
  have hk0 : 0 < X.k0 := X.minWeight_pos
  have hk0ne : X.k0 ≠ 0 := hk0.ne'
  have hdE : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero (K := E)))
  have hdEne : dE E ≠ 0 := hdE.ne'
  have hrd : 0 ≤ rdE E := by
    unfold rdE
    exact Real.rpow_nonneg hdE.le _
  have hepne : ep0 ≠ 0 := hep.ne'
  obtain ⟨d, hd⟩ : ∃ d : VT (X := X.toData) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
    apply FinrankRieszBounds.riesz <;> assumption
  obtain ⟨d', hd'⟩ : ∃ d' : VT (X := X.toData) z ξ,
      d' = (2 / (dE E * X.k0 ^ 2)) • Bmap z ξ d := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : X.Λp ξ, ‖d' - phi z ξ hξ μ‖ ≤
      (finrank ℝ (VT (X := X.toData) z ξ) : ℝ) ^ 3 * X.NA / (2 * X.k0 * Real.sqrt ep0) := by
    apply DiscreteLatticeMinimum.covering (Y := X) (z := z) (ξ := ξ) (hD3 := integerApproximationCount_holds) (hep := hep) <;> assumption
  have hfin : finrank ℝ (VT (X := X.toData) z ξ) ≤ 2 * fdeg E * (r - 2) := by
    apply FinrankRieszBounds.finrank_le <;> assumption
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = finrank ℝ (VT (X := X.toData) z ξ) := ⟨_, rfl⟩
  rw [← hn] at hμ hfin
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ‖d' - phi z ξ hξ μ‖ := ⟨_, rfl⟩
  rw [← hDdef] at hμ
  obtain ⟨w, hw⟩ : ∃ w : VT (X := X.toData) z ξ,
      w = (-(dE E / 2)) • Bmap z ξ (d' - phi z ξ hξ μ) := ⟨_, rfl⟩
  have hd_eq : (-(dE E / 2)) • Bmap z ξ d' = d := by
    rw [hd', map_smul, DiscreteLatticeMinimum.Bmap_Bmap, smul_smul, smul_smul]
    convert one_smul ℝ d using 2
    field_simp <;> ring
  have hw_eq : w = d - (-(dE E / 2)) • Bmap z ξ (phi z ξ hξ μ) := by
    rw [hw, map_sub, smul_sub, hd_eq]
  have hwn : ‖w‖ = dE E / 2 * (X.k0 * D) := by
    rw [hw, norm_smul, DiscreteLatticeMinimum.norm_Bmap, ← hDdef, Real.norm_eq_abs, abs_neg,
      abs_of_pos (half_pos hdE)]
  have hspos : 0 < Real.sqrt ep0 := Real.sqrt_pos.mpr hep
  have hsq : Real.sqrt ep0 ^ 2 = ep0 := Real.sq_sqrt hep.le
  have hden : 0 < 2 * X.k0 * Real.sqrt ep0 := mul_pos (mul_pos two_pos hk0) hspos
  have hD0 : 0 ≤ D := by rw [hDdef]; exact norm_nonneg _
  have hB : D * (2 * X.k0 * Real.sqrt ep0) ≤ (n : ℝ) ^ 3 * X.NA := (le_div_iff₀ hden).mp hμ
  have hD2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) ≤ ((n : ℝ) ^ 3 * X.NA) ^ 2 := by
    have h0 : 0 ≤ D * (2 * X.k0 * Real.sqrt ep0) := mul_nonneg hD0 hden.le
    have h1 := pow_le_pow_left₀ h0 hB 2
    have h2 : D ^ 2 * (4 * X.k0 ^ 2 * ep0) = (D * (2 * X.k0 * Real.sqrt ep0)) ^ 2 := by
      linear_combination (-(4 * D ^ 2 * X.k0 ^ 2)) * hsq
    rw [h2]
    exact h1
  have hx : 0 ≤ (X.NC : ℝ) ^ 2 * rdE E / ep0 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hrd) hep.le
  have hM2 : frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 =
      (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 * (X.NA : ℝ) ^ 2 *
        ((X.NC : ℝ) ^ 2 * rdE E / ep0) := by
    have hs := Real.sq_sqrt hx
    rw [frameIndexBound]
    linear_combination ((fdeg E : ℝ) * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 3 * dE E *
      (X.NA : ℝ)) ^ 2 * hs
  have hwM : ‖w‖ ^ 2 ≤ frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0 := by
    rw [hwn, hM2]
    have hlhs : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by
      have h3 : (dE E / 2 * (X.k0 * D)) ^ 2 * (16 * ep0) =
          dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) := by ring
      rw [h3]
      calc dE E ^ 2 * (D ^ 2 * (4 * X.k0 ^ 2 * ep0)) ≤ dE E ^ 2 * (((n : ℝ) ^ 3 * X.NA) ^ 2) :=
            mul_le_mul_of_nonneg_left hD2 (sq_nonneg _)
        _ = dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 := by ring
    have hQ : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    have hS : 0 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hk0.le) hrd
    have hn6 : (n : ℝ) ^ 6 ≤ ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hfin) 6
    have hinv : ep0 * ep0⁻¹ = 1 := mul_inv_cancel₀ hepne
    have heq : (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 * dE E ^ 2 *
        (X.NA : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * rdE E / ep0) * X.k0 * (16 * ep0) =
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      linear_combination (16 * (fdeg E : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 *
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * (X.NC : ℝ) ^ 2 * rdE E * X.k0) * hinv
    have hP : 0 ≤ dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 := by
      positivity
    have h6 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_left hn6 hQ
    have hrhs : dE E ^ 2 * (X.NA : ℝ) ^ 2 * (n : ℝ) ^ 6 ≤
        16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
          ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by
      by_cases hN : ((2 * fdeg E * (r - 2) : ℕ) : ℝ) = 0
      · have hP0 : dE E ^ 2 * (X.NA : ℝ) ^ 2 * ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6 = 0 := by
          rw [hN]; ring
        have h5 : 0 ≤ 16 * ((fdeg E : ℝ) ^ 2 * (dE E ^ 2 * (X.NA : ℝ) ^ 2 *
            ((2 * fdeg E * (r - 2) : ℕ) : ℝ) ^ 6)) * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) :=
          mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hP)) hS
        linarith
      · have hN' : 2 * fdeg E * (r - 2) ≠ 0 := by exact_mod_cast hN
        have hf0 : fdeg E ≠ 0 := fun h => hN' (by simp [h])
        have hr : 0 < r := Nat.pos_of_ne_zero (fun h => hN' (by simp [h]))
        have hk : 2 ≤ (X.NC : ℝ) ^ 2 * X.k0 * rdE E := by
          apply DiscriminantTraceBounds.two_le_normSq_mul_rootDisc <;> assumption
        have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) ^ 2 := by
          have h1 : (1 : ℝ) ≤ fdeg E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf0
          nlinarith
        have h7 : 2 ≤ (fdeg E : ℝ) ^ 2 * ((X.NC : ℝ) ^ 2 * X.k0 * rdE E) := by nlinarith
        have h8 := mul_le_mul_of_nonneg_left h7 hP
        linarith
    exact le_of_mul_le_mul_right (hlhs.trans (hrhs.trans_eq heq.symm)) (mul_pos (by norm_num) hep)
  refine ⟨(μ : Fin r → E), μ.2, ?_⟩
  intro u hu τ
  have hsm : ∀ (c : ℝ) (v : Fin r → ℂ),
      X.Hf z τ (u τ) (c • v) = (c : ℂ) * X.Hf z τ (u τ) v := by
    intro c v
    have hcv : c • v = (c : ℂ) • v := (Complex.coe_smul c v).symm
    rw [hcv, UnipotentCoefficientShift.Hf_smul_right, Complex.conj_ofReal]
  have hkey : δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
      hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV (μ : Fin r → E)) τ) =
      X.Hf z τ (u τ) (w.val τ) := by
    rw [hw_eq, VT.val_sub, VT.val_smul, Pi.sub_apply, Pi.smul_apply, MajorantOperators.Hf_sub_right,
      ← hd u hu τ, DiscreteLatticeMinimum.Bmap_val, RealTangentSpace.phi_val]
    congr 1
    rw [hsm]
    simp only [MajorantOperators.Bop]
    rw [UnipotentCoefficientShift.Hf_smul_right, Data.Hf_eq_jp, X.hermC_jp_jp hz1]
    simp only [map_mul, map_neg, map_ofNat, MajorantOperators.conj_purely_imaginary_generator]
    push_cast
    ring
  rw [hkey, FinrankRieszBounds.maj_csmul hz1]
  have hc : X.k0 * X.maj z τ (Data.emb τ.1 ξ) = 1 := by
    have h2 := hz'.2 τ
    simp only [Data.c] at h2
    rw [X.ξ0_abs τ] at h2
    linear_combination h2
  have hme : 0 ≤ X.maj z τ (Data.emb τ.1 ξ) := MajorantOperators.maj_nonneg hz1 τ _
  have hmu : 0 ≤ X.maj z τ (u τ) := MajorantOperators.maj_nonneg hz1 τ _
  have hcs := MajorantOperators.Hf_cs hz1 τ (u τ) (w.val τ)
  have hmw : X.maj z τ (w.val τ) ≤ ‖w‖ ^ 2 := by
    apply RealTangentSpace.maj_le_norm_sq
  calc ‖X.Hf z τ (u τ) (w.val τ)‖ ^ 2 * X.maj z τ (Data.emb τ.1 ξ)
      ≤ (X.maj z τ (u τ) * X.maj z τ (w.val τ)) * X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right hcs hme
    _ ≤ (X.maj z τ (u τ) * (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.k0)) *
        X.maj z τ (Data.emb τ.1 ξ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmw.trans hwM) hmu) hme
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) *
        (X.k0 * X.maj z τ (Data.emb τ.1 ξ)) := by ring
    _ = frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ) := by
        rw [hc, mul_one]

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpBasisExistence
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma herm_add_right' (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, HermitianPairingAlgebra.cc_add, mul_add, Finset.sum_add_distrib]

lemma herm_sum_left' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) : herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianPairingAlgebra.herm_add_left, ih]

lemma herm_sum_right' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) : herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm, cc]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right', ih]

def hxi (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x ξ
  map_add' x y := HermitianTraceFormVanishing.herm_add_left G x y ξ
  map_smul' a x := HermitianTraceFormVanishing.herm_smul_left G a x ξ

theorem exists_beta (X : Data E r) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∃ β : Fin (r - 2) → Fin r → E, (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 →
        ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) := by
  classical
  set f := hxi X.Gm ξ with hf
  have hfx : ∀ x, f x = herm X.Gm x ξ := fun _ => rfl

  have hw : (fun b => cc (ξ b)) ≠ 0 := by
    intro h
    apply hξ0
    funext b
    have hb := congrFun h b
    simp only [Pi.zero_apply, cc] at hb
    simpa using hb
  obtain ⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))
  have hfa : f (Pi.single a 1) ≠ 0 := by
    rw [hfx]
    convert ha using 1
    simp [herm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsurj : Function.Surjective f := fun y =>
    ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩
  set K := LinearMap.ker f with hK
  have hξK : ξ ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hξξ
  have hrange : Module.finrank E (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hKr : Module.finrank E K = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    have h2 : 1 + Module.finrank E K = r := this
    omega
  have hKpos : 0 < Module.finrank E K := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    apply hξ0
    have : ξ ∈ (⊥ : Submodule E (Fin r → E)) := h ▸ hξK
    simpa using this
  have hr2 : 2 ≤ r := by omega
  set ξK : K := ⟨ξ, hξK⟩ with hξKdef
  have hξK0 : ξK ≠ 0 := fun h => hξ0 (congrArg Subtype.val h)
  set S : Submodule E K := E ∙ ξK with hS
  have hQ : Module.finrank E (K ⧸ S) = r - 2 := by
    have h0 := Submodule.finrank_quotient_add_finrank S
    have h1 : Module.finrank E S = 1 := by rw [hS]; exact finrank_span_singleton hξK0
    rw [h1, hKr] at h0
    have h2 : Module.finrank E (K ⧸ S) + 1 = r - 1 := h0
    omega
  let bQ := Module.finBasisOfFinrankEq E (K ⧸ S) hQ
  let βK : Fin (r - 2) → K := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose
  have hβK : ∀ k, Submodule.Quotient.mk (p := S) (βK k) = bQ k := fun k =>
    (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec
  have hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK := by
    intro y
    set c := bQ.repr (Submodule.Quotient.mk y) with hc
    refine ⟨c, ?_⟩
    have hmk : Submodule.Quotient.mk (p := S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by
      have h := map_sum S.mkQ (fun k => c k • βK k) Finset.univ
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h
      exact h
    have hq : Submodule.Quotient.mk (p := S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by
      rw [hmk, hc, bQ.sum_repr]
    rw [Submodule.Quotient.eq] at hq
    have hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK := hq
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hq'
    exact ⟨e, by rw [he]; abel⟩
  refine ⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩
  · have hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) := by
      intro y _
      obtain ⟨c, e, rfl⟩ := hdecK y
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨k.succ, by simp⟩
      · exact Submodule.subset_span ⟨0, by simp⟩
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, hKr]; omega)
    have hmap := hli.map' K.subtype (Submodule.ker_subtype K)
    have heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) =
        (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]
    exact heq ▸ hmap
  · intro x hx
    have hxK : x ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hx
    obtain ⟨c, e, he⟩ := hdecK ⟨x, hxK⟩
    refine ⟨c, e, ?_⟩
    have := congrArg Subtype.val he
    simpa [ξK] using this

variable (X : DataX E r)

def LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {c | ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L'}
  add_mem' := by
    rintro c c' ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨e + e', ?_⟩
    have h : ∑ k, (c + c') k • β k + (e + e') • ξ =
        (∑ k, c k • β k + e • ξ) + (∑ k, c' k • β k + e' • ξ) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    rw [h]
    exact X.L'.add_mem he he'
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨e, he⟩
    refine ⟨(a : E) * e, ?_⟩
    have h : ∑ k, (a • c) k • β k + ((a : E) * e) • ξ = a • (∑ k, c k • β k + e • ξ) := by
      rw [integer_smul_eq_coe_smul a c, integer_smul_eq_coe_smul a (∑ k, c k • β k + e • ξ)]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
    rw [h]
    exact X.L'.smul_mem a he

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PivotNeg
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma Bf_single (Z : X.Coord) (τ : X.Ψ) (j k : Fin r) :
    Bf X Z τ (Pi.single j 1) (Pi.single k 1) = Gp X Z τ j k := by
  unfold Bf
  simp [Pi.single_apply]

lemma Bf_split (Z : X.Coord) (τ : X.Ψ) (v t : Fin r → ℂ) (h1 : Bf X Z τ v t = 0) :
    Bf X Z τ v v = Bf X Z τ (v - t) (v - t) - Bf X Z τ t t := by
  have h2 : Bf X Z τ t v = 0 := by rw [Bf_conj, h1, map_zero]
  simp only [Bf_sub_left, Bf_sub_right]
  rw [h1, h2]
  ring

lemma blk_Gp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (c : Fin r) : (blk (Gp X Z τ) c).det ≠ 0 := by
  rw [← gram_xZ X ho Z τ]
  exact blk_det X (xZ_mem_dom X hx ho hZ) τ c

lemma dOf_eq {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) (k : Fin r) :
    dOf X (X.xZ x Z) τ k = Bf X Z τ (fun a => uMat (Gp X Z τ) a k) (fun a => uMat (Gp X Z τ) a k) := by
  have hG : gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := gram_xZ X ho Z τ
  unfold dOf uOf
  rw [hG]
  set M := mat (X.xZ x Z) τ with hM
  set U := uMat (Gp X Z τ) with hU
  have hcol : col (M * U) k = ∑ a, U a k • col M a := by
    funext i
    simp [col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  show hermC τ.1 X.Gm (col (M * U) k) (col (M * U) k) = _
  rw [hcol, hermC_quad]
  unfold Bf
  rw [← hG]
  rfl

lemma pivot_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    1 - X.zN Z ^ 2 ≤ (dOf X (X.xZ x Z) τ k).re ∧ (dOf X (X.xZ x Z) τ k).re ≤ 1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ k]
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  have hvgt : ∀ b, k < b → v b = 0 := by
    intro b hb
    simp [hv, uMat, hb.ne', not_lt.mpr hb.le]
  set t : Fin r → ℂ := fun b => if b < k then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by simp [ht, not_lt.mpr hb]
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have hsingle : v - t = Pi.single k 1 := by
    funext b
    rcases lt_trichotomy b k with hb | hb | hb
    · simp [ht, hb, hb.ne]
    · rw [hb]
      simp [ht, hvk]
    · simp [ht, not_lt.mpr hb.le, hvgt b hb, hb.ne']
  rw [hsingle, Bf_single] at hsplit
  have hvn : ∀ m, v (nI X m) = 0 := fun m => hvgt _ (by
    rw [Fin.lt_def]
    simp [nI]
    omega)
  have hlow := Bf_pos_ge X Z τ v hvn
  have hkk : Fin.castLE X.p0_le (⟨k, hk⟩ : Fin X.p0) = k := Fin.ext rfl
  have hnsq : 1 ≤ nsq (Pv X v) := by
    unfold nsq Pv
    have := Finset.single_le_sum (f := fun j : Fin X.p0 => ‖v (Fin.castLE X.p0_le j)‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ (⟨k, hk⟩ : Fin X.p0))
    simp only [hkk, hvk, norm_one, one_pow] at this
    exact this
  have htn : ∀ m, t (nI X m) = 0 := fun m => ht0 _ (by
    rw [Fin.le_def]
    simp [nI]
    omega)
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hGkk : (Gp X Z τ k k).re ≤ 1 := by
    rw [← hkk, Gp_pp]
    simp only [if_true, Complex.sub_re, Complex.one_re, Complex.re_sum]
    have : 0 ≤ ∑ m, (Z τ m ⟨k, hk⟩ * conj (Z τ m ⟨k, hk⟩)).re :=
      Finset.sum_nonneg fun m _ => by
        rw [Complex.mul_conj]
        simp [Complex.normSq_nonneg]
    linarith
  constructor
  · nlinarith
  · rw [hsplit, Complex.sub_re]
    nlinarith

lemma pivot_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (m0 : Fin (r - X.p0)) : (dOf X (X.xZ x Z) τ (nI X m0)).re ≤ -1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ (nI X m0)]
  set k := nI X m0 with hkdef
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  set t : Fin r → ℂ := fun b => if (b : ℕ) < X.p0 then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by
    have hb' : ¬ ((b : ℕ) < X.p0) := by
      rw [Fin.le_def] at hb
      simp [hkdef, nI] at hb
      omega
    simp [ht, hb']
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have htn : ∀ m, t (nI X m) = 0 := fun m => by simp [ht, nI]
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hre := Bf_self_re X Z τ (v - t)
  have hP0 : Pv X (v - t) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp [Fin.coe_castLE]
    simp [Pv, ht, ha]
  have hNm : Nv X Z τ (v - t) m0 = 1 := by
    have h1 : ∀ c : Fin X.p0, (v - t) (Fin.castLE X.p0_le c) = 0 := fun c => congrFun hP0 c
    simp only [Nv, h1, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Pi.sub_apply, ← hkdef, hvk, ht0 k le_rfl, sub_zero]
  have hN : 1 ≤ nsq (Nv X Z τ (v - t)) := by
    unfold nsq
    have := Finset.single_le_sum (f := fun j => ‖Nv X Z τ (v - t) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ m0)
    simp only [hNm, norm_one, one_pow] at this
    exact this
  have hn0 : nsq (0 : Fin X.p0 → ℂ) = 0 := by simp [nsq]
  rw [hsplit, Complex.sub_re, hre, hP0, hn0]
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

