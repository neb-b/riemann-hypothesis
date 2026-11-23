module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0138
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixRightTranslate
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

section entries

theorem ptEntry_cons (s1 : ℕ) (t1 : ℂ) (rest : C.LPt) (a b : ℕ) :
    D.ptEntry ((s1, t1) :: rest) a b =
      if a < s1 ∧ b < s1 then (if a + b + 1 = s1 then t1 else 0)
      else if s1 ≤ a ∧ s1 ≤ b then D.ptEntry rest (a - s1) (b - s1) else 0 := rfl

theorem ptEntry_append (h : C.LPt) (s : ℕ) (t : ℂ) (a b : ℕ) :
    D.ptEntry (h ++ [(s, t)]) a b =
      if a < D.ptSize h ∧ b < D.ptSize h then D.ptEntry h a b
      else if D.ptSize h ≤ a ∧ D.ptSize h ≤ b then
        (if a - D.ptSize h < s ∧ b - D.ptSize h < s ∧ (a - D.ptSize h) + (b - D.ptSize h) + 1 = s then t else 0)
      else 0 := by
  induction h generalizing a b with
  | nil =>
    simp only [List.nil_append, D.ptSize, List.map_nil, List.sum_nil, Nat.sub_zero]
    rw [ptEntry_cons]
    simp only [D.ptEntry]
    split_ifs <;> first | rfl | omega
  | cons blk h ih =>
    obtain ⟨s1, t1⟩ := blk
    have hsz : D.ptSize ((s1, t1) :: h) = s1 + D.ptSize h := by simp [D.ptSize]
    rw [List.cons_append, hsz, ptEntry_cons, ih]
    split_ifs <;> first | rfl | omega | (rw [ptEntry_cons]; split_ifs <;> first | rfl | omega)

theorem ptMatN_zb (h : C.LPt) (s : ℕ) (t : ℂ) (n : ℕ) (hn : n = D.ptSize h + s) (a b : Fin n) :
    D.ptMatN (h ++ [(s, t)]) n a b = C3.Zb (D.ptSize h) s (D.ptMatN h (D.ptSize h)) t a.val b.val := by
  unfold D.ptMatN
  rw [ptEntry_append]
  unfold C3.Zb
  have ha := a.isLt
  have hb := b.isLt
  by_cases h1 : a.val < D.ptSize h
  · rw [dif_pos h1]
    by_cases h2 : b.val < D.ptSize h
    · rw [if_pos ⟨h1, h2⟩, dif_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega), dif_neg h2]
  · rw [dif_neg h1, if_neg (fun h => h1 h.1)]
    by_cases h2 : D.ptSize h ≤ b.val
    · rw [if_pos ⟨by omega, h2⟩]
      by_cases h3 : a.val - D.ptSize h + (b.val - D.ptSize h) + 1 = s
      · rw [if_pos ⟨by omega, by omega, h3⟩, if_pos ⟨h2, by omega, by omega, h3⟩]
      · rw [if_neg (fun h => h3 h.2.2), if_neg (fun h => h3 h.2.2.2)]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.1)]

end entries

section point

variable {k r : ℕ}

theorem corner_matrix_right_translate (z z' : Fin (2 * r + k + 1) → ℂ) (γ n0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hn0 : n0 ∈ C3.N0set k r z') : Zhat k r z z' (γ * n0) = Zhat k r z z' γ := by
  ext a b
  unfold Zhat
  rw [← Matrix.mulVec_mulVec]
  congr 2
  unfold fvec
  split_ifs with hb
  · exact hn0.2.1 ⟨b.val, hb⟩
  · exact hn0.2.2.1

theorem dmin_zb (z z' : Fin (2 * r + k + 1) → ℂ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x a b = C3.Zb i0 s hh t a.val b.val) (l : Fin (r + 2)) :
    Dmin k r z z' x l = C3.Dlead i0 s hh t l.val := by
  unfold Dmin C3.Dlead
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, hZ]
  rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}

theorem La_one (hD : IsOpen D) (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) : La hD K hK x₁ 1 = K x₁ := by
  show ((vK hD K hK : VS k r 0 D E) : Q.Mx k r → E) x₁ = K x₁
  exact cut_of_mem K hx₁

theorem top_poly (hD : IsOpen D) (z z' yb : Fin (2 * r + k + 1) → ℂ) (i0 s : ℕ) (hs : 2 ≤ s) (hj : i0 + s = r + 1)
    (hh : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (hdet : hh.det ≠ 0) (ht : t ≠ 0) (x₁ : Q.Mx k r)
    (hx₁ : x₁ ∈ Q.Glev k r 0 ∩ D) (hz' : inWb k r z') (hyb : inWb k r yb) (hzy : herm (Hpk k r) z' yb = t)
    (hnf1 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val ≠ i0 →
      xi0 x₁ a p = if p.val < r ∧ p.val ≠ i0 then C3.Zb i0 s hh t a.val p.val else 0)
    (hnf2 : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val = i0 → xi0 x₁ a p = herm (Hpk k r) (bvec p) yb)
    (hZ : ∀ a b : Fin (r + 1), Zhat k r z z' x₁ a b = C3.Zb i0 s hh t a.val b.val)
    (K : Q.Mx k r → E) (hK : Q.SmoothLev k r 0 D K)
    (hR : ∀ g ∈ Q.Glev k r 0 ∩ D, ∀ p q, C3.InNp k r p q → Q.EH k r p q K g = C3.dpsiP k r z' p q • K g) :
    ∃ c : Fin (i0 + 1) → E, c (Fin.last i0) = ((-1) ^ (s - 1) / t) • K x₁ ∧
      ∀ y : ℝ, (Dmin k r z z' x₁ (Fin.last _))⁻¹ •
          C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) K x₁ =
        ∑ n : Fin (i0 + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  have hi0 : i0 ≤ r := by omega
  have hDl : ∀ l : Fin (r + 2), Dmin k r z z' x₁ l = C3.Dlead i0 s hh t l.val := dmin_zb z z' x₁ i0 s hh t hZ
  have hDi0 : C3.Dlead i0 s hh t i0 = hh.det := (Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb i0 s hh t).1
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity (Module.End ℂ (VS k r 0 D E)) k r (E0 hD) (xi0 x₁) i0 hi0
  have hdetxi : (Matrix.of fun a b : Fin i0 => xi0 x₁ (Fin.castLE hi0 a) (C3.xR k r i0 hi0 b)).det = hh.det := by
    rw [det_upper_minor_eq_minor z z' x₁ i0 hi0, hDl, ← hDi0]

  have hpoly : PolyRepN i0 (fun u => (Dmin k r z z' x₁ (Fin.last _))⁻¹ • C3.AAop k r r le_rfl u K x₁)
      (((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁) := by
    refine ⟨fun l => if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) • ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩))
      else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁, by simp, fun u => ?_⟩
    have hE := Formalism.FourierDecayAlt.P.SignAntidiagonal.column_indicator_expansion (Module.End ℂ (VS k r 0 D E)) E k r z' yb (E0 hD) (La hD K hK x₁)
      (xi0 x₁) i0 s hh t u hs hj (La_rule hD z' K hK hR x₁) hdet ht hz' hyb hzy hnf1 hnf2
    rw [La_AAx hD K hK x₁ hx₁] at hE
    have hlast : Dmin k r z z' x₁ (Fin.last (r + 1)) = C3.Dlead i0 s hh t (r + 1) := by rw [hDl]; rfl
    simp only
    rw [hlast, hE, hDi0, hB u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, Finset.sum_range_succ, dif_neg (lt_irrefl i0)]
    have hm : ∀ (c : ℂ) (X : Module.End ℂ (VS k r 0 D E)),
        La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c * X) = c • La hD K hK x₁ X := by
      intro c X
      rw [← Algebra.smul_def, map_smul]
    have ha : ∀ c : ℂ, La hD K hK x₁ (algebraMap ℂ (Module.End ℂ (VS k r 0 D E)) c) = c • K x₁ := by
      intro c
      rw [← mul_one (algebraMap ℂ _ c), hm, La_one hD K hK x₁ hx₁]
    rw [ha, Finset.sum_range (fun l => u ^ l • if hl : l < i0 then ((-1 : ℂ) ^ (s - 1) * t⁻¹) •
      ((hh.det)⁻¹ • La hD K hK x₁ (B ⟨l, hl⟩)) else ((-1 : ℂ) ^ (s - 1) * t⁻¹) • K x₁)]
    simp only [hm, dif_pos (Fin.isLt _), Fin.eta]
    rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      rw [smul_comm ((hh.det)⁻¹) (u ^ (l : ℕ)), smul_comm ((-1 : ℂ) ^ (s - 1) * t⁻¹) (u ^ (l : ℕ))]
    · simp only [smul_smul]
      rw [hdetxi]
      congr 1
      field_simp
  obtain ⟨c, hc, hf⟩ := polyRepN_shift hpoly (((2 * r + k : ℕ) : ℂ) / 2)
  refine ⟨fun n => c n.val, ?_, fun y => ?_⟩
  · simp only [Fin.val_last]
    rw [hc, div_eq_mul_inv]
  · have := hf (y : ℂ)
    simp only at this
    rw [this, Fin.sum_univ_eq_sum_range (fun l => ((y : ℂ) ^ l) • c l)]

end point

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRConst
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

private theorem hsVec_finset_sum_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (c : ι → ℂ) (A : ι → Wq →L[ℂ] Wp) : B.hsVec (∑ i, c i • A i) = ∑ i, c i • B.hsVec (A i) := by
  ext j
  simp [B.hsVec]

private theorem hsVec_injective_apply {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A C : Wq →L[ℂ] Wp)
    (h : B.hsVec A = B.hsVec C) : A = C := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = C (stdOrthonormalBasis ℂ Wq i) := fun i => by
    have := congrArg (fun v => v i) h
    simpa [B.hsVec] using this
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using h' i)

private theorem toSm_smul_hermitian_curvature (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu]
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, smul_zero, dite_eq_left (Subalgebra.zero_mem _)]
      rfl
    · rw [smul_zero, dite_eq_right]
      intro hm
      apply hu
      have := Subalgebra.smul_mem _ hm c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem radial_constant_of_point_and_line (hPt : GTKPt) (hLine : GTKLine) : GTRConst := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d h
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d h
  obtain ⟨e1, he1F, -⟩ := gauge_kappa_of_point_line hPt hLine Wp Wq P Bs X d h
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [h.1.2.2.2.1, h.1.2.2.2.2.1]
    rfl
  set ζ0 : ℂ := ((|P.TT| + 1 : ℝ) : ℂ) with hζ0def
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    nlinarith [le_abs_self P.TT, abs_nonneg P.TT]
  have hFib : ∀ ζ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    unfold NF.Fib
    rw [h.2.2.1.2 ζ ζ0 (hTT ▸ hζ) (hTT ▸ hζ0)]
  choose E hEmem hEQ hEnorm hEuniq using fun ρ => hLine Wp Wq P Bs X d h Qr hQ ζ0 hζ0 ρ
  have hEQ' : ∀ ρ σ, E ρ ∘SL Qr σ = if ρ = σ then E ρ else 0 := by
    intro ρ σ
    calc E ρ ∘SL Qr σ = (E ρ ∘SL Qr ρ) ∘SL Qr σ := by rw [hEQ ρ]
      _ = E ρ ∘SL (Qr ρ ∘SL Qr σ) := ContinuousLinearMap.comp_assoc _ _ _
      _ = _ := by
        rw [hQ.1 ρ σ]
        split_ifs <;> simp [hEQ ρ]
  have hinQ : ∀ ρ σ (C : Wq →L[ℂ] Wp), inner ℂ (B.hsVec (E ρ)) (B.hsVec (C ∘SL Qr σ)) =
      if ρ = σ then inner ℂ (B.hsVec (E ρ)) (B.hsVec C) else 0 := by
    intro ρ σ C
    rw [GTK.hs_comp_right _ _ _ (hQ.2.2.1 σ), hEQ' ρ σ]
    split_ifs
    · rfl
    · rw [GTK.hs_expand]
      simp
  have horth : ∀ ρ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (E σ)) = if ρ = σ then 1 else 0 := by
    intro ρ σ
    have hh := hinQ ρ σ (E σ)
    rw [hEQ σ] at hh
    rw [hh]
    split_ifs with hρσ
    · subst hρσ
      exact hEnorm ρ
    · rfl
  have hv : Orthonormal ℂ (fun σ => B.hsVec (E σ)) := orthonormal_iff_ite.mpr horth
  have hw : Orthonormal ℂ (fun σ => B.hsVec (e1 σ ζ0)) := orthonormal_iff_ite.mpr (he1F.2 ζ0 hζ0).2.1
  have hspan1 : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    intro Y hY
    rw [(he1F.2 ζ0 hζ0).2.2 Y hY, hsVec_finset_sum_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hle : Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) ≤
      Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact hspan1 _ (hEmem σ)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card hv.linearIndependent, finrank_span_eq_card hw.linearIndependent])
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have hm : B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) := heq ▸ hspan1 Y hY
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    have hcoef : ∀ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) = c σ := by
      intro σ
      rw [← hc]
      exact hv.inner_right_fintype c σ
    apply hsVec_injective_apply
    rw [hsVec_finset_sum_smul]
    simp only [hcoef]
    exact hc.symm
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ =>
    ⟨fun ρ => (hFib ζ hζ).symm ▸ hEmem ρ, horth, fun Y hY => hexp Y (hFib ζ hζ ▸ hY)⟩⟩, ?_, fun ρ ζ ζ' => rfl⟩
  intro f Φ
  funext ρ
  unfold trR MA.actA
  simp only [MA.kap, AlgHom.comp_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  have hR : rawR P Bs.μsec (fun ρ _ => E ρ) (↑((d.κ f).1 Φ)) ρ =
      f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (↑Φ) ρ := by
    funext q
    simp only [rawR, Pi.smul_apply, smul_eq_mul]
    rw [hQ.2.2.2 f Φ q, GTK.hs_comp_sum]
    simp only [hinQ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  symm
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    rfl
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ
  · rw [if_pos rfl, hR, toSm_smul_hermitian_curvature]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_gauge_constant_holds : GTRConst := GTK.radial_constant_of_point_and_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTrans
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem vl_add (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (Φ + Ψ) ρ q = SSC.vl P Bs e Φ ρ q + SSC.vl P Bs e Ψ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]

theorem vl_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (c • Φ) ρ q = c * SSC.vl P Bs e Φ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]
  ring

end vals

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 =
        MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzQ MA.DAlg.dzP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vz 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [h0', map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 =
        MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzbQ MA.DAlg.dzbP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vzb 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [h0', map_zero]

theorem theta_fst {V : Type} [AddCommGroup V] [Module ℂ V] (P : M.Par) (d : Q.NFData P (Q.Pr V)) (Φ : V) :
    (ThetaNF P d).1 Φ = d.L.ζ.1 (d.L.nab.1 Φ) + d.L.ζb.1 (d.L.nabs.1 Φ) +
      (d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Φ +
      d.L.TT • d.L.GGi.1 ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Φ) := by
  unfold ThetaNF
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem radial_gauge_transition_holds : GTRTrans := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ
  classical
  have hpl := hyp.1
  have hk2 := hyp.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have hLTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0
  have t0 : trR P Bs e Ψ0 ρ = 1 := by
    rw [hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]
    simp [dTy]
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1 := by
    unfold SSC.vl
    rw [t0]
    rfl
  have t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ) := by
    rw [(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]
  have t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ) := by
    rw [(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]
  have v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ := by
    unfold SSC.vl
    rw [t1, fnZ_val P (hAB ρ).1]
  have v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ := by
    unfold SSC.vl
    rw [t2, fnZ_val P (hAB ρ).2]

  have vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m := by
    unfold SSC.vl
    rw [hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]
    show m * 1 = m
    ring
  have v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  have v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 =
      ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  clear_value Ψ0

  have hfn := fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0
  rw [GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he,
    GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2,
    v3, v4, v1, v2, hLTT] at vm
  have hq : q0.1.2 = ζ := rfl
  rw [hq] at vm
  have hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0 := by
    have : P.TT < Complex.normSq ζ := hζ
    intro h0
    have h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h1
    linarith
  rw [← vm]
  push_cast
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

