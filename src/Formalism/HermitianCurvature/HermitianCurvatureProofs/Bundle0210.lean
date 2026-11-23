module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0131
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0199

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExponentialSymbolHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

namespace ExponentialSymbolLetters

variable {k r : ℕ} (τ : B.Mat k r → ℂ) (u s : ℂ)

def phi (t : Polynomial ℂ × List (B.Mat k r)) : ℂ := t.1.eval u * s ^ t.2.length * (t.2.map τ).prod

theorem head (p : Polynomial ℂ) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (p * t.1, t.2)).map (phi τ u s)).sum = p.eval u * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul]
  ring

theorem letter (d : ℂ) (X : B.Mat k r) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((l.map fun t => (Polynomial.C d * t.1, X :: t.2)).map (phi τ u s)).sum =
      (d * s * τ X) * (l.map (phi τ u s)).sum := by
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, phi, Polynomial.eval_mul, Polynomial.eval_C, List.length_cons, pow_succ,
    List.map_cons, List.prod_cons]
  ring

theorem letters (L : List (ℂ × B.Mat k r)) (l : List (Polynomial ℂ × List (B.Mat k r))) :
    ((L.flatMap fun dX => l.map fun t => (Polynomial.C dX.1 * t.1, dX.2 :: t.2)).map (phi τ u s)).sum =
      s * (L.map fun dX => dX.1 * τ dX.2).sum * (l.map (phi τ u s)).sum := by
  induction L with
  | nil => simp
  | cons dX L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, letter, ih, List.map_cons, List.sum_cons]
    ring

theorem all (gs : List (GenW k r)) : ((fexp gs).map (phi τ u s)).sum =
    (gs.map fun gn => gn.1.eval u + s * (gn.2.map fun dX => dX.1 * τ dX.2).sum).prod := by
  induction gs with
  | nil => simp [fexp, phi]
  | cons gn gs ih =>
    rw [fexp, List.map_append, List.sum_append, head, letters, List.map_cons, List.prod_cons, ← ih]
    ring

end ExponentialSymbolLetters

theorem exponential_symbol_holds : FExpSymb := by
  intro k r gens τ u s
  exact ExponentialSymbolLetters.all τ u s gens

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
section
open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lift

variable {k i r' : ℕ}

theorem ιLev_apply_lev (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (p q : Fin (2 * r' + k + 1)) :
    ιLev k i r' g ⟨p.val + i, by omega⟩ ⟨q.val + i, by omega⟩ = g p q := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [ιLev]
  rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp

theorem ιLev_inj' {g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ}
    (h : ιLev k i r' g = ιLev k i r' g') : g = g' := by
  ext p q
  have := congrFun (congrFun h ⟨p.val + i, by omega⟩) ⟨q.val + i, by omega⟩
  rwa [ιLev_apply_lev, ιLev_apply_lev] at this

theorem contDiff_ιLev' : ContDiff ℝ ∞ (ιLev k i r') := by
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  unfold ιLev
  split_ifs
  · exact (contDiff_apply ℝ (fun _ => ℂ) _).comp (contDiff_apply ℝ (fun _ => (Fin (2 * r' + k + 1) → ℂ)) _)
  all_goals exact contDiff_const

theorem zeta_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    zetaL k (i + r') (liftVec k i r' z) (liftVec k i r' z') (Fin.last (i + r')) (ιLev k i r' g) =
      zetaL k r' z z' (Fin.last r') g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

theorem tz_lift (z : Fin (2 * r' + k + 1) → ℂ) : Tz k (i + r') (liftVec k i r' z) = Tz k r' z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

theorem ggl_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (g : Mx k r') :
    GGl k (i + r') (liftVec k i r' z) (liftVec k i r' z') (ιLev k i r' g) = GGl k r' z z' g := by
  unfold GGl; rw [zeta_lift, tz_lift, tz_lift]

theorem fnVal_lift (z z' : Fin (2 * r' + k + 1) → ℂ) (j : Fin 6) (g : Mx k r') :
    fnVal k (i + r') (liftVec k i r' z) (liftVec k i r' z') j (ιLev k i r' g) = fnVal k r' z z' j g := by
  unfold fnVal
  split <;> simp only [zeta_lift, ggl_lift]

theorem glev_lift (hr' : r' = 0) (g : Mx k r') :
    ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ↔ g ∈ Glev k r' (Fin.last r') := by
  have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
  have himg := QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k i r'
  have hG : ∀ x : Mx k r', x ∈ Glev k r' (Fin.last r') ↔ x ∈ UH (Hpk k r') := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, fun a _ => absurd a.isLt (by omega)⟩⟩
  rw [hl, himg, hG]
  constructor
  · rintro ⟨g0, hg0, e⟩
    rwa [← ιLev_inj' e]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem domR_lift (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (c' : Fin r' → ℂ) (g : Mx k r') :
    (c, ιLev k i r' g) ∈ DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') ↔ (c', g) ∈ DomR k r' zs zs' := by
  show (c ∈ OmX (i + r') ∧ ιLev k i r' g ∈ Glev k (i + r') (Fin.last (i + r')) ∧
      0 < GGl k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') (ιLev k i r' g)) ↔
    (c' ∈ OmX r' ∧ g ∈ Glev k r' (Fin.last r') ∧ 0 < GGl k r' zs zs' g)
  rw [glev_lift hr', ggl_lift]
  exact ⟨fun h => ⟨fun l => absurd l.isLt (by omega), h.2⟩, fun h => ⟨hc, h.2⟩⟩

def rsF {E : Type*} (c : Fin (i + r') → ℂ) (Φ : Fn k (i + r') E) : Fn k r' E := fun _ g => Φ c (ιLev k i r' g)

end lift

section rs

variable {k i r' : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rs_mem (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)} {Φ : Fn k (i + r') (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    rsF c Φ ∈ RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_lift hr' hc zs zs' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_lift hr' hc zs zs' x₀.1 x₀.2).2 hx₀)
    let e : (Fin r' → ℂ) × Mx k r' → (Fin (i + r') → ℂ) × Mx k (i + r') := fun x => (c, ιLev k i r' x.2)
    have he_c : ContDiff ℝ ∞ e := contDiff_const.prodMk (contDiff_ιLev'.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_lift hr' x.2).2 hg)
  · have hx' := (domR_lift hr' hc zs zs' x.1 x.2).2 hx
    show Φ c (ιLev k i r' (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k i r').2, (PI.QnLevBasicsW.level_group_homomorphism k i r').2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k i r' zs' h' hh')

def rsL (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) (zs zs' : Fin (2 * r' + k + 1) → ℂ)
    (π : Mx k (i + r') → (Wp →L[ℂ] Wp)) (π' : Mx k (i + r') → (Wq →L[ℂ] Wq)) :
    RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π' →ₗ[ℂ]
      RadSp k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y)) where
  toFun Φ := ⟨rsF c (Φ : Fn k (i + r') (Wq →L[ℂ] Wp)), rs_mem hr' hc Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hr' : r' = 0) {c : Fin (i + r') → ℂ} (hc : c ∈ OmX (i + r')) {zs zs' : Fin (2 * r' + k + 1) → ℂ}
  {π : Mx k (i + r') → (Wp →L[ℂ] Wp)} {π' : Mx k (i + r') → (Wq →L[ℂ] Wq)}

theorem t_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.t Y a b (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.t Y a b Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.t_apply Y a b _ (c', g) hx]
    show _ = (X₀.t Y a b Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.t_apply Y a b Φ (c, ιLev k i r' g) hx']
    have hl : (Fin.last (i + r')) = (⟨i, by omega⟩ : Fin (i + r' + 1)) := Fin.ext (by simp; omega)
    have h0 : (Fin.last r') = (0 : Fin (r' + 1)) := Fin.ext (by simp; omega)
    rw [hl, h0]
    exact (Formalism.FourierDecayAlt.P.level_transfer _ k i r' zs zs' Y a b ((Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c) g
      hx.2.1.1).symm
  · rw [(X.t Y a b (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.t Y a b Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

theorem fn_rs (X₀ : ActualOps k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π')
    (X : ActualOps k r' zs zs' (fun y => π (ιLev k i r' y)) (fun y => π' (ιLev k i r' y))) (j : Fin 6)
    (Φ : RadSp k (i + r') (liftVec k i r' zs) (liftVec k i r' zs') π π') :
    X.fn j (rsL hr' hc zs zs' π π' Φ) = rsL hr' hc zs zs' π π' (X₀.fn j Φ) := by
  apply Subtype.ext
  funext c' g
  by_cases hx : (c', g) ∈ DomR k r' zs zs'
  · have hx' := (domR_lift hr' hc zs zs' c' g).2 hx
    rw [X.fn_apply j _ (c', g) hx]
    show _ = (X₀.fn j Φ : Fn k (i + r') (Wq →L[ℂ] Wp)) c (ιLev k i r' g)
    rw [X₀.fn_apply j Φ (c, ιLev k i r' g) hx', fnVal_lift]
    rfl
  · rw [(X.fn j (rsL hr' hc zs zs' π π' Φ)).2.1 (c', g) hx]
    exact ((X₀.fn j Φ).2.1 _ (fun h => hx ((domR_lift hr' hc zs zs' c' g).1 h))).symm

end rs

end Formalism.FourierDecayAlt.P.WordCorrespondence
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow
section
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.QuantumDeterminants

theorem hasDerivAt_normPow (z v : ℂ) (hz : z ≠ 0) (n : ℕ) :
    HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ n)
      ((n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2)) 0 := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hsq : HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ 2) (2 * (v * conj z).re) 0 := by
    have := hline.norm_sq
    simpa [Complex.inner] using this
  have h0 : (fun t : ℝ => ‖z + t • v‖ ^ 2) 0 ≠ 0 := by simpa using pow_ne_zero 2 hz'
  have hsqrt := hsq.sqrt h0
  have hn : (fun t : ℝ => √(‖z + t • v‖ ^ 2)) = fun t => ‖z + t • v‖ := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hsqrt
  have hv : (n : ℝ) * ‖z + (0 : ℝ) • v‖ ^ (n - 1) * (2 * (v * conj z).re / (2 * √(‖z + (0 : ℝ) • v‖ ^ 2))) =
      (n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2) := by
    simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _)]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have hp := (hsqrt.pow n).congr_deriv hv
  exact hp

theorem hasDerivAt_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    HasDerivAt (fun t : ℝ => ∏ a, ‖(c + t • (Pi.single l v : Fin r → ℂ)) a‖ ^ n a)
      ((n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2)) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun a (t : ℝ) => ‖c a + t • (Pi.single l v : Fin r → ℂ) a‖ ^ n a)
    (fun a _ => hasDerivAt_normPow (c a) ((Pi.single l v : Fin r → ℂ) a) (hc a) (n a))
  have hv : (∑ i, (∏ j ∈ Finset.univ.erase i, ‖c j + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) j‖ ^ n j) •
        ((n i : ℝ) * ‖c i‖ ^ n i * (((Pi.single l v : Fin r → ℂ) i * conj (c i)).re / ‖c i‖ ^ 2))) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, zero_smul, add_zero, smul_eq_mul]
      rw [← Finset.mul_prod_erase Finset.univ (fun a => ‖c a‖ ^ n a) (Finset.mem_univ l)]
      ring
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ l) h
  exact h.congr_deriv hv

theorem fderiv_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c ∧
    fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
  classical
  have hd : DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c := by
    have := HasFDerivAt.finsetProd (u := Finset.univ) (x := c)
      (g := fun a (x : Fin r → ℂ) => ‖x a‖ ^ n a)
      (fun a _ => (((differentiableAt_apply (𝕜 := ℝ) a c).norm ℂ (hc a)).pow (n a)).hasFDerivAt)
    exact this.differentiableAt
  refine ⟨hd, ?_⟩
  have hline : HasDerivAt (fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ)) (Pi.single l v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l v : Fin r → ℂ)).const_add c
  have hc0 : c + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) = c := by simp
  have h1 : HasDerivAt ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) ∘ fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ))
      (fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v)) 0 := by
    have hd' := hd.hasFDerivAt
    rw [← hc0] at hd'
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    rwa [hc0] at this
  exact h1.unique (hasDerivAt_prodPow r n c hc l v)

theorem gauge_scalar (z : ℂ) (hz : z ≠ 0) (m : ℕ) (P : ℝ) :
    z * ((1 / 2 : ℂ) * ((((m : ℝ) * P * ((1 * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ) -
      Complex.I * (((m : ℝ) * P * ((Complex.I * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ))) = (P : ℂ) * ((m : ℂ) / 2) := by
  have h1 : (1 * conj z).re = z.re := by simp
  have h2 : (Complex.I * conj z).re = z.im := by simp
  have hc : ((z.re : ℂ)) - Complex.I * (z.im : ℂ) = conj z := by apply Complex.ext <;> simp
  have hzz : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hN0 : (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [h1, h2]
  push_cast
  calc _ = ((m : ℂ) * P / 2) * (z * ((z.re : ℂ) - Complex.I * (z.im : ℂ))) / (‖z‖ : ℂ) ^ 2 := by ring
    _ = (P : ℂ) * ((m : ℂ) / 2) := by
      have hN1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [hc, hzz]; field_simp

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.GaugeNormPower

theorem gauge_positivity : PBN.GaugeP := by
  intro E _ _ r n H c hc hH l
  obtain ⟨hψ, hψ'⟩ := fderiv_prodPow r n c hc l 1
  obtain ⟨-, hψI⟩ := fderiv_prodPow r n c hc l Complex.I
  have hfun : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') =
      (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H := by
    funext c'; exact Complex.coe_smul _ _
  rw [hfun]
  have hD : ∀ w, fderiv ℝ ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H) c w =
      (∏ a, ‖c a‖ ^ n a) • fderiv ℝ H c w + fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c w • H c := by
    intro w
    rw [(hψ.hasFDerivAt.smul hH.hasFDerivAt).fderiv]
    simp
  have hs : c l * ((1 / 2 : ℂ) * (((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l 1) : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l Complex.I) : ℝ) : ℂ))) =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) * ((n l : ℂ) / 2) := by
    rw [hψ', hψI]
    exact gauge_scalar (c l) (hc l) (n l) _
  simp only [pOp, if_pos hc, wirt]
  rw [hD, hD]
  simp only [← Complex.coe_smul]
  linear_combination (norm := module) hs • H c

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSumRight
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

def Flt (a : ℕ) (x : Fin (2 * r + k + 1) → ℂ) : Prop := ∀ i : Fin (2 * r + k + 1), a ≤ i.val → x i = 0

def hermL (y : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun x := herm (Hpk k r) x y
  map_add' x x' := herm_add_left x x' y
  map_smul' c x := by simp [herm_smul_left]

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ j ∈ s, f j) y = ∑ j ∈ s, herm (Hpk k r) (f j) y :=
  map_sum (hermL y) f s

theorem herm_sum_right {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (∑ j ∈ s, f j) = ∑ j ∈ s, herm (Hpk k r) x (f j) := by
  rw [herm_swap, herm_sum_left, star_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← herm_swap])

theorem mulVec_sum' {ι : Type*} (s : Finset ι) (g : B.Mat k r) (f : ι → Fin (2 * r + k + 1) → ℂ) :
    g *ᵥ (∑ j ∈ s, f j) = ∑ j ∈ s, g *ᵥ f j :=
  map_sum (Matrix.mulVecLin g) f s

theorem flt_decomp (a : ℕ) (ha : a ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y) :
    y = ∑ j : Fin a, y (eI k r ⟨j.val, by omega⟩) • bvec (eI k r ⟨j.val, by omega⟩) := by
  funext i
  rw [Finset.sum_apply]
  by_cases hi : i.val < a
  · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
    · have : eI k r ⟨i.val, by omega⟩ = i := Fin.ext rfl
      simp [this, bvec]
    · intro j _ hj
      have : eI k r ⟨j.val, by omega⟩ ≠ i := by
        intro e; apply hj; apply Fin.ext; have := congrArg Fin.val e; simpa [eI] using this
      simp [bvec, Ne.symm this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hy i (by omega)]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have : eI k r ⟨j.val, by omega⟩ ≠ i := by
      intro e; have := congrArg Fin.val e; simp [eI] at this; omega
    simp [bvec, Ne.symm this]

def Mblk (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  herm (Hpk k r) (g *ᵥ bvec (eI k r ⟨j.val, by omega⟩)) (bvec (eI k r ⟨i.val, by omega⟩))

theorem dmin_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r) :
    Dmin k r z z' g ⟨a, by omega⟩ = (Mblk g a ha).det := by
  unfold Dmin
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Mblk]
  have hi : (i : ℕ) < a := i.isLt
  have hj : (j : ℕ) < a := j.isLt
  rw [dite_eq_left (show i.val < r by omega), dite_eq_left (show j.val < r by omega)]

theorem dlem_i (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) (g *ᵥ y) (bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : Mblk g a ha *ᵥ y' = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [flt_decomp a ha y hy, mulVec_sum', herm_sum_left] at hc
    simp only [mulVec_smul, herm_smul_left] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [mulVec, dotProduct, Mblk, y']
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hy' : y' = 0 := Matrix.eq_zero_of_mulVec_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := congrFun hy' j
  rw [this, zero_smul]

theorem dlem_ii (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (a : ℕ) (ha : a ≤ r)
    (hD : Dmin k r z z' g ⟨a, by omega⟩ ≠ 0) (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt a y)
    (h : ∀ c : Fin r, c.val < a → herm (Hpk k r) y (g *ᵥ bvec (eI k r c)) = 0) : y = 0 := by
  rw [dmin_eq z z' g a ha] at hD
  set y' : Fin a → ℂ := fun j => y (eI k r ⟨j.val, by omega⟩)
  have hMy : star y' ᵥ* Mblk g a ha = 0 := by
    funext c
    have hc := h ⟨c.val, by omega⟩ c.isLt
    rw [herm_swap, star_eq_zero, flt_decomp a ha y hy, herm_sum_right] at hc
    simp only [herm_smul_right] at hc
    rw [Pi.zero_apply, ← hc]
    simp only [vecMul, dotProduct, Mblk, y', Pi.star_apply]
  have hy' : star y' = 0 := Matrix.eq_zero_of_vecMul_eq_zero hD hMy
  rw [flt_decomp a ha y hy]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : y (eI k r ⟨j.val, by omega⟩) = 0 := by
    have := congrFun hy' j
    simpa [y'] using this
  rw [this, zero_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

