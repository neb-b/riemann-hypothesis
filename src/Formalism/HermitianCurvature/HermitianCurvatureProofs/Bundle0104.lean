module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReflectionTransposeEntriesMem
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DwPt
section
open Matrix MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

private lemma scalar_pow_mul_diagonal {A S : Type} [Ring A] [Fintype S] [DecidableEq S] (a : A) (n : ℕ)
    (D : Ix S → A) :
    (Matrix.scalar (Ix S) a) ^ n * Matrix.diagonal D = Matrix.diagonal (fun e => a ^ n * D e) := by
  rw [← map_pow, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]

theorem dw_pt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (ws : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 ws)
    (Y₀ : ℝ) (e : Ix S) (p : Polynomial ℂ)
    (hp : ∀ ρ : M.Ty P, p.eval (M.xC P ρ (Y₀ : ℂ)) = Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)
    (y : Ix S → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r) (hx : (c, g) ∈ DomR P.k P.r z z')
    (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ) (hBs : IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs) (v : Wq) :
    (act ((Fr.ofWord L st ws).d L) y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g v =
      (((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) ^ ws.length) •
        (y e : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
          (Polynomial.aeval (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2)) p v) := by
  have hD' := hD
  obtain ⟨hPl, -, hAL, hQQ, hq, -, -, hLS⟩ := hD'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -⟩ := id hAL
  obtain ⟨κ, hκx, hκxi, -⟩ := Formalism.FourierDecayAlt.P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual
    Formalism.FourierDecayAlt.P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hxiw : ∀ l ∈ ws, st'.xi (l.pt + 1) = st.xi (l.pt + 1) ∧ st'.xi (l.pt - 1) = st.xi (l.pt - 1) := by
    intro l hl
    obtain ⟨-, h1, h2, -⟩ := hw.1.2.2.1 l hl
    exact ⟨(hκxi _ h1).symm, (hκxi _ h2).symm⟩
  have hc : (Fr.ofWord L st ws).c =
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e := by
    rw [← Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_c_congr L st st' rfl rfl ws hxiw,
      (Formalism.FourierDecayAlt.P.c_diagonal _ S P.r L st' (M.Ty P) κ (M.x0 P l0) (fun Y => hκx Y) (fun Y => rfl) ws).2.2,
      ← hq]
  have hd : (Fr.ofWord L st ws).d L = Matrix.diagonal (fun e => (L.ζ * L.ζb * L.GGi) ^ ws.length *
      κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)) := by
    rw [Fr.FrameData.d, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.ofWord_N, hc]
    exact scalar_pow_mul_diagonal _ _ _
  set K := κ (fun ρ => M.xC P ρ (Y₀ : ℂ)) with hKdef
  have hs : M.sgn P l0 ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hK : K.1 = X.fn 5 * X.t (Y₀ : ℂ) 1 1 := by
    have t := hLS.tau (Y₀ : ℂ)
    rw [hQQ, hκx, Formalism.FourierDecayAlt.P5.signed_coordinate_eq_sign_smul, map_smul] at t
    have t1 := congrArg (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) t
    rw [map_mul, map_smul, Matrix.smul_apply, map_smul] at t1
    change M.sgn P l0 • X.t (Y₀ : ℂ) 1 1 = L.GG.1 * (M.sgn P l0 • K.1) at t1
    rw [hGG, mul_smul_comm] at t1
    have h4 : X.fn 4 * K.1 = X.t (Y₀ : ℂ) 1 1 := (smul_right_injective _ hs t1).symm
    have h54 : X.fn 5 * X.fn 4 = 1 := by
      have := congrArg Prod.fst L.GGi_GG
      rw [hGGi, hGG] at this
      exact this
    rw [← h4, ← mul_assoc, h54, one_mul]
  have hκf : κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e) = Polynomial.aeval K p :=
    Formalism.FourierDecayAlt.P5.Kfp.kappa_aeval (NFData.mk L κ (fun _ => 0)) (Y₀ : ℂ) p _ hp
  have hκf1 : (κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 = Polynomial.aeval K.1 p := by
    rw [hκf]
    exact (Polynomial.aeval_algHom_apply (Formalism.FourierDecayAlt.P5.Kfp.fstAlg _) K p).symm
  have hT : ∀ (Ψ : RadSp P.k P.r z z' π π') (w : Wq),
      ((K.1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g w =
        (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g (qdet (Qr.EB π' Bs) ((Y₀ : ℂ) + ((P.k : ℂ) - 2) / 2) w) := by
    intro Ψ w
    rw [hK]
    exact Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hPl.2.1 hPl.2.2.1 hPl.2.2.2.2.2.2.2.1 hPl.2.2.2.2.2.2.2.2.1 hx Bs hBs _ Ψ w
  have hA := Formalism.FourierDecayAlt.P5.Kfp.aeval_act K.1 _ hT p
  have hpow := Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.pow_apply X L hAL ws.length
    ((κ (fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) ws e)).1 (y e)) (c, g) hx
  have hmul : ∀ a b : Pr (RadSp P.k P.r z z' π π'), (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  rw [hd, Formalism.FourierDecayAlt.P5.WordTransvectionCongruences.act_diagonal, hmul, Module.End.mul_apply, hpow,
    _root_.smul_apply, hκf1, hA]
  congr 1
  simp only [fnVal]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
  rfl

end

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMemOfKappa
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Inv

variable {A T : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype T]

theorem aeval_mem' (𝒜 : StarSubalgebra ℂ A) {x : A} (hx : x ∈ 𝒜) (p : Polynomial ℂ) :
    Polynomial.aeval x p ∈ 𝒜 := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.aeval_C]; exact 𝒜.algebraMap_mem a
  · rw [map_add (f := _)]; exact 𝒜.add_mem hp hq
  · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact 𝒜.mul_mem (𝒜.algebraMap_mem a) (𝒜.pow_mem hx _)

theorem inv_mem_of_kappa (κ : (T → ℂ) →ₐ[ℂ] A) (𝒜 : StarSubalgebra ℂ A) (f : T → ℂ) (hf : κ f ∈ 𝒜) :
    κ (fun ρ => (f ρ)⁻¹) ∈ 𝒜 := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  rw [he, ← Polynomial.aeval_algHom_apply]
  exact aeval_mem' 𝒜 hf p

variable {r : ℕ}

theorem x_eq_of_start (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st) (Y : ℂ) :
    st.x Y = L.GGi * st.QQ Y 1 1 := by
  rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]

theorem gens_of (𝒜 : StarSubalgebra ℂ A) (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st)
    (κ : (T → ℂ) →ₐ[ℂ] A) (x0 : T → ℂ → ℂ) (hx : ∀ Y, st.x Y = κ fun ρ => x0 ρ Y)
    (hxi : ∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (x0 ρ Y)⁻¹)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ 𝒜) : Gens 𝒜 L st := by
  have hxm : ∀ Y : ℂ, star Y = Y → st.x Y ∈ 𝒜 := fun Y hY => by
    rw [x_eq_of_start L st hst Y]
    exact 𝒜.mul_mem (hz _ (by simp [zfns])) (hQ Y hY 1 1)
  refine ⟨hz, hQ, hxm, fun Y hYs hY => ?_⟩
  rw [hxi Y hYs]
  exact inv_mem_of_kappa κ 𝒜 (fun ρ => x0 ρ Y) (by rw [← hx Y]; exact hxm Y hY)

end Inv

section Fn

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fnVal_conj (j : Fin 6) (g : Mx k r) : conj (fnVal k r z z' (fnConj j) g) = fnVal k r z z' j g := by
  fin_cases j <;> simp [fnVal, fnConj, map_inv₀]

theorem fn_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π'))
    (hU : IntOn μ U) (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U) (j : Fin 6) :
    mkP (X.fn j) (X.fn (fnConj j)) ∈ adjAlg μ U hU := by
  refine ⟨fun Φ hΦ => hfn j Φ hΦ, fun Φ hΦ => hfn _ Φ hΦ, fun c _ Φ _ Ψ _ => ?_⟩
  show pairAt μ (X.fn j Φ) Ψ c = pairAt μ Φ (X.fn (fnConj j) Ψ) c
  unfold pairAt
  congr 1
  funext g
  by_cases hx : (c, Matrix.of g) ∈ DomR k r z z'
  · have e1 := X.fn_apply j Φ (c, Matrix.of g) hx
    have e2 := X.fn_apply (fnConj j) Ψ (c, Matrix.of g) hx
    simp only at e1 e2
    rw [e1, e2, hsInner_smul_left', hsInner_smul_right', fnVal_conj]
  · have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off Φ hx
    have h1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off (X.fn j Φ) hx
    rw [h0, h1, hsInner_zero_left, hsInner_zero_left]

end Fn

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_tAdj (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U)
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  have hD' := hD
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, -⟩ := hAL
  have hz : ∀ g ∈ zfns L, g ∈ adjAlg μ U hU := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hζ]; exact fn_adj X μ U hU hfn 0
    · rw [hζi]; exact fn_adj X μ U hU hfn 1
    · rw [hζb]; exact fn_adj X μ U hU hfn 2
    · rw [hζbi]; exact fn_adj X μ U hU hfn 3
    · rw [hGG]; exact fn_adj X μ U hU hfn 4
    · rw [hGGi]; exact fn_adj X μ U hU hfn 5
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ adjAlg μ U hU := by
    intro Y hY i j
    rw [hQQ Y, Matrix.smul_apply]
    exact (adjAlg μ U hU).smul_mem (hT Y hY i j) _
  exact adjTop_of_gens P z z' π π' X μ L st K l0 hD' U hU hK
    (gens_of _ L st hst κ _ hx hxi hz hQ)

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ListMapSumApply
section
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def TermClause (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) (o κ : ℕ) (Θ : DiffOp k r Wp Wq) : Prop :=
  ∀ T ∈ Θ, ∃ (P : Mat k r → ℂ) (a b : Fin (r + 2) → ℕ) (c : ℕ)
      (es : List (Fin nf × List (Mat k r))), U.IsPolyDeg κ P ∧
      (∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) ∧
      T.word.length + (es.map fun e => e.2.length).sum ≤ o ∧ (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) ∧
      ∀ g ∈ C6.domL D L, T.coef g = (P g * C6.monoM D a b c g) • C6.Epart fib es g

theorem toFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (L : Finset (Fin (r + 2))) {o κ : ℕ} :
    ∀ Θ : DiffOp k r Wp Wq, TermClause D fib L o κ Θ →
      ∃ Lf : FS k r nf, (∀ e ∈ Lf, Good L e ∧ e.1.q.totalDegree ≤ κ ∧ e.2.length + fo e.1.es ≤ o) ∧
        (∀ T ∈ Θ, ∃ e ∈ Lf, e.2 = T.word) ∧
        ∀ (H : Mat k r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL D L, opApply Θ H g = shape D fib H Lf g := by
  intro Θ hΘ
  induction Θ with
  | nil => exact ⟨[], by simp, by simp, fun H g _ => by simp [opApply, shape]⟩
  | cons T Θ ih =>
    obtain ⟨Lf, h1, h2, h3⟩ := ih (fun T' hT' => hΘ T' (List.mem_cons_of_mem _ hT'))
    obtain ⟨P, a, b, c, es, ⟨q, hqdeg, hq⟩, hab, hlen, hes, hcoef⟩ := hΘ T (by simp)
    refine ⟨((⟨q, a, b, c, es⟩ : CT k r nf), T.word) :: Lf, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · refine ⟨?_, hqdeg, hlen⟩
        unfold Good
        refine ⟨?_, hes, T.word_lie⟩
        intro l hl
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hab l hcon.1 hcon.2
        rcases hl with hl | hl
        · exact hl ha
        · exact hl hb
      · exact h1 e' he'
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨e', he', h⟩ := h2 T' hT'
        exact ⟨e', List.mem_cons_of_mem _ he', h⟩
    · intro H g hg
      have h3' := h3 H g hg
      simp only [opApply, shape, List.map_cons, List.sum_cons] at h3' ⊢
      rw [h3', hcoef g hg]
      congr 1
      simp only [cv, cvs]
      rw [hq g]
      rfl

section mk

variable [FiniteDimensional ℂ Wp]


open Classical in
def mkTerm (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (e : CT k r nf × List (Mat k r)) : DTerm k r Wp Wq where
  coef := cv D fib e.1
  coefAdj := fun x => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH (cv D fib e.1 x)
  word := if ∀ X ∈ e.2, inLie k r X then e.2 else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := fun x A B => Formalism.FourierDecayAlt.P.HilbertSchmidtVectorization.adjH_spec _ A B

lemma mkTerm_word (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    {e : CT k r nf × List (Mat k r)} (h : ∀ X ∈ e.2, inLie k r X) : (mkTerm D fib e).word = e.2 := by
  dsimp only [mkTerm]
  rw [if_pos h]

lemma opApply_mk (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (Lf : FS k r nf)
    (hL : ∀ e ∈ Lf, ∀ X ∈ e.2, inLie k r X) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    opApply (Lf.map (mkTerm D fib)) F g = shape D fib F Lf g := by
  unfold opApply shape
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  simp only [Function.comp_apply]
  rw [mkTerm_word D fib (hL e he)]
  rfl

end mk

def compFS (D : RealPlaceData k r Wp Wq) {nf : ℕ} (L₁ L₂ : FS k r nf) : FS k r nf :=
  L₁.flatMap fun e₁ => (steps D e₁.2 L₂).map fun e => (mulCT e₁.1 e.1, e.2)

lemma compFS_bound (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} {o₁ κ₁ o₂ κ₂ : ℕ}
    {L₁ L₂ : FS k r nf}
    (h₁ : ∀ e ∈ L₁, Good L e ∧ e.1.q.totalDegree ≤ κ₁ ∧ e.2.length + fo e.1.es ≤ o₁)
    (h₂ : ∀ e ∈ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₂ ∧ e.2.length + fo e.1.es ≤ o₂) :
    ∀ e ∈ compFS D L₁ L₂, Good L e ∧ e.1.q.totalDegree ≤ κ₁ + κ₂ + (2 * r + 2) * o₁ ∧
      e.2.length + fo e.1.es ≤ o₁ + o₂ := by
  intro e he
  simp only [compFS, List.mem_flatMap, List.mem_map] at he
  obtain ⟨e₁, he₁, e', he', rfl⟩ := he
  obtain ⟨hG₁, hq₁, ho₁⟩ := h₁ e₁ he₁
  obtain ⟨hG₁a, hG₁b, hG₁c⟩ := hG₁
  have hG' := (good_steps D e₁.2 hG₁c L₂ (fun e he => (h₂ e he).1) e' he').1
  obtain ⟨hG'a, hG'b, hG'c⟩ := hG'
  obtain ⟨e₂, he₂, hdeg, hlen⟩ := bound_steps D e₁.2 L₂ e' he'
  obtain ⟨-, hq₂, ho₂⟩ := h₂ e₂ he₂
  have hfo : ∀ (l₁ l₂ : List (Fin nf × List (Mat k r))), fo (l₁ ++ l₂) = fo l₁ + fo l₂ := by
    intro l₁ l₂
    simp [fo, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold Good
    refine ⟨?_, ?_, hG'c⟩
    · intro l hl
      simp only [mulCT, Pi.add_apply] at hl
      by_cases h1 : e₁.1.a l ≠ 0 ∨ e₁.1.b l ≠ 0
      · exact hG₁a l h1
      · apply hG'a l
        push_neg at h1
        rcases hl with hl | hl
        · left; omega
        · right; omega
    · intro x hx Y hY
      simp only [mulCT, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hG₁b x hx Y hY
      · exact hG'b x hx Y hY
  · simp only [mulCT]
    have hmul := MvPolynomial.totalDegree_mul e₁.1.q e'.1.q
    have hw : e₁.2.length ≤ o₁ := by omega
    have := Nat.mul_le_mul_left (2 * r + 2) hw
    omega
  · simp only [mulCT]
    rw [hfo]
    omega

lemma list_map_sum_apply {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by
  rw [map_list_sum, List.map_map]
  rfl

private lemma rw_congr_on_domL (D : RealPlaceData k r Wp Wq) (L : Finset (Fin (r + 2))) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ {H H' : Mat k r → (Wq →L[ℂ] Wp)},
      (∀ g ∈ C6.domL D L, H g = H' g) → ∀ g ∈ C6.domL D L, Rw w H g = Rw w H' g := by
  intro w
  induction w with
  | nil => intro _ H H' hH g hg; exact hH g hg
  | cons X w ih =>
    intro hw H H' hH g hg
    have ih' := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hH
    rw [Rw_cons', Rw_cons', Dx_eq, Dx_eq]
    apply Filter.EventuallyEq.deriv_eq
    have hGV : g ∈ GV k r := ((mem_domL D L g).1 hg).1
    have hV0 : g ∈ V0 D L := ((mem_domL D L g).1 hg).2
    filter_upwards [crv_ev (x := (false, X)) (isOpen_big_cell_set D L) hV0] with t ht
    apply ih'
    rw [mem_domL]
    exact ⟨crv_mem (x := (false, X)) (hw X (by simp)) hGV t, ht⟩

theorem comp_identity (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, CkOn ⊤ (GPos D) (fib j)) (L : Finset (Fin (r + 2))) {L₁ L₂ : FS k r nf}
    (hg₁ : ∀ e ∈ L₁, Good L e) (hg₂ : ∀ e ∈ L₂, Good L e) {m : ℕ} (hm : ∀ e₁ ∈ L₁, ∀ e ∈ L₂, e.2.length + e₁.2.length ≤ m)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F) {H : Mat k r → (Wq →L[ℂ] Wp)}
    (hH : ∀ g ∈ C6.domL D L, H g = shape D fib F L₂ g) {g : Mat k r} (hg : g ∈ C6.domL D L) :
    shape D fib H L₁ g = shape D fib F (compFS D L₁ L₂) g := by
  show (L₁.map fun e => cv D fib e.1 g (Rw e.2 H g)).sum = _
  unfold compFS
  rw [shape_flatMap']
  congr 1
  refine List.map_congr_left fun e₁ he₁ => ?_
  obtain ⟨-, -, hw⟩ := hg₁ e₁ he₁
  rw [rw_congr_on_domL D L e₁.2 hw hH g hg]
  rw [expand D fib hfib L hF e₁.2 L₂ hw hg₂ (fun e he => hm e₁ he₁ e he) g hg]
  unfold shape
  rw [list_map_sum_apply, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, cv_mul, ContinuousLinearMap.mul_apply]

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasSgsPow
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

end Formalism.FourierDecayAlt.P.S3dx6
end
end

