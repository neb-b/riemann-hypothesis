module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermLocalOfFibres
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiNegBetaL
section
namespace Formalism.FourierDecayAlt.P.GermRealisation

open Formalism.FourierDecayAlt NumberField

noncomputable section

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)

theorem psi_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (betaL S) (σ * z) = KB.psiL S σ z := by
  unfold G.psi KB.psiL betaL
  congr 1
  rw [Complex.re_ofReal_mul]
  push_cast
  ring

theorem psi_neg_betaL (S : C.HidaSetting E Wp Wq) (σ z : ℂ) : G.psi (-betaL S) (σ * z) = KB.psiL S (-σ) z := by
  have h : G.psi (-betaL S) (σ * z) = G.psi (betaL S) (-σ * z) := by
    unfold G.psi
    rw [show -betaL S * (σ * z) = betaL S * (-σ * z) by ring]
  rw [h, psi_betaL]

theorem betaL_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) : betaL S ≠ 0 := by
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold betaL
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hg.ne')

end loc

end

end Formalism.FourierDecayAlt.P.GermRealisation
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5.Rad

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jf_uEquiv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : Mx k r) {h h' : Mx k r} (hh : h ∈ UWset k r D.z)
    (hh' : h' ∈ UWset k r D.z') : B.JF D F (h * g * h') = (D.π h).comp ((B.JF D F g).comp (D.π' h')) := by
  have := P.B5.haar_sigmaFinite D.haarW
  have := P.B5.haar_sigmaFinite D.haarN
  have := P.B5.haar_sigmaFinite D.haarW'
  exact bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep g h hh h' hh'

theorem radJFExists : RadJFExists := by
  intro Wp Wq _ _ _ _ _ _ Pa z z' π π' D F _hP hz hz' hπ hπ' hF
  subst hz hz' hπ hπ'
  classical
  let Φf : Fn Pa.k Pa.r (Wq →L[ℂ] Wp) := fun c g =>
    if (c, g) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) c g else 0
  have hsm := sf_resG (jf_smoothLev D F hF.1)
  have hmem : Φf ∈ RadSp Pa.k Pa.r D.z D.z' D.π D.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = 0
      rw [if_neg (by simpa using hx)]
    · obtain ⟨U, Fe, hU, hxU, hFe, hΦ⟩ := hsm x₀
        ⟨hx₀.1, wCell_mem_omPlus D.z_mem D.z'_mem hx₀.1 hx₀.2.1 hx₀.2.2⟩ hx₀.2.1
      have hV : IsOpen {x : (Fin Pa.r → ℂ) × Mx Pa.k Pa.r | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2} :=
        ((P.Qx3.isOpen_OmX Pa.r).preimage continuous_fst).inter
          (isOpen_lt continuous_const ((P.Qx5.GGl_continuous Pa.k Pa.r D.z D.z').comp continuous_snd))
      refine ⟨U ∩ {x | x.1 ∈ OmX Pa.r ∧ 0 < GGl Pa.k Pa.r D.z D.z' x.2}, Fe, hU.inter hV,
        ⟨hxU, hx₀.1, hx₀.2.2⟩, hFe.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
      rw [if_pos hxD]
      exact hΦ x hx.1 hxG
    · have hx' : (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' := by simpa using hx
      show (if (x.1, h * x.2 * h') ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 (h * x.2 * h') else 0) =
        (D.π h).comp ((if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0).comp (D.π' h'))
      rw [if_pos (domR_uw hx hh hh'), if_pos hx']
      unfold resG
      have e : wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * (h * x.2 * h') =
          h * (wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2) * h' := by
        have hc := P.Qx3.wlist_comm (k := Pa.k) (Fin.last Pa.r) x.1
          ((List.finRange Pa.r).filter fun a => a.val < (Fin.last Pa.r).val)
          (fun a ha => by simpa using (List.mem_filter.1 ha).2) (P.Qx3.uw_glev (Fin.last Pa.r) hh)
        change wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * h = h * wCell Pa.k Pa.r (Fin.last Pa.r) x.1 at hc
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hc, Matrix.mul_assoc h]
      rw [e, jf_uEquiv D F _ hh hh']
      ext v
      simp
  exact ⟨⟨Φf, hmem⟩, fun x hx => by
    show (if (x.1, x.2) ∈ DomR Pa.k Pa.r D.z D.z' then resG Pa.k Pa.r (Fin.last Pa.r) (B.JF D F) x.1 x.2 else 0) = _
    rw [if_pos (by simpa using hx)]⟩

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralRankZero
section
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dite_eq_left (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Pres

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def presAlg (U : Submodule ℂ V) : StarSubalgebra ℂ (Pr V) where
  carrier := {a | (∀ Φ ∈ U, a.1 Φ ∈ U) ∧ ∀ Φ ∈ U, a.2.unop Φ ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => ha1 _ (hb1 Φ hΦ), fun Φ hΦ => hb2 _ (ha2 Φ hΦ)⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨fun Φ hΦ => U.add_mem (ha1 Φ hΦ) (hb1 Φ hΦ), fun Φ hΦ => U.add_mem (ha2 Φ hΦ) (hb2 Φ hΦ)⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
    · show (algebraMap ℂ (Module.End ℂ V) a) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem a hΦ
    · show (algebraMap ℂ (Module.End ℂ V) (conj a)) Φ ∈ U
      rw [Module.algebraMap_end_apply]; exact U.smul_mem _ hΦ
  star_mem' := by
    rintro a ⟨ha1, ha2⟩
    exact ⟨ha2, ha1⟩

end Pres

section Words

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem entries_mem_transpose {M : M2 (SlopeTestRemainingChoices S A)} (h : E2 𝒜 M) : E2 𝒜 Mᵀ := fun i j => h j i

theorem transfer_word_entries_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S)) (Y : ℂ)
    (hY : star Y = Y) : E2 𝒜 (TTw QQ w Y) := by
  induction w with
  | nil =>
    intro a b
    show io (QQ Y a b) ∈ entSub 𝒜
    exact io_mem (hQ Y hY a b)
  | cons l w ih =>
    by_cases hp : l.plus
    · rw [TTw, if_pos hp]; exact entries_mem_mul ih (reflection_entries_mem _ _)
    · rw [TTw, if_neg hp]; exact entries_mem_mul (reflection_transpose_entries_mem _ _) ih

theorem rrw_mem (QQ : ℂ → M2 A) (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, QQ Y a b ∈ 𝒜) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRw QQ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [RRw]
    refine (entSub 𝒜).mul_mem (ih fun l' hl' => hw l' (by simp [hl'])) (ins_mem _ ?_)
    have hT := transfer_word_entries_mem QQ hQ w l.pt (hw l (by simp))
    split_ifs
    · exact hT
    · exact entries_mem_transpose hT

end Words

section Levels

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem matrix_two_entries_mem {𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))} {a b c d : Pr (RadSp k r z z' π π')}
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (hd : d ∈ 𝒜) : ∀ i j, (!![a, b; c, d] : M2 _) i j ∈ 𝒜 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π')))
    (Y : ℂ) (i : ℕ) (hS : ∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) (a b : Fin 2) :
    tprod L Y i a b ∈ 𝒜 := by
  suffices H : ∀ n i, r - i = n → (∀ l : Fin r, i ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) →
      ∀ a b, tprod L Y i a b ∈ 𝒜 from H _ i rfl hS a b
  intro n
  induction n with
  | zero =>
    intro i hi _ a b
    unfold tprod
    rw [dite_eq_right (by omega), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ n ih =>
    intro i hi hS a b
    unfold tprod
    rw [dite_eq_left (by omega), Matrix.mul_apply]
    refine sum_mem fun e _ => MulMemClass.mul_mem (ih (i + 1) (by omega) (fun l hl => hS l (by omega)) a e) ?_
    obtain ⟨hp, hc, hci⟩ := hS ⟨i, by omega⟩ le_rfl
    have h00 : algebraMap ℂ _ Y + L.p ⟨i, by omega⟩ ∈ 𝒜 := add_mem (𝒜.algebraMap_mem Y) hp
    fin_cases e <;> fin_cases b <;> simp [Ts, Formalism.YangianSpanCharacter.T.Tm, site, h00, hc, hci]

theorem QQi_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (𝒜 : StarSubalgebra ℂ (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (hQ : ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ 𝒜)
    (hS : ∀ l : Fin r, i.val ≤ l.val → L.p l ∈ 𝒜 ∧ L.c l ∈ 𝒜 ∧ L.ci l ∈ 𝒜) :
    ∀ Y : ℂ, star Y = Y → ∀ a b, QQi L st i Y a b ∈ 𝒜 := by
  intro Y hY a b
  unfold QQi
  rw [Matrix.mul_apply]
  refine sum_mem fun e _ => MulMemClass.mul_mem ?_ (tprod_mem L 𝒜 Y i.val hS e b)
  rw [Matrix.mul_apply]
  refine sum_mem fun f _ => MulMemClass.mul_mem ?_ (hQ Y hY f e)
  rw [Matrix.conjTranspose_apply]
  exact star_mem (tprod_mem L 𝒜 (star Y) i.val hS f a)

end Levels

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

