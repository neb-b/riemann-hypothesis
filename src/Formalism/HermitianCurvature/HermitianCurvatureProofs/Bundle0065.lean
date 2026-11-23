module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightMonotonicity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatQMinOp
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminorWordSum (k r t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
      (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ t) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
        B.CkOn (t : ℕ∞) UU f → ∀ g ∈ UU, g ∈ B.GV k r →
          qminorOp (Q.EH k r) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin t) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin t))).toList.flatMap
      (fun σ => (expand k r (ts σ)).map fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨this.1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Loc ((ts σ).length : ℕ∞) f g := by
      intro σ
      obtain ⟨U, f', a, b, c, d⟩ := hf g hgU
      refine ⟨U, f', a, b, ?_, d⟩
      simpa [ts] using c
    have e1 : qminorOp (Q.EH k r) a b u f g = ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [foldT, ts, List.map_ofFn]
      rfl
    rw [e1, sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [expand_eq (ts σ) f g hg (hloc σ), List.map_map, ← sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsv_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp


open Classical in
def pTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := if ∀ X ∈ w, B.inLie k r X then w else []
  word_lie := by
    split_ifs with h
    · exact h
    · simp
  adj_id := by
    intro x A B'
    simp only [B.hsInner, _root_.smul_apply, ContinuousLinearMap.id_apply, hsv_smul,
      inner_smul_left, inner_smul_right]
    simp

theorem pTerm_word {P : B.Mat k r → ℂ} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word = w := by
  simp only [pTerm]
  rw [if_pos hw]

theorem pTerm_word_le (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) :
    (pTerm (Wp := Wp) (Wq := Wq) P w).word.length ≤ w.length := by
  simp only [pTerm]
  split_ifs
  · exact le_refl _
  · simp

theorem inLie_zero : B.inLie k r 0 := by
  unfold B.inLie
  simp

private theorem foldr_max_le_lemma (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → l.foldr max 0 ≤ t := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem le_foldr_max_lemma_2 : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih x hx) (le_max_right _ _)

theorem foldr_max_eq (t : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ t) → t ∈ l → l.foldr max 0 = t := by
  intro l hl ht
  exact le_antisymm (foldr_max_le_lemma t l hl) (le_foldr_max_lemma_2 l t ht)

end terms

theorem qminOpRep {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) a (b j) u F g := by
  have h := fun j => qminorWordSum k r t a (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

section basic₂

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem polyOp_mono {o o' κ κ' : ℕ} {Θ : B.DiffOp k r Wp Wq} (h : PolyOp o κ Θ) (ho : o ≤ o') (hκ : κ ≤ κ') :
    PolyOp o' κ' Θ := by
  unfold PolyOp at *
  intro Tm hTm
  obtain ⟨h1, P, hP, h2, h3⟩ := h Tm hTm
  obtain ⟨q, hq, hq'⟩ := hP
  exact ⟨h1.trans ho, P, ⟨q, hq.trans hκ, hq'⟩, h2, h3⟩

theorem polyOp_append {o κ : ℕ} {Θ₁ Θ₂ : B.DiffOp k r Wp Wq} (h₁ : PolyOp o κ Θ₁) (h₂ : PolyOp o κ Θ₂) :
    PolyOp o κ (Θ₁ ++ Θ₂) := by
  unfold PolyOp at *
  intro Tm hTm
  rcases List.mem_append.mp hTm with h | h
  · exact h₁ Tm h
  · exact h₂ Tm h

theorem opApply_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ₁ ++ Θ₂) F g = B.opApply Θ₁ F g + B.opApply Θ₂ F g := by
  unfold B.opApply
  rw [List.map_append, List.sum_append]

private theorem foldr_max_init_lemma_3 : ∀ (l : List ℕ) (b : ℕ), l.foldr max b = max (l.foldr max 0) b := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons a l ih =>
    intro b
    simp only [List.foldr_cons]
    rw [ih b, max_assoc]

theorem opOrder_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) :
    B.opOrder (Θ₁ ++ Θ₂) = max (B.opOrder Θ₁) (B.opOrder Θ₂) := by
  unfold B.opOrder
  rw [List.map_append, List.foldr_append]
  exact foldr_max_init_lemma_3 _ _

end basic₂

end

end Formalism.FourierDecayAlt.P.CutMP.QMinOp
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagGramRestriction
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FnComm
section
namespace Formalism.FourierDecayAlt.TL

open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {r : ℕ} {L : LevelData A r} {st : Start A}

theorem fn_comm (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : x * y = y * x :=
  L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem z10 (h : IsLevelStart L st) {Y : ℂ} (hi : Y ∈ st.inv) :
    st.QQ Y 1 0 * L.ζ = L.ζ * st.QQ Y 1 0 - st.QQ Y 1 1 ∧ Commute (st.QQ Y 1 0) L.ζb := by
  have hlow := h.low Y hi
  have htau := h.tau Y
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζi : L.ζi ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mGG : L.GG ∈ zfns L := by simp [zfns]
  have mGGi : L.GGi ∈ zfns L := by simp [zfns]
  have cm : ∀ {x y : A}, x ∈ zfns L → y ∈ zfns L → Commute x y := fun hx hy => fn_comm L hx hy
  have hX : ∀ g ∈ zfns L, Commute (st.x Y) g := h.x_fn Y
  have hE : ∀ g ∈ zfns L, Commute (st.ee Y) g := h.ee_fn Y
  have hc : ∀ a : A, Commute (algebraMap ℂ A (Y + 1 / 2)) a := fun a => Algebra.commutes _ a
  have hl : L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y =
      -L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) + L.ζb * L.ζi * L.GGi * st.ee Y) := by
    simp only [Formalism.FourierDecayAlt.R.LevelData.l0]
    abel
  rw [hl] at hlow
  have hT : ∀ g ∈ zfns L, Commute (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
      L.ζb * L.ζi * L.GGi * st.ee Y) g := by
    intro g hg
    apply Commute.add_left
    · exact ((hc _).mul_left ((cm mζb hg).mul_left (cm mGGi hg))).neg_left
    · exact (((cm mζb hg).mul_left (cm mζi hg)).mul_left (cm mGGi hg)).mul_left (hE _ hg)
  have hTz := hT _ mζ
  have hGXz : Commute (L.GG * st.x Y) L.ζ := (cm mGG mζ).mul_left (hX _ mζ)
  constructor
  · rw [hlow, htau]
    calc L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) * L.ζ
        = L.GG * st.x Y * (-(L.nab * L.ζ) + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y) * L.ζ) := by noncomm_ring
      _ = L.GG * st.x Y * (-(L.ζ * L.nab + 1) + L.ζ * (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) := by rw [L.nab_ζ, hTz.eq]
      _ = (L.GG * st.x Y * L.ζ) * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y)) - L.GG * st.x Y := by noncomm_ring
      _ = L.ζ * (L.GG * st.x Y * (-L.nab + (-(algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) +
          L.ζb * L.ζi * L.GGi * st.ee Y))) - L.GG * st.x Y := by
        rw [hGXz.eq]
        noncomm_ring
  · rw [hlow]
    have hnab : Commute L.nab L.ζb := L.nab_ζb
    exact ((cm mGG mζb).mul_left (hX _ mζb)).mul_left (hnab.neg_left.add_left (hT _ mζb))

theorem zetaQQ : ZetaQQ := by
  intro A _ _ _ _ r L st hS h Y hY hi
  have mζ : L.ζ ∈ zfns L := by simp [zfns]
  have mζb : L.ζb ∈ zfns L := by simp [zfns]
  have mG : L.GG ∈ zfns L := by simp [zfns]
  have sζb : star L.ζb = L.ζ := by rw [← hS.1, star_star]
  have herm : ∀ Z : ℂ, star Z = Z → ∀ i j, star (st.QQ Z i j) = st.QQ Z j i := fun Z hZ i j => by
    have := congrFun (congrFun (h.start.herm Z hZ) j) i
    rwa [Matrix.conjTranspose_apply] at this
  have base : ∀ Z : ℂ, star Z = Z → Z ∈ st.inv →
      (st.QQ Z 1 0 * L.ζ = L.ζ * st.QQ Z 1 0 - st.QQ Z 1 1 ∧ Commute (st.QQ Z 1 0) L.ζb ∧
      st.QQ Z 0 1 * L.ζb = L.ζb * st.QQ Z 0 1 + st.QQ Z 1 1 ∧ Commute (st.QQ Z 0 1) L.ζ ∧
      Commute (st.QQ Z 1 1) L.ζ ∧ Commute (st.QQ Z 1 1) L.ζb) := fun Z hZ hZi => by
    obtain ⟨a, b⟩ := z10 h hZi
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · have := congrArg star a
      rw [star_mul, star_sub, star_mul, herm Z hZ, herm Z hZ, hS.1] at this
      rw [this]; abel
    · have := congrArg star b.eq
      rw [star_mul, star_mul, herm Z hZ, sζb] at this
      exact this.symm
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζ) (h.x_fn Z _ mζ)
    · rw [h.tau]; exact Commute.mul_left (fn_comm L mG mζb) (h.x_fn Z _ mζb)
  refine ⟨base Y hY hi, fun hn => ?_⟩
  have cancel : ∀ Z ∈ st.inv, ∀ u : A, u * st.QQ Z 1 1 = 0 → u = 0 := fun Z hZ u hu => by
    rw [h.tau] at hu
    have : u * (L.GG * st.x Z) * st.xi Z * L.GGi = u := by
      rw [mul_assoc u, mul_assoc L.GG, (h.x_xi Z hZ).1, mul_one, mul_assoc, L.GG_GGi, mul_one]
    rw [← this, hu, zero_mul, zero_mul]
  have key : st.QQ Y 0 0 * L.ζb = L.ζb * st.QQ Y 0 0 + st.QQ Y 1 0 := by
    obtain ⟨-, b10, b01, -, -, -⟩ := base Y hY hi
    rcases hn with hm | hp
    · have hr : star (Y - 1) = Y - 1 := by rw [star_sub, hY, star_one]
      obtain ⟨-, -, c01, -, -, c11⟩ := base _ hr hm
      have d := congrFun (congrFun (h.start.det (Y - 1)).1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d
      have dq := Algebra.commutes (st.q (Y - 1)) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hm
      have e1 := c11.eq
      have e2 := b10.eq
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y - 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y - 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1)) +
            (st.QQ Y 1 0 * (st.QQ (Y - 1) 0 1 * L.ζb) - L.ζb * st.QQ Y 1 0 * st.QQ (Y - 1) 0 1
              - st.QQ Y 1 0 * st.QQ (Y - 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [c01, ← e2]
          have : (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 1 0 * st.QQ (Y - 1) 0 1 + st.QQ Y 0 0 * st.QQ (Y - 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
    · have hr : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
      obtain ⟨-, c10, -, -, -, c11⟩ := base _ hr hp
      have d := congrFun (congrFun (h.start.det Y).2 0) 1
      have d' := congrFun (congrFun (h.start.det Y).2 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two, YangianSpanCharacter.T.J] at d d'
      have dq := Algebra.commutes (st.q Y) L.ζb
      rw [← d] at dq
      apply eq_of_sub_eq_zero
      apply cancel _ hp
      have e1 := c11.eq
      have e2 := c10.eq
      have d2 : st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 = st.QQ Y 1 1 * st.QQ (Y + 1) 1 0 := by
        have := d'; rw [neg_add_eq_zero] at this; exact this.symm
      calc _ = st.QQ Y 0 0 * (L.ζb * st.QQ (Y + 1) 1 1) - L.ζb * st.QQ Y 0 0 * st.QQ (Y + 1) 1 1
            - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1 := by noncomm_ring
        _ = ((-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1)) +
            (st.QQ Y 0 1 * (st.QQ (Y + 1) 1 0 * L.ζb) - L.ζb * st.QQ Y 0 1 * st.QQ (Y + 1) 1 0
              - st.QQ Y 1 0 * st.QQ (Y + 1) 1 1) := by rw [← e1]; noncomm_ring
        _ = 0 := by
          rw [e2, ← mul_assoc (st.QQ Y 0 1), b01, d2]
          have : (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) * L.ζb -
            L.ζb * (-st.QQ Y 0 1 * st.QQ (Y + 1) 1 0 + st.QQ Y 0 0 * st.QQ (Y + 1) 1 1) = 0 := by
            rw [sub_eq_zero]; simpa [neg_mul] using dq
          rw [this]; noncomm_ring
  refine ⟨key, ?_⟩
  have := congrArg star key
  rw [star_mul, star_add, star_mul, herm Y hY, herm Y hY, sζb] at this
  rw [this]; abel

end

end Formalism.FourierDecayAlt.TL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormPos
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def rrC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ :=
  fun v ε i w P Q =>
    ((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
      D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ) *
      (p v).RR (F v ε) i w (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)

def setC (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : C.HidaSetting E Wp Wq :=
  KB.withRR S (rrC S p F)

end defs

def FormPos : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x ε, 0 < ε →
    (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerPairs
section
theorem Formalism.FourierDecayAlt.P.stabilizer_pairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs
end

