module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0008
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PowSmulLatticeLeWeightLatticeTop
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionExtendsFromClasses
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem translate_mem_span_adelic (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U) {h : Frames (gramC J emb) → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range g)) :
    (fun y => (S.chi κ : ℂ) * h (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) ∈
      Submodule.span ℂ (Set.range g) := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨z, rfl⟩ := hh
    have hb : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      Formalism.UG.Final.RatPtsLe F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩
    have hk : κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq κ.1).1 κ.2).1
    let z' : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
      ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * z.1 * κ.1, mul_mem (mul_mem hb z.2) hk⟩
    apply Submodule.subset_span
    refine ⟨z', ?_⟩
    funext y
    exact adelic_value_translate S emb hc hg γ hγ z z' κ rfl y
  | zero =>
    have e : (fun y => (S.chi κ : ℂ) * (0 : Frames (gramC J emb) → ℂ)
        (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) = 0 := by funext y; simp
    rw [e]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun y => (S.chi κ : ℂ) * (a + b) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) +
        (fun y => (S.chi κ : ℂ) * b (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp [mul_add]
    rw [e]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : (fun y => (S.chi κ : ℂ) * (r • a) (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) =
        r • (fun y => (S.chi κ : ℂ) * a (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y)) := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact Submodule.smul_mem _ r ha


set_option maxHeartbeats 1000000 in
theorem adelic_function_extends_from_classes (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n)
    {C : Type} [Fintype C] (y : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hs : ∀ c, RndStabTriv S (y c))
    (hdis : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 = (y c').1 * κ.1 → c = c')
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdForms S emb lam)
    (Fc : C → Frames (gramC J emb) → ℂ) (hF : ∀ c, Fc c ∈ Submodule.span ℂ (Set.range g)) :
    ∃ G ∈ AdForms S emb lam, ∀ c, G (y c) = Fc c := by
  classical
  have hgA := (Submodule.mem_inf.1 hg).1
  have hgV : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) z trivial
  have hspan : Submodule.span ℂ (Set.range g) ≤ ValC (gramC J emb) lam :=
    Submodule.span_le.2 (by rintro _ ⟨z, rfl⟩; exact hgV z)
  let G := ∑ c, rndFillG S emb hc (y c) (Fc c)
  refine ⟨G, Submodule.mem_inf.2 ⟨Submodule.sum_mem _ fun c _ => rnd_fill_mem S emb hc (y c) (hs c) (Fc c), ?_⟩, ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => ?_
    show (∑ c, rndFillG S emb hc (y c) (Fc c)) x ∈ _
    rw [Finset.sum_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hx : ∃ p : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U,
        x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) p.1.1 * (y c).1 * p.2.1
    · have e : rndFillG S emb hc (y c) (Fc c) x = fun yy => (S.chi (Classical.choose hx).2 : ℂ) *
          Fc c (frameTranslate emb hc (Classical.choose hx).1.1⁻¹ ((UJ (σ : E →+* E) J).inv_mem (Classical.choose hx).1.2) yy) := by
        funext yy; unfold rndFillG; rw [dite_eq_left hx]
      rw [e]
      exact hspan (translate_mem_span_adelic S emb hc hgA _ (Classical.choose hx).1.2 _ (hF c))
    · have e : rndFillG S emb hc (y c) (Fc c) x = 0 := by
        funext yy; unfold rndFillG; rw [dite_eq_right hx]; rfl
      rw [e]; exact zero_mem _
  · intro c
    show (∑ c', rndFillG S emb hc (y c') (Fc c')) (y c) = Fc c
    rw [Finset.sum_apply, Finset.sum_eq_single c]
    · exact rnd_fill_at S emb hc (y c) (hs c) (Fc c)
    · intro c' _ hne
      funext yy
      unfold rndFillG
      rw [dite_eq_right]
      · rfl
      rintro ⟨p, hp⟩
      apply hne
      refine hdis c' c p.1.1 p.1.2 p.2⁻¹ ?_
      rw [hp, InvMemClass.coe_inv]; group
    · intro h; exact absurd (Finset.mem_univ c) h

end Gen

section Tied

variable {D : D7} {u : D.what₂.Word}



end Tied

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.SecondBranchInclLengthOfLengths
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Parts

variable (D : D7) (u : D.what₂.Word)

def SeenPlaceLatticeLengthFormula : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))

end Parts

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

