module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CcARatioZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0017
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FormCc
section
set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem form_cc (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (s : Fin n) {ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε))}
    (hι : IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι)
    (hιe : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), eeF dual (smE ε (rreg ε)) (ι x) = poleF dual lam s • ι x)
    (hιs : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f → ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), f = ι x)
    {P : Module.End ℂ (Fin n → smD ε (rreg ε))}
    (hPG : IsGKEndo dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) P)
    (hPz : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) (P f) = poleF dual lam s • P f)
    (hP1 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF dual lam s →
      eeF dual (smE ε (rreg ε)) f = z' • f → P f = 0) :
    ∃ (ka : ℝ) (q : (Fin n → smD ε (rreg ε)) → smD ε (rreg ε)), ka ≠ 0 ∧
      (∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        formB ε (ι x) (ι y) = ka * inner ℂ ((x : smD ε (rreg ε)) : L2 ε) ((y : smD ε (rreg ε)) : L2 ε)) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        q f ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') ∧ P f = ι (q f)) ∧
      (∀ a b, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        q (tensF dual (smE ε (rreg ε)) a b f) = smE ε (rreg ε) a b (q f)) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        ((ka * ‖((q f : smD ε (rreg ε)) : L2 ε)‖ ^ 2 : ℝ) : ℂ) = formB ε (P f) (P f)) ∧
      ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ f' ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        ∀ g ∈ UJset ε,
          ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f' c : smD ε (rreg ε)) : L2 ε)
              (tensGrp dual (rreg ε) g (fun d => ((P f d : smD ε (rreg ε)) : L2 ε)) c) =
            ka * inner ℂ ((q f' : smD ε (rreg ε)) : L2 ε) (rreg ε g ((q f : smD ε (rreg ε)) : L2 ε)) := by

  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hV := datumV_isKIrrHW hP hv₀
  have hV' := datumV_isKIrrHW hP' hv₀'
  have hc := datumV_casimir hP v₀
  have hc' := datumV_casimir hP' v₀'
  have hVK := datumV_kStable hP v₀
  have hVK' := datumV_kStable hP' v₀'
  have hinn : ∀ x : L2 ε, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hPB := eigenProj_formB dual hσ hD hgap hV hc hVK hW (poleF dual lam s) hPG.1 hPz hP1 hP0
  have hιinj : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      ι x = ι y → x = y := fun x hx y hy h =>
    sub_eq_zero.1 (hι.2.1 _ (Submodule.sub_mem _ hx hy) (by rw [map_sub, h, sub_self]))
  have hPι : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P (ι x) = ι x := fun x hx => hP1 _ (hι.1 x hx) (hιe x hx)

  let b : smD ε (rreg ε) →ₗ⋆[ℂ] smD ε (rreg ε) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => formB ε (ι x) (ι y))
      (fun x x' y => by simp only [map_add (f := _), fm_formB_add_left])
      (fun a x y => by simp only [map_smul, formB_smul_left, smul_eq_mul])
      (fun x y y' => by simp only [map_add (f := _), formB_add_right])
      (fun a x y => by simp only [map_smul, formB_smul_right, RingHom.id_apply, smul_eq_mul])
  have hb : ∀ x y, b x y = formB ε (ι x) (ι y) := fun _ _ => rfl
  obtain ⟨c, hcb⟩ := data_form_scalar hgap' hσ hD hV' hc' hVK' b
    (fun a a' x hx y hy => by
      rw [hb, hb, hι.2.2.1 a a' x hx, hι.2.2.1 a' a y hy]
      exact fm_formB_tensF dual hU a a' _ _)
    (fun k hk x hx y hy x' hx' y' hy' hxx hyy => by
      rw [hb, hb]
      have h1 := hι.2.2.2 k hk x hx x' hx' hxx
      have h2 := hι.2.2.2 k hk y hy y' hy' hyy
      have := fm_formBH_kDiag dual hσ hk (fun c => ((ι x c : smD ε (rreg ε)) : L2 ε))
        (fun c => ((ι y c : smD ε (rreg ε)) : L2 ε))
      rw [← h1, ← h2] at this
      exact this)
  obtain ⟨w, hwV, hw0, -⟩ := hV'.2.2.2
  have hwM : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') := rorth_le_genSub hwV
  have hwH : ((w : smD ε (rreg ε)) : L2 ε) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hcre : c = (c.re : ℂ) := by
    have h1 := hcb w hwM w hwM
    have h2 : starRingEnd ℂ (b w w) = b w w := by rw [hb]; exact formB_conj _ _
    rw [h1, map_mul, inner_conj_symm] at h2
    have hww : inner ℂ ((w : smD ε (rreg ε)) : L2 ε) ((w : smD ε (rreg ε)) : L2 ε) ≠ 0 := inner_self_ne_zero.2 hwH
    exact (Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hww h2)).symm
  have hform : ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      formB ε (ι x) (ι y) = (c.re : ℂ) * inner ℂ ((x : smD ε (rreg ε)) : L2 ε) ((y : smD ε (rreg ε)) : L2 ε) := by
    intro x hx y hy
    rw [← hb, hcb x hx y hy, ← hcre]

  have hqex : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x := fun f hf => hιs _ (hPG.1 f hf) (hPz f hf)
  let q : (Fin n → smD ε (rreg ε)) → smD ε (rreg ε) := fun f =>
    if h : ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), P f = ι x then h.choose else 0
  have hq : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      q f ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀') ∧ P f = ι (q f) := by
    intro f hf
    have h := hqex f hf
    have e : q f = h.choose := dite_eq_left h
    rw [e]
    exact h.choose_spec
  refine ⟨c.re, q, ?_, hform, hq, ?_, ?_, ?_⟩
  ·
    intro h0
    have hιw : ι w ≠ 0 := fun h => hw0 (hι.2.1 w hwM h)
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 hιw
    let G : Fin n → smD ε (rreg ε) := fun c => (if ε c then (1 : ℂ) else -1) • ι w c
    have hG : G ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :=
      tset_mem.2 fun c => Submodule.smul_mem _ _ (tset_mem.1 (hι.1 w hwM) c)
    have e1 : formB ε (ι w) G = ((∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2 : ℝ) : ℂ) := by
      simp only [formB, G, Submodule.coe_smul, inner_smul_right, Complex.ofReal_sum]
      refine sum_congr rfl fun c _ => ?_
      rw [hinn]
      split_ifs <;> ring
    have hpos : 0 < ∑ c, ‖((ι w c : smD ε (rreg ε)) : L2 ε)‖ ^ 2 := by
      refine Finset.sum_pos' (fun c _ => sq_nonneg _) ⟨c0, mem_univ _, ?_⟩
      have : ((ι w c0 : smD ε (rreg ε)) : L2 ε) ≠ 0 := fun h => hc0 (Subtype.ext h)
      exact pow_pos (norm_pos_iff.2 this) 2
    obtain ⟨y, hy, hPy⟩ := hqex G hG
    have e2 : formB ε (ι w) G = 0 := by
      rw [← hPι w hwM, hPB _ (hι.1 w hwM) G hG, hPy, hform w hwM y hy, h0]
      simp
    rw [e1] at e2
    exact absurd (Complex.ofReal_eq_zero.1 e2) hpos.ne'
  ·
    intro a b' f hf
    have hf' := tensSub_stable dual a b' f hf
    obtain ⟨h1, h2⟩ := hq _ hf'
    obtain ⟨h3, h4⟩ := hq f hf
    refine hιinj _ h1 _ (tset_genSub_E _ _ a b' h3) ?_
    rw [← h2, hPG.2.1 a b' f hf, h4, hι.2.2.1 a b' _ h3]
  ·
    intro f hf
    obtain ⟨h1, h2⟩ := hq f hf
    rw [h2, hform _ h1 _ h1, hinn]
    push_cast
    ring
  ·
    intro f hf f' hf' g hg
    obtain ⟨hq1, hq2⟩ := hq f hf
    obtain ⟨hq1', hq2'⟩ := hq f' hf'
    let F : Fin n → smD ε (rreg ε) := fun c => (if ε c then (1 : ℂ) else -1) • f' c
    have hz : ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ ((c.re : ℂ) • q f') y = ∑ c, inner ℂ (F c) (ι y c) := by
      intro y hy
      have e1 : ∑ c, inner ℂ (F c) (ι y c) = formB ε f' (ι y) := by
        simp only [formB, F, Submodule.coe_inner, inner_smul_left, fm_sgn_star]
      rw [e1, ← hPι y hy, ← hPB f' hf' (ι y) (hι.1 y hy), hq2', hform _ hq1' _ hy,
        Submodule.coe_inner, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]
    have key := coefE_all dual hσ hD hV.1 hV.2.1 hc hV'.1 hV'.2.1 hc' hι.1 hι.2.2.1 F ((c.re : ℂ) • q f') hz g hg
      (q f) hq1
    have hTG : ∀ w : Fin n → L2 ε, tensGrp dual (rreg ε) g w = coefTG dual (rreg ε) g w := by
      intro w; funext c; cases dual <;> rfl
    rw [hq2, hTG]
    calc ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((f' c : smD ε (rreg ε)) : L2 ε)
          (coefTG dual (rreg ε) g (fun d => ((ι (q f) d : smD ε (rreg ε)) : L2 ε)) c)
        = ∑ c, inner ℂ ((F c : smD ε (rreg ε)) : L2 ε)
          (coefTG dual (rreg ε) g (fun d => ((ι (q f) d : smD ε (rreg ε)) : L2 ε)) c) :=
          sum_congr rfl fun c _ => by simp only [F, Submodule.coe_smul, inner_smul_left, fm_sgn_star]
      _ = _ := by
          rw [key, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.SandwichA
section
noncomputable section

open Finset MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem swA_thr {ε : Fin n → Bool} {h : ℝ} (hth : thrStar ε < h) :
    (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧
      16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) < h :=
  ⟨lt_of_le_of_lt (le_max_left _ _) hth, lt_of_le_of_lt (le_max_right _ _) hth⟩

theorem swA_model {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) (hq : 1 ≤ S7.q0 ε) {h : ℝ}
    (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) (T : S7.KType ε (lowK ε lam)) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
          2 (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  obtain ⟨h1, h2⟩ := swA_thr hth
  have hq1 : (0 : ℝ) ≤ (S7.q0 ε : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := mul_nonneg hn0 hq1
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith
  have hs2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, h1⟩
  have hP : IsPsiFor ε lam T (S7.PsiM T m) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T m k₁ k₂ hg, S7.psiM_one T m, S7.psiM_smooth T m hm,
      fun g hg => S7.psiM_casimir T m hm hg, fun ν hν => by
        have := hν
        exact (S7.psiM_integrable T m hm hlam hh hq ν).2.1 h8⟩
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  refine ⟨S7.PsiM T m, hgap, hP, psi_exp_isPositive T (S7.PsiM T m) m hm (fun X hX => S7.psiM_exp_formula T m hX),
    weighted_datum hgap hP hv₀ (fun ν hν => ?_), hasGelfandChar_sigLam hgap hP hv₀ (fun k g hg => S7.psiM_gelfand T m hm k hg)⟩
  have := hν
  exact (S7.psiM_integrable T m hm hlam hh hq ν).2.2 2 (by norm_num) hs2

theorem swB_isFdeg_pull {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τB d) : Formalism.MainNotions.S.IsFdeg ν τA d := by
  obtain ⟨hd0, h⟩ := hd
  have hc : ∀ v w : A, Formalism.MainNotions.S.coefOn (ε := ε) τA v w = Formalism.MainNotions.S.coefOn (ε := ε) τB (U v) (U w) := by
    intro v w
    funext g
    delta Formalism.MainNotions.S.coefOn
    rw [← hU _ g.2, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd0, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := h (U v) (U w) (U v') (U w')
  rw [hc v w, hc v' w']
  refine ⟨hi, ?_⟩
  rw [he, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

theorem swB_isFdeg_push {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τA d) : Formalism.MainNotions.S.IsFdeg ν τB d := by
  refine swB_isFdeg_pull U.symm (fun g hg y => ?_) hd
  apply U.injective
  rw [LinearIsometryEquiv.apply_symm_apply, hU g hg, LinearIsometryEquiv.apply_symm_apply]

theorem swB_isFdeg_unique {ε : Fin n → Bool} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {τ : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)} {ν : Measure (Formalism.REAL.UJ ε)} {d d' : ℝ} {w : A} (hw : w ≠ 0)
    (hd : Formalism.MainNotions.S.IsFdeg ν τ d) (hd' : Formalism.MainNotions.S.IsFdeg ν τ d') : d = d' := by
  rw [← fdegOf_of_isFdeg' hd hw, ← fdegOf_of_isFdeg' hd' hw]

theorem swB_haar_eq {ε : Fin n → Bool} (ν : Measure (Formalism.REAL.UJ ε)) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ν = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure ν (Formalism.REAL.muG ε)
  have heq := Measure.isMulLeftInvariant_eq_smul ν (Formalism.REAL.muG ε)
  have hc : (0 : ℝ) < (Measure.haarScalarFactor ν (Formalism.REAL.muG ε) : ℝ) := by exact_mod_cast hs
  exact ⟨_, hc, by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩

theorem swC_gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : GapAtLeast ε μ h) (dual : Bool)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  have key : ∀ c : Fin n → ℝ, (∀ a b : Fin n, a ≠ b → |c a - c b| ≤ 1) → GapAtLeast ε (μ + c) (h - 1) := by
    intro c hc a b hab
    have hne : a ≠ b := fun e => hab (e ▸ rfl)
    have h1 := hμ a b hab
    have h2 := hc a b hne
    have h3 : |μ a - μ b| ≤ |(μ + c) a - (μ + c) b| + |c a - c b| := by
      have : μ a - μ b = ((μ + c) a - (μ + c) b) - (c a - c b) := by simp only [Pi.add_apply]; ring
      rw [this]
      exact abs_sub _ _
    linarith
  have hsingle : ∀ t : ℝ, |t| ≤ 1 → ∀ a b : Fin n, a ≠ b → |Pi.single (M := fun _ => ℝ) s t a - Pi.single (M := fun _ => ℝ) s t b| ≤ 1 := by
    intro t ht a b hab
    by_cases ha : a = s
    · subst ha
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), sub_zero]
      exact ht
    · by_cases hb : b = s
      · subst hb
        rw [Pi.single_eq_same, Pi.single_eq_of_ne ha, zero_sub, abs_neg]
        exact ht
      · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
        simp
  cases dual
  · exact key _ (hsingle 1 (by simp))
  · have : shiftF true μ s = μ + Pi.single s (-1) := by
      delta shiftF
      simp only [Bool.cond_true]
      rw [sub_eq_add_neg, Pi.single_neg]
    rw [this]
    exact key _ (hsingle (-1) (by simp))

theorem swC_hc_shift {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) (dual : Bool) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s)) : S7.IsHCParam (shiftF dual μ s) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  delta shiftF
  by_cases ha : a = s
  · subst ha
    cases dual
    · exact ⟨m + 1, by simp only [Bool.cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [Bool.cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩
  · cases dual
    · exact ⟨m, by simp only [Bool.cond_false, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]; exact hm⟩
    · exact ⟨m, by simp only [Bool.cond_true, Pi.sub_apply, Pi.single_eq_of_ne ha, sub_zero]; exact hm⟩

theorem swC_main (dual : Bool) {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (shiftF dual μ s) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioF dual μ s) := by
  have := hσ.1
  have := hσ'.1
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hth : thrStar ε < h := by linarith
  have hth' : thrStar ε < h - 1 := by linarith
  have hlam' := swC_hc_shift hμ dual s hs
  have hgap' := swC_gap_shift hgap dual s
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨T'⟩ := HW.kType_exists ε (shiftF dual μ s) hlam'
  obtain ⟨Ψ, hS, hP, hpos, hW, hG⟩ := swA_model hμ hq0 hgap hth T
  obtain ⟨Ψ', hS', hP', hpos', hW', hG'⟩ := swA_model hlam' hq0 hgap' hth' T'
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  have hv₀' : T'.w ≠ 0 := fun h0 => by simpa [h0] using T'.w_norm
  have hDS := isDS_sigLam hS hP hv₀
  have hDS' := isDS_sigLam hS' hP' hv₀'
  have := hDS.2.1
  have := hDS'.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  have hcc := (cc_gk dual hS hP hv₀ hS' hP' hv₀' hgap hth hgap' hth' hpos hpos' hW hW' hG hG' s rfl hw hw').2
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hS hP hv₀
  obtain ⟨U', hU'⟩ := equiv_sigLam_of_isDS hσ' hS' hP' hv₀'
  have hdL : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) d := swB_isFdeg_pull U hU hd
  obtain ⟨d1, hd1⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ (sigLam ε Ψ T.w) hDS
  obtain ⟨d2, hd2⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (shiftF dual μ s) (sigLam ε Ψ' T'.w) hDS'
  rw [fdegOf_of_isFdeg' hd1 hw, fdegOf_of_isFdeg' hd2 hw'] at hcc
  have := hν
  obtain ⟨c, hc, hνeq⟩ := swB_haar_eq ν
  have hd1' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) (d1 / c) := hνeq ▸ isFdeg_smul hc hd1
  have hd2' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ' T'.w) (d2 / c) := hνeq ▸ isFdeg_smul hc hd2
  have hdd : d = d1 / c := swB_isFdeg_unique hw hdL hd1'
  have hd10 : d1 ≠ 0 := hd1.1.ne'
  have hval : d * ratioF dual μ s = d2 / c := by
    rw [hdd, ← hcc]
    field_simp
  rw [hval]
  exact swB_isFdeg_push U' hU' hd2'

end ReciprocityTheory.ChartRestriction.DS
end
end

