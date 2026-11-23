module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Sandwich
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FormBSelfLe
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0018
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0016

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJOfSigLam
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Equiv

variable {ε : Fin n → Bool}
  {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem dSW_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ x : H₁, dSW σ₂ w (U x) = U (dSW σ₁ w x)
  | [], _, _ => rfl
  | X :: w, hw, x => by
    simp only [dSW]
    rw [dSW_map_isometry U hU w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) x,
      dS_map_isometry U hU (hw X List.mem_cons_self)]

theorem nuJ_map_isometry (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ UJset ε, ∀ x : H₁, U (σ₁ g x) = σ₂ g (U x))
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (x : H₁) :
    nuJ σ₂ Ws (U x) = nuJ σ₁ Ws x := by
  delta nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [dSW_map_isometry U hU w (hWs w hw) x, U.norm_map]

end Equiv

theorem decBoundJ_of_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) (m N : ℕ) (hL : DecBoundJ ε (sigLam ε Ψ v₀) m N) :
    DecBoundJ ε σ m N := by
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hstd hP hv₀
  obtain ⟨C, Ws, hWs, hB⟩ := hL
  have hWs' : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  refine ⟨C, Ws, hWs, fun u v hu hv g hg => ?_⟩
  obtain ⟨x, rfl⟩ := U.surjective u
  obtain ⟨y, rfl⟩ := U.surjective v
  have hx := smooth_symm_of_isometry U hU hu
  have hy := smooth_symm_of_isometry U hU hv
  rw [U.symm_apply_apply] at hx hy
  have hb := hB x y hx hy g hg
  rw [← hU g hg x, U.inner_map_map, nuJ_map_isometry U hU hWs' x, nuJ_map_isometry U hU hWs' y]
  exact hb

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ProjectionSquareIntegrable
section
set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem poles_injective {lam : Fin n → ℝ} (hlam : StrictAnti lam) : Function.Injective (poleF false lam) := by
  simpa only [poleF, Bool.cond_false] using poleV_injective hlam.injective

theorem projection_square_integrable {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)),
      (∀ s, IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (P s)) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) (P s f) = poleF false lam s • P s f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P s f = f) ∧
      (∀ s, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
        eeF false (smE ε (rreg ε)) f = z' • f → P s f = 0) ∧
      (∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), f = ∑ s, P s f) ∧
      ∀ s (j : ℕ), ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
        NT (smE ε (rreg ε)) j (P s f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f := by
  classical
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  have hc := datumV_casimir hP v₀
  have hVK := datumV_kStable hP v₀
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε) := fun v =>
    (mem_smD_iff ε (rreg ε) (v : L2 ε)).1 v.2
  obtain ⟨B, hdec, -⟩ := ee_decomp false hσ hD hgap hV hc hVK hW
  obtain ⟨hpole, -⟩ := pole_match false hσ hD hsm hgap hV hc hVK hW hG
  have hinj : Set.InjOn (poleF false lam) (Finset.univ : Finset (Fin n)) :=
    (poles_injective hlam.1).injOn
  set a := poleF false lam with ha
  set EE := eeF false (smE ε (rreg ε)) with hEE
  set S := tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) with hS
  let P : Fin n → Module.End ℂ (Fin n → smD ε (rreg ε)) := fun s =>
    Polynomial.aeval EE (Lagrange.basis Finset.univ a s)
  have hPe : ∀ s (e : Fin n → smD ε (rreg ε)) (z : ℂ), EE e = z • e →
      P s e = (Lagrange.basis Finset.univ a s).eval z • e := fun s e z he => dc_aeval_eigen he _
  have hLval : ∀ s t, (Lagrange.basis Finset.univ a s).eval (a t) = if s = t then 1 else 0 := by
    intro s t
    split_ifs with hst
    · subst hst; exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
    · exact Lagrange.eval_basis_of_ne hst (Finset.mem_univ _)

  have hterm : ∀ s, ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → EE (P s e) = a s • P s e := by
    intro s e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    rw [hPe s e _ hz, hLval s t]
    split_ifs with hst
    · subst hst; rw [one_smul, hz]
    · simp
  have hsum1 : ∀ e ∈ S, ∀ z : ℂ, EE e = z • e → ∑ s, P s e = e := by
    intro e he z hz
    by_cases h0 : e = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z e he h0 hz
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨t, Finset.mem_univ _⟩
    have h1 : ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) = 1 := by
      rw [← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj hne, Polynomial.eval_one]
    calc ∑ s, P s e = ∑ s, (Lagrange.basis Finset.univ a s).eval (a t) • e :=
          Finset.sum_congr rfl fun s _ => hPe s e _ hz
      _ = e := by rw [← Finset.sum_smul, h1, one_smul]
  refine ⟨P, fun s => dc_isGKEndo_aeval (isGKEndo_eeF hσ hD _ false) _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    rw [hfe, map_sum (P s), map_sum EE, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => hterm s _ (hfb b).1 _ (hfb b).2
  · intro s f _ hf
    rw [hPe s f _ hf, Lagrange.eval_basis_self hinj (Finset.mem_univ _), one_smul]
  · intro s f hf z' hz' hfz
    by_cases h0 : f = 0
    · subst h0; simp
    obtain ⟨t, rfl⟩ := hpole z' f hf h0 hfz
    have hts : s ≠ t := fun h => hz' (by rw [h])
    rw [hPe s f _ hfz, hLval s t, ite_eq_right hts, zero_smul]
  · intro f hf
    obtain ⟨fb, hfb, hfe⟩ := hdec f hf
    calc
      f = ∑ b ∈ B, fb b := hfe
      _ = ∑ b ∈ B, ∑ s, P s (fb b) :=
        Finset.sum_congr rfl fun b _ => (hsum1 _ (hfb b).1 _ (hfb b).2).symm
      _ = ∑ s, P s f := by
        rw [Finset.sum_comm, hfe]
        exact Finset.sum_congr rfl fun s _ => (map_sum (P s) fb B).symm
  · intro s j
    obtain ⟨C, hC⟩ := NT_poly_le false (smE ε (rreg ε)) (Lagrange.basis Finset.univ a s) j
    have hdeg : (Lagrange.basis Finset.univ a s).natDegree = n - 1 := by
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    refine ⟨C, fun f _ => ?_⟩
    have := hC f
    rw [hdeg] at this
    exact this

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PsiForPosGelfand
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem opPow_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g) :
    ∀ (k : ℕ) (a b : Fin n) (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.opPow A k a b f g = S7.opPow A k a b f' g
  | 0, a, b, f, f', h, g, hg => by
      simp only [S7.opPow]
      split_ifs
      · exact h g hg
      · rfl
  | k + 1, a, b, f, f', h, g, hg => by
      simp only [S7.opPow, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact hA a c _ _ (fun g' hg' => opPow_congr A hA k c b f f' h g' hg') g hg

theorem opGelfand_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g)
    (k : ℕ) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.opGelfand A k f g = S7.opGelfand A k f' g := by
  delta S7.opGelfand
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => opPow_congr A hA k a a f f' h g hg

theorem rightE_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightE ε a b f g = S7.rightE ε a b f' g :=
  fun a b _ _ h _ hg => icx_eabV_congr h a b hg

theorem rightEanti_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightEanti ε a b f g = S7.rightEanti ε a b f' g := by
  intro a b f f' h g hg
  exact congrArg (fun x : E => -x) (icx_eabV_congr h (Fin.rev b) (Fin.rev a) hg)

theorem psiFor_pos_gelfand {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ) :
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        S7.opGelfand (S7.rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
          S7.opGelfand (S7.rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  have hT1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 ≤ thrStar ε := le_max_left _ _
  have hT2 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
    le_max_right _ _
  have h8' : 8 * (n : ℝ) * S7.q0 ε < h := by
    have : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, by linarith⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 h8'⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' (HW.KType.w_ne_zero T)
  have heq' : ∀ g, inUJ ε g → Ψ g = Ψ' g := fun g hg => (heq g hg).symm
  refine ⟨fun X hX => ?_, fun k g hg => ?_⟩
  · obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
    have hX1 : inUJ ε (NormedSpace.exp X) := by
      have := S7.inUJ_kexp (1 : S7.KG ε) hX
      have hk1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
      rwa [hk1, one_mul] at this
    rw [heq' _ hX1]
    exact psi_exp_isPositive T Ψ' μ hμ (h8 μ hμ) X hX
  · obtain ⟨e1, e2⟩ := h7 k g hg
    refine ⟨?_, ?_⟩
    · rw [opGelfand_congr _ rightE_congr k heq' hg, e1, heq' g hg]
    · rw [opGelfand_congr _ rightEanti_congr k heq' hg, e2, heq' g hg]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end

