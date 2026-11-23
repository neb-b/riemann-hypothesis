module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0621
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalPropertiesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_natMultiple_eval_properties :
    ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d), ∀ n k,
      (∀ i, c.ev n (nmul c.μ k i) = GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k (c.x n i)) ∧
      (∀ f, c.ev n (subst (nmul c.μ k) f) =
        GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k (c.ev n f)) ∧
      ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) =
        pullbackTwo (GlobalTheory.PDiv.mulBy (R := O) (A := G.A n) k) (c.ev₂ n s) := by
  intro p O _ _ G d c n k
  have isEval_algHom_comp {A A' σ : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A']
      {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E) (g : A →ₐ[O] A') :
      IsEval p (fun i => g (x i)) (g.comp E) := by
    refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
    obtain ⟨N, hN⟩ := hE.2 m
    refine ⟨N, fun f hf => ?_⟩
    have := map_dvd g (hN f hf)
    rwa [map_pow, map_natCast] at this

  have constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
      (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
    induction k generalizing i with
    | zero => simp [nmul]
    | succ k ih =>
      have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X _
      have e : nmul μ (k + 1) i = subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (μ i) := by
        simp only [nmul]
        rw [Function.iterate_succ_apply']
        rfl
      rw [e]
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

  have ev₂_inL (c : GlobalTheory.QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_algHom_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

  have ev₂_inR (c : GlobalTheory.QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_algHom_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

  have ev_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (i : Fin d) :
      c.ev n (nmul c.μ k i) = GlobalTheory.PDiv.mulBy O (G.A n) k (c.x n i) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
    induction k generalizing i with
    | zero =>
      have h0 : nmul c.μ 0 i = 0 := rfl
      rw [h0, map_zero]
      simp [GlobalTheory.PDiv.mulBy, c.aug n i]
    | succ k ih =>
      let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
      let L : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
        Algebra.TensorProduct.lift M (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
      have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact constantCoeff_nmul c.isLaw.const k j
        · exact constantCoeff_X _
      have e : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ i) := by
        simp only [nmul]
        rw [Function.iterate_succ_apply']
        rfl
      have hE := isEval_algHom_comp (c.isEval₂ n) L
      have hx : (fun j => L (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
          fun j => c.ev n (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) := by
        funext j
        rcases j with j | j
        · simp [L, M, ih j]
        · simp [L, (c.isEval n).1 j]
      rw [hx] at hE
      rw [e, H _ _ _ hs hE, AlgHom.comp_apply, c.comul n i]
      have h1 : GlobalTheory.PDiv.mulBy O (G.A n) (k + 1) (c.x n i) =
          (WithConv.toConv (AlgHom.id O (G.A n)) ^ (k + 1)).ofConv (c.x n i) :=
        DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O (G.A n)) (k + 1)) (c.x n i)
      have h2 : (M : G.A n →ₐ[O] G.A n) = (WithConv.toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
        comp_mulBy_pts (AlgHom.id O (G.A n)) k
      rw [h1, pow_succ, AlgHom.convMul_apply]
      simp only [L, h2]

  have ev_subst_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (f : MvPowerSeries (Fin d) O) :
      c.ev n (subst (nmul c.μ k) f) = GlobalTheory.PDiv.mulBy O (G.A n) k (c.ev n f) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
    let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    have hE := isEval_algHom_comp (c.isEval n) M
    have hx : (fun j => M (c.x n j)) = fun j => c.ev n (nmul c.μ k j) :=
      funext fun j => (ev_nmul c n k j).symm
    rw [hx] at hE
    exact H (Fin d) _ _ (constantCoeff_nmul c.isLaw.const k) hE f

  have ev₂_pull2_nmul (c : GlobalTheory.QLog.Chart G d) (n k : ℕ) (s : MvPowerSeries (Fin d ⊕ Fin d) O) :
      c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (GlobalTheory.PDiv.mulBy O (G.A n) k) (c.ev₂ n s) := by
    have : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
      _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
    have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
        (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
      rintro (i | i)
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
      · obtain ⟨N, hN⟩ := c.nil n i
        refine ⟨N, ?_⟩
        have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
        simpa [map_pow, map_natCast] using this
    have H := ((GlobalTheory.CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
      (c.ev₂ n) (c.isEval₂ n)).1
    let M : G.A n →ₐ[O] G.A n := (GlobalTheory.PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    let T : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] G.A n := Algebra.TensorProduct.map M M
    have hs : ∀ j, constantCoeff (Sum.elim (fun j => inL (nmul c.μ k j))
        (fun j => inR (nmul c.μ k j)) j) = 0 := by
      have hX : ∀ j : Fin d, constantCoeff (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
        fun _ => constantCoeff_X _
      have hY : ∀ j : Fin d, constantCoeff (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
        fun _ => constantCoeff_X _
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hX) hX
          (constantCoeff_nmul c.isLaw.const k j)
      · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hY) hY
          (constantCoeff_nmul c.isLaw.const k j)
    have hE := isEval_algHom_comp (c.isEval₂ n) T
    have hx : (fun j => T (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n))
        (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
        fun j => c.ev₂ n (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j)) j) := by
      funext j
      rcases j with j | j
      · simp [T, M, ev₂_inL, ev_nmul]
      · simp [T, M, ev₂_inR, ev_nmul]
    rw [hx] at hE
    have e : pull2 (nmul c.μ k) s =
        subst (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j))) s := rfl
    rw [e, H _ _ _ hs hE, AlgHom.comp_apply]
    generalize c.ev₂ n s = t
    induction t with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul a b => simp [T, M]
  exact ⟨ev_nmul c n k, ev_subst_nmul c n k, ev₂_pull2_nmul c n k⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneSubstOfEndomorphism
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobDefect

theorem hasSubst_cc {σ τ S : Type} [Finite σ] [CommRing S] {a : σ → MvPowerSeries τ S}
    (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a := hasSubst_of_constantCoeff_zero h

theorem cc_map {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPowerSeries σ R) :
    constantCoeff (map φ f) = φ (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X φ _

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X φ _

theorem mvPowerSeriesMap_evalTwoGroups {τ : Type} [Finite τ] (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]
  congr 1
  funext i
  cases i <;> rfl

theorem map_formalGroupLawCoboundaryOne_eq (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_cc hμ), map_inL, map_inR]

theorem formalGroupLawCoboundaryOne_sub (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) R) : cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  unfold cob1 inL inR
  rw [subst_sub (hasSubst_cc hμ), subst_sub (hasSubst_cc fun _ => constantCoeff_X _),
    subst_sub (hasSubst_cc fun _ => constantCoeff_X _)]
  abel

theorem powerSeriesEvalTwoGroups_sub {τ : Type} [Finite τ] (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  rw [subst_sub (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]

theorem formalGroupLawCoboundaryOne_subst_of_endomorphism (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Fin d → MvPowerSeries (Fin d) R)
    (hN : ∀ i, constantCoeff (N i) = 0)
    (hom : ∀ j, subst μ (N j) = at2 (μ j) (fun i => inL (N i)) (fun i => inR (N i)))
    (f : MvPowerSeries (Fin d) R) :
    cob1 μ (subst N f) = at2 (cob1 μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
  have hL : ∀ i, constantCoeff (inL (N i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hR : ∀ i, constantCoeff (inR (N i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hE : HasSubst (Sum.elim (fun i => inL (N i)) (fun i => inR (N i))) :=
    hasSubst_cc fun i => by cases i <;> simp [hL, hR]
  have hXL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have hXR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have e1 : inL (subst N f) = subst (fun j => inL (N j)) f := by
    unfold inL
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXL]
  have e2 : inR (subst N f) = subst (fun j => inR (N j)) f := by
    unfold inR
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXR]
  have e3 : at2 (inL f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inL (N j)) f := by
    unfold at2
    rw [show inL f = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXL hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e4 : at2 (inR f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inR (N j)) f := by
    unfold at2
    rw [show inR f = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXR hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e5 : subst μ (subst N f) = at2 (subst μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_cc hN) (hasSubst_cc hμ),
      subst_comp_subst_apply (hasSubst_cc hμ) hE]
    congr 1
    funext j
    exact hom j
  unfold cob1
  rw [powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, e1, e2, e3, e4, e5]

theorem formalGroupLawCoboundaryOne_mulDefect (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ)
    (hinj : Function.Injective (algebraMap R Q)) (f : MvPowerSeries (Fin d) Q)
    (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ)
    (hf : constantCoeff f = 0) (hg : map (algebraMap R Q) g = cob1 (up Q μ) f)
    (hs : map (algebraMap R Q) s = defect μ k f) :
    cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧
      constantCoeff g = 0 := by
  have hH := _root_.GlobalTheory.NMulEndo.isHom_nmul R d μ hμ k
  have hμ0 := hμ.const
  have hN0 := hH.const
  have hmapinj : ∀ {σ : Type} (a b : MvPowerSeries σ R),
      map (algebraMap R Q) a = map (algebraMap R Q) b → a = b := by
    intro σ a b h
    ext n
    apply hinj
    rw [← coeff_map, ← coeff_map, h]
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, cc_map, hμ0 i, map_zero]
  have hNQ : ∀ i, constantCoeff (up Q (nmul μ k) i) = 0 := fun i => by
    simp only [up, cc_map, hN0 i, map_zero]
  have hL : ∀ i, constantCoeff (inL (nmul μ k i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have hR : ∀ i, constantCoeff (inR (nmul μ k i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have homQ : ∀ j, subst (up Q μ) (up Q (nmul μ k) j) =
      at2 (up Q μ j) (fun i => inL (up Q (nmul μ k) i)) (fun i => inR (up Q (nmul μ k) i)) := by
    intro j
    have h1 := congrArg (map (algebraMap R Q)) (hH.hom j)
    rw [map_subst (hasSubst_cc hμ0)] at h1
    unfold pull2 at h1
    rw [mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR] at h1
    simp only [map_inL, map_inR] at h1
    exact h1
  constructor
  · apply hmapinj
    rw [map_formalGroupLawCoboundaryOne_eq _ _ hμ0, hs, map_sub, mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR]
    simp only [map_inL, map_inR]
    change cob1 (up Q μ) (defect μ k f) = _ - at2 _ (fun i => inL (up Q (nmul μ k) i))
      (fun i => inR (up Q (nmul μ k) i))
    rw [Nat.cast_smul_eq_nsmul R k g, map_nsmul, hg]
    unfold defect
    rw [formalGroupLawCoboundaryOne_sub _ hμQ, formalCoboundary_smul hμQ, Nat.cast_smul_eq_nsmul, formalGroupLawCoboundaryOne_subst_of_endomorphism _ hμQ _ hNQ homQ]
  · apply hinj
    rw [← cc_map, hg, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_eq_zero (hasSubst_cc hμQ) hμQ hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf]
    simp

theorem main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q) (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ), constantCoeff f = 0 → map (algebraMap R Q) g = cob1 (up Q μ) f → map (algebraMap R Q) s = defect μ k f → cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧ constantCoeff g = 0 :=
  fun R Q _ _ _ d μ hμ hinj f g s k hf hg hs => formalGroupLawCoboundaryOne_mulDefect R Q d μ hμ hinj f g s k hf hg hs

end GlobalTheory.CobDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightLevi
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas

theorem frameWeight_levi : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  intro n Y _ _ _ _ _ ι La _ A E U β J hU hβ hJ x hx i hi
  have hne : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s → ∀ y ∈ U,
      y ∈ (A.chart i).source → s i y ≠ 0 := by
    intro la s hs y hyU hyi
    rw [hs.1.2 i (A.pick y) y hyU hyi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne _ _ _ y hyi (A.mem_pick y)) (hs.2 y hyU)
  have hloc : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y))) =ᶠ[𝓝 x]
      fun y => A.ph E i y + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
    filter_upwards [(A.chart i).open_source.mem_nhds hi, hU.mem_nhds hx] with y hyi hyU
    have hp := A.mem_pick y
    have hb := hne _ β hβ y hyU hyi
    have hj := hne _ J hJ y hyU hyi
    have e1 := hyq_nsq_chart A (A.kap + E) β i y hyi (hβ.1.2 i _ y hyU hyi hp)
    have e2 := hyq_nsq_chart A A.kap J i y hyi (hJ.1.2 i _ y hyU hyi hp)
    have hb2 : 0 < ‖β i y‖ ^ 2 := by positivity
    have hj2 : 0 < ‖J i y‖ ^ 2 := by positivity
    rw [e1, e2, A.ph_add A.kap E i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
      Real.log_mul hb2.ne' (Real.exp_pos _).ne', Real.log_mul hj2.ne' (Real.exp_pos _).ne',
      Real.log_mul hj2.ne' (inv_pos.mpr hb2).ne', Real.log_inv, Real.log_exp, Real.log_exp]
    ring
  have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hU
  have hxW : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hholo : ∀ (la : La) (s : ι → Y → ℂ), A.IsFrameOn la U s →
      ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (s i ∘ (A.chart i).symm) v := by
    intro la s hs
    filter_upwards [hWo.mem_nhds hxW] with v hv
    exact (hs.1.1 i v hv).differentiableAt (hWo.mem_nhds hv)
  have hevW : ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    hWo.mem_nhds hxW
  have hqd : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hholo _ β hβ, hholo _ J hJ, hevW] with v h1 h2 h3
    have hb := hne _ β hβ _ h3.2 ((A.chart i).map_target h3.1)
    exact h2.mul (h1.inv hb)
  have hq : ContDiffAt ℝ ∞ ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) :=
    hyq_contDiffAt_of_ev hqd
  have hqne : ((fun y => J i y * (β i y)⁻¹) ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simp only [Function.comp, hc]
    exact mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))
  have hlog : ContDiffAt ℝ ∞ ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i x) :=
    (hq.norm_sq ℝ).log (by positivity)
  have hphE : ContDiffAt ℝ ∞ (A.ph E i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph E i).contDiffAt hT
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have := ((A.chart i).continuousAt_symm ((A.chart i).map_source hi)).tendsto
    rwa [hc] at this
  refine ⟨?_, fun f hf ξ => ?_⟩
  · refine (hphE.add hlog).congr_of_eventuallyEq ?_
    filter_upwards [ht.eventually hloc] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  · have hloc' : (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y)
        =ᶠ[𝓝 x] fun y => (A.ph E i y + f y) + Real.log (‖J i y * (β i y)⁻¹‖ ^ 2) := by
      filter_upwards [hloc] with y hy
      rw [hy]; ring
    have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph E i y + f y) ∘ (A.chart i).symm) (A.chart i x) :=
      (hphE.add hf).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
        (A.chart i x) := hlog.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [leviAt_congr A i _ _ x hi hloc' ξ,
      leviAt_add A i (fun y => A.ph E i y + f y)
        (fun y => Real.log (‖J i y * (β i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
      leviAt_log_normSq A i (fun y => J i y * (β i y)⁻¹) x hi hqd
        (mul_ne_zero (hne _ J hJ x hx hi) (inv_ne_zero (hne _ β hβ x hx hi))) ξ, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.NMulHom

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) :=
  GlobalTheory.NMulEndo.isHom_nmul

end GlobalTheory.NMulHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHomStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
end

