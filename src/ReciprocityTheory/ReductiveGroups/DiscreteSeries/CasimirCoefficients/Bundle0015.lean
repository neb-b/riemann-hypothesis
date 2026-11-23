module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandGA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ChainHSlice

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace GelfandG

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem opPow_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (p q : Fin n → Fin n → Fin n) (s : ℂ)
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E'))
    (hA : ∀ a b h, A a b h = s • EabV ε (p a b) (q a b) h) (j : ℕ) :
    ∀ a b, ∀ g ∈ W, inUJ ε g →
      opPow A j a b f g = (-s) ^ j •
        Lk (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j a b G (g⁻¹ * m)) := by
  induction j with
  | zero =>
    intro a b g hg hgu
    simp only [opPow, pow_zero, one_smul]
    split_ifs
    · exact hf g hg hgu
    · simp
  | succ j ih =>
    intro a b g hg hgu
    have hz : g⁻¹ * m ∈ U := (hWU g hg).2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opPow, Finset.sum_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hGd : DifferentiableOn ℂ
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G) U :=
      (GelfandGA.opPow_contDiffOn hU hG _ j c b).differentiableOn (by simp)
    have hF : DifferentiableOn ℂ (fun z => ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G z)) U :=
      ((-s) ^ j • Lk).differentiable.comp_differentiableOn hGd
    have hloc : ∀ g ∈ W, inUJ ε g → opPow A j c b f g = ((-s) ^ j • Lk)
        (opPow (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) j c b G (g⁻¹ * m)) :=
      fun g hg hgu => by rw [ih c b g hg hgu, _root_.smul_apply]
    rw [hA, Pi.smul_apply, eabV_of_local ε hU hF hW hWU hloc _ _ hg hgu,
      CasG.lhol_clm _ _ ((hGd _ hz).differentiableAt (hU.mem_nhds hz)),
      _root_.smul_apply, smul_neg, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

theorem opGelfand_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (p q : Fin n → Fin n → Fin n) (s : ℂ)
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E'))
    (hA : ∀ a b h, A a b h = s • EabV ε (p a b) (q a b) h) (k : ℕ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    opGelfand A k f g = (-s) ^ k •
      Lk (opGelfand (fun a b => Lhol (Matrix.single (p a b) (q a b) (1 : ℂ))) k G (g⁻¹ * m)) := by
  unfold opGelfand
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => opPow_local ε Lk hU hG hW hWU hf p q s A hA k a a g hg hgu

end GelfandG

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_gelfand (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (k : ℕ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    opGelfand (rightE ε) k (PsiM T μ) g = gval (icShift lam) k • PsiM T μ g ∧
      opGelfand (rightEanti ε) k (PsiM T μ) g = gval (icShift (-lam)) k • PsiM T μ g := by
  have := compactSpace_KG ε
  obtain ⟨U₁, hU₁o, hpos₁, -, hgel⟩ := gelfand_psM T μ lam hμ
  have hUo : IsOpen (U₁ ∩ Ps1.Uset ε) := hU₁o.inter Ps1.isOpen_Uset
  have hpos : posSet n ⊆ U₁ ∩ Ps1.Uset ε := Set.subset_inter hpos₁ Ps1.posSet_subset_Uset
  have hsm : ContDiffOn ℂ ∞ (psM T μ) (U₁ ∩ Ps1.Uset ε) :=
    (GelfandGA.psM_contDiffOn T μ).mono Set.inter_subset_right
  obtain ⟨W, k₀, hWo, hgW, hWV, hloc⟩ := psiM_local T μ hμ _ hUo hpos hg
  have hz : g⁻¹ * toMK k₀ ∈ U₁ ∩ Ps1.Uset ε := (hWV g hgW).2
  have hlocL : ∀ g' ∈ W, inUJ ε g' → PsiM T μ g' =
      ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) (psM T μ (g'⁻¹ * toMK k₀)) :=
    fun g' hg' hgu => hloc g' hg' hgu
  obtain ⟨h1, h2⟩ := hgel _ hz.1 k
  constructor
  · calc opGelfand (rightE ε) k (PsiM T μ) g
        = (-(1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (psM T μ) (g⁻¹ * toMK k₀)) :=
          GelfandG.opGelfand_local ε _ hUo hsm hWo hWV hlocL (fun a _ => a) (fun _ b => b) 1 (rightE ε)
            (fun a b h => (one_smul ℂ _).symm) k hgW hg
      _ = (-(1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (((-1 : ℂ) ^ k * gval (icShift lam) k) • psM T μ (g⁻¹ * toMK k₀)) := by rw [h1]
      _ = gval (icShift lam) k • PsiM T μ g := by
          rw [map_smul, smul_smul, hloc g hgW hg, ← mul_assoc, ← mul_pow]
          congr 1
          norm_num
  · calc opGelfand (rightEanti ε) k (PsiM T μ) g
        = (-(-1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (psM T μ)
              (g⁻¹ * toMK k₀)) :=
          GelfandG.opGelfand_local ε _ hUo hsm hWo hWV hlocL (fun a b => Fin.rev b) (fun a b => Fin.rev a)
            (-1) (rightEanti ε) (fun a b h => (neg_one_smul ℂ _).symm) k hgW hg
      _ = (-(-1 : ℂ)) ^ k • ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)
            (gval (icShift (-lam)) k • psM T μ (g⁻¹ * toMK k₀)) := by rw [h2]
      _ = gval (icShift (-lam)) k • PsiM T μ g := by
          rw [map_smul, smul_smul, hloc g hgW hg, neg_neg, one_pow, one_mul]
          rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopContDiffOn
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CapG

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem top_contDiffOn {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hU : IsOpen U)
    {G : Matrix (Fin n) (Fin n) ℂ → E} (hG : ContDiffOn ℂ ∞ G U) (u : ℂ) (a b : Fin n) :
    ContDiffOn ℂ ∞ (Formalism.QuantumDeterminants.Top negL u a b G) U := by
  have h2 : ContDiffOn ℂ ∞ (negL a b G) U := (GelfandGA.lhol_contDiffOn hU hG _).neg
  unfold Formalism.QuantumDeterminants.Top
  by_cases hab : a = b
  · subst hab
    simp only [↓reduceIte]
    exact (hG.const_smul u).add h2
  · simp only [hab, ↓reduceIte, zero_add]
    exact h2

theorem foldr_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (l : List (ℂ × Fin n × Fin n)) :
    ContDiffOn ℂ ∞ ((l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G) U ∧
    ∀ g ∈ W, inUJ ε g →
      (l.map fun x => Formalism.QuantumDeterminants.Top (EabV ε) x.1 x.2.1 x.2.2).foldr (fun T h => T h) f g =
        Lk ((l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G (g⁻¹ * m)) := by
  induction l with
  | nil => exact ⟨hG, fun g hg hgu => by simpa using hf g hg hgu⟩
  | cons x l ih =>
    obtain ⟨ihc, ihf⟩ := ih
    simp only [List.map_cons, List.foldr_cons]
    refine ⟨top_contDiffOn hU ihc _ _ _, fun g hg hgu => ?_⟩
    have hz := (hWU g hg).2
    have hHd := ihc.differentiableOn (by simp)
    set H := (l.map fun x => Formalism.QuantumDeterminants.Top negL x.1 x.2.1 x.2.2).foldr (fun T h => T h) G with hH
    have hF : DifferentiableOn ℂ (fun z => Lk (H z)) U := Lk.differentiable.comp_differentiableOn hHd
    have e := eabV_of_local ε hU hF hW hWU ihf x.2.1 x.2.2 hg hgu
    show (if x.2.1 = x.2.2 then x.1 • _ else 0) + EabV ε x.2.1 x.2.2 _ g =
      Lk ((if x.2.1 = x.2.2 then x.1 • _ else 0) + negL x.2.1 x.2.2 _ (g⁻¹ * m))
    rw [e, CasG.lhol_clm _ _ ((hHd _ hz).differentiableAt (hU.mem_nhds hz)), ihf g hg hgu, map_add (f := _)]
    simp only [negL, map_neg]
    split_ifs <;> simp

theorem qdet_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    Formalism.QuantumDeterminants.qdetOp (EabV ε) u f g = Lk (Formalism.QuantumDeterminants.qdetOp negL u G (g⁻¹ * m)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.QuantumDeterminants.qdetOp, Formalism.QuantumDeterminants.qminorOp, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have key := (foldr_local ε Lk hU hG hW hWU hf
    (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), σ k, k))).2 g hg hgu
  rw [List.map_ofFn, List.map_ofFn] at key
  exact key

end CapG

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_capelli (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) (Y : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (PsiM T μ) g =
      Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • PsiM T μ g := by
  have := compactSpace_KG ε
  obtain ⟨U₁, hU₁o, hpos₁, -, hcap⟩ := cap_psM T μ lam hμ
  have hUo : IsOpen (U₁ ∩ Ps1.Uset ε) := hU₁o.inter Ps1.isOpen_Uset
  have hpos : posSet n ⊆ U₁ ∩ Ps1.Uset ε := Set.subset_inter hpos₁ Ps1.posSet_subset_Uset
  have hsm : ContDiffOn ℂ ∞ (psM T μ) (U₁ ∩ Ps1.Uset ε) :=
    (GelfandGA.psM_contDiffOn T μ).mono Set.inter_subset_right
  obtain ⟨W, k₀, hWo, hgW, hWV, hloc⟩ := psiM_local T μ hμ _ hUo hpos hg
  have hz : g⁻¹ * toMK k₀ ∈ U₁ ∩ Ps1.Uset ε := (hWV g hgW).2
  have hlocL : ∀ g' ∈ W, inUJ ε g' → PsiM T μ g' =
      ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) (psM T μ (g'⁻¹ * toMK k₀)) :=
    fun g' hg' hgu => hloc g' hg' hgu
  have e := CapG.qdet_local ε _ hUo hsm hWo hWV hlocL (Y + ((n : ℂ) - 1) / 2) hgW hg
  show Formalism.QuantumDeterminants.qdetOp (EabV ε) _ (PsiM T μ) g = _
  rw [e, hcap Y _ hz.1, map_smul, hloc g hgW hg]
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

