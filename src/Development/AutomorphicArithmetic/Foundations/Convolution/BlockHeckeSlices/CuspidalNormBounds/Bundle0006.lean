module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.LangStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceCapR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CompBound
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

private theorem bnd : ∀ {n : ℕ} (d : Dat S n) (N : ℕ), ∃ C R : ℝ, ∀ (φ : Sm E n) (B : ℝ), Umg φ →
    (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ t, ‖d.comp φ.1 t‖ ≤ C * B * Real.exp (R * ‖t‖) := by
  intro n d N
  induction d with
  | nil => exact ⟨AutomorphicForm.height (1 : GA E 0) ^ N, 0, fun φ B _ h t => by
      rw [zero_mul, Real.exp_zero, mul_one, mul_comm]; exact h 1⟩
  | @cons r s b d ih =>
    obtain ⟨C, R, h1⟩ := (sliceBound E S r s b).1 N
    obtain ⟨C', R', h2⟩ := ih
    refine ⟨|C' * C|, |R| + |R'|, fun φ B hφ hB (t : Fin (d.len + 1) → ℝ) => ?_⟩
    obtain ⟨ψ, e, hψ, -⟩ := sliceUmg E S r s b (t 0) φ hφ
    have h3 := h2 ψ (C * B * Real.exp (R * |t 0|)) hψ (fun m => e ▸ h1 φ B hφ hB (t 0) m) fun j => t j.succ
    rw [e] at h3
    refine le_trans h3 ?_
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 1)) (pow_pos (AutomorphicForm.height_pos _) N)
    have a1 : |t 0| ≤ ‖t‖ := norm_le_pi_norm t 0
    have a2 : ‖fun j : Fin d.len => t j.succ‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm t j.succ
    have a3 : Real.exp (R * |t 0|) * Real.exp (R' * ‖fun j : Fin d.len => t j.succ‖) ≤ Real.exp ((|R| + |R'|) * ‖t‖) := by
      rw [← Real.exp_add, add_mul]
      exact Real.exp_le_exp.2 (add_le_add (mul_le_mul (le_abs_self R) a1 (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (le_abs_self R') a2 (norm_nonneg _) (abs_nonneg _)))
    calc _ = C' * C * B * (Real.exp (R * |t 0|) * Real.exp (R' * ‖fun j : Fin d.len => t j.succ‖)) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hB0) a3 (by positivity) (by positivity)

private theorem lin : ∀ {n : ℕ} (d : Dat S n) (φ ψ : Sm E n) (c : ℂ), Umg φ → Umg ψ →
    ∀ t, d.comp (c • φ + ψ).1 t = c * d.comp φ.1 t + d.comp ψ.1 t := by
  intro n d
  induction d with
  | nil => exact fun φ ψ c _ _ t => rfl
  | @cons r s b d ih =>
    intro φ ψ c hφ hψ (t : Fin (d.len + 1) → ℝ)
    obtain ⟨φ', e, hφ', -⟩ := sliceUmg E S r s b (t 0) φ hφ
    obtain ⟨ψ', e', hψ', -⟩ := sliceUmg E S r s b (t 0) ψ hψ
    have h := ih φ' ψ' c hφ' hψ' fun j => t j.succ
    have e2 : (c • φ' + ψ').1 = slice b.f.1 (t 0) (c • φ + ψ).1 := funext fun m => by
      rw [(sliceBound E S r s b).2 φ ψ c hφ hψ, ← e, ← e']; rfl
    rw [e2, e, e'] at h
    exact h

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.compBound :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompBound E :=
  fun _ _ _ _ _ _ d => ⟨UpperTheory.ConvolutionTheory.BW.bnd d, UpperTheory.ConvolutionTheory.BW.lin d⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem ct_top {n : ℕ} (φ : GA E n → ℂ) (g : GA E n) : AutomorphicForm.constantTerm n φ g = φ g := by
  haveI : IsEmpty (AutomorphicForm.UPos n n) := ⟨fun p => by have := p.2.2; have := p.1.2.2; omega⟩
  have h1 : AutomorphicForm.unipFundamentalDomain E n n = Set.univ := by
    ext X
    simp [AutomorphicForm.unipFundamentalDomain]
  unfold AutomorphicForm.constantTerm
  rw [h1, Measure.restrict_univ]
  have h2 : ∀ X : AutomorphicForm.UPos n n → AdeleRing (𝓞 E) E, AutomorphicForm.unipGL X = 1 := fun X => by
    rw [Subsingleton.elim X 0, AutomorphicForm.unipGL_zero]
  simp only [h2, one_mul]
  rw [AutomorphicForm.unipMeasure, Measure.pi_of_empty]
  simp

private theorem sph_rt {S : Set (Pl E)} {n : ℕ} {φ : Sm E n} (h : Sph S φ) (k : KA E n) : Sph S (rt E n k φ) :=
  fun w hw => ((((hkOps E n w 0).2.2.2 S φ hw h).2.2.1 k).1) w hw

private theorem len_pos {S : Set (Pl E)} {n : ℕ} (d : Dat S n) (h : 0 < n) : 0 < d.len :=
  (d.idx ⟨0, h⟩).pos

private theorem step {S : Set (Pl E)} {n : ℕ}
    (ih : ∀ m < n, ∀ (ρ : Typ E m) (φ : Sm E m), Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
      (∀ (k : KA E m) (d : Dat S m), d.HasTyp ρ.ρ → d.comp (rt E m k φ).1 = 0) → φ = 0)
    (ρ : Typ E n) (φ : Sm E n) (hU : Umg φ) (hK : Killed ρ.ρ φ.1) (hS : Sph S φ) (R : ℕ) (hR : R ≤ n)
    (H : ∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → (R < n → 2 ≤ d.len) → d.comp (rt E n k φ).1 = 0) :
    ∀ r, 0 < r → r ≤ R → ∀ g, AutomorphicForm.constantTerm r φ.1 g = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
  intro hr hrR
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (hrR.trans hR)
  refine langStep E S r s ρ φ hr hU hK hS (fun r' h0 h1 => ihr r' h1 h0 (h1.le.trans hrR)) ?_
  intro k b hb t
  have hU' : Umg (rt E (r + s) k φ) := ((umgOps E (r + s)).2 φ hU).2.2.2.2.1 _
  obtain ⟨ψ, hψ, hψU, -, hrt, hψS, hψK⟩ := sliceUmg E S r s b t _ hU'
  obtain ⟨-, ⟨ρ', hc, hρ'⟩, hlev⟩ := resTyp E r s ρ
  have h0 : ψ = 0 := by
    refine ih s (by omega) ⟨ρ.d, ρ', hc⟩ ψ hψU ?_ (hψS (sph_rt hS k)) ?_
    · show Killed (⇑ρ') ψ.1
      rw [hρ']
      exact hψK _ _ ((killedOps E _ ρ φ hK).1 k)
    · intro k' d' hd'
      have hd'' : d'.HasTyp (resR ρ.ρ) := by
        rw [← hρ']; exact hd'
      have key := H (⟨_, hlev 1 k'⟩ * k) (Dat.cons b d') ⟨hb, hd''⟩ (fun h => by
        have := len_pos d' (by omega)
        show 2 ≤ d'.len + 1
        omega)
      funext t'
      have := congrFun key (Fin.cons t t' : Fin (d'.len + 1) → ℝ)
      rw [hrt]
      simp only [Dat.comp, Fin.cons_zero, Fin.cons_succ, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
      exact this
  rw [← hψ, h0]
  rfl

private theorem part1 (S : Set (Pl E)) (n : ℕ) : ∀ (ρ : Typ E n) (φ : Sm E n), Umg φ → Killed ρ.ρ φ.1 → Sph S φ →
      (∀ (k : KA E n) (d : Dat S n), d.HasTyp ρ.ρ → d.comp (rt E n k φ).1 = 0) → φ = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ φ hU hK hS H
  refine Subtype.ext (funext fun g => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := congrFun (H 1 Dat.nil trivial) (fun _ => 0)
    rw [Subsingleton.elim g 1]
    simp only [Dat.comp, Subgroup.coe_one, map_one] at this
    exact this
  · have := step ih ρ φ hU hK hS n le_rfl (fun k d hd _ => H k d hd) n hn le_rfl g
    rw [ct_top] at this
    exact this

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.langlands :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.Langlands E := by
  intro E _ _ _ S n ρ φ hU hK hS
  refine ⟨part1 S n ρ φ hU hK hS, fun H r hr hrn => ?_⟩
  exact step (fun m _ => part1 S m) ρ φ hU hK hS r hrn.le (fun k d hd h => H k d hd (h hrn)) r hr le_rfl
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceCap
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem ex_capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : ∃ x, uC E (r + s) x = capR r s τ u :=
  CapFactor.qdet_mem (uC E (r + s)).range _ (fun _ _ => ⟨_, uC_genC τ _ _⟩) _

private theorem ex_capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : ∃ x, uC E (r + s) x = capS r s τ u :=
  CapFactor.qdet_mem (uC E (r + s)).range _ (fun _ _ => ⟨_, uC_genC τ _ _⟩) _

private theorem casimir_commute (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Commute (j1 E r s) (capS r s τ u) := by
  have h2 : capS r s τ u ∈ Subalgebra.centralizer ℂ {j1 E r s} := by
    refine CapFactor.qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    refine Commute.eq ?_
    unfold j1
    refine Commute.smul_left (Commute.sum_left _ _ _ fun σ _ => Commute.sum_left _ _ _ fun i _ => ?_) _
    by_cases h : σ = τ
    · subst h
      exact CapFactor.Eop_commute_blocks r s σ i i k l
    · rw [← uC_genC, ← uC_genC]
      exact (commute_genC h _ _ _ _).map _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.sliceCap :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceCap E := by
  intro E _ _ _ S r s b t φ τ u hφ
  obtain ⟨F, hF, hN, -, hu⟩ := ctOps E r s φ hφ
  obtain ⟨x, hx⟩ := ex_capR r s τ (u - (s : ℂ) / 2)
  obtain ⟨y, hy⟩ := ex_capS r s τ (u + (r : ℂ) / 2)
  have h1 : slice b.f.1 t (cap τ u φ).1 =
      slice b.f.1 t (capR r s τ (u - (s : ℂ) / 2) (capS r s τ (u + (r : ℂ) / 2) φ)).1 := by
    funext m
    unfold slice
    congr 1
    funext z
    congr 1
    have e1 := hu (capC τ u)
    have e2 := hu (y * x)
    rw [uC_capC] at e1
    rw [map_mul, hx, hy] at e2
    have e3 : capR r s τ (u - (s : ℂ) / 2) (capS r s τ (u + (r : ℂ) / 2) φ) =
        (capS r s τ (u + (r : ℂ) / 2) * capR r s τ (u - (s : ℂ) / 2)) φ := by
      rw [← (CapFactor.capR_commute_capS r s τ _ _).eq]; rfl
    rw [← e1, e3, ← e2]
    exact CapFactor.cap_levi E r s τ u F hN _
  have hU : Umg (capS r s τ (u + (r : ℂ) / 2) φ) := by
    rw [← hy]; exact ((umgOps E (r + s)).2 φ hφ).2.2.2.1 y
  rw [h1, sliceCapR E S r s b t _ τ _ hU]
  congr 2
  have hc : Commute (Polynomial.aeval (j1 E r s) (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))))
      (capS r s τ (u + (r : ℂ) / 2)) := by
    generalize (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))) = p
    rw [Polynomial.aeval_eq_sum_range]
    exact Commute.sum_left _ _ _ fun i _ => ((casimir_commute r s τ _).pow_left i).smul_left _
  exact LinearMap.congr_fun hc.eq φ
end
end

