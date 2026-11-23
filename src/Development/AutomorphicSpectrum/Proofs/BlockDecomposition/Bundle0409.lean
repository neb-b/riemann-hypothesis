module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsValueSubset
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
open GlobalTheory.CompanionTheory.LbElem.ConjMonomial GlobalTheory.CompanionTheory.LbElem.MonomialInJ GlobalTheory.CompanionTheory.LbElem.IwahoriLDU

namespace GlobalTheory.CompanionTheory.LbElem.JPredDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry_diag_mul {N : ℕ} {a b : GL (Fin N) k} (n : GL (Fin N) k) {α β : Fin N → k}
    (ha : (a : Matrix (Fin N) (Fin N) k) = Matrix.diagonal α)
    (hb : (b : Matrix (Fin N) (Fin N) k) = Matrix.diagonal β) (i j : Fin N) :
    ((a * n * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      α i * (n : Matrix (Fin N) (Fin N) k) i j * β j := by
  rw [Units.val_mul, Units.val_mul, ha, hb, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem diag_ne_zero {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (i : Fin N) : d i ≠ 0 := by
  have h := diag_ne_zero_of_offDiag x (fun i j hij => by rw [hx, Matrix.diagonal_apply_ne _ hij]) i
  rwa [hx, Matrix.diagonal_apply_eq] at h

theorem val_inv_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) :
    ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
  have h1 : (x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [hx, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (diag_ne_zero hx i)
  calc ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((x⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *
          ((x : Matrix (Fin N) (Fin N) k) * Matrix.diagonal (fun i => (d i)⁻¹)) := by rw [h1, mul_one]
    _ = Matrix.diagonal fun i => (d i)⁻¹ := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem val_pow_diag {N : ℕ} {x : GL (Fin N) k} {d : Fin N → k}
    (hx : (x : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d) (r : ℕ) :
    ((x ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => d i ^ r := by
  rw [Units.val_pow_eq_pow_val, hx, Matrix.diagonal_pow]
  rfl

theorem val_conj_up (a b c : k) (r : ℕ) :
    valuation k (a ^ r * c * (b ^ r)⁻¹) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [map_mul, map_mul, map_inv₀, map_pow, map_pow, div_pow, div_eq_mul_inv, mul_right_comm]

theorem val_conj_lo (a b c : k) (r : ℕ) :
    valuation k ((b ^ r)⁻¹ * c * a ^ r) = (valuation k a / valuation k b) ^ r * valuation k c := by
  rw [← val_conj_up]
  congr 1
  ring

theorem up_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, j < i → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, j < i → ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, ((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k (((t ^ r * n * (t ^ r)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d i) / valuation k (d j)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hp hq
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_up _ _ _ r

theorem lo_entries {N : ℕ} {t n : GL (Fin N) k} {d : Fin N → k}
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (h0 : ∀ i j : Fin N, i < j → (n : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i : Fin N, (n : Matrix (Fin N) (Fin N) k) i i = 1) (r : ℕ) :
    (∀ i j : Fin N, i < j → (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0) ∧
    (∀ i : Fin N, (((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i = 1) ∧
    ∀ i j : Fin N, valuation k ((((t ^ r)⁻¹ * n * t ^ r : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) =
      (valuation k (d j) / valuation k (d i)) ^ r * valuation k ((n : Matrix (Fin N) (Fin N) k) i j) := by
  have hp := val_pow_diag ht r
  have hq := val_inv_diag hp
  have he := entry_diag_mul n hq hp
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he, h0 i j hij, mul_zero, zero_mul]
  · rw [he, h1, mul_one]
    exact inv_mul_cancel₀ (pow_ne_zero _ (diag_ne_zero ht i))
  · rw [he]
    exact val_conj_lo _ _ _ r

theorem ratio_lt_one {a b : ValueGroupWithZero k} (h : a < b) : a / b < 1 :=
  (div_lt_one₀ (lt_of_le_of_lt zero_le' h)).2 h

theorem exists_contract {N : ℕ} {d : Fin N → k} (hd : ∀ i, d i ≠ 0)
    (hinc : ∀ i j : Fin N, i < j → valuation k (d i) < valuation k (d j))
    {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ℕ, ∀ i j : Fin N, i < j → (valuation k (d i) / valuation k (d j)) ^ r < γ := by
  classical
  have h : ∀ p : Fin N × Fin N, ∃ r : ℕ, p.1 < p.2 → ∀ r' : ℕ, r ≤ r' →
      (valuation k (d p.1) / valuation k (d p.2)) ^ r' < γ := by
    intro p
    by_cases hp : p.1 < p.2
    · have h1 := ratio_lt_one (hinc _ _ hp)
      have h2 : valuation k (d p.1) / valuation k (d p.2) ≠ 0 :=
        div_ne_zero ((Valuation.ne_zero_iff _).2 (hd _)) ((Valuation.ne_zero_iff _).2 (hd _))
      obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_pow_succ_lt h2 h1 hγ
      exact ⟨m + 1, fun _ r' hr' => lt_of_le_of_lt (pow_le_pow_of_le_one zero_le' h1.le hr') hm⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using h
  exact ⟨Finset.univ.sup f, fun i j hij => hf (i, j) hij _ (Finset.le_sup (Finset.mem_univ _))⟩

theorem levi_comm {N : ℕ} (s x : Levi k (Bl (ones N))) : s * x = x * s := by
  funext a
  haveI : Subsingleton (Fin (ones N a)) := by
    show Subsingleton (Fin 1)
    infer_instance
  apply Units.ext
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  simp only [Units.val_mul, Matrix.mul_apply, Pi.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem torEmb_diag {N : ℕ} (s : Levi k (Bl (ones N))) :
    ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((torEmb k N s : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i i := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact tor_offDiag (⟨s, rfl⟩ : torEmb k N s ∈ Tor k N) h

theorem sub_one_le {N : ℕ} {x : GL (Fin N) k} {γ : ValueGroupWithZero k}
    (h1 : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i = 1)
    (h2 : ∀ i j, i ≠ j → valuation k ((x : Matrix (Fin N) (Fin N) k) i j) ≤ γ) (i j : Fin N) :
    valuation k ((x : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ := by
  by_cases h : i = j
  · subst h
    rw [h1, Matrix.one_apply_eq, sub_self, map_zero]
    exact zero_le'
  · rw [Matrix.one_apply_ne h, sub_zero]
    exact h2 i j h

theorem exists_value_subset {N : ℕ} {U : Set (GL (Fin N) k)} (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ g : GL (Fin N) k, (∀ i j,
      valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ γ) → g ∈ U := by
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2 Zls.irreducible_unif.ne_zero
  obtain ⟨M, -, hsub⟩ := GlobalTheory.CompanionTheory.CongruenceBasis.exists_congruence_subset k N _ hne
    GlobalTheory.CompanionTheory.CongruenceBasis.val_unif_lt_one GlobalTheory.CompanionTheory.CongruenceBasis.val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨_, (Valuation.ne_zero_iff _).2 (pow_ne_zero M hne), fun g hg => hsub hg⟩

end GlobalTheory.CompanionTheory.LbElem.JPredDom

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentLtOfPrecedes
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SegExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow_nat (t : kˣ) (n : ℕ) : nabs k (t ^ n) = nabs k t ^ n := by
  induction n with
  | zero => simp [nabs]
  | succ n ih => rw [pow_succ, pow_succ, nabs_mul', ih]

theorem norm_absPow_nat (n : ℕ) (u : kˣ) : ‖((absPow k ((n : ℕ) : ℂ) u : ℂˣ) : ℂ)‖ = nabs k u ^ n := by
  have h : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; rfl
  rw [h, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k u).le _),
    Real.rpow_natCast]

theorem cast_tri (l : ℕ) (hl : 0 < l) : (((l * (l - 1) / 2 : ℕ)) : ℝ) = (l : ℝ) * ((l : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ l * (l - 1) := (Nat.even_mul_pred_self l).two_dvd
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hl]
  norm_num

theorem exponent_lseg (Δ : Segment k) (y : IrrGL (k := k)) (s e : ℝ) (t : kˣ) (c : ℂ) (ht : nabs k t < 1)
    (hL : IsLSeg Δ y.rep) (hc : Zl.ScalarBy Δ.first t c) (hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e))
    (hy : ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) :
    s = e + ((Δ.len : ℝ) - 1) / 2 := by
  have h1 := GlobalTheory.T.segment_rep_central_character k Δ y hL t c hc
  have h2 := hy t _ h1
  have hdeg : y.1 = Δ.len * Δ.d := hL.deg_eq.symm
  have hα : 0 < nabs k t := nabs_pos' k t
  have hlog : Real.log (nabs k t) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hα ht.ne
  rw [norm_mul, norm_pow, norm_absPow_nat, nabs_pow_nat, hcn, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hα.le, ← Real.rpow_mul hα.le,
    ← Real.rpow_add hα] at h2
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow hα, Real.log_rpow hα] at h3
  have h4 := mul_right_cancel₀ hlog h3
  rw [cast_tri _ Δ.len_pos, hdeg] at h4
  have hl : (0 : ℝ) < Δ.len := by exact_mod_cast Δ.len_pos
  have hd : (0 : ℝ) < Δ.d := by exact_mod_cast Δ.d_pos
  push_cast at h4
  have h5 : (Δ.len : ℝ) * Δ.d * (s - (e + ((Δ.len : ℝ) - 1) / 2)) = 0 := by linear_combination -h4
  have h6 := (mul_eq_zero.1 h5).resolve_left (by positivity)
  linarith

theorem len_lt_of_precedes {Δ Δ' : Segment k} {j : ℕ} (hl : Δ.Linked Δ') (hf : Δ'.first = Δ.first.nu j) :
    Δ.len < j + Δ'.len := by
  by_contra hcon
  refine hl.2.2 fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
  refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
  rw [hf, IrrGL.nu_nu]
  push_cast
  rfl

theorem exponent_lt_of_precedes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ Δ' : Segment k) (y y' : IrrGL (k := k)) (s s' : ℝ), IsLSeg Δ y.rep → IsLSeg Δ' y'.rep → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y t c → ‖c‖ = nabs k t ^ ((y.1 : ℝ) * s)) → (∀ (t : kˣ) (c : ℂ), Zl.ScalarBy y' t c → ‖c‖ = nabs k t ^ ((y'.1 : ℝ) * s')) → Δ.Precedes Δ' → s < s' := by
  intro k _ _ _ _ Δ Δ' y y' s s' hL hL' hy hy' hP
  obtain ⟨hlink, j, hj, hf⟩ := hP
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.CompanionTheory.LocalFieldPow.exists_unit_pow_tendsto_zero k
  have hα1 : nabs k t < 1 := GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow k t ht
  have hα : 0 < nabs k t := nabs_pos' k t
  obtain ⟨e, he⟩ := GlobalTheory.T.central_character_norm_eq_pow k Δ.first Δ.isCusp_first.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.central_character_exists k Δ.first t
  have hcn : ‖c‖ = nabs k t ^ ((Δ.d : ℝ) * e) := he t c hc
  have hdd : Δ'.d = Δ.d := congrArg Sigma.fst hf
  have hc' : Zl.ScalarBy Δ'.first t (c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)) := by
    rw [hf]
    exact GlobalTheory.CompanionTheory.Dblock.scalarBy_nu k Δ.first _ t c hc
  have hcn' : ‖c * ((absPow k ((j : ℕ) : ℂ) (t ^ Δ.first.1) : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((Δ'.d : ℝ) * (e + j)) := by
    rw [norm_mul, norm_absPow_nat, nabs_pow_nat, hcn, hdd, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hα.le, ← Real.rpow_add hα]
    congr 1
    show (Δ.d : ℝ) * e + (Δ.d : ℝ) * j = _
    ring
  have h1 := exponent_lseg Δ y s e t c hα1 hL hc hcn hy
  have h2 := exponent_lseg Δ' y' s' (e + j) t _ hα1 hL' hc' hcn' hy'
  have h3 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast len_lt_of_precedes hlink hf
  have h4 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [h1, h2]
  linarith

end GlobalTheory.CompanionTheory.SegExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSphNe
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter Function
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.UnitaryWord

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F.U

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev unitFn (n : ℕ) (w : Pl E) : UL n w → ℂ := (KL n w : Set (UL n w)).indicator 1

theorem isHecke_zero {w : Pl E} (K' : Subgroup (UL n w)) : IsHecke K' (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem isHecke_lone (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    IsHecke K' (lone K') :=
  (hL E n w (SmIrr.triv _) K' hK 0 0 (isHecke_zero K') (isHecke_zero K')).2.2.2.2.2.2.1

theorem isHecke_lconv (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {f₁ f₂ : UL n w → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) : IsHecke K' (lconv f₁ f₂) :=
  (hL E n w (SmIrr.triv _) K' hK f₁ f₂ h₁ h₂).2.2.1

theorem lone_KL (w : Pl E) : lone (KL n w) = unitFn n w := by
  simp [lone, unitFn, Subgroup.relIndex_self]
  rfl

theorem isHecke_lpow (hL : LocAlg) {w : Pl E} {K' : Subgroup (UL n w)} (hK : IsLevel (MonoidHom.id _) (KL n w) K')
    {g : UL n w → ℂ} (hg : IsHecke K' g) (k : ℕ) : IsHecke K' (lpow K' g k) := by
  induction k with
  | zero => exact isHecke_lone hL hK
  | succ k ih => exact isHecke_lconv hL hK hg ih

section Fam

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  (F : UFam S lam K') {B : Finset (Pl E)}

end Fam

end GlobalTheory.CompanionTheory.UnitaryWord

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintLevel

theorem finsum_out_of_le {H : Type} [Group H] {L S : Subgroup H} (u : H → ℂ) (hLS : L ≤ S)
    (hS : S ≤ rStab u) (hm : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ c : H ⧸ S, u c.out := by
  have hm' : Nat.card (S ⧸ L.subgroupOf S) ≠ 0 := hm
  haveI : Finite (S ⧸ L.subgroupOf S) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hLS
  have hfst : ∀ q : H ⧸ L, (e q).1 = ((q.out : H) : H ⧸ S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : H ⧸ L)).1 = (g : H ⧸ S) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hLS (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : H ⧸ L)).symm))
  have hg : ∀ q : H ⧸ L, u q.out = u (e q).1.out := by
    intro q
    rw [hfst q]
    have hk : (((q.out : H) : H ⧸ S).out)⁻¹ * q.out ∈ S :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((q.out : H) : H ⧸ S))
    have := hS hk (((q.out : H) : H ⧸ S).out)
    simpa using this
  have hcomp : ∑ᶠ q : H ⧸ L, u q.out =
      ∑ᶠ p : (H ⧸ S) × (S ⧸ L.subgroupOf S), u p.1.out := by
    rw [← finsum_comp_equiv e]
    exact finsum_congr hg
  rw [hcomp]
  by_cases hfin : (Function.support fun c : H ⧸ S => u c.out).Finite
  · have hsupp : (Function.support fun p : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u p.1.out).Finite := by
      refine (hfin.prod (Set.finite_univ (α := S ⧸ L.subgroupOf S))).subset ?_
      intro p hp
      exact ⟨hp, Set.mem_univ _⟩
    rw [finsum_curry _ hsupp]
    have hin : ∀ c : H ⧸ S, ∑ᶠ _ : S ⧸ L.subgroupOf S, u c.out = ((L.relIndex S : ℕ) : ℂ) * u c.out := by
      intro c
      haveI := Fintype.ofFinite (S ⧸ L.subgroupOf S)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl
    simp only [hin]
    rw [mul_finsum]
  · have h0 : ∑ᶠ c : H ⧸ S, u c.out = 0 := finsum_of_infinite_support hfin
    rw [h0, mul_zero]
    refine finsum_of_infinite_support fun hsupp => hfin ?_
    refine (hsupp.image Prod.fst).subset ?_
    intro c hc
    exact ⟨(c, ((1 : S) : S ⧸ L.subgroupOf S)), hc, rfl⟩

theorem hint_eq_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hfin
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have hm : L.relIndex (rStab u ⊓ K) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  rw [finsum_out_of_le u hLS inf_le_left hm, ← hmul, hint]
  have hmC : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.HintLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure Good (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) : Prop where
  left : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g
  level : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : GlobalTheory.UAut.IsSm σ J φ
  growth : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ A
  cusp : IsCuspidal σ J φ

def CloseInf (u : GAd σ J) (δ : ℝ) : Prop :=
  u ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
    ‖(archMat σ J τ (projArch σ J w u) - 1) i j‖ ≤ δ

variable {σ J}

def pre (X : Matrix (Fin n) (Fin r) E) (s : Fin r) : Matrix (Fin n) (Fin (s.val + 1)) E :=
  X.submatrix id (Fin.castLE s.2)

def ratio (t : Fin r → ℝ) (s : Fin r) : ℝ :=
  if h : s.val + 1 < r then t s / t ⟨s.val + 1, h⟩ else t s

def rbar (t : Fin r → ℝ) : ℝ := Finset.univ.fold max 1 (ratio t)

theorem one_le_rbar (t : Fin r → ℝ) : 1 ≤ rbar t := Finset.le_fold_max _ |>.2 (Or.inl le_rfl)

theorem ratio_le_rbar (t : Fin r → ℝ) (s : Fin r) : ratio t s ≤ rbar t :=
  (Finset.le_fold_max _).2 (Or.inr ⟨s, Finset.mem_univ s, le_rfl⟩)

theorem rbar_eq (t : Fin r → ℝ) : rbar t = 1 ∨ ∃ s, rbar t = ratio t s := by
  have key : ∀ S : Finset (Fin r), S.fold max 1 (ratio t) = 1 ∨ ∃ s, S.fold max 1 (ratio t) = ratio t s := fun S => by
    induction S using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert a S ha ih =>
      rw [Finset.fold_insert ha]
      rcases max_choice (ratio t a) (S.fold max 1 (ratio t)) with e | e
      · exact Or.inr ⟨a, e⟩
      · rw [e]; exact ih
  exact key _

theorem ratio_pos {c : ℝ} {t : Fin r → ℝ} (ht : t ∈ cone r c) (s : Fin r) : 0 < ratio t s := by
  unfold ratio
  split_ifs with h
  · exact div_pos (ht.1 _) (ht.1 _)
  · exact ht.1 _

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing

namespace GlobalTheory.CompanionTheory.KoszulCount

def germSec {X : Scheme.{0}} {L : LB X} (s : L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    X.presheaf.stalk x :=
  X.presheaf.germ (L.U i) x hx (s.f i)

def CotIndep {X : Scheme.{0}} {L : LB X} {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun j : {j : Fin d // germSec (t j) hx ∈ maximalIdeal (X.presheaf.stalk x)} =>
        ((maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
          CotangentSpace (X.presheaf.stalk x)))

def GoodStalks {X : Scheme.{0}} {L : LB X} (F : X.Modules) {d : ℕ} (t : Fin d → L.Sec) : Prop :=
  ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
    RingTheory.Sequence.IsWeaklyRegular (F.presheaf.stalk x :)
        (List.ofFn fun j => germSec (t j) hx) ∧
      Module.length (X.presheaf.stalk x)
        ((F.presheaf.stalk x :) ⧸ (Ideal.span (Set.range fun j => germSec (t j) hx) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))) ≤ 1

end GlobalTheory.CompanionTheory.KoszulCount
end
end

