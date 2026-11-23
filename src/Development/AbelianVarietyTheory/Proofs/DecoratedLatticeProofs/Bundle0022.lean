module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalFieldStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_local_field :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
      ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i) := by
  intro k _ _ _ _ N ϖ hϖ μ ν hμ _ n hn g hg hmain
  let ε := indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)
  let T := GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * T ε * κ' at hg
  change ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), T μ * g = κ * T ν * κ' at hmain
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  obtain ⟨κ₁, hκ₁, κ₂, hκ₂, hdecomp⟩ := hmain
  have hϖ₀ : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  have hϖ₁ : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hT (e : Fin N → ℤ) : (T e).1 = diagonal (fun i => (ϖ : k) ^ e i) :=
    GlobalTheory.GLDoubling.val_torusElt ..
  have hsum : ∑ i, ν i = ∑ i, μ i + ∑ i, ε i := by
    have hdet (e : Fin N → ℤ) : valuation k (T e).1.det = valuation k (ϖ : k) ^ ∑ i, e i := by
      rw [hT, det_diagonal, GlobalTheory.CartanDom.val_torus_prod]
    have h := congrArg (fun x : GL (Fin N) k => valuation k x.1.det) hdecomp
    simp only [Units.val_mul, det_mul, map_mul] at h
    rw [hdet, hdet, GlobalTheory.CartanDom.KO_det hκ, GlobalTheory.CartanDom.KO_det hκ',
      GlobalTheory.CartanDom.KO_det hκ₁, GlobalTheory.CartanDom.KO_det hκ₂] at h
    simp only [hdet, mul_one, one_mul] at h
    rw [← zpow_add₀ hϖ₀.ne'] at h
    exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.le)
      ((zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h.ge)
  have hε : Antitone ε := GlobalTheory.CartanDom.indic_antitone N n
  have hcard : ∑ i, ε i = n := GlobalTheory.CartanDom.sum_indic N n hn
  refine ⟨hsum.trans (congrArg ((∑ i, μ i) + ·) hcard), fun j => ?_⟩
  let tail := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j)
  have htail : (∑ i ∈ tail, μ i) + (∑ i ∈ tail, ε i) ≤ ∑ i ∈ tail, ν i := by
    by_cases hj : j < N
    swap
    · have hempty : tail = ∅ := by
        ext i
        simp [tail]
        omega
      simp [hempty]
    let I := {i : Fin N // ¬ (i : ℕ) < j}
    have hA (f h : I → Fin N) :
        valuation k (((T ε).1 * κ'.1).submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ ε hε j hj κ'.1 1
        (fun f h => GlobalTheory.CartanDom.val_det_le_one _
          (fun a b => GlobalTheory.CartanDom.KO_int hκ' (f a) (h b))) f h
    have hB (f h : I → Fin N) :
        valuation k ((κ * T ε * κ').1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1 := by
      rw [Units.val_mul, Units.val_mul, mul_assoc]
      exact GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int hκ) hA f h
    have hC (f h : I → Fin N) :
        valuation k ((T μ * (κ * T ε * κ')).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [Units.val_mul (T μ), hT]
      exact GlobalTheory.CartanDom.tail_diag ϖ hϖ μ hμ j hj _ _ hB f h
    have hνdecomp : T ν = κ₁⁻¹ * (T μ * (κ * T ε * κ')) * κ₂⁻¹ := by
      rw [hdecomp]
      group
    have hD (f h : I → Fin N) :
        valuation k ((T ν).1.submatrix f h).det ≤
          valuation k (ϖ : k) ^ (∑ i ∈ tail, μ i) *
            (valuation k (ϖ : k) ^ (∑ i ∈ tail, ε i) * 1) := by
      rw [hνdecomp, Units.val_mul, Units.val_mul]
      exact GlobalTheory.CartanDom.minor_mul_int _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₂))
        (GlobalTheory.CartanDom.minor_int_mul _ _ _ (GlobalTheory.CartanDom.KO_int (inv_mem hκ₁)) hC) f h
    have h := hD Subtype.val Subtype.val
    rw [hT, submatrix_diagonal _ _ Subtype.val_injective, det_diagonal] at h
    simp only [Function.comp_apply] at h
    rw [GlobalTheory.CartanDom.val_torus_prod, mul_one, ← zpow_add₀ hϖ₀.ne'] at h
    have hle := (zpow_le_zpow_iff_right_of_lt_one₀ hϖ₀ hϖ₁).1 h
    rwa [← Finset.sum_subtype tail (fun i => by simp [tail]) ν] at hle
  have hνsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ν
  have hμsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) μ
  have hεsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j) ε
  change ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + ε i)
  rw [Finset.sum_add_distrib]
  dsimp only [tail] at htail
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrderStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.ZonalInduct (pot pot_lt pot_nonneg pos_iff_lt psum nonneg_of_dom) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_dominance_order :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 →
    (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧
      ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        x = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
    (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
          (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ μ * g =
          κ * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
            (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) →
    (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) →
    ∀ h : GL (Fin N) k → ℂ,
      (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) →
      (∀ (s : Finset (Fin N)) R,
        IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R →
          ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) →
      h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  let torus := GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ
  have torus_add (a b : Fin N → ℤ) : torus (a + b) = torus a * torus b := by
    apply Units.ext
    simp only [torus, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt, diagonal_mul_diagonal]
    congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]
  have torus_zero : torus (fun _ => 0) = 1 := by
    apply Units.ext
    rw [GlobalTheory.GLDoubling.val_torusElt]; simp
  have torus_one_comm (g : GL (Fin N) k) :
      g * torus (fun _ => 1) = torus (fun _ => 1) * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  have vanish_of_shift (j : ℕ) (m : GL (Fin N) k)
      (hm : h (m * torus (fun _ => (j : ℤ))) = 0) : h m = 0 := by
    induction j generalizing m with
    | zero => simpa [torus_zero] using hm
    | succ j ih =>
      apply ih
      have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
      obtain ⟨R, hR⟩ := hex (torus (indic Finset.univ))
      set z := torus (fun _ => 1) with hzdef
      set m' := m * torus (fun _ => (j : ℤ))
      have hsplit : torus (fun _ => ((j + 1 : ℕ) : ℤ)) = torus (fun _ => (j : ℤ)) * z := by
        rw [hzdef, ← torus_add]; congr 1
      have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
      have key := hT Finset.univ R hR m'
      have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
        intro g hg
        obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
        rw [hz] at *
        have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
          rw [torus_one_comm]
          simp only [mul_assoc]
        rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
      rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
      exact (mul_eq_zero.1 key.symm).resolve_left hc
  have vanish_dominant :
      ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torus e) = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih e ha he hpot
    have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
        h (torus ν) = 0 := by
      intro ν hν hν0 hlt
      have h0 := pot_nonneg hν0
      exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
    by_cases hzero : ∀ i, e i = 0
    · have : e = fun _ => 0 := funext hzero
      rw [this, torus_zero, h1]
    push Not at hzero
    obtain ⟨i₀, hi₀⟩ := hzero
    have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
    have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
    have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
    obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
    have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
      intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
    have hscard : s.card = n₀ := by
      rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
    set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
    have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
    have hμa : Antitone μ := by
      intro i j hij
      have := ha hij; have hi := he i; have hj := he j
      simp only [hμdef, hind]
      split_ifs <;> omega
    have hμ0 : ∀ i, 0 ≤ μ i := by
      intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
    have hμlt : pot μ < pot e := by
      apply pot_lt
      · intro j; unfold psum
        exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
      · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, ite_eq_left hi₀pos] at this; omega
    have hμv := IH μ hμa hμ0 hμlt
    have hTe : torus e = torus μ * torus (indic s) := by
      rw [← torus_add]; congr 1; funext i; exact (hμe i).symm
    have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
      rw [← hscard]; simp [indic]
    obtain ⟨R, hR⟩ := hex (torus (indic s))
    have hsum := hT s R hR (torus μ)
    rw [hμv, mul_zero] at hsum
    have hterm : ∀ g ∈ R, h (torus μ * g) = 0 ∨
        h (torus μ * g) = h (torus e) := by
      intro g hg
      obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torus μ * g)
      have hval : h (torus μ * g) = h (torus ν) := by
        rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
      obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
      have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
      simp only [← hs] at hd
      obtain ⟨hd1, hd2⟩ := hd
      have hle : ∀ j, psum ν j ≤ psum e j := by
        intro j; have := hd2 j; simp only [hμe] at this; exact this
      have hsumeq : ∑ i, ν i = ∑ i, e i := by
        rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
      have hν0 := nonneg_of_dom hν he hle hsumeq
      by_cases hνe : ν = e
      · right; rw [hval, hνe]
      · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
    obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
    have hg₁ : h (torus μ * g₁) = h (torus e) := by
      have e1 : torus μ * g₁ =
          torus e * (g₁⁻¹ * (1 * torus (indic s)))⁻¹ := by
        rw [hTe]; group
      rw [e1, (hK _ (inv_mem hg₁K) _).2]
    by_contra hx
    have hite : ∀ g ∈ R, h (torus μ * g) =
        if h (torus μ * g) = h (torus e) then h (torus e) else 0 := by
      intro g hg
      rcases hterm g hg with h0 | h0
      · rw [h0, ite_eq_right (Ne.symm hx)]
      · rw [ite_eq_left h0]; exact h0
    rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul] at hsum
    have hcard : (R.filter fun g => h (torus μ * g) = h (torus e)).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
    rcases mul_eq_zero.1 hsum with hc0 | hc0
    · exact hcard (by exact_mod_cast hc0)
    · exact hx hc0
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  change h (torus ν) = 0
  let j := (∑ i, |ν i|).toNat
  apply vanish_of_shift j
  rw [← torus_add]
  refine vanish_dominant (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
section
open MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx

section Gen
variable {k : Type} [Field k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]

def fillAt (β : Matrix R Q k) (E I : Finset (R × Q)) (x : Matrix R Q k) (y : I → k) : Matrix R Q k :=
  Matrix.of fun r q => if h : (r, q) ∈ I then y ⟨(r, q), h⟩ else if (r, q) ∈ E then β r q else x r q

variable [TopologicalSpace k] [MeasurableSpace k]

def red (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k) : ℂ :=
  ∫ y : I → k, Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ) ∂(Measure.pi fun _ => ν)

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Kills (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) : Prop :=
  ∀ Φ : SB (Matrix R Q k), red ψ ν w β E I Φ.1 = 0 → L Φ = 0

def EvalLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (b : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = (ψ (b * (x e.1 e.2 - β e.1 e.2)) : ℂ) * red ψ ν w β E I Φ.1 x

def IntLaw (L : SB (Matrix R Q k) →ₗ[ℂ] M) (ψ : AddChar k Circle) (ν : Measure k) (w : Matrix R Q k →ₗ[k] k)
    (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) : Prop :=
  ∀ (a : k) (Φ : SB (Matrix R Q k)), ∃ Φ' : SB (Matrix R Q k), L Φ' = L Φ ∧
    ∀ x, red ψ ν w β E I Φ'.1 x = red ψ ν w β E I Φ.1 (x + Matrix.single e.1 e.2 a)

end Gen

section Flat
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def chL : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k →ₗ[k] k where
  toFun := ch
  map_add' x y := by simp [ch, Finset.sum_add_distrib]
  map_smul' a x := by simp [ch, Finset.mul_sum]

theorem chL_apply (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : chL x = ch x := rfl


open Classical in
def fixSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => (∃ i, e.2 = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) e) ∨
    (∃ l s, e.1 = Sum.inr l ∧ ρ < l.val ∧ e.2 = Sum.inl s)


open Classical in
def transSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => Free (ρ + 1) e ∧ ∀ i, e.2 = Sum.inr i → ρ < i.val


open Classical in
def lowSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ ρ < i.val ∧ i.val ≤ l.val


open Classical in
def upSet (ρ : ℕ) : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) :=
  Finset.univ.filter fun e => ∃ (l : Fin c) (i : Fin (c + 1)), e = (Sum.inr l, Sum.inr i) ∧ l.val < i.val ∧ i.val ≤ ρ

def colIx (e : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))) : ℕ := Sum.elim (fun _ => 0) (fun i => i.val) e.2

end Flat

end GlobalTheory.PartRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLevi
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PClassAlg

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_aX (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (l : Fin c) (y : n) :
    B (Sum.inr l) (Sum.inl y) = 0 := by
  by_cases h : l.val + 1 < p
  · apply h2
    show OrderDual.toDual (lev p (Sum.inl y : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr l : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega

theorem shape_aa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i j : Fin c) (hij : i ≠ j) :
    B (Sum.inr i) (Sum.inr j) = 0 := by
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr j : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c))
    simp only [lev, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inr]; omega

theorem shape_Xa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (i : Fin c) (hi : i.val + 1 ≠ p) :
    B (Sum.inl x) (Sum.inr i) = 0 := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inl x : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega

theorem eq_fromBlocks (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  congr 1
  ext l y; exact shape_aX hp B h1 h2 l y

theorem diag_block (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toBlocks₂₂]
  · simp [toBlocks₂₂, diagonal_apply_ne _ h, shape_aa B h1 h2 i j h]

end GlobalTheory.PClassAlg

namespace GlobalTheory.PClassAlg

theorem blockDiag_mem_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  intro k _ _ _ _ ϖ n _ _ c p hp hpc A hA1 hA2 hB1 hB2 hD hE
  have eA := eq_fromBlocks hp _ hA1 hA2
  have eB := eq_fromBlocks hp _ hB1 hB2
  have dA := diag_block _ hA1 hA2
  have dB := diag_block _ hB1 hB2
  have sXa := shape_Xa _ hA1 hA2
  set P := toBlocks₁₁ A.val
  set Q := toBlocks₁₂ A.val
  set S := toBlocks₂₂ A.val
  set P' := toBlocks₁₁ (A⁻¹).val
  set Q' := toBlocks₁₂ (A⁻¹).val
  set S' := toBlocks₂₂ (A⁻¹).val
  have hAB : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have hBA : (A⁻¹).val * A.val = 1 := Units.inv_mul A
  rw [eA, eB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hAB hBA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hAB hBA
  obtain ⟨hPP', hPQ, -, -⟩ := hAB
  obtain ⟨hP'P, -, -, -⟩ := hBA
  let γ : GL n k := ⟨P', P, hP'P, hPP'⟩
  have hpow : ∀ i : Fin c, (((ϖ ^ (i.val + 1) : kˣ)) : k) = (ϖ : k) ^ (i.val + 1) := fun i => by simp
  have hne : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  refine ⟨γ, (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨?_, ?_⟩⟩
  · have hM : (A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))).val =
        fromBlocks (P * P') (Q * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) 0
          (S * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
      rw [Units.val_mul, Units.val_mul, eA]
      show fromBlocks P Q 0 S * fromBlocks P' 0 0 1 * fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val = _
      simp [fromBlocks_multiply, hpow]
    rw [hM, hPP']
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, mul_diagonal]
      by_cases h : i.val + 1 = p
      · exact hE i h x
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, mul_diagonal, dA]
      by_cases h : l = i
      · subst h; simpa using (hD l).1
      · simp [diagonal_apply_ne _ h]

  · have hM : ((A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)))⁻¹).val =
        fromBlocks (P * P') (P * Q') 0
          ((diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) * S') := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, Units.val_mul, Units.val_mul, eB]
      show fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val *
        (fromBlocks P 0 0 1 * fromBlocks P' Q' 0 S') = _
      have : ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val =
          diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹ := by
        ext i j; simp [GlobalTheory.SplitFlip.diagGL, diagonal_apply]
      rw [this]
      simp [fromBlocks_multiply]
    have hPQ' : P * Q' = -(Q * S') := eq_neg_of_add_eq_zero_left hPQ
    rw [hM, hPP', hPQ', dB]
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, mul_diagonal]
      by_cases h : i.val + 1 = p
      · have e : Q x i * (A⁻¹).val (Sum.inr i) (Sum.inr i) =
            (A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1)) *
              ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) := by
          have := hne i
          simp only [Q, toBlocks₁₂, of_apply]
          field_simp
        rw [e]
        exact neg_mem (mul_mem (hE i h x) (hD i).2)
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, diagonal_mul_diagonal, diagonal_apply]
      split_ifs with h
      · subst h; rw [mul_comm]; exact (hD l).2
      · exact zero_mem _

end GlobalTheory.PClassAlg
end
end

