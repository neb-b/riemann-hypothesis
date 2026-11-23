module

public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0009
public import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
section
noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.RT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Polynomial CategoryTheory Formalism.MainNotions.PairedCharacterCondition

section Reps

open Formalism.IrreducibleCountingLemmas.TYPES (RepIso)

variable {Γ : Type} [Group Γ]

variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

end Reps

section Blocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem twoBlock_eq_zero {n a : ℕ} (i : Fin n) : twoBlock n a i = 0 ↔ (i : ℕ) < a := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem twoBlock_eq_one {n a : ℕ} (i : Fin n) : twoBlock n a i = 1 ↔ a ≤ (i : ℕ) := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

def blk0 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 0} ≃ Fin a where
  toFun i := ⟨i.1, (twoBlock_eq_zero i.1).1 i.2⟩
  invFun j := ⟨⟨j, by omega⟩, (twoBlock_eq_zero _).2 j.2⟩
  left_inv i := by rcases i with ⟨⟨i, hi⟩, h⟩; rfl
  right_inv j := by rcases j with ⟨j, hj⟩; rfl

def blk1 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 1} ≃ Fin b where
  toFun i := ⟨i.1 - a, by have := (twoBlock_eq_one i.1).1 i.2; have := i.1.2; omega⟩
  invFun j := ⟨⟨a + j, by omega⟩, (twoBlock_eq_one _).2 (by simp)⟩
  left_inv i := by
    rcases i with ⟨⟨i, hi⟩, h⟩
    have hai : a ≤ i := (twoBlock_eq_one _).1 h
    apply Subtype.ext
    apply Fin.ext
    show a + (i - a) = i
    omega
  right_inv j := by
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def pairRep {a b : ℕ} (ρ : FDRep ℂ (GL (Fin a) K)) (ρ' : FDRep ℂ (GL (Fin b) K)) :
    ∀ c : Fin 2, FDRep ℂ (GL {i : Fin (a + b) // twoBlock (a + b) a i = c} K)
  | 0 => transp (blk0 a b).symm ρ
  | 1 => transp (blk1 a b).symm ρ'

end Blocks

section Comparison₂

open Formalism.IrreducibleCountingLemmas.TYPES

def castIrr {g : ℕ} (L : LzData g) {a a' : ℕ} (h : a = a') (τ : L.Irr a) : L.Irr a' := h ▸ τ

structure LzTie {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)
    (L : LzData g) where
  rep : ∀ {a : ℕ}, L.Irr a → FDRep ℂ (GL (Fin a) (ZMod g))
  rep_simple : ∀ {a : ℕ} (τ : L.Irr a), Simple (rep τ)
  rep_inj : ∀ {a : ℕ} (τ σ : L.Irr a), RepIso (rep τ).ρ (rep σ).ρ → τ = σ
  rep_surj : ∀ {a : ℕ} (σ : FDRep ℂ (GL (Fin a) (ZMod g))), Simple σ → ∃ τ, RepIso σ.ρ (rep τ).ρ
  idem_eq : ∀ {a : ℕ} (τ : L.Irr a), L.idem τ = zIdem (rep τ)
  lab_eq : ∀ {a : ℕ} (τ : L.Irr a), 1 ≤ a → HasLabelO O (rep τ) (L.lab τ)
  real : ∀ {a : ℕ}, L.Rep a → FDRep ℂ (GL (Fin a) (ZMod g))
  real_ext : ∀ {a : ℕ} (R R' : L.Rep a), RepIso (real R).ρ (real R').ρ → R = R'
  real_ofIrr : ∀ {a : ℕ} (τ : L.Irr a), RepIso (real (L.ofIrr τ)).ρ (rep τ).ρ
  cons_iff : ∀ {a : ℕ} (R : L.Rep a) (σ : L.Irr a), L.cons R σ ↔ IsConstituent (rep σ) (real R).ρ
  real_hc : ∀ {a b : ℕ} (τ : L.Irr a) (τ' : L.Irr b), 1 ≤ a → 1 ≤ b →
    RepIso (real (L.hc τ τ')).ρ (hcRep (ZMod g) (twoBlock (a + b) a) (pairRep (rep τ) (rep τ')))
  hc_zero_left : ∀ {b : ℕ} (τ : L.Irr 0) (τ' : L.Irr b),
    L.hc τ τ' = L.ofIrr (castIrr L (Nat.zero_add b).symm τ')
  hc_zero_right : ∀ {a : ℕ} (τ : L.Irr a) (τ' : L.Irr 0), L.hc τ τ' = L.ofIrr τ

end Comparison₂

section HC

open Formalism.IrreducibleCountingLemmas.TYPES

def HCBody {g : ℕ} (L : LzData g) : Prop :=
  ∀ (a b : ℕ) (τ : L.Irr a) (τ' : L.Irr b),
    (∀ σ, L.cons (L.hc τ τ') σ → L.lab σ = L.lab τ * L.lab τ') ∧
    (IsCoprime (L.lab τ) (L.lab τ') →
      (∃ σ, L.hc τ τ' = L.ofIrr σ) ∧
      ∀ (τ₁ : L.Irr a) (τ₁' : L.Irr b), L.lab τ₁ = L.lab τ →
        L.lab τ₁' = L.lab τ' → L.hc τ₁ τ₁' = L.hc τ τ' → τ₁ = τ ∧ τ₁' = τ')

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}

end HC

section Row

open Formalism.IrreducibleCountingLemmas.TYPES

variable {D : D7}

def AdmHarishChandraTypes (P : Pend D) : Prop :=
  ∀ k : Fin 2,
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (C : LabelConv (ZMod (D.host.g k))) (O : LabelMap (ZMod (D.host.g k)) C),
      Nonempty (LzTie O (P.lz k)) → HCBody (P.lz k)

end Row

section Refute

open Formalism.IrreducibleCountingLemmas.TYPES

end Refute

section DZ

variable {D : D7}

def Occurs (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k)
    (z : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) : Prop :=
  ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F ≠ 0

def DZConcl (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i)
    (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
    D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) ∧
    D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t ∧
    ∀ w', IsConjPl D.host (D.naut.plGw k v) w' →
      D.naut.mono0 (D.naut.locV i PI w') ∧
      (D.naut.items₂ k w' (D.naut.locV i PI w')).natDegree = D.R.nV ∧
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
        (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)

def AdmDepthZeroTypes : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]),
      Simple ρ → Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ →
      Occurs i PI k v (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) → Squarefree f →
      (∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
        ¬ f.IsRoot (u : ZMod (D.host.g k))) →
      DZConcl i k v PI f

def KtyTie (P : Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (τ : (P.lz k).Irr D.R.r),
    τ ∈ P.kty i PI k v → Occurs i PI k v ((P.lz k).idem τ)

theorem ktyTie_of_spec (P : Pend D) : KtyTie P := by
  intro i PI k v τ hτ
  exact (P.kty_spec i PI k v τ).1 hτ

theorem idem_mul_eSer (P : Pend D) (k : Fin 2) (τ : (P.lz k).Irr D.R.r) :
    (P.lz k).idem τ * D.ntypes.eSer k ((P.lz k).lab τ) = (P.lz k).idem τ := by
  rw [P.eSer_eq, Finset.mul_sum, Finset.sum_eq_single τ]
  · rw [if_pos rfl, (P.lz k).idem_idem τ]
  · intro σ _ hne
    split_ifs
    · exact (P.lz k).idem_orth τ σ (fun h => hne h.symm)
    · exact mul_zero _
  · intro h
    exact absurd (Finset.mem_univ τ) h

end DZ

section TY

open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end TY

end Formalism.MainNotions.PairedCharacterCondition.RT

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions
section
noncomputable section

namespace Formalism.MainNotions.ElementDenominator.CongruenceModules

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator

theorem leg (l n : ℕ) (hp : l.Prime) (hl : l ≠ 2) :
    ((n + padicValNat l n.factorial : ℕ) : ℝ) ≤ 3 / 2 * n := by
  have : Fact l.Prime := ⟨hp⟩
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  have h1 := Nat.Prime.sub_one_mul_multiplicity_factorial (n := n) hp
  rw [← Nat.padicValNat_def] at h1
  have h2 : 2 * padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : 2 * padicValNat l n.factorial ≤ n := by omega
  have h5 : (2 : ℝ) * (padicValNat l n.factorial : ℝ) ≤ n := by exact_mod_cast h4
  push_cast
  linarith

theorem logA (l h h' S : ℕ) (h3 : 3 ≤ l) (h1 : 1 ≤ h') (h2 : h' ≤ h + S + 1) :
    Real.logb l h' ≤ Real.logb l h + S + 1 := by
  have hL : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hpow : S + 1 < l ^ (S + 1) := Nat.lt_pow_self (by omega)
  have hp : Real.logb l ((l : ℝ) ^ (S + 1)) = S + 1 := by
    rw [Real.logb_pow, Real.logb_self_eq_one hL]; push_cast; ring
  have hh' : (0 : ℝ) < h' := by exact_mod_cast h1
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · have : (h' : ℝ) ≤ (l : ℝ) ^ (S + 1) := by exact_mod_cast (by omega : h' ≤ l ^ (S + 1))
    have := Real.logb_le_logb_of_le hL hh' this
    simp only [Nat.cast_zero, Real.logb_zero]
    linarith
  · have e1 : h' ≤ h * l ^ (S + 1) := by nlinarith
    have : (h' : ℝ) ≤ (h : ℝ) * (l : ℝ) ^ (S + 1) := by exact_mod_cast e1
    have h4 := Real.logb_le_logb_of_le hL hh' this
    have h0' : (h : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    rw [Real.logb_mul h0' (by positivity), hp] at h4
    linarith

set_option maxHeartbeats 800000 in
theorem Ynum : ∀ (l e s h h' S η : ℕ), l.Prime → l ≠ 2 → e * s = l - 1 → 1 ≤ h' → h' ≤ h + S + 1 → (((2 * (2 * ⌈(2 * e * h' : ℝ) / ((l : ℝ) - 1)⌉₊ - 1 + padicValNat l (2 * ⌈(2 * e * h' : ℝ) / ((l : ℝ) - 1)⌉₊ - 1).factorial) + 4 * (⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1 + padicValNat l (⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1).factorial) + e * (S + padicValNat l S.factorial + Nat.log l h') + max (2 * (⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1 + padicValNat l (⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1).factorial)) ⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊ : ℕ) : ℝ)) ≤ 80 * ((e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) := by
  intro l e s h h' S η hp hl hes hh1 hh2
  have hl3 : 3 ≤ l := by have := hp.two_le; omega
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · omega
    · exact h0
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | h0
    · omega
    · exact h0
  have hel : e ≤ l := by nlinarith [Nat.sub_le l 1]
  have hL : (3 : ℝ) ≤ l := by exact_mod_cast hl3
  have hE : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hEl : (e : ℝ) ≤ l := by exact_mod_cast hel
  have hS : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hH : (1 : ℝ) ≤ h' := by exact_mod_cast hh1
  have hH2 : (h' : ℝ) ≤ h + S + 1 := by exact_mod_cast hh2
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hES : (e : ℝ) * s = l - 1 := by
    have : ((e * s : ℕ) : ℝ) = ((l - 1 : ℕ) : ℝ) := by rw [hes]
    push_cast [Nat.cast_sub (show 1 ≤ l by omega)] at this
    exact this
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = h' / s := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hxs : x * s = h' := by rw [hx]; field_simp
  have hxp : x * (l - 1) = e * h' := by rw [← hES, ← hxs]; ring
  have h1 : (2 * e * h' : ℝ) / (l - 1) = 2 * x := by
    rw [div_eq_iff (by linarith)]; linarith
  have h2 : (4 * h' : ℝ) / s = 4 * x := by rw [hx]; ring
  rw [h1, h2]
  have ha1 : 1 ≤ ⌈2 * x⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hb1 : 1 ≤ ⌈4 * x⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have ha2 : (⌈2 * x⌉₊ : ℝ) < 2 * x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hb2 : (⌈4 * x⌉₊ : ℝ) < 4 * x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hρ := leg l (2 * ⌈2 * x⌉₊ - 1) hp hl
  have hσ := leg l (⌈4 * x⌉₊ - 1) hp hl
  have hκ := leg l S hp hl
  have ca : ((2 * ⌈2 * x⌉₊ - 1 : ℕ) : ℝ) = 2 * (⌈2 * x⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have cb : ((⌈4 * x⌉₊ - 1 : ℕ) : ℝ) = (⌈4 * x⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hb1]; push_cast; ring
  rw [ca] at hρ
  rw [cb] at hσ
  have hA := logA l h h' S hl3 hh1 hh2
  have hL1 : (1 : ℝ) < l := by linarith
  have hLh : 0 ≤ Real.logb l h := by
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · simp
    · exact Real.logb_nonneg hL1 (by exact_mod_cast h0)
  have hLh' : 0 ≤ Real.logb l h' := Real.logb_nonneg hL1 hH
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (h : ℝ) / l := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hul : u * l = h := by rw [hu]; field_simp
  have hN : ((Nat.log l h' : ℕ) : ℝ) ≤ Real.logb l h + 3 / 2 * S + 3 / 2 * u := by
    by_cases hlt : h' < l
    · rw [Nat.log_of_lt hlt]; push_cast; positivity
    · have h5 : (l : ℝ) ≤ h' := by exact_mod_cast (not_lt.1 hlt)
      have h6 := Real.natLog_le_logb h' l
      have h7 : 1 ≤ 3 / 2 * u + S / 2 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonneg hS0 (sub_nonneg.2 hL)]
      linarith
  have hy : (⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊ : ℝ) < (η : ℝ) + 1 / 2 + Real.logb l h' + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hx1 : x ≤ 3 / 2 * (e * u + e * S / 3 + 1) := by
    have e1 : (e : ℝ) * h' ≤ (e * u + e * S / 3 + 1) * l := by
      have : (e : ℝ) * h' ≤ e * (h + S + 1) := mul_le_mul_of_nonneg_left hH2 (by linarith)
      have e2 : (e : ℝ) * S * 3 ≤ e * S * l := mul_le_mul_of_nonneg_left hL (by positivity)
      have e3 : (e : ℝ) * u * l = e * h := by rw [mul_assoc, hul]
      linarith
    have e4 : x * (2 / 3 * l) ≤ x * (l - 1) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have hl0 : (0 : ℝ) < l := by linarith
    have e5 : x * l ≤ 3 / 2 * (e * u + e * S / 3 + 1) * l := by linarith
    exact le_of_mul_le_mul_right e5 hl0
  have eu : (e : ℝ) * h / l = e * u := by rw [hu]; ring
  rw [eu]
  generalize 2 * ⌈2 * x⌉₊ - 1 + padicValNat l (2 * ⌈2 * x⌉₊ - 1).factorial = ρ at hρ ⊢
  generalize ⌈4 * x⌉₊ - 1 + padicValNat l (⌈4 * x⌉₊ - 1).factorial = σ at hσ ⊢
  generalize S + padicValNat l S.factorial = κ at hκ ⊢
  generalize ⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊ = y at hy ⊢
  generalize Nat.log l h' = N at hN ⊢
  have hm : max (2 * σ) y ≤ 2 * σ + y := by omega
  have hm' : ((max (2 * σ) y : ℕ) : ℝ) ≤ 2 * σ + y := by exact_mod_cast hm
  have k1 : (e : ℝ) * κ ≤ e * (3 / 2 * S) := mul_le_mul_of_nonneg_left hκ (by linarith)
  have k2 : (e : ℝ) * N ≤ e * (Real.logb l h + 3 / 2 * S + 3 / 2 * u) :=
    mul_le_mul_of_nonneg_left hN (by linarith)
  have k3 : (S : ℝ) ≤ e * S := le_mul_of_one_le_left hS0 hE
  have k4 : Real.logb l h ≤ e * Real.logb l h := le_mul_of_one_le_left hLh hE
  have k5 : 0 ≤ (e : ℝ) * u := by positivity
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
  simp only [Nat.cast_ofNat]
  linarith

def sigA (l s h' : ℕ) : ℕ :=
  ⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1 + padicValNat l (⌈(4 * h' : ℝ) / (s : ℝ)⌉₊ - 1).factorial

def rhoA (l e h' : ℕ) : ℕ :=
  2 * ⌈(2 * e * h' : ℝ) / ((l : ℝ) - 1)⌉₊ - 1 +
    padicValNat l (2 * ⌈(2 * e * h' : ℝ) / ((l : ℝ) - 1)⌉₊ - 1).factorial

def kapA (l e h' S : ℕ) : ℕ := e * (S + padicValNat l S.factorial + Nat.log l h')

def ycA (l h' η : ℕ) : ℕ := ⌈(η : ℝ) + 1 / 2 + Real.logb l h'⌉₊

def YA (l e s h' S η : ℕ) : ℕ :=
  2 * rhoA l e h' + 4 * sigA l s h' + kapA l e h' S + max (2 * sigA l s h') (ycA l h' η)

def expLift (l h : ℕ) (J : Finset ℤ) : ℕ :=
  2 * (2 * (2 * h) + padicValNat l (2 * (2 * h)).factorial) +
    ((∑ j ∈ J, (1 + padicValInt l j)) + h + padicValNat l h.factorial)

def claimA {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    ∃ (s h' g : ℕ) (J : Finset ℤ), finrank ↥(K0 K) ↥K.1 * s = l - 1 ∧ 1 ≤ h' ∧ h' ≤ h + S + 1 ∧
      J ⊆ Finset.Icc (-(h : ℤ)) (2 * h) ∧ (0 : ℤ) ∉ J ∧
      g ≤ 2 * ((finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 + 1) * r) ∧
      TwoStep l g (finrank ℚ_[l] ↥(K0 K) * finrank ↥(K0 K) ↥K.1 * (finrank ↥(K0 K) ↥K.1 + 1) * m)
        (YA l (finrank ↥(K0 K) ↥K.1) s h' S η) (expLift l h J)
        (latticeFiniteCocycles (P.PD K) T₂.L) (latticeCoboundaries T₂.L) (F.ImF (P.PD K))

def LocalTheoremAtGoodExtensions (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → claimA (D.loc l) K LL

theorem thmA_of_claim {l : ℕ} [hp : Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (hl : l ≠ 2) (C : ℝ)
    (hC : 160 ≤ C) (H : claimA P K LL) : thmA P K LL C := by
  intro T₁ T₂ F r S η m h up b h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨s, h', g, J, hes, hh1, hh2, hJ, h0, hg, hT⟩ :=
    H T₁ T₂ F r S η m h up b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  refine colLe_mono P K LL F ?_ (colLe_of_twoStep P K LL F _ _ _ _ hT)
  generalize finrank ℚ_[l] ↥(K0 K) = n at hg ⊢
  generalize finrank ↥(K0 K) ↥K.1 = e at hg hes ⊢
  have hY : ((YA l e s h' S η : ℕ) : ℝ) ≤
      80 * ((e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η) :=
    Ynum l e s h h' S η hp.out hl hes hh1 hh2
  have hE : expLift l h J ≤ 18 * h := Formalism.IrreducibleCountingLemmas.WindowSums.valuationSumBound l h J hp.out hl hJ h0
  have hE' : ((expLift l h J : ℕ) : ℝ) ≤ C * ((h : ℝ) + 1) := by
    have : ((expLift l h J : ℕ) : ℝ) ≤ 18 * (h : ℝ) := by exact_mod_cast hE
    have h0' : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    nlinarith
  have hg' : (g : ℝ) ≤ 2 * (((n : ℝ) * e + 1) * r) := by exact_mod_cast hg
  have hY0 : (0 : ℝ) ≤ ((YA l e s h' S η : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold boundA
  set B : ℝ := (e : ℝ) * h / l + (e : ℝ) * S + (e : ℝ) * Real.logb l h + 1 + η with hB
  have hB0 : 0 ≤ B := by linarith
  have hA0 : (0 : ℝ) ≤ ((n : ℝ) * e + 1) * r := by positivity
  have e1 : (g : ℝ) * ((YA l e s h' S η : ℕ) : ℝ) ≤ 2 * (((n : ℝ) * e + 1) * r) * (80 * B) :=
    mul_le_mul hg' hY hY0 (by positivity)
  have e2 : 160 * ((((n : ℝ) * e + 1) * r) * B) ≤ C * ((((n : ℝ) * e + 1) * r) * B) :=
    mul_le_mul_of_nonneg_right hC (mul_nonneg hA0 hB0)
  have e3 : ((n * e * (e + 1) * m : ℕ) : ℝ) * ((expLift l h J : ℕ) : ℝ) ≤
      ((n * e * (e + 1) * m : ℕ) : ℝ) * (C * ((h : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hE' (Nat.cast_nonneg _)
  push_cast at e3 ⊢
  nlinarith

theorem local_theorem_of_good_extensions (D : D7) (C : ℝ) (hC : 160 ≤ C) (H : LocalTheoremAtGoodExtensions D) : Conclusion1 D C :=
  fun l _ hl K LL hg => thmA_of_claim (D.loc l) K LL hl C hC (H l hl K LL hg)

end Formalism.MainNotions.ElementDenominator.CongruenceModules

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.PrimesEffectiveChebotarev
section
noncomputable section

namespace Formalism.MainNotions.N.CuspidalLatticeIdempotents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped ComplexOrder

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem algBB_sub (g N : ℕ) (hg : 2 ≤ g) :
    Formalism.CyclotomicNorms.BB N g ⊆ ((Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BB g N : Finset ℕ) : Set ℕ) := by
  intro l hl
  rw [Finset.mem_coe, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_BB_iff]
  rcases hl with h | ⟨d, hd1, hdN, hlp, hlt⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, hlp, d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, hlt⟩
    have hone : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, pow_zero] at hlt
      omega
    have hdvd : l ∣ g ^ d - 1 := by
      by_contra hnd
      exact hv (by rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd hnd)
    have h1 := Nat.le_of_dvd (by omega) hdvd
    have h2 : g ^ d ≤ g ^ N := Nat.pow_le_pow_right (by omega) hdN
    omega

end Formalism.MainNotions.N.CuspidalLatticeIdempotents
end
end

