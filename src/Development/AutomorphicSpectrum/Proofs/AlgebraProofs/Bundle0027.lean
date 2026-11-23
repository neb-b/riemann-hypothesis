module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0021
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbAflat

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num.StepOnto

def stepSub (F : Type) [Field F] (n i : ℕ) : AddSubgroup (Fin n → F) where
  carrier := {x | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  zero_mem' := by
    intro j _
    rfl
  neg_mem' := by
    intro a ha j hj
    simp [ha j hj]

theorem exists_inv_add_sq {C R : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R]
    [Algebra R C] (v : Valuation C NNReal) (hv : v.Integers R) {N : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) (g : N → C)
    (hg : g ∈ AA.carrier) (h0 : g 0 = 0) (hK : ∀ k ∈ K, g k = 0) :
    ∃ h ∈ AA.carrier, ∃ q ∈ sqIdeal (augIdeal AA.carrier),
      h 0 = 0 ∧ (∀ x, ∀ k ∈ K, h (x + k) = h x) ∧ g = h + q := by
  classical
  obtain ⟨-, -, -, H4⟩ := ReciprocityTheory.PGsh.L2.h3 C R ‹IsAlgClosed C› ‹CharZero C› v hv N K AA
  have hg' : g ∈ augIdeal AA.carrier := by
    refine Submodule.mem_inf.2 ⟨hg, ?_⟩
    rw [LinearMap.mem_ker]
    exact h0
  have hres : ReciprocityTheory.PGsh.L2.resK (R := R) K g = 0 := by
    funext k
    show g k = 0
    exact hK k k.2
  have h2 := H4 g hg' (by rw [hres]; exact zero_mem _)
  obtain ⟨h, hh, q, hq, hgq⟩ := Submodule.mem_sup.1 h2
  obtain ⟨b, hb, rfl⟩ := hh
  obtain ⟨hbA, hb0⟩ := Submodule.mem_inf.1 hb
  refine ⟨_, hbA, q, ?_, ?_, ?_, hgq.symm⟩
  · have hsq : augIdeal AA.carrier * augIdeal AA.carrier ≤ sqIdeal (augIdeal AA.carrier) := by
      rw [Submodule.mul_le]
      intro x hx y hy
      show x * y ∈ Submodule.span R {h | ∃ f ∈ augIdeal AA.carrier, ∃ f' ∈ augIdeal AA.carrier, h = f * f'}
      exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    exact hsq hq
  · show b (QuotientAddGroup.mk 0) = 0
    rw [QuotientAddGroup.mk_zero]
    exact LinearMap.mem_ker.1 hb0
  · intro x k hk
    show b (QuotientAddGroup.mk (x + k)) = b (QuotientAddGroup.mk x)
    have hk0 : (QuotientAddGroup.mk k : N ⧸ K) = 0 := (QuotientAddGroup.eq_zero_iff k).2 hk
    rw [QuotientAddGroup.mk_add, hk0, add_zero]

theorem avg_mem {C V X F : Type} [Field C] [AddCommGroup V] [Module C V] [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup X] [Module F X]
    (T : AddSubgroup ((X → C) × V)) (S : Set C) (hs : ∀ a ∈ S, ∀ t ∈ T, a • t ∈ T)
    (χ : F → C) (hS : ∀ a, χ a ∈ S) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1)
    (u : C) (hu : u ∈ S) (hu' : u * (Fintype.card Fˣ : C) = 1)
    (heq : ∀ (a : F) g m, (g, m) ∈ T → ((fun x => g (a • x)), χ a • m) ∈ T)
    (h : X → C) (m : V) (hm : (h, m) ∈ T) :
    ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) ∈ T := by
  have hmem : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)) ∈ T :=
    fun a => hs u hu _ (hs _ (hS _) _ (heq _ h m hm))
  suffices e : ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) =
      ∑ a : Fˣ, u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m) by
    rw [e]
    exact T.sum_mem (fun a _ => hmem a)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    funext x
    dsimp only
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · rw [Prod.snd_sum]
    have hterm : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)).2 = u • m := by
      intro a
      simp only [Prod.smul_snd, smul_smul]
      rw [mul_assoc, ← hmul, Units.inv_mul, h1, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul C, smul_smul, mul_comm, hu', one_smul]

theorem avg_smul {C X F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F] [AddCommGroup X]
    [Module F X] (χ : F → C) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1) (u : C)
    (h : X → C) (b : Fˣ) (x : X) :
    u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)) := by
  have key : ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      ∑ c : Fˣ, χ (b : F) * (χ ((c⁻¹ : Fˣ) : F) * h ((c : F) • x)) := by
    refine Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun a => ?_)
    show χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (χ (((a * b)⁻¹ : Fˣ) : F) * h (((a * b : Fˣ) : F) • x))
    rw [smul_smul, ← mul_assoc, ← hmul, Units.val_mul, mul_inv_rev, Units.val_mul, ← mul_assoc,
      Units.mul_inv, one_mul]
  rw [key, ← Finset.mul_sum]
  ring

theorem mem_vanSub {C F : Type} [Field C] [Field F] {n i : ℕ} (g : (Fin n → F) → C) :
    g ∈ (vanSub C F n i).toAddSubgroup ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → g x = 0 := by
  rw [Submodule.mem_toAddSubgroup]
  show g ∈ Submodule.pi {x : Fin n → F | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} (fun _ => (⊥ : Submodule C C)) ↔ _
  simp only [Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]

theorem eq_on_step {C F : Type} [Field C] [Field F] {n : ℕ} (i : Fin n) (H : (Fin n → F) → C)
    (χ : F → C) (hχ0 : χ 0 = 0)
    (hinv : ∀ y, ∀ k ∈ stepSub F n i, H (y + k) = H y)
    (hsm : ∀ (b : Fˣ) y, H ((b : F) • y) = χ (b : F) * H y) (h0 : H 0 = 0)
    (x : Fin n → F) (hx : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) :
    H x = H (Pi.single i 1) * χ (x i) := by
  have hk : x - x i • Pi.single i 1 ∈ stepSub F n i := by
    show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → (x - x i • (Pi.single i 1 : Fin n → F) : Fin n → F) j = 0
    intro j hj
    rcases eq_or_lt_of_le hj with hij | hij
    · have hji : j = i := Fin.ext hij.symm
      subst hji
      simp
    · have hne : j ≠ i := fun e => by subst e; exact lt_irrefl _ hij
      simp [hx j hij, Pi.single_apply, hne]
  have e : H x = H (x i • Pi.single i 1) := by
    have := hinv (x i • Pi.single i 1) _ hk
    rwa [add_sub_cancel] at this
  rw [e]
  by_cases hxi : x i = 0
  · rw [hxi, zero_smul, h0, hχ0, mul_zero]
  · have := hsm (Units.mk0 (x i) hxi) (Pi.single i 1)
    rw [Units.val_mk0] at this
    rw [this, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Num.StepOnto

namespace GlobalTheory.CompanionTheory.Ar.Num

open StepOnto

theorem stepGraph_snd_eq_kk : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  intro o C _ _ _ _ _ RC v hRC p _ hp F _ _ _ _ n Sg r s D w χ φ hB AA hAA hFS σ hσ hfl e hχ hφ hTh τ i
  obtain ⟨hsq, heq, -⟩ := hTh τ
  have hth := (hB.th τ).1
  have hstab : ∀ a ∈ RC, ∀ t ∈ D.Th τ, a • t ∈ D.Th τ := fun a ha t ht => ((hB.stable τ) a ha).2.2 t ht
  have hχ0 : χ τ 0 = 0 := by
    rw [hχ, MulChar.map_zero]
    rfl
  ext m
  constructor
  · rintro ⟨⟨a, m'⟩, hmem, rfl⟩
    have hmem' : ((a • fun y : Fin n → F => χ τ (y i)), m') ∈
        D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥ := hmem
    obtain ⟨⟨g, m1⟩, hgm, ⟨f, m2⟩, hf, hsum⟩ := AddSubgroup.mem_sup.1 hmem'
    obtain ⟨hfv, hm2⟩ := AddSubgroup.mem_prod.1 hf
    have hm2' : m2 = 0 := AddSubgroup.mem_bot.1 hm2
    have e0 : g + f = a • (fun y : Fin n → F => χ τ (y i)) := congrArg Prod.fst hsum
    have e1 : m1 + m2 = m' := congrArg Prod.snd hsum
    rw [hm2', add_zero] at e1
    subst e1
    have e2 : g = a • (fun y : Fin n → F => χ τ (y i)) - f := eq_sub_of_add_eq e0
    show m1 ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤)
    refine AddSubgroup.mem_map.2 ⟨(g, m1), AddSubgroup.mem_inf.2 ⟨hgm, AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_top _⟩⟩, rfl⟩
    refine (mem_vanSub g).2 (fun x hx => ?_)
    have hxi : x i = 0 := hx i le_rfl
    have hfx : f x = 0 := (mem_vanSub f).1 hfv x (fun j hj => hx j (by omega))
    rw [e2]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxi, hχ0, mul_zero, hfx, sub_zero]
  · intro hm
    have hm' : m ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤) := hm
    obtain ⟨⟨g, m'⟩, hgm, rfl⟩ := AddSubgroup.mem_map.1 hm'
    obtain ⟨hgTh, hgp⟩ := AddSubgroup.mem_inf.1 hgm
    have hgv : g ∈ (vanSub C F n ↑i).toAddSubgroup := (AddSubgroup.mem_prod.1 hgp).1
    obtain ⟨hgM, hg0⟩ := (hth g).1 ⟨m', hgTh⟩
    have hgA : g ∈ AA.carrier := by
      rw [← hAA] at hgM
      exact (Submodule.mem_toAddSubgroup _).1 hgM
    have hgK : ∀ k ∈ stepSub F n ↑i, g k = 0 := fun k hk => (mem_vanSub g).1 hgv k hk
    have hv : v.Integers RC :=
      ⟨fun a b hab => Subtype.ext hab, fun x => (hRC x).1 x.2, fun r hr => ⟨⟨r, (hRC r).2 hr⟩, rfl⟩⟩
    obtain ⟨h, hhA, q, hq, hh0, hhinv, hgq⟩ := exists_inv_add_sq v hv AA (stepSub F n ↑i) g hgA hg0 hgK
    have hhTh : (h, m') ∈ D.Th τ := by
      have e3 : (h, m') = (g, m') - (q, 0) := by
        rw [hgq]
        simp
      rw [e3]
      exact sub_mem hgTh (hsq q hq)
    have hcard : ((Fintype.card Fˣ : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hu' : ((Fintype.card Fˣ : ℕ) : C)⁻¹ * (Fintype.card Fˣ : C) = 1 := inv_mul_cancel₀ hcard
    have hvF : v ((Fintype.card F : ℕ) : C) < 1 := by
      obtain ⟨k, -, hk⟩ := FiniteField.card F p
      rw [hk, Nat.cast_pow, map_pow]
      exact pow_lt_one₀ zero_le' hp (PNat.ne_zero k)
    have hvU : v ((Fintype.card Fˣ : ℕ) : C) = 1 := by
      have e3 : ((Fintype.card Fˣ : ℕ) : C) = -(1 - ((Fintype.card F : ℕ) : C)) := by
        rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
        ring
      rw [e3, Valuation.map_neg, Valuation.map_one_sub_of_lt v hvF]
    have hu : ((Fintype.card Fˣ : ℕ) : C)⁻¹ ∈ RC := (hRC _).2 (by rw [map_inv₀, hvU, inv_one])
    have hS : ∀ a, χ τ a ∈ (RC : Set C) := fun a => by
      rw [hχ]
      exact Subtype.prop _
    have hmul : ∀ a b, χ τ (a * b) = χ τ a * χ τ b := fun a b => by
      rw [hχ, hχ, hχ, map_mul]
      rfl
    have h1 : χ τ 1 = 1 := by
      rw [hχ, map_one]
      rfl
    have hav := avg_mem (D.Th τ) (RC : Set C) hstab (χ τ) hS hmul h1 _ hu hu' heq h m' hhTh
    let H' : (Fin n → F) → C := fun x =>
      ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)
    have hinv' : ∀ y, ∀ k ∈ stepSub F n ↑i, H' (y + k) = H' y := by
      intro y k hk
      have hk' : ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → k j = 0 := hk
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (y + k)) =
        ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • y)
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hak : (a : F) • k ∈ stepSub F n ↑i := by
        show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → ((a : F) • k) j = 0
        intro j hj
        rw [Pi.smul_apply, hk' j hj, smul_zero]
      rw [smul_add, hhinv _ _ hak]
    have hsm' : ∀ (b : Fˣ) y, H' ((b : F) • y) = χ τ (b : F) * H' y := fun b y =>
      avg_smul (χ τ) hmul h1 _ h b y
    have h0' : H' 0 = 0 := by
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (0 : Fin n → F)) = 0
      simp [hh0]
    have hstep := eq_on_step i H' (χ τ) hχ0 hinv' hsm' h0'
    show m' ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.stepGraph τ (χ τ) i)
    refine AddSubgroup.mem_map.2 ⟨(H' (Pi.single i 1), m'), ?_, rfl⟩
    show ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)), m') ∈
      D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥
    refine AddSubgroup.mem_sup.2 ⟨(H', m'), hav, ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H', 0),
      AddSubgroup.mem_prod.2 ⟨?_, zero_mem _⟩, ?_⟩
    · refine (mem_vanSub _).2 (fun x hx => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hstep x hx, sub_self]
    · refine Prod.ext ?_ ?_
      · show H' + ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H') =
          H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)
        abel
      · show m' + 0 = m'
        rw [add_zero]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InjectiveModPLatticeCharacterBound
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelSeq

section Lattices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat (R : Subalgebra o Ω) {κ : Type} (v : κ → Ω) :
    v ∈ stdLat R κ ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

theorem af_le_std (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af R p χ ≤ stdLat R (Fin n) := by
  have hl1 : D.l1 R p ≤ stdLat R _ := by
    refine sup_le hB.M_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (mem_stdLat R _).2 fun i => ?_
    have := (mem_stdLat R f).1 hf i
    simpa using R.mul_mem (natCast_mem R p) this
  intro l hl
  refine (mem_stdLat R l).2 fun i => ?_
  have h := (mem_stdLat R _).1 (hl1 hl) (Pi.single i 1)
  have e : (linMap n χ) l (Pi.single i 1) = l i := by
    simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  have e' : (linMap n χ).toAddMonoidHom l (Pi.single i 1) = l i := e
  rwa [e'] at h

theorem std_le_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (hB : D.Base R p w)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : stdLat R (Fin n) ≤ D.hh R p χ := by
  intro v hv
  refine (mem_dotDual R _ v).2 fun l hl => ?_
  have hl' := (mem_stdLat R l).1 (af_le_std D R p w hB χ h0 h1 hl)
  have hv' := (mem_stdLat R v).1 hv
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std_of_mem_hh (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (h : mulLat w (stdLat R _) ≤ D.af R p χ) {b : Fin n → Ω} (hb : b ∈ D.hh R p χ) :
    w • b ∈ stdLat R (Fin n) := by
  refine (mem_stdLat R _).2 fun i => ?_
  have hi : (Pi.single i 1 : Fin n → Ω) ∈ stdLat R (Fin n) := by
    refine (mem_stdLat R _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp [one_mem]
    · simp [Pi.single_eq_of_ne hj, zero_mem]
  have hm : w • (Pi.single i 1 : Fin n → Ω) ∈ D.af R p χ := h ⟨_, hi, rfl⟩
  have := (mem_dotDual R _ b).1 hb _ hm
  simpa [smul_dotProduct, single_one_dotProduct] using this

theorem mem_kerH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (v : Fin (r τ) → Ω) :
    v ∈ D.kerH R p τ χ ↔ ∃ b, (v, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.kerH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_imH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (c : Fin (s τ) → Ω) :
    c ∈ D.imH R p τ χ ↔ ∃ b, (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [LieLatticeData.imH, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

def gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω)) :=
  D.Gam τ ⊓ (⊤ : AddSubgroup (Fin (r τ) → Ω)).prod (D.hh R p χ)

def delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω) :
    AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω)) :=
  D.Del τ ⊓ (D.hh R p χ).prod (⊤ : AddSubgroup (Fin (s τ) → Ω))

theorem mem_gamH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (a : Fin (r τ) → Ω) (b : Fin n → Ω) :
    (a, b) ∈ gamH D R p τ χ ↔ (a, b) ∈ D.Gam τ ∧ b ∈ D.hh R p χ := by
  simp [gamH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

theorem mem_delH (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (τ : Sg) (χ : F → Ω)
    (b : Fin n → Ω) (c : Fin (s τ) → Ω) :
    (b, c) ∈ delH D R p τ χ ↔ (b, c) ∈ D.Del τ ∧ b ∈ D.hh R p χ := by
  simp [delH, AddSubgroup.mem_inf, AddSubgroup.mem_prod]

end Lattices

section Families

variable (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem isLatFamily_inf_prod_right (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V₁} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (⊤ : AddSubgroup V).prod (H c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨trivial, hH.1 c hc a ha _ h2⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).2
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨trivial, ?_⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

theorem isLatFamily_inf_prod_left (x : (Σ k, ι k) → Ω) {G : (∀ k, ι k) → AddSubgroup (V × V₁)}
    {H : (∀ k, ι k) → AddSubgroup V} (hG : IsLatFamily o x G) (hH : IsLatFamily o x H) :
    IsLatFamily o x fun c => G c ⊓ (H c).prod (⊤ : AddSubgroup V₁) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    exact ⟨hG.1 c hc a ha v hv.1, AddSubgroup.mem_prod.2 ⟨hH.1 c hc a ha _ h2, trivial⟩⟩
  · have h2 := (AddSubgroup.mem_prod.1 hv.2).1
    obtain ⟨m₁, h₁⟩ := hG.2 c t hc ht v hv.1
    obtain ⟨m₂, h₂⟩ := hH.2 c t hc ht _ h2
    have hq := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    refine ⟨m₂ + m₁, ?_, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
    · have := hG.1 t ht _ (pow_mem hq m₂) _ h₁
      rwa [smul_smul, ← pow_add] at this
    · have := hH.1 t ht _ (pow_mem hq m₁) _ h₂
      rw [smul_smul, ← pow_add, add_comm] at this
      simpa using this

end Families

theorem relSeq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → ∀ τ, QuotExact O x (fun c => divLat (algebraMap O Ω w) ((D c).lie τ)) (fun c => (D c).W τ) (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) (fun c => stdLat (chartRing O (mseg x) c) (Fin n)) (fun c => (D c).om τ) (fun c => (D c).omHT τ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x hinj F _ _ _ n Sg _ r s p hp w χ φ D hD hG hF τ
  have hhfam := (((_root_.GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main O Ω K ι x hinj p hp w χ φ D hD).2 τ).2.2.2.2 hG).1
  obtain ⟨-, -, -, -, hGam, hDel, -⟩ := hD.fam τ
  have h0 : χ τ 0 = 0 := (hD.char.2.2.2.2 τ).1
  have h1 : χ τ 1 = 1 := (hD.char.2.2.2.2 τ).2
  have h0' : algebraMap O Ω (χ τ 0) = 0 := by rw [h0, map_zero]
  have h1' : algebraMap O Ω (χ τ 1) = 1 := by rw [h1, map_one]
  have hstd : ∀ c, mseg x c ≠ 0 → stdLat (chartRing O (mseg x) c) (Fin n) ≤
      (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)) :=
    fun c hc => std_le_hh (D c) _ p _ (hD.base c hc) _ h0' h1'
  refine ⟨fun c => gamH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    fun c => delH (D c) (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)),
    ⟨isLatFamily_inf_prod_right O x hGam hhfam, fun c hc => ?_⟩,
    ⟨isLatFamily_inf_prod_left O x hDel hhfam, fun c hc => ?_⟩, fun c hc => ?_⟩
  · have hB := hD.base c hc
    have hk := (hF c hc).ker τ
    refine ⟨fun v b hvb => ?_, fun v hv => ?_, fun b => ?_, fun v hv => ?_⟩
    · have h := (mem_gamH _ _ _ _ _ _ _).1 hvb
      refine ⟨?_, h.2⟩
      beta_reduce
      rw [← hk]
      exact (mem_kerH _ _ _ _ _ _).2 ⟨b, h⟩
    · beta_reduce at hv
      rw [← hk] at hv
      obtain ⟨b, h⟩ := (mem_kerH _ _ _ _ _ _).1 hv
      exact ⟨b, (mem_gamH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_gamH]
      exact ⟨fun h => ((hB.gam τ).2.1 b).1 h.1, fun h => ⟨((hB.gam τ).2.1 b).2 h, hstd c hc h⟩⟩
    · exact (mem_gamH _ _ _ _ _ _ _).2 ⟨((hB.gam τ).2.2 v).2 hv, zero_mem _⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun b e hbe => ?_, fun b hb => ?_, fun e => ?_, fun b hb => ?_⟩
    · have h := (mem_delH _ _ _ _ _ _ _).1 hbe
      refine ⟨h.2, ?_⟩
      beta_reduce
      rw [← hi]
      exact (mem_imH _ _ _ _ _ _).2 ⟨b, h⟩
    · obtain ⟨e, he⟩ := ((hB.del τ).1 b).2
        (smul_mem_std_of_mem_hh (D c) _ p _ _ ((hF c hc).le_af τ) hb)
      exact ⟨e, (mem_delH _ _ _ _ _ _ _).2 ⟨he, hb⟩⟩
    · rw [mem_delH]
      exact ⟨fun h => ((hB.del τ).2.2.1 e).1 h.1, fun h => ⟨((hB.del τ).2.2.1 e).2 h, zero_mem _⟩⟩
    · refine (mem_delH _ _ _ _ _ _ _).2 ⟨((hB.del τ).2.2.2 b).2 ⟨0, ((hB.gam τ).2.1 b).2 hb⟩, hstd c hc hb⟩
  · have hB := hD.base c hc
    have hi := (hF c hc).im τ
    refine ⟨fun v hv => ?_, fun e he => ?_, fun b => ?_⟩
    · exact ((hB.gam τ).2.2 v).1 ((mem_gamH _ _ _ _ _ _ _).1 hv).1
    · beta_reduce at he
      rw [← hi] at he
      obtain ⟨b, h⟩ := (mem_imH _ _ _ _ _ _).1 he
      exact ⟨b, (mem_delH _ _ _ _ _ _ _).2 h⟩
    · rw [mem_delH]
      constructor
      · rintro ⟨h, hb⟩
        obtain ⟨a, ha⟩ := ((hB.del τ).2.2.2 b).1 h
        exact ⟨a, (mem_gamH _ _ _ _ _ _ _).2 ⟨ha, hb⟩⟩
      · rintro ⟨a, ha⟩
        have h := (mem_gamH _ _ _ _ _ _ _).1 ha
        exact ⟨((hB.del τ).2.2.2 b).2 ⟨a, h.1⟩, h.2⟩

end GlobalTheory.CompanionTheory.Ar.Num.RelSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactSubDegreeBound
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes

theorem subDeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) :=
  @PositivityTheory.HtPt.Ch.subdeg_ses

end GlobalTheory.CompanionTheory.Ar.Crv.SubDegSes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengths
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @PositivityTheory.HtPt.Rb.flag_D | exact PositivityTheory.HtPt.Rb.flag_D
end

