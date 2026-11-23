module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundMultiplierSqrtNegD
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzMult

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  intro l _ lam d σ p hd hd4 hld hA hB h3
  have hlp : l.Prime := Fact.out
  obtain ⟨hint, -, hmul, hmono, -, hl, -⟩ := _root_.GlobalTheory.SzRules.main l lam
  obtain ⟨-, hadd2, -, -, hZ, -⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hne : ∀ n : ℕ, ¬ l ∣ n → (n : ℂ) ≠ 0 := by
    intro n hn h
    apply hn
    rw [Nat.cast_eq_zero.mp h]
    exact dvd_zero l
  have hinv : ∀ n : ℕ, ¬ l ∣ n → Sz l lam 0 ((n : ℂ)⁻¹) := by
    intro n hn
    apply hint n _ hn
    rw [mul_inv_cancel₀ (hne n hn)]
    exact isIntegral_one
  have hnat : ∀ n : ℕ, Sz l lam 0 (n : ℂ) := fun n => by exact_mod_cast hZ n
  have hm0 : ∀ (r : ℝ) (x y : ℂ), Sz l lam 0 x → Sz l lam r y → Sz l lam r (x * y) := by
    intro r x y hx hy
    simpa using hmul 0 r x y hx hy
  have hcancel : ∀ (r : ℝ) (n : ℕ) (x : ℂ), ¬ l ∣ n → Sz l lam r ((n : ℂ) * x) → Sz l lam r x := by
    intro r n x hn h
    have := hm0 r _ _ (hinv n hn) h
    rwa [← mul_assoc, inv_mul_cancel₀ (hne n hn), one_mul] at this
  have hkey : ∀ r : ℝ, 0 ≤ r → Sz l lam r (((d : ℂ) + 1) * p) → Sz l lam r (((2 * d : ℕ) : ℂ) * σ) := by
    intro r hr h
    have hB' := hmono 0 r _ hr hB
    have := (hadd2 r _ _ h hB').2
    convert this using 1
    push_cast
    ring
  have hmulk : ∀ (r : ℝ) (m k : ℕ), d + 1 = m * k → Sz l lam r ((m : ℂ) * p) → Sz l lam r (((d : ℂ) + 1) * p) := by
    intro r m k hk h
    have := hm0 r (k : ℂ) _ (hnat k) h
    have e : ((d : ℂ) + 1) = (m : ℂ) * k := by exact_mod_cast hk
    rw [e]
    convert this using 1
    ring
  by_cases h2 : l = 2
  · subst h2
    have hd2 : ¬ 2 ∣ d := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h
      omega
    have h4p : Sz 2 lam 0 (((4 : ℕ) : ℂ) * p) := by
      apply hcancel 0 3 _ (by norm_num)
      convert hA using 1
      push_cast
      ring
    rw [if_pos rfl]
    split_ifs with h43
    · obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 4 k hk h4p)
      have h2s : Sz 2 lam 0 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 0 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 0 σ).mp h2s
      norm_num at this
      exact this
    · have h2p : Sz 2 lam 1 (((2 : ℕ) : ℂ) * p) := by
        have := (hl 0 (((2 : ℕ) : ℂ) * p)).mp (by convert h4p using 1; push_cast; ring)
        norm_num at this ⊢
        exact this
      obtain ⟨k, hk⟩ : 2 ∣ d + 1 := by omega
      have h1 := hkey 1 zero_le_one (hmulk 1 2 k hk h2p)
      have h2s : Sz 2 lam 1 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 1 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 1 σ).mp h2s
      norm_num at this
      exact this
  · rw [if_neg h2]
    by_cases h3' : l = 3
    · subst h3'
      have hd3 := h3 rfl
      have h3p : Sz 3 lam 0 (((3 : ℕ) : ℂ) * p) := by
        apply hcancel 0 4 _ (by norm_num)
        convert hA using 1
        push_cast
        ring
      obtain ⟨k, hk⟩ : 3 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 3 k hk h3p)
      exact hcancel 0 (2 * d) σ (by omega) h1
    · have hl2 : ∀ n : ℕ, n.Prime → l ∣ n → l = n := fun n hn h =>
        (Nat.prime_dvd_prime_iff_eq hlp hn).mp h
      have h12 : ¬ l ∣ 12 := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp (show l ∣ 2 * 2 * 3 from h) with h' | h'
        · rcases (Nat.Prime.dvd_mul hlp).mp h' with h'' | h'' <;>
            exact h2 (hl2 2 Nat.prime_two h'')
        · exact h3' (hl2 3 Nat.prime_three h')
      have h2d : ¬ l ∣ 2 * d := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp h with h' | h'
        · exact h2 (hl2 2 Nat.prime_two h')
        · exact hld (hl2 d hd h')
      have hp : Sz l lam 0 p := by
        apply hcancel 0 12 p h12
        exact_mod_cast hA
      have h1 := hkey 0 le_rfl (hmulk 0 1 (d + 1) (by ring) (by simpa using hp))
      exact hcancel 0 (2 * d) σ h2d h1

end GlobalTheory.SzMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationBoundThreeInert
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.ArithThreeInert

theorem main : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  intro _ lam d w σ p hd hw h1 h2
  obtain ⟨hint, hadd, hmul, -, hneg, -, -⟩ := _root_.GlobalTheory.SzRules.main 3 lam
  have hsub : ∀ x y : ℂ, Sz 3 lam 0 x → Sz 3 lam 0 y → Sz 3 lam 0 (x - y) := by
    intro x y hx hy
    rw [sub_eq_add_neg]; exact hadd 0 x (-y) hx (hneg 0 y hy)
  have hI : ∀ x : ℂ, IsIntegral ℤ x → Sz 3 lam 0 x := by
    intro x hx
    exact hint 1 x (by norm_num) (by simpa using hx)
  have hw_int : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.Monic.def.mpr (by
        rw [Polynomial.leadingCoeff_X_pow_add_C (by norm_num)])
    · simp [hw]
  have hA : Sz 3 lam 0 ((1 + w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.add hw_int).pow 2).sub isIntegral_one)
  have hB : Sz 3 lam 0 ((1 - w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.sub hw_int).pow 2).sub isIntegral_one)
  have hW : Sz 3 lam 0 w := hI _ hw_int
  have hcomb : Sz 3 lam 0 (((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w) := by
    have := hmul 0 0 _ _ (hsub _ _ (by simpa using hmul 0 0 _ _ hB h1) (by simpa using hmul 0 0 _ _ hA h2)) hW
    simpa using this
  have heq : ((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w
      = ((4 * d ^ 2 : ℕ) : ℂ) * (-σ) := by
    push_cast
    linear_combination (4 * (d : ℂ) * σ) * hw
  rw [heq] at hcomb
  have hd0 : ((4 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd
    exact_mod_cast (by positivity : 0 < 4 * d ^ 2).ne'
  have h3 : ¬ 3 ∣ 4 * d ^ 2 := by
    intro h
    have h0 : (4 * d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.mul_mod, Nat.pow_mod, hd] at h0
    norm_num at h0
  have hinv : Sz 3 lam 0 (((4 * d ^ 2 : ℕ) : ℂ))⁻¹ :=
    hint (4 * d ^ 2) _ h3 (by rw [mul_inv_cancel₀ hd0]; exact isIntegral_one)
  have hm := hmul 0 0 _ _ hinv hcomb
  rw [zero_add] at hm
  have hfin := hneg 0 _ hm
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_neg] at hfin
  exact hfin

end GlobalTheory.ArithThreeInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section

namespace GlobalTheory.HomFixMat

abbrev powPull {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => a)

theorem wchart_comp_le {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f ≫ φ) j ≤ f ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j := by
  intro y hy
  exact Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    simpa using this

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev topS (Rg : Type) [CommRing Rg] : Over (Sp Rg) := overRes (T := baseOver (Sp Rg)) ⊤

def coord {X : Scheme.{0}} {N : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (n : Fin N) : Γ(X, ⊤) :=
  g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.X n))

def matOf {X : Scheme.{0}} {mA mB : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Fin mA → Fin mB → Γ(X, ⊤) :=
  fun i j => coord g (finProdFinEquiv (i, j))

abbrev affπ (Rg : Type) [CommRing Rg] (N : ℕ) : Sp (MvPolynomial (Fin N) Rg) ⟶ Sp Rg :=
  Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))


variable (A B L M) in
def IsTest {T : Scheme.{0}} (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') : Prop :=
  IsGrpPullback A' A t φA' ∧ IsGrpPullback B' B t φB' ∧ IsMonHom Φ' ∧
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left)

def IsPullD {T₁ T₂ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left)
    (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left)
    (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (h : T₂ ⟶ T₁) : Prop :=
  ∃ (ψA : A₂.left ⟶ A₁.left) (ψB : B₂.left ⟶ B₁.left), IsGrpPullback A₂ A₁ h ψA ∧
    IsGrpPullback B₂ B₁ h ψB ∧ ψA ≫ φA₁ = φA₂ ∧ ψB ≫ φB₁ = φB₂ ∧ Φ₂.left ≫ ψB = ψA ≫ Φ₁.left


variable (A L) in
def IsBCBasis (k : ℕ) {m : ℕ} (b : Fin m → LB.Sec (LPow A L (k : ℤ) (topS Rg))) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (topS Rg).left)
    (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))),
    (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) →
    LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧
    Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev isoLB (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)} (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) : LB A'.left :=
  LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
    (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))

abbrev zeroPt {R : Type} [CommRing R] (A' : Over (Sp R)) [GrpObj A'] : Sp R ⟶ A'.left := η[A'].left


variable (L M) in
def IsMat (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A']
    [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) : Prop :=
  ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)),
    ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ α.IsGen ∧
    (∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k) ∧
    ∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}


variable (L M) in
def Hyps (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) : Prop :=
  IsAbelianScheme A ∧ IsAbelianScheme B ∧ L.IsLB ∧ M.IsLB ∧ eA.IsGen ∧ eB.IsGen ∧ RelAmple A L ∧ 1 ≤ k ∧
    VeryAmpleAt B M k ∧ IsBCBasis A L k bA ∧ IsBCBasis B M k bB

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat
variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

theorem IsPullD.comp {T₁ T₂ T₃ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] {φA₁ : A₁.left ⟶ A.left}
    {φB₁ : B₁.left ⟶ B.left} {Φ₁ : A₁ ⟶ B₁} {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] {φA₂ : A₂.left ⟶ A.left}
    {φB₂ : B₂.left ⟶ B.left} {Φ₂ : A₂ ⟶ B₂} {A₃ B₃ : Over T₃} [GrpObj A₃] [GrpObj B₃] {φA₃ : A₃.left ⟶ A.left}
    {φB₃ : B₃.left ⟶ B.left} {Φ₃ : A₃ ⟶ B₃} {h₁ : T₂ ⟶ T₁} {h₂ : T₃ ⟶ T₂}
    (p₁ : IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h₁) (p₂ : IsPullD φA₂ φB₂ Φ₂ φA₃ φB₃ Φ₃ h₂) :
    IsPullD φA₁ φB₁ Φ₁ φA₃ φB₃ Φ₃ (h₂ ≫ h₁) := by
  obtain ⟨ψA, ψB, qA, qB, eA, eB, eΦ⟩ := p₁
  obtain ⟨ψA', ψB', qA', qB', eA', eB', eΦ'⟩ := p₂
  refine ⟨ψA' ≫ ψA, ψB' ≫ ψB, qA'.comp qA, qB'.comp qB, by rw [Category.assoc, eA, eA'],
    by rw [Category.assoc, eB, eB'], ?_⟩
  rw [← Category.assoc, eΦ', Category.assoc, eΦ, Category.assoc]

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem hom_ext_affine (Rg : Type) [CommRing Rg] (N : ℕ) (X : Scheme.{0}) (g g' : X ⟶ Sp (MvPolynomial (Fin N) Rg))
    (h0 : g ≫ affπ Rg N = g' ≫ affπ Rg N) (h1 : ∀ n, coord g n = coord g' n) : g = g' := by
  apply ext_of_isAffine
  refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))) _ _).1 ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have e := congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)) h0
    simp only [Scheme.Hom.comp_appTop] at e
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg N).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
    rw [n2]
    simpa using e
  · intro n
    exact h1 n

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassTorsionQExpansionIntegral
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.ExpansionIntegral

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ)
    (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 →
    QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  intro l hl lam N _ M x hM hx hx0
  have hpos : 0 < M := Nat.pos_of_ne_zero fun h => hM (h ▸ dvd_zero l)
  have hpow : ∀ e : ℕ, ¬ l ∣ M ^ e := fun e h => hM (hl.out.dvd_of_dvd_pow h)
  have hsz := (_root_.GlobalTheory.SzRules.main l lam).1
  refine ⟨⟨cB N x, _root_.GlobalTheory.WpFam.ExpansionB.main N x hx0, fun k => hsz (M ^ 2) _ (hpow 2) ?_⟩,
    ⟨cD N x, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, fun k => hsz (M ^ 3) _ (hpow 3) ?_⟩⟩
  · rw [Nat.cast_pow]
    exact (_root_.GlobalTheory.WpFam.isIntegral_coefficients N M x k hpos hx).1
  · rw [Nat.cast_pow]
    exact (_root_.GlobalTheory.WpFam.isIntegral_coefficients N M x k hpos hx).2.1

end GlobalTheory.WpFam.ExpansionIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm in
theorem degW_le_of_isSide {σ : Type} {p q r s : ℕ} {e : Ln p q r s → σ}
    {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} [Fintype σ]
    (he : Function.Bijective e) (h : IsSide e act) {d : ℕ}
    {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ} (hd : P ∈ homog σ d) (hP0 : P ≠ 0)
    (hP : P ∈ wtSub act μ) : degW (cPair r s) μ ≤ d := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP0
  obtain ⟨h1, h2⟩ := (h.mem_wtSub μ P).1 hP
  have e1 : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.1 hm)
  rw [← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum]
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)
  · rw [mixed_weight _ _ (h1 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])
  · rw [mixed_weight _ _ (h2 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])

theorem degW_le_of_homog_wtSub : ∀ (p q r s : ℕ),
    (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧
    (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := fun _ _ _ _ =>
  ⟨fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Function.bijective_id GlobalTheory.JointHarm.isSide_one hd h0 hP,
    fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Prod.swap_bijective GlobalTheory.JointHarm.isSide_two hd h0 hP⟩

end GlobalTheory.FockAlg
end
end

