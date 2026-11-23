module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpWindowOfJumpSets
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow


open Formalism.MainNotions.AdmissibleParameterJ in
theorem JJ_finite_ncard {D : D7} (L : SizeData₂ D) (hb : AdmissibleParameterJ.CloudCentreDistance L) (hn : 0 < D.R.nV) (up : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite ∧ (JJ D up j ρ).ncard = D.R.nV := by
  have hc : (Jp D j ρ).ncard = D.R.nV := (hb j h1 h2 ρ).2.2.2.2.2
  have hf : (Jp D j ρ).Finite := Set.finite_of_ncard_pos (by omega)
  cases up with
  | true => simpa [JJ] using And.intro hf hc
  | false =>
    have hinj : Function.Injective (AdmissibleParameterJ.refl D) := by
      intro a b hab
      simp only [AdmissibleParameterJ.refl] at hab
      linarith
    have hEq : Jm D j ρ = AdmissibleParameterJ.refl D '' Jp D j ρ := by
      ext q
      simp only [Jm, reflS, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨_, h, by simp [AdmissibleParameterJ.refl]⟩
      · rintro ⟨u, hu, rfl⟩
        have : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D u) = u := by simp [AdmissibleParameterJ.refl]
        rwa [this]
    simp only [JJ, Bool.false_eq_true, if_false]
    rw [hEq]
    exact ⟨hf.image _, by rw [Set.ncard_image_of_injective _ hinj, hc]⟩

theorem jumpWindow_of_jumpSets : ∀ (D : D7) (large₂ : SizeData₂ D), AdmissibleParameterJ.JumpConditions large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ ∧ ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ π : D.nd.X i, GlobalTheory.BlockWindow.JumpWindow D i r π ⌊2 * large₂.sc.b⌋₊ := by
  classical
  intro D large₂ hJ hP
  obtain ⟨⟨ep, hA⟩, hb, -, -, he, -, -⟩ := hJ
  have hn : 0 < D.R.nV := by
    have := D.R.rank_add_five_le
    unfold Ranks.nV; omega
  have hS := large₂.Sc_pos
  have hη := large₂.etaSz_pos
  have hP' : large₂.Sc + large₂.etaSz + (D.R.t : ℝ) + 2 ≤ large₂.sc.b := hP
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨Nat.le_floor (by linarith), ?_⟩
  intro i r hr π w hw CL h τ
  obtain ⟨g, ρ, -, hx, -⟩ := hA i r hr w hw ⟨CL, h⟩ τ
  have hj := D.nd.j_range i
  obtain ⟨hfin, hcard⟩ := JJ_finite_ncard large₂ hb hn (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) hj.1 hj.2 ρ
  have hpre : ((fun a : ℤ => (a : ℚ)) ⁻¹' AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ).Finite :=
    hfin.preimage (Int.cast_injective.injOn)
  refine ⟨hpre.toFinset, ?_, ?_, ?_⟩
  · rw [← hcard, ← Set.ncard_eq_toFinset_card _ hpre,
      ← Set.ncard_image_of_injective _ (Int.cast_injective (α := ℚ))]
    exact Set.ncard_le_ncard (Set.image_preimage_subset _ _) hfin
  · intro u hu
    have hu' : (u : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := by
      simpa using hu
    have hbd := he.1 _ hj.1 hj.2 ρ _ _ hu'
    have hc0 : ((AdmissibleParameterJ.c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
      simp [AdmissibleParameterJ.c0]
    rw [hc0] at hbd
    have habs : ((u.natAbs : ℕ) : ℝ) = |((u : ℚ) : ℝ)| := by
      simp [Nat.cast_natAbs]
    have hle : u.natAbs + 1 ≤ ⌊2 * large₂.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      rw [habs]
      linarith
    omega
  · intro a ha
    have : (a : ℚ) ∈ AdmissibleParameterJ.JJ D (decide (AdmissibleParameterJ.TypeU D ep g)) (D.nd.j i) ρ := (hx π a).1.1 ha
    simpa using this

end GlobalTheory.BlockWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeRoundedSizeBound
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (_root_.GlobalTheory.HTW.bHat_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := _root_.GlobalTheory.HTW.wHat_le L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
section
noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

abbrev MP (R : Type) [CommRing R] (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) R

def genM (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MP R n) := Matrix.of fun a s => X (a, s)

def cofAct (R : Type) [CommRing R] (n : ℕ) : MP R n →ₐ[R] MP R n :=
  aeval fun v => (genM R n).adjugate v.2.rev v.1

def nuDual {m : ℕ} (ν : Fin (m + 1) → ℕ) : Fin (m + 1) → ℕ := fun i => ν 0 - ν i.rev

def CofRel (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (f g : MP R (m + 1)) : Prop :=
  (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * g = cofAct R (m + 1) f

def stdN (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (dualWeyl O n n ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def stdD (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν : Fin n → ℕ) : Submodule O (MP Kf n) :=
  (weyl O n n le_rfl ν).map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap

def rnd (Kf : Type) [Field Kf] {n : ℕ} (e : ℤ) (g : Matrix (Fin n) (Fin n) Kf) : MP Kf n →ₗ[Kf] MP Kf n :=
  g.det ^ (-e) • (rowAct Kf g⁻¹).toLinearMap

def twLat {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n : ℕ} (e : ℤ) (S : Submodule O (MP Kf n))
    (g : Matrix (Fin n) (Fin n) Kf) : Submodule O (MP Kf n) :=
  S.map ((rnd Kf e g).restrictScalars O)

def PosOk (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n : ℕ) (ν ν' : Fin n → ℕ) (e e' c : ℤ)
    (tw : Matrix (Fin n) (Fin n) Kf → Matrix (Fin n) (Fin n) Kf) (Ψ : MP Kf n →ₗ[Kf] MP Kf n) : Prop :=
  (∀ f ∈ dualWeyl Kf n n ν, Ψ f = 0 → f = 0) ∧
  (dualWeyl Kf n n ν).map Ψ = dualWeyl Kf n n ν' ∧
  (∀ h : Matrix (Fin n) (Fin n) Kf, IsUnit h.det → ∀ f ∈ dualWeyl Kf n n ν,
    Ψ (rnd Kf e h f) = h.det ^ c • rnd Kf e' (tw h) (Ψ f)) ∧
  (stdN O Kf n ν).map (Ψ.restrictScalars O) = stdN O Kf n ν' ∧
  (stdD O Kf n ν).map (Ψ.restrictScalars O) = stdD O Kf n ν'

end GlobalTheory.ValCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_box : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).Box := by
  intro D L C j ε τ φ hR
  have hb := (_root_.GlobalTheory.HTW.bHat_window L C hR).1
  have hw := (_root_.GlobalTheory.HTW.wHat_le L C hR).2.2
  have hnt := fun g => _root_.GlobalTheory.HTW.size_not_thick L C g j hR
  have hth := fun g => GlobalTheory.T.floor_size_bounds_at_thick_embedding L g j
  obtain ⟨hC, h100, hroom, hwb, -, hCb⟩ := hR
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have ht := L.t_win.1
  have ht' : 1 ≤ D.R.t := by exact_mod_cast ht
  have hLw : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : 0 ≤ L.sc.b' := by linarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by
    have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hb'
    linarith
  have hw0 : (0 : ℝ) ≤ wHat D := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
  have hE : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold etaHat
    push_cast
    have := Nat.floor_le hη.le
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ bHat L
    have : (1 : ℝ) ≤ bHat L := by linarith
    exact_mod_cast this
  · show 1 ≤ wHat D
    unfold wHat
    omega
  · show 20 * wHat D ≤ bHat L
    have : (20 : ℝ) * wHat D ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * etaHat L ≤ bHat L
    have : (20 : ℝ) * etaHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · show 20 * sHat L ≤ bHat L
    have : (20 : ℝ) * sHat L ≤ bHat L := by linarith
    exact_mod_cast this
  · intro i
    show ((etaHat L : ℕ) : ℤ) < szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
    generalize letter τ φ i = g
    have hsz : L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) := by
      by_cases hT : Thick D.host g
      · have := (hth g hT).1
        linarith
      · exact (hnt g hT).1
    have key : ((etaHat L : ℕ) : ℤ) + D.R.t + 1 < ⌊(hcAt D g).e j⌋ := by
      have : ((etaHat L : ℕ) : ℝ) + D.R.t + 1 < (⌊(hcAt D g).e j⌋ : ℝ) := by linarith
      exact_mod_cast this
    unfold szT
    split_ifs <;> omega

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThick
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_large_of_roomy {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (100 : ℝ) ≤ bHat L ∧ 2 * (etaHat L : ℝ) + sHat L ≤ (bHat L : ℝ) / 10 := by
  obtain ⟨hC, hw, hr, hwb, -, hb⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := le_trans (mul_le_mul_of_nonneg_right hCL hb') hb
  have h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    have := Nat.floor_le he.le
    unfold etaHat
    push_cast
    linarith
  have h2 : (sHat L : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t := by
    unfold bHat
    omega
  have h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t := by
    have h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h5
  constructor <;> linarith

theorem conjWord_hypAT {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ)
    (hR : Roomy L C) (hl : 11 ≤ l) (hτ : Thick D.host τ) :
    (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  obtain ⟨hord, hplc⟩ := _root_.GlobalTheory.HTW.ConjWord.conj_word_one_place τ
  have hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
    intro i
    rw [_root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ (D.R.cc) hR i]
    unfold Thick at hτ ⊢
    rw [hplc i]
    exact hτ
  refine ⟨⟨?_, ?_, ?_⟩, hth⟩
  · rw [hord]; exact even_two
  · exact (_root_.GlobalTheory.signs_alternate_inert ε τ (D.R.cc) rfl).2
  · intro M hM i
    obtain ⟨hB, hroom⟩ := bHat_large_of_roomy L C hR
    have hη : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
    have hS : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
    have key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧
        ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L := by
      intro k
      obtain ⟨h1, h2⟩ := hth k
      have h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k := h1
      have h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ) := h2
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    obtain ⟨k, hk⟩ := hM.1
    have hMk := key k
    rw [hk] at hMk
    have hi := key i
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.alternatingWord_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ)
      ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom
      (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩)
      (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    refine ⟨?_, h1, h2⟩
    have : (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) := by linarith [hi.1]
    exact_mod_cast this

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBounds
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem abs_szT_sub_floor_le {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) :
    |((szT P j s : ℤ) : ℝ) - ((⌊P.e j⌋ : ℤ) : ℝ)| ≤ ((R.t : ℝ) + 1) / 2 := by
  have h0 : (0 : ℤ) ≤ ((R.t : ℤ) + 1) / 2 := by omega
  have h1 : 2 * (((R.t : ℤ) + 1) / 2) ≤ (R.t : ℤ) + 1 := by omega
  have h0' : (0 : ℝ) ≤ ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : 2 * ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) ≤ (R.t : ℝ) + 1 := by exact_mod_cast h1
  unfold szT
  generalize ((R.t : ℤ) + 1) / 2 = q at h0' h1'
  cases s
  · simp only [Bool.false_eq_true, if_false, Int.cast_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [if_true, Int.cast_add]
    rw [abs_le]; constructor <;> linarith

theorem pageWord_not_thick_size : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  intro D L C j ε τ φ hR i hi
  have hnt : ¬ Thick D.host (letter τ φ i) := fun h => hi ((_root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR i).2 h)
  have h1 := _root_.GlobalTheory.HTW.size_not_thick L C (letter τ φ i) j hR hnt
  have h2 := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hR).2 (letter τ φ i) j hnt
  refine ⟨((⌊(hcAt D (letter τ φ i)).e j⌋ : ℤ) : ℝ), h1.1, ?_, h1.2, ?_⟩
  · exact_mod_cast h2
  · exact abs_szT_sub_floor_le _ j _

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickOr
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thickOr : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → (pageWord L j ε τ φ).ThickOr := by
  intro D L C j ε τ φ hR i
  by_cases h : Thick D.host (letter τ φ i)
  · exact Or.inl ((_root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR i).2 h)
  · right
    have h1 := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hR).2 _ j h
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) ≤ ((wHat D : ℕ) : ℤ)
    unfold szT wHat
    push_cast
    split_ifs <;> omega

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MuBlock

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem frobEig_spehLoc (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) :
    A.unr (spehLoc N A p w) ∧ A.frobEig (spehLoc N A p w) =
      ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum :=
  frobEig_foldr N A _ h (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) _

theorem frobEig_isoLoc (Pa : List (Part A.CG)) (w : PlE H) (h : ∀ p ∈ Pa, A.unr (A.locG p.π w)) :
    A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) =
      (Pa.map fun p => ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum := by
  induction Pa with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p Pa ih =>
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := frobEig_spehLoc N A p w (h p (List.mem_cons_self ..))
    refine ⟨(A.unr_sum _ _).2 ⟨hp.1, ih'.1⟩, ?_⟩
    change A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A Pa w)) = _
    rw [A.frobEig_sum _ _ hp.1 ih'.1, hp.2, ih'.2]
    simp only [List.map_cons, List.sum_cons]

theorem frobEig_eq_single {w : PlE H} (a : A.LP w) (hu : A.unr a) (hd : A.lpDim a = 1) :
    ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem absNorm_eq_normV (w : PlE H) : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem exists_split_not_mem (hC : ∀ Sg : Set (PlE H), Sg.Finite →
    closure {σ : G H.E N.Om | ∃ w ∉ Sg, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = Set.univ)
    (S : Set (PlE H)) (hS : S.Finite) : ∃ w ∉ S, IsSplitPl H w := by
  by_contra hn
  push_neg at hn
  have h := hC S hS
  have he : {σ : G H.E N.Om | ∃ w ∉ S, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = ∅ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, hs, -⟩
    exact hn w hw hs
  rw [he, closure_empty] at h
  exact Set.empty_ne_univ h

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock
end
end

