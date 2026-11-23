module

public import Mathlib
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

@[expose] public section

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

def GMod.quots {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R] :
    List (Deg k × R) → GMod B R k → GMod B R k
  | [], F => F
  | (_, s) :: ts, F => GMod.quots ts (F.quot s)

def RulePos : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 ts F.Ann → ∀ᶠ m in atTop, 0 ≤ chi ts F m

def RuleUB : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts us : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 (ts ++ us) →
    F.IsGr X.𝒜 → admitted X.𝒜 (ts ++ us) F.Ann →
    ∀ᶠ m in atTop, chi (ts ++ us) F m ≤ chi us (F.quots ts) m

def RuleMono : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F' F F'' : X.Mod), Valid X.𝒜 ts →
    F'.IsGr X.𝒜 → F.IsGr X.𝒜 → F''.IsGr X.𝒜 → SES F' F F'' → admitted X.𝒜 ts F.Ann →
    ∀ᶠ m in atTop, chi ts F'' m ≤ chi ts F m

def RuleSmall : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod), Valid X.𝒜 ts → F.IsGr X.𝒜 →
    admitted X.𝒜 [] F.Ann → ∀ᶠ m in atTop,
      chi ts F m = ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
        (-1 : ℤ) ^ I.card * ((Module.length X.B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

def EulerAdditivityDegreeZero : Prop :=
  ∀ (k : ℕ) (X : HidaSetting k) (ts : List (Deg k × X.R)) (F : X.Mod) (d : Deg k) (s s' : X.R),
    Valid X.𝒜 ((0, s) :: (d, s') :: ts) → F.IsGr X.𝒜 → admitted X.𝒜 ((d, s * s') :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, s * s') :: ts) F m = chi ((0, s) :: ts) F m + chi ((d, s') :: ts) F m

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

namespace GIso

variable {F G : GMod B R k}

theorem mem_gr_iff (φ : GIso F G) (m : Deg k) (x : F.M) : φ.e x ∈ G.gr m ↔ x ∈ F.gr m := by
  rw [← φ.map_gr m]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := φ.e.injective hxy
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def grEquiv (φ : GIso F G) (m : Deg k) : F.gr m ≃ₗ[B] G.gr m :=
  LinearEquiv.ofSubmodules (φ.e.restrictScalars B) (F.gr m) (G.gr m) (by
    rw [← φ.map_gr m]; rfl)

def sub (φ : GIso F G) (N : Submodule R F.M) (N' : Submodule R G.M)
    (h : N.map (φ.e : F.M →ₗ[R] G.M) = N') : GIso (F.sub N) (G.sub N') where
  e := LinearEquiv.ofSubmodules φ.e N N' h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (φ.mem_gr_iff m x.1).2 hx
    · intro hy
      refine ⟨(LinearEquiv.ofSubmodules φ.e N N' h).symm y, ?_, ?_⟩
      · have h1 : φ.e ((LinearEquiv.ofSubmodules φ.e N N' h).symm y).1 = y.1 := by
          have := congrArg Subtype.val
            ((LinearEquiv.ofSubmodules φ.e N N' h).apply_symm_apply y)
          exact this
        have h2 : φ.e ((LinearEquiv.ofSubmodules φ.e N N' h).symm y).1 ∈ G.gr m := by
          rw [h1]; exact hy
        exact (φ.mem_gr_iff m _).1 h2
      · exact (LinearEquiv.ofSubmodules φ.e N N' h).apply_symm_apply y

def quo (φ : GIso F G) (N : Submodule R F.M) (N' : Submodule R G.M)
    (h : N.map (φ.e : F.M →ₗ[R] G.M) = N') : GIso (F.quo N) (G.quo N') where
  e := Submodule.Quotient.equiv N N' φ.e h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨φ.e x, (φ.mem_gr_iff m x).2 hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.mkQ (φ.e.symm z), ⟨φ.e.symm z, ?_, rfl⟩, ?_⟩
      · apply (φ.mem_gr_iff m _).1
        rw [LinearEquiv.apply_symm_apply]; exact hz
      · show N'.mkQ (φ.e (φ.e.symm z)) = N'.mkQ z
        rw [LinearEquiv.apply_symm_apply]

def shift (φ : GIso F G) (d : Deg k) : GIso (F.shift d) (G.shift d) where
  e := φ.e
  map_gr m := φ.map_gr (m - d)

def quot (φ : GIso F G) (s : R) : GIso (F.quot s) (G.quot s) :=
  φ.quo _ _ (by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨φ.e x, (φ.e.map_smul s x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨s • φ.e.symm z, ⟨φ.e.symm z, rfl⟩, ?_⟩
      show φ.e (s • φ.e.symm z) = s • z
      rw [map_smul, LinearEquiv.apply_symm_apply])

def ann (φ : GIso F G) (s : R) (d : Deg k) : GIso (F.ann s d) (G.ann s d) :=
  (φ.sub _ _ (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : s • x = 0 := hx
      show s • φ.e x = 0
      rw [← map_smul, hx', map_zero]
    · intro hy
      have hy' : s • y = 0 := hy
      refine ⟨φ.e.symm y, ?_, φ.e.apply_symm_apply y⟩
      show s • φ.e.symm y = 0
      rw [← map_smul, hy', map_zero])).shift d

end GIso

theorem chi_congr (ts : List (Deg k × R)) : ∀ (F G : GMod B R k), GIso F G →
    ∀ m, chi ts F m = chi ts G m := by
  induction ts with
  | nil =>
    intro F G φ m
    simp only [chi]
    rw [(φ.grEquiv m).length_eq]
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F G φ m
    simp only [chi]
    rw [ih _ _ (φ.quot s) m, ih _ _ (φ.ann s d) m]

theorem ruleIso : RuleIso := fun _ _ ts F G φ m => chi_congr ts F G φ m

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleNzd
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem chi_of_subsingleton (ts : List (Deg k × R)) : ∀ (F : GMod B R k), Subsingleton F.M →
    ∀ m, chi ts F m = 0 := by
  induction ts with
  | nil =>
    intro F hF m
    have : Subsingleton (F.gr m) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    simp only [chi]
    rw [Module.length_eq_zero]
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hF m
    simp only [chi]
    have h1 : Subsingleton (F.quot s).M :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
        rw [Subsingleton.elim x y]⟩
    have h2 : Subsingleton (F.ann s d).M :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := F.M) _ _)⟩
    rw [ih _ h1, ih _ h2, sub_zero]

theorem chi_nzd (ts : List (Deg k × R)) (F : GMod B R k) (d : Deg k) (s : R)
    (h : ∀ x : F.M, s • x = 0 → x = 0) (m : Deg k) :
    chi ((d, s) :: ts) F m = chi ts (F.quot s) m := by
  have h2 : Subsingleton (F.ann s d).M :=
    ⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩
  simp only [chi]
  rw [chi_of_subsingleton ts _ h2, sub_zero]

theorem ruleNzd : RuleNzd := fun _ _ ts F d s h m => chi_nzd ts F d s h m

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift
section
noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem GMod.quot_shift (F : GMod B R k) (s : R) (d : Deg k) :
    (F.shift d).quot s = (F.quot s).shift d := rfl

theorem GMod.ann_shift (F : GMod B R k) (s : R) (d d' : Deg k) :
    (F.shift d).ann s d' = (F.ann s d').shift d := by
  have h : ∀ m : Deg k, m - d' - d = m - d - d' := fun m => sub_right_comm m d' d
  unfold GMod.ann GMod.shift GMod.sub
  simp only [h]

theorem chi_shift (ts : List (Deg k × R)) : ∀ (F : GMod B R k) (d m : Deg k),
    chi ts (F.shift d) m = chi ts F (m - d) := by
  induction ts with
  | nil => intro F d m; rfl
  | cons p ts ih =>
    obtain ⟨d', s⟩ := p
    intro F d m
    simp only [chi]
    rw [GMod.quot_shift, GMod.ann_shift, ih, ih]

theorem ruleShift : RuleShift := fun _ _ ts F d m => chi_shift ts F d m

end Formalism.MainNotions.V.Pf.V2.Calc
end
end

