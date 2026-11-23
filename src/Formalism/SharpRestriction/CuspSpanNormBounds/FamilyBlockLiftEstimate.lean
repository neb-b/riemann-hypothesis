module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

open MeasureTheory Matrix Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.S.GramWordSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsDiffOpOn {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (U : Set (Fin m → ℂ))
    (R : ((Fin m → ℂ) → E) → (Fin m → ℂ) → E) : Prop :=
  ∃ a : ∀ k : Fin (d + 1), (Fin m → ℂ) → (ContinuousMultilinearMap ℝ (fun _ : Fin k.val => (Fin m → ℂ)) E →L[ℝ] E),
    (∀ k, ContDiffOn ℝ ∞ (a k) U) ∧
    ∀ (φ : (Fin m → ℂ) → E), ∀ x ∈ U, ContDiffAt ℝ d φ x → R φ x = ∑ k : Fin (d + 1), a k x (iteratedFDeriv ℝ k.val φ x)

def IsRadQQd (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  L.IsRadQQ R ∧ ∀ (Y : ℂ) (a b : Fin 2), IsDiffOpOn (2 * L.r + L.k0 + 2) L.BD (R Y a b)

abbrev GFn {k0 r : ℕ} (L : LocBessel (k0 + 1) r) :=
  Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)

abbrev Sec (k0 : ℕ) := ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

export Formalism.MainNotions.S.UnitaryLevelOperators (levOf headEl cutF)

def lev {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) : Lev :=
  (levOf L μsec).down j (r - j) (by show j + (r - j) = r; omega)

def headAt (k r j : ℕ) (hj : j ≤ r) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * (r - j) + k + 1)) (Fin (2 * (r - j) + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun p q => headEl k j (r - j) h g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def fullPt {r j : ℕ} (hj : j ≤ r) (p : Point ℂ j) : Point ℂ (r + 1) :=
  ⟨p.1 ++ List.replicate (r + 1 - j) ((1 : ℂ), 1), by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact p.2.1 b hb
      · rw [List.eq_of_mem_replicate hb]; exact ⟨one_ne_zero, le_rfl⟩
    · simp [p.2.2]; omega⟩


open Classical in
def orbJ {k r : ℕ} (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  if h : ∃ ν : Measure (PairSp k r), ∃ μR : Measure (Mt k r), IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν then
    OrbInt L F g h.choose else 0

def sliceJ {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) (F : GFn L) (p : Point ℂ j) :
    (lev L μsec j hj).GF :=
  fun g => orbJ L F (fullPt hj p) (headAt (k0 + 1) r j hj (ptMat p) g)

def IsCellOp (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ {g | Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    ∀ F : Lt.GF, SmoothOnH (Hpk (Lt.k0 + 1) Lt.r) F → ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r),
      Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0 → Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def minorsNe (Lt : Lev) (E : List ℕ) : Set (Mat Lt.k0 Lt.r) :=
  {g | ∀ l ∈ E, ∀ hl : l < Lt.r + 2, Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩ ≠ 0}

def CkAt (Lt : Lev) (o : ℕ) (F : Lt.GF) (g₀ : Mat Lt.k0 Lt.r) : Prop :=
  ∃ (U : Set (Mat Lt.k0 Lt.r)) (F' : Lt.GF), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ o F' U ∧
    ∀ g ∈ U, g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) → F g = F' g

def IsInvC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ F : Lt.GF, (∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), CkAt Lt o F g) →
      ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), Θ (Lt.act h n h' n' F) g = Lt.act h n h' n' (Θ F) g

def BigPosR (Lt : Lev) : Set (Mat Lt.k0 Lt.r) :=
  {g | g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ (∀ l : Fin (Lt.r + 2), Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g l ≠ 0) ∧
    0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g}

def IsCellOpAt (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, (ws n).length ≤ o) ∧
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ minorsNe Lt E ∩ {g | 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    (∀ n, ∀ w : List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)), ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), ε ≤ Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g →
        (∀ l ∈ E, ∀ hl : l < Lt.r + 2, δ ≤ Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩)) →
        ‖Lt.EwordV w (a n) g‖ ≤ C * (1 + Lev.matNorm g) ^ (dP + 3 * ((Lt.r : ℝ) + 1) * w.length)) ∧
    IsInvC Lt (Finset.univ.sup fun n => (ws n).length) Θ ∧
    ∀ F : Lt.GF, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), g ∈ minorsNe Lt E →
      0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g → CkAt Lt (Finset.univ.sup fun n => (ws n).length) F g →
      Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def RadC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) (R : Lt.POp) : Prop :=
  ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
    (∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
      ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ g ∈ BigPosR Lt, Lt.act h n h' n' J g = J g) →
    ∀ x ∈ Lt.BD, Lt.B (Θ J) x = R (Lt.B J) x

def IsInvL (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
      ∀ g ∈ BigPosR Lt, Θ (Lt.act h n h' n' J) g = Lt.act h n h' n' (Θ J) g

def IsLetters (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (w : Word) (Θ : AuxiliarySlotStates w.length → Lt.GF → Lt.GF) : Prop :=
  ∀ β, IsCellOp Lt j hj (Θ β) ∧ Lt.Rad (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧
    IsCellOpAt Lt [j] (w.length * j) ((w.length * j + w.length * j ^ 2 : ℕ) : ℝ) (Θ β) ∧
    RadC Lt (w.length * j) (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧ IsInvL Lt (w.length * j) (Θ β)

def pt0 : Point ℂ 0 := ⟨[], by simp⟩

structure GramMap (k0 r : ℕ) extends ValMap (k0 + 1) r where
  top : ∀ (B : LocBessel (k0 + 1) r), Set ℝ → Word → GFn B → List (ℂ × ℕ) → List (ℂ × ℕ) → ℂ
  top_nil : ∀ (B : LocBessel (k0 + 1) r) (I : Set ℝ) (F : GFn B) (p p' : List (ℂ × ℕ)),
    top B I [] F p p' = hsInner (V B F p) (V B F p')

structure Dat (D : D7) (k0 : ℕ) where
  hk : k0 + 1 = D.R.k
  B : D.what₂.Tau → LocBessel (k0 + 1) D.R.rS
  μsec : D.what₂.Tau → Sec k0
  l : D.what₂.Tau → Fin (k0 + 1)
  a : D.what₂.Tau → ℝ
  b : D.what₂.Tau → ℝ
  a1 : D.what₂.Tau → ℝ
  b1 : D.what₂.Tau → ℝ
  f : ∀ v, GFn (B v)
  R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (lev (B v) (μsec v) j hj).POp
  Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : Word), AuxiliarySlotStates w.length → GFn (B v) → GFn (B v)

abbrev GWord (D : D7) := D.what₂.Tau → Word

abbrev Head (D : D7) (j : ℕ) := D.what₂.Tau → Point ℂ j

def Len {D : D7} (m : ℕ) (w : GWord D) : Prop := ∀ v, (w v).length ≤ m

def NN (D : D7) (Ks : ℕ) : ℕ := 4 * Ks * (D.R.rS + 1)

namespace Dat

variable {D : D7} {k0 : ℕ} (X : Dat D k0)

abbrev lv (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) : Lev := lev (X.B v) (X.μsec v) j hj

def T (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z
def T' (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z'

def I (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a v) (X.b v)
def I1 (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a1 v) (X.b1 v)

def sg (v : D.what₂.Tau) : ℝ := sCut (X.B v).u (X.B v).u' (X.I v)

def loc (v : D.what₂.Tau) : LocalDataRealPlace D where
  lam := fun s => (X.B v).lam (Fin.cast (by have := X.hk; omega) s)
  u := fun i => (X.B v).u (Fin.cast X.hk.symm i)
  u' := fun i => (X.B v).u' (Fin.cast X.hk.symm i)
  l := Fin.cast X.hk (X.l v)
  a := X.a v
  b := X.b v
  a1 := X.a1 v
  b1 := X.b1 v

def admitted (w : GWord D) : Prop := ∀ v, Admissible (X.I v) (w v)

def brk (w : GWord D) : ℝ := ∏ v, brkW (X.B v).lam ((w v).map Prod.snd)

def Fv (χ : ℝ → ℝ) (ε : ℝ) (v : D.what₂.Tau) : GFn (X.B v) := cutF (X.B v).z (X.B v).z' χ ε (X.f v)

def gramLow (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) (w : Word) (F : GFn (X.B v)) (p p' : Point ℂ j) : ℂ :=
  (X.lv v j hj).form ((X.lv v j hj).wmod (X.R v j hj) (X.sg v) (X.B v).u (X.B v).u' w).RR
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p))
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p'))

def energy (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) : ℂ :=
  ∏ v, X.gramLow v 0 (Nat.zero_le _) (w v) (X.Fv χ ε v) pt0 pt0

def jn2 : ℂ := ∏ v, (X.B v).beta (X.μsec v) (X.f v) (X.f v)

def Std (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  4 ≤ Ks ∧ ∀ v,
    (∀ i, (X.B v).ε i = epsSH D.R (Fin.cast (by have := X.hk; omega) i)) ∧ (X.B v).c = cStd ∧
    IsSection (k0 + 1) D.R.rS (X.B v).z (X.B v).z' (X.μsec v) ∧
    IsCutS (X.B v).u (X.B v).u' (X.I v) ∧
    ((X.B v).u (X.l v) ≠ (X.B v).u' (X.l v) ∧
      min (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) + 2 ≤ X.a v ∧ X.a v ≤ X.b v ∧
      X.b v ≤ max (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) - 2) ∧
    (∃ ρ : Fin k0 → ℝ, Interlace (X.B v).u ρ ∧ Interlace (X.B v).u' ρ) ∧
    X.I1 v ⊆ X.I v ∧ X.a1 v ≤ X.b1 v ∧ ((NN D Ks : ℕ) : ℝ) ^ 3 / 2 ≤ X.b1 v - X.a1 v ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u (X.B v).lam ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u' (X.B v).lam ∧
    C₀ * ((D.R.k : ℝ) * (NN D Ks : ℕ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((NN D Ks : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 +
      ((NN D Ks : ℕ) : ℝ) ^ 3) ≤ X.b v - X.a v ∧
    GapAtLeast (X.B v).ε (X.B v).lam
      (Cg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (((NN D Ks : ℕ) : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) ∧
    UnitaryLevelOperators.IsKFinCoefT (X.B v).σ (X.f v) ∧
    (∀ (j : ℕ) (hj : j ≤ D.R.rS), IsRadQQd (X.lv v j hj) (X.R v j hj)) ∧
    ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), IsLetters (levOf (X.B v) (X.μsec v)) j hj w (X.Th v j hj w)

end Dat

section Weights

variable {D : D7} {k0 : ℕ} (Gm : GramMap k0 D.R.rS) (X : Dat D k0)


end Weights

section Lattices

variable (D : D7)

end Lattices

section Estimates

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

def E (k0 : ℕ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ w : GWord D, X.admitted w → Len (NN D Ks) w →
    Tendsto (fun ε => X.energy w χ ε) (𝓝[>] 0) (𝓝 ((X.brk w : ℂ) * X.jn2))

end Estimates

section TopLevel

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

end TopLevel

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : ∀ k0 r : ℕ, GramMap k0 r)

end Family

end Formalism.MainNotions.S.GramWordSpace

end
