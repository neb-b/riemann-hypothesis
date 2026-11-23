module

public import Mathlib

@[expose] public section

open NumberField Matrix

noncomputable section

namespace UpperTheory.V.KT

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

abbrev Lat : Type := Fin N → 𝓞 L

abbrev Gm : Type := GL (Fin N) (𝓞 L)

abbrev VR : Type := InfinitePlace L → Fin N → ℂ

abbrev dd : ℕ := Module.finrank ℚ L * N

abbrev absD : ℕ := (NumberField.discr L).natAbs

def HSsub : Submodule ℝ (InfinitePlace L → Fin N → Fin N → ℂ) where
  carrier := {h | ∀ w, (Matrix.of (h w)).IsHermitian}
  add_mem' := fun {a b} ha hb w => (ha w).add (hb w)
  zero_mem' := fun _ => Matrix.isHermitian_zero
  smul_mem' := fun c h hh w => by
    have := hh w
    ext i j
    have h2 := congrFun (congrFun this i) j
    simp only [conjTranspose_apply, of_apply, Pi.smul_apply] at h2 ⊢
    rw [← h2]; simp

abbrev HS : Type := HSsub L N

variable {L N}

def embO (w : InfinitePlace L) : 𝓞 L →+* ℂ := w.embedding.comp (algebraMap (𝓞 L) L)

def mat (h : HS L N) (w : InfinitePlace L) : Matrix (Fin N) (Fin N) ℂ := Matrix.of (h.1 w)

theorem mat_herm (h : HS L N) (w : InfinitePlace L) : (mat h w).IsHermitian := h.2 w

@[simp] theorem mat_add (h k : HS L N) (w : InfinitePlace L) :
    mat (h + k) w = mat h w + mat k w := rfl

@[simp] theorem mat_smul (c : ℝ) (h : HS L N) (w : InfinitePlace L) :
    mat (c • h) w = c • mat h w := rfl

@[simp] theorem mat_zero (w : InfinitePlace L) : mat (0 : HS L N) w = 0 := rfl

theorem HS_ext {h k : HS L N} (e : ∀ w, mat h w = mat k w) : h = k :=
  Subtype.ext (funext fun w => e w)

def mkHS (A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ) (hA : ∀ w, (A w).IsHermitian) :
    HS L N := ⟨fun w i j => A w i j, hA⟩

@[simp] theorem mat_mkHS (A : InfinitePlace L → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ w, (A w).IsHermitian) (w : InfinitePlace L) : mat (mkHS A hA) w = A w := rfl

def toR (y : Lat L N) : VR L N := fun w a => embO w (y a)

def qR (h : HS L N) (z : VR L N) : ℝ := ∑ w, (star (z w) ⬝ᵥ (mat h w *ᵥ z w)).re

def q (h : HS L N) (y : Lat L N) : ℝ := qR h (toR y)

def evR (z : VR L N) : HS L N →ₗ[ℝ] ℝ where
  toFun h := qR h z
  map_add' h k := by
    simp [qR, add_mulVec, dotProduct_add, Finset.sum_add_distrib]
  map_smul' c h := by
    simp [qR, smul_mulVec, dotProduct_smul, Finset.mul_sum]

def ev (y : Lat L N) : HS L N →ₗ[ℝ] ℝ := evR (toR y)

@[simp] theorem evR_apply (z : VR L N) (h : HS L N) : evR z h = qR h z := rfl
@[simp] theorem ev_apply (y : Lat L N) (h : HS L N) : ev y h = q h y := rfl

variable (L N)

def Pos : Set (HS L N) := {h | open ComplexOrder in ∀ w, (mat h w).PosDef}

def Ry : Set (HS L N) := {h | ∀ y : Lat L N, y ≠ 0 → 1 ≤ q h y}

variable {L N}

def minVec (h : HS L N) : Set (Lat L N) := {y | q h y = 1}

def face (M : Set (Lat L N)) : Set (HS L N) := {h | h ∈ Ry L N ∧ M ⊆ minVec h}

def toL (y : Lat L N) : Fin N → L := fun a => (y a : L)

def spanL (M : Set (Lat L N)) : Submodule L (Fin N → L) := Submodule.span L (toL '' M)

def Spans (M : Set (Lat L N)) : Prop := spanL M = ⊤

variable (L N)

def WR : Set (HS L N) := {h | h ∈ Ry L N ∧ Spans (minVec h)}

def Cell : Type := {F : Set (HS L N) // F.Nonempty ∧ ∃ M, Spans M ∧ F = face M}

instance : PartialOrder (Cell L N) := Subtype.partialOrder _

variable {L N}

def carrier (h : HS L N) (hh : h ∈ WR L N) : Cell L N :=
  ⟨face (minVec h), ⟨h, hh.1, subset_rfl⟩, minVec h, hh.2, rfl⟩

theorem smul_lat (g : Gm L N) (y : Lat L N) :
    g • y = (g : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ y := rfl

def pull (A : Matrix (Fin N) (Fin N) (𝓞 L)) : HS L N →ₗ[ℝ] HS L N where
  toFun h := mkHS (fun w => (A.map (embO w))ᴴ * mat h w * A.map (embO w))
    (fun w => isHermitian_conjTranspose_mul_mul _ (mat_herm h w))
  map_add' h k := HS_ext fun w => by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c h := HS_ext fun w => by simp

theorem mat_pull (A : Matrix (Fin N) (Fin N) (𝓞 L)) (h : HS L N) (w : InfinitePlace L) :
    mat (pull A h) w = (A.map (embO w))ᴴ * mat h w * A.map (embO w) := rfl

theorem pull_one (h : HS L N) : pull 1 h = h := HS_ext fun w => by simp [mat_pull]

theorem pull_mul (A B : Matrix (Fin N) (Fin N) (𝓞 L)) (h : HS L N) :
    pull (A * B) h = pull B (pull A h) := HS_ext fun w => by
  simp [mat_pull, Matrix.map_mul, Matrix.mul_assoc]

theorem toR_mulVec (A : Matrix (Fin N) (Fin N) (𝓞 L)) (y : Lat L N) (w : InfinitePlace L) :
    toR (A *ᵥ y) w = A.map (embO w) *ᵥ toR y w := by
  ext a; simp [toR, mulVec, dotProduct]

theorem q_pull (A : Matrix (Fin N) (Fin N) (𝓞 L)) (h : HS L N) (y : Lat L N) :
    q (pull A h) y = q h (A *ᵥ y) := by
  simp only [q, qR, mat_pull, toR_mulVec]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

instance : DistribMulAction (Gm L N) (HS L N) where
  smul g h := pull ((g⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) h
  one_smul h := by change pull ((1⁻¹ : Gm L N) : Matrix _ _ _) h = h; simp [pull_one]
  mul_smul g k h := by
    change pull (((g * k)⁻¹ : Gm L N) : Matrix _ _ _) h =
      pull ((g⁻¹ : Gm L N) : Matrix _ _ _) (pull ((k⁻¹ : Gm L N) : Matrix _ _ _) h)
    rw [_root_.mul_inv_rev, Units.val_mul, pull_mul]
  smul_zero g := map_zero (pull _)
  smul_add g := map_add (pull _)

theorem q_smul (g : Gm L N) (h : HS L N) (y : Lat L N) : q (g • h) y = q h (g⁻¹ • y) :=
  q_pull _ h y

theorem smul_mem_Ry (g : Gm L N) {h : HS L N} (hh : h ∈ Ry L N) : g • h ∈ Ry L N := by
  intro y hy
  rw [q_smul]
  exact hh _ (fun e => hy (by rw [← smul_inv_smul g y, e, smul_zero]))

variable (L N)

def Simp (p : ℕ) : Type := {s : Fin (p + 1) → Cell L N // StrictMono s}

variable {L N}

def Simp.del {p : ℕ} (i : Fin (p + 2)) (s : Simp L N (p + 1)) : Simp L N p :=
  ⟨fun j => s.1 (i.succAbove j), s.2.comp (Fin.strictMono_succAbove i)⟩

variable (L N)

def bd (p : ℕ) : (Simp L N (p + 1) →₀ ℤ) →ₗ[ℤ] (Simp L N p →₀ ℤ) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (Simp.del i)

def I0 : ℕ := absD L ^ N * dd L N ^ dd L N

def RR : ℕ := N ^ N * I0 L N ^ 2

def orbBound (p : ℕ) : ℕ :=
  I0 L N ^ (1 + dd L N * N) * ((2 * RR L N + 1) ^ dd L N + 1) ^ (dd L N * N * (p + 1))

variable {L N}

def ColsMin (A : Matrix (Fin N) (Fin N) (𝓞 L)) (h : HS L N) : Prop :=
  ∀ a, q h (fun i => A i a) = 1

def nrmDet (A : Matrix (Fin N) (Fin N) (𝓞 L)) : ℕ := (Algebra.norm ℤ A.det).natAbs

def nearVec (A : Matrix (Fin N) (Fin N) (𝓞 L)) : Set (Lat L N) :=
  {y | ∃ h ∈ Ry L N, ColsMin A h ∧ q h y = 1}

end UpperTheory.V.KT
