module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
section
noncomputable section

namespace Formalism.MainNotions.S

open NumberField Formalism.BasicNotions

structure AutTie (D : D7) (B : RowsAut) (pl : InfinitePlace B.I.F ≃ D.what₂.Tau) : Prop where
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  rd_eq : B.I.rd = D.host.rdE
  eps_eq : ∀ v (i : Fin B.I.n), B.I.ε v i = epsS D.R (Fin.cast n_eq i)
  lam_eq : ∀ v (i : Fin B.I.n), B.lam v i = lamS D.R (D.hc (pl v)) (Fin.cast n_eq i)
  ds : ∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)
  low : ∀ v, IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v)
  g_eq : B.g = D.host.g 0 * D.host.g 1
  g0_eq : B.g₀ = D.host.g 0
  D_eq : B.D = D.what₂.Dall
  Dstar_eq : D.what₂.Dstar =
    B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (B.w v)) B.μf B.fund B.e

end Formalism.MainNotions.S
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
section
noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions MeasureTheory
open scoped InnerProductSpace ComplexOrder nonZeroDivisors NumberField

section S1bNum

variable (D : D7)

def plEmb (v : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau v).1

def rhoReal (i s : ℕ) : ℝ := D.host.rdE ^ (-((((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (i : ℤ) - (s : ℤ))))

def locBlocksFrom (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) : ℕ → List (D.host.E × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | a, (t, s) :: bs => (((ρ (a + 1) s : ℝ) : ℂ) * plEmb D v t, s) :: locBlocksFrom ρ v (a + s) bs

def locBlocks (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) : List (ℂ × ℕ) :=
  locBlocksFrom D ρ v 0 bs

theorem locBlocksFrom_snd (ρ : ℕ → ℕ → ℝ) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) :
    ∀ a, (locBlocksFrom D ρ v a bs).map Prod.snd = bs.map Prod.snd := by
  induction bs with
  | nil => intro a; rfl
  | cons b bs ih => intro a; obtain ⟨t, s⟩ := b; simp [locBlocksFrom, ih]

theorem locBlocksFrom_ok (ρ : ℕ → ℕ → ℝ) (hρ : ∀ i s, ρ i s ≠ 0) (v : D.what₂.Tau) (bs : List (D.host.E × ℕ)) :
    ∀ a, (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ p ∈ locBlocksFrom D ρ v a bs, p.1 ≠ 0 ∧ 1 ≤ p.2 := by
  induction bs with
  | nil => intro a _ p hp; simp [locBlocksFrom] at hp
  | cons b bs ih =>
    intro a h p hp
    obtain ⟨t, s⟩ := b
    simp only [locBlocksFrom, List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hb := h (t, s) (by simp)
      exact ⟨mul_ne_zero (by exact_mod_cast hρ (a + 1) s) ((map_ne_zero (plEmb D v)).2 hb.1), hb.2⟩
    · exact ih (a + s) (fun b hb => h b (by simp [hb])) p hp

def ptLocS (ρ : ℕ → ℕ → ℝ) (hρ : ∀ i s, ρ i s ≠ 0) (v : D.what₂.Tau) {i : ℕ} (γ : Point D.host.E i) : Point ℂ i :=
  ⟨locBlocks D ρ v γ.1, locBlocksFrom_ok D ρ hρ v γ.1 0 γ.2.1, by
    rw [locBlocks, locBlocksFrom_snd]; exact γ.2.2⟩

theorem rdE_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.rpow_pos_of_pos
  exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)

theorem rhoReal_ne (i s : ℕ) : rhoReal D i s ≠ 0 := zpow_ne_zero _ (rdE_pos D).ne'

theorem rhoReal_pos (i s : ℕ) : 0 < rhoReal D i s := zpow_pos (rdE_pos D) _

def ptWeightG (ρ : ℕ → ℕ → ℝ) (T T' : ℝ) (bs : List (D.host.E × ℕ)) : ℝ :=
  ∏ v, ptWeightFrom D.R.k D.R.rS T T' 0 (locBlocks D ρ v bs)

def ptSnoc {j : ℕ} (h : Point D.host.E j) (t : D.host.E) (ht : t ≠ 0) (s : ℕ) (hs : 1 ≤ s) :
    Point D.host.E (j + s) :=
  ⟨h.1 ++ [(t, s)], by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact h.2.1 b hb
      · rw [List.mem_singleton.1 hb]; exact ⟨ht, hs⟩
    · simp [h.2.2]⟩

def embInf : D.host.E →+ (D.what₂.Tau → ℂ) := (RingHom.pi fun v => plEmb D v).toAddMonoidHom

def cPsi (δ : D.host.E) (v : D.what₂.Tau) : ℂ := 4 * (Real.pi : ℂ) / plEmb D v δ

def kaV (δ : D.host.E) (v : D.what₂.Tau) : ℝ := 2 * Real.pi / ‖plEmb D v δ‖

def dualPsi (δ : D.host.E) (L : Submodule ℤ D.host.E) : Set D.host.E :=
  {l | ∀ c ∈ L, ∃ z : ℤ, Algebra.trace ℚ D.host.E (l * c / δ) = (z : ℚ)}

def FullLat (L : Submodule ℤ D.host.E) : Prop :=
  L.FG ∧ Submodule.span ℚ (L : Set D.host.E) = ⊤

def embInfS (c : ℝ) : D.host.E →+ (D.what₂.Tau → ℂ) :=
  { toFun := fun x v => ((c : ℝ) : ℂ) * plEmb D v x
    map_zero' := by funext v; simp
    map_add' := fun x y => by funext v; simp [mul_add] }

def IsCovol (κ c : ℝ) (L : Submodule ℤ D.host.E) : Prop :=
  ∃ F : Set (D.what₂.Tau → ℂ), MeasurableSet F ∧
    IsAddFundamentalDomain (L.toAddSubgroup.map (embInfS D c)) F volume ∧ volume F = ENNReal.ofReal κ

end S1bNum

section Kernels

def PSDK {α : Type*} (K : α → α → ℂ) : Prop :=
  ∀ (X : Finset α) (a : α → ℂ), 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * K p q * a q

end Kernels

section S1bData

variable (D : D7)

structure LocalDataRealPlace where
  lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ
  u : Fin D.R.k → ℝ
  u' : Fin D.R.k → ℝ
  l : Fin D.R.k
  a : ℝ
  b : ℝ
  a1 : ℝ
  b1 : ℝ

structure LatticeDataWithDual where
  La : ℕ → ℕ → Submodule ℤ D.host.E
  La' : ℕ → ℕ → Submodule ℤ D.host.E
  aaV : ℕ → ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E
  aaP : ℕ → ℕ → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E
  κ : ℝ
  ρ : ℕ → ℕ → ℝ

structure KernelData where
  K : (i : ℕ) → Point D.host.E i → Point D.host.E i → ℂ
  Th : (j s : ℕ) → D.host.E → Point D.host.E j → Point D.host.E j → ℂ
  e : ℕ → ℝ

def IsBlockSL2Embedding (i s : ℕ) : Prop := 1 ≤ i ∧ 1 ≤ s ∧ i - 1 + s ≤ D.R.rS + 1

def LatAx (δ : D.host.E) (L : LatticeDataWithDual D) : Prop :=
  0 < L.κ ∧ ∀ i s, IsBlockSL2Embedding D i s →
    0 < L.ρ i s ∧ FullLat D (L.La i s) ∧ FullLat D (L.La' i s) ∧ IsCovol D L.κ (L.ρ i s) (L.La i s) ∧
    dualPsi D δ (L.La i s) ⊆ (L.aaV i s : Set D.host.E) ∧ (L.La' i s : Set D.host.E) ⊆ (L.aaP i s : Set D.host.E)

def IsFrameScale (L : LatticeDataWithDual D) (ϱ : ℝ) : Prop :=
  0 < ϱ ∧ ∀ i s, IsBlockSL2Embedding D i s → L.ρ i s = ϱ ^ (-((((2 * D.R.rS + 3 : ℕ) : ℤ) - 2 * (i : ℤ) - (s : ℤ))))

end S1bData

section Sizes

variable (D : D7)

def supBe (ka T T' : ℝ) (x : LocalDataRealPlace D) (J : Set ℝ) : ℝ :=
  sSup ((beS ka D.R.rS x.lam T T' x.u x.u') '' J)

def xSz (C1 C2 N ka T T' : ℝ) (x : LocalDataRealPlace D) (i : ℕ) : ℝ :=
  C1 * supBe D ka T T' x (if i = 1 then Set.Icc x.a1 x.b1 else Set.Icc x.a x.b) *
    (C2 * ka * N / (x.b - x.a)) ^ (2 * i - 2)

def LamSz (C1 C2 N ka T T' : ℝ) (x : LocalDataRealPlace D) (i s : ℕ) : ℝ :=
  C1 * supBe D ka T T' x (Set.Icc x.a x.b) * (C2 * ka * N / (x.b - x.a)) ^ (2 * (i - 1) + s - 1)

def LamPSz (C1 C2 N ka T T' : ℝ) (x : LocalDataRealPlace D) (i : ℕ) : ℝ :=
  Real.sqrt (C1 * supBe D ka T T' x (Set.Icc x.a x.b) * ka ^ (2 * i - 1) * (T * T') ^ (-(1 / 2 : ℝ)) *
    (C2 * N / (x.b - x.a)) ^ (2 * (i - 1)))

def nrmHalf (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℝ :=
  Real.sqrt ((FractionalIdeal.absNorm aa : ℚ) : ℝ)

def ThInvF (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) : ℝ :=
  sSup ({y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS + 1 ∧
          y = (∏ v, xSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaV i 1)} ∪
        {y | ∃ i s, 1 ≤ i ∧ 2 ≤ s ∧ i - 1 + s ≤ D.R.rS + 1 ∧
          y = (∏ v, LamSz D C1 C2 N (kaV D δ v) T T' (x v) i s) /
            min (nrmHalf D (L.aaV i s)) (nrmHalf D (L.aaP i (s - 1)))} ∪
        {y | ∃ i, 1 ≤ i ∧ i ≤ D.R.rS ∧
          y = (∏ v, LamPSz D C1 C2 N (kaV D δ v) T T' (x v) i) / nrmHalf D (L.aaP i (D.R.rS + 2 - i))})

def ThS (C1 C2 N T T' : ℝ) (δ : D.host.E) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) : ℝ :=
  ThInvF D C1 C2 N T T' δ x L ^ (-(1 / (D.R.f : ℝ)))

end Sizes

section Rows

end Rows

end Formalism.MainNotions.S
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.QuantumDeterminants

abbrev PairSp (k r : ℕ) := (Mt k r × Mt k r) × (Mt k r × Mt k r)

section Orb

variable {k r : ℕ}

def besselIntg (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) : L.Wq →L[ℂ] L.Wp :=
  (psi k r L.z L.c (Matrix.of p.1.2) * star (psi k r L.z' L.c (Matrix.of p.2.2))) •
    ((L.π (Matrix.of p.1.1)).comp
      ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
        (L.π' (Matrix.of p.2.1)⁻¹)))

def pairMeas (L : LocBessel k r) : Measure (PairSp k r) := (L.μW.prod L.μN).prod (L.μW'.prod L.μN)

def RStab (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {a | a ∈ Nset k r ∧ g⁻¹ * a * g ∈ Nset k r}

def stabAct (g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p : PairSp k r) : PairSp k r :=
  ((p.1.1, fun i j => (a * Matrix.of p.1.2) i j), (p.2.1, fun i j => (g⁻¹ * a * g * Matrix.of p.2.2) i j))

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
  if hi : i.val < r then (a *ᵥ fvec k r z j) (eI k r ⟨i.val, hi⟩) else (if i = j then 1 else 0)

def blockIdx : List (ℂ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, p => if p < s then 0 else 1 + blockIdx bs (p - s)

def rootPat {r : ℕ} (γ : Point ℂ (r + 1)) : Finset (Fin (r + 1) × Fin (r + 1)) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ blockIdx γ.1 p.1.val = blockIdx γ.1 p.2.val

def rootCoords (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) (x : Mt k r) :
    (rootPat γ) → ℂ := fun p => flagMat k r z (Matrix.of x) p.1.1 p.1.2

def IsRootMeas (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) : Prop :=
  μR {x | Matrix.of x ∉ RStab k r g} = 0 ∧
    μR.map (rootCoords k r L.z γ) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card) • volume

def IsOrbQuot (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)) : Prop :=
  ∀ f : PairSp k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂(pairMeas L) = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν

def IsRelStab (L : LocBessel k r) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ a ∈ RStab k r g, psi k r L.z L.c a = psi k r L.z' L.c (g⁻¹ * a * g)

def OrbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : L.Wq →L[ℂ] L.Wp :=
  ∫ x, besselIntg L F g x ∂ν

def IsPtRep (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧ Zhat k r L.z L.z' g = ptMat γ

def ZhatO (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  fun a b => (-1 : ℂ) ^ (r - b.val) * Zhat k r z z' g a b

def IsPtRepO (L : LocBessel k r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧ ZhatO k r L.z L.z' g = ptMat γ

end Orb

def OrbRStabBig : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k → RStab k r (bigCell k r c μ) = {1}

end Formalism.MainNotions.S
end
end

