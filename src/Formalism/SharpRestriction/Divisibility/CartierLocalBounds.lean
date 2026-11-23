module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def rad1 (l i : ℕ) : ℝ := rho l + ((l : ℝ) ^ i)⁻¹ / 2

def rad2 (l : ℕ) : ℝ := rho l + 1 / 2

def dlt (l i : ℕ) : ℝ := ((l : ℝ) ^ i)⁻¹ / 8

def vLe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := (l : ℝ) ^ (-b) ≤ ‖x‖

def vGe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := ‖x‖ ≤ (l : ℝ) ^ (-b)

section Jets

variable {C : Type} [Field C]

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def dL {ι ι' : Type} [Fintype ι] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ c : ι, μ (Sum.inl c)

def dR {ι ι' : Type} [Fintype ι'] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ b : ι', μ (Sum.inr b)

end Jets

def WeightGe {l : ℕ} [Fact l.Prime] (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h1 : MvPowerSeries (ι ⊕ ι') ℂ_[l]) : Prop :=
  ∀ μ, vGe (MvPowerSeries.coeff μ h1)
    (1 / ((l : ℝ) - 1) - ((dL μ : ℝ) * (rad1 l i - dlt l i) + (dR μ : ℝ) * (rad2 l - dlt l i)))

def hP (l : ℕ) [Fact l.Prime] (i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) ℂ_[l]) :
    MvPowerSeries (PVar n0) ℂ_[l] :=
  -(((l : ℂ_[l]) ^ expE l i)⁻¹) • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

structure LocD (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] where

  five_le_l : 5 ≤ l

  d_even : Even d

  r : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  rh_le : rh ≤ j'

  rh_le_big : rh + j' ≤ r
  jj_le : j + j' ≤ r

  big : Fin 2 → ZMod d → Prop

  rk : Fin 2 → ZMod d → ℕ
  rk_big : ∀ g a, big g a → rk g a = r - j'
  rk_small : ∀ g a, ¬ big g a → rk g a = j'

  U : ∀ g a, Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])
  U_summand : ∀ g a, big g a → ∃ Q : Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l]), IsCompl (U g a) Q
  U_basis : ∀ g a, big g a → Nonempty (Module.Basis (Fin (r - j' - j)) 𝓞_ℂ_[l] (U g a))

  Chart : Type

  tan : Chart → ∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])

  chart_tan : ∀ b : (∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])),
    ∃ χ : Chart, tan χ = b

  alC : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk g a) → ℂ_[l]
  alC_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → alC χ g b c s a = 0

  alC_zero : ∀ χ g b c k, alC χ g b c 0 b k = ((tan χ g b c k : 𝓞_ℂ_[l]) : ℂ_[l])

  beP : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk (1 - g) a) → ℂ_[l]
  beP_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → beP χ g b c s a = 0

  beP_zero : ∀ χ g b c a, beP χ g b c 0 a = 0

  chart_mod : ∀ (χ : Chart)
    (x : ∀ g : Fin 2, ℕ → (Σ b : ZMod d, Fin (rk g b)) → (Σ b : ZMod d, Fin (rk g b)) → 𝓞_ℂ_[l]),
    (∀ g (s : ℕ) c b, b.1 ≠ c.1 + (s : ZMod d) → x g s c b = 0) →
    (∀ g, IsUnit (Matrix.of (x g 0)).det) →
    ∃ χ' : Chart,
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, alC χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * alC χ g b.1 b.2 (n - s) a k) ∧
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, beP χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * beP χ g b.1 b.2 (n - s) a k)

  tL : Chart → ∀ (g : Fin 2) (a : ZMod d), (Σ b : ZMod d, Fin (rk g b)) → MvPowerSeries (Fin (rk g a)) ℂ_[l]
  tL_const : ∀ χ g a x, MvPowerSeries.constantCoeff (tL χ g a x) = 0

  tL_log_same : ∀ χ g a (k : Fin (rk g a)) (μ : Fin (rk g a) →₀ ℕ),
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) =
      if μ = Finsupp.single k 1 then 1 else 0

  tL_log_other : ∀ χ g a a' (k : Fin (rk g a')) (μ : Fin (rk g a) →₀ ℕ), a' ≠ a →
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a' k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) = 0

  hL : ∀ (g : Fin 2) (a a' : ZMod d), MvPowerSeries (Fin (rk g a) ⊕ Fin (rk (1 - g) a')) ℂ_[l]

  Tt : Fin 2 → Type
  [instTt : ∀ g, AddCommGroup (Tt g)]
  [modTt : ∀ g, Module ℤ_[l] (Tt g)]
  Tt_free : ∀ g, Module.Free ℤ_[l] (Tt g)
  Tt_rank : ∀ g, Module.finrank ℤ_[l] (Tt g) = d * (r - rh)

  alHT : ∀ g, Tt g → ∀ a, (Fin (rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]

  chiG : Chart → ∀ g, Tt g → MvPowerSeries (Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l]

  chiG_leaf : ∀ χ g (t : Tt g) a,
    MvPowerSeries.subst (fun x => tL χ g a x)
        (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (chiG χ g t)) =
      mvExp (∑ k : Fin (rk g a), ((alHT g t a (Pi.single k 1) : 𝓞_ℂ_[l]) : ℂ_[l]) •
        (MvPowerSeries.X k : MvPowerSeries (Fin (rk g a)) ℂ_[l]))

  ev : Chart → ∀ N : ℕ,
    MvPolynomial (Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (rk g a)) 𝓞_ℂ_[l] →
    MvPowerSeries (Fin N × Σ g : Fin 2, Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l] → ℂ_[l]

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def nn : ℕ := Λ.r - Λ.j' - Λ.j

def mm : ℕ := Λ.j + Λ.j'

def Alternating : Prop := ∀ a : ZMod d, (Λ.big 0 a ↔ Even a.val) ∧ (Λ.big 1 a ↔ ¬ Even a.val)

def bg (_Λ : LocD l d) (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

abbrev CoG (g : Fin 2) := Σ b : ZMod d, Fin (Λ.rk g b)

def zeP (χ : Λ.Chart) (g : Fin 2) (a a' : ZMod d) (b : Fin (Λ.rk (1 - g) a')) :
    MvPowerSeries (Fin (Λ.rk g a)) ℂ_[l] :=
  fun μ => -(∑ s ∈ Finset.range (μ.degree + 1), ∑ x : Λ.CoG g, ∑ k : Fin (Λ.rk (1 - g) a'),
    ((Λ.tan χ (1 - g) a' b k : 𝓞_ℂ_[l]) : ℂ_[l]) * Λ.beP χ g x.1 x.2 s a' k *
      MvPowerSeries.coeff μ (Λ.tL χ g a x ^ (l ^ s)))

end LocD

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

abbrev LV (N : ℕ) := Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (Λ.rk g a)

abbrev CV (N : ℕ) := Fin N × Σ g : Fin 2, Λ.CoG g

def detBlock (N : ℕ) (a : ZMod d) (S : Fin Λ.nn ↪ Fin N)
    (bas : Fin Λ.nn → Fin (Λ.rk (Λ.bg a) a) → 𝓞_ℂ_[l]) : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l] :=
  Matrix.det (Matrix.of fun k c : Fin Λ.nn =>
    ∑ κ : Fin (Λ.rk (Λ.bg a) a), MvPolynomial.C (bas c κ) * MvPolynomial.X (S k, ⟨Λ.bg a, a, κ⟩))

def DetProd (N : ℕ) (W : ZMod d → ℕ) : Set (MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) :=
  {P | ∃ (B : ℕ) (blk : Fin B → ZMod d) (S : Fin B → (Fin Λ.nn ↪ Fin N)) (ex : Fin B → ℕ)
      (bas : ∀ a, Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U (Λ.bg a) a)),
    (∀ a, ∑ β ∈ Finset.univ.filter (fun β => blk β = a), ex β = W a) ∧
    (∀ β β', β ≠ β' → blk β = blk β' → Disjoint (Set.range (S β)) (Set.range (S β'))) ∧
    P = ∏ β, (Λ.detBlock N (blk β) (S β)
      (fun c => (bas (blk β) c : Fin (Λ.rk (Λ.bg (blk β)) (blk β)) → 𝓞_ℂ_[l]))) ^ (ex β)}

end LocD

def thl (l k : ℕ) : ℝ :=
  ((l : ℝ) ^ sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i})⁻¹

def addl (C : ℝ) (l k n d : ℕ) (l1 : ℝ) : ℝ :=
  if (l : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 2) then C * d * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then C * d * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def ContentAt (C : ℝ) : Prop :=
  Λ.Alternating → 0 < Λ.mm →
  ∀ (T Dp l1 : ℝ) (w : ZMod d → ℝ) (W : ZMod d → ℕ) (tha : ZMod d → ℝ),
    1 ≤ T → 1 ≤ Dp → Dp * ((Λ.nn : ℝ) + 1) / Λ.mm ≤ T → (Dp + 4) / T ≤ 1 / 2 →
    (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - tha a)) →
    (∀ a, 0 ≤ tha a ∧ tha a ≤ (Dp + 4) / T) →
    ((Λ.nn : ℝ) + 1) ^ ((3 : ℝ) / 2) < l1 → 2 * (Λ.nn : ℝ) + 2 < l1 →
    ∃ N : ℕ, (N : ℝ) ≤ C * Λ.r * d * (1 + ((Finset.univ.sup W : ℕ) : ℝ) / l1 ^ 2) ∧
      ∃ P ∈ Λ.DetProd N W, ∃ (χ : Λ.Chart) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
        vLe (Λ.ev χ N P g)
          ((lpF l d (fun a => (Λ.nn : ℝ) * w a) +
            C * Real.log ((Λ.nn : ℝ) + 1) * Λ.mm * (∑ a, w a) / l +
            C * ((Λ.nn : ℝ) + 1) * thl l (Λ.nn + 1) * (∑ a, w a) +
            T * addl C l (Λ.nn + 1) Λ.nn d l1) / T)

def CartierFrobeniusFormLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2), ∃ (c : ℕ → Λ.CoG g → Λ.CoG g → 𝓞_ℂ_[l])
      (c' : ℕ → Λ.CoG g → ∀ a : ZMod d, Fin (Λ.rk (1 - g) a) → 𝓞_ℂ_[l]),
    ∀ (x : Λ.CoG g) (i : ℕ) (a : ZMod d),
      (∀ k, (l : ℂ_[l]) * Λ.alC χ g x.1 x.2 (i + 1) a k =
        ∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.alC χ g y.1 y.2 (i - s) a k) ∧
      (∀ k, (l : ℂ_[l]) * Λ.beP χ g x.1 x.2 (i + 1) a k =
        (∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.beP χ g y.1 y.2 (i - s) a k) +
          ((c' i x a k : 𝓞_ℂ_[l]) : ℂ_[l]))

def GoodC (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) {N : ℕ} (e : Fin N ↪ Fin (Λ.rk g a)) : Prop :=
  ∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0

def RankOneLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a → Λ.big g (a + 2) →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk g (a + 2))), N ≤ N' + Λ.j' ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.alC χ g a (e (ρ s)) 2 (a + 2) (κ t)).det‖ = 1

end LocD

def PtCl (D : Formalism.BasicNotions.D7) (Y : ModuliIntegralCharts.Prov D) (w : Y.Dat) (l : ℕ) [Fact l.Prime] : Type :=
  Σ y : (Y.loc w l).Pt (Y.loc w l).YY,
    {e : ((Y.loc w l).fld y).C ≃+* ℂ_[l] // ∀ x, ‖e x‖ = ‖x‖}

structure Loc (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) where

  dat : ℕ → Y.Dat
  dat_rk : ∀ j, 1 ≤ j → j < D.R.m → Y.rk (dat j) = D.R.r
  dat_jj : ∀ j, 1 ≤ j → j < D.R.m → Y.jj (dat j) = D.R.k + j - 1

  Pt : D.jet.Sit → Type

  la : ∀ i, Pt i → X.PlP (D.jet.loc i).l

  ty : ∀ i, Pt i → ZMod (D.jet.loc i).d → DV.Emb D (D.jet.loc i).l
  ty_succ : ∀ i y a, ty i y (a + 1) = DV.phiPow D 1 (ty i y a)
  ty_inj : ∀ i y, Function.Injective (ty i y)

  ptE : ∀ i, D.jet.jOf i < D.R.m → Pt i ≃ PtCl D Y (dat (D.jet.jOf i)) (D.jet.loc i).l

  loc : ∀ i, Pt i → LocD (D.jet.loc i).l (D.jet.loc i).d

  loc_r : ∀ i y, (loc i y).r = D.R.r
  loc_j : ∀ i y, (loc i y).j = D.jet.jOf i
  loc_j' : ∀ i y, (loc i y).j' = D.R.m - D.jet.jOf i

  loc_big : ∀ i y a,
    ((loc i y).big 0 a ↔ ty i y a ∈ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y))) ∧
    ((loc i y).big 1 a ↔ ty i y a ∉ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y)))

  loc_alt : ∀ i y, (loc i y).Alternating

  loc_rh : ∀ i (h : D.jet.jOf i < D.R.m) (y : Pt i),
    Module.finrank ℤ ((Y.loc (dat (D.jet.jOf i)) (D.jet.loc i).l).Ylat (ptE i h y).1) =
      2 * D.R.f * (loc i y).rh

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

def adm1 : Prop := ∀ i y, (Lc.loc i y).CartierFrobeniusFormLocal ∧ (Lc.loc i y).RankOneLocalSpread

def Conclusion5 (C : ℝ) : Prop := ∀ i y, (Lc.loc i y).ContentAt C

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i))

end Family

end Formalism.MainNotions.CartierLocalBounds
