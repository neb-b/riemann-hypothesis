module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

structure Ch (D : D7) (u : D.what₂.Word) where
  C : ColumnChain D.R D.what₂.Tau (D.hcW u)
  A : ColumnsAtT D.R C
  P : PeriodMap D.R C
  fm : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P

abbrev own (D : D7) (u : D.what₂.Word) : Ch D u := ⟨(D.mem u).C, (D.mem u).A, (D.mem u).P, D.fm u⟩

abbrev tw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Ch D u :=
  ⟨D.chTw u μ, Tw.A u μ, D.PTw u μ, Tw.fm u μ⟩

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

def duX : ℕ := haveI := X.A.Mu0_fd; Module.finrank ℂ X.A.Mu0

def TauWeight (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

abbrev Fn (i : ℕ) : Type := X.C.cls i → X.C.Y i → ℂ

abbrev Vl (i : ℕ) : Type := (X.fm.lat i).V

instance lvModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Module.Finite (X.A.Fv v) (X.fm.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lv_rank]; exact D.R.N_pos i)

instance lvFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Fintype (X.fm.lv i v c) :=
  haveI : Finite (X.fm.lv i v c) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def Uop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1),
    (X.fm.upT i v c x).toLinearMap ∘ₗ LinearMap.proj (X.fm.up i v c x)

def VVT (w : D.what₂.places.Pl) : Finset X.A.vT :=
  if X.fm.seenP w then Finset.univ.filter (fun v => X.fm.tauOf w v ∈ topsOf D.host D.eTau) else ∅

def Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn X i →ₗ[ℂ] Fn X i :=
  (VVT X w).toList.foldr (fun v g => (Uop X i v).comp g) LinearMap.id

def imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i →ₗ[ℂ] Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) : Submodule (Ow D w) (Vl X j) where
  carrier := {y | ∃ x ∈ A, X.fm.emb j y = f (X.fm.emb i x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro r a ⟨x, hx, h1⟩
    refine ⟨r • x, A.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  X.fm.S 0 w ⊓ X.fm.ramSub.restrictScalars (Ow D w)

def expT (w : D.what₂.places.Pl) : ℤ :=
  (D.R.m : ℤ) * ∑ v ∈ VVT X w, X.fm.bTop (X.fm.tauOf w v)

def Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  imgL X w (((X.A.T : ℂ) ^ expT X w) • (Uprod X 0 w) ^ D.R.m) (Sram X w)

def OverT (w : D.what₂.places.Pl) : Prop := D.what₂.places.resChar w = X.A.T

def tpow (n : ℕ) : ℂ := (X.A.T : ℂ) ^ n

instance lkModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Module.Finite (X.A.Fv v) (X.fm.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lk_rank]; exact D.R.N_pos i)

instance lkDualFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Fintype (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) :=
  haveI : Finite (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def Dop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (X.A.Fv v) (X.fm.lk i v c) => g (X.fm.te i v c) = 1),
    (X.fm.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (X.fm.dn i v c g)

def Eop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (X.A.Fv v) (X.fm.lk i v c) => g ≠ 0),
    (X.fm.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (X.fm.dn i v c g)

def dia (i : ℕ) (v : X.A.vT) (a : (X.A.Fv v)ˣ) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => (X.fm.dilT i v a c).toLinearMap ∘ₗ LinearMap.proj (X.fm.dil i v a c)

def Nm (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i := ∑ a : (X.A.Fv v)ˣ, dia X i v a

def trp (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  ((X.A.T : ℂ) ^ (D.R.N i - 1))⁻¹ • (Eop X i v ∘ₗ Uop X i v)

theorem dia_zero (v : X.A.vT) (a : (X.A.Fv v)ˣ) : dia X 0 v a = X.A.rhoT v a := by
  apply LinearMap.ext; intro φ; funext c
  rw [X.fm.rhoT_dil v a φ c]; rfl

theorem Nm_zero (v : X.A.vT) : Nm X 0 v = X.A.Nm v := by
  unfold Nm ColumnsAtT.Nm; exact Finset.sum_congr rfl (fun a _ => dia_zero X v a)

def MramI (i : ℕ) : Submodule ℂ (Fn X i) := X.fm.Fi i ⊓ ⨅ v, LinearMap.ker (Nm X i v)

theorem MramI_zero : MramI X 0 = X.A.Mram := by
  unfold MramI ColumnsAtT.Mram; rw [X.fm.Fi_zero]; simp only [Nm_zero]

def KT (i : ℕ) : Fn X i →ₗ[ℂ] Fn X (i + 1) := X.C.Klin i

def colT : Fn X 0 → Fn X D.R.m := X.C.col

abbrev Wt (τ : D.what₂.Tau) : ℕ := TauWeight X τ

def Into {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i → Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) (B : Submodule (Ow D w) (Vl X j)) : Prop :=
  ∀ x ∈ A, ∃ y ∈ B, X.fm.emb j y = f (X.fm.emb i x)

def len {i : ℕ} (w : D.what₂.places.Pl) (A B : Submodule (Ow D w) (Vl X i)) : ℕ∞ :=
  Module.length (Ow D w) (A ⧸ B.comap A.subtype)

def tL {i : ℕ} (w : D.what₂.places.Pl) (n : ℤ) (A : Submodule (Ow D w) (Vl X i)) :
    Submodule (Ow D w) (Vl X i) :=
  imgL X w (((X.A.T : ℂ) ^ n) • LinearMap.id) A

def Conclusion2 : Prop :=
  (X.A.du : ℚ) = (duX X : ℚ) * (1 - 1 / ((X.A.T : ℚ) - 1)) ^ D.R.f ∧
  X.fm.ramLat.mu = (X.fm.lat 0).mu -
    (D.R.f : ℝ) * Real.log ((X.A.T : ℝ) - 1) / ((X.A.T : ℝ) - 2) ∧
  X.fm.ramLat.muMax ≤ (X.fm.lat 0).muMax ∧
  (∀ w, OverT X w → X.fm.seenP w = true → ∀ v,
    (0 ≤ (X.fm.lam 0 (X.fm.tauOf w v)).detShift →
      X.fm.S 0 w ≤ X.fm.Bw 0 w v ∧
      (∃ n : ℕ, len X w (X.fm.Bw 0 w v) (X.fm.S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((duX X : ℚ) * (wsum (X.fm.lam 0 (X.fm.tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
      len X w (Sram X w) (imgL X w (Uop X 0 v) (Sram X w)) ≤
        len X w (X.fm.Bw 0 w v) (X.fm.S 0 w) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * duX X) : ℕ) : ℕ∞) +
          len X w (imgL X w (Uop X 0 v) (Sram X w)) (Sram X w)) ∧
    (0 ≤ X.fm.bTop (X.fm.tauOf w v) →
      tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w) ≤ X.fm.Bw 0 w v ∧
      (∃ n : ℕ, len X w (X.fm.Bw 0 w v) (tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((duX X : ℚ) *
          ((wsum (X.fm.lam 0 (X.fm.tauOf w v)) : ℚ) + (D.R.k : ℚ) * (X.fm.bTop (X.fm.tauOf w v) : ℚ)) /
            (D.R.k : ℚ))) ∧
      len X w (Sram X w)
          (imgL X w (((X.A.T : ℂ) ^ X.fm.bTop (X.fm.tauOf w v)) • Uop X 0 v) (Sram X w)) ≤
        len X w (X.fm.Bw 0 w v) (tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w)) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * duX X) : ℕ) : ℕ∞) +
          len X w (imgL X w (((X.A.T : ℂ) ^ X.fm.bTop (X.fm.tauOf w v)) • Uop X 0 v) (Sram X w))
            (Sram X w)))

def IsBfam (i : ℕ) (w : D.what₂.places.Pl)
    (BV : Finset X.A.vT → Submodule (Ow D w) (Vl X i)) : Prop :=
  BV ∅ = X.fm.S i w ∧ (∀ v, BV {v} = X.fm.Bw i w v) ∧
  (∀ V v, v ∈ V → Into X w (Uop X i v) (BV V) (BV (V.erase v)) ∧
    Into X w (Dop X i v) (BV (V.erase v)) (BV V)) ∧
  (∀ V v, v ∈ V → X.fm.tauOf w v ∉ tops D →
    Into X w (fun φ => tpow X (2 * Wt X (X.fm.tauOf w v) + D.R.t) • φ) (BV V) (BV (V.erase v)))

def lossK (C : ℝ) : ℕ := ⌊∑ τ, (2 * (Wt X τ : ℝ) + C * D.R.N D.R.m)⌋₊

def PointsLemma (C : ℝ) : Prop :=
  ∀ w, OverT X w →
    (∀ i, i < D.R.m →
      (X.fm.seenP w = false →
        Into X w (fun φ => tpow X (lossK X C) • KT X i φ) (X.fm.S i w) (X.fm.S (i + 1) w)) ∧
      (X.fm.seenP w = true → ∃ BV, IsBfam X (i + 1) w BV ∧
        Into X w (fun φ => tpow X (lossK X C) • KT X i φ) (X.fm.S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt X τ : ℝ) + C * D.R.f * D.R.N D.R.m ∧
        Into X w (fun φ => tpow X e1 • Uprod X (i + 1) w (KT X i φ))
          (X.fm.S i w) (X.fm.S (i + 1) w))) ∧
    (∀ i, i ≤ D.R.m → X.fm.seenP w = true → ∀ v, X.fm.tauOf w v ∉ tops D →
      Into X w (fun φ => tpow X (2 * Wt X (X.fm.tauOf w v) + D.R.t) • φ) (X.fm.Bw i w v) (X.fm.S i w))

def LevelChainUOperatorCommutation : Prop :=
  ∀ i, i < D.R.m → ∀ v : X.A.vT, ∀ φ ∈ X.fm.Fi i,
    Uop X (i + 1) v (KT X i φ) =
      ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • KT X i (Uop X i v φ)

def ETpi : ℝ :=
  2 * ∑ τ, (Wt X τ : ℝ) + (D.R.f : ℝ) * D.R.N D.R.m +
    ((tops D).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

def ET (w : D.what₂.places.Pl) : ℝ := if X.fm.seenP w then ETpi X else 0

def Conclusion5Sharp : Prop :=
  ∀ w, OverT X w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET X w) ≤ (n : ℝ) →
    Into X w (fun φ => D.what₂.embLL c • colT X φ) (Nlam X w) (X.fm.S D.R.m w)

def Pt : Fn X D.R.m →ₗ[ℂ] X.P.Wrow := X.P.lowerMap ∘ₗ X.P.evz

def lamTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m) := wSh (X.fm.lam D.R.m τ) (cTw D.R)

def sgTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m - 1) := wSh (X.fm.sg τ) (cTw D.R)

def sqrtT : ℂˣ := Units.mk0 ((Real.sqrt (X.A.T : ℝ) : ℝ) : ℂ) (by
  have h : 0 < (X.A.T : ℝ) := by exact_mod_cast X.A.T_prime.pos
  exact_mod_cast (Real.sqrt_pos.mpr h).ne')

def gFull (g : GL (Fin (D.R.N D.R.m - 1)) ℂ) : GL (Fin (D.R.N D.R.m)) ℂ :=
  Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ (sqrtT X)

def opNorm (τ : D.what₂.Tau) (b : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) : ℝ :=
  sSup ((fun f => Real.sqrt ((normFock (X.fm.sg τ) (b f) (b f)).re /
      (normFock (X.fm.lam D.R.m τ) f f).re)) '' {f | f ∈ delSq ℂ _ (X.fm.lam D.R.m τ) ∧ f ≠ 0})

def TupleChainSharpColumnValuation (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, Formalism.MainNotions.product_first_zeroth_parts.OverT D u w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ (n : ℝ) →
    ∀ x ∈ LT.Nlam D u w, ∃ y ∈ (Tw.fm u μ).S D.R.m w,
      (Tw.fm u μ).emb D.R.m y = D.what₂.embLL c • (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

section Indep

variable (Y : Ch D u)

end Indep

theorem emb_mem_Fi (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

def Ulist (l : List X.A.vT) : Fn X 0 →ₗ[ℂ] Fn X 0 := l.foldr (fun v g => (Uop X 0 v).comp g) LinearMap.id

variable {X}

structure SharedBy (X Y : Ch D u) (e : Fn X 0 ≃ₗ[ℂ] Fn Y 0) (eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0)
    (ev : X.A.vT ≃ Y.A.vT) (eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)) : Prop where
  T_eq : Y.A.T = X.A.T
  emb_eq : ∀ x, Y.fm.emb 0 (eL x) = e (X.fm.emb 0 x)
  lat_iff : ∀ x, x ∈ (X.fm.lat 0).L ↔ eL x ∈ (Y.fm.lat 0).L
  ip_eq : ∀ φ ∈ X.fm.Fi 0, ∀ ψ ∈ X.fm.Fi 0, Y.fm.ipC 0 (e φ) (e ψ) = X.fm.ipC 0 φ ψ
  psi_eq : ∀ v a, Y.A.psiT (ev v) (eF v a) = X.A.psiT v a
  seen_eq : ∀ w, OverT X w → Y.fm.seenP w = X.fm.seenP w
  tau_eq : ∀ w, OverT X w → ∀ v, Y.fm.tauOf w (ev v) = X.fm.tauOf w v
  B_iff : ∀ w, OverT X w → X.fm.seenP w = true → ∀ v x, x ∈ X.fm.Bw 0 w v ↔ eL x ∈ Y.fm.Bw 0 w (ev v)
  U_eq : ∀ v, ∀ φ ∈ X.fm.Fi 0, e (Uop X 0 v φ) = Uop Y 0 (ev v) (e φ)
  D_eq : ∀ v, ∀ φ ∈ X.fm.Fi 0, e (Dop X 0 v φ) = Dop Y 0 (ev v) (e φ)
  dia_eq : ∀ v (a : (X.A.Fv v)ˣ), ∀ φ ∈ X.fm.Fi 0,
    e (dia X 0 v a φ) = dia Y 0 (ev v) (Units.map (eF v : X.A.Fv v →* Y.A.Fv (ev v)) a) (e φ)

def Shared (X Y : Ch D u) (e : Fn X 0 ≃ₗ[ℂ] Fn Y 0) (eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0) : Prop :=
  ∃ (ev : X.A.vT ≃ Y.A.vT) (eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)), SharedBy X Y e eL ev eF

namespace SharedBy

variable {Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}
  {ev : X.A.vT ≃ Y.A.vT} {eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)} (h : SharedBy X Y e eL ev eF)
include h

end SharedBy

section Reformulated

variable (D u)

theorem levelChainSharpColumnValuation_ownChain_iff : Conclusion5Sharp (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u := Iff.rfl

end Reformulated

end GlobalTheory.LvT
