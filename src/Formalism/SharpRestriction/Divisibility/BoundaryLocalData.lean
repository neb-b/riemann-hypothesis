module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BoundaryLocalData

open Formalism.BasicNotions NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def vU (p : ℕ) {C : Type} [NormedField C] (u : Cˣ) : ℝ := -Real.logb p ‖(u : C)‖

theorem sqrtMinusD_sq (D : Formalism.BasicNotions.D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  exact D.host.sqd_sq

theorem half_one_add_sqrt_neg_isIntegral (D : Formalism.BasicNotions.D7) :
    IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2 : D.host.E) := by
  obtain ⟨-, -, -, hd, -⟩ := D.host.hyp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((4 * k + 2 : ℕ) : ℤ), ?_, ?_⟩
  · monicity!
  · have h := sqrtMinusD_sq D
    rw [hk] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    push_cast at h
    simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    have : ((1 + D.host.sqrtMinusD) / 2 : D.host.E) ^ 2 =
        (1 + 2 * D.host.sqrtMinusD + D.host.sqrtMinusD ^ 2) / 4 := by ring
    rw [this, h]
    ring

def w0 (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2, half_one_add_sqrt_neg_isIntegral D⟩

theorem conj_sqrtMinusD (D : Formalism.BasicNotions.D7) :
    D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have h := D.host.gal_sqd D.host.conj
  have h2 : D.host.gal D.host.conj = D.R.cc := D.host.gal.apply_symm_apply _
  rw [h2] at h
  simpa [Host.sqrtMinusD, Formalism.HC.Frame.cc, c0] using h

theorem one_sub_halfSqrt_eq_conj (D : Formalism.BasicNotions.D7) :
    ((1 - w0 D : 𝓞 D.host.E) : D.host.E) = D.host.conj (w0 D : D.host.E) := by
  have hw : algebraMap (𝓞 D.host.E) D.host.E (w0 D) = (1 + D.host.sqrtMinusD) / 2 := rfl
  change algebraMap (𝓞 D.host.E) D.host.E (1 - w0 D) =
    D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (w0 D))
  rw [map_sub, map_one, hw, map_div₀, map_add (f := _), map_one, conj_sqrtMinusD, map_ofNat]
  ring

structure LocB (D : Formalism.BasicNotions.D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) where

  chX : ∀ {Z : L.Mdl}, L.Pt Z → Type
  [xAdd : ∀ {Z : L.Mdl} (y : L.Pt Z), AddCommGroup (chX y)]
  [xMod : ∀ {Z : L.Mdl} (y : L.Pt Z), Module (𝓞 D.host.E) (chX y)]

  phi : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y ≃+ chX y

  phi_conj : ∀ {Z : L.Mdl} (y : L.Pt Z) (c c' : 𝓞 D.host.E),
    (c' : D.host.E) = D.host.conj (c : D.host.E) → ∀ a : L.Ylat y, phi y (c' • a) = c • phi y a

  tau : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → chX y → ((L.fld y).C)ˣ
  tau_add_left : ∀ {Z : L.Mdl} (y : L.Pt Z) a a' χ, tau y (a + a') χ = tau y a χ * tau y a' χ
  tau_add_right : ∀ {Z : L.Mdl} (y : L.Pt Z) a χ χ', tau y a (χ + χ') = tau y a χ * tau y a χ'
  tau_symm : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, tau y a (phi y b) = tau y b (phi y a)
  tau_smul : ∀ {Z : L.Mdl} (y : L.Pt Z) (c : 𝓞 D.host.E) a χ, tau y (c • a) χ = tau y a (c • χ)

  be_tau : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, L.be y a b = vU p (tau y a (phi y b))

  multiplicationLatticeFirst : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  multiplicationLatticeSecond : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  mulC : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → ((L.fld y).C)ˣ

  psiV_def : ∀ {Z : L.Mdl} (y : L.Pt Z) a, L.psiV y a = vU p (mulC y a (w0 D • a))

  StrictHenselianAcyclic : L.Unim → Type
  squareRootLineBundle : L.Unim → Type
  res2 : ∀ {La}, StrictHenselianAcyclic La → squareRootLineBundle La

  PoiQ : ∀ La, squareRootLineBundle La

  biext : ∀ {La}, StrictHenselianAcyclic La → Prop

  dg : ∀ {La}, StrictHenselianAcyclic La → L.LBG La
  dgq : ∀ {La}, squareRootLineBundle La → L.LBGq La
  dg_res : ∀ {La} (P : StrictHenselianAcyclic La), L.resQ (dg P) = dgq (res2 P)

  PPq_def : ∀ La, L.PPq La = dgq (PoiQ La)

  BPt : Type

  Rl : BPt → Type
  [iRr : ∀ z, CommRing (Rl z)]
  [iRd : ∀ z, IsDomain (Rl z)]
  [iRl : ∀ z, IsLocalRing (Rl z)]
  [iRn : ∀ z, IsNoetherianRing (Rl z)]
  [iRi : ∀ z, IsIntegrallyClosed (Rl z)]
  [iRc : ∀ z, IsAdicComplete (IsLocalRing.maximalIdeal (Rl z)) (Rl z)]

  Yb : BPt → Type
  [iYa : ∀ z, AddCommGroup (Yb z)]
  [iYm : ∀ z, Module (𝓞 D.host.E) (Yb z)]
  Xb : BPt → Type
  [iXa : ∀ z, AddCommGroup (Xb z)]
  [iXm : ∀ z, Module (𝓞 D.host.E) (Xb z)]
  phib : ∀ z, Yb z ≃+ Xb z
  phib_conj : ∀ z (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a : Yb z, phib z (c' • a) = c • phib z a
  taub : ∀ z, Yb z → Xb z → (FractionRing (Rl z))ˣ
  taub_add_left : ∀ z a a' χ, taub z (a + a') χ = taub z a χ * taub z a' χ
  taub_add_right : ∀ z a χ χ', taub z a (χ + χ') = taub z a χ * taub z a χ'
  taub_symm : ∀ z a b, taub z a (phib z b) = taub z b (phib z a)
  taub_smul : ∀ z (c : 𝓞 D.host.E) a χ, taub z (c • a) χ = taub z a (c • χ)

  taub_pos : ∀ z a, ((taub z a (phib z a) : (FractionRing (Rl z))ˣ) : FractionRing (Rl z)) ∈
    (algebraMap (Rl z) (FractionRing (Rl z))).range

  Sg : BPt → Type
  [iSg : ∀ z, AddCommGroup (Sg z)]
  [iSk : ∀ z, Module (FractionRing (Rl z)) (Sg z)]
  [iSm : ∀ z, Module (Rl z) (Sg z)]
  [iSt : ∀ z, IsScalarTower (Rl z) (FractionRing (Rl z)) (Sg z)]

  Sreg : ∀ z, Submodule (Rl z) (Sg z)

  fc : ∀ z, Sg z →ₗ[FractionRing (Rl z)] (Xb z → FractionRing (Rl z))

  trU : ∀ z, Yb z → Xb z → (Rl z)ˣ

  oX : L.Sh L.Xm
  oX_inv : L.IsInv oX

  secOf : ∀ {F : L.Sh L.Xm}, L.GIso oX F → L.Sec F

  nrm_secOf : ∀ {F : L.Sh L.Xm} (φ : L.GIso oX F) y, L.nrm F (secOf φ) y = (p : ℝ) ^ (-(L.vrat φ y))

  keySh_inv : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)

  dimB : L.Pt L.Xm → ℕ
  dimB_add : ∀ y, dimB y + L.dP y = D.R.f * r

  FB : ∀ (y : L.Pt L.Xm) (nW n : ℕ), (Fin nW → chX y) → Type
  [fbAdd : ∀ y nW n χ, AddCommGroup (FB y nW n χ)]
  [fbMod : ∀ y nW n χ, Module (L.fld y).C (FB y nW n χ)]

  nB : ∀ {y nW n χ}, FB y nW n χ → ℝ

  sgc : ∀ y nW n χ, L.Sn y (L.latStd nW) n →ₗ[(L.fld y).C] FB y nW n χ

  trB : ∀ y nW n (a : Fin nW → L.Ylat y) χ,
    FB y nW n χ ≃ₗ[(L.fld y).C] FB y nW n (χ + n • fun i => phi y (a i))
  trB_norm : ∀ y nW n a χ σ, nB (trB y nW n a χ σ) = nB σ

  alp : ℕ → 𝓞 D.host.E
  alp_spec : ∀ n, ModuliIntegralCharts.NHyp D p n →
    (alp n : D.host.E) * D.host.conj (alp n : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ alp n = (mm : 𝓞 D.host.E)) ∨ (alp n : D.host.E) ∈ D.host.K)

  th1 : ∀ y nW, L.Sn y (L.latStd nW) 1
  pbAl : ∀ y nW n, L.Sn y (L.latStd nW) 1 →ₗ[(L.fld y).C] L.Sn y (L.latStd nW) n
  vth_def : ∀ y nW n, ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = pbAl y nW n (th1 y nW)

  jX : ∀ y nW n DF χ, FB y nW n χ →ₗ[(L.fld y).C] L.Jet y (L.latStd nW) n DF

  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (L.fld y).C (L.Jet y (L.latStd nW) n DF)),
    ∀ v, v ∈ L.intJet y (L.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1

  jX_int : ∀ y nW n DF χ (σ : FB y nW n χ), nB σ ≤ 1 → jX y nW n DF χ σ ∈ L.intJet y (L.latStd nW) n DF

  jet_fourier : ∀ y nW n DF (s : L.Sn y (L.latStd nW) n) (t : (L.fld y).C), t ≠ 0 →
    ∃ F₀ : Finset (Fin nW → chX y), ∀ F : Finset (Fin nW → chX y), F₀ ⊆ F →
      ∃ v ∈ L.intJet y (L.latStd nW) n DF,
        L.jet y (L.latStd nW) n DF s - ∑ χ ∈ F, jX y nW n DF χ (sgc y nW n χ s) = t • v

attribute [instance] LocB.xAdd LocB.xMod LocB.iRr LocB.iRd LocB.iRl LocB.iRn LocB.iRi LocB.iYa LocB.iYm
  LocB.iXa LocB.iXm LocB.iSg LocB.iSk LocB.iSm LocB.iSt LocB.fbAdd LocB.fbMod

structure Prov (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) where
  loc : ∀ w p, p.Prime → LocB D (X.loc w p)

namespace LocB

variable {D : Formalism.BasicNotions.D7} {r j p : ℕ} {L : ModuliIntegralCharts.Loc D r j p} (B : LocB D L)

variable {y : L.Pt L.Xm} {nW : ℕ}

variable (y nW)

end LocB

variable (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

abbrev BaseObjectsAlongFamily : Type 1 := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ModuliIntegralCharts.Prov (Fm.D x i)

abbrev ProvF (XF : BaseObjectsAlongFamily Fm) : Type 1 := ∀ x hx (i : Fm.Ix x), Prov (Fm.D x i) (XF x hx i)

variable (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF)

end Family

end Formalism.MainNotions.BoundaryLocalData
