module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

structure PtGeo (l : ℕ) [Fact l.Prime] (Λ : Type) [AddCommGroup Λ] (σ : Type) where

  BB : Type
  [acgBB : AddCommGroup BB]
  tor_fin : ∀ N : ℕ, N ≠ 0 → Finite {z : BB // N • z = 0}

  Sec : ℕ → Type
  [acgSec : ∀ k, AddCommGroup (Sec k)]
  [modSec : ∀ k, Module ℂ_[l] (Sec k)]
  s : Sec 1

  nrm : ∀ k, Sec k → BB → ℝ
  nrm_nonneg : ∀ k F x, 0 ≤ nrm k F x
  nrm_smul : ∀ k (c : ℂ_[l]) F x, nrm k (c • F) x = ‖c‖ * nrm k F x
  nrm_add : ∀ k F F' x, nrm k (F + F') x ≤ max (nrm k F x) (nrm k F' x)

  pull : ∀ N : ℕ, Sec 1 →ₗ[ℂ_[l]] Sec (N ^ 2)
  pull_isom : ∀ N : ℕ, N ≠ 0 → ∀ F x, nrm (N ^ 2) (pull N F) x = nrm 1 F (N • x)

  Up : ∀ N : ℕ, BB → (Sec (N ^ 2) ≃ₗ[ℂ_[l]] Sec (N ^ 2))
  Up_fin : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ m : ℕ, m ≠ 0 ∧ (Up N z) ^ m = 1

  Up_cube : ∀ (N : ℕ) (z : BB), (N ^ 2) • z = 0 → ∃ ph : BB → ℝ,
    (∀ F x, nrm (N ^ 2) (Up N z F) x = Real.exp (ph x) * nrm (N ^ 2) F (x + z)) ∧
    (∃ C, ∀ x, |ph x| ≤ C) ∧
    ∃ c, ∀ x x' x'', ph (x + x' + x'') - ph (x + x') - ph (x + x'') - ph (x' + x'') + ph x + ph x' + ph x''
      - ph 0 = c

  Gt : Type
  [acgGt : AddCommGroup Gt]
  Y : Type
  [acgY : AddCommGroup Y]
  per : Y →+ Gt
  unif : Gt →+ BB

  YR : Type
  [acgYR : AddCommGroup YR]
  [modYR : Module ℝ YR]
  iY : Y →+ YR
  Bf : YR →ₗ[ℝ] YR →ₗ[ℝ] ℝ
  w0 : YR →ₗ[ℝ] YR
  w0b : YR →ₗ[ℝ] YR

  chr : Y → Gt → ℂ_[l]
  cst : Y → ℂ_[l]
  trop : Gt →+ YR

  SecM : Type
  [acgSecM : AddCommGroup SecM]
  [modSecM : Module ℂ_[l] SecM]
  nrmM : SecM → Gt → ℝ
  nrmM_smul : ∀ (c : ℂ_[l]) F g, nrmM (c • F) g = ‖c‖ * nrmM F g
  nrmM_add : ∀ F F' g, nrmM (F + F') g ≤ max (nrmM F g) (nrmM F' g)
  up : Sec 1 →ₗ[ℂ_[l]] SecM
  be : SecM
  trY : Y → SecM →ₗ[ℂ_[l]] SecM

  Co : Type
  [finCo : Fintype Co]
  ser : ∀ k, Sec k →ₗ[ℂ_[l]] MvPowerSeries Co ℂ_[l]

  H : Type
  [acgH : AddCommGroup H]
  [modH : Module ℂ_[l] H]
  HO : AddSubgroup H
  HO_smul : ∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∀ h ∈ HO, c • h ∈ HO
  Fil : Submodule ℂ_[l] H
  curv : H →ₗ[ℂ_[l]] H →ₗ[ℂ_[l]] ℂ_[l]

  Gm : ℕ → Type
  [acgGm : ∀ k, AddCommGroup (Gm k)]
  [modGm : ∀ k, Module ℂ_[l] (Gm k)]
  germ : ∀ k, Sec k →ₗ[ℂ_[l]] Gm k
  pullG : ∀ N : ℕ, Gm 1 →ₗ[ℂ_[l]] Gm (N ^ 2)
  pullG_germ : ∀ N F, pullG N (germ 1 F) = germ (N ^ 2) (pull N F)
  pullG_inj : ∀ N : ℕ, N ≠ 0 → Function.Injective (pullG N)
  ev0 : ∀ k, Gm k →ₗ[ℂ_[l]] ℂ_[l]
  ev_zero_pull_square : ∀ N G, ev0 (N ^ 2) (pullG N G) = ev0 1 G
  IntG : ∀ k, AddSubgroup (Gm k)
  IntG_smul : ∀ k (c : ℂ_[l]), ‖c‖ ≤ 1 → ∀ G ∈ IntG k, c • G ∈ IntG k
  integral_ev_zero_norm_le_one : ∀ k, ∀ G ∈ IntG k, ‖ev0 k G‖ ≤ 1
  IntG_iff : ∀ k F, germ k F ∈ IntG k ↔ ∀ m, ‖MvPowerSeries.coeff m (ser k F)‖ ≤ 1

  nab : ∀ k, H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm k)
  nabD : H →ₗ[ℂ_[l]] Module.End ℂ_[l] (Gm 1)

  EL : Set (σ → H)
  lf : σ → H
  lf_mem : lf ∈ EL

  half : ℕ → BB → BB
  half_spec : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 → N • half N z = z
  Uz : ℕ → BB → Gm 1
  Uz_def : ∀ N : ℕ, N ≠ 0 → ∀ z : BB, N • z = 0 →
    pullG N (Uz N z) = germ (N ^ 2) (Up N (half N z) (pull N s))

  kr : ℕ → Λ → BB → ℂ_[l]
  kr_per : ∀ (N : ℕ) x w z, kr N (x + N • w) z = kr N x z
  kr_int : ∀ N x z, ‖kr N x z‖ ≤ 1

  key : ℂ_[l]
  key_ne : key ≠ 0

attribute [instance] PtGeo.acgBB PtGeo.acgSec PtGeo.modSec PtGeo.acgGt PtGeo.acgY PtGeo.acgYR PtGeo.modYR
  PtGeo.acgSecM PtGeo.modSecM PtGeo.finCo PtGeo.acgH PtGeo.modH PtGeo.acgGm PtGeo.modGm

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

def mon {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (m : σ →₀ ℕ) : Module.End ℂ_[l] (X.Gm k) :=
  (ord.map fun u => (Dl (L u)) ^ (m u)).prod

def PN {k : ℕ} (ord : List σ) (Dl : X.H →ₗ[ℂ_[l]] Module.End ℂ_[l] (X.Gm k)) (L : σ → X.H)
    (P : MvPolynomial σ ℂ_[l]) (g : X.Gm k) : ℂ_[l] :=
  ∑ m ∈ P.support, P.coeff m * X.ev0 k (X.mon ord Dl L m g)

def hat (N e : ℕ) (φ : Λ → ℂ_[l]) (z : X.BB) : ℂ_[l] :=
  ((N : ℂ_[l]) ^ e)⁻¹ * ∑ᶠ c : Λ ⧸ (nsmulAddMonoidHom (α := Λ) N).range,
    φ (Quotient.out c) * X.kr N (Quotient.out c) z

def fG (N e : ℕ) (φ : Λ → ℂ_[l]) : X.Gm 1 :=
  ∑ᶠ z : {z : X.BB // N • z = 0}, X.hat N e φ z.1 • X.Uz N z.1

end PtGeo

variable (D : Formalism.BasicNotions.D7)

def Per {L V : Type} [AddCommGroup L] (n : ℕ) (φ : L → V) : Prop :=
  ∀ x z : L, φ (x + (n : ℤ) • z) = φ x

def PerI {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]
    (I : Ideal (𝓞 E)) (φ : L → V) : Prop :=
  ∀ x : L, ∀ y ∈ I • (⊤ : Submodule (𝓞 E) L), φ (x + y) = φ x

def ConjPl (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) → (x ∈ P.asIdeal ↔ y ∈ P'.asIdeal)

def VacOff {L V : Type} [AddCommGroup L] [Module (𝓞 D.host.E) L] (φ : L → V) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), ¬ IsSplitPl D.host w →
    ∃ I : Ideal (𝓞 D.host.E), IsCoprime I w.asIdeal ∧ PerI I φ

def SplitLev (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    IsSplitPl D.host w


open scoped Classical in
def vdd (l : ℕ) : ℝ :=
  ⨆ v : placesOver D.host.E l,
    ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ (𝓞 D.host.E))).count
        (v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal : ℝ) /
      ((v : HeightOneSpectrum (𝓞 D.host.E)).asIdeal.ramificationIdx ℤ : ℝ)

variable {D}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

def iO (i : D.ntw.Tw) : D.ntw.O i →+* ℂ_[D.ntw.l i] :=
  (D.nth.iC i).comp (algebraMap (D.ntw.O i) (KK i))

def GalF (i : D.ntw.Tw) (F : Subfield (KK i)) : Set (RingAut ℂ_[D.ntw.l i]) :=
  {s | (∀ x, ‖s x‖ = ‖x‖) ∧ ∀ x ∈ F, s (D.nth.iC i x) = D.nth.iC i x}


variable (D) in
structure Geo where

  pt : ∀ i j (_ : D.nth.Pt i j), PtGeo (D.ntw.l i) (D.nth.Lt i j) (D.nth.Let i j)

  ord : ∀ i j, List (D.nth.Let i j)
  ord_nodup : ∀ i j, (ord i j).Nodup
  ord_mem : ∀ i j u, u ∈ ord i j

  thV_def : ∀ i j (φ : D.nth.Lt i j → KK i) (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i))
    (y : D.nth.Pt i j) (n : ℕ), Odd n → Nat.Coprime n (D.ntw.l i) → SplitLev D n →
    Per (D.ntw.l i ^ D.nth.aL i * n) φ →
    D.nth.thV i j φ P y = (pt i j y).key * (pt i j y).PN (ord i j) (pt i j y).nabD (pt i j y).lf
      (P.map (iO i)) ((pt i j y).fG (D.ntw.l i ^ D.nth.aL i * n) (2 * D.R.f * D.R.r * D.R.nV)
        (fun x => D.nth.iC i (φ x)))

  det_actK : ∀ i j P P', ConjPl D P P' → ∀ (k : D.nth.Kq i j P) (y : D.nth.Pt i j) {A : Type} [CommGroup A]
    (χ : G D.host.E D.nd.Om →* A), IsOpen (χ.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc χ →
    (∀ v, v = P ∨ v = P' → ∀ B : ValuationSubring D.nd.Om, IsPlaceOver B v →
      ∀ σ ∈ Ine (F := D.host.E) B, χ σ = 1) →
    χ (D.nth.recDet i j (D.nth.actK i j P k y)) = χ (D.nth.recDet i j y)

  Ks : ∀ i : D.ntw.Tw, Subfield (KK i)
  Ks_le : ∀ i, Ks i ≤ D.nth.MaximalUnramifiedExtension i
  Ks_E : ∀ i (τ : D.host.E →+* ℂ_[D.ntw.l i]) (x : D.host.E), ∃ z ∈ Ks i, D.nth.iC i z = τ x
  Ks_zeta : ∀ i k, D.ntw.l i = D.host.g k → ∃ z ∈ Ks i, IsPrimitiveRoot z (D.ntw.l i)

  actG : ∀ i j, RingAut ℂ_[D.ntw.l i] → D.nth.Pt i j → D.nth.Pt i j
  actG_one : ∀ i j y, actG i j 1 y = y
  actG_mul : ∀ i j, ∀ s ∈ GalF i (Ks i), ∀ t ∈ GalF i (Ks i), ∀ y,
    actG i j (s * t) y = actG i j s (actG i j t y)

  tB : ∀ i j s y, (pt i j y).BB →+ (pt i j (actG i j s y)).BB
  tB_bij : ∀ i j s y, Function.Bijective (tB i j s y)
  tH : ∀ i j s y, (pt i j y).H →+ (pt i j (actG i j s y)).H
  tH_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) h, tH i j s y (c • h) = s c • tH i j s y h
  tG : ∀ i j s y, (pt i j y).Gm 1 →+ (pt i j (actG i j s y)).Gm 1
  tG_smul : ∀ i j s y (c : ℂ_[D.ntw.l i]) g, tG i j s y (c • g) = s c • tG i j s y g

  FQ : ∀ i j, Bool → Finset (HeightOneSpectrum (𝓞 D.host.E)) → Submodule ℂ_[D.ntw.l i] (D.nth.Pt i j → ℂ_[D.ntw.l i])

  Fm_desc : ∀ i j b (QP : Finset (HeightOneSpectrum (𝓞 D.host.E))),
    (∀ P ∈ QP, IsSplitPl D.host P ∧ P ∉ D.ntw.S0 i) → ∀ F : D.nth.Pt i j → ℂ_[D.ntw.l i],
    (∃ f, D.nth.ev i j b f = F) ↔ F ∈ FQ i j b QP ∧ (∀ s ∈ GalF i ⊤, ∀ y, F (actG i j s y) = s (F y)) ∧
      ∀ P ∈ QP, ∀ (k : D.nth.Kq i j P) y, F (D.nth.actK i j P k y) = F y

  FmUr_def : ∀ i j b (f : D.nexp.Fm i j b), f ∈ D.nth.FmUr i j b ↔
    ∀ s ∈ GalF i (D.nth.MaximalUnramifiedExtension i), ∀ y, D.nth.ev i j b f (actG i j s y) = s (D.nth.ev i j b f y)





variable (X : Geo D)


end Formalism.MainNotions.ExistsIdealDenominator
