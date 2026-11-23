module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
section
open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

def val_vp {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (p : ℕ) (x : K) : ℚ :=
  (ordE w x : ℚ) / (ordE w (p : K) : ℚ)

def UnitAt {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop := w.valuation K x = 1

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def vpIdeal (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) E :=
  (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) * ((conjPrime₂ P).asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) :
    Submodule (𝓞 E) E)

def vpLat (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E 1) :=
  (vpIdeal P).comap ((LinearMap.proj (0 : Fin 1) : Sp E 1 →ₗ[E] E).restrictScalars (𝓞 E))

def StdOver {n : ℕ} (p : ℕ) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt E n P

def IsFrames {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

end Lat

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ)

def idTo (I : Submodule (𝓞 X.E) X.E) : TaylorLogMetric.IdE D :=
  Submodule.span (𝓞 D.host.E) (s.iE '' (I : Set X.E))

def ChiInK : Prop := ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → ∃ k : X.K, s.σ₀ k = χ 𝔞

def chiK (𝔞 : TaylorLogMetric.IdE D) : X.K := desc s.σ₀ (χ 𝔞)

def chiVp (P : HeightOneSpectrum (𝓞 X.E)) : X.K := chiK s χ (idTo s (vpIdeal P))

def chiDet {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : X.K :=
  chiK s χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N))

def chiFK (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  desc s.σ₀ (Base.chiFac χ a b (s.lat N) (s.lat N'))

end Chi

section Rho

variable {D : D7} (Z : Dat) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ)
  (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) {S : Set ℕ}
  (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu))

def muInv (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInvDet sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) (muAtT Z.Ch sel mu cst i) N fr

def scal (i : ℕ) {a b : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * (muInv Z sel mu cst i N' fr')⁻¹

def rho (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  muInv Z sel mu cst i N fr * chiDet s χ N ^ (-((Z.R.N (i + 1) / 2 : ℕ) : ℤ))

def rho' (i : ℕ) {n : ℕ} (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)) : Z.X.K :=
  (muInv Z sel mu cst i N fr)⁻¹ * chiDet s χ N ^ (((Z.R.N i / 2 : ℕ) : ℤ))

def sPrime (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp' Z.R ((Z.W.row τ).e i) (i.1 + 1)

def sPlain (i : Fin Z.R.m) (τ : Z.X.Tau) : ℚ := sExp Z.R ((Z.W.row τ).e i) (i.1 + 1)

def PartA (u : Z.Pr.Word) : Prop :=
  ∀ P ∈ Z.Pr.vT u,
    (∀ σ : Z.X.K →+* ℂ, ‖σ (chiVp s χ P)‖ = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∉ w.asIdeal → UnitAt w (chiVp s χ P)) ∧
    ∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → ∀ τ : Z.X.Tau,
      (SeesP w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = -1) ∧
      (SeesPbar w τ P → val_vp w (Z.Pr.T u) (chiVp s χ P) = 1)

def PartBChi (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) : Prop :=
  (∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Z.Pr.T u : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      localization₂ P.asIdeal 𝔞 = localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) →
    UnitAt w (chiK s χ 𝔞)) ∧
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N → UnitAt w (chiDet s χ N)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)), Even a → Even b →
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → UnitAt w (chiFK s χ a b N N')

def PartBMu (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : ℕ) : Prop :=
  (∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)), IsSdLat N → StdOver (Z.Pr.T u) N →
    UnitAt w (muOff sel (rowSG Z.Pr sel mu) (mUof Z.Ch mu i) N) ∧
    ∀ fr : Frs Z.X.E n (rowSG Z.Pr sel mu), IsFrames N fr →
      UnitAt w (muInv Z sel mu cst i N fr) ∧ UnitAt w (rho Z s χ sel mu cst i N fr) ∧ UnitAt w (rho' Z s χ sel mu cst i N fr)) ∧
  ∀ (a b : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E a)) (fr : Frs Z.X.E a (rowSG Z.Pr sel mu))
    (N' : Submodule (𝓞 Z.X.E) (Sp Z.X.E b)) (fr' : Frs Z.X.E b (rowSG Z.Pr sel mu)),
    IsSdLat N → IsSdLat N' → StdOver (Z.Pr.T u) N → StdOver (Z.Pr.T u) N' → IsFrames N fr → IsFrames N' fr' →
    UnitAt w (scal Z sel mu cst i N fr N' fr')

def PartC (u : Z.Pr.Word) (w : HeightOneSpectrum (𝓞 Z.X.K)) (i : Fin Z.R.m) : Prop :=
  ∀ P ∈ Z.Pr.vT u, ∀ τ : Z.X.Tau, SeesP w τ P ∨ SeesPbar w τ P →
    rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧ rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1) ≠ 0 ∧
    val_vp w (Z.Pr.T u) (rho Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      sPrime Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P) ∧
    val_vp w (Z.Pr.T u) (rho' Z s χ sel mu cst i.1 (vpLat P) (fun _ => 1)) =
      -sPlain Z i τ * val_vp w (Z.Pr.T u) (chiVp s χ P)

def PartD (i : ℕ) : Prop :=
  ∀ (n : ℕ) (N : Submodule (𝓞 Z.X.E) (Sp Z.X.E n)) (fr : Frs Z.X.E n (rowSG Z.Pr sel mu)), IsSdLat N → IsFrames N fr →
    chiDet s χ N ≠ 0 ∧
    rho Z s χ sel mu cst i N fr * rho' Z s χ sel mu cst i N fr = chiDet s χ N ^ (-(((Z.R.t + 1) / 2 : ℕ) : ℤ))

def UnramOver {X : Fields} (ξ : Chr X.F X.E X.K) (p : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (p : 𝓞 X.F) ∈ v.asIdeal → v ∉ Qprime ξ

end Rho

def CharValAtT : Prop :=
  ∀ (Z : Dat) (D : D7) (s : Seam D Z.X) (χ : TaylorLogMetric.IdE D → ℂ) (u : Z.Pr.Word),
    Z.Ok → s.Ok → s.σ₀ = Z.sig0 → TaylorLogMetric.IsChi D χ → ChiInK s χ →
    PartA Z s χ u ∧
    (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal → PartBChi Z s χ u w) ∧
    ∀ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E),
      Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta →
      ∀ (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)), IsSel Z.X sel →
      ∀ (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S),
        UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.T u) → (∀ k, UnramOver (mu : Chr Z.X.F Z.X.E Z.X.K) (Z.Pr.g k)) →
      ∀ cst : LocCst Z.X (rowSG Z.Pr sel mu), MuqTieG (Pr := Z.Pr) (R := Z.R) sel mu cst Z.sig0 m0 →
      ∀ i : Fin Z.R.m,
        (∀ w : HeightOneSpectrum (𝓞 Z.X.K), ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal →
          PartBMu Z s χ sel mu cst u w i.1 ∧ PartC Z s χ sel mu cst u w i) ∧
        PartD Z s χ sel mu cst i.1

theorem UnitAt.ne_zero {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : UnitAt w x) : x ≠ 0 := by
  rintro rfl
  simp [UnitAt] at h

end GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Lattices

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def idxExp {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : ℤ :=
  ordDet P N₂ - ordDet P N₁

def AgreeOff (T : ℕ) {n : ℕ} (N₁ N₂ : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((T : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N₁ = localization₂ Q.asIdeal N₂

def InBox {K : Type} [Field K] {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt Sall N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt Sall N N'), Ξ (x + y) = Ξ x

end Lattices

section Jets

variable {X : Fields} {a b : ℕ}

def degAt (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) : ℕ := ∑ β : Fin b, ∑ α : Fin a, m (τ, β, α)

def degNu (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (τ : X.Tau) : ℤ :=
  ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))

def JetsIn (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ) (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

end Jets

def locScal {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) (e e' : ℤ) : K :=
  ((w ^ (e' - e) : Kˣ) : K) * (q : K) ^ (((b / 2 : ℕ) : ℤ) * e - ((a / 2 : ℕ) : ℤ) * e')

section Scal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def moveScal (u : Pr.Word) (i : ℕ) {a b : ℕ} (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) : X.K :=
  ∏ P ∈ Pr.vT u, locScal a b (Pr.T u) (mUof Ch mu i P) (idxExp P N₁ N₂) (idxExp P N₁' N₂')

end Scal

theorem locScal_one_one {K : Type} [Field K] (R : Ranks) (i q : ℕ) (w : Kˣ) :
    locScal (R.N i) (R.N (i + 1)) q w 1 1 = (q : K) ^ ((R.t + 1) / 2) := by
  obtain ⟨c, hc⟩ := R.t_odd
  have h1 : R.N (i + 1) = R.N i + 2 * (c + 1) := by
    unfold Ranks.N
    rw [hc]
    ring
  have h2 : (R.t + 1) / 2 = c + 1 := by omega
  have h3 : (((R.N (i + 1) / 2 : ℕ) : ℤ) * 1 - ((R.N i / 2 : ℕ) : ℤ) * 1) = ((c + 1 : ℕ) : ℤ) := by
    rw [h1]
    omega
  unfold locScal
  rw [h3, h2, sub_self, zpow_zero, Units.val_one, one_mul, zpow_natCast]

theorem locScal_zero_zero {K : Type} [Field K] (a b q : ℕ) (w : Kˣ) : locScal a b q w 0 0 = 1 := by
  simp [locScal]

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add ((R.t_odd.add_one).mul_left j)

end GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Supp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

def adj (x : HomE E a b) : HomE E b a := Matrix.toLin' (LinearMap.toMatrix' x).conjTranspose


omit [NumberField E] in
theorem adj_single (x : HomE E a b) (α : Fin a) (β : Fin b) :
    adj x (Pi.single β 1) α = star (x (Pi.single α 1) β) := by
  rw [adj, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp [LinearMap.toMatrix'_apply]

variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def suppBar (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}

def suppP (d : Deco E a ST SG) (d' : Deco E b ST SG') : Set (HomE E a b) :=
  {x | ∀ P : ST, ∀ y ∈ d'.at P.1, d'.f P y = 0 → adj x y ∈ d.at P.1}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

end Supp

section Mom

variable {p : ℕ} [Fact p.Prime]

def InIntClosure {H I : Type} (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) (J : I → ℂ_[p]) : Prop :=
  ∀ F : Finset I, (F : Set I) ⊆ M → ∀ ε : ℝ, 0 < ε →
    ∃ c : H →₀ ℂ_[p], (c.support : Set H) ⊆ Sup ∧ (∀ x, ‖c x‖ ≤ 1) ∧
      ∀ m ∈ F, ‖J m - c.sum fun x r => r * tab x m‖ < ε

variable {X : Fields} {a b : ℕ}

def Induces (ι : X.K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 X.K)) : Prop :=
  ∀ y : 𝓞 X.K, y ∈ w.asIdeal ↔ ‖ι (y : X.K)‖ < 1

def ptTab (ι : X.K →+* ℂ_[p]) (u : X.Tau → ℂ_[p]) (x : HomE X.E a b) (m : DVar X.Tau a b →₀ ℕ) : ℂ_[p] :=
  m.prod fun k n => (u k.1 * ι (X.emb k.1 (adj x (Pi.single k.2.1 1) k.2.2))) ^ n

end Mom

section Tab

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)

def jetSum (m : DVar X.Tau a b →₀ ℕ) : X.K :=
  latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) fun x => Ξ x * A.jetK S N N' cB x m

def RatIdx : Set (DVar X.Tau a b →₀ ℕ) :=
  {m | ∀ x ∈ divLat cA (homAt S N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' cB x) m}

def OffDatum (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (w : HeightOneSpectrum (𝓞 X.K)) (Ξ₀ : HomE X.E a b → X.K) : Prop :=
  ∀ x ∈ divLat cA (homAt SB N N'),
    w.valuation X.K (Ξ₀ x) ≤ 1 ∧ ∀ y ∈ mulLat cB (homAt SB N N'), Ξ₀ (x + y) = Ξ₀ x

end Tab

def AnaOk (D : Dat) {H : D7} (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE H → ℂ)
    (cD : H.what₂.Tau → ℂ) : Prop :=
  s.Ok ∧ s.σ₀ = D.sig0 ∧ TaylorLogMetric.IsCurveIdeal H cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice H cc δ ∧ TaylorLogMetric.IsChi H χ ∧ IsDgen H cD

def MomAt (D : Dat) {H : D7} (cc : Ideal (𝓞 H.host.K)) (A : Amb D.X) (u : D.Pr.Word) [Fact (D.Pr.T u).Prime]
    (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]) (un : D.X.Tau → ℂ_[D.Pr.T u]) : Prop :=
  ∀ (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) (S : Set ℕ) (mu : Tup D.X.F D.X.E D.X.K S)
    (cst : LocCst D.X (rowSG D.Pr sel mu)),
    IsSel D.X sel → hostS H.host.q H.host.d (D.Pr.g 0) (D.Pr.g 1) (Set.range D.Pr.T) ⊆ S →
    (∀ P ∈ rowSG D.Pr sel mu, Nat.Coprime (Ideal.absNorm cc) (qOf P)) →
    ∀ (i b : ℕ), i < D.R.m → b = D.R.N (i + 1) →
    ∀ (SG SG' : Finset (HeightOneSpectrum (𝓞 D.X.E)))
      (d : DecoSet (E := D.X.E) (n := D.R.N i) (ST := D.Pr.vT u) (SG := SG)) (d' : DecoSet (E := D.X.E) (n := b) (ST := D.Pr.vT u) (SG := SG')),
      StdAtT d.1 → StdAtT d'.1 →
      ∀ Ξ₀ : HomE D.X.E (D.R.N i) b → D.X.K,
        OffDatum (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N (rowSG D.Pr sel mu) w Ξ₀ →
        (seenBarC D.Pr u w →
          InIntClosure (suppBar d.1 d'.1) (ptTab ι un)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m)) ∧
        (seenC D.Pr u w →
          InIntClosure (suppP d.1 d'.1)
            (fun x m => ((D.Pr.T u : ℂ_[D.Pr.T u]) ^ (D.X.f * D.R.N i))⁻¹ * ptTab ι un x m)
            (RatIdx A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x)
            fun m => ι (jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
              (fun x => phiT D.X.K d.1 d'.1 x * Ξ₀ x) m))

def JetMoments : Prop :=
  ∀ (D : Dat), D.Ok →
  ∀ (H : D7) (s : Seam H D.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ),
    AnaOk D s cc δ χ cD →
    ∀ (u : D.Pr.Word) [Fact (D.Pr.T u).Prime], Nat.Coprime (Ideal.absNorm cc) (D.Pr.T u) →
    ∀ (w : HeightOneSpectrum (𝓞 D.X.K)) (ι : D.X.K →+* ℂ_[D.Pr.T u]), Induces ι w →
      ∃ un : D.X.Tau → ℂ_[D.Pr.T u], (∀ τ, ‖un τ‖ = 1) ∧ MomAt D cc (ambOf s B χ cD) u w ι un

end GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MovementLaw
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def InRangeOf {K : Type} [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Ξ : HomE E a b → K) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) ∧ ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x

end Generic


open Classical in
def JetsIn {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (deg : X.Tau → ℤ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K) : Prop :=
  ∀ x, Ξ x ≠ 0 → ∀ m : DVar X.Tau a b →₀ ℕ,
    (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
    ∃ y : X.K, A.σ₀ y = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

section Scalar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Scalar

end GlobalTheory.IndefiniteRowSideFullHecke.MovementLaw
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
section
open NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

def ptTable {R : Type} [CommRing R] {ι : Type} {a b : ℕ} (ap : ι → Matrix (Fin a) (Fin b) R)
    (m : DVar ι a b →₀ ℕ) : R :=
  m.prod fun k e => ap k.1 k.2.2 k.2.1 ^ e

def substAdj {K : Type} [Field K] {ι : Type} {a b : ℕ} (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) :
    Pol K ι a →ₐ[K] Pol K ι b :=
  aeval fun v => ∑ β : Fin b, C (ap v.1 v.2.1 β) * X (v.1, β, Fin.castLE hab v.2.2)

def sharp {K : Type} [Field K] {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (P : Pol K ι a) : Pol K ι a :=
  P * ∏ τ, frDet K a τ ^ n τ

def WtCompat {ι : Type} {a b : ℕ} (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (s s' : ι → ℤ) (n : ι → ℕ) : Prop :=
  (∀ τ (i : Fin a), (lam' τ).w (Fin.castLE hab.le i) + s τ = (lam τ).w i + s' τ) ∧
  (∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).w j = -s τ) ∧
  ∀ τ, (n τ : ℤ) = (lam τ).detShift + s' τ

def InDeg {ι : Type} {a b : ℕ} (lam : ι → DomWeight a) (s' : ι → ℤ) (m : DVar ι a b →₀ ℕ) : Prop :=
  ∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) = ∑ i : Fin a, ((lam τ).w i + s' τ)

section Lat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

def HAt {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) :
    Submodule (𝓞 K) (VV K lam) :=
  localization₂ w.asIdeal (nabK lam fun τ => dualFr (M τ))

def detFac {a b : ℕ} (s s' : ι → ℤ) (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K) : K :=
  ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ * (BW τ : Matrix (Fin b) (Fin b) K).det ^ (-s τ)

def LatWithBasis {a : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : ι → Submodule (𝓞 K) (Fin a → K))
    (B : ι → GL (Fin a) K) : Prop :=
  ∀ τ, (M τ).FG ∧ IsBasisAt w (M τ) (B τ)

def extLat {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a : ℕ}
    (M : Submodule (𝓞 K) (Fin a → K)) : Submodule v.integer (Fin a → L) :=
  Submodule.span v.integer ((fun (x : Fin a → K) (i : Fin a) => σ (x i)) '' (M : Set (Fin a → K)))

def admitted {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (ap : ι → Matrix (Fin a) (Fin b) L) : Prop :=
  ∀ τ, ∀ y ∈ extLat v σ (MW τ), ap τ *ᵥ y ∈ extLat v σ (M τ)

def InClosure {L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L) {a b : ℕ}
    (lam : ι → DomWeight a) (s' : ι → ℤ)
    (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
    (κ : K) (J : (DVar ι a b →₀ ℕ) → K) : Prop :=
  ∀ ε : K, ε ≠ 0 → ∃ (k : ℕ) (c : Fin k → L) (ap : Fin k → ι → Matrix (Fin a) (Fin b) L),
    (∀ i, v (c i) ≤ 1) ∧ (∀ i, admitted v σ M MW (ap i)) ∧
    ∀ m, InDeg lam s' m → v (σ (J m) - σ κ * ∑ i, c i * ptTable (ap i) m) ≤ v (σ ε)

end Lat

def DetIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (r : ℕ) (B B' : GL (Fin r) K)
    (M' : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (q : K), q ≠ 0 →
    localization₂ w.asIdeal M' = localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range fun j : Fin r => fun α : Fin r =>
      (if j = i then q else 1) * (B : Matrix (Fin r) (Fin r) K) α j)) →
    IsBasisAt w M' B' →
    w.valuation K (B' : Matrix (Fin r) (Fin r) K).det = w.valuation K (q * (B : Matrix (Fin r) (Fin r) K).det)

def PointIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ ap : ι → Matrix (Fin a) (Fin b) K, (∀ τ, ∀ y ∈ MW τ, ap τ *ᵥ y ∈ localization₂ w.asIdeal (M τ)) →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' (ptTable ap) n F = detFac s s' B BW • G

def ClosureIntegral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) (σ : K →+* L),
    (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
      (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ),
    WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K))
      (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K), LatWithBasis w M B → LatWithBasis w MW BW →
    ∀ (κ : K) (J : (DVar ι a b →₀ ℕ) → K), InClosure v σ lam s' M MW κ J →
    ∀ F ∈ HAt w lam M, ∃ G ∈ HAt w lam' MW, jetOp lam lam' J n F = (κ * detFac s s' B BW) • G

end GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
end
end

