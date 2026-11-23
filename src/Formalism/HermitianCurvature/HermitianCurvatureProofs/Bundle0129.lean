module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0126
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsMeasurableSection
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AutomorphicInSphericalLevel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def dMul (d : (Fin r → ℂ) → ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X := fun c g => d c • Φ c g

def drF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => ∏ a, c a

def drbF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => starRingEnd ℂ (∏ a, c a)

variable (k r)

def rhGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drbF r) (Q.QL k r z z' (Fin.last r) y 1 0 (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vAB r y r) 1) Φ))

def rhvGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drF r) (Q.QL k r z z' (Fin.last r) y 0 1 (Q.crd (Q.cmp (Q.vABs r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vABs r y r) 1) Φ))

end defs

def JDRGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRDrTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      (∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) Φ) ρ) =
        MA.actA P L.Drb (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) Φ) ρ) =
        MA.actA P L.Dr (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def JDRModelV : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℝ,
    (∀ b : Fin 2, Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) b = L.Tprod (y : ℂ) b 0) ∧
    ∀ a : Fin 2, star (Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) a) = L.Tvprod (y : ℂ) a 0

def JDRGrpP : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRGrpM : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

theorem jDRGrp_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDRGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, h1, h3, hR⟩ := hP Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θv, h2, h4, hRv⟩ := hM Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  exact ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ c hc g hg hcg => ⟨hR J hJ c hc g hg hcg, hRv J hJ c hc g hg hcg⟩⟩

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jdr_tr_at (hD : JDRDrTr) (hM : JDRModelV) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : Gauge.FamR P Bs Dc Φ)
    (y : ℝ) :
    Gauge.VLem.trR P Bs.μsec e (rhGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) ∧
      Gauge.VLem.trR P Bs.μsec e (rhvGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhvM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) := by
  have hV : Gauge.GVTr := by
    intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
    have h := Gauge.VLem.vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
    rw [Gauge.VLem.sitesCommonSpace_v0_eq_Vp]
    fin_cases b
    · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
    · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩
  have hV := fun b => hV Wp Wq P Bs hpl hk e he Dc Φ hΦ y b
  have hVs : Gauge.GVsTr := by
    intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y a
    have h := Gauge.VLem.vabs_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
    rw [Gauge.VLem.sitesCommonSpace_v0_eq_Vp]
    fin_cases a
    · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
    · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩
  have hVs := fun a => hVs Wp Wq P Bs hpl hk e he Dc Φ hΦ y a
  have hsm := fun (Dc' : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (hΨ : Gauge.FamR P Bs Dc' Ψ) => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc' Ψ hΨ
  have hql := fun (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΨ : Gauge.FamR P Bs Dc Ψ) (a b : Fin 2) =>
    Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Ψ hΨ y a b
  obtain ⟨hMv, hMs⟩ := hM P L hL y
  have hsum : ∀ (Ψ₀ Ψ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Ψ₀ → Gauge.FamR P Bs Dc Ψ₁ →
      Gauge.FamR P Bs Dc (Ψ₀ + Ψ₁) := fun _ _ h₀ h₁ => Gauge.VLem.famR_add h₀ h₁
  constructor
  · have hF0 := hql _ (hV 0).1 1 0
    have hF1 := hql _ (hV 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).1 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 0 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 1 0 * L.Ar (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Br (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Ar, R.LevelData.Br, ← hMv 0, ← hMv 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hV 0).1 y 1 0 ρ']; congr 1; funext ρ''; exact (hV 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hV 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hV 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl
  · have hF0 := hql _ (hVs 0).1 0 1
    have hF1 := hql _ (hVs 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).2 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 0 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 0 1 * L.Avr (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Bvr (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Avr, R.LevelData.Bvr, ← hMs 0, ← hMs 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hVs 0).1 y 0 1 ρ']; congr 1; funext ρ''; exact (hVs 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hVs 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hVs 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl

end assembly

theorem jDCapR_of_parts (hG : JDRGrp) (hD : JDRDrTr) (hM : JDRModelV) : JDCapR := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨tR, tRv⟩ := jdr_tr_at hD hM (D.parOf S v) (T v).base hpl hk e hFr
    (fun Dc Φ hΦ Y a b ρ => hQQ Dc Φ hΦ Y a b ρ) L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    exact tR
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    exact tRv

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQCore
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdg_gauge_of_core {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (hcore : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) :
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs), ∀ Y : ℝ,
      Gauge.trJB P Bs e (Q.CV P.k P.r (Y : ℂ) J) =
        MA.actA P (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ)) (Gauge.trJB P Bs e J) := by
  intro J hJ Y
  obtain ⟨hF, hres, hcv⟩ := Gauge.gauge_transition_chain_holds Wp Wq P Bs hpl hk J hJ
  set Φ := Q.resG P.k P.r (Fin.last P.r) J with hΦ
  have hJe : Gauge.trJB P Bs e J = fun ρ => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) := by
    funext ρ
    exact congrArg (MA.toSm P) (hres e ρ)
  have hpair : ∀ a b : Fin 2,
      (∀ ρ, Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ ∈ MA.smSub P.r P.TT) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ) =
        MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
          Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) ρ := by
    intro a b
    obtain ⟨hF1, hV1⟩ := Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he _ Φ hF Y b
    have hF2 := Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk _ _ hF1 Y a b
    obtain ⟨hF3, hV2⟩ := Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he _ _ hF2 Y a
    refine ⟨fun ρ => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he _ _ hF3 ρ, fun ρ => ?_⟩
    have hin : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ')) =
        MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) := by
      funext ρ'
      rw [hV1 ρ', hJe]
    have hmid : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J)) := by
      funext ρ'
      rw [hcore _ _ hF1 Y a b ρ', hin]
    rw [hV2 ρ, Gauge.actA_mul, Gauge.actA_mul, hmid]
  funext ρ
  show MA.toSm P (Gauge.rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ) = _
  rw [hcv e ρ Y]
  rw [show Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ) =
      ∑ a, ∑ b, star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
        Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b from rfl]
  simp only [Gauge.actA_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ((hpair a b).2 ρ).symm]
  rw [Gauge.toSm_of_mem P (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => (hpair a b).1 ρ)]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Gauge.toSm_of_mem P ((hpair a b).1 ρ)]

theorem jdg_exists_of_gCore (hK : Gauge.GCore) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (hB : BuiltOW Cc S T f χ ν' m₀ top A₀) (v : Fin S.f) :
    ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e := by
  obtain ⟨hBP, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIB, -, -, -, -, -, -, hk2, -, -⟩ := hBP
  obtain ⟨-, -, -, hpl, -, -⟩ := hIB.2 v
  obtain ⟨e, he, hc⟩ := hK (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hpl hk2
  exact ⟨e, he, jdg_gauge_of_core (D.parOf S v) (T v).base hpl hk2 e he hc, hc⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNSandwich
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem coef_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {z Y z' : Mx k r}
    (hz : z ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ z w, σ Y (σ z' w)⟫_ℂ = ⟪w, σ (z⁻¹ * Y * z') w⟫_ℂ := by
  have hzi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hz
  have hiso := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).2 z hz
  have hM : z⁻¹ * Y * z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hzi.1 hY) hz'
  have h1 : σ Y (σ z' w) = σ z (σ (z⁻¹ * Y * z') w) := by
    have e1 : σ (Y * z') = (σ Y).comp (σ z') := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hY hz'
    have e2 : σ (z * (z⁻¹ * Y * z')) = (σ z).comp (σ (z⁻¹ * Y * z')) :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hz hM
    have e3 : z * (z⁻¹ * Y * z') = Y * z' := by
      rw [← mul_assoc, ← mul_assoc, hzi.2.1, one_mul]
    rw [e3] at e2
    have h2 := congrArg (fun T => T w) (e1.symm.trans e2)
    simpa using h2
  rw [h1]
  exact (⟨(σ z).toLinearMap, hiso⟩ : H →ₗᵢ[ℂ] H).inner_map_map w _

theorem gN_sandwich (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by
  have hN := hNI k r
  have hxi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hx
  have hyi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hxi.1 hA) hy
  have hm1 := (hN.2 _ hM).2
  have ha1 := (hN.2 _ hA).2
  have hx1 := (hN.2 _ hx).2
  have hy1 := (hN.2 _ hy).2
  have hyinv := (hN.2 _ hy).1
  have hAeq : x * (x⁻¹ * A * y) * y⁻¹ = A := by
    rw [show x * (x⁻¹ * A * y) * y⁻¹ = (x * x⁻¹) * A * (y * y⁻¹) by simp only [mul_assoc],
      hxi.2.1, hyi.2.1, one_mul, mul_one]
  have hle : B.gN A ≤ (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by
    calc B.gN A = B.gN (x * (x⁻¹ * A * y) * y⁻¹) := by rw [hAeq]
      _ ≤ B.gN (x * (x⁻¹ * A * y)) * B.gN y⁻¹ := hN.1 _ _
      _ ≤ B.gN x * B.gN (x⁻¹ * A * y) * B.gN y⁻¹ :=
          mul_le_mul_of_nonneg_right (hN.1 _ _) (by rw [hyinv]; linarith)
      _ = (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by rw [hyinv]; ring
  have hp : 0 < B.gN x * B.gN y := mul_pos (by linarith) (by linarith)
  have hmb : 0 < B.gN (x⁻¹ * A * y) ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hab : 0 < B.gN A ^ b := Real.rpow_pos_of_pos (by linarith) b
  have key : B.gN A ^ b ≤ (B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hle hb
  rw [Real.rpow_neg (show (0:ℝ) ≤ B.gN (x⁻¹ * A * y) by linarith),
    Real.rpow_neg (show (0:ℝ) ≤ B.gN A by linarith)]
  calc (B.gN (x⁻¹ * A * y) ^ b)⁻¹
        = (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * B.gN A ^ b * (B.gN A ^ b)⁻¹ := by
          exact (mul_inv_cancel_right₀ hab.ne' _).symm
    _ ≤ (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * ((B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b) *
          (B.gN A ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hmb.le))
          (inv_nonneg.2 hab.le)
    _ = (B.gN x * B.gN y) ^ b * (B.gN A ^ b)⁻¹ := by
        rw [mul_comm ((B.gN x * B.gN y) ^ b) (B.gN (x⁻¹ * A * y) ^ b), inv_mul_cancel_left₀ hmb.ne']

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
section
namespace Formalism.FourierDecayAlt.P

theorem phi_zero_hermitian_curvature : Formalism.FourierDecayAlt.KB.PhiZero :=
  phi_zero_of_parts pbi_sectionExists_proof fibre_integral_smooth fibre_integral_cells

theorem density_constant : Formalism.FourierDecayAlt.KB.DensC :=
  pb_densC_of phi_zero_hermitian_curvature vector_vanishes_big_cell

end Formalism.FourierDecayAlt.P
end

