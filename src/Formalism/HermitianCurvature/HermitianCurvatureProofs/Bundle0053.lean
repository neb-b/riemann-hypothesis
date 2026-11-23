module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.Bundle0009

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section model

variable (P : M.Par)

def RhM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Drb * (MA.t21 P (MA.DQ P) y * L.Ar y + MA.t22 P (MA.DQ P) y * L.Br y)

def RhvM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Dr * (MA.t12 P (MA.DQ P) y * L.Avr y + MA.t22 P (MA.DQ P) y * L.Bvr y)

def xInvM (y : ℂ) : MA.A P (MA.DQ P) := MA.kap P (MA.DQ P) fun π => (M.xC P π y)⁻¹

def SSn (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) : MA.A P (MA.DQ P) :=
  L.Drb * L.Dri * MA.SS P (MA.DQ P) l

def RegY (y : ℂ) : Prop := ∀ π : M.Ty P, M.xC P π y ≠ 0

end model

def lagC {m : ℕ} (ν : Fin m → ℝ) (j : Fin m) (y : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (y - (ν i : ℂ)) / ((ν j : ℂ) - (ν i : ℂ))

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def HatOK (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
    GlobCoef Θ (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder Θ : ℝ) ≤ Cc * nDim S.G.k S.G.r

def IsGaugeQQ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ (Dc : (Fin (D.parOf S v).r → ℂ) → Set (Q.Mx (D.parOf S v).k (D.parOf S v).r))
    (Φ : Q.Fn (D.parOf S v).k (D.parOf S v).r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Gauge.FamR (D.parOf S v) (T v).base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty (D.parOf S v)),
      MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e
          (Q.QL (D.parOf S v).k (D.parOf S v).r (T v).base.z (T v).base.z' (Fin.last (D.parOf S v).r) (Y : ℂ) a b Φ) ρ) =
        MA.actA (D.parOf S v) (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v)) (Y : ℂ) a b)
          (fun ρ' => MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e Φ ρ')) ρ

end defs

def ResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0 y = xInvM P y * RhM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * SSn P L l * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y

def MirrorResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0v y = xInvM P y * RhvM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y

def JDHatLagrange : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (ν : Fin (P.r + 2) → ℝ), Function.Injective ν → ∀ y : ℂ,
    L.R0 y = ∑ j, lagC ν j y • L.R0 (ν j) ∧ L.R0v y = ∑ j, lagC ν j y • L.R0v (ν j)

def JDHatNodes : Prop :=
  ∀ P : M.Par, ∃ ν : Fin (P.r + 2) → ℝ, Function.Injective ν ∧ ∀ j, RegY P (ν j)

def JDOpA : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)

def JDOpR : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)

section gen

variable (P : M.Par)

theorem jdh_actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  funext π
  show ∑ π', ((1 : MA.A P (MA.DQ P)) π π').1 (f π') = f π
  rw [Finset.sum_eq_single π (fun π' _ h => by rw [Matrix.one_apply_ne (Ne.symm h)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h), Matrix.one_apply_eq]
  rfl

theorem jdh_actA_zeroR (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  funext π
  show ∑ π', (a π π').1 0 = 0
  exact Finset.sum_eq_zero fun π' _ => map_zero _

theorem jdh_actA_addR (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _

theorem jdh_actA_listsum {ι : Type} (a : MA.A P (MA.DQ P)) (l : List ι) (g : ι → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (l.map g).sum = (l.map fun i => MA.actA P a (g i)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil]; exact jdh_actA_zeroR P a
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; rw [jdh_actA_addR, ih]

theorem jdh_kap_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (g : M.Ty P → ℂ) :
    MA.kap P (MA.DQ P) g ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨g, rfl⟩)))

theorem jdh_SSn_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    SSn P L l ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩))

theorem jdh_SSns_mem (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) (hl : l ∈ Finset.Icc 1 (P.k - 1)) :
    star (SSn P L l) ∈ Submonoid.closure (MA.bddSet P L) :=
  Submonoid.subset_closure (Or.inr ⟨l, Finset.mem_Icc.1 hl, rfl⟩)

theorem jdh_smul_eq (c : ℂ) (a : MA.A P (MA.DQ P)) : c • a = MA.kap P (MA.DQ P) (fun _ => c) * a := by
  rw [Algebra.smul_def, ← (MA.kap P (MA.DQ P)).commutes c]
  rfl

end gen

section realise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}


variable (Cc S T v e L) in
def HReal (X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ HatOK Cc S T v t.2) ∧
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

theorem hReal_op {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (hΘ : HatOK Cc S T v Θ)
    (h : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) X (trJ S T v e J)) :
    HReal Cc S T v e L X := by
  refine ⟨[(1, Θ)], fun t ht => ?_, fun J hJ => ?_⟩
  · rw [List.mem_singleton] at ht
    subst ht
    exact ⟨Submonoid.one_mem _, hΘ⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [jdh_actA_one, h J hJ]

theorem hReal_zero : HReal Cc S T v e L 0 :=
  ⟨[], fun t ht => absurd ht List.not_mem_nil, fun J _ => by
    simp only [List.map_nil, List.sum_nil]; exact Gauge.actA_zero _ _⟩

theorem hReal_add {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X + Y) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  obtain ⟨ts', hts', hJ'⟩ := hY
  refine ⟨ts ++ ts', fun t ht => ?_, fun J hJJ => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hts t h
    · exact hts' t h
  · rw [Gauge.actA_add, hJ J hJJ, hJ' J hJJ, List.map_append, List.sum_append]

theorem hReal_mul {b X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (hb : b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L)) (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (b * X) := by
  obtain ⟨ts, hts, hJ⟩ := hX
  refine ⟨ts.map fun t => (b * t.1, t.2), fun t ht => ?_, fun J hJJ => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ⟨Submonoid.mul_mem _ hb (hts t' ht').1, (hts t' ht').2⟩
  · rw [Gauge.actA_mul, hJ J hJJ, jdh_actA_listsum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    rw [Gauge.actA_mul]

theorem hReal_sum {ι : Type} (s : Finset ι) (X : ι → MA.A (D.parOf S v) (MA.DQ (D.parOf S v)))
    (h : ∀ i ∈ s, HReal Cc S T v e L (X i)) : HReal Cc S T v e L (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hReal_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hReal_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hReal_smul (c : ℂ) {X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X) :
    HReal Cc S T v e L (c • X) := by
  rw [jdh_smul_eq]
  exact hReal_mul (jdh_kap_mem _ L _) hX

theorem hReal_sub {X Y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))} (hX : HReal Cc S T v e L X)
    (hY : HReal Cc S T v e L Y) : HReal Cc S T v e L (X - Y) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Y]
  exact hReal_add hX (hReal_smul _ hY)

end realise

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstPeelingMinorMemIdeal
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

section peel

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem sign_last (m : ℕ) : ((((-1 : ℤ) ^ (m + m) : ℤ) : A)) = 1 := by
  rw [← two_mul, pow_mul]
  norm_num

theorem smul_mem' (I : Ideal A) (c : ℂ) {x : A} (hx : x ∈ I) : c • x ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ hx

theorem peel_core {m : ℕ} (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (Q : Fin (m + 1) → A)
    (T : Fin (m + 1) → ι → A) (κ : ℂ)
    (hT : ∀ l, (∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) ∈ I := by
  have key : (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) = ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (Q l * ((∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
    congr 1
    · exact Finset.sum_comm
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [if_pos rfl, Fin.val_last, sign_last, one_mul, Algebra.smul_def, Algebra.commutes]
      · intro l _ hl
        rw [if_neg hl, map_zero, mul_zero, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  rw [key]
  exact Submodule.sum_mem _ fun l _ => I.mul_mem_left _ (I.mul_mem_left _ (hT l))

theorem peel_col {n m : ℕ} (I : Ideal A) (E : Fin n → Fin n → A) {ι : Type} [Fintype ι] (η : ι → ℂ)
    (a : Fin (m + 1) → Fin n) (b0 : Fin m → Fin n) (bw : ι → Fin n) (u κ : ℂ)
    (hT : ∀ l, (∑ w, η w • Tm E (u - (m : ℂ)) (a l) (bw w)) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u) - κ • qminor E (a ∘ Fin.castSucc) b0 u ∈ I := by
  have hexp : ∀ w, qminor E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u =
      ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (qminor E (a ∘ l.succAbove) b0 u * Tm E (u - (m : ℂ)) (a l) (bw w)) := by
    intro w
    rw [Formalism.FourierDecayAlt.P.expansion_last_column A n m E a (Fin.snoc (α := fun _ => Fin n) b0 (bw w)) u]
    congr 1; ext l
    have h1 : (Fin.snoc (α := fun _ => Fin n) b0 (bw w) : Fin (m + 1) → Fin n) ∘ Fin.castSucc = b0 := by
      funext x; simp [Fin.snoc_castSucc]
    rw [h1, Fin.snoc_last]
  simp_rw [hexp]
  have := peel_core I η (fun l => qminor E (a ∘ l.succAbove) b0 u) (fun l w => Tm E (u - (m : ℂ)) (a l) (bw w)) κ hT
  simpa [Fin.succAbove_last] using this

theorem hT_of (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (X : ι → A) (d : ι → ℂ) (c : ℂ)
    (hX : ∀ w, X w - algebraMap ℂ A (d w) ∈ I) (hc : ∑ w, η w * d w = c) :
    (∑ w, η w • X w) - algebraMap ℂ A c ∈ I := by
  have e : (∑ w, η w • X w) - algebraMap ℂ A c = ∑ w, η w • (X w - algebraMap ℂ A (d w)) := by
    rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [smul_sub, Finset.sum_sub_distrib, map_sum, map_mul, Algebra.smul_def, mul_sub]
  rw [e]
  exact Submodule.sum_mem _ fun w _ => smul_mem' I _ (hX w)

end peel

def pe (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨min p (2 * r + k), by omega⟩
def ps (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨2 * r + k - p, by omega⟩

@[simp] theorem pe_val (k r p : ℕ) : (pe k r p).val = min p (2 * r + k) := rfl
@[simp] theorem ps_val (k r p : ℕ) : (ps k r p).val = 2 * r + k - p := rfl

theorem mem_gen {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {p q : Fin (2 * r + k + 1)} (h : InNp k r p q) :
    E p q - algebraMap ℂ A (dpsiP k r z' p q) ∈ Ideal.span (rgen k r z' E) := Ideal.subset_span ⟨p, q, h, rfl⟩

theorem tm_offdiag {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {p q : Fin n}
    (h : p ≠ q) : Tm E u p q = E p q := by
  simp [Tm, h]

theorem last_iff {m : ℕ} (l : Fin (m + 1)) : l = Fin.last m ↔ l.val = m := by
  rw [Fin.ext_iff, Fin.val_last]

theorem first_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => pe k r l.val) (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u -
      qminor E (fun l : Fin i => pe k r l.val) (fun l : Fin i => pe k r l.val) u ∈ Ideal.span (rgen k r z' E) := by
  intro m
  induction m with
  | zero =>
    intro i hi _
    have hi0 : i = 0 := by omega
    subst hi0
    have e : (fun l : Fin 0 => pe k r (if l.val < 0 then l.val else l.val + 1)) = fun l : Fin 0 => pe k r l.val :=
      funext fun l => l.elim0
    rw [e, sub_self]
    exact Submodule.zero_mem _
  | succ m ih =>
    intro i hi hr
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · have hih := ih i (by omega) (by omega)
      have hstep : qminor E (fun l : Fin (m + 1) => pe k r l.val)
            (fun l : Fin (m + 1) => pe k r (if l.val < i then l.val else l.val + 1)) u -
          qminor E (fun l : Fin m => pe k r l.val)
            (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u ∈
            Ideal.span (rgen k r z' E) := by
        have hc := peel_core (Ideal.span (rgen k r z' E)) (ι := Unit) (fun _ => (1 : ℂ))
          (fun l : Fin (m + 1) => qminor E ((fun l : Fin (m + 1) => pe k r l.val) ∘ l.succAbove)
              (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u)
          (fun l _ => Tm E (u - (m : ℂ)) (pe k r l.val) (pe k r (m + 1))) 1 ?_
        · rw [Formalism.FourierDecayAlt.P.expansion_last_column A (2 * r + k + 1) m E]
          have hm : ¬ (m < i) := by omega
          simpa [Fin.succAbove_last, Fin.val_last, hm, Function.comp_def, Fin.coe_castSucc] using hc
        · intro l
          have hl := l.isLt
          have h1 : min (l.val) (2 * r + k) = l.val := Nat.min_eq_left (by omega)
          have h2 : min (m + 1) (2 * r + k) = m + 1 := Nat.min_eq_left (by omega)
          have hne : pe k r l.val ≠ pe k r (m + 1) := by
            intro e
            have := congrArg Fin.val e
            simp only [pe_val, h1, h2] at this
            omega
          have hin : InNp k r (pe k r l.val) (pe k r (m + 1)) := by
            simp only [InNp, pe_val, h1, h2]
            omega
          have hd : dpsiP k r z' (pe k r l.val) (pe k r (m + 1)) = if l.val = m then 1 else 0 := by
            simp only [dpsiP, pe_val, h1, h2]
            rw [if_pos ⟨by omega, by omega⟩]
            split_ifs <;> first | rfl | (exfalso; omega)
          simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, last_iff]
          rw [tm_offdiag _ _ hne, ← hd]
          exact mem_gen hin
      have hsum := (Ideal.span (rgen k r z' E)).add_mem hstep hih
      rwa [sub_add_sub_cancel] at hsum
    · have hi1 : i = m + 1 := by omega
      subst hi1
      have e : (fun l : Fin (m + 1) => pe k r (if l.val < m + 1 then l.val else l.val + 1)) =
          fun l : Fin (m + 1) => pe k r l.val := by
        funext l
        rw [if_pos l.isLt]
      rw [e, sub_self]
      exact Submodule.zero_mem _

theorem first_peeling_identity : PeelingOmittedColumn := by
  intro A _ _ k r z' E m hm i u
  have e1 : ∀ (j : ℕ) (hj : j ≤ r), xR k r j hj = fun l : Fin j => pe k r l.val := by
    intro j hj
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val]
    have := l.isLt
    omega
  have e2 : (fun l : Fin m => xR k r (m + 1) hm (i.succAbove l)) =
      fun l : Fin m => pe k r (if l.val < i.val then l.val else l.val + 1) := by
    funext l
    apply Fin.ext
    simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, pe_val, succAbove_val]
    have := l.isLt
    split_ifs <;> omega
  rw [e2, e1, e1]
  exact first_peeling_minor_mem_ideal k r z' E u m i.val (by have := i.isLt; omega) hm

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBStmt
section
namespace Formalism.FourierDecayAlt.KB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def NhatV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (L : Fin S.f → ℂ) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hatB S v ε i 1 (w.1 v) (L v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')

def NstV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (t t' : Fin S.f → ℂ) : ℂ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)])
      (C.loc (S.σ v) h' ++ [(s, t' v)])) / (C.Word.size S.P w.1 : ℂ)

end loc

def WaveV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ),
    (∀ v, WaveLoc S v fun i => X i v) →
    ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
          ∀ (L : Fin S.f → ℂ) (A : Finset (Fin S.f)),
            (∏ v ∈ A, ‖L v‖ ^ C.Kst) * ‖NhatV S ε i w Y κ L‖ ≤
              (∏ v ∈ A, X i v ^ C.Kst) *
                ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ A w' * S.base.N0 ε (i - 1) w' Y κ

def LiftV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Λ : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → (∀ v, LiftLoc S v fun b s => Λ b s v) →
    ∀ ε, 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ S.G.r → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
        (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ (Y : Finset (TB.Pt E)) (κa κw κb : TB.Pt E → TB.Pt E → ℂ),
          (∀ h ∈ Y, TB.level h = i - s) → BlockPSD Y Y κa κw κb →
          ∀ (t t' : Fin S.f → ℂ), (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) → ∀ A : Finset (Fin S.f),
            (∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) * ‖NstV S ε i s w Y κw t t'‖ ≤
              (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) *
                ∑ x ∈ S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst), θ A x *
                  (((NstV S ε i s x.1 Y κa t t).re + (NstV S ε i s x.2 Y κb t' t').re) / 2)

end

end Formalism.FourierDecayAlt.KB
end

