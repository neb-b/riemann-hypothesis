module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0132
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0133

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocal
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_locality_holds : GTCLocal := gTCLocal_of_cut radial_torus_local_holds local_nabla_holds local_frame_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem gauge_lines_holds : PRho.GaugeLines :=
  PRho.GL.gaugeLines_of_cut PRho.GL.gauge_right_line_holds PRho.GL.gauge_left_line_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpM
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def colsV (t : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < t.val then r + j.val else r + j.val + 1, by have := j.isLt; have := t.isLt; split_ifs <;> omega⟩

def rowV (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun q =>
    if h : p.val < r then herm (Hpk k r) (g *ᵥ bvec q) (bvec (eI k r ⟨p.val, h⟩))
    else if h2 : p.val = r then herm (Hpk k r) (g *ᵥ bvec q) z
    else if q = J ⟨p.val - r - 1, by have := p.isLt; omega⟩ then 1 else 0

def alJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => rowV k r z g J p q).det

def rvhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ t : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (t : ℕ)) * z' (wI k r t) * alJ k r z g J) •
      qminorOp (Q.EH k r) J (colsV k r t) (Q.uC k r (Fin.last r) Y - 1) f g

end defs

def JDRRadM : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rvhatOp k r z z' Y J x) c g =
        rhvGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvM : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
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
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rvhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpM_of_parts (hR : JDRRadM) (hI : JDRRealInvM) : JDRGrpM := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRad
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsN (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t)) •
      qminorOp (Q.EH k r) (rowsN k r l s) (rowsN k r l t) u f g

def FN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NL k r z z' l (Q.uC k r l Y) J)

end defs

def JDRBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * starRingEnd ℂ (∏ a, c a)) • NL k r z z' 0 (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)

def JDRTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 1 0 (Q.resG k r (Fin.last r) J) c g

def JDRStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FN k r z z' Y J (Fin.last r) + Q.crd (Formalism.QuantumDeterminants.pOp ⟨r - 1, by omega⟩) (FN k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.ciOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FN k r z z' Y J ⟨l + 1, by omega⟩ + Q.crd (Formalism.QuantumDeterminants.pOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.ciOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRChainP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 1 0 (Q.crd (Q.cmp (Q.vAB r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vAB r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRConseq : Prop := JDRTop → JDRStepA → JDRStepB → JDRChainP

theorem jDRRadP_of_parts (hB : JDRBeta) (hT : JDRTop) (hA : JDRStepA) (hS : JDRStepB) (hC : JDRConseq) :
    JDRRadP := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hBσ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hx
  have h1 := hBσ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := congrArg Neg.neg (hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hx)
  clear hBσ hCh hB hT hA hS hC
  simp only [Pi.neg_apply, neg_neg] at h2
  simp only [rhGrp, dMul, drbF, Pi.add_apply] at h2 ⊢
  rw [← h2]
  simp only [FN, Q.resG, h1]
  simp only [smul_smul, smul_neg, neg_smul]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableInvCube
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GSup (S : C.HidaSetting E Wp Wq) (ε : ℝ) (b n : ℕ) (P : ℝ) : Prop :=
  ∀ w' ∈ S.base.Wall, S.base.cnt w' + n * C.Kst ≤ S.Ntop →
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : crystallineComparison.V S.f, Good t →
          (KB.NstV S ε (b + n - 1) n w' Y κ t t).re ≤
            P * ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ

theorem integrable_inv_cube : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem zero_mem_dual {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) : (0 : crystallineComparison.V f) ∈ crystallineComparison.dualSet La := by
  intro z _; simp [Lat.psi_zero]

theorem one_le_tsum_mL {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (g : ℝ)
    (hs : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :
    1 ≤ ∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := by
  have := hs.le_tsum (⟨0, zero_mem_dual La⟩ : crystallineComparison.dualSet La) (fun σ _ => mL_nonneg K L hL _)
  simpa [mL_zero] using this

theorem gN_one_reg (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (w : S.W) (h h' : C.LPt) (hh : D.ptSize h = b - 1)
    (hh' : D.ptSize h' = b - 1) :
    ContinuousOn (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) {0}ᶜ ∧
    Integrable (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) := by
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hC⟩, -⟩ := hI v ε hε b hb hbr w h h' hh hh'
  have e : b + 1 - 1 = b := by omega
  rw [e]
  have hcongr : ∀ c ∈ ({0}ᶜ : Set ℂ), φ c / (S.sizeAt v (w.1 v) : ℂ) =
      KB.gN S v ε b (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
    intro c hc
    unfold KB.gN
    rw [hφ c hc]
  have hφi : Integrable φ :=
    Integrable.mono' (integrable_inv_cube.const_mul Cφ) hφc.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hφc.div_const _).continuousOn.congr fun c hc => (hcongr c hc).symm, ?_⟩
  refine (hφi.div_const (S.sizeAt v (w.1 v) : ℂ)).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with c hc
  exact hcongr c hc

def SumBound (f : ℕ) (Cs : ℝ) : Prop :=
  ∀ (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2)

theorem size_step (f : ℕ) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (dl R g : ℝ) (hdl : 0 ≤ dl) (hR : 0 < R) (hg : 0 < g)
    (L thr : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v ∧ L v ≤ thr v) (M V : ℝ) (hM : M ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2))
    (hV : dl * (∏ v, Cs * (1 + (R * thr v / g) ^ 2)) / R ^ (2 * f) ≤ V) : dl * M / R ^ (2 * f) ≤ V := by
  refine le_trans ?_ hV
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (hM.trans ?_) hdl
  refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have h1 : R * L v / g ≤ R * thr v / g := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL v).2 hR.le) hg.le
  have h0 : 0 ≤ R * L v / g := div_nonneg (mul_nonneg hR.le (hL v).1) hg.le
  nlinarith

theorem gsup_one (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hpos : C.ThmPPos S) (hI : KB.IntAll S)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v) (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hbr : b ≤ S.G.r + 1) (hX : ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v) (Cs : ℝ) (hCs1 : 1 ≤ Cs)
    (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b 1) * (∏ v, Cs * (1 + (R * thr S b 1 v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b 1) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b 1 ∧ GSup S ε b 1 P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ X b v := fun v => (hX v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => X b v) hR hg' hL0
  have hM1 := one_le_tsum_mL (Lstd S.f R) C.Kst (fun v => X b v) hL0 (S.g : ℝ) hsm
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) with hMdef
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b 1 := Finset.prod_nonneg fun v _ => (dlB_pos S hg b 1).le
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b 1) * M / R ^ (2 * S.f), by positivity,
    size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b 1) hX M _ hsle hRB, ?_⟩
  intro w' hw' hcnt
  simp only [one_mul] at hcnt ⊢
  obtain ⟨θ, hθ, hWV⟩ := Formalism.FourierDecayAlt.P.plane_wave_bound E Wp Wq S X hW ε hε b hb hbr w' hw' hcnt
  obtain ⟨θ', hθ', hmix⟩ := tsum_mix (S.base.Wb (S.base.cnt w' + C.Kst))
    (fun σ : crystallineComparison.dualSet (Lstd S.f R) => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith)
    (fun σ => θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))) (fun σ => hθ _)
  refine ⟨θ', hθ', fun Y hY κ hκ t ht => ?_⟩
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + 1 - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(1, c)]) (C.loc (S.σ v) h' ++ [(1, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + 1 - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(1, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(1, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  have hreg := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) =>
    gN_one_reg S hI v ε hε b hb hbr w' (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [JCx1.needs.ptSize_loc]; exact hY h hh) (by rw [JCx1.needs.ptSize_loc]; exact hY h' hh')
  set N0 : S.W → ℝ := fun u => S.base.N0 ε (b - 1) u Y κ
  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd S.f R),
      ‖Hh Y κ (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h'))
        ((S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
          ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u := by
    intro σ _
    exact bound_mL C.Kst (fun v => X b v) hL0 _ _ _ (hWV Y hY κ hκ _ _)
  have hH := herglotz_plain (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b 1)
    (fun _ => dlB_pos S hg b 1)
    (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h')) (fun _ _ _ _ => rfl)
    (Lstd S.f R)
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
      ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u)
    (hmix N0).1 (fun σ hσ => hF σ hσ)
    t {t} (by simp)
  rw [(hmix N0).2, hcov, Finset.sum_singleton] at hH
  have hN : Nz Y κ D t = (KB.NstV S ε (b + 1 - 1) 1 w' Y κ t t).re := by
    simp only [Nz, if_pos ht]
    rw [nstV_eq]
    rfl
  rw [hN] at hH
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  linarith [hH]

end

end Formalism.FourierDecayAlt.P.PBC
end

