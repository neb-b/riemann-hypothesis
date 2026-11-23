module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blkT (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * c)]
  | [], b => by simp [D.toStd, D.ptSize]
  | (s', t) :: rest, b => by
    have ih := toStd_append_blkT r g s c rest (b + s')
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

section rr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_top_eq (hVT : Top.VecVTypes) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (P1 Q1 : C.LPt) (hP : D.IsLocPt P1 (P.r + 1)) (hQ : D.IsLocPt Q1 (P.r + 1)) :
    p.RR F (P.r + 1) w P1 Q1 = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w P1 Q1 := by
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hP, hQ⟩, dite_eq_right (by omega), if_pos rfl]
  split_ifs with hw
  · subst hw
    set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
    by_cases h1 : 0 < D.ptG TT P.r P1
    · by_cases h2 : 0 < D.ptG TT P.r Q1
      · exact (Formalism.FourierDecayAlt.P.top_of_empty hVT Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F P1 Q1 p.hP p.hF hP hQ
          h1 h2).symm
      · unfold Top.topOf
        rw [vecV_of_G _ _ _ _ _ h2, hsInner_zero_right']
        symm
        refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
        rw [p.Θ.nil, vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, hsInner_zero_right', mul_zero]
    · unfold Top.topOf
      rw [vecV_of_G _ _ _ _ _ h1, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left]
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rw [p.Θ.nil, vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left, mul_zero]
  · rfl

end rr

section gramtop

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev HV (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v))

def vecT (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (s : ℕ)
    (t : ℂ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) (P : C.LPt) : HV S v :=
  if D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1) then
    B.hsVec (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
      (stdS S (P ++ [(s, t)]))))
  else 0

def omT (S : C.HidaSetting E Wp Wq) (s : ℕ) (t : ℂ) (P : C.LPt) : ℝ :=
  √(nnS S (P ++ [(s, t)])) / bS S (P ++ [(s, t)])

def del2 (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) : ℝ :=
  √((Top.cW (D.parOf S v) (p v).l0 w e ρ).re) * √((Top.cW (D.parOf S v) (p v).l0 w e ρ).re)

theorem second_defect_nonneg (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) : 0 ≤ del2 S p v w e ρ :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem gN_top (hVT : Top.VecVTypes) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (s : ℕ)
    (hs : 2 ≤ s) (t : ℂ) (w : List C.Letter) (P Q : C.LPt) (hP : D.ptSize P + s = S.G.r + 1)
    (hQ : D.ptSize Q + s = S.G.r + 1) :
    KB.gN (setC S p F) v ε (S.G.r + 1) w (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      (omT S s t P : ℂ) * (omT S s t Q : ℂ) * ((1 / (ΓS S (S.G.r + 1) * S.sizeAt v w) : ℝ) : ℂ) *
        ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty (D.parOf S v),
          (del2 S p v w e ρ : ℂ) * gramH (vecT S p F v ε s t w e ρ) P Q := by
  have hgpos := g_pos_of_built hB
  by_cases hloc : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1) ∧ D.IsLocPt (Q ++ [(s, t)]) (S.G.r + 1)
  · obtain ⟨hPl, hQl⟩ := hloc
    rw [gN_setC hB]
    have hPs : D.IsLocPt (stdS S (P ++ [(s, t)])) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hPl
    have hQs : D.IsLocPt (stdS S (Q ++ [(s, t)])) (S.G.r + 1) := (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hQl
    rw [rr_top_eq hVT (p v) (F v ε) w _ _ hPs hQs]
    have eP : stdS S (P ++ [(s, t)]) = stdS S P ++ [(s, (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r
        ((1 + D.ptSize P : ℕ) : ℤ) (s : ℤ) : ℝ) * Complex.I ^ (s - 1) * t)] := toStd_append_blkT _ _ _ _ _ _
    have eQ : stdS S (Q ++ [(s, t)]) = stdS S Q ++ [(s, (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r
        ((1 + D.ptSize Q : ℕ) : ℤ) (s : ℤ) : ℝ) * Complex.I ^ (s - 1) * t)] := toStd_append_blkT _ _ _ _ _ _
    have hPQ : D.ptSize P = D.ptSize Q := by omega
    have hgr : ∀ e ρ, gramH (vecT S p F v ε s t w e ρ) P Q =
        B.hsInner (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
          (stdS S (P ++ [(s, t)]))))
          (((p v).TP.E ρ).comp (D.vecV (p v).T.base (p v).ν' (p v).m₀ ((p v).Θ.Θ w e (F v ε))
          (stdS S (Q ++ [(s, t)])))) := by
      intro e ρ
      unfold gramH vecT
      rw [if_pos hPl, if_pos hQl]
      rfl
    simp only [hgr]
    rw [eP, eQ, hPQ]
    rw [topOf_big (p v) (F v ε) w (stdS S P) (stdS S Q) s _ _ hs (by rw [stdS_size]; omega)
      (by rw [stdS_size]; omega)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
    unfold del2 omT
    push_cast
    ring
  · rw [gN_setC_zero hB F v ε (S.G.r + 1) w _ _ hloc]
    symm
    have hz : ∀ e ρ, gramH (vecT S p F v ε s t w e ρ) P Q = 0 := by
      intro e ρ
      unfold gramH vecT
      by_cases h1 : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1)
      · rw [if_neg (fun h2 => hloc ⟨h1, h2⟩), inner_zero_left]
      · rw [if_neg h1, inner_zero_right]
    simp [hz]

theorem hsVec_smul {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (c : ℂ) (X : Wq' →L[ℂ] Wp') :
    B.hsVec (c • X) = c • B.hsVec X := by
  unfold B.hsVec; rfl

theorem hsVec_sum {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {ι : Type} (s : Finset ι) (X : ι → Wq' →L[ℂ] Wp') :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold B.hsVec; simp; rfl
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← ih]
    unfold B.hsVec; rfl

theorem vecT_deg (hDT : KB.DegTop) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ)
    (hF : KB.CptCoef (p v).T.base (F v ε)) (s : ℕ) (hs : 2 ≤ s) (t : ℂ) (ht : t ≠ 0) (d : ℕ) (hd : d + s = S.G.r + 1)
    (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty (D.parOf S v)) {K : ℕ} (grid : Fin K → Fin (d + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b))
    (hcut : ∀ n : Fin K → Fin (d + 1), KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) w))
    (P : C.LPt) (hP : D.ptSize P = d) :
    vecT S p F v ε s t w e ρ P =
      ((((-1 : ℂ) ^ (s - 1) / ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) *
        Complex.I ^ (s - 1) * t)) ^ K)⁻¹) •
        ∑ n : Fin K → Fin (d + 1), (((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ)) •
          vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) ρ P := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  set τ : ℂ := (((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) *
    Complex.I ^ (s - 1) * t with hτ
  have hτ0 : τ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ Complex.I_ne_zero)) ht
    have : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) := zpow_pos (by positivity) _
    exact_mod_cast this.ne'
  have hc0 : ((-1 : ℂ) ^ (s - 1) / τ) ^ K ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (pow_ne_zero _ (by norm_num)) hτ0)
  by_cases hloc : D.IsLocPt (P ++ [(s, t)]) (S.G.r + 1)
  · have eP : stdS S (P ++ [(s, t)]) = stdS S P ++ [(s, τ)] := by
      rw [hτ, ← hP]; exact toStd_append_blkT _ _ _ _ _ _
    have hPs : D.IsLocPt (stdS S P ++ [(s, τ)]) ((D.parOf S v).r + 1) := by
      rw [← eP]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).2 hloc
    have hdeg : ∀ (h : C.LPt) (hh : D.ptSize h = d), D.IsLocPt (h ++ [(s, τ)]) ((D.parOf S v).r + 1) →
        ((-1 : ℂ) ^ (s - 1) / τ) ^ K • (p v).V ((p v).Θ.Θ w e (F v ε)) (h ++ [(s, τ)]) =
          ∑ n : Fin K → Fin (d + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) •
            (p v).V ((p v).Θ.Θ (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) (F v ε))
              (h ++ [(s, τ)]) := by
      intro h hh hloc'
      subst hh
      exact hDT _ _ (D.parOf S v) (p v) (F v ε) s w h τ K grid e Cb (by rw [hl0]; exact hInD) hs hloc' hF hinj
        (fun n => by rw [hl0]; exact hcut n)
    have h1 := hdeg (stdS S P) (by rw [stdS_size]; exact hP) hPs
    have hV : (p v).V ((p v).Θ.Θ w e (F v ε)) (stdS S P ++ [(s, τ)]) =
        (((-1 : ℂ) ^ (s - 1) / τ) ^ K)⁻¹ • ∑ n : Fin K → Fin (d + 1), ((∏ b, F7.lagCo (grid b) (n b) : ℝ) : ℂ) •
          (p v).V ((p v).Θ.Θ (KB.plusW (List.ofFn fun b => grid b (n b)) w) (KB.firstSt _ e) (F v ε))
            (stdS S P ++ [(s, τ)]) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    unfold vecT
    rw [if_pos hloc]
    simp only [if_pos hloc]
    rw [eP]
    change B.hsVec (((p v).TP.E ρ).comp ((p v).V ((p v).Θ.Θ w e (F v ε)) (stdS S P ++ [(s, τ)]))) = _
    have hcomp (a : Finset (Fin K → Fin (d + 1)))
        (X : (Fin K → Fin (d + 1)) → Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
        ((p v).TP.E ρ).comp (∑ n ∈ a, X n) = ∑ n ∈ a, ((p v).TP.E ρ).comp (X n) := by
      induction a using Finset.induction_on with
      | empty => simp
      | insert n a hn ih => simp [hn, ContinuousLinearMap.comp_add, ih]
    rw [hV, ContinuousLinearMap.comp_smul, hcomp, hsVec_smul, hsVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ContinuousLinearMap.comp_smul, hsVec_smul]
    rfl
  · unfold vecT
    simp only [if_neg hloc, smul_zero, Finset.sum_const_zero]

end gramtop

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothGConst
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Ops

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


variable (k ρ) in
def ParOK (T : (Q.Mx k ρ → E) → Q.Mx k ρ → E) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ →
  ∀ f : Par → Q.Mx k ρ → E, PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) →
    PBI.ParFam k ρ U₀ (fun q => T (f q.1) (Matrix.of q.2)) ∧
    (∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∀ W : Set (Par × Mt k ρ), IsOpen W → q ∈ W →
      (∀ q' ∈ W, Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q'.1 (Matrix.of q'.2) = 0) →
      T (f q.1) (Matrix.of q.2) = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (fi : Q.Mx k ρ → E) (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ y' ∈ V, Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) → fi (Matrix.of y') = ∫ Z, f Z (Matrix.of y') ∂ν) →
      T fi (Matrix.of y) = ∫ Z, T (f Z) (Matrix.of y) ∂ν


variable (k ρ) in
def SmoothG (a : Q.Mx k ρ → ℂ) : Prop :=
  ∀ y₀ : Mt k ρ, Matrix.of y₀ ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Mt k ρ)) (F : Mt k ρ → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ y ∈ U, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → a (Matrix.of y) = F y

theorem smoothG_const (s : ℂ) : SmoothG k ρ (fun _ => s) := fun _ _ =>
  ⟨Set.univ, fun _ => s, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothG_mul {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g * b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y * F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).mul (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) * b (Matrix.of y) = F y * F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem smoothG_sub {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g - b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y - F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).sub (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) - b (Matrix.of y) = F y - F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem parFam_congr {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f)
    (h : ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = g q) (hU₀ : IsOpen U₀) :
    PBI.ParFam k ρ U₀ g := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U ∩ U₀, F, hU.inter hU₀, ⟨hqU, hq⟩, hF.mono Set.inter_subset_left,
    fun q hq' hG' => (h q hq'.2 hG').symm.trans (hfF q hq'.1 hG')⟩

theorem parFam_smulG {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a (Matrix.of q.2) • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', A, hU', hqU', hA, haA⟩ := ha q₀.2 hG
  refine ⟨U ∩ Prod.snd ⁻¹' U', fun q => A q.2 • F q, hU.inter (hU'.preimage continuous_snd), ⟨hqU, hqU'⟩, ?_,
    fun q hq' hG' => ?_⟩
  · exact (hA.comp contDiff_snd.contDiffOn (fun q (hq : q ∈ U ∩ Prod.snd ⁻¹' U') => hq.2)).smul (hF.mono Set.inter_subset_left)
  · show a (Matrix.of q.2) • f q = A q.2 • F q
    rw [haA q.2 hq'.2 hG', hfF q hq'.1 hG']

theorem parOK_id : ParOK k ρ (E := E) (fun f => f) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨hf, fun q _ hG W _ hqW hW => hW q hqW hG, fun ν _ Kp _ _ fi y V _ hyV hyG _ hi => hi y hyV hyG⟩

theorem parOK_zero : ParOK k ρ (E := E) (fun _ _ => 0) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨parFam_zero, fun _ _ _ _ _ _ _ => rfl, fun ν _ Kp _ _ fi y V _ _ _ _ _ => by simp⟩

theorem parOK_congr {T T' : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) (h : ∀ f g, T f g = T' f g) :
    ParOK k ρ T' := by
  have e : T = T' := funext fun f => funext fun g => h f g
  rw [← e]; exact hT

theorem parOK_add {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f g => T₁ f g + T₂ f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  refine ⟨parFam_add a₁ a₂, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show T₁ (f q.1) (Matrix.of q.2) + T₂ (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, b₂ q hq hG W hW hqW hz, add_zero]
  · have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    show T₁ fi (Matrix.of y) + T₂ fi (Matrix.of y) = ∫ Z, (T₁ (f Z) (Matrix.of y) + T₂ (f Z) (Matrix.of y)) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, c₂ ν Kp hKp hν fi y V hV hyV hyG hKV hi,
      integral_add (parFam_integrable a₁ hKp hν hyG hKU) (parFam_integrable a₂ hKp hν hyG hKU)]

theorem parOK_smulG {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (hT : ParOK k ρ T) : ParOK k ρ (fun f g => a g • T f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := hT Par U₀ hU₀ f hf
  refine ⟨parFam_smulG ha a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show a (Matrix.of q.2) • T (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, smul_zero]
  · show a (Matrix.of y) • T fi (Matrix.of y) = ∫ Z, a (Matrix.of y) • T (f Z) (Matrix.of y) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, integral_smul]

theorem parOK_csmul (s : ℂ) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) :
    ParOK k ρ (fun f g => s • T f g) := parOK_smulG (smoothG_const s) hT

theorem parOK_neg {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) : ParOK k ρ (fun f g => -T f g) :=
  parOK_congr (parOK_csmul (-1) hT) (fun f g => by simp)

theorem parOK_comp {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f => T₁ (T₂ f)) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ (fun Z => T₂ (f Z)) a₂
  refine ⟨a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · refine b₁ q hq hG (W ∩ U₀) (hW.inter hU₀) ⟨hqW, hq⟩ (fun q' hq' hG' => ?_)
    exact b₂ q' hq'.2 hG' W hW hq'.1 hz
  · refine c₁ ν Kp hKp hν (T₂ fi) y V hV hyV hyG hKV (fun y' hy' hG' => ?_)
    exact c₂ ν Kp hKp hν fi y' V hV hy' hG' hKV hi

theorem parOK_sum {ι : Type} (s : Finset ι) {T : ι → (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (h : ∀ i ∈ s, ParOK k ρ (T i)) : ParOK k ρ (fun f g => ∑ i ∈ s, T i f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact parOK_congr parOK_zero (fun f g => by simp)
  | insert a s ha ih =>
    have := parOK_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact parOK_congr this (fun f g => by simp [Finset.sum_insert ha])

theorem parOK_foldr (L : List ((Q.Mx k ρ → E) → Q.Mx k ρ → E)) (hL : ∀ T ∈ L, ParOK k ρ T) :
    ParOK k ρ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact parOK_id
  | cons T L ih =>
    exact parOK_comp (hL T List.mem_cons_self) (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))

end Ops

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordFamilySymbolHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_family_apply_holds : WFamApp := by
  intro d α L F c v x
  simp [wfam, WOp.app, List.map_append, List.sum_append, vfW, Function.comp_def]

theorem word_family_symbol_holds : WFamSymb := by
  intro d α L F c j x ξ τ hj hτ
  have h0 : ¬ (0 = j) := by omega
  simp only [wfam, WOp.symb, List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, h0, if_false, add_zero]
  congr 1
  refine List.map_congr_left (fun t ht => ?_)
  simp only [Function.comp_apply, List.length_map]
  split_ifs with hl
  · congr 1
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left (fun X hX => hτ t ht X hX))
  · rfl

theorem trace_real_lie_holds : TrRealLie := by
  intro k r A X hA hX
  have hH : (Hpk k r)ᴴ = Hpk k r := Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose k r
  have hH2 : Hpk k r * Hpk k r = 1 := WeylGroupFacts.hpk_sq
  have eA : Aᴴ = -(Hpk k r * A * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hA
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have eX : Xᴴ = -(Hpk k r * X * Hpk k r) := by
    have h := congrArg (· * Hpk k r) hX
    simp only [add_mul, zero_mul, Matrix.mul_assoc, hH2, Matrix.mul_one] at h
    rw [eq_neg_iff_add_eq_zero, Matrix.mul_assoc]; exact h
  have hstar : star (Matrix.trace (A * X)) = Matrix.trace (A * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, eX, eA, neg_mul_neg]
    calc Matrix.trace (Hpk k r * X * Hpk k r * (Hpk k r * A * Hpk k r))
        = Matrix.trace (Hpk k r * (X * (Hpk k r * Hpk k r) * A * Hpk k r)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * (Hpk k r * Hpk k r) * A * Hpk k r) * Hpk k r) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * A) := by simp only [Matrix.mul_assoc, hH2, Matrix.mul_one]
      _ = Matrix.trace (A * X) := Matrix.trace_mul_comm _ _
  exact Complex.conj_eq_iff_re.mp hstar

theorem smooth_on_levels_holds : CkLevOn := by
  intro k r m Dm E _ _ f hf g₀ hg₀
  have hg₀' : g₀ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hg₀.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg₀.2⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀'
  exact ⟨U, F, hU, hgU, by exact_mod_cast hF, fun g hg hgG => hfF g hg ⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩⟩

theorem operator_capelli_vector : OpCVOf := opCVOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_right_capelli : OpCapROf := opCapROf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

theorem operator_left_capelli : OpCapLOf := opCapLOf_of word_family_apply_holds word_family_symbol_holds trace_real_lie_holds smooth_on_levels_holds

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

