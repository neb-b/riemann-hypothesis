module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0196
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0011
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0195

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapARep
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp

open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

theorem exists_polyOp_qminor_sum {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : ι → Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) (a j) (b j) u F g := by
  have h := fun j => qminorWordSum k r t (a j) (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => ?_, fun g => ?_⟩
      · simp [T₀, pTerm]
      · simp [T₀, pTerm]
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      simp [T₀, pTerm]
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl

end Formalism.FourierDecayAlt.P.CutMP.QMinOp

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

noncomputable section

theorem capBeta_pd (k r : ℕ) (c : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capBeta k r c) := by
  unfold capBeta
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE le_rfl a)))) fun a l => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Matrix.mulVec]
  refine pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  refine pd_sum _ fun j _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun c _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul (pd_entry _ _) (pd_const _ 0))

theorem capAlphaV_pd (k r : ℕ) (B : Fin r → Fin (2 * r + k + 1)) : U.IsPolyDeg r (capAlphaV k r B) := by
  unfold capAlphaV
  refine pd_det (fun g => Matrix.of fun a l : Fin r =>
    ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE le_rfl a))) (B l)) fun a l => ?_
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine pd_sum _ fun m _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  refine pd_sum _ fun l _ => pd_mono (by norm_num : 1 + 0 ≤ 1) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun i _ => pd_mono (by norm_num : 0 + 1 ≤ 1) (pd_mul (pd_const _ 0) (pd_star_entry _ _))

theorem capelli_representation_holds : JDACapRep := by
  intro k r Wp Wq _ _ _ _ _ y
  classical
  have hκ : r ≤ (r + 1) * (2 * r + k + 1) := by nlinarith
  have ho : r ≤ 2 * r + k + 1 := by omega
  obtain ⟨Θ, hP, hO, hE⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun c : Fin r → Fin (2 * r + k + 1) => StrictMono c) (fun _ => C3.xR k r r le_rfl)
    (fun c => c) (capBeta k r) (fun c _ => capBeta_pd k r c) (Q.uC k r 0 y)
  obtain ⟨Θv, hPv, hOv, hEv⟩ := QMinOp.exists_polyOp_qminor_sum (Wp := Wp) (Wq := Wq)
    (Finset.univ.filter fun B : Fin r → Fin (2 * r + k + 1) => StrictMono fun l => C3.keyS k r (B l)) (fun B => B)
    (fun _ => C3.sR k r r le_rfl) (capAlphaV k r) (fun B _ => capAlphaV_pd k r B)
    (y - ((2 * r + k : ℕ) : ℂ) / 2 + (r : ℂ) - 1)
  refine ⟨Θ, Θv, QMinOp.polyOp_mono hP ho hκ, QMinOp.polyOp_mono hPv ho hκ, hO, hOv, fun F g hg hF => ?_,
    fun F g hg hF => ?_⟩
  · rw [hO] at hF
    rw [hE {g} F hF g rfl hg, Finset.sum_filter]
    rfl
  · rw [hOv] at hF
    rw [hEv {g} F hF g rfl hg, Finset.sum_filter]
    have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hg
    simp only [capAv, C3.AAvop, capAlphaV, hinv]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
section
noncomputable section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.PBI

def FrameTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ c : Fin P.r → ℂ, c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∃ T : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' →ₗ[ℂ]
        Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π',
      (∀ Ψ c' g, (T Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g =
        (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
        (e : Wd.Ix (Fin w.length)) (c' : Fin (JC.parLev P P.r).r → ℂ) (g : B.Mat P.k (P.r - P.r)),
        g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
            c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g

def ParFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
    [NormedSpace ℝ Par] (k ρ : ℕ) (U₀ : Set (Par × Mt k ρ)) (f : Par × Mt k ρ → E) : Prop :=
  ∀ q₀ ∈ U₀, Matrix.of q₀.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Par × Mt k ρ)) (F : Par × Mt k ρ → E),
    IsOpen U ∧ q₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = F q

def FrameParam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ (w : List C.Letter), Fr.admitted st (D.positionted w) →
    ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
      [BorelSpace Par] (U₀ : Set (Par × Mt P.k (P.r - P.r))), IsOpen U₀ →
      U₀ ⊆ Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} →
    ∀ (Ψ : Par → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
      (Ψf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
      (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ Z e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e y) →
      (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Ψf q.1 e q.2)) →
      ∃ Φf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Φf Z e y) ∧
        (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Φf q.1 e q.2)) ∧
        (∀ (K : Set (Par × Mt P.k (P.r - P.r))),
          (∀ e q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Ψf q.1 e q.2 = 0) →
          ∀ e q, q ∈ U₀ → Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ closure K → Φf q.1 e q.2 = 0) ∧
        ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
        ∀ (Ψi : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
            (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') (y : Mt P.k (P.r - P.r)) (V : Set (Mt P.k (P.r - P.r))),
          IsOpen V → y ∈ V → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Kp ×ˢ V ⊆ U₀ →
          (∀ e c y', y' ∈ V → Matrix.of y' ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
            (Ψi e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y') =
              ∫ Z, Ψf Z e y' ∂ν) →
          ∀ e c, (P5.act (Fr.ofWord L st (D.positionted w)).F Ψi e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z e y ∂ν

def RadWord : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ e : Wd.Ix (Fin w.length),
      Top.IsRadOf P p.T.base (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e)
        (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e)

def hcell {r : ℕ} (c : Fin r → ℂ) : C.LPt := List.ofFn fun j => (1, c j)

theorem ptSize_hcell {r : ℕ} (c : Fin r → ℂ) : D.ptSize (hcell c) = r := by
  simp [hcell, D.ptSize, List.map_ofFn, Function.comp_def]

def RadWordSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
          c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
            (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) (hcell c))) g

def PicSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (Φ_G : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G (hcell c))) g

end Formalism.FourierDecayAlt.P.PBI
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeNormPower
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R

def lstN (K m : ℕ) (y : Fin K → ℝ) : List ℝ :=
  List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lstN_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    lstN K ((a : ℕ) + 1) (Function.update y a t) = t :: lstN K a y := by
  unfold lstN
  rw [List.ofFn_succ]
  congr 1
  · rw [dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dite_eq_left (by simp; omega), dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lstN_full (K : ℕ) (z : Fin K → ℝ) : lstN K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold lstN
  congr 1
  funext b
  rw [dite_eq_left (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

theorem cutWord_plusW {P : M.Par} {l0 : ℕ} {w : List C.Letter} :
    ∀ ys : List ℝ, KB.CutWord P l0 (KB.plusW ys w) → KB.CutWord P l0 w
  | [], h => h
  | _ :: ys, h => cutWord_plusW ys (cutWord_tail h)

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def aaIter {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (F0 : B.Mat k r → (Wq →L[ℂ] Wp)) :
    List ℝ → B.Mat k r → (Wq →L[ℂ] Wp)
  | [] => F0
  | y :: ys => aaTop Bs y (aaIter Bs F0 ys)

def aPIter {V : Type} [AddCommGroup V] [Module ℂ V] {r : ℕ} (L : R.LevelData (Q.Pr V) r) : List ℝ → V → V
  | [], Ψ => Ψ
  | y :: ys, Ψ => (TL.aP L (y : ℂ)).1 (aPIter L ys Ψ)

theorem aaIter_rad (hRA : RadAATop) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ)
    (hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0) {F0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF0 : KB.CptCoef Bs F0) {Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'} (hΨ : Top.IsRadOf P Bs Ψ F0) :
    ∀ ys : List ℝ, KB.CptCoef Bs (aaIter Bs F0 ys) ∧ Top.IsRadOf P Bs (aPIter L ys Ψ) (aaIter Bs F0 ys) := by
  intro ys
  induction ys with
  | nil => exact ⟨hF0, hΨ⟩
  | cons y ys ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := hRA Wp Wq P Bs X μ L st l0 y hD _ h1
    exact ⟨h3, h4 _ h2⟩

theorem rad_plusW (hWS : TL.WordStep) (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (hD : P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X μ L st p.l0) (w : List C.Letter)
    (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (e : Ix (Fin w.length)) :
    ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      P5.act ((Fr.ofWord L st (D.positionted (KB.plusW ys w))).F * P5.bTall L (D.positionted (KB.plusW ys w)))
          (Top.firstStateVector Φ) (KB.firstSt ys e) =
        aPIter L ys (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) := by
  intro ys
  induction ys with
  | nil => intro; rfl
  | cons y ys ih =>
    intro hc
    have h1 := rad_plus hWS P p X μ L st hD (KB.plusW ys w) y hc Φ (KB.firstSt ys e)
    exact h1.trans (congrArg (fun Ψ => (TL.aP L (y : ℂ)).1 Ψ) (ih (cutWord_tail hc)))

end deg

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBN

theorem degree_top_of_parts : PBN.DegTopOfParts := by
  intro hWS hRA hPT hDC Wp Wq _ _ _ _ _ _ P p F s w h t K grid e Cb hCb hs hloc hF hgrid hcut
  obtain ⟨X, μ, L, st, hD, hTL⟩ := p.hΘ
  have hcw : KB.CutWord P p.l0 w := cutWord_plusW _ (hcut fun _ => 0)
  obtain ⟨F0, hF0, hF0eq, hV0⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hcw
  obtain ⟨Φ, hΦ⟩ := radExists p hF
  have hΨ := isRadOf_congr p.T.base (hTL w hcw F hF Φ hΦ e) hF0eq
  have hIt := aaIter_rad hRA P p.T.base X μ L st p.l0 hD hF0 hΨ

  have hVit : ∀ ys : List ℝ, KB.CutWord P p.l0 (KB.plusW ys w) →
      p.V (aaIter p.T.base F0 ys) (h ++ [(s, t)]) =
        p.V (p.Θ.Θ (KB.plusW ys w) (KB.firstSt ys e) F) (h ++ [(s, t)]) := by
    intro ys hc
    obtain ⟨Fn, hFn, hFneq, hVn⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F (KB.plusW ys w) (KB.firstSt ys e) Cb hCb hF hc
    rw [hVn]
    have hrad := isRadOf_congr p.T.base (hTL (KB.plusW ys w) hc F hF Φ hΦ (KB.firstSt ys e)) hFneq
    rw [rad_plusW hWS P p X μ L st hD w Φ e ys hc] at hrad
    exact vecV_eq_of_rad hDC p (hIt ys).1 hFn (hIt ys).2 hrad _
  set W : ℕ → (Fin K → ℝ) → (Wq →L[ℂ] Wp) := fun m y => p.V (aaIter p.T.base F0 (lstN K m y)) (h ++ [(s, t)])
    with hW
  have hPS : F7.PolyStep K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W := by
    intro a y
    obtain ⟨c, hc, hpoly⟩ := hPT Wp Wq P p (aaIter p.T.base F0 (lstN K a y)) s h t hs hloc (hIt _).1
    refine ⟨c, hc, fun t' => ?_⟩
    simp only [hW]
    rw [lstN_succ]
    exact hpoly t'
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound (Wq →L[ℂ] Wp) K (D.ptSize h) (fun _ => ((-1) ^ (s - 1) / t : ℂ)) W
    (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hE
  have hW0 : W 0 (fun _ => 0) = p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) := by
    simp only [hW, lstN, List.ofFn_zero, aaIter]
    rw [hV0]
  rw [hW0] at hE
  rw [hE]
  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW]
  rw [lstN_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (D.ptSize h + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2, hVit _ (hcut _)]

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LenEqLenI
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem ntop_eq_N'' (S : C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = S.G.N := by
  simp only [C.HidaSetting.Ntop, Sz.Glob.N, C.Kst]; push_cast; ring

theorem len_eq_lenI' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem glob_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem lenI_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  rw [len_eq_lenI'] at hlen
  have hN : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ S.Ntop := by
    have : 1 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
    exact_mod_cast this
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

theorem lamTop_thr (hC : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (s : ℕ) (hs2 : 2 ≤ s)
    (hsr : s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamTop S (S.G.r + 2 - s) v ∧ 2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hlen := lenI_posT hB (Fin.pos v)
  have hsz : S.base.szL (S.G.r + 2 - s) s v = 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l (S.G.r + 2 - s) (S.pl v) := by
    show (if S.G.r + 2 - s + s ≤ S.G.r + 1 then _ else _) = _
    rw [if_neg (by omega)]
  rw [hsz]
  have hsA : ∀ one, 0 ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := fun one => supA_nonneg S hg hk v one
  have hFT := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hlen
    (hC.trans hCA) hsA).2 (S.G.r + 2 - s) (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)))
    (by omega) (Real.exp_pos 1).le le_rfl (pow_nonneg (div_nonneg (by unfold Sz.Glob.N; positivity) hlen.le) _) le_rfl
  unfold lamTop
  have e : ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) = ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) := rfl
  linarith [hFT]

end thr

end

end Formalism.FourierDecayAlt.P.PBL
end

