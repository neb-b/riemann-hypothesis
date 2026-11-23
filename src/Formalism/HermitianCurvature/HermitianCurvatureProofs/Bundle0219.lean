module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0213
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProdOfFnMap
section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def uS (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  uY S p F v ε j hj w (Y.image fun h => h ++ [blk]) (h ++ [blk])

theorem uS_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) (hh : h ∈ Y) :
    uS S p F v ε j hj w Y blk h = uB S p F v ε j hj w (h ++ [blk]) :=
  uY_mem S p F v ε j hj w _ _ (Finset.mem_image_of_mem _ hh)

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem prod_ofFn_map' {K : ℕ} (g0 : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn g0).map g).prod = ∏ c, g (g0 c) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

end blockL

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiContOf
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem psi_cont_of {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : B.Mat k r => psi k r z c g) := by
  have hl : Continuous fun g : B.Mat k r => ell k r z g := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
  unfold psi
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul hl))))

theorem krI_aesm {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (y₀ : B.Mat k (p + ρ))
    (hy₀ : y₀ ∈ B.GV k (p + ρ)) (hD : U.DjU k p ρ y₀ ≠ 0) :
    AEStronglyMeasurable (LeftFubiniLemmas.KrI B0 H y₀) (B0.μW'.prod B0.μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite B0.haarN
  set S := {ξ : Mt k (p + ρ) × Mt k (p + ρ) | Formalism.FourierDecayAlt.P.PBG.InR B0 ξ} with hS
  have hcG := Formalism.FourierDecayAlt.P.unitary_group_closed k (p + ρ)
  have hcW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) B0.z'
  have hmem : ∀ ξ ∈ S, y₀ * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    intro ξ hξ
    refine ⟨hcG.mul_mem _ (hcG.mul_mem _ hy₀ _ hξ.2.1) _ hξ.1.1, ?_⟩
    show U.DjU k p ρ (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0
    rw [LeftFubiniLemmas.djU_mul_UW B0.z' _ _ hξ.1, LeftFubiniLemmas.djU_mul_N _ _ hξ.2]
    exact hD
  have hof1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))) :=
    continuous_fst
  have hof2 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.2 : B.Mat k (p + ρ))) :=
    continuous_snd
  have hc1 : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => y₀ * Matrix.of ξ.2 * Matrix.of ξ.1) :=
    (continuous_const.matrix_mul hof2).matrix_mul hof1
  have hH : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => H (y₀ * Matrix.of ξ.2 * Matrix.of ξ.1)) S :=
    hHc.comp hc1.continuousOn hmem
  have hinv : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    Formalism.FourierDecayAlt.P.PBG.inv_cont_GV.comp hof1.continuousOn (fun ξ hξ => hξ.1.1)
  have hπ : ContinuousOn (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => B0.π' (Matrix.of ξ.1 : B.Mat k (p + ρ))⁻¹) S :=
    B0.π'_cont.comp hinv (fun ξ hξ => hcW.inv_mem _ hξ.1)
  have hψ : Continuous (fun ξ : Mt k (p + ρ) × Mt k (p + ρ) => star (psi k (p + ρ) B0.z' cStd (Matrix.of ξ.2))) :=
    continuous_star.comp ((psi_cont_of B0.z' cStd).comp hof2)
  have hK : ContinuousOn (LeftFubiniLemmas.KrI B0 H y₀) S := hψ.continuousOn.smul (hH.clm_comp hπ)
  have hm := hK.aestronglyMeasurable (μ := B0.μW'.prod B0.μN) (Formalism.FourierDecayAlt.P.PBG.isClosed_InR B0).measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := S) (Formalism.FourierDecayAlt.P.PBG.ae_inR B0)] at hm

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem torus_step (hTC : TorusCell) (hGP : GaugeP) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (l : Fin r) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    Q.resG k r (Fin.last r) (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
      y • Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c g₀ +
        pOp l (fun c' => Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c' g₀) c := by
  have hγ := hcell c hc
  set h : Mx k r → E := ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) with hh
  set H : (Fin r → ℂ) → E := fun c' => h (wCell k r (Fin.last r) c' * g₀) with hH
  have e1 : (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x : SA E hD) :
      Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c * g₀) =
      ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) • H c + pOp l H c := by
    simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
      Submodule.coe_add, Pi.add_apply, ite_true, if_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
      Submodule.coe_smul, Pi.smul_apply]
    rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D h hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l]
  rw [resG_last, e1]
  simp only [resG_last]
  rw [hGP E r (fun a => Mdim k r a - 1) H c hc (hdiff x c hc) l]
  have hw : (y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ) = y + ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    have hl := l.isLt
    have e : Mdim k r l - 1 = 2 * (r - l.val) + k := by simp [Mdim]
    rw [e]
    push_cast [Nat.cast_sub hl.le]
    ring
  rw [hw]
  module

end claim

theorem qminor_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 1 → Fin n) (u : ℂ) :
    qminor E a b u = Tm E u (a 0) (b 0) := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp [List.ofFn_succ]

theorem qminor_zero {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 0 → Fin n) (u : ℂ) :
    qminor E a b u = 1 := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp

section vab

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem vAB_succ (y : ℂ) (i : ℕ) (hi : i < r) (G : (Fin r → ℂ) → V) :
    (Q.vAB r y (i + 1)).1 G = (fun c => y • (Q.vAB r y i).1 G c + pOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) c -
      cOp ⟨i, hi⟩ ((Q.vAB r y i).2 G) c) ∧
    (Q.vAB r y (i + 1)).2 G = ciOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) := by
  simp only [Q.vAB, dif_pos hi]
  exact ⟨funext fun c => rfl, trivial⟩

end vab

section claim2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem leftEq_cut (z : Fin (2 * r + k + 1) → ℂ) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hLf : LeftEq k r z 0 D f) : LeftEq k r z 0 D (cut k r 0 D f) := by
  intro g hg n hn
  rw [cut_of_mem f ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩, cut_of_mem f hg]
  exact hLf g hg n hn

theorem claim (hRR : RightRuleE) (hLR : LeftRuleCell) (hTC : TorusCell) (hGP : GaugeP)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (hWS : ∀ x : SA E hD, resW ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ ∈ WSm r E) :
    ∀ (m : ℕ) (hm : m ≤ r), ∀ P ∈ Tor hD m, ∀ c ∈ OmX r,
      Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r m hm) (C3.xR k r m hm) (y + ((2 * r + k : ℕ) : ℂ) / 2) * P :
          SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        (Q.vAB r y m).1 (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [qminor_zero, one_mul]
    rfl
  · rw [qminor_one]
    have hx0 : C3.xR k r 1 hm 0 = eI k r ⟨0, by omega⟩ := by ext; simp [C3.xR, eI]
    have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨0, by omega⟩ P c hc
    simp only [Fin.val_mk, Nat.cast_zero, sub_zero] at hts
    rw [hx0, hts, (vAB_succ y 0 (show 0 < r by omega) _).1]
    simp [Q.vAB, cOp]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ Tor hD (m + 1) := Tor_mono hD (by omega) hP
    have hP0 : P ∈ Tor hD m := Tor_mono hD (by omega) hP
    set u : ℂ := y + ((2 * r + k : ℕ) : ℂ) / 2 with hu
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ (a : ℕ) (ha : a < m + 2), ∀ l' : Fin r, m + 2 ≤ l'.val → eI k r ⟨a, by omega⟩ ≠ eI k r l' := by
      intro a ha l' hl' e
      have := congrArg Fin.val e
      simp [eI] at this
      omega
    have hR0 : ∀ (x : SA E hD) (l : ℕ) (hl : l < m),
        LaP (x * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0 := by
      intro x l hl
      rw [hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot l (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨l, by omega⟩ ⟨m + 1, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD, LaP (x * EA hD (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot m (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp), if_pos (by simp), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (q : ℕ) (hq : q ≤ m),
        LaP (EA hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
          (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • LaP x := by
      intro x q hq
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 ⟨m + 1, by omega⟩ ⟨q, by omega⟩ (by simp; omega)]
      congr 1
      by_cases hqm : q = m
      · subst hqm
        simp
      · rw [if_neg (by simp; omega), if_neg hqm]
    have hX := Formalism.FourierDecayAlt.P.PBN.chainX1' k r c (EA (E := E) hD) LaP (EA_gl (E := E) hD) m hm2 u hR0 hR1 hL

    set T := Tm (EA (E := E) hD) (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) with hT
    have hTmem : T ∈ Tor hD (m + 1) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EA_mem_Tor hD ⟨m + 1, by omega⟩ le_rfl)
    have hTP : T * P ∈ Tor hD (m + 1) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc

    have eL : Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 2) hm) (C3.xR k r (m + 2) hm) u * P :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 1) (by omega)) (C3.xR k r (m + 1) (by omega)) u *
          (T * P) : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • Q.resG k r (Fin.last r)
          (((qminor (EA hD) (C3.xR k r m (by omega)) (C3.xR k r m (by omega)) u * P : SA E hD) :
            Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ := by
      rw [resG_last, resG_last, resG_last]
      have key : ∀ (s t : ℂ) (a b d : E), a = b - t • d → s • a = s • b - t • (s • d) := by
        intro s t a b d h
        rw [h, smul_sub, smul_comm]
      apply key
      have h2 := hX
      simp only [hLaP_apply, La_apply, mul_assoc] at h2
      exact h2
    rw [eL, ih1, ih0]

    obtain ⟨G', hG'def⟩ : ∃ G' : (Fin r → ℂ) → E,
        G' = resW ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ := ⟨_, rfl⟩
    have hG' : G' ∈ WSm r E := hG'def ▸ hWS P
    have hGG' : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = G' c' := by
      intro c' hc'
      rw [hG'def, wsm_resG_eq _ _ hc']
    have hTS : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ =
          (pOp ⟨m + 1, by omega⟩ G' + y • G') c' := by
      intro c' hc'
      have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨m + 1, by omega⟩ P c' hc'
      rw [hT, hts, Pi.add_apply, Pi.smul_apply, hGG' c' hc',
        pOp_locO ⟨m + 1, by omega⟩ (fun c'' hc'' => hGG' c'' hc'') hc', add_comm]
    have vAB_loc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
        ∀ c ∈ OmX r, (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
          (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
      intro i
      induction i with
      | zero =>
        intro f₁ f₂ h c hc
        exact ⟨h c hc, rfl⟩
      | succ i ih =>
        intro f₁ f₂ h c hc
        by_cases hi : i < r
        · simp only [Q.vAB, dif_pos hi]
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
            rw [(ih f₁ f₂ h c hc).1, (ih f₁ f₂ h c hc).2,
              pOp_locO _ (fun c' hc' => (ih f₁ f₂ h c' hc').1) hc]
          · simp only [ciOp]
            rw [(ih f₁ f₂ h c hc).1]
        · simp only [Q.vAB, dif_neg hi]
          exact ih f₁ f₂ h c hc
    have hl1 := vAB_loc (m + 1)
      (fun c' => Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀)
      (pOp ⟨m + 1, by omega⟩ G' + y • G') hTS c hc
    have hl0 := vAB_loc m
      (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) G' hGG' c hc
    have hl2 := vAB_loc (m + 2)
      (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) G' hGG' c hc
    rw [hl1.1, hl0.1, hl2.1]
    have hpG : pOp ⟨m + 1, by omega⟩ G' ∈ WSm r E := opL_mem ⟨m + 1, by omega⟩ 0 hG'
    rw [(vAB_lin y (m + 1) hpG hG' y).1, (vAB_comm y ⟨m + 1, by omega⟩ (m + 1) le_rfl hG').2.2.1]
    rw [(vAB_succ y (m + 1) (by omega) G').1, (vAB_succ y m (by omega) G').2]
    simp only [Pi.add_apply, Pi.smul_apply, cOp, ciOp, div_eq_mul_inv, mul_smul]
    abel

end claim2

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThresholdsPositive
section
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem supA_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (one : Bool) :
    0 < J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGR, -⟩ := hB'
  have hcard : 1 ≤ (S.grid1 v).card := by
    have h1 := (hGR v).1
    have h20 := PBD.ntop_ge S
    have : (1 : ℝ) ≤ S.Ntop := by linarith
    have : 1 ≤ S.Ntop := by exact_mod_cast this
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.1 hcard
  obtain ⟨-, -, hI1, -, -, hnode⟩ := hGo v
  obtain ⟨hyI, -, hP0, hP1⟩ := hnode y (Or.inr hy)
  have hy1 := (hI1 y hy).1
  have hq : (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y ≠ 0 := by
    rw [← PBL.qC_re]
    refine (PBL.q_pos_cut hB v y ?_).ne'
    rw [← PBL.cutI_eq]; exact hyI
  have hcore : 0 < (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y := by
    unfold Sz.Cfg.core
    exact Real.sqrt_pos.2 (abs_pos.2 (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  refine lt_of_lt_of_le hcore (PBL.core_le_supA hB v one y ?_)
  cases one
  · simpa using hyI
  · simp only [if_true]
    rw [← PBL.ntop_eq_N']
    exact hy1

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g := by
  obtain ⟨hg1, hg2, -⟩ := hB
  unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  have he : S.cutHi ⟨0, hS⟩ - S.cutLo ⟨0, hS⟩ = S.G.lenI := by
    simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring
  rw [he] at hlen
  have h20 := PBD.ntop_ge S
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

theorem thrS_pos (hC : 0 < Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) :
    0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v) := by
  have hg := glob_pos' hB
  have hI := lenI_pos' hB (Fin.pos v)
  have hA := supA_pos hB v (decide (b = 1 ∧ s = 1))
  have hN : (0 : ℝ) < S.G.N := by rw [← PBL.ntop_eq_N']; linarith [PBD.ntop_ge S]
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  have hC' : 0 < S.CA := lt_of_lt_of_le hC hCA
  unfold J.thrS Sz.lamThreshold
  have hk : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

end thr

theorem thrPos : ThresholdsPositive := by
  intro Cb
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB b s v _ _
  exact thrS_pos one_pos hB b s v

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

