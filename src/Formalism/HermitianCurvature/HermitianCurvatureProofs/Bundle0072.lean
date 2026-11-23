module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0066

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

section gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cptInCC_G {F : Mat k r → E} {C : Set (Mat k r)} (hF : CkOn ⊤ (GV k r) F) (hC : IsCompact C)
    (hz : ∀ g ∈ GV k r, g ∉ C → F g = 0) (A : ℝ) (m : ℕ) : InCC A m F := by
  classical
  set F₂ : Mat k r → E := fun g => if g ∈ GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hF₂c : CkOn ⊤ (GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, hff⟩ := hF g₀ hg₀
    exact ⟨U, F', hU, hgU, hc, fun g hg hgG => (he g hgG).trans (hff g hg hgG)⟩
  obtain ⟨c, hc1, hc2⟩ := Formalism.FourierDecayAlt.P.compact_support_finite_class k r E F₂ C hF₂c hC (fun g hg => by
    by_cases hgG : g ∈ GV k r
    · rw [he g hgG]; exact hz g hgG hg
    · simp [hF₂, hgG]) A m
  refine ⟨c, B5.ckOn_mono le_top hF, fun u v hu hv hl g hg => ?_⟩
  have := hc2 u v hu hv hl g hg
  rwa [dLR_eq, W_congr (lr u v) (fun y hy => by
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1) he g hg, ← dLR_eq] at this

theorem ckOn_Rw_top {f : Mat k r → E} (h : CkOn ⊤ (GV k r) f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → CkOn ⊤ (GV k r) (Rw w f) := by
  intro w
  induction w with
  | nil => intro _; exact h
  | cons X w ih =>
    intro hw
    show CkOn ⊤ (GV k r) (RdV X (Rw w f))
    have h1 : CkOn (⊤ + 1) (GV k r) (Rw w f) := by
      rw [top_add]; exact ih fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    exact B5.ckOn_RdV (hw X List.mem_cons_self) h1

end gen

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
section
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lpt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (s : ℕ) (t : E) (h : TB.Pt E) : C.LPt :=
  C.loc (S.σ v) h ++ [(s, S.σ v t)]

theorem re_real_sum {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

theorem liftOfLoc_statement : KB.LiftOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ hpos _ _ hloc
  intro ε hε i s hs hsi hir w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by
    have := len_le_cnt S w.1 v; omega
  have hb1 : 1 ≤ i - s + 1 := by omega
  have hbs : i - s + 1 + s ≤ S.G.r + 1 := by omega
  have hlev : i - s + 1 + s - 1 = i := by omega
  have hi : i ≤ S.G.r + 1 := by omega
  have hwn : w.1.cnt ≤ w.1.cnt + C.Kst := by omega
  have hL := fun v => hloc v (i - s + 1) s hb1 hs hbs (w.1 v) ⟨w, rfl⟩ (hlen v)
  simp only [hlev] at hL
  choose Up θp Um θm hPp hPm hblk using hL
  have hUp : ∀ v, ∀ a ∈ Up v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPp v).2 a ha).1, ((hPp v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hUm : ∀ v, ∀ a ∈ Um v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPm v).2 a ha).1, ((hPm v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hprobP := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θp) (fun v _ => (hPp v).1) (fun v _ => hUp v) hwn hcnt'
  have hprobM := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θm) (fun v _ => (hPm v).1) (fun v _ => hUm v) hwn hcnt'
  refine ⟨fun A x => pθ S A w θp x.1 * pθ S A w θm x.2, fun A => pair_prob (hprobP A) (hprobM A), ?_⟩
  intro Y T κ hY hκ t ht t' ht' ht0 ht0' _ A
  have hσ : ∀ v, S.σ v t ≠ 0 := fun v => (map_ne_zero _).2 ht0
  have hσ' : ∀ v, S.σ v t' ≠ 0 := fun v => (map_ne_zero _).2 ht0'
  have hsz : ∀ v, ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = i - s + 1 - 1 := by
    intro v p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    rw [ptSize_loc, hY h hh]; omega
  have hU : ∀ v, ∃ u : ℂ, ‖u‖ = 1 ∧ (v ∈ A → KB.BlockPSD Y Y
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h'))
      (fun h h' => u * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst *
        KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h'))) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (S.σ v t) (S.σ v t') (Y.image (C.loc (S.σ v))) (hσ v) (hσ' v) (hsz v)
      exact ⟨u, hu, fun _ => blockPSD_comp _ _ _ _ hB Y (C.loc (S.σ v))
        (fun x hx => Finset.mem_image_of_mem _ hx)⟩
    · exact ⟨1, by simp, fun h => absurd h hv⟩
  choose u hu1 hu2 using hU
  have hprod := blockPSD_prod (Y₁ := Y) (Y₂ := Y) univ
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t h')))
    (fun v h h' => (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t' h) (lpt S v s t' h')))
    (by
      intro v _
      by_cases hv : v ∈ A
      · simp only [if_pos hv]; exact hu2 v hv
      · simp only [if_neg hv, one_mul]
        exact blockPSD_pull (Y.image (lpt S v s t) ∪ Y.image (lpt S v s t')) (KB.gN S v ε i (w.1 v))
          (gN_psd S hpos v hε hi w _) Y (lpt S v s t) (lpt S v s t')
          (fun h hh => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
          (fun h hh => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)))
  have hmem : ∀ τ ∈ T, ∀ h ∈ Y, TB.join h s τ ∈ TB.pts Y s T := by
    classical
    intro τ hτ h hh
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(h, τ), Finset.mem_product.2 ⟨hh, hτ⟩, rfl⟩
  have hκb : KB.BlockPSD Y Y (TB.blk κ s t t) (TB.blk κ s t t') (TB.blk κ s t' t') :=
    blockPSD_pull (TB.pts Y s T) κ hκ Y (fun h => TB.join h s t) (fun h => TB.join h s t')
      (hmem t ht) (hmem t' ht')
  have hmain := block_cross_le (blockPSD_mul hκb hprod)

  have eL : (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s t t' h h' * ∏ v, (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h')) =
      (∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t' := by
    rw [Nst_eq S hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp only [lpt]; ring

  have eD : ∀ (τ : E) (Uq : Fin S.f → Finset (List C.Letter)) (θq : Fin S.f → List C.Letter → ℝ),
      (∀ v, TB.IsProb (Uq v) (θq v)) → (∀ v, ∀ a ∈ Uq v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst) →
      (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s τ τ h h' * ∏ v,
        (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
      ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S A w θq w' : ℂ) * S.base.Nst ε i s w' Y (TB.blk κ s τ τ) τ τ := by
    intro τ Uq θq hP hUq
    have hx : ∀ h h', (∏ v, (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
        ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst),
          (pθ S A w θq w' : ℂ) * ∏ v, KB.gN S v ε i (w'.1 v) (lpt S v s τ h) (lpt S v s τ h') := by
      intro h h'
      have he := expand (A := A) (w := w) (θ := θq) (U := Uq) (fun v _ => hP v) (fun v _ => hUq v) hwn hcnt'
        (fun v a => KB.gN S v ε i a (lpt S v s τ h) (lpt S v s τ h'))
      rw [he, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Complex.ofReal_prod]
      rfl
    simp only [hx]
    rw [mix_sum]
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Nst_eq S hi]; rfl
  have hK : S.base.K = C.Kst := rfl
  have hcw : S.base.cnt w = w.1.cnt := rfl
  rw [eL, eD t Up θp (fun v => (hPp v).1) hUp, eD t' Um θm (fun v => (hPm v).1) hUm, re_real_sum, re_real_sum]
    at hmain
  have hsp := sum_pair (S.base.Wb (w.1.cnt + C.Kst)) (S.base.Wb (w.1.cnt + C.Kst)) (pθ S A w θp) (pθ S A w θm)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t t) t t).re)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t' t') t' t').re) (hprobM A).2.2 (hprobP A).2.2
  rw [hK, hcw, hsp]
  calc (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ C.Kst) * ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ =
      ‖(∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ := by
        rw [norm_mul, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [norm_mul, hu1, one_mul, norm_pow, av_eq, map_sub, map_inv₀, map_inv₀]
    _ ≤ _ := hmain
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

theorem hpk_eq (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := rfl

theorem sigma_contOn {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPunit⟩, hDS⟩ := hσ
  have hc := hDS.2.2.1.2.2 v
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hmaps : Set.MapsTo (fun g : Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
    intro g hg
    show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hJ : (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
      rw [← hpk_eq, ← hPJ]
      have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
      have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹
          = ((P⁻¹)ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = PI.UpqRep.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    have hPPh : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * gᴴ * Pᴴ * ((P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹) * (P * g * P⁻¹) := by
          rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ (P⁻¹)ᴴ, hPPh, Matrix.one_mul]
          rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
      _ = PI.UpqRep.Jm ε := by rw [hg', hJ]
  have hcont : Continuous (fun g : Mx k r => P * g * P⁻¹) := by fun_prop
  have := hc.comp hcont.continuousOn hmaps
  refine this.congr ?_
  intro g _
  show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralInnerGermMoving
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section L2m

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma mul_le_young_bounds_of_le_add {nF nG g e t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hnF : 0 ≤ nF)
    (hG : nG ≤ g + e) :
    (nF ≤ δ → nF * nG ≤ t * nF ^ 2 + (0 + e ^ 2) / (2 * t) + δ / 2 * (1 + g ^ 2)) ∧
      nF * nG ≤ t * nF ^ 2 + (g ^ 2 + e ^ 2) / (2 * t) + δ / 2 * (0 + g ^ 2) := by
  have h2t : 0 < 2 * t := by positivity
  have hGa : nF * nG ≤ nF * |g| + nF * |e| := by
    have : nG ≤ |g| + |e| := hG.trans (add_le_add (le_abs_self g) (le_abs_self e))
    nlinarith

  have hA : ∀ y : ℝ, nF * |y| ≤ t * nF ^ 2 / 2 + y ^ 2 / (2 * t) := by
    intro y
    rw [show t * nF ^ 2 / 2 + y ^ 2 / (2 * t) = (t ^ 2 * nF ^ 2 + y ^ 2) / (2 * t) by field_simp <;> ring,
      le_div_iff₀ h2t]
    nlinarith [sq_nonneg (t * nF - |y|), sq_abs y]
  have hg1 : |g| ≤ (1 + g ^ 2) / 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  refine ⟨fun hK => ?_, ?_⟩
  · have h1 : nF * |g| ≤ δ * |g| := mul_le_mul_of_nonneg_right hK (abs_nonneg g)
    have h2 : δ * |g| ≤ δ / 2 * (1 + g ^ 2) := by nlinarith
    have h3 := hA e
    have h4 : t * nF ^ 2 / 2 ≤ t * nF ^ 2 := by nlinarith [sq_nonneg nF]
    have h5 : (0 + e ^ 2) / (2 * t) = e ^ 2 / (2 * t) := by ring
    rw [h5]
    linarith
  · have h3 := hA e
    have h4 := hA g
    have h5 : (g ^ 2 + e ^ 2) / (2 * t) = g ^ 2 / (2 * t) + e ^ 2 / (2 * t) := by ring
    have h6 : 0 ≤ δ / 2 * (0 + g ^ 2) := by positivity
    rw [h5]
    linarith

private lemma exists_isCompact_integral_compl_sq_lt (μ : Measure ℂ) [NullSingletonClass μ] {g : ℂ → ℝ}
    (hg2 : Integrable (fun D => g D ^ 2) μ) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ < η := by
  let Kn : ℕ → Set ℂ := fun n => Metric.closedBall (0 : ℂ) (n + 1) \ Metric.ball 0 (1 / (n + 1))
  have hKc : ∀ n, IsCompact (Kn n) := fun n => (isCompact_closedBall 0 _).diff Metric.isOpen_ball
  have h0K : ∀ n, (0 : ℂ) ∉ Kn n := by
    intro n h
    exact h.2 (Metric.mem_ball_self (by positivity))
  have hlim : Tendsto (fun n : ℕ => ∫ D, (Kn n)ᶜ.indicator (fun D => g D ^ 2) D ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun D => g D ^ 2)
      (F := fun n D => (Kn n)ᶜ.indicator (fun D => g D ^ 2) D) (f := fun _ => (0 : ℝ))
      (fun n => (hg2.indicator (hKc n).isClosed.measurableSet.compl).aestronglyMeasurable) hg2
      (fun n => Filter.Eventually.of_forall fun D => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
        exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) D)
      (by
        have h0 : ∀ᵐ D ∂μ, D ≠ (0 : ℂ) := compl_mem_ae_iff.2 (measure_singleton 0)
        filter_upwards [h0] with D hD
        have hpos : 0 < ‖D‖ := norm_pos_iff.2 hD
        obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖D‖) ‖D‖)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have ha : 1 / ‖D‖ < n + 1 := by linarith [le_max_left (1 / ‖D‖) ‖D‖]
        have hb : ‖D‖ < n + 1 := by linarith [le_max_right (1 / ‖D‖) ‖D‖]
        have hmem : D ∈ Kn n := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact hb.le
          · rw [Metric.mem_ball, dist_zero_right, not_lt]
            rw [div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at ha
            linarith
        simp [Set.indicator_apply, hmem])
    simpa using h
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨Kn n, hKc n, h0K n, hn⟩

theorem tendsto_integral_inner_germ_moving {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (e : α → ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (he : ∀ᶠ x in l, MemLp (e x) 2 μ)
    (he0 : Tendsto (fun x => ∫ D, e x D ^ 2 ∂μ) l (𝓝 0))
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D + e x D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set t : ℝ := ε / (4 * B') with ht_def
  have ht : 0 < t := by positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := hg.integrable_sq
  obtain ⟨K, hKc, h0K, hKint⟩ := exists_isCompact_integral_compl_sq_lt μ hg2 (η := ε * t / 2) (by positivity)
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hI1 : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin.ne)
  set M : ℝ := ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ + ∫ D, g D ^ 2 ∂μ + 1 with hM_def
  have hM : 0 < M := by
    have h1 : 0 ≤ ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ :=
      integral_nonneg fun D => Set.indicator_nonneg (fun _ _ => zero_le_one) D
    have h2 : 0 ≤ ∫ D, g D ^ 2 ∂μ := integral_nonneg fun D => sq_nonneg _
    linarith
  set δ : ℝ := ε / (4 * M) with hδ_def
  have hδ : 0 < δ := by positivity
  have he' : ∀ᶠ x in l, ∫ D, e x D ^ 2 ∂μ < ε * t / 2 := he0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hF, he, he', hG, hloc K hKc h0K δ hδ] with x hFx hex he2 hGx hlx
  have hFmem : MemLp (F x) 2 μ := hFx.1
  have hFB := hFx.2
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
  have he2i : Integrable (fun D => e x D ^ 2) μ := hex.integrable_sq
  have hIc : Integrable (Kᶜ.indicator (fun D => g D ^ 2)) μ := hg2.indicator hKmeas.compl
  have i1 : Integrable (fun D => t * ‖F x D‖ ^ 2) μ := hF2.const_mul t
  have i2 : Integrable (fun D => (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ :=
    (hIc.add he2i).div_const _
  have i3 : Integrable (fun D => δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) μ :=
    (hI1.add hg2).const_mul _
  have i12 : Integrable (fun D => t * ‖F x D‖ ^ 2 +
      (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ := i1.add i2
  have hbnd : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤
      t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2) := by
    filter_upwards [hGx, hlx] with D hGD hlD
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * ‖G x D‖ := norm_inner_le_norm _ _
    have hP := mul_le_young_bounds_of_le_add ht hδ.le (norm_nonneg (F x D)) hGD
    by_cases hD : D ∈ K
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 1 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = 0 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans (hP.1 (hlD hD))
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 0 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = g D ^ 2 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans hP.2
  have hsplit : ∫ D, (t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) ∂μ =
      t * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) +
        δ / 2 * (M - 1) := by
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_div,
      integral_add hIc he2i, integral_const_mul, integral_add hI1 hg2]
    simp only [hM_def]
    ring
  have hle : ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ t * ∫ D, ‖F x D‖ ^ 2 ∂μ +
      (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) + δ / 2 * (M - 1) := by
    rw [← hsplit]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (i12.add i3) hbnd)
  have hb1 : t * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hFB' : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B' := by linarith [le_max_left B 0]
    have : t * B' = ε / 4 := by rw [ht_def]; field_simp <;> ring
    nlinarith
  have hb2 : (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb3 : δ / 2 * (M - 1) ≤ ε / 8 := by
    have : δ * M = ε / 4 := by rw [hδ_def]; field_simp <;> ring
    nlinarith
  linarith

end L2m

end

end Formalism.FourierDecayAlt.P.PBK
end

