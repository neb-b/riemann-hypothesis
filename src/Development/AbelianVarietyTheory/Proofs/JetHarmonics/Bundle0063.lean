module

public import Mathlib
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FoldrCapelliSumEigen
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

section
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothLev_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) :
    Q.SmoothLev k r 0 Set.univ (fun y => ∑ i ∈ t, c i • f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Formalism.FourierDecayAlt.P.Qx2.smooth_zero
  | insert a t ha ih =>
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', he⟩ := ih g₀ hg₀
    obtain ⟨V, h', hV, hgV, hh', he'⟩ := hf a g₀ hg₀
    refine ⟨U ∩ V, fun y => c a • h' y + f' y, hU.inter hV, ⟨hgU, hgV⟩,
      ((hh'.mono Set.inter_subset_right).const_smul (c a)).add (hf'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgG
    beta_reduce
    rw [Finset.sum_insert ha, he' g hg.2 hgG, ← he g hg.1 hgG]

theorem capelli_finsum_smul {ι : Type} (t : Finset ι) (c : ι → ℂ) (f : ι → B.Mat k r → E)
    (hf : ∀ i, Q.SmoothLev k r 0 Set.univ (f i)) (Y : ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Q.CV k r Y (fun y => ∑ i ∈ t, c i • f i y) g = ∑ i ∈ t, c i • Q.CV k r Y (f i) g := by
  classical
  have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := E) Y
  have hg' := Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg
  induction t using Finset.induction_on with
  | empty => simpa using hT.map_zero hg'
  | insert a t ha ih =>
    have h := hT.lin _ (f a) (c a) (smoothLev_finsum_smul t c f hf) (hf a) g hg'
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm, ← h]
    congr 1
    funext y
    rw [add_comm]

end

theorem foldr_capelli_sum_eigen : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ev : Fin N₀ → ℝ → ℂ) (s : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ i, B.CkOn ⊤ (B.GV k r) (Fi i)) → (∀ i (Y : ℝ), ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ev i Y • Fi i g) → (∀ g ∈ B.GV k r, F g = ∑ i, Fi i g) → ∀ w : List (Bool × ℝ), ∀ g ∈ B.GV k r, (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) g = ∑ i, (w.map fun a => s * ev i a.2).prod • Fi i g := by
  intro k r Wp Wq _ _ _ _ _ _ N₀ Fi ev s F hs hev hF w
  induction w with
  | nil => intro g hg; simpa using hF g hg
  | cons a w ih =>
    intro g hg
    have hT := Formalism.FourierDecayAlt.P.Dx1.LZ.good_CV (k := k) (r := r) (E := Wq →L[ℂ] Wp) (a.2 : ℂ)
    have h1 := hT.loc _ _ (fun y hy => ih y hy.1.1) g (Formalism.FourierDecayAlt.P.Dx1.LZ.glev0 hg)
    have h2 := capelli_finsum_smul Finset.univ (fun i => (w.map fun a => s * ev i a.2).prod) Fi
      (fun i => Formalism.FourierDecayAlt.P.Dx1.LZ.smooth_of_ck (hs i)) (a.2 : ℂ) hg
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, Pi.smul_apply]
    rw [h1.trans h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i a.2 g hg, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWord
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.StartForm

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

end GlobalTheory.HatNF.StartForm

namespace GlobalTheory.HatNF

open StartForm

open MeasureTheory in
private lemma prod_ofFn_mul_prod_ofFn_eq_one {A : Type} [Ring A] :
    ∀ {n : ℕ} (f g : Fin n → A), (∀ i, f i * g i = 1) → (∀ i j, Commute (f i) (g j)) →
      (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hrest : (List.ofFn fun i : Fin n => f i.succ).prod *
        (List.ofFn fun i : Fin n => g i.succ).prod = 1 :=
      prod_ofFn_mul_prod_ofFn_eq_one _ _ (fun i => h i.succ) (fun i j => hc i.succ j.succ)
    have hcomm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) :=
      Commute.list_prod_left _ _ (List.forall_mem_ofFn_iff.mpr fun i => hc i.succ 0)
    simp only [mul_assoc]
    rw [hcomm.left_comm, ← mul_assoc (f 0), h 0, hrest, one_mul]

open MeasureTheory in
private lemma levelConstants_commute {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r)
    {x y : A}
    (hx : x ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi})
    (hy : y ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}) : Commute x y :=
  L.fns_comm x hx y hy

open MeasureTheory in
private lemma commute_prod_ofFn {A : Type} [Ring A] {n : ℕ} (a : A) (f : Fin n → A)
    (h : ∀ i, Commute a (f i)) : Commute a (List.ofFn f).prod :=
  Commute.list_prod_right _ _ (List.forall_mem_ofFn_iff.mpr h)

open MeasureTheory in
theorem _root_.GlobalTheory.HatNF.start_normalForm : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d → ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s → (∀ x ∈ _root_.Formalism.FourierDecayAlt.TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  intro P A _ _ _ _ d hHyp L st s hTie
  obtain ⟨hA, hSame, hs, hQ, hinv⟩ := hTie
  obtain ⟨-, -, hRel, -⟩ := hHyp
  obtain ⟨-, hκfns, -⟩ := hRel
  obtain ⟨-, -, -, -, -, -, -, hζi, hζb, -, hGG, hGGi, -⟩ := hSame
  have hst := hA.start
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num

  have hκ : ∀ (f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ) (g : A), g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) →
      Commute (d.κ f) g := by
    intro f g hg
    exact hκfns f g (Or.inl (by unfold _root_.Formalism.FourierDecayAlt.R.LevelData.fns; exact Or.inr hg))

  have hx : ∀ Y, st.x Y = s • d.x Y := by
    intro Y
    have h11 := congrFun (congrFun (hQ Y) 1) 1
    rw [hst.tau Y, hGG] at h11
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h11
    simp at h11
    calc st.x Y = d.L.GGi * (d.L.GG * st.x Y) := by rw [← mul_assoc, d.L.GGi_GG, one_mul]
      _ = s • d.x Y := by rw [h11, mul_smul_comm, ← mul_assoc, d.L.GGi_GG, one_mul]

  have hxinv : ∀ Y ∈ st.inv, d.x Y * d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) = 1 ∧
      d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.x Y = 1 := by
    intro Y hY
    rw [hinv] at hY
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
    rw [← map_mul, ← map_mul, ← map_one d.κ]
    constructor
    · congr 1; funext ρ; exact mul_inv_cancel₀ (hY ρ)
    · congr 1; funext ρ; exact inv_mul_cancel₀ (hY ρ)
  refine ⟨?_, ?_⟩
  · intro a ha
    have hle : _root_.Formalism.FourierDecayAlt.TL.kAlg st ≤ d.κ.range := by
      unfold _root_.Formalism.FourierDecayAlt.TL.kAlg
      refine Algebra.adjoin_le ?_
      rintro b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · rw [hx Y]
        unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
        exact ⟨s • fun ρ => _root_.Formalism.FourierDecayAlt.M.xC P ρ Y, by simp [map_smul]⟩
      · have hxi : st.xi Y = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
          have hright : st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) = 1 := by
            rw [hx Y, smul_mul_smul_comm, mul_inv_cancel₀ hs0, (hxinv Y hY).1, one_smul]
          calc st.xi Y = st.xi Y * (st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹))) := by
                rw [hright, mul_one]
            _ = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
                rw [← mul_assoc, (hst.x_xi Y hY).2, one_mul]
        rw [hxi]
        exact ⟨s⁻¹ • fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹, by simp [map_smul]⟩
    rw [← AlgHom.coe_range]
    exact hle ha
  · intro Y hY
    obtain ⟨hXXi, hXiX⟩ := hxinv Y hY
    have h10 := congrFun (congrFun (hQ Y) 1) 0
    rw [hst.low Y hY, hx Y, hGG, hζb, hζi, hGGi] at h10
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h10
    simp at h10
    rw [← smul_add] at h10
    have h10' : d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y) =
        d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by
      have h := congrArg (fun a => s⁻¹ • a) h10
      simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul] using h
    have hcancel : ∀ a : A, d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * a)) = a := by
      intro a
      simp only [← mul_assoc]
      rw [mul_assoc _ d.L.GGi d.L.GG, d.L.GGi_GG, mul_one, hXiX, one_mul]
    have key : L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y =
        d.L.l0 Y + d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * d.weightedSumBis Y) := by
      have h : d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y *
          (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y)) := by
        rw [h10']
      rw [hcancel, mul_add, mul_add, hcancel] at h
      exact h
    have hmem : ∀ b ∈ _root_.GlobalTheory.HatNF.bmon d, b ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.nfSpan
      exact Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩
    have hgen : ∀ b ∈ _root_.GlobalTheory.HatNF.bset d, b ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.bmon
      exact Submonoid.subset_closure hb
    have hκgen : ∀ f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ, d.κ f ∈ _root_.GlobalTheory.HatNF.bmon d := fun f =>
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
    have hDgen : d.L.D * d.L.Dbi ∈ _root_.GlobalTheory.HatNF.bmon d :=
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inl (by simp))))
    have hPgen : ∀ l ∈ Finset.Icc 1 (P.k - 1), d.L.Drb * d.L.Dri * d.SS l ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro l hl
      refine hgen _ ?_
      unfold _root_.GlobalTheory.HatNF.bset
      refine Or.inl (Or.inr ⟨l, by simpa using hl, ?_⟩)
      unfold _root_.GlobalTheory.HatNF.ssn
      rfl
    have hDD : ∀ l, d.L.D * d.L.Dbi * (d.L.Drb * d.L.Dri * d.SS l) = d.L.ζ * (d.L.ζbi * d.SS l) := by
      intro l
      have hcb : (List.ofFn d.L.cbi).prod * (List.ofFn d.L.cb).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.cbi_cb
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hc : (List.ofFn d.L.c).prod * (List.ofFn d.L.ci).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.c_ci
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hζci : Commute d.L.ζ (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      have hζbici : Commute d.L.ζbi (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.D _root_.Formalism.FourierDecayAlt.R.LevelData.Dbi _root_.Formalism.FourierDecayAlt.R.LevelData.Drb _root_.Formalism.FourierDecayAlt.R.LevelData.Dri _root_.Formalism.FourierDecayAlt.R.LevelData.Dr _root_.Formalism.FourierDecayAlt.R.LevelData.Drbi
      simp only [mul_assoc]
      rw [← mul_assoc (List.ofFn d.L.cbi).prod, hcb, one_mul, ← hζbici.symm.left_comm,
        ← hζci.symm.left_comm, ← mul_assoc, hc, one_mul]
    have hGGiζ : Commute d.L.GGi d.L.ζ := levelConstants_commute d.L (by simp) (by simp)
    have hGGiζbi : Commute d.L.GGi d.L.ζbi := levelConstants_commute d.L (by simp) (by simp)
    have hXiζ : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζ := hκ _ _ (by simp)
    have hXiζbi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζbi := hκ _ _ (by simp)
    have hXiGGi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.GGi := hκ _ _ (by simp)
    refine ⟨d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.weightedSumBis Y)), ?_, ?_⟩
    · have hS : d.weightedSumBis Y = ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := rfl
      rw [hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Submodule.sum_mem _ (fun l hl => hmem _ ?_)
      have heq : d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) *
          (d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.D * d.L.Dbi) * (d.L.Drb * d.L.Dri * d.SS l) *
            d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := by
        rw [mul_assoc (d.κ _) (d.L.D * d.L.Dbi), hDD, ← hXiζbi.left_comm, ← hXiζ.left_comm]
        simp only [mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (mul_mem (hκgen _) hDgen) (hPgen l hl)) (hκgen _)
    · rw [hζb, hζi, hGGi, key]
      congr 1
      simp only [mul_assoc]
      rw [hGGiζ.left_comm, hGGiζbi.left_comm, ← mul_assoc d.L.ζi, d.L.ζi_ζ, one_mul,
        ← mul_assoc d.L.ζb, d.L.ζb_ζbi, one_mul, hXiGGi.left_comm]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ v ∈ R.sm, ContinuousOn (fun g => Bm (R.σ g v)) (GG k r) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → HasDerivAt (fun t : ℝ => Bm (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) (Bm (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) 0 := by
  first | exact @GlobalTheory.cwCont_continuousOn_hasDerivAt | exact GlobalTheory.cwCont_continuousOn_hasDerivAt | (intros; apply GlobalTheory.cwCont_continuousOn_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HcParamSubIntegral
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InterlaceHalf
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.StdGrid

theorem half_le_of_lt {x y : ℝ} (m : ℤ) (h : y - x = (m : ℝ) + 1 / 2) (hlt : x < y) : x + 1 / 2 ≤ y := by
  have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
  have h2 : (-1 : ℤ) < m := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ m := by omega
  have h4 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  linarith

theorem scale_bounds {Ch b ka T : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch) (h2 : ka⁻¹ ≤ b ^ Ch)
    (h3 : 1 ≤ T * (1 / ka) ^ (2 * r)) (h4 : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) :
    b ^ (-((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ))) ≤ T ∧ T ≤ b ^ ((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hC : Ch ≤ |Ch| := le_abs_self _
  have hC0 : 0 ≤ |Ch| := abs_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hbC : b ^ Ch ≤ b ^ |Ch| := Real.rpow_le_rpow_of_exponent_le hb hC
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ b ^ Ch → x ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    intro x hx hxb
    calc x ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) := pow_le_pow_left₀ hx (hxb.trans hbC) _
      _ = b ^ (|Ch| * ((2 * r : ℕ) : ℝ)) := by rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        apply mul_le_mul_of_nonneg_left _ hC0
        push_cast; linarith
  have hm : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set m : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hmdef
  have hk1 := hpow ka hka.le h1
  have hk2 := hpow (1 / ka) (by positivity) (by rwa [one_div])
  have hq : 0 < (1 / ka) ^ (2 * r) := by positivity
  have hT : 0 < T := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hq.le
    linarith
  have hTe : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel hka.ne', one_pow, mul_one]
  have hE : 0 < b ^ (|Ch| * m) := Real.rpow_pos_of_pos hb0 _
  constructor
  · have h5 : 1 ≤ T * b ^ (|Ch| * m) := h3.trans (mul_le_mul_of_nonneg_left hk2 hT.le)
    have h6 : b ^ (|Ch| * m) ≤ b ^ ((2 * |Ch|) * m) := by
      apply Real.rpow_le_rpow_of_exponent_le hb
      nlinarith [mul_nonneg hC0 hm]
    have h7 : 1 ≤ T * b ^ ((2 * |Ch|) * m) := h5.trans (mul_le_mul_of_nonneg_left h6 hT.le)
    rw [Real.rpow_neg hb0.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hb0 _)]
    exact h7
  · have h5 : b ^ (Ch * m) ≤ b ^ (|Ch| * m) :=
      Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC hm)
    calc T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := hTe
      _ ≤ b ^ (|Ch| * m) * b ^ (|Ch| * m) := mul_le_mul (h4.trans h5) hk1 (by positivity) hE.le
      _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

theorem cut_gap {k : ℕ} {u u' : Fin k → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : HasCut u u' L) : ∃ l, L ≤ |u l - u' l| := by
  obtain ⟨a, b, ⟨l, a', b', _, hab, hI, h1, h2, _⟩, hLb⟩ := h
  have ha : a ∈ Set.Icc a' b' := hI ▸ (⟨le_rfl, by linarith⟩ : a ∈ Set.Icc a b)
  have hb : b ∈ Set.Icc a' b' := hI ▸ (⟨by linarith, le_rfl⟩ : b ∈ Set.Icc a b)
  refine ⟨l, ?_⟩
  have h3 : max (-u l) (-u' l) - min (-u l) (-u' l) = |u l - u' l| := by
    rw [max_sub_min_eq_abs]
    congr 1; ring
  linarith [ha.1, hb.2]

theorem interlace_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}
    (hl : ∀ a, ∃ m : ℤ, lam a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ))
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (s : Fin (2 * r + k + 1)) (hs : s.val + 2 ≤ k) :
    lam s + 1 / 2 ≤ u (s.val + 1) ∧ u (s.val + 2) + 1 / 2 ≤ lam s := by
  obtain ⟨h1, h2⟩ := hI.1 s.val (by omega)
  obtain ⟨m, hm⟩ := hl s
  obtain ⟨a, ha⟩ := hu (s.val + 1) (by simp; omega)
  obtain ⟨a', ha'⟩ := hu (s.val + 2) (by simp; omega)
  push_cast at hm
  refine ⟨half_le_of_lt (a - m - r - 1) ?_ h1, half_le_of_lt (m + r - a') ?_ h2⟩
  · push_cast; linarith
  · push_cast; linarith

theorem std_grid : ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (ka b g : ℝ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) (P.T * (1 / ka) ^ (2 * P.r)) (P.T' * (1 / ka) ^ (2 * P.r)) ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → AllGaps lam g → StdNum (2 * |Ch|) b (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g / 2) P lam ∧ P.T ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ P.T' ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∀ n₀ : ℕ, ((∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 30 * (P.r + 1) ^ 2 + 6) → (¬ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 0) → Cases P n₀ := by
  refine ⟨36, ?_⟩
  intro Ch Cg hCg P lam ka b g hk hS hint hg
  obtain ⟨⟨hanti, hhalf⟩, hI, hI', hka, hka1, hka2, hT1, hT1', hT2, hT2', hlb, hub, hub', hgap, -,
    ⟨bv, hbv, hshape⟩, hcase⟩ := hS
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _

  let s1 : Fin (2 * P.r + P.k + 1) := ⟨P.k - 1, by omega⟩
  let s2 : Fin (2 * P.r + P.k + 1) := ⟨P.k, by omega⟩
  have h12 : s1 < s2 := by simp only [s1, s2, Fin.mk_lt_mk]; omega
  have hbelow : ∀ i : Fin P.k, lam s1 < P.u (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < P.k
    · have h1 := (hI.1 i.val hi).1
      have h2 : lam s1 ≤ lam ⟨i.val, by omega⟩ := hanti.antitone (by simp only [s1, Fin.mk_le_mk]; omega)
      exact lt_of_le_of_lt h2 h1
    · have h1 := hI.2 (by omega)
      have he : i.val = P.k - 1 := by have := i.isLt; omega
      rw [he]
      exact h1
  have hn1 := (hshape s1).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd (hbelow i) (not_lt.2 hi.le))
  have hn2 := (hshape s2).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd ((hanti h12).trans (hbelow i)) (not_lt.2 hi.le))
  have hd : |lam s1 - lam s2| ≤ bv := by
    rw [abs_le]; constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]
  have hbvb : bv ≤ b := by
    have := hlb s1
    have := neg_abs_le (lam s1)
    linarith [hn1.2]
  have hmaxgap : AllGaps lam (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g) :=
    fun s t h => max_le (hgap s t h) (hg s t h)
  have hcb := (hmaxgap s1 s2 h12.ne).trans (hd.trans hbvb)
  have hc4 : 36 ≤ max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g := by
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by push_cast; linarith)
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hkb : (P.k : ℝ) ≤ b := by
    have h0 : (1 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      push_cast; linarith
    have h1 : ((2 * P.r + P.k + 1 : ℕ) : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ h0 (by norm_num)
    have h2 : (P.k : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  obtain ⟨hTl, hTu⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1 hT2
  obtain ⟨hTl', hTu'⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1' hT2'
  have hh := interlace_half hhalf (fun i hi => (hint i hi).1) hI
  have hh' := interlace_half hhalf (fun i hi => (hint i hi).2) hI'
  refine ⟨⟨fun l hl => ⟨by linarith, by linarith, hkb, ?_, ?_, hlb, ?_, ?_, ?_, hTl, hTl'⟩,
    fun s hs => ⟨(hh s hs).1, (hh s hs).2, (hh' s hs).1, (hh' s hs).2⟩⟩, hTu, hTu', ?_⟩
  · rw [Finset.mem_Icc] at hl
    have := hub ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · rw [Finset.mem_Icc] at hl
    have := hub' ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · intro s t hst
    have h1 := hmaxgap s t hst.ne
    rw [abs_of_pos (sub_pos.2 (hanti hst))] at h1
    linarith
  · exact fun s hs => ⟨fun _ => (hh s hs).1, fun _ => (hh s hs).2⟩
  · exact fun s hs => ⟨fun _ => (hh' s hs).1, fun _ => (hh' s hs).2⟩
  · intro n₀ he hne
    have hL : ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ Cg * ((P.r : ℝ) + 1) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
      push_cast; nlinarith
    rcases hcase with ⟨heq, l, hl, hsl, -⟩ | ⟨hneq, hcut⟩
    · have hall : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have := congrFun heq ⟨i - 1, by omega⟩
        simpa [Nat.sub_add_cancel hi.1] using this
      right
      refine ⟨he hall, hall, l + 1, by omega, hl, ?_⟩
      rw [he hall, ← hall (l + 1) (by simp; omega), ← hall (l + 1 + 1) (by simp; omega)]
      simp only at hsl
      linarith
    · left
      refine ⟨hne (fun hall => hneq (funext fun i => hall _ (by simp))), ?_⟩
      obtain ⟨l, hl⟩ := cut_gap (le_trans (Nat.cast_nonneg _) hL) hcut
      exact ⟨l.val + 1, by simp, hL.trans hl⟩

end GlobalTheory.StdGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosureStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_maps_closure : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' mu'' : Fin (2 * r + k + 1) → ℝ) (R R' R'' : Rep k r), R.IsDS ε mu → R'.IsDS ε mu' → R''.IsDS ε mu'' → (∀ g ∈ GG k r, SmMap R R (fun v => R.σ g v)) ∧ (∀ (T : R.H → R'.H) (T' : R'.H → R''.H), SmMap R R' T → SmMap R' R'' T' → SmMap R R'' (fun v => T' (T v))) ∧ (∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v)) ∧ ∀ (Wp : Type) [NormedAddCommGroup Wp] (T : R.H → R'.H) (Bm : R'.H → Wp), SmMap R R' T → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  first | exact @GlobalTheory.SmMapAct.smMap_act | exact GlobalTheory.SmMapAct.smMap_act | (intros; apply GlobalTheory.SmMapAct.smMap_act <;> assumption)
end

