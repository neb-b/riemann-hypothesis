module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0198
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordCorrespondence

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OpCapLOfOf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def wfam {d : ℕ} {α : Type} (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d :=
  L.map (fun t => (t.1, t.2.map F)) ++ [(c, [])]

def WFamApp : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ)
    (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ),
    WOp.app (wfam L F c) v x = (L.map fun t => t.1 * vfW (t.2.map F) v x).sum + c * v x

def WFamSymb : Prop :=
  ∀ (d : ℕ) (α : Type) (L : List (ℂ × List α)) (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ)
    (x ξ : Fin d → ℝ) (τ : α → ℂ), 1 ≤ j → (∀ t ∈ L, ∀ X ∈ t.2, ((ξ ⬝ᵥ F X x : ℝ) : ℂ) = τ X) →
    WOp.symb (wfam L F c) j x ξ = (L.map fun t => if t.2.length = j then t.1 * (t.2.map τ).prod else 0).sum

def TrRealLie : Prop :=
  ∀ (k r : ℕ) (A X : B.Mat k r), B.inLie k r A → B.inLie k r X →
    (((Matrix.trace (A * X)).re : ℝ) : ℂ) = Matrix.trace (A * X)

def CkLevOn : Prop :=
  ∀ (k r m : ℕ) (Dm : Set (B.Mat k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E),
    Q.CkLev k r 0 m Dm f → B.CkOn (m : ℕ∞) (B.GV k r ∩ Dm) f

theorem wfam_ok {d : ℕ} {α : Type} {O : Set (Fin d → ℝ)} (L : List (ℂ × List α))
    (F : α → (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (j : ℕ) (hL : ∀ t ∈ L, t.2.length ≤ j)
    (hF : ∀ X, ContDiffOn ℝ ∞ (F X) O) : FamOK O (wfam L F c) j := by
  intro t ht
  rw [wfam, List.mem_append] at ht
  rcases ht with ht | ht
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    refine ⟨by simpa using hL t0 ht0, ?_⟩
    intro V hV
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hV
    exact hF X
  · simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simp, by simp⟩

theorem opCVOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCVOf := by
  intro hRw hCW k r z z' d O U κ Φ u hC hOm hCk hev j hj1 hjn
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨Ys, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r j hj1 hjn
  choose c hc using hev
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (Ys i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapROf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapROf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z' Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VR κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).1), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VR κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • B.Rw t.2 u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).1, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ₀ hΞ₀ hcov
    rw [hS d _ L (VR κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ₀ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ₀ X hΞ₀ ((hL t ht).2 X hX)])]
    exact hsym Ξ₀ hΞ₀

theorem opCapLOf_of (hA : WFamApp) (hS : WFamSymb) (hT : TrRealLie) (hK : CkLevOn) : OpCapLOf := by
  intro hRw hCW k r z z' d O U κ Φ u Bs hC hOm hCk hBs hev j hj1 hjk
  obtain ⟨_, hfld, hw⟩ := hRw k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨ws, lam, L, cj, hcj, hL, hid, hsym⟩ := hCW k r z Bs hBs j hj1 hjk
  choose c hc using hev
  have hjn : j ≤ 2 * r + k + 1 := by omega
  refine ⟨wfam L (VL κ Φ) (-(∑ i, lam i * c (ws i))), cj, hcj,
    wfam_ok L _ _ j (fun t ht => (hL t ht).1) (fun X => (hfld X).2), ?_, ?_⟩
  · intro x hx
    rw [hA]
    have hgG : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    have hgO : κ x ∈ JF.Om k r z z' := ⟨hgG, hOm x hx⟩
    have e1 := hid ℂ (B.GV k r ∩ Q.OmPlus k r z z') u (hK k r _ _ ℂ u hCk) (κ x) ⟨hgG, hOm x hx⟩ hgG
    have e2 : (L.map fun t => t.1 * vfW (t.2.map (VL κ Φ)) (fun y => u (κ y)) x) =
        (L.map fun t => t.1 • t.2.foldr Q.LdV u (κ x)) := by
      refine List.map_congr_left (fun t ht => ?_)
      rw [(hw t.2 (hL t ht).2 ((hL t ht).1.trans hjn) x hx).2, smul_eq_mul]
    rw [e2, ← e1]
    simp only [hc _ _ hgO, smul_eq_mul]
    rw [neg_mul, Finset.sum_mul]
    simp only [mul_assoc, add_neg_cancel]
  · intro x hx ξ Ξ hΞ hcov
    rw [hS d _ L (VL κ Φ) _ j x ξ (fun X => Matrix.trace (Ξ * X)) hj1 (fun t ht X hX => by
      rw [hcov X ((hL t ht).2 X hX), hT k r Ξ X hΞ ((hL t ht).2 X hX)])]
    exact hsym Ξ hΞ

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ParFamIntegrable
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}


variable (z z' π π') in
def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]


variable (z z' π π') in
def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop


variable (z z' π π') in
def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩

theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtEntryAppendStart
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem ptEntry_append_start (rest : C.LPt) : ∀ (H : C.LPt) (a b : ℕ),
    D.ptEntry (H ++ rest) (D.ptSize H + a) b = if D.ptSize H ≤ b then D.ptEntry rest a (b - D.ptSize H) else 0 := by
  intro H
  induction H with
  | nil => simp [D.ptSize]
  | cons block H' ih =>
    obtain ⟨s, t⟩ := block
    intro a b
    have hsz : D.ptSize ((s, t) :: H') = s + D.ptSize H' := by simp [D.ptSize]
    rw [hsz]
    show D.ptEntry ((s, t) :: (H' ++ rest)) (s + D.ptSize H' + a) b = _
    simp only [D.ptEntry]
    rw [if_neg (by omega)]
    by_cases hb : s ≤ b
    · rw [if_pos ⟨by omega, hb⟩, show s + D.ptSize H' + a - s = D.ptSize H' + a by omega,
        ih a (b - s)]
      by_cases h2 : D.ptSize H' ≤ b - s
      · rw [if_pos h2, if_pos (by omega), show b - s - D.ptSize H' = b - (s + D.ptSize H') by omega]
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem det_big (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    (D.ptMatN (H ++ [(s, t)]) r).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨D.ptSize H, by omega⟩ : Fin r)
  intro j
  show D.ptEntry (H ++ [(s, t)]) (D.ptSize H) j = 0
  have h := ptEntry_append_start [(s, t)] H 0 j
  rw [add_zero] at h
  rw [h]
  split_ifs with hj
  · simp only [D.ptEntry]
    rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega)]
  · rfl

theorem ptG_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    D.ptG TT r (H ++ [(s, t)]) = Complex.normSq (D.ptMatN (H ++ [(s, t)]) (r + 1)).det := by
  unfold D.ptG
  rw [det_big H s t r hs hr]
  simp

theorem wPt_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1)
    (hG : 0 < D.ptG TT r (H ++ [(s, t)])) : Top.wPt TT r (H ++ [(s, t)]) = 1 := by
  unfold Top.wPt
  rw [ptG_big TT H s t r hs hr] at hG ⊢
  exact div_self hG.ne'

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem hsInner_zero_right' (A : Wq →L[ℂ] Wp) : B.hsInner A 0 = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 := rfl
  simp only [ContinuousLinearMap.zero_apply, this, inner_zero_left]

theorem vecV_of_G (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt)
    (hG : ¬ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r Q) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dite_eq_right (fun h => hG h.2)]

theorem topOf_big (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (H H' : C.LPt) (s : ℕ) (t t' : ℂ) (hs : 2 ≤ s) (hH : D.ptSize H + s = P.r + 1) (hH' : D.ptSize H' + s = P.r + 1) :
    Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (H ++ [(s, t)]) (H' ++ [(s, t')]) =
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Real.sqrt (Top.cW P p.l0 w e ρ).re * Real.sqrt (Top.cW P p.l0 w e ρ).re : ℝ) : ℂ) *
          B.hsInner ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H ++ [(s, t)])))
            ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H' ++ [(s, t')]))) := by
  unfold Top.topOf
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  by_cases h1 : 0 < D.ptG TT P.r (H ++ [(s, t)])
  · by_cases h2 : 0 < D.ptG TT P.r (H' ++ [(s, t')])
    · unfold Top.dH
      rw [wPt_big TT H s t P.r hs hH h1, wPt_big TT H' s t' P.r hs hH' h2, one_pow, one_mul]
    · rw [vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, hsInner_zero_right', mul_zero, mul_zero]
  · rw [vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left]
    simp

end top

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfParts
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfParts : Prop := KB.RadHead → KB.HeadTop → FormOne → ZetaNormExists → KB.PStd

theorem pStdOfParts : PStdOfParts := fun hRH hHT hOne hZN hP =>
  pStd_of hRH hHT hOne hZN
    (fun Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw => by
      have hPc : P5.ThmPActualCpt := by
        intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        obtain ⟨K, h1, h2, h3, h4⟩ := hP Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩
      exact topContOn_of hPc hHT Wp Wq P p F w h h' hh hh' Cb hθ hF hw) hP

theorem pStd_cpt_of_parts (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne)
    (hZN : ZetaNormExists) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_of_cpt hP hRH hHT hOne hZN (topContOn_of hP hHT)

end Formalism.FourierDecayAlt.P.PBO
end
end

