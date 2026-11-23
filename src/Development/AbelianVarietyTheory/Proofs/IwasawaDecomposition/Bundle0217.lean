module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.GelfScalar

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def LinAdjOn (D : Submodule ℂ H) (f : H → H) : Prop :=
  (∀ w ∈ D, f w ∈ D) ∧ (∀ v ∈ D, ∀ w ∈ D, f (v + w) = f v + f w) ∧ (∀ (c : ℂ), ∀ w ∈ D, f (c • w) = c • f w) ∧
    ∀ u ∈ D, ∃ u' ∈ D, ∀ w ∈ D, ⟪u, f w⟫_ℂ = ⟪u', w⟫_ℂ

variable {D : Submodule ℂ H}

theorem linAdjOn_id : LinAdjOn D fun w => w := ⟨fun _ hw => hw, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun u hu => ⟨u, hu, fun _ _ => rfl⟩⟩

theorem linAdjOn_zero : LinAdjOn D fun _ => 0 := by
  refine ⟨fun _ _ => D.zero_mem, fun _ _ _ _ => (add_zero 0).symm, fun c _ _ => (smul_zero c).symm,
    fun _ _ => ⟨0, D.zero_mem, fun w _ => ?_⟩⟩
  simp

theorem LinAdjOn.comp {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f (g w) := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => hf1 _ (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show f (g (v + w)) = f (g v) + f (g w)
    rw [hg2 v hv w hw, hf2 _ (hg1 v hv) _ (hg1 w hw)]
  · show f (g (c • w)) = c • f (g w)
    rw [hg3 c w hw, hf3 c _ (hg1 w hw)]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u₁ hu₁
    exact ⟨u₂, hu₂, fun w hw => (h₁ _ (hg1 w hw)).trans (h₂ w hw)⟩

theorem LinAdjOn.add {f g : H → H} (hf : LinAdjOn D f) (hg : LinAdjOn D g) : LinAdjOn D fun w => f w + g w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  refine ⟨fun w hw => D.add_mem (hf1 w hw) (hg1 w hw), fun v hv w hw => ?_, fun c w hw => ?_,
    fun u hu => ?_⟩
  · show f (v + w) + g (v + w) = (f v + g v) + (f w + g w)
    rw [hf2 v hv w hw, hg2 v hv w hw]
    abel
  · show f (c • w) + g (c • w) = c • (f w + g w)
    rw [hf3 c w hw, hg3 c w hw, smul_add]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    obtain ⟨u₂, hu₂, h₂⟩ := hg4 u hu
    refine ⟨u₁ + u₂, D.add_mem hu₁ hu₂, fun w hw => ?_⟩
    show ⟪u, f w + g w⟫_ℂ = ⟪u₁ + u₂, w⟫_ℂ
    rw [inner_add_right, inner_add_left, h₁ w hw, h₂ w hw]

theorem LinAdjOn.smul {f : H → H} (hf : LinAdjOn D f) (a : ℂ) : LinAdjOn D fun w => a • f w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  refine ⟨fun w hw => D.smul_mem a (hf1 w hw), fun v hv w hw => ?_, fun c w hw => ?_, fun u hu => ?_⟩
  · show a • f (v + w) = a • f v + a • f w
    rw [hf2 v hv w hw, smul_add]
  · show a • f (c • w) = c • a • f w
    rw [hf3 c w hw, smul_comm]
  · obtain ⟨u₁, hu₁, h₁⟩ := hf4 u hu
    refine ⟨(starRingEnd ℂ a) • u₁, D.smul_mem _ hu₁, fun w hw => ?_⟩
    show ⟪u, a • f w⟫_ℂ = ⟪(starRingEnd ℂ a) • u₁, w⟫_ℂ
    rw [inner_smul_right, inner_smul_left, h₁ w hw, Complex.conj_conj]

theorem linAdjOn_sum {ι : Type} (s : Finset ι) {f : ι → H → H} (hf : ∀ i, LinAdjOn D (f i)) :
    LinAdjOn D fun w => ∑ i ∈ s, f i w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact linAdjOn_zero
  · intro i s hi ih
    simp only [Finset.sum_insert hi]
    exact (hf i).add ih

theorem linAdjOn_foldr (l : List (H → H)) (hl : ∀ f ∈ l, LinAdjOn D f) :
    LinAdjOn D fun w => l.foldr (fun f acc => f acc) w := by
  induction l with
  | nil =>
    simp only [List.foldr_nil]
    exact linAdjOn_id
  | cons f l ih =>
    simp only [List.foldr_cons]
    exact (hl f (by simp)).comp (ih fun g hg => hl g (by simp [hg]))

theorem LinAdjOn.exists_extend {f : H → H} (hf : LinAdjOn D f) : ∃ A : H →ₗ[ℂ] H, ∀ w ∈ D, A w = f w := by
  obtain ⟨-, hf2, hf3, -⟩ := hf
  let g : D →ₗ[ℂ] H :=
    { toFun := fun x => f x
      map_add' := fun x y => hf2 x x.2 y y.2
      map_smul' := fun c x => hf3 c x x.2 }
  obtain ⟨A, hA⟩ := LinearMap.exists_extend g
  refine ⟨A, fun w hw => ?_⟩
  have key := LinearMap.congr_fun hA ⟨w, hw⟩
  exact key

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem linAdjOn_dRep (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieG G) : LinAdjOn (smSub G π) (dRep π X) := by
  refine ⟨fun w hw => dRep_mem hG hπ hw hX, fun v hv w hw => dRep_add hv hw hX,
    fun c w hw => dRep_smul c hw hX, fun u hu => ⟨-dRep π X u, neg_mem (dRep_mem hG hπ hu hX), fun w hw => ?_⟩⟩
  rw [inner_dRep hG hπ hu hw hX, inner_neg_left]

theorem linAdjOn_dRepC (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    (Z : Matrix (Fin n) (Fin n) ℂ) : LinAdjOn (smSub G π) (dRepC G π Z) := by
  obtain ⟨h₁, h₂⟩ := parts_mem hG hh Z
  exact (linAdjOn_dRep hG hπ h₁).add ((linAdjOn_dRep hG hπ h₂).smul Complex.I)

theorem linAdjOn_gelfH (hG : IsUnit G) (hh : Gᴴ = G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) (k : ℕ) :
    LinAdjOn (smSub G π) (gelfH G π k) := by
  show LinAdjOn (smSub G π) fun w => ∑ idx : Fin (k + 1) → Fin n,
    (List.ofFn fun a : Fin (k + 1) => dRepC G π (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
      (fun f acc => f acc) w
  refine linAdjOn_sum Finset.univ fun idx => linAdjOn_foldr _ fun g hg => ?_
  rw [List.mem_ofFn] at hg
  obtain ⟨a, rfl⟩ := hg
  exact linAdjOn_dRepC hG hh hπ _

end

theorem gelfH_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (k : ℕ), ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k w = c • w := by
  intro n ε H _ _ _ σ P G hP hPG hσ hirr k
  have hGu : IsUnit G := gram_unit hP hPG
  have hh : Gᴴ = G := gram_herm hPG
  have hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isURepOn_trRep hP hPG hσ
  have hirr' : IsIrredOn (Formalism.QuantumDeterminants.UH G) (trRep σ P) := isIrredOn_trRep hP hPG hirr
  have hL := linAdjOn_gelfH hGu hh hπ k
  obtain ⟨A, hA⟩ := hL.exists_extend
  obtain ⟨-, -, -, hadj⟩ := hL
  have hnorm : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ v : H, ‖trRep σ P g v‖ = ‖v‖ := fun g hg v => hπ.2.1 g hg v
  have hAg : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      A (trRep σ P g w) = trRep σ P g (A w) := by
    intro g hg w hw
    rw [hA _ (rep_mem hGu hπ hw hg), hA w hw]
    exact _root_.GlobalTheory.SmVecGelfComm.gelfH_rep n ε H σ P G hP hPG hσ k g hg w hw
  have h₁ : ∀ (i : Formalism.QuantumDeterminants.UH G) (v : H), ‖trRep σ P i.1 v‖ = ‖v‖ := fun i v => hnorm i.1 i.2 v
  have h₂ : ∀ i : Formalism.QuantumDeterminants.UH G, ∃ j : Formalism.QuantumDeterminants.UH G,
      (∀ v, trRep σ P j.1 (trRep σ P i.1 v) = v) ∧ ∀ v, trRep σ P i.1 (trRep σ P j.1 v) = v := by
    intro i
    have hu : IsUnit i.1.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mem_UH hGu i.2)
    refine ⟨⟨i.1⁻¹, inv_mem_UH hGu i.2⟩, fun v => ?_, fun v => ?_⟩
    · rw [← rep_mul hπ (inv_mem_UH hGu i.2) i.2, Matrix.nonsing_inv_mul _ hu, rep_one hπ]
    · rw [← rep_mul hπ i.2 (inv_mem_UH hGu i.2), Matrix.mul_nonsing_inv _ hu, rep_one hπ]
  have h₃ : ∀ S : Submodule ℂ H, IsClosed (S : Set H) →
      (∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ S, trRep σ P i.1 v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hinv => hirr' S hS fun g hg v hv => hinv ⟨g, hg⟩ v hv
  have h₄ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ v ∈ smSub G (trRep σ P), trRep σ P i.1 v ∈ smSub G (trRep σ P) :=
    fun i v hv => rep_mem hGu hπ hv i.2
  have h₅ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), ‖A (trRep σ P i.1 w)‖ = ‖A w‖ := by
    intro i w hw
    rw [hAg i.1 i.2 w hw, hnorm i.1 i.2]
  have h₆ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ‖(LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)‖ = ‖(LinearMap.id : H →ₗ[ℂ] H) w‖ := by
    intro i w _
    simp only [LinearMap.id_apply]
    exact hnorm i.1 i.2 w
  have h₇ : ∀ i : Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P),
      ⟪A (trRep σ P i.1 w), (LinearMap.id : H →ₗ[ℂ] H) (trRep σ P i.1 w)⟫_ℂ =
        ⟪A w, (LinearMap.id : H →ₗ[ℂ] H) w⟫_ℂ := by
    intro i w hw
    simp only [LinearMap.id_apply]
    rw [hAg i.1 i.2 w hw, rep_inner hπ i.2]
  have h₈ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f hu hu0 hAu
    apply eq_zero_of_inner_smooth hP hPG hσ
    intro v hv
    obtain ⟨v', -, hvv⟩ := hadj v hv
    have t₁ : Tendsto (fun i => ⟪v, A (u i)⟫_ℂ) atTop (𝓝 ⟪v, f⟫_ℂ) := tendsto_const_nhds.inner hAu
    have t₂ : Tendsto (fun i => ⟪v', u i⟫_ℂ) atTop (𝓝 ⟪v', (0 : H)⟫_ℂ) :=
      tendsto_const_nhds.inner hu0
    rw [inner_zero_right] at t₂
    refine tendsto_nhds_unique t₁ (t₂.congr fun i => ?_)
    rw [hA _ (hu i), hvv _ (hu i)]
  have h₉ : ∀ (u : ℕ → H) (f : H), (∀ i, u i ∈ smSub G (trRep σ P)) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun i => (LinearMap.id : H →ₗ[ℂ] H) (u i)) atTop (𝓝 f) → f = 0 := by
    intro u f _ hu0 hu
    simp only [LinearMap.id_apply] at hu
    exact tendsto_nhds_unique hu hu0
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ClosableSchur.inner_eq_pair (Formalism.QuantumDeterminants.UH G) H H (fun i => trRep σ P i.1) (smSub G (trRep σ P))
    h₁ h₂ h₃ h₄ A LinearMap.id h₅ h₆ h₇ h₈ h₉
  refine ⟨starRingEnd ℂ c, fun w hw => ?_⟩
  rw [← hA w hw]
  apply ext_inner_smooth hP hPG hσ
  intro u hu
  have e₁ : ⟪A w, u⟫_ℂ = ⟪starRingEnd ℂ c • w, u⟫_ℂ := by
    have e := hc w hw u hu
    rw [LinearMap.id_apply] at e
    rw [e, inner_smul_left, Complex.conj_conj]
  rw [← inner_conj_symm, e₁, inner_conj_symm]

end GlobalTheory.SmVec.GelfScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

theorem selfDual_frame_level_one_lattice_eq_standard {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem pi_eq_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem arr_injective {n : ℕ} {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  unfold arr at h'
  apply Fin.ext
  split_ifs at h' <;> simp only at h' <;> omega

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

theorem nNeg_eq (τ : D.what₂.Tau) : nNeg (M.ε τ) = q := by
  rw [nNeg_shape (by omega) (hε τ)]; omega

theorem negM_eq (τ : D.what₂.Tau) :
    negM V q = diagonal fun c => (if M.ε τ (arr (nNeg (M.ε τ)) c) = true then (1 : ℂ) else -1) := by
  unfold negM
  congr 1
  funext c
  have := c.2
  rw [nNeg_eq M hpq hε, hε, arr, sgn]
  by_cases h : (c : ℕ) < q
  · rw [dite_eq_left h, if_pos h, if_neg (by simp only [decide_eq_true_eq]; omega)]; simp
  · rw [dite_eq_right h, if_neg h, if_pos (by simp only [decide_eq_true_eq]; omega)]; simp

theorem isONeg_x0Mat : IsONeg V q (x0Mat M) := by
  intro τ
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  have h3 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      ((onb M τ)ᴴ * gramAt D V τ * onb M τ).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h3, h2, negM_eq M hpq hε τ, Formalism.REAL.Jm, Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le _))]
  rfl

theorem cart_eq_cartZ : cart M = cartZ V q (x0Mat M) := by
  funext τ
  have hn : negM V q * negM V q = 1 := by
    rw [negM_eq M hpq hε τ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have h1 : (negM V q * ((x0Mat M τ)ᴴ * gramAt D V τ)) * x0Mat M τ = 1 := by
    rw [Matrix.mul_assoc, isONeg_x0Mat M hpq hε τ, hn]
  have hu : IsUnit (x0Mat M τ).det := Matrix.isUnit_det_of_left_inverse h1
  rw [cartZ, negM_eq M hpq hε τ, ← torus_x0Mat M τ fun a => if M.ε τ a = true then (1 : ℂ) else -1,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end Model

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV; exact h

theorem latEmb_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ ι) := by
  subst hV; exact h

theorem isAA_span {k : ℕ} (L : Lt D.host.E k) : GlobalTheory.Ker.IsAA (Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) L := by
  intro v
  rw [← Submodule.mem_toAddSubgroup]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x hx' hx =>
      clear hx'
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hx
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx) hv

theorem isMov_hLat (W : HSp D) (h : GA D W) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt W h) (Bridge.hLat W 1) (Bridge.hLat W (FWT.fin W h)) := by
  intro u
  rw [GlobalTheory.MovedLat.hLat_one]
  have := Set.ext_iff.1 (GlobalTheory.MovedLat.hat_hLat W (FWT.fin W h)) u
  exact this.trans ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

end GlobalTheory.OneMapRef.FactsLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem petInt_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : PetInt D :=
  fun _ hθ _ μ 𝓕 hq _ _ hψ hφ =>
    GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hq.1 hq.2 hψ hφ.1 hφ.2

end GlobalTheory.Mem.Th
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobGarding

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) :
    ∃ φ', IsTest φ' ∧ ∀ w, word (trRep σ P) l (gard ε σ φ w) = gard ε σ φ' w := by
  induction l with
  | nil => exact ⟨φ, hφ, fun _ => rfl⟩
  | cons X l ih =>
    obtain ⟨φ', h1, h2⟩ := ih fun Y hY => hl Y (by simp [hY])
    obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.SmVec.dRep_gard n ε H σ P G hP h hσ φ' h1
    exact ⟨ψ X, (hψ X).1, fun w => by rw [word_cons, h2, (hψ X).2 (hl X (by simp))]⟩

theorem inner_word_gard (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ)
    {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (l : List (Matrix (Fin n) (Fin n) ℂ))
    (hl : ∀ X ∈ l, X ∈ lieG G) {w : H} (hw : w ∈ smSub G (trRep σ P)) (a : H) :
    ⟪a, word (trRep σ P) l (gard ε σ φ w)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪a, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
  have hc := _root_.GlobalTheory.SmVec.WordCont.continuous_word_translate n ε H σ P G hP h hσ l hl w hw
  have key : ∀ y : H, ⟪y, ∫ g : Formalism.REAL.UJ ε, φ (umat g) • word (trRep σ P) l (σ (umat g) w) ∂(Formalism.REAL.muG ε)⟫_ℂ
      = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ⟪y, word (trRep σ P) l (σ (umat g) w)⟫_ℂ ∂(Formalism.REAL.muG ε) := by
    intro y
    rw [← integral_inner (hφ.integrable hc)]
    congr 1
    funext g
    rw [← Complex.coe_smul, inner_smul_right, Complex.real_smul]
  rw [← key]
  congr 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint (gram_unit hP h) (isURepOn_trRep hP h hσ) hl hu
  rw [key, h2 _ (gard_mem hP h hσ hφ w), inner_gard hσ hφ]
  congr 1
  funext g
  rw [h2 _ (sigma_mem hP h hσ hw g.2)]

theorem sobCont_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  intro n ε H _ _ _ σ P G hP h hσ ℓ hℓ
  obtain ⟨m, ls, a, hls, hrep⟩ := _root_.GlobalTheory.SmVec.sobCont_repr n ε H σ P G hP h hσ ℓ hℓ
  refine ⟨fun φ hφ => ?_, fun w hw => ?_⟩
  · choose ψ _ hψ using fun i => word_gard hP h hσ hφ (ls i) (hls i)
    refine ⟨∑ i, ‖a i‖ * ∫ g : Formalism.REAL.UJ ε, |ψ i (umat g)| ∂(Formalism.REAL.muG ε), fun w => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w), Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [hψ, mul_assoc]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (norm_gard_le hσ _ w) (norm_nonneg _))
  · have e : ∀ g : Formalism.REAL.UJ ε, ℓ (σ (umat g) w) = ∑ i, ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun g => hrep _ (sigma_mem hP h hσ hw g.2)
    have hc : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ⟪a i, word (trRep σ P) (ls i) (σ (umat g) w)⟫_ℂ :=
      fun i => continuous_const.inner (_root_.GlobalTheory.SmVec.WordCont.continuous_word_translate n ε H σ P G hP h hσ (ls i) (hls i) w hw)
    simp only [e]
    refine ⟨continuous_finsetSum _ fun i _ => hc i, fun φ hφ => ?_⟩
    rw [hrep _ (gard_mem hP h hσ hφ w)]
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ fun i _ => hφ.integrable (hc i)]
    exact Finset.sum_congr rfl fun i _ => inner_word_gard hP h hσ hφ (ls i) (hls i) hw (a i)

end GlobalTheory.SobGarding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairInfTypes

theorem hasInfQ_tauE (D : D7) {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) (fun τ => a (D.eTau τ)) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Fintype.prod_equiv D.eTau _ _ fun _ => rfl).symm

theorem infTypesAt : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.InfTypesAt L i t τ := by
  intro D T L μ0 hL i t τ
  have h1 : HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 i) (hasInfQ_tauE D (L.C.isMu0 i).inf) τ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (hasInfQ_tauE D (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 : HasInfExp D (L.xi t) τ 0 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t) ⟨fun _ => 0, fun _ => by norm_num, fun k => ?_⟩ τ
    rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho k]
    simp
  have h4 : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i τ) := by
    have h := GlobalTheory.Mem.HeckeExp.hasInfExp_mul h1 h3
    rw [add_zero] at h
    exact h
  refine ⟨h4, h2, h4, ?_⟩
  rw [sub_eq_add_neg]
  exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul h4 (GlobalTheory.Mem.HeckeExp.hasInfExp_inv h2)

end GlobalTheory.PairInfTypes
end

