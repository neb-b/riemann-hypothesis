module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtSplitPlaceReframe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaAtReframe

section
variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

noncomputable def reFi : (WO (reS S b) T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := LinearMap.funLeft ℂ ℂ (reWi S T b)

theorem reWi_add (x y : WO S T) : reWi S T b (x + y) = reWi S T b x + reWi S T b y := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_reWi S T b y, ← reW_add, reWi_reW]

theorem reWi_nsmul (k : ℕ) (x : WO S T) : reWi S T b (k • x) = k • reWi S T b x := by
  conv_lhs => rw [← reW_reWi S T b x, ← reW_nsmul, reWi_reW]

theorem isHalf_reWi_iff (e : AE D) (x : WO S T) : IsHalf e (reWi S T b x) ↔ IsHalf e x := by
  have h := isHalf_reW_iff S T b e (reWi S T b x)
  rw [reW_reWi] at h
  exact h.symm

theorem reF_reFi (g : WO (reS S b) T → ℂ) : reF S T b (reFi S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reWi_reW]

theorem reFi_reF (g : WO S T → ℂ) : reFi S T b (reF S T b g) = g := by
  funext x
  simp only [reF, reFi, LinearMap.funLeft_apply, reW_reWi]

theorem heisO_reFi (ψ : AddChar (AF D.host.F) ℂ)
    (hB : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (g : WO (reS S b) T → ℂ) :
    reFi S T b (heisO ψ (reS S b) T u g) = heisO ψ S T (reW S T b u) (reFi S T b g) := by
  have h := heisO_reF S T b ψ hB u (reFi S T b g)
  rw [reF_reFi] at h
  rw [h, reFi_reF]

variable (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T))

theorem isSBHalf_comp_reW (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Φ : WO S T → ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ' (fun x => Φ (reW S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reW_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reW_add, reW_nsmul]
    exact h2 _ ((hΛ u).1 hu) ((isHalf_reW_iff S T b e u).2 hh) _
  · intro t ht
    rw [hΛ, reW_nsmul]
    exact h3 _ ht

theorem isSBHalf_comp_reWi (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) (Ψ : WO (reS S b) T → ℂ)
    (h : IsSBHalf e Λ' Ψ) : IsSBHalf e Λ (fun x => Ψ (reWi S T b x)) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  refine ⟨fun t ht => (isHalf_reWi_iff S T b e t).1 (h1 _ ht), k, hk, ?_, ?_⟩
  · intro u hu hh t
    simp only [reWi_add, reWi_nsmul]
    exact h2 _ ((hΛ _).2 (by rwa [reW_reWi])) ((isHalf_reWi_iff S T b e u).2 hh) _
  · intro t ht
    have h4 := (hΛ _).1 (h3 _ ht)
    rwa [reW_nsmul, reW_reWi] at h4

theorem reF_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reF S T b (halfInd e Λ) = halfInd e Λ' := by
  funext x
  simp only [reF, LinearMap.funLeft_apply, halfInd, ← hΛ, isHalf_reW_iff]

theorem reFi_halfInd (hΛ : ∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) :
    reFi S T b (halfInd e Λ') = halfInd e Λ := by
  rw [← reF_halfInd S T b e Λ Λ' hΛ, reFi_reF]

end

theorem isThetaAt_reframe : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := by
  intro D ψ S T b e Λ Λ' c f₀ Φ f hB hΛ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  refine ⟨⟨(reF S T b) ∘ₗ Tm ∘ₗ reFi S T b, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro Ψ hΨ x hx
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => Ψ (t + x)) =
          fun s => (fun s' => Ψ (reWi S T b s')) (s + reW S T b x) := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, reWi_add, reWi_reW]
      rw [h1, hTm.trans _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b e x).2 hx), ← heisO_reF S T b ψ hB]
      rfl
    · intro Ψ hΨ y hy
      simp only [LinearMap.comp_apply]
      have h1 : reFi S T b (fun t => ψ (symplO (reS S b) T t y) * Ψ t) =
          fun s => ψ (symplO S T s (reW S T b y)) * (fun s' => Ψ (reWi S T b s')) s := by
        funext s
        simp only [reFi, LinearMap.funLeft_apply, hB, reW_reWi]
      rw [h1, hTm.modul _ (isSBHalf_comp_reWi S T b e Λ Λ' hΛ Ψ hΨ) _
        ((isHalf_reW_iff S T b _ y).2 hy), ← heisO_reF S T b ψ hB]
      rfl
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, map_smul (reFi S T b),
        reFi_halfInd S T b e Λ Λ' hΛ, hTm.vac]
  · intro Tm' hTm'
    let Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) := reFi S T b ∘ₗ Tm' ∘ₗ reF S T b
    have hPM : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => Φ (t + x)) =
            fun s => (fun s' => Φ (reW S T b s')) (s + reWi S T b x) := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, reW_add, reW_reWi]
        rw [h1, hTm'.trans _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b e x).2 hx), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · intro Φ hΦ y hy
        simp only [Tm, LinearMap.comp_apply]
        have h1 : reF S T b (fun t => ψ (symplO S T t y) * Φ t) =
            fun s => ψ (symplO (reS S b) T s (reWi S T b y)) * (fun s' => Φ (reW S T b s')) s := by
          funext s
          simp only [reF, LinearMap.funLeft_apply, hB, reW_reWi]
        rw [h1, hTm'.modul _ (isSBHalf_comp_reW S T b e Λ Λ' hΛ Φ hΦ) _
          ((isHalf_reWi_iff S T b _ y).2 hy), heisO_reFi S T b ψ hB, reW_reWi]
        rfl
      · simp only [Tm, LinearMap.comp_apply]
        rw [map_smul (reF S T b), reF_halfInd S T b e Λ Λ' hΛ, hTm'.vac, reFi_reF]
    rw [hall Tm hPM]
    exact reF_reFi S T b _

end GlobalTheory.ThetaAtReframe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevCong

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  intro v
  simp only [map_one]
  exact one_mem _

theorem toAf_mem_hatV {k : ℕ} {L : Lt D.host.E k} {x : Fin k → D.host.E} (hx : x ∈ L) :
    toAf (D := D) x ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hx, rfl⟩

theorem hatV_mono {k : ℕ} {L L' : Lt D.host.E k} (h : L ≤ L') : hatV (D := D) L ≤ hatV L' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem toAf_add {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x + y) = toAf x + toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_add]

theorem toAf_sub {k : ℕ} (x y : Fin k → D.host.E) : toAf (D := D) (x - y) = toAf x - toAf y := by
  funext i; simp [toAf, TensorProduct.tmul_sub]

theorem toAf_zero {k : ℕ} : toAf (D := D) (0 : Fin k → D.host.E) = 0 := by
  funext i; simp [toAf]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (x : Fin k → D.host.E) :
    toAf (D := D) (c • x) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • toAf x := by
  funext i
  simp [toAf, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem smul_mem_hatV {k : ℕ} (c : 𝓞 D.host.E) {L L' : Lt D.host.E k} (h : ∀ x ∈ L, c • x ∈ L')
    {u : Fin k → AfE D} (hu : u ∈ hatV L) :
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, h x hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

section
variable {r : ℕ} (m : Matrix (Fin r) (Fin r) (AfE D))

theorem fadd (x y : Fin r → D.host.E) : m *ᵥ toAf (D := D) (x + y) - toAf (x + y) =
    (m *ᵥ toAf x - toAf x) + (m *ᵥ toAf y - toAf y) := by
  rw [toAf_add, Matrix.mulVec_add]; abel

theorem fsmul (c : 𝓞 D.host.E) (x : Fin r → D.host.E) : m *ᵥ toAf (D := D) (c • x) - toAf (c • x) =
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • (m *ᵥ toAf x - toAf x) := by
  rw [toAf_smul, Matrix.mulVec_smul, smul_sub]

theorem sum_one_smul (β : Fin r → Fin r → D.host.E) (i : Fin r) :
    ∑ j, (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i • β j = β i := by
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_sub_one (β : Fin r → Fin r → D.host.E) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (i : Fin r) :
    ∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j = ∑ j, κ' j i • β j - β i := by
  rw [← sum_one_smul β i, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul]
end

theorem mem_of_smul {r : ℕ} (Λ : Lt D.host.E r) (𝔪 I : Ideal (𝓞 D.host.E)) (h𝔪I : 𝔪 ≤ I)
    (m : Matrix (Fin r) (Fin r) (AfE D)) (hmov : IsMov m Λ Λ) :
    ∀ t ∈ 𝔪 • Λ, m *ᵥ toAf (D := D) t - toAf t ∈ hatV (I • Λ) := by
  intro t ht
  refine Submodule.smul_induction_on ht ?_ ?_
  · intro p hp y hy
    have h1 : m *ᵥ toAf (D := D) y ∈ hatV Λ := (hmov _).2 ⟨_, toAf_mem_hatV hy, rfl⟩
    rw [fsmul]
    rw [smul_sub]
    refine sub_mem (smul_mem_hatV p (fun x hx => Submodule.smul_mem_smul (h𝔪I hp) hx) h1) ?_
    rw [← toAf_smul]; exact toAf_mem_hatV (Submodule.smul_mem_smul (h𝔪I hp) hy)
  · intro x y hx hy; rw [fadd]; exact add_mem hx hy

theorem mem_of_span {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E))
    (hβ : ∀ i, β i ∈ Λ) (h𝔪I : 𝔪 ≤ I) (m : Matrix (Fin r) (Fin r) (AfE D))
    (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E))
    (hκ : ∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I)
    (hfr : ∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) :
    ∀ s ∈ Submodule.span (𝓞 D.host.E) (Set.range β), m *ᵥ toAf (D := D) s - toAf s ∈ hatV (I • Λ) := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have e : m *ᵥ toAf (D := D) (β i) - toAf (β i) = (m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j)) +
        toAf (∑ j, (κ' j i - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) j i) • β j) := by
      rw [sum_sub_one, toAf_sub, sub_add_sub_cancel]
    rw [e]
    exact add_mem (hatV_mono (Submodule.smul_mono_left h𝔪I) (hfr i))
      (toAf_mem_hatV (sum_mem fun j _ => Submodule.smul_mem_smul (hκ j i) (hβ j)))
  | zero => rw [toAf_zero, Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [fadd]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [fsmul]; exact smul_mem_hatV c (fun y hy => Submodule.smul_mem _ c hy) hx

theorem cong_of_frame : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  intro D r Λ β 𝔪 I hβ hspan h𝔪I m κ' hκ hmov hfr x hx
  obtain ⟨s, hs', t, ht', rfl⟩ := Submodule.mem_sup.1 (hspan hx)
  rw [fadd]
  exact add_mem (mem_of_span Λ β 𝔪 I hβ h𝔪I m κ' hκ hfr s hs') (mem_of_smul Λ 𝔪 I h𝔪I m hmov t ht')

end GlobalTheory.LevCong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelAndTwistPlacesSplitDistinct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistTypePlaces

theorem card_quot_of_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hr : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E))
    (h2 : (Ideal.primesOver (P.under (𝓞 F)).asIdeal (𝓞 E)).ncard = 2) :
    Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm (P.under (𝓞 F)).asIdeal := by
  classical
  set p := (P.under (𝓞 F)).asIdeal with hp
  have hp0 : p ≠ ⊥ := (P.under (𝓞 F)).ne_bot
  have : p.IsMaximal := (P.under (𝓞 F)).isMaximal
  have : P.asIdeal.LiesOver p := ⟨by rw [hp, HeightOneSpectrum.under_asIdeal]⟩
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E (p := p) hp0
  have hcard : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = 2 := by
    rw [← h2, ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 E), Set.ncard_coe_finset]
  have hle : ∀ Q ∈ IsDedekindDomain.primesOverFinset p (𝓞 E), 1 ≤ p.ramificationIdx' Q * p.inertiaDeg' Q := by
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).1 hQ
    have h1 : 0 < p.inertiaDeg' Q := Ideal.inertiaDeg'_pos p Q
    have h2 : 0 < p.ramificationIdx' Q := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]
      exact Ideal.ramificationIdx_pos (R := 𝓞 F) Q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h2.ne' h1.ne')
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hsum, hr, Finset.sum_const, hcard]; rfl)
  have hPm : P.asIdeal ∈ IsDedekindDomain.primesOverFinset p (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 E)).2 ⟨P.isPrime, inferInstance⟩
  have hf : p.inertiaDeg' P.asIdeal = 1 := Nat.eq_one_of_mul_eq_one_left (heq _ hPm).symm
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p (P.under (𝓞 F)).isPrime hp0
  rw [hf, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  exact hn

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem under_conjPl {D : D7} (P : Pl D.host.E) :
    (conjPl P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  have hfix : ∀ x : 𝓞 D.host.F,
      Formalism.DivisionValues.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    intro x
    apply RingOfIntegers.ext
    show star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) = _
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  have hinv : ∀ z, Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E z) = z :=
    fun z => RingOfIntegers.ext (star_star (z : D.host.E))
  apply HeightOneSpectrum.ext
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]
  change algebraMap _ _ x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have e : z = algebraMap _ _ x := by rw [← hinv z, hzx, hfix]
    rwa [← e]
  · intro h
    exact ⟨_, h, hfix x⟩

theorem natCast_mem_conjPl {D : D7} (P : Pl D.host.E) (n : ℕ) (h : (n : 𝓞 D.host.E) ∈ P.asIdeal) :
    (n : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h
  rwa [map_natCast] at this

theorem ncard_primesOver_two {D : D7} (P : Pl D.host.E) (h : conjPl P ≠ P) :
    (Ideal.primesOver (P.under (𝓞 D.host.F)).asIdeal (𝓞 D.host.E)).ncard = 2 := by
  rw [GlobalTheory.QuadSignLocal.ncard_primesOver]
  have hs : {u : HeightOneSpectrum (𝓞 D.host.E) | u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)} = {P, conjPl P} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq
    · rintro (rfl | rfl)
      · rfl
      · exact under_conjPl P
  rw [hs, Set.ncard_pair h.symm]

theorem natCast_not_mem_of_card {E : Type} [Field E] [NumberField E] (PP : Pl E) {q g : ℕ} (hq : q.Prime) (hg : g.Prime)
    (hc : Nat.card (kP PP) = q) (hne : q ≠ g) : ((g : ℕ) : 𝓞 E) ∉ PP.asIdeal := by
  intro hm
  have hnt : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hq0 : ((q : ℕ) : kP PP) = 0 := by
    have := card_nsmul_eq_zero' (G := kP PP) (x := 1)
    rwa [hc, nsmul_one] at this
  have hg0 : ((g : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (g : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hg).2 hne)
  have h1 : ((a * q + b * g : ℤ) : kP PP) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  rw [hq0, hg0, mul_zero, mul_zero, add_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.TwistTypePlaces

namespace GlobalTheory.TwistTypePlaces

theorem places_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ↑(R.Pg ∪ R.Q t) ∧ ∀ PP ∈ R.Pg ∪ R.Q t, (Ideal.primesOver ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal (𝓞 D.host.E)).ncard = 2 ∧ Nat.card (kP PP) = Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  have hPg := hL.Pg
  have hQ := hL.Q_pl t
  have gP : ∀ PP ∈ R.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP h
    obtain ⟨k, hk⟩ := (hPg PP).1 h
    exact ⟨k, R.C.P.overP hk⟩
  have qN : ∀ PP ∈ R.Q t, ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP h k
    obtain ⟨q, hq, hc, -, hne⟩ := (hQ PP h).1
    exact natCast_not_mem_of_card PP hq (D.host.g_prime k) hc (hne k)
  have hdis : Disjoint R.Pg (R.Q t) := by
    rw [Finset.disjoint_left]
    intro PP h1 h2
    obtain ⟨k, hk⟩ := gP PP h1
    exact qN PP h2 k hk
  have cross : ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Q t, PP' ≠ conjPl PP := by
    rintro PP h PP' h' rfl
    obtain ⟨k, hk⟩ := gP PP h
    exact qN _ h' k (natCast_mem_conjPl PP _ hk)
  have hnc : ∀ PP ∈ R.Pg ∪ R.Q t, ∀ PP' ∈ R.Pg ∪ R.Q t, PP' ≠ conjPl PP := by
    intro PP h PP' h' e
    rcases Finset.mem_union.1 h with h | h <;> rcases Finset.mem_union.1 h' with h' | h'
    · exact GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hPg PP h PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
    · exact cross PP h PP' h' e
    · refine cross PP' h' PP h ?_
      rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    · exact (hQ PP h).2 PP' h' (GlobalTheory.GoodPrimes.isConjPl_iff.2 e)
  refine ⟨hdis, ?_, ?_⟩
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact e'.symm
    · exact absurd e' (hnc PP h PP' h')
  · intro PP h
    have h2 := ncard_primesOver_two PP (fun e => hnc PP h PP h e.symm)
    exact ⟨h2, card_quot_of_two D.sp.cm.deg2 PP h2⟩

end GlobalTheory.TwistTypePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.InertHomIdx

variable {D : D7}

def compW (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.compAt D.host.F w).comp (finPart D)

def matW (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.FinWeilO.XF S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) where
  toFun x := (x : WO S T).map (compW D w)
  map_zero' := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_zero]
  map_add' x y := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_add]

theorem matW_apply (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : GlobalTheory.FinWeilO.XF S T) :
    matW S T w x = (x : WO S T).map (compW D w) := rfl

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) L) where
  carrier := {X | ∀ i j, X i j ∈ Formalism.UG.intL L}
  add_mem' hX hY i j := add_mem (hX i j) (hY i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hX i j := neg_mem (hX i j)

theorem mem_intMat {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) L} : X ∈ intMat L m n ↔ ∀ i j, X i j ∈ Formalism.UG.intL L := Iff.rfl

def lmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := g * X
  map_zero' := Matrix.mul_zero g
  map_add' := Matrix.mul_add g

theorem lmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) (X : Matrix (Fin m) (Fin n) L) :
    lmul g X = g * X := rfl

end GlobalTheory.InertHomIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrability
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumFockLaws

theorem vacuumFock_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D :=
  fun D => vacuumFock_of_thetaSquareIntegrable D (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D)

end GlobalTheory.VacuumFockLaws
end

