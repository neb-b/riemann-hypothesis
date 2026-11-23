module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Lean

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Transfer

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X]

theorem isCell_transfer {φ : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hφ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; φ.eval X B) = (letI := m2; letI := f2; φ.eval X B))
    {k : ℕ} {γ : Fin k → LinearMap.BilinForm ℤ X} (h : letI := m1; letI := f1; IsCell bar φ γ) :
    letI := m2; letI := f2; IsCell bar φ γ := by
  obtain ⟨hm, hn, hl, hs⟩ := h
  have hZ : ∀ β : LinearMap.BilinForm ℤ X, (letI := m1; letI := f1; φ.evalZ β) = (letI := m2; letI := f2; φ.evalZ β) :=
    fun β => hφ _
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hs
  letI := m2
  letI := f2
  refine ⟨fun i => (hbal _).1 (hm i), hn, fun c hc => ?_, N, ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← hφ]
    simp only [← hZ]
    exact hl c hc
  · rw [← hZ]; exact h1 i
  · rw [← hZ]; exact h2 β ((hbal β).2 hβ) hp
  · exact h3 β ((hbal β).2 hβ) hp (by rw [hZ]; exact he)

theorem isStarDepth_transfer {ψ w : InvFun O} (m1 m2 : Module O X) (f1 : letI := m1; Module.Finite O X)
    (f2 : letI := m2; Module.Finite O X)
    (hbal : ∀ β, β ∈ (letI := m1; balForms bar X) ↔ β ∈ (letI := m2; balForms bar X))
    (hψ : ∀ B : X → X → ℝ, (letI := m1; letI := f1; ψ.eval X B) = (letI := m2; letI := f2; ψ.eval X B))
    (hw : ∀ B : X → X → ℝ, (letI := m1; letI := f1; w.eval X B) = (letI := m2; letI := f2; w.eval X B))
    {B₁ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {t : ℝ} (h : letI := m1; letI := f1; IsStarDepth bar ψ w B₁ t) :
    letI := m2; letI := f2; IsStarDepth bar ψ w B₁ t := by
  obtain ⟨ht, k, γ, v, hc, hv, hpos, hw1, hin, hB, hBt⟩ := h
  exact ⟨ht, k, γ, v, isCell_transfer bar m1 m2 f1 f2 hbal hψ hc, (hbal v).1 hv, hpos, (hw _).symm.trans hw1, hin, hB,
    hBt⟩

end Transfer

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem host_bar_map_comm (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem mem_balForms_twist (τ : 𝓞 E ≃+* 𝓞 E) (β : LinearMap.BilinForm ℤ X) :
    β ∈ balForms H.bar X ↔ β ∈ (letI := Module.compHom X τ.toRingHom; balForms H.bar X) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    show β (τ a • y) z = β y (τ (H.bar a) • z)
    rw [h2, host_bar_map_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a y z => ?_⟩
    have := h2 (τ.symm a) y z
    change β (τ (τ.symm a) • y) z = β y (τ (H.bar (τ.symm a)) • z) at this
    rwa [host_bar_map_comm, τ.apply_symm_apply] at this

theorem eval_twist_of_isTwInv {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (τ : 𝓞 E ≃+* 𝓞 E) (hτ : τ H.w0 = H.w0)
    [Module.Finite (𝓞 E) X] (hf : letI := Module.compHom X τ.toRingHom; Module.Finite (𝓞 E) X) (B : X → X → ℝ) :
    φ.eval X B = (letI := Module.compHom X τ.toRingHom; letI := hf; φ.eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  rw [φ.eval_eq hr, ← hφ τ hτ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => τ.symm (a i), funext fun i => τ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ τ.toRingHom
  letI := hf
  exact (φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _).symm


omit [Module (𝓞 E) X] in
theorem depthSet_twist_subset {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hw : IsTwInv H w) (σ : 𝓞 E ≃+* 𝓞 E)
    (hσ : σ H.w0 = H.w0) (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ) :
    depthSet H.bar ψ w n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ⊆ depthSet H.bar ψ w n B := by
  rintro t ⟨X₁, i1, i2, i3, r, B₁, hr, hrad, hB, hd⟩
  set τ := σ.symm with hτdef
  have hτ : τ H.w0 = H.w0 := (σ.symm_apply_eq).2 hσ.symm
  let g : (Fin n → 𝓞 E) →+ X₁ := r.toAddMonoidHom.comp
    ⟨⟨fun a i => τ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = τ c • g a := fun c a => by
    change r _ = τ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ (a i), funext fun i => σ.symm_apply_apply _⟩
  have hgB : ∀ a b, B a b = B₁ (g a) (g b) := fun a b => by
    have := hB (fun i => τ (a i)) (fun i => τ (b i))
    simp only [hτdef, RingEquiv.apply_symm_apply] at this
    exact this
  have hf' : letI := Module.compHom X₁ τ.toRingHom; Module.Finite (𝓞 E) X₁ := by
    letI := Module.compHom X₁ τ.toRingHom
    exact Module.Finite.of_surjective (⟨g.toAddHom, hg⟩ : (Fin n → 𝓞 E) →ₗ[𝓞 E] X₁) hs
  have hd' := isStarDepth_transfer H.bar i2 (Module.compHom X₁ τ.toRingHom) i3 hf' (mem_balForms_twist H τ)
    (eval_twist_of_isTwInv H hψ τ hτ hf') (eval_twist_of_isTwInv H hw τ hτ hf') hd
  letI := Module.compHom X₁ τ.toRingHom
  exact ⟨X₁, i1, _, hf', ⟨g.toAddHom, hg⟩, B₁, hs, hrad, hgB, hd'⟩

theorem isTwInv_starDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  intro E _ _ _ H ψ w hψ hw σ hσ n B
  show sSup _ = sSup _
  congr 1
  refine Set.Subset.antisymm (depthSet_twist_subset H hψ hw σ hσ n B) ?_
  have h := depthSet_twist_subset H hψ hw σ.symm ((σ.symm_apply_eq).2 hσ.symm) n
    (fun a b => B (fun i => σ (a i)) (fun i => σ (b i)))
  simpa only [RingEquiv.apply_symm_apply] using h

end Twist

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.CoverSuper

theorem mul_evalR_le {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {e : X ≃ₗ[O] X} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hγ : IsCell bar φ γ) (hc : ∀ i, 0 ≤ c i)
    (hB : pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) (f : X ≃ₗ[O] X) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hℓ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (N : ℝ) * φ.evalZ β ≤ ℓ β) :
    (N : ℝ) * evalR φ B ≤ ∑ i, c i * (ℓ (pull (f.trans e.symm).toLinearMap (γ i)) : ℝ) ∧
      pullR f.toLinearMap B = ∑ i, c i • toReal (pull (f.trans e.symm).toLinearMap (γ i)) := by
  have hB' : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hB a b
  have hev : evalR φ B = ∑ i, c i * φ.evalZ (γ i) :=
    hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc hB'
  refine ⟨?_, LinearMap.ext₂ fun a b => ?_⟩
  · rw [hev, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hℓ _ (pull_mem (f.trans e.symm).toLinearMap (hγ.mem i)) (fun y => hγ.nonneg i _)
    rw [evalZ_pull φ (f.trans e.symm).surjective] at h1
    calc (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * (N * φ.evalZ (γ i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hc i)
  · have := hB' (e.symm (f a)) (e.symm (f b))
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearMap.sum_apply, this]

theorem add_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone (bar := bar) (X := X)) (hB' : B' ∈ psdCone (bar := bar) (X := X)) : B + B' ∈ psdCone (bar := bar) (X := X) := by
  obtain ⟨m₁, γ₁, c₁, h1, h2, h3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B hB
  obtain ⟨m₂, γ₂, c₂, k1, k2, k3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B' hB'
  have := ConeSub.sum_smul_toReal_mem_psdCone O bar X (m₁ + m₂) (Fin.append γ₁ γ₂) (Fin.append c₁ c₂)
    (fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using k1 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h2 j) (fun j => by simpa using k2 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h3 j) (fun j => by simpa using k3 j) i)
  simpa [Fin.sum_univ_add] using this

theorem superadd_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) →
    ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X), evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  intro O _ _ _ _ bar φ X _ _ _ hcov B hB B' hB'
  have hBB := add_mem_psdCone O bar X hB hB'
  obtain ⟨e₁, m₁, γ₁, c₁, hγ₁, hc₁, h₁⟩ := hcov B hB
  obtain ⟨e₂, m₂, γ₂, c₂, hγ₂, hc₂, h₂⟩ := hcov B' hB'
  obtain ⟨e₃, m₃, γ₃, c₃, hγ₃, hc₃, h₃⟩ := hcov (B + B') hBB
  obtain ⟨N, ℓ, hN, hℓ1, hℓ2, -⟩ := hγ₃.strict
  obtain ⟨i1, j1⟩ := mul_evalR_le hγ₁ hc₁ h₁ e₃ hℓ2
  obtain ⟨i2, j2⟩ := mul_evalR_le hγ₂ hc₂ h₂ e₃ hℓ2
  have hev3 : evalR φ (B + B') = ∑ i, c₃ i * φ.evalZ (γ₃ i) :=
    hγ₃.linear.eval_eq_sum (r := e₃.toLinearMap) e₃.surjective hc₃ fun a b => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h₃ a b
  have hN3 : (N : ℝ) * evalR φ (B + B') = ∑ i, c₃ i * (ℓ (γ₃ i) : ℝ) := by
    rw [hev3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hℓ1 i]; ring
  have hpull : pullR e₃.toLinearMap (B + B') = pullR e₃.toLinearMap B + pullR e₃.toLinearMap B' :=
    LinearMap.ext₂ fun a b => by simp
  have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
    (β := Sum.elim (Sum.elim (fun i => pull (e₃.trans e₁.symm).toLinearMap (γ₁ i))
      (fun i => pull (e₃.trans e₂.symm).toLinearMap (γ₂ i))) γ₃)
    (c := Sum.elim (Sum.elim c₁ c₂) (-c₃)) (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib]
      rw [← j1, ← j2, ← h₃, hpull]
      abel)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at rel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * (evalR φ B + evalR φ B') ≤ N * evalR φ (B + B') := by
    rw [mul_add, hN3]
    linarith
  exact le_of_mul_le_mul_left key hNpos

end GlobalTheory.PolFan.CoverSuper
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WithLocPre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure Mv (D : D7) : Type 1 where
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ
  dsig : D.what₂.Tau → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData D.R (↥D.host.F) D.host.E D.conjF D.what₂.Word D.what₂.Tau D.hcW
  s_split : ∀ p : HeightOneSpectrum (𝓞 ↥D.host.F),
    (s.atP p).split.isSome = true ↔ Formalism.MainNotions.S.Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = D.what₂.Dall
  s_Cu : (u : D.what₂.Word) → s.Cu u ≃ₗ[ℂ] ↥(D.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 ↥D.host.F)
  s_Cu_isom : ∀ (u : D.what₂.Word) (x y : s.Cu u), inner ℂ x y = (D.fm u).ipC 0 ↑((s_Cu u) x) ↑((s_Cu u) y)
  sEE : D.what₂.EE →ₗᵢ⋆[ℂ] s.HH

abbrev Mv.D {D : D7} (m : Mv D) : D7 :=
  { (setDiv D m.N m.h) with
    dsig := m.dsig
    dsig_pos := m.dsig_pos
    s := m.s
    s_split := m.s_split
    s_HH := m.s_HH
    s_Cu := m.s_Cu
    s_PlF := m.s_PlF
    s_Cu_isom := m.s_Cu_isom
    sEE := m.sEE }

section
variable {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) (S' : SStage B w.C Z.W)
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def mvOf : Mv (w.D Z) :=
  ⟨N, h, (w.D (upL Z S' N h)).dsig, (w.D (upL Z S' N h)).dsig_pos, (w.D (upL Z S' N h)).s, (w.D (upL Z S' N h)).s_split,
    (w.D (upL Z S' N h)).s_HH, (w.D (upL Z S' N h)).s_Cu, (w.D (upL Z S' N h)).s_PlF, (w.D (upL Z S' N h)).s_Cu_isom,
    (w.D (upL Z S' N h)).sEE⟩

end

variable {D : D7} (m : Mv D)

def Mv.pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) : Mv D₀ :=
  { N := (by with_unfolding_all exact (m.N :))
    h := (by with_unfolding_all exact (m.h :))
    dsig := (by with_unfolding_all exact (m.dsig :))
    dsig_pos := (by with_unfolding_all exact (m.dsig_pos :))
    s := (by with_unfolding_all exact (m.s :))
    s_split := (by with_unfolding_all exact (m.s_split :))
    s_HH := (by with_unfolding_all exact (m.s_HH :))
    s_Cu := (by with_unfolding_all exact (m.s_Cu :))
    s_PlF := (by with_unfolding_all exact (m.s_PlF :))
    s_Cu_isom := (by with_unfolding_all exact (m.s_Cu_isom :))
    sEE := (by with_unfolding_all exact (m.sEE :)) }

def Mv.loc (L : LocAll (lay0 D)) : LocAll (lay0 m.D) := (by with_unfolding_all exact (L :))

theorem Mv.withLoc_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) : m.D = withLoc (m.pre.loc L) := (by with_unfolding_all exact ((Eq.refl m.D) :))

def Mv.cf (cf : CharFrame D) : CharFrame m.D :=
  { P := (by with_unfolding_all exact (cf.P :))
    W := (by with_unfolding_all exact (cf.W :))
    mu0 := (by with_unfolding_all exact (cf.mu0 :))
    eta := (by with_unfolding_all exact (cf.eta :))
    chiPsi := (by with_unfolding_all exact (cf.chiPsi :))
    del := (by with_unfolding_all exact (cf.del :))
    del' := (by with_unfolding_all exact (cf.del' :))
    isMu0 := (by with_unfolding_all exact (cf.isMu0 :))
    isEta := (by with_unfolding_all exact (cf.isEta :))
    isChi := (by with_unfolding_all exact (cf.isChi :))
    isDel := (by with_unfolding_all exact (cf.isDel :))
    isDel' := (by with_unfolding_all exact (cf.isDel' :)) }

def Mv.ch (C : NChoice D) : NChoice m.D := { C with }

def Mv.xd (x : ThData D) : ThData m.D := { x with }

def Mv.tp {cf : CharFrame D} {C : NChoice D} (tp : TupTied D cf C) : TupTied m.D (m.cf cf) (m.ch C) :=
  { xi := (by with_unfolding_all exact (tp.xi :))
    xi_inj := (by with_unfolding_all exact (tp.xi_inj :))
    xi_fin := (by with_unfolding_all exact (tp.xi_fin :))
    xi_triv := (by with_unfolding_all exact (tp.xi_triv :))
    xi_tame := (by with_unfolding_all exact (tp.xi_tame :))
    psi := (by with_unfolding_all exact (tp.psi :))
    trueColumnChoices_heckeChar_reference_eq_one := (by with_unfolding_all exact (tp.trueColumnChoices_heckeChar_reference_eq_one :))
    xi_star := (by with_unfolding_all exact (tp.xi_star :))
    xi_star' := (by with_unfolding_all exact (tp.xi_star' :))
    xi_tw := (by with_unfolding_all exact (tp.xi_tw :))
    psi_is := (by with_unfolding_all exact (tp.psi_is :))
    psi_un := (by with_unfolding_all exact (tp.psi_un :)) }

def Mv.mt (M : Formalism.L2.MtFam D) : Formalism.L2.MtFam m.D := @fun x1 => @fun x2 => @fun x3 => @fun x4 =>
  { wt := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).wt : _))
    J := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).J : _))
    χ := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).χ : _))
    J_open := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).J_open : _))
    real := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real : _))
    real_inj := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real_inj : _))
    real_range := (by with_unfolding_all exact ((@M ((x1)) ((x2)) ((x3)) ((x4))).real_range : _)) }

end GlobalTheory.LayerMove
end
end

