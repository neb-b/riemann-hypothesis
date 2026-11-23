module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.ExistsIsAlgebraicRatFuncFractionRingDedekind
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.Development
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
section
noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowestDataIso

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (lowK)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (LocFin IsMin Cyc mem_cyc cyc_stab hMultAlg)

variable {n : ℕ} {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

def fstL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V :=
  LinearMap.fst ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def sndL (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] : WithLp 2 (V × V') →ₗ[ℂ] V' :=
  LinearMap.snd ℂ V V' ∘ₗ (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

def pair (x : V) (y : V') : WithLp 2 (V × V') := WithLp.toLp 2 (x, y)

theorem ext2 {x y : WithLp 2 (V × V')} (h₁ : fstL V V' x = fstL V V' y) (h₂ : sndL V V' x = sndL V V' y) : x = y :=
  WithLp.ofLp_injective _ (Prod.ext h₁ h₂)

theorem inner_eq (x y : WithLp 2 (V × V')) :
    ⟪x, y⟫_ℂ = ⟪fstL V V' x, fstL V V' y⟫_ℂ + ⟪sndL V V' x, sndL V V' y⟫_ℂ :=
  WithLp.prod_inner_apply x y

def sumE (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n) :
    Module.End ℂ (WithLp 2 (V × V')) :=
  (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ (E a b).prodMap (E' a b) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (V × V')).toLinearMap

variable {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}

@[simp] theorem fstL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    fstL V V' (sumE E E' a b x) = E a b (fstL V V' x) := rfl

@[simp] theorem sndL_sumE (a b : Fin n) (x : WithLp 2 (V × V')) :
    sndL V V' (sumE E E' a b x) = E' a b (sndL V V' x) := rfl

theorem glRel_sumE (hE : GlRel E) (hE' : GlRel E') : GlRel (sumE E E') := by
  intro a b c d
  refine LinearMap.ext fun x => ?_
  have h₁ := LinearMap.congr_fun (hE a b c d) (fstL V V' x)
  have h₂ := LinearMap.congr_fun (hE' a b c d) (sndL V V' x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h₁ h₂
  refine ext2 ?_ ?_
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all
  · by_cases p : b = c <;> by_cases q : d = a <;> simp_all

theorem kUnit_sumE {ε : Fin n → Bool} (hU : KUnit ε E) (hU' : KUnit ε E') : KUnit ε (sumE E E') := by
  intro a b hab x y
  rw [inner_eq, inner_eq, fstL_sumE, sndL_sumE, fstL_sumE, sndL_sumE, hU a b hab, hU' a b hab]

theorem locFin_sumE {ε : Fin n → Bool} (hF : LocFin ε E) (hF' : LocFin ε E') : LocFin ε (sumE E E') := by
  intro x
  obtain ⟨S, hS, hk, hx⟩ := hF (fstL V V' x)
  obtain ⟨S', hS', hk', hx'⟩ := hF' (sndL V V' x)
  have hfg : (S.prod S').FG :=
    Submodule.FG.prod (Module.Finite.iff_fg.1 hS) (Module.Finite.iff_fg.1 hS')
  refine ⟨(S.prod S').map (WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap,
    Module.Finite.iff_fg.2 (hfg.map _), ?_, ?_⟩
  · rintro a b hab _ ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    exact ⟨(E a b y.1, E' a b y.2), ⟨hk a b hab _ hy₁, hk' a b hab _ hy₂⟩, rfl⟩
  · exact ⟨(fstL V V' x, sndL V V' x), ⟨hx, hx'⟩, rfl⟩

theorem kHighest_fst {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E μ (fstL V V' x) :=
  ⟨fun a => by rw [← fstL_sumE (E' := E'), h.1 a, map_smul],
    fun a b hab he => by rw [← fstL_sumE (E' := E'), h.2 a b hab he, map_zero]⟩

theorem kHighest_snd {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : WithLp 2 (V × V')}
    (h : KHighest ε (sumE E E') μ x) : KHighest ε E' μ (sndL V V' x) :=
  ⟨fun a => by rw [← sndL_sumE (E := E), h.1 a, map_smul],
    fun a b hab he => by rw [← sndL_sumE (E := E), h.2 a b hab he, map_zero]⟩

theorem kHighest_pair {ε : Fin n → Bool} {μ : Fin n → ℝ} {x : V} {y : V'} (h : KHighest ε E μ x)
    (h' : KHighest ε E' μ y) : KHighest ε (sumE E E') μ (pair x y) :=
  ⟨fun a => ext2 (by simpa [fstL, sndL, pair, sumE] using h.1 a) (by simpa [fstL, sndL, pair, sumE] using h'.1 a),
    fun c d hcd he => ext2 (by simpa [fstL, sndL, pair, sumE] using h.2 c d hcd he) (by simpa [fstL, sndL, pair, sumE] using h'.2 c d hcd he)⟩

theorem isMin_sumE {ε : Fin n → Bool} {lam : Fin n → ℝ} (hM : IsMin ε E lam) (hM' : IsMin ε E' lam) :
    IsMin ε (sumE E E') lam := by
  intro μ x hx h
  by_cases h₁ : fstL V V' x = 0
  · refine hM' μ _ (fun h₂ => hx ?_) (kHighest_snd h)
    exact ext2 (by simpa using h₁) (by simpa using h₂)
  · exact hM μ _ h₁ (kHighest_fst h)

theorem exists_iso_of_highest {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hE : GlRel E)
    (hE' : GlRel E') (hU : KUnit ε E) (hU' : KUnit ε E') (hF : LocFin ε E) (hF' : LocFin ε E')
    (hM : IsMin ε E lam) (hM' : IsMin ε E' lam)
    (hS : ∀ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hS' : ∀ S : Submodule ℂ V', (∀ a b, ∀ x ∈ S, E' a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    {v₁ : V} {v₂ : V'} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (k₁ : KHighest ε E (lowK ε lam) v₁)
    (k₂ : KHighest ε E' (lowK ε lam) v₂) :
    ∃ e : V ≃ₗ[ℂ] V', ∀ a b x, e (E a b x) = E' a b (e x) := by
  set v : WithLp 2 (V × V') := pair v₁ v₂ with hv
  have hv0 : v ≠ 0 := fun h => h₁ (show fstL V V' v = 0 by rw [h, map_zero])
  have hvk : KHighest ε (sumE E E') (lowK ε lam) v := kHighest_pair k₁ k₂
  have hone : ∀ w ∈ Cyc (sumE E E') v, KHighest ε (sumE E E') (lowK ε lam) w → ∃ c : ℂ, w = c • v :=
    fun w hw hh => hMultAlg n ε lam _ (sumE E E') hlam (glRel_sumE hE hE') (kUnit_sumE hU hU')
      (locFin_sumE hF hF') (isMin_sumE hM hM') v w hv0 hvk hh hw
  set C := Cyc (sumE E E') v with hC
  have hvC : v ∈ C := mem_cyc.2 ⟨1, by simp⟩
  have hst : ∀ a b, ∀ w ∈ C, sumE E E' a b w ∈ C := fun a b w hw => cyc_stab a b hw

  have hp₁ : C.map (fstL V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => h₁ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₁ ∈ C.map (fstL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  have hp₂ : C.map (sndL V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => h₂ ?_
    · rintro a b _ ⟨w, hw, rfl⟩
      exact ⟨_, hst a b w hw, rfl⟩
    · have : v₂ ∈ C.map (sndL V V') := ⟨v, hvC, rfl⟩
      rwa [h, Submodule.mem_bot] at this

  have hno₁ : pair v₁ (0 : V') ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair k₁ ⟨fun a => by simp, fun a b _ _ => by simp⟩)
    have e₁ : v₁ = c • v₁ := by simpa [fstL, sndL, pair, hv] using congrArg (fstL V V') hc
    have e₂ : (0 : V') = c • v₂ := by simpa [fstL, sndL, pair, hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₂.symm with rfl | h
    · exact h₁ (by simpa using e₁)
    · exact h₂ h
  have hno₂ : pair (0 : V) v₂ ∉ C := by
    intro h
    obtain ⟨c, hc⟩ := hone _ h (kHighest_pair ⟨fun a => by simp, fun a b _ _ => by simp⟩ k₂)
    have e₁ : (0 : V) = c • v₁ := by simpa [fstL, sndL, pair, hv] using congrArg (fstL V V') hc
    have e₂ : v₂ = c • v₂ := by simpa [fstL, sndL, pair, hv] using congrArg (sndL V V') hc
    rcases smul_eq_zero.1 e₁.symm with rfl | h
    · exact h₂ (by simpa using e₂)
    · exact h₁ h
  have hsplit : pair v₁ (0 : V') + pair (0 : V) v₂ = v := ext2 (by simp [fstL, sndL, pair, hv]) (by simp [fstL, sndL, pair, hv])

  let K₁ : Submodule ℂ V :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inl ℂ V V')
  let K₂ : Submodule ℂ V' :=
    C.comap ((WithLp.linearEquiv 2 ℂ (V × V')).symm.toLinearMap ∘ₗ LinearMap.inr ℂ V V')
  have mem₁ : ∀ x, x ∈ K₁ ↔ pair x (0 : V') ∈ C := fun x => Iff.rfl
  have mem₂ : ∀ y, y ∈ K₂ ↔ pair (0 : V) y ∈ C := fun y => Iff.rfl
  have hK₁ : K₁ = ⊥ := by
    refine (hS K₁ fun a b x hx => ?_).resolve_right fun h => hno₂ ?_
    · rw [mem₁] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair x (0 : V')) = pair (E a b x) (0 : V') := ext2 (by simp [fstL, sndL, pair, sumE]) (by simp [fstL, sndL, pair, sumE])
      rwa [e] at this
    · have : pair v₁ (0 : V') ∈ C := (mem₁ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_left] at h'
  have hK₂ : K₂ = ⊥ := by
    refine (hS' K₂ fun a b x hx => ?_).resolve_right fun h => hno₁ ?_
    · rw [mem₂] at hx ⊢
      have := hst a b _ hx
      have e : sumE E E' a b (pair (0 : V) x) = pair (0 : V) (E' a b x) := ext2 (by simp [fstL, sndL, pair, sumE]) (by simp [fstL, sndL, pair, sumE])
      rwa [e] at this
    · have : pair (0 : V) v₂ ∈ C := (mem₂ _).1 (h ▸ Submodule.mem_top)
      have h' := C.sub_mem hvC this
      rwa [← hsplit, add_sub_cancel_right] at h'

  let q₁ : C →ₗ[ℂ] V := (fstL V V').comp C.subtype
  let q₂ : C →ₗ[ℂ] V' := (sndL V V').comp C.subtype
  have b₁ : Function.Bijective q₁ := by
    refine ⟨(injective_iff_map_eq_zero q₁).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : fstL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (0 : V) (sndL V V' w) := ext2 (by simpa [fstL, sndL, pair] using hw') (by simp [fstL, sndL, pair, sumE])
      have : sndL V V' w ∈ K₂ := (mem₂ _).2 (e ▸ w.2)
      rw [hK₂, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp [fstL, sndL, pair, sumE]) (by simp [fstL, sndL, pair, sumE]))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (fstL V V') := hp₁ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  have b₂ : Function.Bijective q₂ := by
    refine ⟨(injective_iff_map_eq_zero q₂).2 fun w hw => ?_, fun x => ?_⟩
    · have hw' : sndL V V' (w : WithLp 2 (V × V')) = 0 := hw
      have e : (w : WithLp 2 (V × V')) = pair (fstL V V' w) (0 : V') := ext2 (by simp [fstL, sndL, pair, sumE]) (by simpa [fstL, sndL, pair] using hw')
      have : fstL V V' w ∈ K₁ := (mem₁ _).2 (e ▸ w.2)
      rw [hK₁, Submodule.mem_bot] at this
      exact Subtype.ext (by rw [e, this]; exact ext2 (by simp [fstL, sndL, pair, sumE]) (by simp [fstL, sndL, pair, sumE]))
    · obtain ⟨w, hw, rfl⟩ : x ∈ C.map (sndL V V') := hp₂ ▸ Submodule.mem_top
      exact ⟨⟨w, hw⟩, rfl⟩
  let f₁ : C ≃ₗ[ℂ] V := LinearEquiv.ofBijective q₁ b₁
  let f₂ : C ≃ₗ[ℂ] V' := LinearEquiv.ofBijective q₂ b₂
  refine ⟨f₁.symm.trans f₂, fun a b x => ?_⟩
  obtain ⟨w, rfl⟩ := f₁.surjective x
  have e : E a b (f₁ w) = f₁ ⟨sumE E E' a b w, hst a b w w.2⟩ := rfl
  rw [e]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem algUniq : CompanionTheory.RgExh.Fin.AlgUniq := by
  intro n ε V V' _ _ _ _ E E' hE hE' s mu hU hU' hF hF' hS hS' hD hD'
  obtain ⟨hP, -, hM, v₁, h₁, k₁⟩ := hD
  obtain ⟨-, -, hM', v₂, h₂, k₂⟩ := hD'
  have gl : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, GlRel F →
      GlRel fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b c d
    simpa only [s.injective.eq_iff] using hF (s a) (s b) (s c) (s d)
  have un : ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      IsUnitary ε F → KUnit (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF a b hab x y
    have hab' : ε (s a) = ε (s b) := hab
    rw [hF (s a) (s b) x y]
    simp [Formalism.REAL.sgn, hab']
  have lf : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W}, LocFin ε F →
      LocFin (ε ∘ s) fun a b => F (s a) (s b) := by
    intro W _ _ F hF x
    obtain ⟨S, hS, hk, hx⟩ := hF x
    exact ⟨S, hS, fun a b hab y hy => hk (s a) (s b) hab y hy, hx⟩
  have si : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] {F : Fin n → Fin n → Module.End ℂ W},
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F a b x ∈ S) → S = ⊥ ∨ S = ⊤) →
      ∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, F (s a) (s b) x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro W _ _ F hF S hst
    refine hF S fun a b x hx => ?_
    simpa using hst (s.symm a) (s.symm b) x hx
  obtain ⟨e, he⟩ := exists_iso_of_highest (ε := ε ∘ s) (lam := mu) (E := fun a b => E (s a) (s b))
    (E' := fun a b => E' (s a) (s b)) hP.1 (gl hE) (gl hE') (un hU) (un hU') (lf hF) (lf hF') hM hM'
    (si hS.2) (si hS'.2) h₁ h₂ k₁ k₂
  refine ⟨e, fun a b x => ?_⟩
  simpa using he (s.symm a) (s.symm b) x

end GlobalTheory.CompanionTheory.LowestDataIso
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
section
open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem charOfAlgDS : CompanionTheory.RgExh.Fin.CharOfAlgDS := by
  intro n ε V _ _ E hE χ s mu hU hLF hSC hDS
  obtain ⟨hHC, -, hMin, v, hv0, hKH⟩ := hDS
  obtain ⟨S, hSfin, hSK, hvS⟩ := hLF v
  have hU' : Formalism.REAL.IsUnitary (ε ∘ s) (fun a b => E (s a) (s b)) := fun a b x y => hU (s a) (s b) x y
  have hSK' : CompanionTheory.D.DSIC.KStab (ε ∘ s) (fun a b => E (s a) (s b)) S :=
    fun a b hab w hw => hSK (s a) (s b) hab w hw
  have hcap : ∀ Y, Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    have h1 := CompanionTheory.D.DSIC.hAlgCore n (ε ∘ s) mu V (fun a b => E (s a) (s b)) v S hHC
      (GlobalTheory.CompanionTheory.HolCoef.CapLW.glRel_perm hE s) hU' hKH hSfin hSK' hvS hMin Y
    rw [GlobalTheory.CompanionTheory.HolCoef.CapLW.qdet_perm hE s] at h1
    have h2 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) = Formalism.QuantumDeterminants.capP χ Y • 1 := hSC Y
    have h3 : Formalism.QuantumDeterminants.capP χ Y • v = Formalism.QuantumDeterminants.capP (fun a => (mu a : ℂ)) Y • v := by
      rw [← h1, h2]
      simp
    exact (smul_left_injective ℂ hv0 h3).symm
  exact exists_perm_of_capelliPolynomial_eq (fun a => (mu a : ℂ)) χ hcap

end GlobalTheory.CompanionTheory.CharOfLowK
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

theorem hasChar_path (hS : StepChar) (ss : List (Fin n)) :
    ∀ (X : GMod n) (χ : Fin n → ℂ), HasChar X χ → HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hS n X χ s h)

theorem hasChar_of_scalChar {X : GMod n} {χ : Fin n → ℂ} (h : ScalChar X χ) : HasChar X χ :=
  ⟨1, fun Y => by rw [pow_one, h Y, sub_self]⟩

theorem capelliPoly_eq_of_perm {χ χ₂ : Fin n → ℂ} (τ τ₂ : Equiv.Perm (Fin n)) (h : ∀ a, χ (τ a) = χ₂ (τ₂ a)) :
    Formalism.QuantumDeterminants.capP χ = Formalism.QuantumDeterminants.capP χ₂ := by
  funext Y
  delta Formalism.QuantumDeterminants.capP
  rw [← Equiv.prod_comp τ (fun s => Y + χ s), ← Equiv.prod_comp τ₂ (fun s => Y + χ₂ s)]
  exact Finset.prod_congr rfl fun a _ => by rw [h a]

def EndOf (ε : Fin n → Bool) (M : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (d : Equiv.Perm (Fin n) × (Fin n → ℝ)) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : GlRel E), IsUnitary ε E ∧ LocFin ε E ∧ IsSimple ⟨V, E, hE⟩ ∧ AlgDS ε ⟨V, E, hE⟩ d.1 d.2 ∧
      Iso (path M χ ss) ⟨V, E, hE⟩

theorem iso_of_ends (hH : Hecke) (hI : IsoFacts) (hU : AlgUniq) {ε : Fin n → Bool} {M M' : GMod n}
    {χ : Fin n → ℂ} {ss : List (Fin n)} {d : Equiv.Perm (Fin n) × (Fin n → ℝ)}
    (hg : GoodPath χ ss) (hM : IsSimple M) (hM' : IsSimple M') (hc : HasChar M χ) (hc' : HasChar M' χ)
    (hs : ScalChar (path M χ ss) (pathEnd χ ss)) (e : EndOf ε M χ ss d) (e' : EndOf ε M' χ ss d) :
    Iso M M' := by
  obtain ⟨V, i1, i2, E, hE, u, l, sm, a, iso⟩ := e
  obtain ⟨V', j1, j2, E', hE', u', l', sm', a', iso'⟩ := e'
  have h := hU n ε V V' E E' hE hE' d.1 d.2 u u' l l' sm sm' a a'
  have h1 := (hI n ε (path M χ ss) ⟨V, E, hE⟩ ⟨V', E', hE'⟩).2.2.1 iso h
  have h2 := (hI n ε (path M' χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.1 iso'
  have h3 := (hI n ε (path M χ ss) ⟨V', E', hE'⟩ (path M' χ ss)).2.2.1 h1 h2
  exact (hH n M χ ss hg hM hc hs).2.2 M' hM' hc' h3

theorem finish : StartMod → PathFin → PathExists → PathEndNat → SimpleDistinct → ScalarCharacterOfL2Embedding → UnitarizableOfL2Embedding →
    IsoFacts → CharOfAlgDS → AlgUniq → DataUniq → DSOfArr → DSOfData → KModOf → ArrCount → Finish := by
  intro hSM hPF hPE hPN hSD hSc hUn hI hCh hU hDU hDA hDD hKM hAC hS hH hDec hFR n ε H _ _ σ hσ
  obtain ⟨hcpl, hnt, hur, hir, hsq⟩ := id hσ
  haveI := hcpl
  obtain ⟨D, E, hK⟩ := hKM n ε H σ hur hir
  obtain ⟨hsim, ⟨χ, hχ⟩, hiw⟩ := hSM n ε H σ hur hir hnt D E hK
  obtain ⟨B, hB⟩ := hDec n
  obtain ⟨C, δ, hδ, hP⟩ := hPE n χ B
  obtain ⟨N₀, hN₀⟩ := hFR n C δ hδ
  obtain ⟨ss, N, hN, hg, hfar, hall, hgap, hbd⟩ := hP N₀
  have key : ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (D' : Submodule ℂ H')
      (E' : Fin n → Fin n → Module.End ℂ D') (hK' : IsKMod ε σ' D' E'), GlobalTheory.Dec.IsSqIntIrr ε σ' →
      IsSimple ⟨D', E', hK'.gl⟩ → ScalChar ⟨D', E', hK'.gl⟩ χ → IntWt ⟨D', E', hK'.gl⟩ →
      SimplePath χ ss ∧ ScalChar (path ⟨D', E', hK'.gl⟩ χ ss) (pathEnd χ ss) ∧
        ∃ d : Equiv.Perm (Fin n) × (Fin n → ℝ), EndOf ε ⟨D', E', hK'.gl⟩ χ ss d ∧
          Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = pathEnd χ ss (τ a) := by
    intro H' _ _ _ σ' D' E' hK' hs' hsm' hsc' hiw'
    obtain ⟨_, _, ur, ir, sq⟩ := id hs'
    have hcX := hasChar_of_scalChar hsc'
    have hL := hB ε H' σ' D' E' hK' χ ss ur ir sq hcX hg hfar
    have hce := hasChar_path hS ss _ χ hcX
    have hse := hSc n ε _ _ hL hce
    obtain ⟨sp, sm, -⟩ := hH n _ χ ss hg hsm' hcX hse
    obtain ⟨V, i1, i2, EV, hEV, hun, iso⟩ := hUn n ε _ hL sm
    have facts := hI n ε (path ⟨D', E', hK'.gl⟩ χ ss) ⟨V, EV, hEV⟩ ⟨V, EV, hEV⟩
    have smV : IsSimple ⟨V, EV, hEV⟩ := (facts.2.2.2.1 iso).1 sm
    have scV : ScalChar ⟨V, EV, hEV⟩ (pathEnd χ ss) := (facts.2.2.2.2.1 iso _).1 hse
    have lfV : LocFin ε EV := (facts.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).1 hK'.locFin)
    have iwV : IntWt ⟨V, EV, hEV⟩ := (facts.2.2.2.2.2.2.2.1 iso).1 ((hPF n ε _ χ ss).2 hiw')
    obtain ⟨s', mu', hAlg⟩ := hN₀ ε V EV hEV (pathEnd χ ss) N smV.1 hun lfV iwV scV hN hgap hbd
    obtain ⟨τ, hτ⟩ := hCh n ε V EV hEV (pathEnd χ ss) s' mu' hun lfV scV hAlg
    exact ⟨sp, hse, (s', mu'), ⟨V, i1, i2, EV, hEV, hun, lfV, smV, hAlg, iso⟩, hAlg.1, hAlg.2.1, τ, hτ⟩
  obtain ⟨sp, hse, d₀, e₀, hc₀, ho₀, τ₀, hτ₀⟩ := key H σ D E hK hσ hsim hχ hiw
  have hend : ∀ a, pathEnd χ ss a = ((d₀.2 (τ₀.symm a) : ℝ) : ℂ) := fun a => by
    rw [hτ₀, Equiv.apply_symm_apply]
  have hinj' : Function.Injective (pathEnd χ ss) := fun a b h => by
    rw [hend, hend] at h
    exact τ₀.symm.injective (hc₀.1.injective (Complex.ofReal_injective h))
  have hr' : ∀ a, (pathEnd χ ss a).im = 0 ∧ ∃ m : ℤ, (pathEnd χ ss a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    rw [hend]
    exact ⟨Complex.ofReal_im _, by simpa using hc₀.2 (τ₀.symm a)⟩
  obtain ⟨m, hm, -⟩ := hPN n χ ss
  have hχa : ∀ a, χ a = pathEnd χ ss a - (m a : ℂ) := fun a => by
    rw [hm]; simp
  have hr : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m := fun a => by
    obtain ⟨h1, k, h2⟩ := hr' a
    refine ⟨by rw [hχa]; simp [h1], k - m a, ?_⟩
    rw [hχa]
    simp only [Complex.sub_re, Complex.natCast_re]
    push_cast
    linarith
  have hinj := hSD n χ ss sp hall
  obtain ⟨A, A', hcard, hA, hA'⟩ := hAC n ε χ (pathEnd χ ss) hinj hinj' hr hr'
  have per : ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), ∃ (M : GMod n) (e : Equiv.Perm (Fin n) × (Fin n → ℝ)),
      d ∈ A → e ∈ A' ∧ IsSimple M ∧ HasChar M χ ∧ ScalChar (path M χ ss) (pathEnd χ ss) ∧
        EndOf ε M χ ss e ∧ AlgDS ε M d.1 d.2 ∧ ConeDS ε M d.1 d.2 := by
    intro d
    by_cases hd : d ∈ A
    · obtain ⟨hhc, hord, τ, hτ⟩ := (hA d).1 hd
      obtain ⟨H', i1, i2, i3, σ', hsi, hall'⟩ := hDA n ε d.1 d.2 hhc hord
      obtain ⟨_, hnt', ur', ir', _⟩ := id hsi
      obtain ⟨D', E', hK'⟩ := hKM n ε H' σ' ur' ir'
      obtain ⟨s1, ⟨χd, hχd⟩, iw⟩ := hSM n ε H' σ' ur' ir' hnt' D' E' hK'
      obtain ⟨hAlg, hCone⟩ := hall' D' E' hK'
      obtain ⟨τ', hτ'⟩ := hCh n ε D' E' hK'.gl χd d.1 d.2 hK'.unit hK'.locFin hχd hAlg
      have hcap : Formalism.QuantumDeterminants.capP χd = Formalism.QuantumDeterminants.capP χ :=
        capelliPoly_eq_of_perm τ' τ fun a => by rw [← hτ', ← hτ]
      have hsc : ScalChar ⟨D', E', hK'.gl⟩ χ := fun Y => by rw [hχd Y, hcap]
      obtain ⟨-, hse', e, he, hce, hoe, τe, hτe⟩ := key H' σ' D' E' hK' hsi s1 hsc iw
      exact ⟨⟨D', E', hK'.gl⟩, e, fun _ => ⟨(hA' e).2 ⟨hce, hoe, τe, hτe⟩, s1, hasChar_of_scalChar hsc, hse', he,
        hAlg, hCone⟩⟩
    · exact ⟨triv n, d, fun h => absurd h hd⟩
  haveI : Nonempty (GMod n) := ⟨triv n⟩
  choose! M e hMe using per
  have hmaps : Set.MapsTo e (A : Set _) (A' : Set _) := fun d hd => (hMe d hd).1
  have hinjA : Set.InjOn e (A : Set _) := by
    intro d₁ h₁ d₂ h₂ heq
    obtain ⟨-, s1, c1, p1, n1, a1, k1⟩ := hMe d₁ h₁
    obtain ⟨-, s2, c2, p2, n2, a2, k2⟩ := hMe d₂ h₂
    rw [← heq] at n2
    have hiso := iso_of_ends hH hI hU hg s1 s2 c1 c2 p1 n1 n2
    have a2' : AlgDS ε (M d₁) d₂.1 d₂.2 :=
      ((hI n ε (M d₁) (M d₂) (M d₁)).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
    obtain ⟨q1, q2⟩ := hDU n ε (M d₁) _ _ _ _ a1 k1 a2'
    exact Prod.ext q1 q2
  have hsurj := Finset.surjOn_of_injOn_of_card_le e hmaps hinjA hcard.symm.le
  obtain ⟨d, hd, hde⟩ := hsurj ((hA' d₀).2 ⟨hc₀, ho₀, τ₀, hτ₀⟩)
  obtain ⟨-, s2, c2, p2, n2, a2, -⟩ := hMe d hd
  rw [hde] at n2
  have hiso := iso_of_ends hH hI hU hg hsim s2 (hasChar_of_scalChar hχ) c2 hse e₀ n2
  have aX : AlgDS ε ⟨D, E, hK.gl⟩ d.1 d.2 :=
    ((hI n ε ⟨D, E, hK.gl⟩ (M d) ⟨D, E, hK.gl⟩).2.2.2.2.2.2.2.2.1 hiso _ _).2 a2
  obtain ⟨hhc, hord, -⟩ := (hA d).1 hd
  exact ⟨d.1, d.2, hhc, hord, hDD n ε H σ D E hK d.1 d.2 hσ aX⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.DSData

open Formalism.REAL (KHighest)
open CompanionTheory.RgExh CompanionTheory.RgExh.Fin

variable {n : ℕ}

theorem kHighest_of_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x) :
    KHighest ε E (μ ∘ s.symm) x := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · simpa using h.1 (s.symm a)
  · have h1 : (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) := by simpa using he
    simpa using h.2 (s.symm a) (s.symm b) (GlobalTheory.DSId.PermK.mono_symm hs a b hab h1) h1

theorem kHighest_perm {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {E : Fin n → Fin n → Module.End ℂ V}
    {μ : Fin n → ℝ} {x : V} (h : KHighest ε E (μ ∘ s.symm) x) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) μ x := by
  refine ⟨fun a => ?_, fun a b hab he => h.2 _ _ (hs a b hab he) he⟩
  simpa using h.1 (s a)

theorem dsOfData : DSOfData := by
  intro n ε H _ _ σ D E hK s mu hSq hA
  obtain ⟨-, hord, hmin, v, hv0, hv⟩ := hA
  obtain ⟨hT, -, -, hS, -⟩ := GlobalTheory.DSId.PermK.permKType n ε s H σ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.1 hSq
  have e : ∀ f : Fin n → ℝ, (f ∘ s.symm) ∘ s = f := fun f => by funext a; simp
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
  · obtain ⟨T, hT'⟩ := hK.ty _ v hv0 (kHighest_of_perm hord hv)
    refine ⟨T, ?_⟩
    have h6 := (hT _ T).1 hT'
    rwa [e] at h6
  · intro μ S hS'
    have h6 : Formalism.MainNotions.S.IsKTypeOf ε σ (μ ∘ s.symm) S := by
      refine (hT _ S).2 ?_
      rwa [e]
    obtain ⟨w, hw0, -, hw⟩ := hK.hw _ S h6
    exact hmin μ w hw0 (kHighest_perm hord hw)

end GlobalTheory.CompanionTheory.DSData
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
section
namespace GlobalTheory.CompanionTheory.KModOfStep

theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
end

