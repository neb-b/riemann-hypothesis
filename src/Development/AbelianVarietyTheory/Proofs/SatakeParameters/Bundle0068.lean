module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalRingCardinality.DataJet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
section
open MeasureTheory

namespace GlobalTheory

section
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}


omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_image_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
  refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
  · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
  · intro γ h
    simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  rw [h𝓕.setIntegral_eq (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)]
  exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
    (measurableEmbedding_mulRight y) u 𝓕).symm

theorem integrableOn_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  rw [h𝓕.integrableOn_iff (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)] at hi
  exact ((measurePreserving_mul_right μ y).integrableOn_image
    (measurableEmbedding_mulRight y)).1 hi

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumps
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := _root_.GlobalTheory.HTW.Rec.jump_multV_ne_zero P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := _root_.GlobalTheory.HTW.Rec.recWord_jumps L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := _root_.GlobalTheory.HTW.Rec.existsUnique_over P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (_root_.GlobalTheory.HTW.Rec.recWord_jumps L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearMapExtOfISupEqTop
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.EigTransfer

theorem linearMap_ext_of_iSup_eq_top {E F C : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (Ec : C → Submodule ℂ E) (htop : (⨆ c, Ec c) = ⊤) (f g : E →ₗ[ℂ] F)
    (h : ∀ c, ∀ w ∈ Ec c, f w = g w) : f = g := by
  have hle : (⊤ : Submodule ℂ E) ≤ LinearMap.eqLocus f g := by
    rw [← htop]
    exact iSup_le fun c w hw => LinearMap.mem_eqLocus.2 (h c w hw)
  ext e
  exact LinearMap.mem_eqLocus.1 (hle Submodule.mem_top)

end GlobalTheory.EigTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPowStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n),
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  g ∈ Formalism.L2.Col.GLint E n P ∧ ∀ w ∈ Formalism.L2.Col.stdAt E n P, ((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ • (g w - w) ∈ Formalism.L2.Col.stdAt E n P := by
  first | exact @GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | exact GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | (intros; apply GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
section
noncomputable section

namespace GlobalTheory.BiextInhab

open MvPowerSeries Formalism.FG.SolveVAux

def laK (K : Type) [Field K] (l d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : K) ^ e)⁻¹ else 0

section Field

variable {K : Type} [Field K] {l d : ℕ}

open MvPowerSeries in
variable {K : Type} [Field K] {l d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.laK_idMod2 (hl : l.Prime) :
    _root_.Formalism.FG.IsIdMod2 (_root_.GlobalTheory.BiextInhab.laK K l d) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · show _root_.GlobalTheory.BiextInhab.laK K l d j 0 = 0
    unfold _root_.GlobalTheory.BiextInhab.laK
    refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
    exact pow_ne_zero _ hl.ne_zero (Finsupp.single_eq_zero.mp h.symm)
  · show _root_.GlobalTheory.BiextInhab.laK K l d j (Finsupp.single i 1) = _
    unfold _root_.GlobalTheory.BiextInhab.laK
    rw [Finset.sum_eq_single 0]
    · simp [Finsupp.single_left_inj one_ne_zero]
    · intro e _ he
      refine if_neg fun h => he ?_
      have h1 := congrArg (fun f : ZMod d →₀ ℕ => f.sum fun _ k => k) h
      simp only [Finsupp.sum_single_index] at h1
      rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
      · exact absurd h2 hl.ne_one
      · omega
    · intro h
      simp at h

variable [NeZero d]

end Field

section Padic

open Formalism.G

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} {τ : Type}

variable [NeZero d]

end Padic

section Main

open GlobalTheory.ThStr Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

def serW (l : ℕ) [Fact l.Prime] (κ : Type) : Subring (MvPowerSeries κ ℂ_[l]) :=
  (MvPowerSeries.map (σ := κ) (Wp l).subtype).range

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.mem_serW {κ : Type} {F : MvPowerSeries κ ℂ_[l]} :
    F ∈ _root_.GlobalTheory.BiextInhab.serW l κ ↔ _root_.Formalism.MainNotions.GL3Theta.IntegralW F := by
  constructor
  · rintro ⟨G, rfl⟩ n
    exact (coeff n G).2
  · intro h
    exact ⟨fun n => ⟨coeff n F, h n⟩, by ext n; rfl⟩

variable [NeZero d]




open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
private theorem coeff_mapDomain_rename_of_injective {σ τ R : Type} [CommSemiring R] (f : σ → τ)
    [Filter.TendstoCofinite f] (hf : Function.Injective f) (p : MvPowerSeries σ R)
    (n : σ →₀ ℕ) : coeff (Finsupp.mapDomain f n) (rename f p) = coeff n p := by
  rw [coeff_rename, Finset.sum_eq_single n]
  · intro y hy hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact absurd (Finsupp.mapDomain_injective hf hy) hne
  · intro hn
    exact absurd (by simp) hn


open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
theorem _root_.GlobalTheory.BiextInhab.bridge (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]
    {β : Type} (b : β) (s : ZMod d) :
    _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) := by
  have hinj : Function.Injective (fun r : ZMod d => (r, b)) := fun x y h => (Prod.mk.inj h).1
  have hren : _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      rename (fun r : ZMod d => (r, b)) (_root_.GlobalTheory.ThStr.laS l d s) := by
    rw [rename_eq_subst]
    rfl
  have hsingle : ∀ e : ℕ, (Finsupp.single (s - 2 * (e : ZMod d), b) ((l ^ 2) ^ e) :
      ZMod d × β →₀ ℕ) = Finsupp.mapDomain (fun r : ZMod d => (r, b))
        (Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) := by
    intro e
    rw [Finsupp.mapDomain_single, pow_mul]
    push_cast
    rfl
  rw [hren]
  ext m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (fun r : ZMod d => (r, b)))
  · obtain ⟨n, rfl⟩ := hm
    have hdeg : _root_.Formalism.BasicNotions.JetTdeg (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n) =
        n.sum fun _ k => k := by
      unfold _root_.Formalism.BasicNotions.JetTdeg
      exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [coeff_mapDomain_rename_of_injective _ hinj]
    show _root_.GlobalTheory.ThStr.laS l d s n =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n)
    unfold _root_.GlobalTheory.ThStr.laS _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hsingle e, (Finsupp.mapDomain_injective hinj).eq_iff]
  · rw [coeff_rename_eq_zero _ _ hm]
    show (0 : ℂ_[l]) = _root_.Formalism.BasicNotions.jetLogG l d (s, b) m
    unfold _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    exact hm ⟨_, (hsingle e).symm⟩

end Main

end GlobalTheory.BiextInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

namespace NormalFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem adjoint_apply_eq_zero {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) {v : E}
    (hv : S v = 0) : LinearMap.adjoint S v = 0 := by
  have e : S (LinearMap.adjoint S v) = LinearMap.adjoint S (S v) := LinearMap.congr_fun h.eq v
  rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, e, hv, map_zero, inner_zero_left]

theorem apply_eq_zero_of_pow {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) (k : ℕ) {v : E}
    (hv : (S ^ k) v = 0) : S v = 0 := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    rw [this, map_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hv
    have h1 := adjoint_apply_eq_zero h (ih hv)
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← LinearMap.adjoint_inner_left, h1, inner_zero_left]

theorem adjoint_sub_smul (T : Module.End ℂ E) (a : ℂ) :
    LinearMap.adjoint (T - a • (1 : Module.End ℂ E)) =
      LinearMap.adjoint T - (starRingEnd ℂ a) • (1 : Module.End ℂ E) := by
  rw [map_sub, LinearEquiv.map_smulₛₗ]
  congr 2
  exact star_one (Module.End ℂ E)

theorem commute_sub_smul {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    Commute (T - a • (1 : Module.End ℂ E)) (LinearMap.adjoint (T - a • (1 : Module.End ℂ E))) := by
  rw [adjoint_sub_smul]
  exact (h.sub_right ((Commute.one_right T).smul_right _)).sub_left ((Commute.one_left _).smul_left a)

theorem maxGenEigenspace_eq {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    T.maxGenEigenspace a = T.eigenspace a := by
  ext v
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨k, hk⟩
    have := apply_eq_zero_of_pow (commute_sub_smul h a) k hk
    simpa [sub_eq_zero] using this
  · intro hv
    exact ⟨1, by simp [hv]⟩

theorem eigenspace_isOrtho {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) {a b : ℂ}
    (hab : a ≠ b) : T.eigenspace a ⟂ T.eigenspace b := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  rw [Module.End.mem_eigenspace_iff] at hv hw
  have h0 : (T - a • (1 : Module.End ℂ E)) v = 0 := by simp [hv]
  have h1 := adjoint_apply_eq_zero (commute_sub_smul h a) h0
  have h2 : inner ℂ v ((T - a • (1 : Module.End ℂ E)) w) = 0 := by
    rw [← LinearMap.adjoint_inner_left, h1, inner_zero_left]
  have h3 : (T - a • (1 : Module.End ℂ E)) w = (b - a) • w := by simp [hw, sub_smul]
  rw [h3, inner_smul_right, mul_eq_zero] at h2
  exact h2.resolve_left (sub_ne_zero.2 hab.symm)

end NormalFamily

theorem normalFamily_orthogonal_decomposition :
    ∀ {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (op : I → Module.End ℂ E), PairComm op → (∀ i, ∃ i', op i' = LinearMap.adjoint (op i)) → (∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i)) ∧ (⨆ x, eigAt op x) = ⊤ ∧ ∀ x x', x ≠ x' → eigAt op x ⟂ eigAt op x' := by
  intro E I _ _ _ op hc hadj
  have hn : ∀ i, Commute (op i) (LinearMap.adjoint (op i)) := fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    rw [← hi']
    exact hc i i'
  have h1 : ∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i) := fun x =>
    iInf_congr fun i => NormalFamily.maxGenEigenspace_eq (hn i) (x i)
  refine ⟨h1, iSup_eigAt_eq_top hc fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i), ?_⟩
  intro x x' hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  rw [h1, h1]
  exact (NormalFamily.eigenspace_isOrtho (hn i) hi).mono (iInf_le _ i) (iInf_le _ i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrime
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := _root_.GlobalTheory.HTW.Rec.jA_eq_depth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := _root_.GlobalTheory.depth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (_root_.GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XLeA
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShXa

theorem X''_le_a : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨-, -, -, -, -, h4, -, -, hw, -⟩ := h x hx hx1 i
  have ha : 0 ≤ (Fm.L x i).sc.a := by
    have h0 : 0 ≤ (Fm.L x i).sc.x := by linarith
    unfold Scale.a Scale.b
    positivity
  rw [Scale.X'']
  exact div_le_self ha hw

end GlobalTheory.ShXa
end

