module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0391
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponent
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticeMeanCountBound
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMean

theorem orbSum_encard_le (G A B : Type) [Group G] [MulAction G A] [MulAction G B] (Y : Set A) (P : A → Set B)
    (hP : ∀ (g : G) a b, g • b ∈ P (g • a) ↔ b ∈ P a) (hY : Stable G Y)
    (hfin : ∀ y ∈ Y, Finite (MulAction.stabilizer G y)) (s : Finset B)
    (hs : ∀ a ∈ Y, ∀ b ∈ P a, ∃ b₀ ∈ s, ∃ g : G, g • b₀ = b) :
    orbSum G Y (fun a => (((P a).encard : ℕ∞) : ℝ≥0∞)) ≤
      ∑ b₀ ∈ s, orbMass (MulAction.stabilizer G b₀) {a | a ∈ Y ∧ b₀ ∈ P a} := by
  set X : Set (A × B) := {p | p.1 ∈ Y ∧ p.2 ∈ P p.1} with hX
  have hXs : Stable G X := fun g p hp => ⟨hY g _ hp.1, (hP g _ _).2 hp.2⟩
  have h1 := GlobalTheory.Mass.orbMass_eq_orbSum_fibre G (A × B) A X Y Prod.fst (fun _ _ => rfl) hXs hY
    (fun p hp => hp.1) hfin
  have h2 : orbSum G Y (fun a => (((P a).encard : ℕ∞) : ℝ≥0∞)) ≤ orbMass G X := by
    rw [h1]
    refine (_root_.GlobalTheory.Mass.OrbMono.main G A).1 Y Y _ _ subset_rfl fun a ha => ?_
    have : (P a).encard ≤ (X ∩ Prod.fst ⁻¹' {a}).encard :=
      Set.encard_le_encard_of_injOn (f := fun b => (a, b)) (fun b hb => ⟨⟨ha, hb⟩, rfl⟩)
        (fun b _ b' _ e => (Prod.ext_iff.1 e).2)
    exact_mod_cast this
  refine h2.trans ?_
  have h3 := (_root_.GlobalTheory.Mass.OrbMono.main G (A × B)).2.2.1 B s X (fun b₀ => {p | p ∈ X ∧ ∃ g : G, g • b₀ = p.2})
    (fun _ => 1) (by
      intro p hp
      obtain ⟨b₀, hb₀, g, hg⟩ := hs _ hp.1 _ hp.2
      simp only [Set.mem_iUnion]
      exact ⟨b₀, hb₀, hp, g, hg⟩)
  refine h3.trans (Finset.sum_le_sum fun b₀ _ => le_of_eq ?_)
  have hS : Stable (MulAction.stabilizer G b₀) {p : A × B | p ∈ X ∧ p.2 = b₀} := by
    rintro g p ⟨hp, e⟩
    refine ⟨hXs g p hp, ?_⟩
    change (g : G) • p.2 = b₀
    rw [e]
    exact g.2
  have h4 := _root_.GlobalTheory.Mass.Slice.orbSum_restrict G (A × B) (MulAction.stabilizer G b₀)
    {p | p ∈ X ∧ ∃ g : G, g • b₀ = p.2} {p | p ∈ X ∧ p.2 = b₀} (fun _ => 1)
    (fun p hp => ⟨hp.1, 1, by rw [one_smul, hp.2]⟩)
    (by
      rintro g p ⟨hp, g', e⟩
      refine ⟨hXs g p hp, g * g', ?_⟩
      rw [mul_smul, e]
      rfl)
    hS (fun _ _ => rfl)
    (by
      rintro p ⟨hp, g, e⟩
      refine ⟨g⁻¹, hXs _ p hp, ?_⟩
      change g⁻¹ • p.2 = b₀
      rw [← e, inv_smul_smul])
    (by
      rintro g p ⟨_, e⟩ ⟨_, e'⟩
      change g • p.2 = b₀ at e'
      rw [e] at e'
      exact e')
  rw [← h4]
  exact _root_.GlobalTheory.Mass.OrbTransport.main (MulAction.stabilizer G b₀) (MulAction.stabilizer G b₀) (A × B) A (MulEquiv.refl _)
    Prod.fst {p | p ∈ X ∧ p.2 = b₀} {a | a ∈ Y ∧ b₀ ∈ P a} (fun _ => 1) hS
    (by
      rintro g a ⟨ha, hb⟩
      refine ⟨hY g a ha, ?_⟩
      have := (hP g a b₀).2 hb
      rw [g.2] at this
      exact this)
    ⟨fun p hp => ⟨hp.1.1, hp.2 ▸ hp.1.2⟩,
      fun p hp q hq e => Prod.ext e (hp.2.trans hq.2.symm),
      fun a ha => ⟨(a, b₀), ⟨ha, rfl⟩, rfl⟩⟩
    (fun _ _ _ => rfl) (fun _ _ => rfl)

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · positivity
  · exact le_rfl

theorem isIntLat_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : IsIntLat h L)
    (U : Submodule K V) : IsIntLat (hRes h U) (latIn U L) := by
  letI : Submodule.IsLattice K (latIn U L) := by
    refine ⟨?_, ?_⟩
    · apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype
      exact hL.1.fg.of_le (Submodule.map_comap_le _ _)
    · intro s hs hli
      letI : Submodule.IsLattice K L := hL.1.toIsLattice
      apply LinearIndependent.of_comp U.subtype
      apply Submodule.IsLattice.linearIndependent K L
      · intro x
        exact hs x.2
      · exact hli.map' (U.subtype.restrictScalars (𝓞 K))
          (LinearMap.ker_eq_bot.mpr U.injective_subtype)
  refine ⟨{ span_eq_top := ?_ }, fun x hx y hy => hL.2 x hx y hy⟩
  · letI : Submodule.IsFullLattice K L := hL.1
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, hax⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K L (x : V)
      (show (x : V) ∈ Submodule.span K (L : Set V) by rw [Submodule.IsFullLattice.span_eq_top]; trivial)
    rw [Submodule.span_eq] at hax
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using nonZeroDivisors.coe_ne_zero a
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax


end

theorem exponents (n X j s l c : ℝ) (m : ℕ) (hm : (m : ℝ) = s) (hn : 1 ≤ n) (hX : n ≤ X) (hl : 0 ≤ l)
    (hc : c ≤ n ^ (1 + l)) :
    c * (n ^ ((j + l) / 2) * (X * X ^ ((s + l) / 2)) * (n * X) ^ (2 * m + 1)) ≤
      n ^ (j / 2) * X ^ ((9 * s + 8 + 4 * l) / 2) := by
  have n0 : 0 < n := by linarith
  have X0 : 0 < X := by linarith
  have e1 : n ^ ((j + l) / 2) = n ^ (j / 2) * n ^ (l / 2) := by
    rw [← Real.rpow_add n0]; congr 1; ring
  have b1 : c ≤ X ^ (1 + l) := hc.trans (Real.rpow_le_rpow n0.le hX (by linarith))
  have b2 : n ^ (l / 2) ≤ X ^ (l / 2) := Real.rpow_le_rpow n0.le hX (by linarith)
  have b3 : (n * X) ^ (2 * m + 1) ≤ X ^ (4 * s + 2) := by
    have : (n * X) ^ (2 * m + 1) ≤ (X * X) ^ (2 * m + 1) := by gcongr
    refine this.trans (le_of_eq ?_)
    rw [← hm, ← sq, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e2 : X ^ ((9 * s + 8 + 4 * l) / 2) =
      X ^ (1 + l) * (X ^ (l / 2) * (X * X ^ ((s + l) / 2)) * X ^ (4 * s + 2)) := by
    have : X * X ^ ((s + l) / 2) = X ^ (1 + (s + l) / 2) := by rw [Real.rpow_add X0, Real.rpow_one]
    rw [this, ← Real.rpow_add X0, ← Real.rpow_add X0, ← Real.rpow_add X0]
    congr 1
    ring
  rw [e1, e2]
  calc c * (n ^ (j / 2) * n ^ (l / 2) * (X * X ^ ((s + l) / 2)) * (n * X) ^ (2 * m + 1))
      ≤ X ^ (1 + l) * (n ^ (j / 2) * X ^ (l / 2) * (X * X ^ ((s + l) / 2)) * X ^ (4 * s + 2)) := by
        gcongr
    _ = _ := by ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (j s : ℕ), 1 ≤ j → 1 ≤ s → j + s = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ s → ∀ (n N₀ : ℕ), 1 ≤ n → 1 ≤ N₀ → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j n).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (n : ℝ) ^ ((j : ℝ) / 2) * ((n : ℝ) * N₀) ^ ((9 * (s : ℝ) + 8 + 4 * Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j s hj hs1 hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    n N₀ hn hN 𝒢 hst h𝒢
  obtain ⟨S, hcard, hdim, hcov⟩ := GlobalTheory.T.few_orbits_subspaces_hermitian_lattice_discriminant K V h hK hs hp hLand j n hn
  have hnd : h.Nondegenerate := by
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · by_contra hne
      have := hp τ x hne
      simp [hx x] at this
    · by_contra hne
      have := hp τ x hne
      simp [hx x] at this
  set l : ℝ := Real.logb 2 (Module.finrank ℚ K) with hl
  have l0 : 0 ≤ l := Real.logb_nonneg one_lt_two (by exact_mod_cast Module.finrank_pos)
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢 (fun L => primSp h L j n)
    (fun g L U => (_root_.GlobalTheory.Mass.PrimMove.main K V h hK hs hnd g L U j n).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  set X : ℝ := (n : ℝ) * N₀ with hX
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have N1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN
  have hnX : (n : ℝ) ≤ X := le_mul_of_one_le_right (by positivity) N1
  have X0 : 0 ≤ X := by positivity
  set C : ℝ := (mass h₁ I₁ * (n : ℝ) ^ (((j : ℝ) + l) / 2)) * (X * (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) *
    ((n : ℝ) * X) ^ (2 * s + 1) with hC
  have C0 : 0 ≤ C := by positivity
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j n} ≤
      ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, sU, pU, -⟩ := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp).2 U
    obtain ⟨-, sW, pW, -⟩ := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp).2 (perp h U)
    have dW : Module.finrank K (perp h U) = s := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (_root_.GlobalTheory.Mass.OrbMono.main (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j n}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2, hL.2.2⟩) (fun _ _ => le_rfl)
    refine a1.trans ((GlobalTheory.T.orbitStabilizerMass_subspace_cyclicDiscriminant_le K V h hK hs hp U n N₀).trans ?_)
    have a2 := GlobalTheory.T.mass_integralLattices_discriminantOrder_le hM K U (hRes h U) hK sU pU (dU ▸ hj) V₁ h₁ hs₁ I₁ (dU ▸ hI₁) n hn
    rw [dU] at a2
    have a3 : ∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') ≤
        ENNReal.ofReal (X * (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) := by
      refine (Finset.sum_le_card_nsmul _ _
        (ENNReal.ofReal (mass h₂ I₂ * X ^ (((s : ℝ) + l) / 2))) fun n' hn' => ?_).trans (le_of_eq ?_)
      · obtain ⟨b1, b2⟩ := Finset.mem_Icc.1 hn'
        have a := GlobalTheory.T.mass_integralLattices_discriminantOrder_le hM K (perp h U) (hRes h (perp h U)) hK sW pW (dW ▸ hs1) V₂ h₂ hs₂ I₂
          (dW ▸ hI₂) n' b1
        rw [dW] at a
        refine a.trans (ENNReal.ofReal_le_ofReal ?_)
        have b3 : (n' : ℝ) ≤ X := by rw [hX]; exact_mod_cast b2
        gcongr
      · rw [ENNReal.ofReal_mul X0, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, hX,
          ← Nat.cast_mul, ENNReal.ofReal_natCast]
    rw [hC, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), dW]
    refine mul_le_mul' (mul_le_mul' a2 a3) (le_of_eq ?_)
    rw [← ENNReal.ofReal_natCast, hX]
    push_cast
    rfl
  refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have key := exponents n X j s l S.card s rfl n1 hnX l0 hcard
  have := mul_le_mul_of_nonneg_left key (mul_nonneg m1 m2)
  calc (S.card : ℝ) * C = mass h₁ I₁ * mass h₂ I₂ * ((S.card : ℝ) * ((n : ℝ) ^ (((j : ℝ) + l) / 2) *
        (X * X ^ (((s : ℝ) + l) / 2)) * ((n : ℝ) * X) ^ (2 * s + 1))) := by rw [hC]; ring
    _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.Mass.PrimMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
section
noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopVol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem root_fst_lt (w : Point D.host.E (D.R.rS + 1)) (q : GlobalTheory.LoopV.roots (ptMat w)) : q.1.1.1 < D.R.rS := by
  have hq := q.2
  simp only [GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
  have h := hq.2.1
  have h2 := q.1.2.2
  rw [Fin.lt_def] at h
  omega

def ratCoord (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s y : X.B.I.Ginf) : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ :=
  fun τ q => Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε (X.pl.symm τ))
    (Formalism.L2.SG.HidaSetting.rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
    (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ)) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) q.1.2)

theorem ratCoord_cont (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s : X.B.I.Ginf) : Continuous (ratCoord X u' w γ s) := by
  unfold ratCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun τ => continuous_pi fun q => ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply _).comp
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)))

end GlobalTheory.LoopVol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsMeanBoundOfGenusMean
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.HermitianLatticesTheory GlobalTheory.Mass

namespace GlobalTheory.RowsMean

section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sameGenus_trans (h : V →ₗ⋆[K] V →ₗ[K] K) {L M N : Submodule (𝓞 K) V}
    (h1 : SameGenus h L M) (h2 : SameGenus h M N) : SameGenus h L N := by
  intro p hp
  obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
  obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  rw [genusBasic_gmap_mul, e₁, e₂]

theorem sameGenus_refl (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : SameGenus h L L :=
  fun _ _ => ⟨1, one_mem _, genusBasic_gmap_one _⟩

theorem genus_eq_iff (h : V →ₗ⋆[K] V →ₗ[K] K) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hM : Submodule.IsFullLattice K M) :
    genus h L = genus h M ↔ L ∈ genus h M := by
  constructor
  · intro e; rw [← e]; exact ⟨hL, sameGenus_refl h L⟩
  · intro hLM
    ext N
    constructor
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h hLM.2 hs⟩
    · rintro ⟨hN, hs⟩
      exact ⟨hN, sameGenus_trans h (genusBasic_symm h _ _ hLM.2) hs⟩

theorem mass_nonneg (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : 0 ≤ mass h L := by
  unfold mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean
section General
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inv_card_eq (X : Type) [Nonempty X] :
    ((ENat.card X : ℕ∞) : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((Nat.card X : ℝ))⁻¹ := by
  rcases finite_or_infinite X with hX | hX
  · rw [ENat.card_eq_coe_natCard]
    have hp : 0 < Nat.card X := Nat.card_pos
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hp), ENNReal.ofReal_natCast]
    simp
  · rw [ENat.card_eq_top_of_infinite, Nat.card_eq_zero_of_infinite]
    simp

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isom h) M ≃ Formalism.ThetaLiftIndependence.autL h M where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  left_inv g := rfl
  right_inv a := rfl

theorem mass_le_orbMass (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) :
    ENNReal.ofReal (mass h L) ≤ orbMass (isom h) (genus h L) := by
  unfold mass
  split_ifs with hs
  swap
  · simp
  have hs' : Formalism.ThetaLiftIndependence.IsClassReps h L hs.choose := hs.choose_spec
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  have hrel : ∀ M : Submodule (𝓞 K) V, MulAction.orbitRel (isom h) (Submodule (𝓞 K) V)
      (Quotient.out (Quotient.mk'' M : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V))) M :=
    fun M => Quotient.exact' (Quotient.out_eq' _)
  have hq : ∀ M ∈ hs.choose, Quotient.out (Quotient.mk'' M :
      MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) ∈ genus h L := by
    intro M hM
    obtain ⟨g, hg⟩ := hrel M
    rw [← hg]
    exact GlobalTheory.Mass.Transp.genus_stable L g M (hs'.1 M hM)
  let qm : hs.choose → {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) //
      Quotient.out q ∈ genus h L} := fun M => ⟨Quotient.mk'' M.1, hq M.1 M.2⟩
  have hinj : Function.Injective qm := by
    rintro ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ e
    have e' : (Quotient.mk'' M₁ : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V)) =
        Quotient.mk'' M₂ := congrArg Subtype.val e
    obtain ⟨g, hg⟩ := Quotient.exact' e'
    have hM₁ : M₁ ∈ genus h L := hs'.1 M₁ h₁
    have u := (hs'.2 M₁ hM₁).unique ⟨h₁, 1, one_mem _, genusBasic_gmap_one _⟩ ⟨h₂, g.1, g.2, hg⟩
    exact Subtype.ext u
  unfold orbMass orbSum
  rw [← Finset.sum_attach]
  have hterm : ∀ M : hs.choose, ENNReal.ofReal (((Nat.card (Formalism.ThetaLiftIndependence.autL h M.1) : ℕ) : ℝ))⁻¹ =
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := by
    intro M
    rw [mul_one]
    have e1 : ENat.card (MulAction.stabilizer (isom h) (Quotient.out (qm M).1)) =
        ENat.card (Formalism.ThetaLiftIndependence.autL h M.1) :=
      ENat.card_congr (((MulAction.stabilizerEquivStabilizerOfOrbitRel (hrel M.1)).toEquiv).trans
        (stabEquiv h M.1))
    haveI : Nonempty (Formalism.ThetaLiftIndependence.autL h M.1) := ⟨stabEquiv h M.1 1⟩
    rw [e1, inv_card_eq]
  simp_rw [hterm]
  exact (Finset.sum_image (s := hs.choose.attach) (g := qm)
    (f := fun q : {q : MulAction.orbitRel.Quotient (isom h) (Submodule (𝓞 K) V) // Quotient.out q ∈ genus h L} =>
      ((ENat.card (MulAction.stabilizer (isom h) (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
    (fun a _ b _ e => hinj e)).symm.le.trans (ENNReal.sum_le_tsum _)

end General
end GlobalTheory.RowsMean

namespace GlobalTheory.RowsMean

theorem sum_le_of_classes {ι α : Type} (s : Finset ι) (L : ι → α) (G : α → Set α) (P : α → Prop)
    (hP : ∀ i ∈ s, P (L i)) (hG : ∀ a b, P a → P b → (G a = G b ↔ a ∈ G b))
    (F w : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hcl : ∀ i₀ ∈ s, ∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), F i ≤
      (∑ i ∈ s.filter (fun i => L i ∈ G (L i₀)), w i) * b) :
    ∑ i ∈ s, F i ≤ (∑ i ∈ s, w i) * b := by
  have hmap : ∀ i ∈ s, G (L i) ∈ s.image (fun i => G (L i)) := fun i hi => Finset.mem_image_of_mem _ hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap F, ← Finset.sum_fiberwise_of_maps_to hmap w, Finset.sum_mul]
  refine Finset.sum_le_sum fun y hy => ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hy
  have e : s.filter (fun i => G (L i) = G (L i₀)) = s.filter (fun i => L i ∈ G (L i₀)) :=
    Finset.filter_congr fun i hi => hG _ _ (hP i hi) (hP i₀ hi₀)
  rw [e]
  exact hcl i₀ hi₀

end GlobalTheory.RowsMean

namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsMean : RowsMeanC := by
  intro D large₂ X Y u hStd W HW hEmb φ B hB hφ hbd
  have hOrb := _root_.GlobalTheory.RowsOrb.rowsOrbC D large₂ X Y u hStd W HW hEmb
  have hLat := _root_.GlobalTheory.TypeAsm.lat0C D large₂ X Y u hStd W HW hEmb
  have hw : ∀ Λ, 0 ≤ wRow D (X.Fu u) Λ := fun Λ => by unfold wRow; positivity
  have hm : 0 ≤ massRows D (X.Fu u) (Y.what₂ u) := Finset.sum_nonneg fun Λ _ => hw Λ
  rw [ENNReal.ofReal_mul hm]
  unfold massRows
  rw [ENNReal.ofReal_sum_of_nonneg fun Λ _ => hw Λ]
  refine GlobalTheory.RowsMean.sum_le_of_classes (Y.what₂ u) (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)
    (Formalism.HermitianLatticesTheory.genus HW.B.flip) (Submodule.IsFullLattice D.host.E) (fun Λ hΛ => (hLat Λ hΛ).1.1)
    (fun a b ha hb => GlobalTheory.RowsMean.genus_eq_iff _ ha hb) _ _ _ ?_
  intro Λ₀ hΛ₀
  have h1 := hOrb φ hφ Λ₀ hΛ₀
  have h2 := hOrb (fun _ => 1) (fun _ _ => rfl) Λ₀ hΛ₀
  simp only [mul_one] at h2
  rw [h1, h2, mul_assoc]
  gcongr
  refine (hbd Λ₀ hΛ₀).trans ?_
  rw [ENNReal.ofReal_mul (GlobalTheory.RowsMean.mass_nonneg _ _)]
  gcongr
  exact GlobalTheory.RowsMean.mass_le_orbMass _ _

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassLatticesOrbitsSubspacesSharpExponentStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ de : ℕ, 1 ≤ de → ∃ s : Finset (Submodule K V), (∀ U ∈ s, Module.finrank K U = j) ∧ (∀ U : Submodule K V, Module.finrank K U = j → (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)).Nonempty → ∃ U₀ ∈ s, ∃ g : isom h, g • U₀ = U) ∧ ∑ U ∈ s, orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) ≤ ENNReal.ofReal (mass h₁ I₁ * (de : ℝ) ^ j * (de : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.TotalMass.main | exact GlobalTheory.Mass.TotalMass.main | (intros; apply GlobalTheory.Mass.TotalMass.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
section
namespace GlobalTheory.VolRatioFromSiegelWeil

theorem volumeRatio :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hP =>
    GlobalTheory.VolRatioFromSecondClause.volumeRatio
      (_root_.GlobalTheory.OneVecMeas.sw1b2_of_cc (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil hP))

end GlobalTheory.VolRatioFromSiegelWeil
end

