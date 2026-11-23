module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesCharRepModPowLeOfDuality
section
open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift ReciprocityTheory.Gal

namespace GlobalTheory.Cyc.CocycleCount

theorem card_Z1_mul_card_H0 {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) (h : ContAction rho) :
    Nat.card (Z1 rho) * Nat.card (H0 rho) = Nat.card M * Nat.card (H1 rho) := by
  have hker : LinearMap.ker (d0 rho) = H0 rho := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have hg := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at hg
      exact hg
    · intro h
      funext g
      rw [amitsur_d0_apply, Pi.zero_apply, h g, sub_self]
  have hM : Nat.card M = Nat.card (H0 rho) * Nat.card (B1 rho) := by
    rw [(LinearMap.ker (d0 rho)).card_eq_card_quotient_mul_card,
      Nat.card_congr (LinearMap.quotKerEquivRange (d0 rho)).toEquiv, hker]
    rfl
  have hZ : Nat.card (Z1 rho) = Nat.card (B1 rho) * Nat.card (H1 rho) := by
    rw [((B1 rho).comap (Z1 rho).subtype).card_eq_card_quotient_mul_card,
      Nat.card_congr (Submodule.comapSubtypeEquivOfLe (coboundaries_le_cocycles rho h)).toEquiv]
  rw [hZ, hM]
  ring

private theorem pow_sub_dvd_val_of_pow_mul_eq_zero {l : ℕ} (hl : 0 < l) (N r : ℕ) [NeZero (l ^ r)] (a : ZMod (l ^ r))
    (ha : (l : ZMod (l ^ r)) ^ N * a = 0) : l ^ (r - N) ∣ a.val := by
  rcases le_or_gt r N with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero]
    exact one_dvd _
  · have h1 : ((l ^ N * a.val : ℕ) : ZMod (l ^ r)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact ha
    rw [CharP.cast_eq_zero_iff (ZMod (l ^ r)) (l ^ r)] at h1
    have h2 : l ^ r = l ^ N * l ^ (r - N) := by
      rw [← pow_add, Nat.add_sub_cancel' h.le]
    have h3 : l ^ N * l ^ (r - N) ∣ l ^ N * a.val := by
      rw [← h2]
      exact h1
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hl N) h3

private theorem card_le_pow_of_injective_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (N r : ℕ) {X : Type*} (f : X → ZMod (l ^ r))
    (hf : Function.Injective f) (hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0) :
    Nat.card X ≤ l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  let g : X → Fin (l ^ N) := fun x => ⟨(f x).val / l ^ (r - N), by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hl _), ← pow_add]
    calc (f x).val < l ^ r := ZMod.val_lt _
      _ ≤ l ^ (N + (r - N)) := Nat.pow_le_pow_right hl (by omega)⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    apply ZMod.val_injective
    have hx := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f x) (hann x)
    have hy := pow_sub_dvd_val_of_pow_mul_eq_zero hl N r (f y) (hann y)
    have e : (f x).val / l ^ (r - N) = (f y).val / l ^ (r - N) := congrArg Fin.val hxy
    rw [← Nat.div_mul_cancel hx, ← Nat.div_mul_cancel hy, e]
  have hc := Nat.card_le_card_of_injective g hg
  simpa using hc

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G]

theorem card_invariants_twistedDual_charRep_le_pow (χ ψ : G →* ℤ_[l]ˣ) (N r : ℕ)
    (g₀ : G) (hg : ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ))) :
    Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ∧
    Nat.card (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G))) ≤
      l ^ N := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have key : ∀ (φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r))) (m : ZMod (l ^ r)), φ m = m * φ 1 := by
    intro φ m
    have h := LinearMap.map_smul (show Module.Dual (ZMod (l ^ r)) (ZMod (l ^ r)) from φ) m 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  let f : H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →
      ZMod (l ^ r) := fun x => x.1 1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply LinearMap.ext
    intro m
    change x.1 m = y.1 m
    rw [key x.1 m, key y.1 m]
    exact congrArg (m * ·) hxy
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1
    ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 hg.le)
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(N : ℤ)) := zpow_pos (by exact_mod_cast hl) _
  have hvn : ‖v‖ = 1 := by
    have hn := congrArg norm hv
    rw [norm_mul, PadicInt.norm_p_pow, hg] at hn
    exact mul_right_cancel₀ hpos.ne' (hn.trans (one_mul _).symm)
  have hvu : IsUnit (PadicInt.toZModPow r v) := (PadicInt.isUnit_iff.2 hvn).map _
  have hred : (redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1 =
      PadicInt.toZModPow r v * (l : ZMod (l ^ r)) ^ N := by
    have e := congrArg (PadicInt.toZModPow r) hv
    simp only [map_mul, map_pow, map_natCast, map_sub, map_one] at e
    rw [redChar_apply, redChar_apply, e]
  have hann : ∀ x, (l : ZMod (l ^ r)) ^ N * f x = 0 := by
    intro x
    have h0 : ∀ g, twDual (redChar χ r) (charRep (redChar ψ r)) g x.1 = x.1 := by
      have hx := x.2
      exact hx
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ r)) (ZMod (l ^ r)) => φ 1) (h0 g₀)
    simp only [twDual_apply, charRep_apply, mul_one] at h1
    rw [key x.1] at h1
    have h2 : ((redChar χ r g₀ : ZMod (l ^ r)) * (redChar ψ r g₀⁻¹ : ZMod (l ^ r)) - 1) * f x = 0 := by
      show _ * x.1 1 = 0
      linear_combination h1
    rw [hred, mul_assoc] at h2
    exact hvu.mul_right_eq_zero.1 h2
  exact ⟨Finite.of_injective f hf, card_le_pow_of_injective_of_pow_mul_eq_zero N r f hf hann⟩

theorem card_cocycles_charRep_modPow_le_of_duality : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℤ_[l]ˣ), (Continuous fun g => (ψ g : ℤ_[l])) → ∀ (N r d : ℕ) (g₀ : G), ‖(χ g₀ : ℤ_[l]) * (ψ g₀⁻¹ : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(N : ℤ)) → Nonempty (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar χ r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) → Function.Injective (ReciprocityTheory.Gal.cup20 (redChar χ r) (ReciprocityTheory.Gal.charRep (redChar ψ r)) (MonoidHom.id G)) → Nat.card (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep (redChar ψ r))) * Nat.card (ZMod (l ^ r)) ^ d → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ l ^ N * l ^ (r * (d + 1)) := by
  intro l _ G _ _ _ χ ψ hψ N r d g₀ hg hH2 hinj hH1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero (l ^ r) := ⟨(pow_pos hl r).ne'⟩
  have hcont : ContAction (charRep (redChar ψ r)) := by
    apply contAction_charRep
    have e : (fun g => ((redChar ψ r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) =
        fun g => PadicInt.toZModPow r (ψ g : ℤ_[l]) := funext fun g => redChar_apply ψ r g
    rw [e]
    exact (continuous_toZModPow r).comp hψ
  have h1 := card_Z1_mul_card_H0 (charRep (redChar ψ r)) hcont
  obtain ⟨hfin0, hle0⟩ := card_invariants_twistedDual_charRep_le_pow χ ψ N r g₀ hg
  obtain ⟨e⟩ := hH2
  let F : H2 (charRep (redChar ψ r)) →
      (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+ ZMod (l ^ r)) :=
    fun c => (e.toLinearMap ∘ₗ
      (cup20 (redChar χ r) (charRep (redChar ψ r)) (MonoidHom.id G) c)).toAddMonoidHom
  have hF : Function.Injective F := by
    intro c c' hcc
    apply hinj
    apply LinearMap.ext
    intro y
    apply e.injective
    exact DFunLike.congr_fun hcc y
  have : Finite (H0 ((twDual (redChar χ r) (charRep (redChar ψ r))).comp (MonoidHom.id G)) →+
      ZMod (l ^ r)) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (H2 (charRep (redChar ψ r))) := Finite.of_injective F hF
  have hc2 : Nat.card (H2 (charRep (redChar ψ r))) ≤ l ^ N :=
    ((Nat.card_le_card_of_injective F hF).trans
      (GlobalTheory.natCard_addMonoidHom_zmod_le (l ^ r) _)).trans hle0
  have hc2pos : 0 < Nat.card (H2 (charRep (redChar ψ r))) := Nat.card_pos
  have h0pos : 0 < Nat.card (H0 (charRep (redChar ψ r))) := Nat.card_pos
  have hZ : Nat.card (Z1 (charRep (redChar ψ r))) =
      l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d) := by
    apply Nat.eq_of_mul_eq_mul_right h0pos
    rw [h1, hH1, Nat.card_zmod]
    ring
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hZ]; positivity), ?_⟩
  rw [hZ]
  calc l ^ r * (Nat.card (H2 (charRep (redChar ψ r))) * (l ^ r) ^ d)
      ≤ l ^ r * (l ^ N * (l ^ r) ^ d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc2)
    _ = l ^ N * l ^ (r * (d + 1)) := by ring

end GlobalTheory.Cyc.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.CocycleCount

theorem card_linear_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : Finite (A →ₗ[ZMod N] ZMod N) ∧ Nat.card (A →ₗ[ZMod N] ZMod N) ≤ Nat.card A := by
  have h1 : Finite (A →ₗ[ZMod N] ZMod N) := DFunLike.finite _
  have h2 : Finite (A →+ ZMod N) := DFunLike.finite _
  refine ⟨h1, le_trans ?_ (GlobalTheory.natCard_addMonoidHom_zmod_le N A)⟩
  exact Nat.card_le_card_of_injective (fun f => f.toAddMonoidHom) LinearMap.toAddMonoidHom_injective

theorem card_H2_le (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Finite (ReciprocityTheory.Gal.H2 rho) ∧ Nat.card (ReciprocityTheory.Gal.H2 rho) ≤ Nat.card M := by
  have hT := card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  have hA := card_linear_le N A
  have hAc : Nat.card A ≤ Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have := hA.1
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E]
  exact hA.2.trans (hAc.trans hTc)

theorem card_cocycles_mul_invariants_discrete (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) :
    Nat.card (ReciprocityTheory.Gal.Z1 rho) * Nat.card (ReciprocityTheory.Gal.H0 rho) =
      Nat.card (ReciprocityTheory.Gal.H1 rho) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 rho ≤ ReciprocityTheory.Gal.Z1 rho := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · exact (hrho.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype)
  have h2 : Nat.card ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype) =
      Nat.card (ReciprocityTheory.Gal.B1 rho) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : LinearMap.ker (ReciprocityTheory.Gal.d0 rho) = ReciprocityTheory.Gal.H0 rho := by
    ext m
    rw [LinearMap.mem_ker, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [ReciprocityTheory.Gal.amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ReciprocityTheory.Gal.d0 rho))
  have h4 : Nat.card (M ⧸ LinearMap.ker (ReciprocityTheory.Gal.d0 rho)) = Nat.card (ReciprocityTheory.Gal.B1 rho) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

def repOfAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

theorem count_of_euler (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2) := by
  obtain ⟨hf2, hc2⟩ := card_H2_le _ _ M _ rho e hb
  have hZ := card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have h2 : 0 < Nat.card (ReciprocityTheory.Gal.H2 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : ↥{c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) :=
    Nat.finite_of_card_ne_zero (by rw [hZ']; positivity)
  refine ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ E.symm), ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr E, hZ', pow_succ' _ (_ + 1)]
  exact Nat.mul_le_mul_right _ hc2

theorem cocycles_finite_ncard_le :
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, l ^ r • m = 0) → (∀ m, IsLocallyConstant fun g => a g m) → {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧ {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤ Nat.card M ^ (Module.finrank ℚ_[l] ↥K.1 + 2) := by
  intro hT hE l _ K r M _ _ a h1 hmul hr hlc
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  have hEu := hE l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  exact count_of_euler _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl

end GlobalTheory.CocycleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GaloisTransport

section Generic

variable {R G' G Q M : Type} [CommRing R] [Group G'] [TopologicalSpace G'] [Group G]
  [TopologicalSpace G] [AddCommGroup Q] [Module R Q] {N : ℕ} [AddCommGroup M] [Module (ZMod N) M]
  [TopologicalSpace M] [DiscreteTopology M]

theorem card_H1_transport (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (act : G' → Q → Q) (Z B : Submodule R (G' → Q))
    (hZ : ∀ c, c ∈ Z ↔ IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + act g (c h))
    (hB : ∀ c, c ∈ B ↔ ∃ t, ∀ g, c g = act g t - t)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card (↥Z ⧸ B.comap Z.subtype) = Nat.card (ReciprocityTheory.Gal.H1 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  let F : (G' → Q) → (G → M) := fun c g => e (c (φ.symm g))
  have hF : ∀ c g, F c (φ g) = e (c g) := fun c g => by simp only [F, MulEquiv.symm_apply_apply]
  have hFB : ∀ c, c ∈ B ↔ F c ∈ ReciprocityTheory.Gal.B1 rho := by
    intro c
    rw [hB, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨e t, fun g => ?_⟩
      simp only [F, ht, map_sub, hr]
    · rintro ⟨m, hm⟩
      refine ⟨e.symm m, fun g => ?_⟩
      have h1 := hm (φ g)
      rw [hF] at h1
      apply e.injective
      rw [h1, map_sub, ← hr', e.apply_symm_apply]
  have hZf : ∀ c : ↥Z, F c.1 ∈ ReciprocityTheory.Gal.Z1 rho := fun c => by
    obtain ⟨hc1, hc2⟩ := (hZ c.1).1 c.2
    refine ⟨((hc1.comp_continuous hφ.2).comp e).continuous, fun g h => ?_⟩
    simp only [F, map_mul, hc2, map_add (f := _), hr]
  have hZb : ∀ f : ↥(ReciprocityTheory.Gal.Z1 rho), (fun g => e.symm (f.1 (φ g))) ∈ Z := fun f => by
    obtain ⟨hf1, hf2⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 f.2
    refine (hZ _).2 ⟨((IsLocallyConstant.iff_continuous _).2 (hf1.comp hφ.1)).comp e.symm,
      fun g h => ?_⟩
    apply e.injective
    have h2 := hr' g (e.symm (f.1 (φ h)))
    rw [e.apply_symm_apply] at h2
    simp only [map_mul, hf2, map_add (f := _), AddEquiv.apply_symm_apply, h2]
  let E : ↥Z ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨F c.1, hZf c⟩
      invFun := fun f => ⟨fun g => e.symm (f.1 (φ g)), hZb f⟩
      left_inv := fun c => Subtype.ext (funext fun g => by
        show e.symm (F c.1 (φ g)) = c.1 g
        rw [hF, e.symm_apply_apply])
      right_inv := fun f => Subtype.ext (funext fun g => by
        show e (e.symm (f.1 (φ (φ.symm g)))) = f.1 g
        rw [e.apply_symm_apply, MulEquiv.apply_symm_apply]) }
  have hEsub : ∀ a b : ↥Z, ((E a - E b : ↥(ReciprocityTheory.Gal.Z1 rho)) : G → M) = F ((a - b : ↥Z) : G' → Q) :=
    fun a b => funext fun g => by
      show e (a.1 (φ.symm g)) - e (b.1 (φ.symm g)) = e (a.1 (φ.symm g) - b.1 (φ.symm g))
      rw [map_sub]
  refine Nat.card_congr (Quotient.congr E fun a b => ?_)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hEsub, hFB]

theorem card_H0_transport (φ : G' ≃* G) (act : G' → Q → Q)
    (e : Q ≃+ M) (rho : Representation (ZMod N) G M)
    (hr : ∀ g x, rho g (e x) = e (act (φ.symm g) x)) :
    Nat.card {x : Q // ∀ g, act g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  have hr' : ∀ g x, rho (φ g) (e x) = e (act g x) := fun g x => by
    rw [hr, MulEquiv.symm_apply_apply]
  refine Nat.card_congr
    { toFun := fun x => ⟨e x.1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by rw [hr, x.2]⟩
      invFun := fun m => ⟨e.symm m.1, fun g => by
        apply e.injective
        rw [← hr', e.apply_symm_apply]
        exact (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2 (φ g)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

end Generic

theorem card_H1_H0_transport : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  intro l _ K LL _ _ _ O _ _ A LA I hI N M _ _ _ _ e rho hrho
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hφ := GlobalTheory.fixingSubgroupEquiv_bicontinuous _ _ K.1
  refine ⟨card_H1_transport _ hφ (fun g x => actQ LA I hI g x) (quotientCocycles LA I hI) (BQ LA I hI)
    (fun c => Iff.rfl) (fun c => ?_) e rho hrho,
    card_H0_transport _ (fun g x => actQ LA I hI g x) e rho hrho⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g => (congrFun ht g).symm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, funext fun g => (ht g).symm⟩

end GlobalTheory.GaloisTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem charpoly_span_and_hom_relations_of_admissible : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG1 i r → LargeLevelLemmas.CharpolyCoeffsLemmaFamily i r ∧ LargeLevelLemmas.SpanQuotientLemma i r ρ π ∧ LargeLevelLemmas.HomRelationsLemmaAllChoices i r ρ π :=
  fun _ i r ρ π h => ⟨LargeLevelLemmas.span_lemma_clause i r h, LargeLevelLemmas.eigenspace_lemma_clause i r ρ π, LargeLevelLemmas.relation_lemma_clause i r ρ π⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDdR

theorem ddR_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  exact GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ

end GlobalTheory.Per.TiedDdR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEll
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CycUnram

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  intro D i v hv γ hγ
  have hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by simpa [placesOver] using hv
  have h1 : cycZ D.host.E D.nd.Om (D.nd.l i) γ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hl (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hγ.2 x hx) n]
    simp
  have h2 : epsU D.nd i γ = 1 := by
    unfold epsU Glob.epsO
    rw [MonoidHom.comp_apply, h1, map_one]
  refine ⟨h2, fun c hc1 hc2 => ?_⟩
  change D.nd.chi i c γ = D.nd.chi i 1 γ
  rw [D.nd.chi_def i c hc1 hc2, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, h1, map_one,
    one_zpow, mul_one]

end GlobalTheory.CycUnram
end

