module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRows
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.DiagFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem vset_one {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨hfg, hdual, s, hs, -, h1, h2⟩ := h
  exact ⟨hfg, hdual, s, hs, Nat.coprime_one_right s, h1, h2⟩

theorem conjI_mono {P Q : Ideal (𝓞 E)} (h : P ≤ Q) : conjI P ≤ conjI Q := by
  unfold conjI
  exact Ideal.span_mono fun _ ⟨b, hb, e⟩ => ⟨b, h hb, e⟩

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 := GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (0 : ℂ) (0 : TF n g)
    simpa using h0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      GlobalTheory.SW.UnAct.thA_add idx hs hx (hf a) (GlobalTheory.SW.RecSum.isSB_sum s f hf), ih]

theorem isSB_unitv_projA (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) {φ : TF n g} (hφ : IsSB φ) :
    IsSB (unitv (projA X bas w (tens Λ L) φ)) := by
  unfold unitv projA
  refine isSB_smul _ (isSB_smul _ ?_)
  refine finsum_mem_induction (fun ψ => IsSB ψ) isSB_zero
    (fun a b ha hb => (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) a b ha hb).1) ?_
  rintro _ ⟨y, -, rfl⟩
  exact isSB_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).1

private theorem thA_finset_sum_smul (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (a : T → ℂ) (ψ : T → TF n g)
    (hψ : ∀ i, IsSB (ψ i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (∑ i ∈ s, a i • ψ i) x z = ∑ i ∈ s, a i * thA X bas idx (ψ i) x z := by
  rw [thA_sum idx hs hx s _ (fun i => isSB_smul (a i) (hψ i)), Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x (a i) (ψ i)]
  rfl

theorem thP_phi_eq_thP_phiF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn D hrn M 𝔐 𝔍 hM hMm hsplit hcop v₀ hv₀ k k' Λ hΛ P hP
  have hle : D.𝔪 ≤ 𝔍 := by
    rw [hsplit]
    exact Ideal.mul_le_inf.trans inf_le_right
  have h𝔍 : 𝔍 ≠ ⊥ := by
    intro h0
    apply D.ne_bot
    rw [hsplit, h0, Ideal.mul_bot]
  have hMJ : ((M : ℕ) : 𝓞 E) ∈ 𝔍 := hle hMm
  have hcopJ : IsCoprime 𝔍 (conjI 𝔍) := by
    have h1 := D.cop
    rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
    exact top_unique (h1.symm.le.trans (sup_le_sup hle (conjI_mono hle)))
  obtain ⟨α, 𝔞, hα, hspan, hcopa⟩ := _root_.GlobalTheory.Dict.exists_generator_at_primes_dividing E 𝔍 M h𝔍 hM
  set H : Matrix (Fin n) (Fin n) E :=
    Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) with hHdef
  obtain ⟨hunit, hmove⟩ := _root_.GlobalTheory.Dict.Patch.main E n r M 𝔍 𝔞 α hM hMJ hcopJ hα hspan hcopa H hHdef
  obtain ⟨Λ', hΛ', Λ'', hΛ'', hmv, hle1, hle2⟩ := hmove Λ hΛ
  obtain ⟨t, ht0, ht⟩ := _root_.GlobalTheory.Dict.SumFree.sum_free E r X g bas idx n hs hn D hrn M 𝔐 𝔍 𝔞 α hM hMm hsplit hcop hα
    hspan hcopa v₀ hv₀ H hHdef Λ hΛ Λ' hΛ' Λ'' hΛ'' hmv hle1 hle2
  obtain ⟨t', ht'1, ht'⟩ := _root_.GlobalTheory.Dict.thA_vacuum_hAct E r X g bas idx n hs hn D.w D.w_int D.w_tr H hunit Λ
    (vset_one hΛ) Λ'' hΛ'' hmv
  obtain ⟨P', hP', hPd⟩ := _root_.GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct E r X g q0 hr bas idx n hs hn H hunit k k' P hP
  have ht'0 : t' ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at ht'1
    exact zero_ne_one ht'1
  refine ⟨Λ', hΛ', (t / t') • P', Submodule.smul_mem _ _ hP', fun L hL x hx => ?_⟩
  have hSh : SelfD X (D.sh L) := ((_root_.GlobalTheory.SW.level_laws E r X g bas idx n hs hn D hrn).2.2.2.1 L hL).1
  have hv := hv₀ L hL
  have hφ := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh (vset_one hΛ) hv.1
  have hφ'' := isSB_unitv_projA idx hs hn D.w_int D.w_tr hSh hΛ'' hv.1
  have hheis : ∀ (y : Matrix (Fin n) (Fin r) E) (ψ : TF n g), IsSB ψ → IsSB (heisG X bas y ψ) :=
    fun y ψ hψ => ((heisG_laws E r X g bas idx n hs hn).2.2.2 y ψ hψ).1
  obtain ⟨s, hs1, hs2⟩ := ht L hL
  have hphiF : IsSB (phiF bas D 𝔐 hrn v₀ L Λ') := by
    have h2 : phiF bas D 𝔐 hrn v₀ L Λ' = t⁻¹ • (t • phiF bas D 𝔐 hrn v₀ L Λ') := by
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h2, ← hs2]
    exact isSB_smul _ (GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ''))
  have hDphi : IsSB (D.phi bas hrn v₀ L Λ) := by
    rw [hs1]
    exact GlobalTheory.SW.RecSum.isSB_sum s _ fun y => isSB_smul _ (hheis _ _ hφ)
  have key : ∀ z, t * thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z) =
      t' * thA X bas idx (D.phi bas hrn v₀ L Λ) x z := by
    intro z
    have e1 := congrFun (GlobalTheory.SW.UnAct.thA_smul (bas := bas) idx x t (phiF bas D 𝔐 hrn v₀ L Λ'))
      (GlobalTheory.Dict.hAct X idx H z)
    rw [Pi.smul_apply, smul_eq_mul] at e1
    rw [← e1, ← hs2, thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ''), hs1,
      thA_finset_sum_smul idx hs hx s _ _ (fun y => hheis _ _ hφ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [_root_.GlobalTheory.Dict.thA_heisG_hAct E r X g bas idx n hs hn H hunit _ _ hφ hφ'' t' x hx
      (fun z => ht' (D.sh L) hSh (v₀ L) hv x hx z) y z]
    ring
  have hana := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hphiF P' hP').2.2.2 x hx
  have hdiff := ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff (GlobalTheory.SW.ThetaHol.differentiable_thA idx hs hDphi hx)
  have hfun : (fun z => thA X bas idx (phiF bas D 𝔐 hrn v₀ L Λ') x (GlobalTheory.Dict.hAct X idx H z)) =
      (t' / t) • thA X bas idx (D.phi bas hrn v₀ L Λ) x := by
    funext z
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key z
  unfold GlobalTheory.SW.thP
  rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ← hPd _ hana, hfun,
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul_fun _ _ hdiff]
  field_simp

end GlobalTheory.Dict.DiagFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliser
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem GlobalTheory.Dict.conjI_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  have hb : ∀ a : 𝓞 E, Lev.bar a = H.bar a := fun a => by
    apply IsFractionRing.injective (𝓞 E) E
    exact (H.bar_eq a).symm
  ext a
  rw [Lev.mem_conjI, hb, Mfr,
    Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  exact ⟨fun ⟨y, hy, e⟩ => H.bar.injective e ▸ hy, fun h => ⟨a, h, rfl⟩⟩

theorem GlobalTheory.Dict.mult_eq_one_on_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  intro E _ _ _ H Dw l Xo c n d σ r g X bas idx D hn ph hs hev hT D' φ hr hinj hsp hEF v₀ hv mu hmu L hL ga
    hga hfix
  have hle : D.𝔪 ≤ Mfr l := by rw [hT.prod]; exact Ideal.mul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
  have hN : Mfr l * conjI (Mfr l) = Ideal.span {(l.M : 𝓞 E)} := by
    rw [conjI_half, mul_comm]; exact l.prod
  obtain ⟨h1, h2, h3⟩ := (stab_trivial_mod E r X g bas idx n hs hev D (Mfr l) l.M hle hN
    (fun k hk => (hT.grp k).1 hk) ga hga).2 L hL hfix
  refine ⟨?_, h1⟩
  obtain ⟨-, -, hgrp, hlat, -⟩ := GlobalTheory.SW.level_laws E r X g bas idx n hs hev D hn
  obtain ⟨hu, k, hk, hred⟩ := (hgrp ga).1 hga
  obtain ⟨hsd, -, -, hsh⟩ := hlat L hL
  have hfix' : mapL ga (D.sh L) = D.sh L := by rw [← (hsh ga hga).2, hfix]
  have hvac := hv L hL
  have hw := _root_.GlobalTheory.VacMult.wG_vac_eq E r X g bas idx n hs hev H D' φ hr hinj hsp hEF (D.sh L) hsd l.M l.three_le ga hu
    hfix' h2 (v₀ L) (hT.w ▸ hvac)
  have hlam : D.lam ⟨k, hk⟩ = 1 := hT.det _ (h3 ⟨k, hk⟩ hred l.three_le)
  have e := hmu ga hga L hL ⟨k, hk⟩ hred
  rw [hw, hlam, hfix, Units.val_one, _root_.mul_one] at e
  have hne : v₀ L ≠ 0 := fun h0 => by
    have := hvac.2.1
    rw [h0] at this
    simp [ip, haar, haarAt] at this
  have : (mu ga L - 1) • v₀ L = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hne)
end

