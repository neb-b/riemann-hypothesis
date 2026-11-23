module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove.Rat

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_of_loc (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · exact hloc v hI (ind v) (hind1 v) (hind0 v)
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

variable {D : D7}

theorem mov_comp {k : ℕ} {m m₂ : Matrix (Fin k) (Fin k) (AfE D)} {L L' L'' : Lt D.host.E k}
    (h : IsMov m L L') (h₂ : IsMov m₂ L' L'') : IsMov (m₂ * m) L L'' := by
  intro u
  rw [h₂ u]
  constructor
  · rintro ⟨u₁, hu₁, rfl⟩
    obtain ⟨u₀, hu₀, rfl⟩ := (h u₁).1 hu₁
    exact ⟨u₀, hu₀, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    exact ⟨m *ᵥ u₀, (h _).2 ⟨u₀, hu₀, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩

theorem smul_sandwich {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' G B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * G * B) = P • G := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hB,
    Matrix.mul_smul, mul_one]

theorem map_mulVec_toAf {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E) (u : Fin k → D.host.E) :
    (M.map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) *ᵥ toAf u = toAf (M *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, toAf, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    TensorProduct.tmul_sum]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (u : Fin k → D.host.E) :
    toAf (c • u) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) : AfE D) • toAf u := by
  funext i
  simp only [toAf, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

theorem smul_step {R : Type} [CommRing R] {k : ℕ} (P : R) (K G : Matrix (Fin k) (Fin k) R) (u w : Fin k → R)
    (h : P • K = P • G) : P • (K *ᵥ u - w) = P • (G *ᵥ u - w) := by
  rw [smul_sub, smul_sub, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]

theorem toAf_sub {k : ℕ} (u w : Fin k → D.host.E) : (toAf (u - w) : Fin k → AfE D) = toAf u - toAf w := by
  funext i
  simp only [toAf, Pi.sub_apply, TensorProduct.tmul_sub]

theorem toAf_mem {k : ℕ} {L : Lt D.host.E k} {u : Fin k → D.host.E} (hu : u ∈ L) : toAf u ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, u, hu, rfl⟩

end GlobalTheory.Ker.LevMove.Rat


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Ker.LevMove.levK_of_rat_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  intro D S T C Lv γ κ hred a f g₁ g₂ L ha hf hrat h1 h2 t1 t2 hLfg hLs hMfg m1 m2
  set G : Matrix (Fin T.rank) (Fin T.rank) (AfE D) :=
    (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x with hGdef
  have hfa : fmt T a = 1 := (((GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1 a ha).1
  have hff : fmt T f = G := by
    have e : fmt T (a * f) = G := by
      rw [fmt, hrat, Matrix.map_map]; rfl
    rw [← e, GlobalTheory.Ker.LevMove.fmt_mul', hfa, one_mul]
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨hto, -, -, lawsΛ⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Ker.isMov_laws D T.rank L ⟨hLfg, hLs⟩
  obtain ⟨-, hinv2, -, -, -⟩ := (lawsΛ _ _ e2).2 (mapL γ L) hMfg m2
  have hk : IsMov (fmt T (g₂⁻¹ * f * g₁)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.mov_comp m1 (GlobalTheory.Ker.LevMove.Rat.mov_comp (hG γ) hinv2)
  obtain ⟨κ', hκ', hcong⟩ := hred
  refine ⟨mul_mem (mul_mem (inv_mem h2) hf) h1, hk, κ', hκ', fun i => ?_⟩
  have hb : toAf (Lv.β i) ∈ hatV C.X.Λ := GlobalTheory.Ker.LevMove.Rat.toAf_mem (Lv.β_mem i)
  have hw : toAf (∑ j, κ' j i • Lv.β j) ∈ hatV C.X.Λ :=
    GlobalTheory.Ker.LevMove.Rat.toAf_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (Lv.β_mem j))
  refine GlobalTheory.Ker.LevMove.Rat.mem_of_loc (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
    (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw) ?_
  intro v hv α a1 a0
  have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
  have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
  set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
  have hPint : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := GlobalTheory.Ker.LevMove.ind_int a1 a0
  have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
  have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
  have qk : P • fmt T (g₂⁻¹ * f * g₁) = P • G := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.smul_sandwich P _ _ _ _ q2 q1 e2
  obtain ⟨d, hd⟩ : ∃ d : Fin T.rank → D.host.E, d = (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i -
    ∑ j, κ' j i • Lv.β j := ⟨_, rfl⟩
  have hx : P • (fmt T (g₂⁻¹ * f * g₁) *ᵥ toAf (Lv.β i) - toAf (∑ j, κ' j i • Lv.β j)) = P • toAf d := by
    rw [GlobalTheory.Ker.LevMove.Rat.smul_step P _ _ _ _ qk, GlobalTheory.Ker.LevMove.Rat.map_mulVec_toAf,
      ← GlobalTheory.Ker.LevMove.Rat.toAf_sub, hd]
  have hPd : P • toAf d ∈ hatV C.X.Λ := by
    rw [← hx]
    exact GlobalTheory.Ker.LevMove.int_smul_mem C.X.Λ hPint (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw)
  change P • _ ∈ hatV (Lv.𝔪 • C.X.Λ)
  rw [hx]
  obtain ⟨s, hs, hsd⟩ := hcong i
  rw [← hd] at hsd
  obtain ⟨u, hu, m, hm, hum⟩ := Ideal.isCoprime_iff_exists.1 hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hsplit : P • toAf d = P • toAf ((t * s) • d) +
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((m : 𝓞 D.host.E) : D.host.E) : AfE D) • (P • toAf d) := by
    have hum' : ((t * s : 𝓞 D.host.E) : D.host.E) + ((m : 𝓞 D.host.E) : D.host.E) = 1 := by
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hum
      simpa using this
    rw [GlobalTheory.Ker.LevMove.Rat.toAf_smul, smul_comm P, ← add_smul, ← TensorProduct.tmul_add, hum',
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (GlobalTheory.Ker.LevMove.ideal_smul_mem C.X.Λ Lv.𝔪 hm hPd)
  refine GlobalTheory.Ker.LevMove.int_smul_mem _ hPint (GlobalTheory.Ker.LevMove.Rat.toAf_mem ?_)
  rw [mul_smul]
  exact Submodule.smul_mem _ t hsd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilLevel

theorem stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := _root_.GlobalTheory.WeilLevelStab.exists_level_stab
theorem prodId : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := _root_.GlobalTheory.ThetaFixedProd.prod_eq_of_fixed
theorem openKer : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := _root_.GlobalTheory.OpenKer.eq_one_on_finite_of_mul

theorem scalar_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ))
    (hAR : ∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1)
    (hM : ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hp : ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      ∀ x, M f x * star (M g x) = f x * star (g x)) :
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → M f = c • f := by
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨l1, l2, l3, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
    rw [Complex.star_def, Complex.mul_conj', h]; simp
  have skew : ∀ x y : WO S T, symplOH S T y x = -symplOH S T x y := fun x y => by
    have := l3 (x + y)
    rw [l1, l2, l2, l3, l3] at this
    linear_combination this

  have hfix : ∀ w g, (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T w g) = (heisO ψ S T w g)) := by
    intro w g hg hw u hu hu0
    have e1 := hcomp u w g
    have e2 := hcomp w u g
    rw [hg u hu hu0] at e2
    rw [e1, add_comm u w]
    have hs : ψ (symplOH S T u w) = ψ (symplOH S T w u) := by
      have h1 := hw u hu hu0
      rw [← l4] at h1
      have h2 : ψ (symplOH S T w u) * ψ (symplOH S T w u) = 1 := by
        rw [← AddChar.map_add_eq_mul]; exact h1
      rw [skew w u, AddChar.map_neg_eq_inv]
      exact inv_eq_of_mul_eq_one_right h2
    rw [hs, e2]
  by_cases h0 : ∃ f₀ x₀, IsThetaFunO ψ S T f₀ ∧ (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f₀ = f₀) ∧ f₀ x₀ ≠ 0
  · obtain ⟨f₀, x₀, hf₀, hf₀N, hx₀⟩ := h0
    have h1 := hp f₀ f₀ hf₀ hf₀N hf₀ hf₀N x₀
    have hn1 : ‖M f₀ x₀‖ = ‖f₀ x₀‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ x₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]; exact norm_ne_zero_iff.2 hx₀
    have hs : star (M f₀ x₀) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ x₀) / star (M f₀ x₀), fun f hf hfN => funext fun x => ?_⟩
    obtain ⟨γ, hγ, hA⟩ := hAR (x₀ - x)
    set w := x₀ - x - γ with hw
    have hg := hth w f₀ hf₀
    have hgN := hfix w f₀ hf₀N hA
    have h2 := hp f (heisO ψ S T w f₀) hf hfN hg hgN x
    rw [hc w f₀ hf₀ hf₀N hA] at h2
    obtain ⟨δ, hδ⟩ := (ratL T S).neg_mem hγ
    have hxw : x + w = ratW T S δ + x₀ := by
      have hδ' : ratW T S δ = -γ := hδ
      rw [hδ', hw]; abel
    simp only [heisO, hxw] at h2
    rw [hf₀.quasi δ x₀, (hM f₀ hf₀ hf₀N).quasi δ x₀] at h2
    rw [star_mul', star_mul', star_mul', star_mul'] at h2
    have h3 : M f x * star (M f₀ x₀) = f x * star (f₀ x₀) := by
      linear_combination (ψ (symplOH S T x w) * ψ (-symplOH S T (ratW T S δ) x₀)) * h2
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * hunit (symplOH S T x w)
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * ψ (symplOH S T x w) * star (ψ (symplOH S T x w))
          * hunit (-symplOH S T (ratW T S δ) x₀)
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h3, mul_comm]
  · refine ⟨0, fun f hf hfN => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hfN, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.WeilLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    funext x
    simp [Lift.liftInt, thetaKO_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    have h2 := congrFun hb.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 h2 ⊢
    simp only [thetaKO_add, add_mul]
    rw [integral_add (hI a ha.1 x) (hI b hb.1 x), h1, h2, add_zero]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 ⊢
    simp only [thetaKO_smul, mul_assoc]
    rw [integral_const_mul, h1, mul_zero]

theorem eq_zero_of_le_mul_pos {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  rcases eq_or_ne K 0 with rfl | hK0
  · exact (h 1 one_pos).trans (by simp)
  · have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have := h (ε / K) (ENNReal.div_pos hε' hK)
    rwa [ENNReal.mul_div_cancel hK0 hK] at this

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hint : ∀ f', IsThetaFunO ψ V W f' → ∀ x,
      IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' x => by
    simpa [rTr] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ g ∈ GlobalTheory.Size.thetaLevel ψ V W U, Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 →
      growthSob θ V 0 A (lift ω ν 𝓕 f Φ) ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := by
    intro g hg hg0
    have hb := hC (f - g) (sub_mem hf hg) Φ hΦ
    have heq : lift ω ν 𝓕 (f - g) Φ = lift ω ν 𝓕 f Φ := by
      funext x
      have h0 := congrFun hg0 x
      simp only [lift, Lift.liftInt, Pi.zero_apply] at h0 ⊢
      simp only [thetaKO_sub, sub_mul]
      rw [integral_sub (hint f hf.1 x) (hint g hg.1 x), h0, sub_zero]
    rwa [heq] at hb
  have hdec := hL.decay_ne_top Φ hΦ A
  have hz : growthSob θ V 0 A (lift ω ν 𝓕 f Φ) = 0 := by
    refine eq_zero_of_le_mul_pos (K := C * decayInt ν 𝓕 A Φ) (ENNReal.mul_ne_top ENNReal.coe_ne_top hdec) ?_
    intro δ hδ
    obtain ⟨g, hg, hg0, hsm⟩ := happ d δ hδ
    calc growthSob θ V 0 A (lift ω ν 𝓕 f Φ)
        ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := key g hg hg0
      _ ≤ C * δ * decayInt ν 𝓕 A Φ := by gcongr
      _ = C * decayInt ν 𝓕 A Φ * δ := by ring
  have hz' : growthSize V A (lift ω ν 𝓕 f Φ) = 0 := by simpa [growthSob] using hz
  unfold growthSize at hz'
  funext x
  have hx := ENNReal.ofReal_eq_zero.1 ((ENNReal.iSup_eq_zero.1 hz') x)
  have hpos : 0 < height V x ^ A := pow_pos (lt_of_lt_of_le one_pos ((height_laws V).1 x)) A
  rw [div_le_iff₀ hpos, zero_mul] at hx
  exact norm_le_zero_iff.1 hx

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
end

