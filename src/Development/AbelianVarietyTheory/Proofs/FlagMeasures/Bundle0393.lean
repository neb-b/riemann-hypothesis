module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatsDiscStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0389
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0390
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.LabPin
open GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem principalCongruence_fixed_vector_rational_local_field {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥) :
    fixK1 (pull I k v τ).ρ ≠ ⊥ := by
  have hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hle : ∀ t : ℚ_[D.host.g k], ‖t‖ ≤ 1 → ‖I.i k v t‖ ≤ 1 := fun t ht =>
    GlobalTheory.TypeRec.Model.emb_le (D.naut.plGw k v) (D.host.g k) (I.i k v).toRingHom (I.cont k v) t ht
  have hlt : ∀ t : ℚ_[D.host.g k], ‖t‖ < 1 → ‖I.i k v t‖ < 1 := by
    intro t ht
    have hp := (Fact.out : (D.host.g k).Prime)
    have h2 : ‖t‖ ≤ ((D.host.g k : ℕ) : ℝ) ^ (-1 : ℤ) :=
      (Padic.norm_le_pow_iff_norm_lt_pow_add_one t (-1)).2 (by simpa using ht)
    have hp0 : ((D.host.g k : ℕ) : ℚ_[D.host.g k]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h3 : ‖t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one₀ (by have := hp.one_lt; positivity)]
      simpa using h2
    have e : I.i k v t = ((D.host.g k : ℕ) : (D.naut.plGw k v).adicCompletion D.host.E) *
        I.i k v (t / ((D.host.g k : ℕ) : ℚ_[D.host.g k])) := by
      rw [← map_natCast (I.i k v) (D.host.g k), ← map_mul, mul_div_cancel₀ _ hp0]
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hle _ h3))
      (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt (D.naut.plGw k v) (D.host.g k) hw)
  have hint : ∀ (q : GL (Fin n) ℤ_[D.host.g k]) a b,
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n q)).1 a b ∈
        (D.naut.plGw k v).adicCompletionIntegers D.host.E := by
    intro q a b
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (Valued.toNormedField.norm_le_one_iff.1 (hle _ (PadicInt.norm_le_one (q.1 a b))))
  have hone : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) a b =
      I.i k v (((1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b : ℤ_[D.host.g k]) : ℚ_[D.host.g k]) := by
    intro a b
    by_cases h' : a = b
    · subst h'; simp
    · simp [Matrix.one_apply_ne h']
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun z => ?_, hy0⟩
  have hu : Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z) ∈
      GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n) := by
    rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne (D.naut.plGw k v) n).2, GlobalTheory.AdelicU.mem_princ_iff,
      GlobalTheory.AdelicU.mem_GLint_iff]
    refine ⟨⟨fun a b => hint _ a b, fun a b => ?_⟩, fun a b => ?_⟩
    · rw [← map_inv, ← map_inv]
      exact hint _ a b
    · have hz : GlobalTheory.GLp.red (D.host.g k) n z = 1 := z.2
      have hab : PadicInt.toZMod ((z : GL (Fin n) ℤ_[D.host.g k]).1 a b) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (D.host.g k))) a b :=
        congrArg (fun m : GL (Fin n) (ZMod (D.host.g k)) => m.1 a b) hz
      have h4 : (z : GL (Fin n) ℤ_[D.host.g k]).1 a b - (1 : Matrix (Fin n) (Fin n) ℤ_[D.host.g k]) a b ∈
          RingHom.ker (PadicInt.toZMod (p := D.host.g k)) := by
        rw [RingHom.mem_ker, map_sub, hab]
        by_cases h' : a = b
        · subst h'; simp
        · simp [Matrix.one_apply_ne h']
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h4
      have h5 := hlt _ h4
      apply Valued.toNormedField.norm_lt_one_iff.1
      rw [Matrix.sub_apply, hone a b]
      convert h5 using 2
      rw [PadicInt.coe_sub, map_sub]
      rfl
  change τ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom (GlobalTheory.GLp.inc (D.host.g k) n z)) y - y = 0
  rw [sub_eq_zero]
  exact GlobalTheory.Parabolic.mem_fixed.1 hy _ hu

theorem principalCongruenceFixedVectors_ne_bot_of_iso {g : ℕ} [Fact g.Prime] {n : ℕ} {π π' : QRep g n} (e : π ≅ π') (h : fixK1 π'.ρ ≠ ⊥) :
    fixK1 π.ρ ≠ ⊥ := by
  intro hb
  apply h
  rw [Submodule.eq_bot_iff] at hb ⊢
  intro x hx
  have hy : (e.inv.hom x) ∈ fixK1 π.ρ := by
    simp only [fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro q
    rw [← Rep.hom_comm_apply, hx q]
  have h0 := hb _ hy
  have : e.hom.hom (e.inv.hom x) = x := by simp
  rw [← this, h0, map_zero]

end GlobalTheory.LabPin

namespace GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.LabPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem cardE (α : Type) [Nonempty α] :
    ENNReal.ofReal ((Nat.card α : ℝ)⁻¹) = ((ENat.card α : ℕ∞) : ℝ≥0∞)⁻¹ := by
  rcases finite_or_infinite α with h | h
  · have h0 : 0 < Nat.card α := Nat.card_pos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]
    simp
  · rw [Nat.card_eq_zero_of_infinite, ENat.card_eq_top_of_infinite]
    simp

set_option maxHeartbeats 4000000 in
theorem rowsOrbC : GlobalTheory.TypeAsm.RowsOrbC := by
  intro D large₂ X Y u hS W HW hEmb φ hφ Λ₀ hΛ₀
  obtain ⟨e, he, heX⟩ := _root_.GlobalTheory.RowsOrb.ub_equiv_model D X u W HW hEmb
  have hlat := GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart D X u W e heX
  set M₀ := GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ₀) with hM₀
  obtain ⟨hψ, hgen, horb⟩ := _root_.GlobalTheory.Mass.Transp.orbSum_img D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he φ hφ M₀
  obtain ⟨hcm, -, -, -, hf, -, -, -, -, -, -, -, hTu⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hS
  obtain ⟨hTp, hsp⟩ := hTu u
  have hl0 := _root_.GlobalTheory.TypeAsm.lat0C D large₂ X Y u hS W HW hEmb Λ₀ hΛ₀
  rw [hlat Λ₀] at hl0
  obtain ⟨hM₀i, hM₀d⟩ := _root_.GlobalTheory.Mass.Transp.discModule_transport D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he M₀ _ hl0.1 hl0.2
  have hbs : (GlobalTheory.RowsOrb.hb X).IsSymm := ⟨fun a b => (VS D).herm.eq (a : (VS D).V) (b : (VS D).V)⟩
  have hz : GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.zb X u) = -((Tu D u : ℕ) : D.host.E) := X.zu_norm u
  have hrm := GlobalTheory.Mass.RowMean.main D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) hcm hbs (Tu D u)
    (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.Ub X u) hTp hsp hz rfl (_root_.GlobalTheory.RowsOrb.pd_hU D X u) M₀ hM₀i hM₀d
    (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  simp only [hlat, ← hM₀, hgen]
  rw [horb, ← hf]
  refine Eq.trans ?_ hrm
  obtain ⟨hst, hinv⟩ := _root_.GlobalTheory.RowsOrb.StabSet.main D X u M₀ (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  have hinj : ∀ a ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      ∀ b ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      GlobalTheory.RowsOrb.Lmap X u a = GlobalTheory.RowsOrb.Lmap X u b → a = b := by
    intro a ha b hb hab
    exact _root_.GlobalTheory.RowsOrb.rows_eq_of_conj D large₂ X Y u hS a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 1 ((one_smul (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u a)).trans hab)
  refine Eq.trans ?_ (GlobalTheory.Mass.orbSum_eq_sum_reps (GlobalTheory.RowsOrb.Gz X u) (Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X))
    {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} (fun L => φ (GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L))) hst (fun g L => hinv g L)
    (((Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀)).image (GlobalTheory.RowsOrb.Lmap X u)) ?_ ?_).symm
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    congr 1
    show ENNReal.ofReal ((Nat.card (autLz D (X.Fu u) Λ) : ℝ)⁻¹) = _
    rw [_root_.GlobalTheory.RowsOrb.card_autLz D large₂ X Y u hS Λ (Finset.mem_filter.1 hΛ).1, cardE]
  · intro L hL
    obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hΛr, hΛg⟩ := Finset.mem_filter.1 hΛ
    obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.RowsOrb.Basic.lmap_basic D large₂ X Y u hS Λ hΛr
    exact ⟨h1, h2, h3, hΛg⟩
  · intro L hL
    obtain ⟨Λ, hΛ, g, hg⟩ := _root_.GlobalTheory.RowsOrb.exists_row_of_unimod D large₂ X Y u hS L hL.1 hL.2.1 hL.2.2.1
    refine ⟨GlobalTheory.RowsOrb.Lmap X u Λ, ⟨Finset.mem_image.2 ⟨Λ, Finset.mem_filter.2 ⟨hΛ, ?_⟩, rfl⟩, g, hg⟩, ?_⟩
    · have := hst g⁻¹ L hL
      erw [← hg, inv_smul_smul] at this
      exact this.2.2.2
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.1 hy
      congr 1
      exact _root_.GlobalTheory.RowsOrb.rows_eq_of_conj D large₂ X Y u hS Λ' (Finset.mem_filter.1 hΛ').1 Λ hΛ (g⁻¹ * g') (by erw [mul_smul, hg', ← hg, inv_smul_smul])

end GlobalTheory.RowsOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLine
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineMass

theorem sum_encard_fibre_le {α ι : Type*} (S : Set α) (f : α → ι) (s : Finset ι) :
    ∑ n ∈ s, (S ∩ {a | f a = n}).encard ≤ (S ∩ {a | f a ∈ s}).encard := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : S ∩ {x | f x ∈ insert a s} = (S ∩ {x | f x = a}) ∪ (S ∩ {x | f x ∈ s}) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union]
      tauto
    rw [e, Set.encard_union_eq]
    · gcongr
    · rw [Set.disjoint_left]
      rintro x ⟨-, h1⟩ ⟨-, h2⟩
      exact ha (by rw [← show f x = a from h1]; exact h2)

theorem orbSum_finsetSum {G α ι : Type} [Group G] [MulAction G α] (X : Set α) (N : ι → α → ℝ≥0∞)
    (s : Finset ι) : ∑ n ∈ s, orbSum G X (N n) = orbSum G X (fun x => ∑ n ∈ s, N n x) := by
  obtain ⟨-, hconst, -, -, hadd⟩ := _root_.GlobalTheory.Mass.OrbMono.main G α
  induction s using Finset.induction_on with
  | empty => simp [hconst]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hadd, ih]

theorem sub_count {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h1 : Module.finrank K V = 1)
    (M : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (X : ℕ) :
    {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N ≠ 0 ∧ idxN M N ≤ X}.encard ≤
      {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.encard := by
  by_cases hbot : M = ⊥
  · subst M
    by_cases hX : X = 0
    · subst X
      simp
    · have htop : (⊤ : Ideal (𝓞 K)) ∈ {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X} := by
        simp [Nat.one_le_iff_ne_zero.mpr hX]
      calc
        _ ≤ 1 := by
          apply Set.encard_le_one_iff.mpr
          intro a b ha hb
          exact (le_bot_iff.mp ha.1).trans (le_bot_iff.mp hb.1).symm
        _ ≤ _ := Set.one_le_encard_iff_nonempty.mpr ⟨⊤, htop⟩
  obtain ⟨e⟩ : Nonempty (V ≃ₗ[K] K) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (by simp [h1])
  let e' : V →ₗ[𝓞 K] K := (e : V →ₗ[K] K).restrictScalars (𝓞 K)
  obtain ⟨a, ha, hint⟩ : IsFractional (nonZeroDivisors (𝓞 K)) (M.map e') :=
    FractionalIdeal.isFractional_of_fg (hM.fg.map e')
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  let ψ : V →ₗ[𝓞 K] K := a • e'
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : a • e x = 0 := hx
    rw [smul_eq_zero] at this
    exact e.map_eq_zero_iff.1 (this.resolve_left ha0)
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective (𝓞 K) K
  let J : Submodule (𝓞 K) V → Ideal (𝓞 K) := fun N => (N.map ψ).comap ι
  have hJ : ∀ N ≤ M, Submodule.map ι (J N) = N.map ψ := by
    intro N hN
    refine Submodule.map_comap_eq_of_le ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hint (e' x) ⟨x, hN hx, rfl⟩
    exact ⟨y, hy⟩
  have hle : ∀ N ≤ M, J N ≤ J M := fun N hN => Submodule.comap_mono (Submodule.map_mono hN)
  have hidx : ∀ N ≤ M, idxN M N * Ideal.absNorm (J M) = Ideal.absNorm (J N) := by
    intro N hN
    have e1 : idxN M N = (J N).toAddSubgroup.relIndex (J M).toAddSubgroup := by
      unfold idxN
      rw [← AddSubgroup.relIndex_map_map_of_injective (f := ψ.toAddMonoidHom) _ _ hψ,
        ← AddSubgroup.relIndex_map_map_of_injective (f := ι.toAddMonoidHom) (J N).toAddSubgroup _ hι]
      change (N.map ψ).toAddSubgroup.relIndex (M.map ψ).toAddSubgroup =
        (Submodule.map ι (J N)).toAddSubgroup.relIndex (Submodule.map ι (J M)).toAddSubgroup
      rw [hJ N hN, hJ M le_rfl]
    rw [e1]
    simpa only [Ideal.absNorm_eq_index] using
      AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono (hle N hN))
  have hJM : J M ≠ ⊥ := by
    intro h0
    have h2 := hJ M le_rfl
    rw [h0, Submodule.map_bot] at h2
    have h3 : M = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : ψ x ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ ⟨x, hx, rfl⟩
      exact (injective_iff_map_eq_zero ψ).1 hψ x this
    exact hbot h3
  have hq : ∀ N : Submodule (𝓞 K) V, ∃ I : Ideal (𝓞 K), N ≤ M → J N = J M * I := by
    intro N
    by_cases hN : N ≤ M
    · obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 (hle N hN)
      exact ⟨I, fun _ => hI⟩
    · exact ⟨⊥, fun h => (hN h).elim⟩
  choose q hq using hq
  refine Set.encard_le_encard_of_injOn (f := q) ?_ ?_
  · rintro N ⟨hN, h0, hX⟩
    have h2 := hidx N hN
    rw [hq N hN, map_mul, mul_comm] at h2
    have h3 := Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hJM)) h2
    refine ⟨fun hb => h0 (by rw [h3, hb, Ideal.absNorm_bot]), ?_⟩
    rw [← h3]
    exact_mod_cast hX
  · rintro N ⟨hN, -⟩ N' ⟨hN', -⟩ hqq
    apply Submodule.map_injective_of_injective hψ
    rw [← hJ N hN, ← hJ N' hN', hq N hN, hq N' hN', hqq]

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' I hs' hI X hX
  have hnd := SpaceMass.nondeg_of_PD h hp
  have hp' := SpaceMass.PD_of_ortho h' hK I _ hI
  have hnd' := SpaceMass.nondeg_of_PD h' hp'
  by_cases hE : ∃ M₁ : Submodule (𝓞 K) V, IsIntLat h M₁
  swap
  · refine le_of_eq_of_le (Finset.sum_eq_zero fun n _ => ?_) zero_le
    unfold orbMass orbSum
    exact ENNReal.tsum_eq_zero.2 fun q => (hE ⟨_, q.2.1⟩).elim
  obtain ⟨M₁, hM₁⟩ := hE
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, -⟩ := hex M₁ hM₁
  obtain ⟨c, hc⟩ := hMM K hK 1 le_rfl
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  have hm₀ : mass h M₀ = c := by
    have : lamMax h M₀ = 1 := by
      unfold lamMax
      refine finprod_mem_of_eqOn_one fun P _ => ?_
      have : (qIn P : ℝ) + 1 ≠ 0 := by positivity
      simp only [hj, pow_one, sub_neg_eq_add, Pi.one_apply]
      exact div_self this
    rw [hc V h hs hp hj M₀ hM₀, this, mul_one]
  obtain ⟨mono, hconst, -⟩ := _root_.GlobalTheory.Mass.OrbMono.main (isom h) (Submodule (𝓞 K) V)
  have key : ∀ n : ℕ, orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbSum (isom h) (genus h M₀)
      (fun M' => ((({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard : ℕ∞) :
        ℝ≥0∞)) := by
    intro n
    have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
      intro g M hM
      have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M
        (SpaceMass.mem_genus_self h M hM.1.1)
      have h2 := (hdisc M hM.1).2.2.2.1 _ h1
      exact ⟨h2.1, h2.2.trans hM.2⟩
    let Y : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
      {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
    have hXst : Stable (isom h) Y := by
      rintro g p ⟨h1, h2, h3⟩
      exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
    have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
      (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
    have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ Y (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
      (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
    have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) Y := by
      rw [f1]
      refine mono _ _ _ _ subset_rfl fun M hM => ?_
      obtain ⟨M', hM', hle⟩ := hex M hM.1
      have hne : (Y ∩ Prod.fst ⁻¹' {M}).Nonempty :=
        ⟨(M, M'), ⟨hM, (_root_.GlobalTheory.Mass.MaxGenus.main K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
      have := Set.one_le_encard_iff_nonempty.2 hne
      exact_mod_cast this
    refine s1.trans ?_
    rw [f2]
    refine mono _ _ _ _ subset_rfl fun M' _ => ?_
    have : (Y ∩ Prod.snd ⁻¹' {M'}).encard ≤
        ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩ {N | discN h N = n}).encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        exact ⟨⟨h1.1, h3⟩, h1.2⟩
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine (Finset.sum_le_sum fun n _ => key n).trans ?_
  rw [orbSum_finsetSum]
  obtain ⟨hIfin, hIcard⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K (X : ℝ) (by exact_mod_cast hX)
  have hexp : 1 + Real.logb 2 (Module.finrank ℚ K) = 2 + Real.logb 2 (fDeg K) := by
    have := hK.1
    have h2 : Module.finrank ℚ K = 2 * fDeg K := by
      unfold fDeg
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.finrank,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have h3 : (fDeg K : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := InfinitePlace K)).ne'
    rw [h2]
    push_cast
    rw [Real.logb_mul two_ne_zero h3, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [hexp] at hIcard
  rw [hcI, ← hm₀, mul_comm, ENNReal.ofReal_mul (by positivity), hmass, ← hconst]
  refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
  have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
  have a1 := sum_encard_fibre_le {N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} (fun N => discN h N)
    (Finset.Icc 1 (X ^ 2))
  have a2 : ({N : Submodule (𝓞 K) V | IsIntLat h N ∧ N ≤ M'} ∩
      {N | discN h N ∈ Finset.Icc 1 (X ^ 2)}).encard ≤
      {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N ≠ 0 ∧ idxN M' N ≤ X}.encard := by
    refine Set.encard_le_encard ?_
    rintro N ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨h4, h5⟩ := (hdisc N h1).2.2.1 M' hM''.1 h2
    refine ⟨h2, h4, ?_⟩
    have h6 : discN h N ≤ X ^ 2 := (Finset.mem_Icc.1 h3).2
    have h7 := Nat.pos_of_ne_zero (hdisc M' hM''.1).1
    have h8 : idxN M' N ^ 2 ≤ X ^ 2 := (Nat.le_mul_of_pos_left _ h7).trans (h5 ▸ h6)
    exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h8
  have a3 := (a1.trans a2).trans (sub_count hj M' hM'.1.toIsLattice X)
  rw [← hIfin.cast_ncard_eq] at a3
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hIcard)
  rw [ENNReal.ofReal_natCast]
  have a4 := ENat.toENNReal_le.2 a3
  rw [ENat.toENNReal_coe] at a4
  refine le_trans (le_of_eq ?_) a4
  exact (map_sum ENat.toENNRealRingHom _ _).symm

end GlobalTheory.Mass.LineMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSumsStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_rationalClasses_eq_prod_localSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  first | exact @GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | exact GlobalTheory.GenMass.tsum_classes_eq_prod_locSums | (intros; apply GlobalTheory.GenMass.tsum_classes_eq_prod_locSums <;> assumption)
end

