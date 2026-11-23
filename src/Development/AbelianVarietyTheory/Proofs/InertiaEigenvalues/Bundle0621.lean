module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Formalism.AdmissibleDesigns.Bundle0001
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Polynomial Cardinal

namespace GlobalTheory.LocGL

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_not_isUnit_sub [Nontrivial V] (hV : Module.rank ℂ V ≤ ℵ₀) (T : Module.End ℂ V) :
    ∃ c : ℂ, ¬ IsUnit (T - algebraMap ℂ _ c) := by
  first
  | exact @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub
  | (apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonUnitShift.exists_not_isUnit_sub ..)

variable {G : Type} [Group G]

theorem exists_eq_smul_of_rank_le {π : Representation ℂ G V} (hi : π.IsIrreducible) (hV : Module.rank ℂ V ≤ ℵ₀)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨c, hc⟩ := exists_not_isUnit_sub hV T.toLinearMap
  let S : π.IntertwiningMap π := T - c • .id π
  rcases Representation.IsIrreducible.bijective_or_eq_zero S with h | h
  · exact absurd ((Module.End.isUnit_iff _).2 h) hc
  · exact ⟨c, fun v => sub_eq_zero.1 (congrArg (fun f : π.IntertwiningMap π => f v) h)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

theorem countable_orbit {π : Representation ℂ G V} (hs : IsSmooth π) (v : V) : (Set.range fun g => π g v).Countable := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense G
  refine (hD.image fun g => π g v).mono ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ ((hs v).preimage (continuous_const_mul g⁻¹)) ⟨g, by simp⟩
  refine ⟨x, hxD, ?_⟩
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem rank_le_aleph0_of_isIrreducible {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Module.rank ℂ V ≤ ℵ₀ := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have ht : Submodule.span ℂ (Set.range fun g => π g v) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨f, rfl⟩ := orbitMap_surjective hi hv w
    show π.asAlgebraHom f v ∈ _
    induction f using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span ⟨g, by simp⟩
    | add a b ha hb => rw [map_add (f := _), LinearMap.add_apply]; exact add_mem (ha trivial) (hb trivial)
    | smul c a ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ (ha trivial)
  rw [← rank_top, ← ht]
  exact (rank_span_le _).trans (le_aleph0_iff_set_countable.2 (countable_orbit hs v))

theorem exists_eq_smul_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  exists_eq_smul_of_rank_le hi (rank_le_aleph0_of_isIrreducible hs hi) T

theorem algebraMap_intertwiningMap_bijective_of_isSmooth {π : Representation ℂ G V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨fun a b h => smul_left_injective ℂ hv (congrArg (fun f : π.IntertwiningMap π => f v) h), fun T => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_isSmooth hs hi T
  exact ⟨c, by ext w; exact (hc w).symm⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


variable (k n) in
theorem secondCountableTopology_GL : SecondCountableTopology (GL n k) := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  have : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  have : SecondCountableTopology (Matrix n n k)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem schur_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (T : π.IntertwiningMap π) : ∃ c : ℂ, ∀ v, T v = c • v :=
  haveI := secondCountableTopology_GL k n
  exists_eq_smul_of_isSmooth hs hi T

theorem algebraMap_intertwiningMap_bijective_GL {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    (hi : π.IsIrreducible) : Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) :=
  haveI := secondCountableTopology_GL k n
  algebraMap_intertwiningMap_bijective_of_isSmooth hs hi


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_glScalar : Continuous (GeneralLinearGroup.scalar n : kˣ → GL n k) := by
  refine Units.continuous_map (f := (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom) ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem isSmoothChar_of_hasCentralChar [Nontrivial V] {π : Representation ℂ (GL n k) V} (hs : IsSmooth π)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : IsSmoothChar ω := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (ω.ker : Set kˣ) = GeneralLinearGroup.scalar n ⁻¹' {g | π g v = v} := by
    ext z
    show ω z = 1 ↔ π (GeneralLinearGroup.scalar n z) v = v
    rw [h]
    exact ⟨fun e => by simp [e], fun e => Units.ext (smul_left_injective ℂ hv (e.trans (one_smul _ _).symm))⟩
  show IsOpen (ω.ker : Set kˣ)
  rw [this]
  exact (hs v).preimage continuous_glScalar

theorem exists_smooth_hasCentralChar {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) :
    ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω := by
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  have key : ∀ z : kˣ, ∃ c : ℂ, ∀ w, π (GeneralLinearGroup.scalar n z) w = c • w := fun z =>
    schur_GL hs hi ⟨π (GeneralLinearGroup.scalar n z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]⟩
  choose c hc using key
  have : ∃ ω, HasCentralChar π ω := by
    refine ⟨MonoidHom.toHomUnits ⟨⟨c, smul_left_injective ℂ hw₀ ?_⟩, fun x y => smul_left_injective ℂ hw₀ ?_⟩, hc⟩
    · simp [← hc]
    · simp only [← hc, mul_smul, map_mul, Module.End.mul_apply]
  obtain ⟨ω, hω⟩ := this
  exact ⟨ω, isSmoothChar_of_hasCentralChar hs hω, hω⟩

section CentralChar

variable {R : Type} [CommRing R]

theorem centralChar_unique [Nontrivial V] {π : Representation ℂ (GL n R) V} {ω ω' : Rˣ →* ℂˣ}
    (h : HasCentralChar π ω) (h' : HasCentralChar π ω') : ω = ω' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hv ((h z v).symm.trans (h' z v)))

theorem hasCentralChar_of_equiv {π : Representation ℂ (GL n R) V} {σ : Representation ℂ (GL n R) W} (φ : π.Equiv σ)
    {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := fun z w => by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ _ (φ.toIntertwiningMap v) = _ • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem hasCentralChar_twist {π : Representation ℂ (GL n R) V} {ω : Rˣ →* ℂˣ} (h : HasCentralChar π ω)
    (χ : Rˣ →* ℂˣ) : HasCentralChar (twist π (detChar n χ)) (ω * χ ^ Fintype.card n) := fun z v => by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar n z) = z ^ Fintype.card n := by
    ext; simp [GeneralLinearGroup.scalar]
  rw [twist_apply, h, detChar_apply, this, smul_smul, mul_comm]
  simp

end CentralChar

namespace IrrGL

theorem pow_eq_of_tw_eq {x : IrrGL (k := k)} {χ ψ : kˣ →* ℂˣ} {hχ : IsSmoothChar χ} {hψ : IsSmoothChar ψ}
    (h : x.tw χ hχ = x.tw ψ hψ) : χ ^ x.1 = ψ ^ x.1 := by
  have := Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h)
  have h1 := centralChar_unique (V := x.2.rep.V) (hasCentralChar_of_equiv φ (hasCentralChar_twist hω χ)) (hasCentralChar_twist hω ψ)
  simpa using h1

theorem nu_ofReal_inj {x : IrrGL (k := k)} (hx : 0 < x.1) {s t : ℝ} : x.nu s = x.nu t ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := pow_eq_of_tw_eq h
  have h2 : ∀ (s : ℂ) (m : ℕ), absPow k s ^ m = absPow k (m * s) := fun s m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, ← absPow_add]; congr 1; push_cast; ring
  rw [h2, h2] at h1
  have h3 : absPow k ((x.1 * (s - t) : ℝ) : ℂ) = 1 := by
    rw [show ((x.1 * (s - t) : ℝ) : ℂ) = x.1 * s + -(x.1 * t) by push_cast; ring, absPow_add, absPow_neg, h1,
      mul_inv_cancel]
  exact sub_eq_zero.1 ((mul_eq_zero.1 (absPow_ofReal_eq_one.1 h3)).resolve_left (Nat.cast_ne_zero.2 hx.ne'))

theorem nu_intCast_inj {x : IrrGL (k := k)} (hx : 0 < x.1) {a b : ℤ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

theorem nu_natCast_inj {x : IrrGL (k := k)} (hx : 0 < x.1) {a b : ℕ} : x.nu a = x.nu b ↔ a = b := by
  simpa using nu_ofReal_inj hx (s := a) (t := b)

theorem nu_ofReal_eq_self {x : IrrGL (k := k)} (hx : 0 < x.1) {s : ℝ} : x.nu s = x ↔ s = 0 := by
  simpa using nu_ofReal_inj hx (s := s) (t := 0)

end IrrGL

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem term_injective (Δ : Segment k) : Function.Injective Δ.term := fun _ _ h =>
  Fin.ext ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 h)

theorem nodup_ms (Δ : Segment k) : Δ.ms.Nodup := Finset.univ.nodup.map Δ.term_injective

theorem carrier_injective : Function.Injective (carrier : Segment k → Set (IrrGL (k := k))) := fun Δ Δ' h => by
  have key : ∀ D : Segment k, D.first ∈ D.carrier := fun D => mem_carrier.2 ⟨0, D.len_pos, by simp⟩
  obtain ⟨a, -, ha⟩ := mem_carrier.1 (h ▸ key Δ)
  obtain ⟨b, -, hb⟩ := mem_carrier.1 (h.symm ▸ key Δ')
  have h0 : b + a = 0 := (IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by
    rw [Nat.cast_add, ← IrrGL.nu_nu, hb, ha, Nat.cast_zero, IrrGL.nu_zero])
  obtain rfl : b = 0 := by omega
  refine ext_first (by simpa using hb) ?_
  rw [← card_ms, ← card_ms, (Multiset.Nodup.ext Δ.nodup_ms Δ'.nodup_ms).2 fun x => by rw [mem_ms, mem_ms, h]]

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem schur_and_segments (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
      IsSmooth π → π.IsIrreducible → Function.Bijective (algebraMap ℂ (π.IntertwiningMap π)) ∧
        ∃ ω, IsSmoothChar ω ∧ HasCentralChar π ω) ∧
    (∀ x : IrrGL (k := k), 0 < x.1 → ∀ s t : ℝ, x.nu s = x.nu t ↔ s = t) ∧
    (∀ Δ : Segment k, Function.Injective Δ.term ∧ Δ.ms.Nodup) ∧
    Function.Injective (Segment.carrier : Segment k → Set (IrrGL (k := k))) :=
  ⟨fun _ _ _ _ _ _ _ hs hi => ⟨algebraMap_intertwiningMap_bijective_GL hs hi, exists_smooth_hasCentralChar hs hi⟩,
    fun _ hx _ _ => IrrGL.nu_ofReal_inj hx, fun Δ => ⟨Δ.term_injective, Δ.nodup_ms⟩, Segment.carrier_injective⟩

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BKaRows

theorem bkaAll_of_hypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilator_above_l D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D) _root_.GlobalTheory.LitGood.litGoodO

end GlobalTheory.BKaRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂

theorem aux_of_blochKato_tateDuality_eulerChar₂ :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ D : D7, LocalSituation.Conclusion5 D :=
  GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato

end GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.AdmBK

theorem litGoodO_all : LitGoodO := fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

theorem blochKato_dimFormula_all_finiteExt_coeffField (D : D7) : TruncatedSeriesCountingBounds.adm8 D := fun l _ K LL _ =>
  GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL

theorem admBK_loc_of_blochKato_tateDuality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilators_of D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D)
    (fun l _ K => GlobalTheory.TateTop.tateH2_of_duality_loc hTD l (D.loc l) K) (blochKato_dimFormula_all_finiteExt_coeffField D) litGoodO_all

end GlobalTheory.AdmBK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresOfFiniteIndexSubLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classPres_of_finiteIndex_subLevel : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι S σ ρ J χ) (J' : Subgroup G), J' ≤ J → (J'.subgroupOf J).FiniteIndex → ∀ χ' : J' →* ℂˣ, (∀ k, ∃ a : K, σ a = ((χ' k : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) → ∃ (Cl : Type) (fC : Fintype Cl) (π : Cl → S.Cl) (k : Cl → J) (Gam : Cl → Type) (gG : ∀ c, Group (Gam c)) (fG : ∀ c, Fintype (Gam c)) (ρ' : ∀ c, Gam c →* Module.End K S.V) (P' : Bridge.ClassPres ι ({ S with Cl := Cl, finCl := fC, Gam := Gam, grpGam := gG, finGam := fG, ρ := ρ', Nab := fun c => S.Nab (π c), Del := fun c => S.Del (π c) } : CSD K) σ ρ J' χ'), (∀ c : Cl, P'.y c = P.y (π c) * (k c : G)) ∧ P'.coef = P.coef := by
  first | exact @GlobalTheory.classPres_subLevel | exact GlobalTheory.classPres_subLevel | (intros; apply GlobalTheory.classPres_subLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FromMat

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {n : Type} [Fintype n] [DecidableEq n]

def matRep (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) :=
  MonoidHom.toHomUnits
    ((((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).mapMatrix : Matrix n n ℚ_[l] →+* Matrix n n ↥(MaximalUnramifiedExtension l)) :
        Matrix n n ℚ_[l] →* Matrix n n ↥(MaximalUnramifiedExtension l)).comp
      (((LinearMap.toMatrixAlgEquiv b : (V →ₗ[ℚ_[l]] V) ≃ₐ[ℚ_[l]] Matrix n n ℚ_[l]) :
        (V →ₗ[ℚ_[l]] V) →* Matrix n n ℚ_[l]).comp ρ))

theorem matRep_apply (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (i j : n) :
    (matRep b ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (b.repr (ρ g (b j)) i) := by
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply]

theorem toMatrix_map_apply (b : Module.Basis n ℚ_[l] V) (f : V →ₗ[ℚ_[l]] V) {A : Type} [Semiring A] [Algebra ℚ_[l] A]
    (i j : n) : (LinearMap.toMatrix b b f).map (algebraMap ℚ_[l] A) i j = algebraMap ℚ_[l] A (b.repr (f (b j)) i) := by
  simp [LinearMap.toMatrix_apply]

end GlobalTheory.PMon.FromMat

namespace GlobalTheory.PMon.FromMat

open GlobalTheory.PMon.Inhab

theorem deRhamPotSemistable_of_matThm : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  intro hM l _ P AI hT K V _ _ _ _ _ ρ hc hDR
  obtain ⟨T⟩ := hT
  let b := Module.finBasis ℚ_[l] V
  have hR : IsRat 1 (matRep b ρ) := by
    refine ⟨one_pos, fun c hc' => ?_, fun g i j => ?_, fun i j => ?_⟩
    · obtain ⟨q, rfl⟩ := fixed_frob P c (by rwa [fr_one] at hc')
      exact K.1.algebraMap_mem q
    · rw [matRep_apply, fr_q]
    · simp only [matRep_apply]
      have h1 : Continuous fun g : ↥(GK K) => b.coord i (ρ g (b j)) :=
        (IsModuleTopology.continuous_of_linearMap (R := ℚ_[l]) (b.coord i)).comp (hc (b j))
      exact (continuous_algebraMap ℚ_[l] (Om l)).comp h1
  have hD : AdmDR P (matRep b ρ) := by
    intro m
    obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.DRMat.exists_period_matrix_of_isDR l P AI T _ K V b ρ hDR
    refine ⟨Q, fun g => ?_⟩
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    rw [matD, Matrix.map_apply, matRep_apply, fr_q, kd_alg, toMatrix_map_apply]
  obtain ⟨K', hK, Q, hQ⟩ := hM l P AI T _ K 1 (matRep b ρ) hR hD
  have hS : IsSst P (resTo ρ hK) := by
    refine _root_.GlobalTheory.PMon.isSst_of_periodMatrix l P AI T _ K' V b (resTo ρ hK) Q fun g => ?_
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [matRep_apply, LinearMap.toMatrix_apply, ks, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      Polynomial.algebraMap_apply]
    rfl
  exact _root_.GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K' hK V ρ hS

end GlobalTheory.PMon.FromMat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_frame_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F hDR
  obtain ⟨P, r, hP⟩ := GlobalTheory.T.exists_breuilKisin_basis_limit_lattice l K bk τ hτ d N ρ tw (fun n => (F n).toPre)
  obtain ⟨F₀, hF₀⟩ := _root_.GlobalTheory.BKLim.frame_of_links l K bk d N ρ tw F P r hP
  have hL : ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
    subst hF₀
    exact hP
  exact ⟨F₀, GlobalTheory.T.isDR_of_links' l K bk d N ρ tw F F₀ r hL hDR,
    fun hCr => GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower l K bk d N ρ tw F F₀ r hL hCr, r, hL⟩

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedVectorFiltrationJumpBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  first | exact @GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | exact GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector | (intros; apply GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoFin

theorem finite_continuous_cocycles_localGaloisRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    (∀ v, Continuous fun g => ρ g v) → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  obtain ⟨ρ', m, hc', hD⟩ := _root_.GlobalTheory.DualTwist.exists_dual1 l P K V ρ hc
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] :=
    { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hc' }
  have hH := (GlobalTheory.T.finrank_H1_dual_pair CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler l P K ℚ_[l] ℤ_[l]
    GlobalTheory.Published.BlochKato.goodO_padicInt A A' m hD).1
  exact GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hH

end GlobalTheory.HyodoFin
end

