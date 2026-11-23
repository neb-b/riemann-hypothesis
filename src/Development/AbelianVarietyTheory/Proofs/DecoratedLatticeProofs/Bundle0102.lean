module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LastSteps

variable {D : D7}

theorem flagN_rank_zero {S S₀ : HSp D} (d : HypDec S S₀ 0) {n : GA D S} (hn : n ∈ flagN d) : n = 1 := by
  have hle : flagN d ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, hg⟩
    have hcol : ∀ i : Fin S.rank, ∀ k, subOne S g k i = 0 := by
      intro i k
      obtain ⟨a, ha⟩ := hg (Pi.single i 1) (Subsingleton.elim _ _)
      have h1 := congrFun ha k
      have hr : ratV (D := D) (Pi.single i (1 : D.host.E)) = Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [ratV, Pi.single_apply, h]
      rw [hr] at h1
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
    have hm : (matHom S g).1 = 1 := by
      have : subOne S g = 0 := by ext k i; exact hcol i k
      simpa [subOne, sub_eq_zero] using this
    have : matHom S g = 1 := Units.ext hm
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  exact Subgroup.mem_bot.1 (hle hn)

theorem per_rank_zero (B : BesLev D 0) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ f = ∫ h in B.vA.𝓕, φ h * f (embA B.d B.o h) ∂B.vA.μ := by
  unfold BesLev.per besPer
  congr 1; funext h
  have e : ∀ n : flagN B.d, besFun ψ 1 B.d B.o B.ζ φ f h n = φ h * f (embA B.d B.o h) := by
    intro n
    have hp : ∀ m, psiBes ψ B.d 1 (vecB B.o B.ζ) m = 1 := fun m => by
      simp [psiBes, simpleSum, upSum, dotProduct, psiE]
    rw [besFun, flagN_rank_zero B.d n.2, one_mul, hp, star_one, mul_one]
  simp_rw [e]
  rw [setIntegral_const]
  simp [Measure.real, B.vN.unit.2.2]

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem swap_bdd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] (μ : Measure X) (ν : Measure Y)
    (s : Set X) (t : Set Y) (hs : μ s < ⊤) (ht : ν t < ⊤) (f : X → Y → ℂ) (hf : Continuous (Function.uncurry f))
    (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C) :
    ∫ x in s, ∫ y in t, f x y ∂ν ∂μ = ∫ y in t, ∫ x in s, f x y ∂μ ∂ν := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  have : IsFiniteMeasure (ν.restrict t) := isFiniteMeasure_restrict.2 ht.ne
  exact integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun p => hC p.1 p.2))

theorem om_bdd {S T A T₀ : HSp D} {χ χ' : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χ χ' om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hA : CoCpt A) (hT : CoCpt T₀) (a : GA D A →* GA D S)
    (b : GA D T₀ →* GA D T) (ha : Continuous a) (hb : Continuous b) (ha' : ∀ γ ∈ GQ A, a γ ∈ GQ S)
    (hb' : ∀ γ ∈ GQ T₀, b γ ∈ GQ T) :
    Continuous (fun p : GA D A × GA D T₀ => om (a p.1, b p.2) f 0) ∧ ∃ C : ℝ, ∀ x y, ‖om (a x, b y) f 0‖ ≤ C := by
  have t0 := EvalCont.tame_om hom hf hA hT a b ha hb ha' hb'
  refine ⟨?_, ?_⟩
  · have := t0.1.comp ((continuous_const (y := (1 : GA D T))).prodMk
      (continuous_id.prodMk (continuous_const (y := (0 : WO S T)))))
    simpa [Function.comp_def] using this
  · obtain ⟨C, hC⟩ := t0.2 1
    exact ⟨C, fun x y => by simpa using hC.self_of_nhds ((x, y), 0)⟩

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps

open EvalCont

theorem bound_mul {x y : ℂ} {C C' : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C') : ‖x * y‖ ≤ C * C' := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

theorem triple {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology X]
    [SecondCountableTopology Y] [SecondCountableTopology Z] (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    (s : Set X) (u : Set Y) (w : Set Z) (hs : μ s < ⊤) (hu : ν u < ⊤) (hw : κ w < ⊤)
    (φ : X → ℂ) (F : Z → ℂ) (a : X → Y → ℂ) (b : Y → Z → ℂ) (hφ : Continuous φ) (hF : Continuous F)
    (ha : Continuous fun p : X × Y => a p.1 p.2) (hb : Continuous fun p : Y × Z => b p.1 p.2)
    {Cφ CF Ca Cb : ℝ} (hCφ : ∀ x, ‖φ x‖ ≤ Cφ) (hCF : ∀ z, ‖F z‖ ≤ CF) (hCa : ∀ x y, ‖a x y‖ ≤ Ca)
    (hCb : ∀ y z, ‖b y z‖ ≤ Cb) :
    ∫ x in s, φ x * ∫ y in u, a x y * ∫ z in w, b y z * F z ∂κ ∂ν ∂μ =
      ∫ z in w, F z * ∫ y in u, b y z * ∫ x in s, φ x * a x y ∂μ ∂ν ∂κ := by
  have : FirstCountableTopology Y := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  set c : Y → ℂ := fun y => ∫ z in w, b y z * F z ∂κ with hc
  set m : Y → ℂ := fun y => ∫ x in s, φ x * a x y ∂μ with hm
  have hcC : Continuous c :=
    Tame.continuous_integral _ _ hw (F := fun y z => b y z * F z) (tame_of_bounded (C := Cb * CF)
      (hb.mul (hF.comp continuous_snd)) fun y z => bound_mul (hCb y z) (hCF z))
  have hcB : ∀ y, ‖c y‖ ≤ Cb * CF * κ.real w := fun y =>
    norm_setIntegral_le_of_norm_le_const hw fun z _ => bound_mul (hCb y z) (hCF z)
  have hmC : Continuous m :=
    Tame.continuous_integral _ _ hs (F := fun y x => φ x * a x y) (tame_of_bounded (C := Cφ * Ca)
      ((hφ.comp continuous_snd).mul (ha.comp continuous_swap)) fun y x => bound_mul (hCφ x) (hCa x y))
  have hmB : ∀ y, ‖m y‖ ≤ Cφ * Ca * μ.real s := fun y =>
    norm_setIntegral_le_of_norm_le_const hs fun x _ => bound_mul (hCφ x) (hCa x y)
  calc ∫ x in s, φ x * ∫ y in u, a x y * c y ∂ν ∂μ
      = ∫ x in s, ∫ y in u, φ x * (a x y * c y) ∂ν ∂μ := by
        congr 1; funext x; rw [integral_const_mul]
    _ = ∫ y in u, ∫ x in s, φ x * (a x y * c y) ∂μ ∂ν := by
        refine swap_bdd _ _ _ _ hs hu _ ?_ (Cφ * (Ca * (Cb * CF * κ.real w))) fun x y =>
          bound_mul (hCφ x) (bound_mul (hCa x y) (hcB y))
        exact (hφ.comp continuous_fst).mul (ha.mul (hcC.comp continuous_snd))
    _ = ∫ y in u, m y * c y ∂ν := by
        congr 1; funext y; rw [hm]; dsimp only; rw [← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ y in u, ∫ z in w, m y * (b y z * F z) ∂κ ∂ν := by
        congr 1; funext y; rw [hc]; dsimp only; rw [integral_const_mul]
    _ = ∫ z in w, ∫ y in u, m y * (b y z * F z) ∂ν ∂κ := by
        refine swap_bdd _ _ _ _ hu hw _ ?_ (Cφ * Ca * μ.real s * (Cb * CF)) fun y z =>
          bound_mul (hmB y) (bound_mul (hCb y z) (hCF z))
        exact (hmC.comp continuous_fst).mul (hb.mul (hF.comp continuous_snd))
    _ = ∫ z in w, F z * ∫ y in u, b y z * m y ∂ν ∂κ := by
        congr 1; funext z; rw [← integral_const_mul]; congr 1; funext y; ring

end GlobalTheory.Unf.LastSteps

namespace GlobalTheory.Unf.LastSteps


open EvalCont in
theorem lastLaw : ∀ D : D7, LastLaw D := by
  intro D ψ T B t φ Φ₁ Φ₂ F hφ hF hΦ₁ hΦ₂
  obtain ⟨-, iA2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨-, iS2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D t.J.W
  obtain ⟨-, iT2, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (GA D t.J.W) := ⟨rfl⟩
  have : BorelSpace (GA D T) := ⟨rfl⟩
  obtain ⟨Cφ, hCφ⟩ := bounded_of_contAut B.cpt hφ
  obtain ⟨CF, hCF⟩ := bounded_of_contAut t.cptT hF
  obtain ⟨ha, Ca, hCa⟩ := om_bdd t.s.weil hΦ₁ B.cpt t.cptS (embA B.d B.o) (MonoidHom.id _)
    (B.d.continuous_embed.comp (continuous_embL B)) continuous_id
    (fun γ hγ => B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))) (fun γ hγ => hγ)
  obtain ⟨hb, Cb, hCb⟩ := om_bdd t.weil hΦ₂ t.cptS t.cptT (MonoidHom.id _) (MonoidHom.id _) continuous_id continuous_id
    (fun γ hγ => hγ) (fun γ hγ => hγ)
  simp only [MonoidHom.id_apply] at ha hCa hb hCb
  have e1 : ∀ h₀, t.s.lift (liftS t.om t.vT.μ t.vT.𝓕 F Φ₂) Φ₁ (embA B.d B.o h₀) =
      ∫ h in t.s.vW.𝓕, t.s.om (embA B.d B.o h₀, h) Φ₁ 0 * ∫ h' in t.vT.𝓕, t.om (h, h') Φ₂ 0 * F h' ∂t.vT.μ ∂t.s.vW.μ :=
    fun h₀ => rfl
  rw [per_rank_zero]
  simp_rw [e1]
  exact triple B.vA.μ t.s.vW.μ t.vT.μ B.vA.𝓕 t.s.vW.𝓕 t.vT.𝓕 (vol_lt_top B.cpt B.vA) (vol_lt_top t.cptS t.s.vW)
    (vol_lt_top t.cptT t.vT) φ F (fun x y => t.s.om (embA B.d B.o x, y) Φ₁ 0) (fun y z => t.om (y, z) Φ₂ 0) hφ.2 hF.2
    ha hb hCφ hCF hCa hCb

end GlobalTheory.Unf.LastSteps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.LevelCompact

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem actO_actO' (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_inv_actO' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO', mul_inv_cancel, mul_inv_cancel]
  unfold actO
  rw [inv_one, mt_one', mt_one']
  simp

theorem actO_add' (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_map_infPart (S T : HSp D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx]; simp

theorem continuous_actO_inv (S T : HSp D) :
    Continuous fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2 := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [actO, inv_inv]
  exact (((hmti T).comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((hmt S).comp (continuous_fst.comp continuous_fst))

theorem exists_level_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  intro D ψ S T χS χT om hom f hf K hK
  obtain ⟨U0, hU0, hf0⟩ := hf.level
  have hz : ∀ p : GA D S × GA D T, actO S T p.1⁻¹ p.2⁻¹ 0 = 0 := fun p => by simp [actO]
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0}
      add_mem' := fun {a b} ha hb p hp => by
        rw [actO_add']; exact U0.add_mem (ha p hp) (hb p hp)
      zero_mem' := fun p _ => by rw [hz]; exact U0.zero_mem
      neg_mem' := fun {a} ha p hp => by
        have : actO S T p.1⁻¹ p.2⁻¹ (-a) = -actO S T p.1⁻¹ p.2⁻¹ a := by
          simp only [actO, Matrix.mul_neg, Matrix.neg_mul]
        rw [this]; exact U0.neg_mem (ha p hp) }
  have hU : ∀ u, u ∈ U ↔ ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0 := fun _ => Iff.rfl
  refine ⟨U, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds U (g := 0) ?_
    have hn : IsOpen ((fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2) ⁻¹'
        (U0 : Set (WO S T))) := hU0.preimage (continuous_actO_inv S T)
    obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hn (by
      rintro ⟨p, w⟩ ⟨_, hw⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U0
      rw [hz]; exact U0.zero_mem)
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun w hw => (hU w).2 fun p hp => ?_
    have h2 := Set.mem_preimage.1 (huv (Set.mk_mem_prod (hKu hp) hw))
    exact SetLike.mem_coe.1 h2
  · rintro ⟨g, h⟩ hp
    change IsThetaFunO ψ S T (om (g, h) f) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (g, h) f) = om (g, h) f
    refine ⟨hom.om_pres (g, h) f hf, fun u hu h0 => ?_⟩
    have h1 : actO S T g⁻¹ h⁻¹ u ∈ U0 := (hU u).1 hu (g, h) hp
    have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf
    rw [actO_inv_actO', hf0 _ h1 (actO_map_infPart S T _ _ h0)] at e
    exact e.symm

end GlobalTheory.LevelCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteComponentUnitaryActingOnFiniteSuppor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.GlobFin.cong_entry {D : D7} {S : HSp D} {I : Ideal (AE D)} {h : GA D S} (hh : h ∈ congGrp S I) (i j : Fin S.rank) :
    mt S h i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ I := by
  have h1 := congrArg (fun A : GL (Fin S.rank) (AE D ⧸ I) => A.1 i j) (MonoidHom.mem_ker.mp hh)
  rw [← Ideal.Quotient.eq]
  have h2 : Ideal.Quotient.mk I ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ I)) i j := by
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *]
  rw [h2]
  simpa [Formalism.L2.Theta.mt, Matrix.GeneralLinearGroup.map] using h1

theorem GlobalTheory.GlobFin.mem_GfC {D : D7} {S : HSp D} {x : GA D S} (hx : x ∈ congGrp S (idAt D (fun _ => True))) : x ∈ GfC S := by
  show infHom S x = 1
  ext i j
  have h := GlobalTheory.GlobFin.cong_entry hx i j
  have hk : mt S x i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ RingHom.ker (infPart D) :=
    (inf_le_left : idAt D (fun _ => True) ≤ _) h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  have : ((infHom S x : GL _ _) : Matrix _ _ _) i j = infPart D (mt S x i j) := rfl
  rw [this, hk]
  simp [Matrix.one_apply, apply_ite]

theorem GlobalTheory.GlobFin.fin_rep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  intro D S g
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, hS⟩ := _root_.GlobalTheory.FinPl.localComponents D (fun _ => True)
  obtain ⟨x, hx, u, hu, rfl⟩ := (hS S).1 g
  refine ⟨x, GlobalTheory.GlobFin.mem_GfC hx, fun P y hy => ?_⟩
  have hy0 : ∀ j, y j ∈ idAt D (fun _ => True) := by
    intro j
    refine Ideal.mem_inf.mpr ⟨(Ideal.mem_inf.mp (hy j)).1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  have hu1 : Formalism.L2.Theta.mt S u *ᵥ y = y := by
    funext i
    have hz : ∀ j, (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j = 0 := by
      intro j
      have ha := (hOff _).mp (GlobalTheory.GlobFin.cong_entry hu i j)
      have hb := (hAt _).mp (hy0 j)
      calc (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j
          = (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * (ε * y j) := by rw [hb]
        _ = (ε * (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) * y j := by ring
        _ = 0 := by rw [ha, zero_mul]
    have hsum : ((Formalism.L2.Theta.mt S u - 1) *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      exact Finset.sum_eq_zero fun j _ => hz j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hsum
    exact hsum
  rw [mt_mul, ← Matrix.mulVec_mulVec, hu1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagUnipotentCoordinateMeasurableEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf

def coordFlip (D : D7) (ρ m : ℕ) : skewA D ρ × (Mx D ρ m × UX D ρ) ≃ₜ UX D ρ × (Mx D ρ m × skewA D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ m) := (lattice_Mx D ρ m).1
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  { toFun := fun p => (p.2.2⁻¹, (-p.2.1, -p.1))
    invFun := fun q => (-q.2.2, (-q.2.1, q.1⁻¹))
    left_inv := fun p => Prod.ext (neg_neg _) (Prod.ext (neg_neg _) (inv_inv _))
    right_inv := fun q => Prod.ext (inv_inv _) (Prod.ext (neg_neg _) (neg_neg _))
    continuous_toFun := continuous_snd.snd.inv.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.neg)
    continuous_invFun := continuous_snd.snd.neg.prodMk (continuous_snd.fst.neg.prodMk continuous_fst.inv) }

theorem coordFlip_apply (D : D7) (ρ m : ℕ) (p : skewA D ρ × (Mx D ρ m × UX D ρ)) :
    coordFlip D ρ m p = (p.2.2⁻¹, (-p.2.1, -p.1)) := rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem flagCoord_measEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ),
    ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d,
      ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  intro D V V₀ ρ d
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.MixPer.flagCoord_homeo D V V₀ ρ d
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : SecondCountableTopology (UX D ρ) := (GlobalTheory.UnitU.topology D ρ).2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨((coordFlip D ρ V₀.rank).trans (Φ.trans (Homeomorph.inv (flagN d)))).toMeasurableEquiv, fun p => ?_⟩
  change (((Φ (coordFlip D ρ V₀.rank p))⁻¹ : flagN d) : GA D V) = _
  rw [Subgroup.coe_inv, hΦ, coordFlip_apply]
  change (d.levi ((p.2.2⁻¹ : UX D ρ) : GL (Fin ρ) (AE D)) * (d.nB (-p.2.1) * d.nC (-p.1)))⁻¹ = _
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, d.nB_inv, d.nC_inv, neg_neg, neg_neg, Subgroup.coe_inv, map_inv, inv_inv,
    mul_assoc]

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarCovolumeOneSkewHermitianAdelic
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SkewVol

variable (D : D7) (ρ : ℕ)

def skewPart (x : Mx D ρ ρ) : Mx D ρ ρ := half D • (x - adj x)

variable {D ρ}

theorem skewPart_mem (x : Mx D ρ ρ) : skewPart D ρ x ∈ skewA D ρ := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {c : Mx D ρ ρ} (hc : c ∈ skewA D ρ) : skewPart D ρ c = c := by
  rw [skewPart, (mem_skewA).1 hc, sub_neg_eq_add, smul_add, half_smul_add]

theorem skewPart_add (x y : Mx D ρ ρ) : skewPart D ρ (x + y) = skewPart D ρ x + skewPart D ρ y := by
  rw [skewPart, skewPart, skewPart, adj_add, add_sub_add_comm, smul_add]

theorem skewPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : skewPart D ρ x ∈ ratMx D ρ ρ := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ - γᴴ), ?_⟩
  rw [rat_smul, rat_sub, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPart D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  show Continuous fun x => half D • (x - adj x) from (continuous_id.sub continuous_adj).const_smul (half D)

theorem isClosed_skewA : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) :=
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
  isClosed_eq continuous_adj continuous_neg

theorem isCoLat_skew :
    GlobalTheory.CuspGeneric.IsCoLat ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D ρ ρ
  refine ⟨?_, ?_⟩
  · let φ : (ratMx D ρ ρ).addSubgroupOf (skewA D ρ) → ratMx D ρ ρ := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D ρ ρ → skewA D ρ := fun x => ⟨skewPart D ρ x, skewPart_mem x⟩
    have hP : Continuous P := continuous_skewPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_addSubgroupOf.2 (skewPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change skewPart D ρ (γ + x.1) = skewPart D ρ γ + x.1
    rw [skewPart_add, skewPart_of_mem x.2]

theorem exists_haar_covol_one : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  intro D ρ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (skewA D ρ) := (isClosed_skewA (D := D) (ρ := ρ)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (skewA D ρ) _ isCoLat_skew
  exact ⟨μ, 𝓕, hμ, inferInstance, hF, h1⟩

end GlobalTheory.SkewVol
end
end

