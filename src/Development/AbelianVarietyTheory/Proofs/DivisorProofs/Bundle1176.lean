module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfKillsIdealPowerTorsionSemiAbelian
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense
open scoped nonZeroDivisors

theorem exists_pow_eq_span (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (hI' : I ≠ ⊤) : ∃ (h : ℕ) (π : 𝓞 E), 0 < h ∧ I ^ h = Ideal.span {π} ∧ π ≠ 0 ∧ ¬ IsUnit π := by
  have hmem : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  let c := ClassGroup.mk0 ⟨I, hmem⟩
  have hc : c ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  have hmem' : I ^ Fintype.card (ClassGroup (𝓞 E)) ∈ (Ideal (𝓞 E))⁰ := pow_mem hmem _
  have hp : (I ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hmem']
    rw [← hc, ← map_pow]
    rfl
  obtain ⟨π, hπ⟩ := hp
  have hpos : 0 < Fintype.card (ClassGroup (𝓞 E)) := Fintype.card_pos
  refine ⟨_, π, hpos, by rw [hπ], ?_, ?_⟩
  · rintro rfl
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊥ := by rw [hπ]; simp
    exact hI (pow_eq_zero_iff hpos.ne' |>.1 this)
  · intro hu
    have : I ^ Fintype.card (ClassGroup (𝓞 E)) = ⊤ := by
      rw [hπ]; exact Ideal.span_singleton_eq_top.2 hu
    exact hI' (eq_top_iff.2 (this ▸ Ideal.pow_le_self hpos.ne'))

theorem exists_act_pow_stable {k : Type} [Field k] [IsAlgClosed k] {O : Type} [CommRing O]
    (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (act : OAct O G) (π : O)
    (K : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)) (Z : Set G.left) (hZ : IsClosed Z)
    (hK : ∀ x, x ∈ K ↔ Set.range x.left ⊆ Z) (hKs : ∀ x ∈ K, x ≫ act.act π ∈ K) :
    ∃ a : ℕ, ∀ x ∈ K, ∃ y ∈ K, y ≫ act.act (π ^ (a + 1)) = x ≫ act.act (π ^ a) := by
  letI := zariski G
  haveI := noetherianSpace_zariski G
  have hcl : ∀ n : ℕ, IsClosed {z : 𝟙_ (Over (Sp k)) ⟶ G | ∃ y ∈ K, y ≫ act.act (π ^ n) = z} :=
    fun n => by
    obtain ⟨Z', hZ', h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (act.act (π ^ n))
      (act.hom _) inferInstance inferInstance inferInstance inferInstance K Z hZ hK
    refine isClosed_induced_iff.2 ⟨Z', hZ', ?_⟩
    ext z
    rw [Set.mem_preimage, ← range_left_subset_iff, ← h]
    rfl
  let F : ℕ → Closeds (𝟙_ (Over (Sp k)) ⟶ G) := fun a => ⟨_, hcl a⟩
  obtain ⟨_, ⟨a, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds (𝟙_ (Over (Sp k)) ⟶ G))).has_min
    (Set.range F) ⟨_, 0, rfl⟩
  have hle : F (a + 1) ≤ F a := by
    rintro _ ⟨y, hy, rfl⟩
    haveI := act.hom π
    refine ⟨y ≫ act.act π, ?_, by rw [Category.assoc, ← act.mul, ← pow_succ']⟩
    exact hKs y hy
  have heq : F (a + 1) = F a := hle.eq_of_not_lt (hmin _ ⟨_, rfl⟩)
  refine ⟨a, fun x hx => ?_⟩
  have : x ≫ act.act (π ^ a) ∈ F (a + 1) := by
    rw [heq]
    exact ⟨x, hx, rfl⟩
  exact this

end GlobalTheory.IdealTorsion

namespace GlobalTheory.IdealTorsion

open RationalPoint GlobalTheory.TorsionDense

theorem eq_one_of_idealTorsion_comp_eq_one : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (u : G ⟶ G) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom u → (∀ a, act.act a ≫ u = u ≫ act.act a) → I ≠ ⊤ → (∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ u = 1) → u = 1 := by
  intro E _ _ k _ _ _ G _ act u I hG hu hcomm hI hkill
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := isIntegral_left_of_isSemiAbelian G
  haveI := hu
  have hact : ∀ a, IsMonHom (act.act a) := act.hom
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    MonoidHom.mk' (fun x => x ≫ u) fun x y => MonObj.mul_comp x y u
  by_cases hbot : I = ⊥
  · subst hbot
    refine eq_one_of_finite_range u ?_
    have : (Set.range fun x : 𝟙_ (Over (Sp k)) ⟶ G => x ≫ u) ⊆ {1} := by
      rintro _ ⟨x, rfl⟩
      refine hkill 1 x fun a ha => ?_
      rw [pow_one, Ideal.mem_bot] at ha
      rw [ha, h0, MonObj.comp_one]
    exact (Set.finite_singleton _).subset this
  obtain ⟨h, π, hh, hπ, hπ0, hπu⟩ := exists_pow_eq_span E I hbot hI
  have htors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), x ≫ act.act (π ^ n) = 1 → x ≫ u = 1 := by
    intro n x hx
    refine hkill (h * n) x fun a ha => ?_
    rw [pow_mul, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_comm, act.mul, ← Category.assoc, hx, MonObj.one_comp]
  obtain ⟨a, ha⟩ := exists_act_pow_stable G act π φ.ker (u.left ⁻¹' {pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)})
    ((isClosed_pt _).preimage u.left.continuous) (fun x => by
      rw [range_left_subset_iff, Set.mem_preimage, ← pt_comp, Set.mem_singleton_iff,
        pt_injective.eq_iff]
      rfl) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      change x ≫ act.act π ≫ u = 1
      rw [hcomm, ← Category.assoc]
      change (x ≫ u) ≫ act.act π = 1
      rw [show x ≫ u = 1 from hx, MonObj.one_comp])
  obtain ⟨Z', hZ', h'⟩ := exists_isClosed_image_of_isClosed_subgroup k G G u hu inferInstance
    inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ (by simp)
  have hfin : Finite φ.range := by
    refine _root_.GlobalTheory.OStableClosed.finite_of_isClosed_of_no_torsion E k G act π hG hπ0 hπu _ Z' hZ' (fun y => ?_) ?_ ?_
    · rw [← h']
      exact ⟨fun ⟨x, hx⟩ => ⟨x, trivial, hx⟩, fun ⟨x, _, hx⟩ => ⟨x, hx⟩⟩
    · rintro b _ ⟨g, rfl⟩
      refine ⟨g ≫ act.act b, ?_⟩
      change (g ≫ act.act b) ≫ u = (g ≫ u) ≫ act.act b
      rw [Category.assoc, hcomm, Category.assoc]
    · rintro _ ⟨g, rfl⟩ hg
      have hgk : g ≫ act.act π ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        change (g ≫ act.act π) ≫ u = 1
        rw [Category.assoc, hcomm, ← Category.assoc]
        exact hg
      obtain ⟨y, hy, hyg⟩ := ha _ hgk
      let ψ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
        MonoidHom.mk' (fun x => x ≫ act.act (π ^ (a + 1))) fun x y => MonObj.mul_comp x y _
      have h1 : φ (g / y) = 1 := htors (a + 1) (g / y) (by
        change ψ (g / y) = 1
        rw [map_div, div_eq_one]
        change g ≫ act.act (π ^ (a + 1)) = y ≫ act.act (π ^ (a + 1))
        rw [hyg, pow_succ', act.mul, Category.assoc])
      rwa [map_div, MonoidHom.mem_ker.1 hy, div_one] at h1
  exact eq_one_of_finite_range u hfin

end GlobalTheory.IdealTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
section
noncomputable section

open NumberField MeasureTheory Matrix Topology Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CuspQuot

section Test

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Set V} {α : V → ℂ}

def IsTest (U : Set V) (α : V → ℂ) : Prop := ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U

theorem IsTest.continuous_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Continuous fun x => α x * G x :=
  continuous_of_tsupport fun x hx => h.1.continuous.continuousAt.mul
    (hG.continuousAt (hU.mem_nhds (h.2.2 (tsupport_mul_subset_left hx))))

theorem IsTest.add {β : V → ℂ} (h : IsTest U α) (h' : IsTest U β) : IsTest U (α + β) :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, (tsupport_add α β).trans (Set.union_subset h.2.2 h'.2.2)⟩

theorem IsTest.mul (h : IsTest U α) {β : V → ℂ} (hβ : ContDiff ℝ ∞ β) : IsTest U fun x => α x * β x :=
  ⟨h.1.mul hβ, h.2.1.mul_right, tsupport_mul_subset_left.trans h.2.2⟩

theorem IsTest.fderiv (h : IsTest U α) (v : V) : IsTest U fun x => fderiv ℝ α x v :=
  ⟨(h.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, h.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans h.2.2⟩

theorem isTest_zero : IsTest U (0 : V → ℂ) := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure]

theorem IsTest.integrable_mul (hU : IsOpen U) (h : IsTest U α) {G : V → ℂ} (hG : ContinuousOn G U) :
    Integrable (fun x => α x * G x) ν :=
  (h.continuous_mul hU hG).integrable_of_hasCompactSupport h.2.1.mul_right

end Test

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def smoothing (ν : Measure (Lie E a)) (α : Lie E a → ℂ) (φ : GA E a → ℂ) (x : GA E a) : ℂ :=
  ∫ y, α y * chart φ x y ∂ν

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]


variable {μ} [μ.IsMulRightInvariant] {S : Submodule ℂ (L2 (latticeGL E a) μ)}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [_root_.NumberField.IsTotallyComplex E] in
theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin a) (Cinf E) → Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact Units.isOpenEmbedding_val
end

theorem continuous_infGL : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Continuous fun p : GA E a × Lie E a => α p.2 * chart φ p.1 p.2 := by
  refine continuous_of_tsupport fun p hp => (hα.1.continuous.comp continuous_snd).continuousAt.mul ?_
  have h1 : p.2 ∈ tsupport α := by
    refine (closure_minimal (fun q hq => ?_) ((isClosed_tsupport α).preimage continuous_snd) :
      _ ⊆ Prod.snd ⁻¹' tsupport α) hp
    exact subset_tsupport _ (left_ne_zero_of_mul hq)
  obtain ⟨x, y⟩ := p
  obtain ⟨u, hu⟩ := hα.2.2 h1
  obtain rfl : y = toL u.val := hu.symm
  have he : IsOpenEmbedding (Prod.map id fun u : GL (Fin a) (Cinf E) => toL u.val : GA E a × _ → GA E a × Lie E a) :=
    IsOpenEmbedding.id.prodMap isOpenEmbedding_val
  refine (he.continuousAt_iff (x := (x, u))).1 (Continuous.continuousAt ?_)
  exact (hφ.comp (continuous_fst.mul (continuous_infGL.comp continuous_snd))).congr fun q => (chart_val φ q.1 q.2).symm

theorem norm_chart_le {φ : GA E a → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (x : GA E a) (y : Lie E a) : ‖chart φ x y‖ ≤ C := by
  unfold chart
  split_ifs
  · exact hC _
  · exact norm_zero.trans_le ((norm_nonneg _).trans (hC 1))

theorem continuous_smoothing (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}
    (hα : IsTest (invSet E a) α) {φ : GA E a → ℂ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) :
    Continuous (smoothing ν α φ) :=
  continuous_of_dominated (bound := fun y => ‖α y‖ * C)
    (fun x => ((continuous_integrand hα hφ).comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    (fun x => .of_forall fun y => (norm_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (norm_chart_le hC x y) (norm_nonneg _)))
    ((hα.1.continuous.integrable_of_hasCompactSupport hα.2.1).norm.mul_const C)
    (.of_forall fun y => (continuous_integrand hα hφ).comp (Continuous.prodMk_left y))

variable [IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)]


omit [μ.IsMulRightInvariant] in
theorem memL2_of_bound {φ : GA E a → ℂ} (hφ : Continuous φ) (hl : LeftInv (latticeGL E a) φ) {C : ℝ}
    (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ :=
  ⟨hl, MemLp.of_bound (aestronglyMeasurable_quotMeasure_iff_lift.2 (by
    rw [hl.lift_descend]; exact hφ.aestronglyMeasurable)) C (.of_forall fun q => hC _)⟩


end GlobalTheory.CuspQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantDoubleCosetSectionMemEquivariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def secMemLeftMul {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g : H) : Module.End ℂ V ≃+ Module.End ℂ V where
  toFun f := ρ g * f
  invFun f := ρ g⁻¹ * f
  left_inv f := by
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  right_inv f := by
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  map_add' a b := mul_add _ a b

theorem secM_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V),
    secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K' x v
  refine ⟨fun g y => ?_, fun k hk y => ?_⟩
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0) v
      = ρ g (((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v)
    have hsum : (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
        = ρ g * (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) := by
      rw [← finsum_comp_equiv (Equiv.mulLeft g)]
      have hpt : ∀ h' : H, (fun h : H => if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
          ((Equiv.mulLeft g) h') = secMemLeftMul ρ g (if (ι h' * x)⁻¹ * y ∈ K' then ρ h' else 0) := by
        intro h'
        have he : (ι (g * h') * x)⁻¹ * (ι g * y) = (ι h' * x)⁻¹ * y := by
          rw [map_mul]; group
        simp only [Equiv.coe_mulLeft, he]
        change _ = ρ g * _
        split_ifs
        · exact map_mul ρ g h'
        · exact (mul_zero _).symm
      simp_rw [hpt]
      exact (AddEquiv.map_finsum (secMemLeftMul ρ g) _).symm
    rw [hsum, map_smul]
    rfl
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (y * k) ∈ K' then ρ h else 0) v
      = ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v
    have hc : ∀ h : H, ((ι h * x)⁻¹ * (y * k) ∈ K' ↔ (ι h * x)⁻¹ * y ∈ K') := by
      intro h
      rw [← mul_assoc]
      exact Subgroup.mul_mem_cancel_right K' hk
    simp_rw [hc]

end GlobalTheory.BCT.TraceBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantFunctionEqFinsumDoubleCosetSections
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_apply' (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) (v : V) (y : G) :
    secM ι ρ K x v y =
      ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v := rfl

theorem finsum_apply_eq (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) {φ : G → V}
    (hφ : φ ∈ eqvM ι ρ K) (x y : G) (hs : Set.Finite {h : H | (ι h * x)⁻¹ * y ∈ K}) :
    (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) (φ x) =
      Nat.card {h : H | (ι h * x)⁻¹ * y ∈ K} • φ y := by
  rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) ?_]
  · rw [LinearMap.sum_apply,
      Finset.sum_congr rfl (g := fun _ => φ y) ?_, Finset.sum_const, ← Nat.card_eq_card_finite_toFinset]
    intro h hh
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
    rw [if_pos hh, ← hφ.1 h x, ← hφ.2 _ hh (ι h * x), mul_inv_cancel_left]
  · intro h hh
    rw [Function.mem_support] at hh
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hc
    exact hh (if_neg hc)

theorem card_eq (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup G) (x : G) (h₀ : H) {k₀ : G}
    (hk₀ : k₀ ∈ K) :
    ∃ e : {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} → ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom),
      Function.Bijective e := by
  have key : ∀ h : H, (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K ↔ x⁻¹ * ι (h⁻¹ * h₀) * x ∈ K := by
    intro h
    have : (ι h * x)⁻¹ * (ι h₀ * x * k₀) = x⁻¹ * ι (h⁻¹ * h₀) * x * k₀ := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.mul_mem_cancel_right K hk₀]
  refine ⟨fun h => ⟨ι (h.1⁻¹ * h₀), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
    Subgroup.mem_map.mpr ⟨x⁻¹ * ι (h.1⁻¹ * h₀) * x, (key h.1).mp h.2, ?_⟩⟩⟩, ?_, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · intro a b hab
    have := hι (congrArg Subtype.val hab)
    exact Subtype.ext (by simpa using this)
  · rintro ⟨g, hg⟩
    obtain ⟨⟨s, rfl⟩, hm⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨h₀ * s⁻¹, ?_⟩, ?_⟩
    · show (ι (h₀ * s⁻¹) * x)⁻¹ * (ι h₀ * x * k₀) ∈ K
      rw [key]
      have : x⁻¹ * ι ((h₀ * s⁻¹)⁻¹ * h₀) * x = k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hks
        simp [← hks, mul_assoc]
      rw [this]; exact hk
    · apply Subtype.ext
      simp

end GlobalTheory.BCT.TraceBlocks.Decomp

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_self (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K : Subgroup G)
    {φ : G → V} (hφ : φ ∈ eqvM ι ρ K) (x : G) [Finite ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom)]
    (h₀ : H) {k₀ : G} (hk₀ : k₀ ∈ K) :
    secM ι ρ K x (φ x) (ι h₀ * x * k₀) = φ (ι h₀ * x * k₀) := by
  obtain ⟨e, he⟩ := card_eq ι hι K x h₀ hk₀
  have hfin : Set.Finite {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} :=
    Set.finite_coe_iff.mp (Finite.of_injective e he.1)
  rw [secM_apply', finsum_apply_eq ι ρ K hφ x _ hfin, Nat.card_congr (Equiv.ofBijective e he),
    ← Nat.cast_smul_eq_nsmul ℂ]
  have hpos : (0 : ℕ) < Nat.card ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom) := Nat.card_pos
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr hpos.ne') _

theorem secM_off (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x y : G) (v : V)
    (hy : ∀ h : H, (ι h * x)⁻¹ * y ∉ K) : secM ι ρ K x v y = 0 := by
  rw [secM_apply']
  simp only [hy, if_false, finsum_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.BCT.TraceBlocks.Decomp


open GlobalTheory.BCT.TraceBlocks.Decomp in
theorem GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K' : Subgroup G), Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) → (∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) → ∀ φ ∈ eqvM ι ρ K', ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G), secM ι ρ K' (Quotient.out q) (φ (Quotient.out q)) = φ := by
  intro G H V _ _ _ _ ι hι ρ K' hQ hS φ hφ
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G))
  funext y
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.sum_eq_single (DoubleCoset.mk ι.range K' y)]
  · obtain ⟨g, hg, k₀, hk₀, hy⟩ := (@DoubleCoset.eq _ _ ι.range K'
      (Quotient.out (DoubleCoset.mk ι.range K' y)) y).mp (DoubleCoset.out_eq' _)
    obtain ⟨h₀, rfl⟩ := hg
    haveI := hS (Quotient.out (DoubleCoset.mk ι.range K' y))
    have key := secM_self ι hι ρ K' hφ (Quotient.out (DoubleCoset.mk ι.range K' y)) h₀ hk₀
    rw [← hy] at key
    exact key
  · intro q _ hq
    refine secM_off ι ρ K' _ y _ fun h hh => hq ?_
    refine (DoubleCoset.out_eq' q).symm.trans ((@DoubleCoset.eq _ _ _ _ _ _).mpr
      ⟨ι h, ⟨h, rfl⟩, _, hh, (mul_inv_cancel_left _ _).symm⟩)
  · intro h
    exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigherStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_char_h0_h1_bound_higher : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  first | exact @GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | exact GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le | (intros; apply GlobalTheory.NefRR.abs_chi_sub_hdim_zero_add_hdim_one_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  first | (exact @GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (exact GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (intros; apply GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep  <;> assumption)
end

