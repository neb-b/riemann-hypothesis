module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import GroundTheory.LocalFields.Uniqueness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0498
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := _root_.GlobalTheory.SerOSys.zIdem_centralIdempotent τ h

theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := _root_.GlobalTheory.SerOSys.zIdem_mul_eq_zero_of_ne τ τ' h h' hne

theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := _root_.GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPr
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory

theorem isL_of_irreducible_prod_unitarisable_nu :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  intro k _ _ _ _ hprec a V _ _ σ hσ m δ Δ s hL hU hs hd ⟨e⟩
  refine ⟨m, fun j => (δ j).nu (s j), hd, ⟨fun j => (Δ j).nu (s j), ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Fin.univ_val_map _
  · intro i j _ h
    have h1 := hprec (δ i) (δ j) (Δ i) (Δ j) (hL i) (hU i) (hL j) (hU j) (s i) (s j) h
    have hi := abs_lt.1 (hs i)
    have hj := abs_lt.1 (hs j)
    linarith
  · intro j
    exact ((hL j).tw _ (isSmoothChar_absPow _)).of_equiv ((δ j).twEquiv _ _)
  · exact (isCosocle_self hσ).of_equiv (.refl _) e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LBC
open scoped Topology

namespace GlobalTheory.LBC.Inh
open ValuativeRel Filter

section Cont
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']

theorem isOpen_lt_one (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen {x : F | valuation F x < 1} := by
  refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff').2 ⟨1, fun z hz => ?_⟩
  have e : z = (z - x) + x := by ring
  show valuation F z < 1
  rw [e]
  have hz' : valuation F (z - x) < 1 := by simpa using hz
  exact (valuation F).map_add_lt hz' hx

theorem lt_one_of_lt_one (hc : Continuous (algebraMap k k')) {z : k} (h : valuation k z < 1) :
    valuation k' (algebraMap k k' z) < 1 := by
  have h1 := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff z).2 h
  have h2 := (hc.tendsto 0).comp h1
  rw [map_zero] at h2
  apply (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).1
  refine h2.congr fun n => ?_
  simp [Function.comp_apply, map_pow]

theorem lt_one_iff (hc : Continuous (algebraMap k k')) (z : k) :
    valuation k' (algebraMap k k' z) < 1 ↔ valuation k z < 1 := by
  refine ⟨fun h => ?_, lt_one_of_lt_one hc⟩
  by_contra hz
  push_neg at hz
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  rcases hz.lt_or_eq with hlt | heq
  · have h2 : valuation k z⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    have h3 := lt_one_of_lt_one (k' := k') hc h2
    have h4 : valuation k' (algebraMap k k' z) * valuation k' (algebraMap k k' z⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
    have := lt_of_le_of_lt (mul_le_of_le_one_left' h.le) h3
    rw [h4] at this
    exact lt_irrefl _ this
  · set S : Set k := {x | valuation k x ≤ 1} ∩ {x | valuation k x < 1}ᶜ with hS
    have hSc : IsCompact S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall k 1).inter_right (isOpen_lt_one k).isClosed_compl
    haveI : T2Space k' := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k'
    have hI : IsClosed (algebraMap k k' '' S) := (hSc.image hc).isClosed
    have h0 : (0 : k') ∉ algebraMap k k' '' S := by
      rintro ⟨x, hx, hx0⟩
      rw [map_eq_zero_iff _ (algebraMap k k').injective] at hx0
      subst hx0
      simp [hS] at hx
    have ht := (GroundTheory.LocalField.tendsto_pow_atTop_nhds_zero_iff (algebraMap k k' z)).2 h
    obtain ⟨n, hn⟩ := (ht.eventually (hI.isOpen_compl.mem_nhds h0)).exists
    apply hn
    refine ⟨z ^ n, ?_, by rw [map_pow]⟩
    simp [hS, map_pow, ← heq]

theorem valuativeExtension (hc : Continuous (algebraMap k k')) : ValuativeExtension k k' :=
  ⟨fun {a b} => GroundTheory.LocalField.vle_map_iff_of_valuation_lt_one_iff
    (algebraMap k k') (lt_one_iff hc) a b⟩

theorem continuous_algNorm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) :
    Continuous (Algebra.norm k : k' → k) := by
  classical
  haveI := valuativeExtension hc
  haveI := GroundTheory.LocalField.isModuleTopology k k'
  let b := Module.finBasis k k'
  have h : (Algebra.norm k : k' → k) = fun t => (Algebra.leftMulMatrix b t).det := by
    funext t; exact Algebra.norm_eq_matrix_det b t
  rw [h]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun t : k' => Algebra.leftMulMatrix b t i j) =
      fun t => (b.coord i) (LinearMap.mulRight k (b j) t) := by
    funext t; simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord i).comp (LinearMap.mulRight k (b j)))

theorem isSmoothChar_comp_norm [FiniteDimensional k k'] (hc : Continuous (algebraMap k k')) {χ : kˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) : IsSmoothChar (χ.comp (Units.map (Algebra.norm k : k' →* k))) :=
  hχ.comp _ (Continuous.units_map _ (continuous_algNorm hc))

end Cont

end GlobalTheory.LBC.Inh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldEStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i.symm → ∀ {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.SmGL.IsCuspidal (π.comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  first | exact @GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | exact GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | (intros; apply GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

noncomputable section

namespace GlobalTheory.SupercuspUnitary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def scal (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {h | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ y, l (ρ h y) = c * l y}
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], fun y => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha, hb, mul_assoc]
  one_mem' := ⟨1, by simp, fun y => by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun y => ?_⟩
    have h := ha (ρ a⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

def term (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))

theorem term_mul {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (v w : V) (g : G) {h : G}
    (hh : h ∈ scal ρ l) : term ρ l v w (g * h) = term ρ l v w g := by
  obtain ⟨c, hc, hl⟩ := (scal ρ l).inv_mem hh
  have h1 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [term, mul_inv_rev, map_mul, Module.End.mul_apply, hl]
  linear_combination (l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))) * h1

theorem term_inv_mul (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (x g : G) :
    term ρ l v w (x⁻¹ * g) = term ρ l (ρ x v) (ρ x w) g := by
  simp only [term, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

def qterm (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (q : G ⧸ scal ρ l) : ℂ :=
  term ρ l v w q.out

theorem qterm_mk (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) :
    qterm ρ l v w (g : G ⧸ scal ρ l) = term ρ l v w g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (scal ρ l) g
  rw [qterm, hh, term_mul v w g h.2]

theorem center_le_scal {ρ : Representation ℂ G V} (l : Module.Dual ℂ V)
    (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) :
    Subgroup.center G ≤ scal ρ l := fun z hz' => by
  obtain ⟨c, hc, h⟩ := hz z hz'
  exact ⟨c, hc, fun y => by rw [h, map_smul, smul_eq_mul]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_scal {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual) :
    IsOpen (scal ρ l : Set G) := by
  refine (scal ρ l).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((show IsOpen
    {g : G | ρ.dual g l = l} from hl).mem_nhds (by
      simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg => ⟨1, by simp, fun y => ?_⟩)
  have h1 : (ρ.dual g l) (ρ g y) = l (ρ g y) := by rw [show ρ.dual g l = l from hg]
  rw [Representation.dual_apply] at h1
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply] at h1
  rw [one_mul, h1]

theorem exists_finset {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual)
    (hsc : IsSupercuspidal ρ) (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v)
    (v : V) : ∃ s : Finset (G ⧸ scal ρ l), ∀ g : G, l (ρ g⁻¹ v) ≠ 0 → (g : G ⧸ scal ρ l) ∈ s := by
  obtain ⟨C, hC, hCz⟩ := hsc.2 v l hl
  haveI := QuotientGroup.discreteTopology (isOpen_scal hl)
  have hD : ((fun c : G => ((c⁻¹ : G) : G ⧸ scal ρ l)) '' C).Finite :=
    (hC.image (by fun_prop)).finite_of_discrete
  refine ⟨hD.toFinset, fun g hg => ?_⟩
  obtain ⟨z, hz', c, hc, e⟩ := hCz g⁻¹ hg
  rw [Set.Finite.mem_toFinset]
  refine ⟨c, hc, QuotientGroup.eq.2 ?_⟩
  have h2 : (c⁻¹)⁻¹ * g = z⁻¹ := by rw [← inv_inv g, e]; group
  rw [h2]
  exact center_le_scal l hz (inv_mem hz')

end GlobalTheory.SupercuspUnitary

namespace GlobalTheory


open GlobalTheory.SupercuspUnitary in
theorem isUnitarisable_of_isSupercuspidal : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual →
    l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ →
    (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  intro G V _ _ _ _ _ ρ l hl hl0 hirr hsc hz
  have hfin : ∀ v w, (Function.support (qterm ρ l v w)).Finite := fun v w => by
    obtain ⟨s, hs⟩ := exists_finset hl hsc hz v
    refine s.finite_toSet.subset fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Function.mem_support, qterm_mk] at hq
      exact hs g (left_ne_zero_of_mul hq)

  have hadd1 : ∀ v v' w q, qterm ρ l (v + v') w q = qterm ρ l v w q + qterm ρ l v' w q := by
    intro v v' w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), add_mul]
  have hsmul1 : ∀ (a : ℂ) v w q, qterm ρ l (a • v) w q = a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w' q, qterm ρ l v (w + w') q = qterm ρ l v w q + qterm ρ l v w' q := by
    intro v w w' q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), mul_add]
  have hsmul2 : ∀ (a : ℂ) v w q, qterm ρ l v (a • w) q = starRingEnd ℂ a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_smul, smul_eq_mul, map_mul]
      ring
  have hconj : ∀ v w q, qterm ρ l w v q = starRingEnd ℂ (qterm ρ l v w q) := by
    intro v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_mul, Complex.conj_conj]
      ring
  have hinv : ∀ (x : G) v w q, qterm ρ l (ρ x v) (ρ x w) q = qterm ρ l v w (x⁻¹ • q) := by
    intro x v w q
    induction q using QuotientGroup.induction_on with
    | H g => rw [MulAction.Quotient.smul_mk, smul_eq_mul, qterm_mk, qterm_mk, term_inv_mul]
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∑ᶠ q, qterm ρ l v w q)
    (fun v v' w => by simp only [hadd1]; exact finsum_add_distrib (hfin v w) (hfin v' w))
    (fun a v w => by simp only [hsmul1, RingHom.id_apply, smul_eq_mul, mul_finsum])
    (fun v w w' => by simp only [hadd2]; exact finsum_add_distrib (hfin v w) (hfin v w'))
    (fun a v w => by simp only [hsmul2, smul_eq_mul, mul_finsum])
  have hB : ∀ v w, B v w = ∑ᶠ q, qterm ρ l v w q := fun v w => LinearMap.mk₂'ₛₗ_apply _ _ _
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun x v w => ?_⟩
  · rw [hB, hB, map_finsum _ (hfin v w)]
    exact finsum_congr fun q => hconj v w q
  · have hex : ∃ g : G, l (ρ g v) ≠ 0 := by
      by_contra! h0
      let U : Subrepresentation ρ :=
        { toSubmodule := ⨅ g : G, LinearMap.ker (l ∘ₗ (ρ g : V →ₗ[ℂ] V))
          apply_mem_toSubmodule := fun g y hy => by
            simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
            intro g'
            rw [← Module.End.mul_apply, ← map_mul]
            exact hy _ }
      haveI := hirr
      rcases eq_bot_or_eq_top U with hU | hU
      · have hvU : v ∈ U.toSubmodule := by
          simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
          exact h0
        rw [hU] at hvU
        exact hv ((Submodule.mem_bot ℂ).1 hvU)
      · refine hl0 (LinearMap.ext fun y => ?_)
        have hyU : y ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hyU
        simpa using hyU 1
    obtain ⟨g, hg⟩ := hex
    rw [hB, finsum_eq_sum _ (hfin v v), Complex.re_sum]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨((g⁻¹ : G) : G ⧸ scal ρ l), ?_, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H g' =>
        rw [qterm_mk, term, Complex.mul_conj, Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    · rw [Set.Finite.mem_toFinset, Function.mem_support, qterm_mk, term, inv_inv, Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 hg).ne'
    · rw [qterm_mk, term, inv_inv, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_pos.2 hg
  · rw [hB, hB]
    simp only [hinv]
    exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ : G) : Equiv.Perm (G ⧸ scal ρ l))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagFrameIsLagFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalAbsorptionLengthBoundOfBlochKato
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ClosingStatement

theorem main : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      BlochKatoDuality.Conclusion1 D ∧ BlochKatoDuality.Conclusion2 D := by
  intro hBK hTD hEC D _ _ _
  have h5 : Formalism.MainNotions.LocalSituation.Conclusion5 D := _root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hBK hTD hEC D
  have a1 : BlochKatoDuality.adm1 D := dimension_input_one_of_bloch_kato D h5
  have a2 : BlochKatoDuality.adm2 D := dimension_input_two_of_bloch_kato D h5
  have a3 : BlochKatoDuality.adm3 D := fun l _ K => GlobalTheory.T.tate_H2_period_datum hTD l (D.loc l) K
  have a5 : BlochKatoDuality.adm5 D := fun l _ K => GlobalTheory.T.finite_H1_period_datum hTD l (D.loc l) K
  have a6 : BlochKatoDuality.adm6 D := fun l _ K => (_root_.GlobalTheory.TateDualFil.main D l K).1
  exact ⟨BlochKatoDuality.ramification_two_and_conjugation_at_q_and_d D a1 a2 a6, BlochKatoDuality.second_proposition_every_localisation D a1 a2 a3 a5 a6⟩

end GlobalTheory.ClosingStatement
end

