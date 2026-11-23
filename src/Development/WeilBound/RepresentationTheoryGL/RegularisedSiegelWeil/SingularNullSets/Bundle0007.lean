module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LBumpExA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Rsw.L.LBumpEx

variable {D : D7}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

abbrev Ev (D : D7) (v : Pl D) : Type := Fv D.host.F v ⊗[D.host.F] D.host.E

def cf (v : Pl D) : AfE D →ₐ[D.host.F] Ev D v :=
  Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)

theorem cf_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) : cf v (a ⊗ₜ[D.host.F] x) = evalV D.host.F v a ⊗ₜ[D.host.F] x :=
  rfl

theorem cv_eq (v : Pl D) (x : AE D) : cv D v x = cf v (finPart D x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), map_add (f := _), hx, hy]

theorem cf_mem_of_mem {z : AfE D} (hz : z ∈ intAE D) (v : Pl D) : cf v z ∈ intLoc D.host.F D.host.E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [cf_tmul]
    exact tmul_mem_intLoc (ha v) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def pr (φ : D.host.E →ₗ[D.host.F] D.host.F) : AfE D →ₗ[D.host.F] Af D.host.F :=
  (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ φ.lTensor (Af D.host.F)

theorem pr_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (a : Af D.host.F) (x : D.host.E) :
    pr φ (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [pr, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

def aux₃ (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) : Ev D v →ₗ[D.host.F] Fv D.host.F v :=
  (TensorProduct.rid D.host.F (Fv D.host.F v)).toLinearMap ∘ₗ φ.lTensor (Fv D.host.F v)

theorem trace_projection_tmul (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (a : Fv D.host.F v) (x : D.host.E) :
    aux₃ φ v (a ⊗ₜ[D.host.F] x) = φ x • a := by
  rw [aux₃, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]

theorem evalV_pr (φ : D.host.E →ₗ[D.host.F] D.host.F) (v : Pl D) (y : AfE D) :
    evalV D.host.F v (pr φ y) = aux₃ φ v (cf v y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rw [pr_tmul, cf_tmul, trace_projection_tmul, AlgHom.map_smul_of_tower]
  | add y y' hy hy' => rw [LinearMap.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.map_add (f := _), hy, hy']

theorem trace_projection_mem_integers (φ : D.host.E →ₗ[D.host.F] D.host.F) (hφ : ∀ x : 𝓞 D.host.E, φ x ∈ (algebraMap (𝓞 D.host.F) D.host.F).range)
    (v : Pl D) {w : Ev D v} (hw : w ∈ intLoc D.host.F D.host.E v) : aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F := by
  refine intLoc_induction (p := fun w => aux₃ φ v w ∈ v.adicCompletionIntegers D.host.F) (fun a ha x => ?_) ?_
    (fun y z hy hz => ?_) (fun y hy => ?_) hw
  · obtain ⟨r, hr⟩ := hφ x
    rw [trace_projection_tmul, ← hr, Algebra.smul_def]
    exact mul_mem (v.coe_mem_adicCompletionIntegers r) ha
  · rw [LinearMap.map_zero]; exact zero_mem _
  · rw [LinearMap.map_add (f := _)]; exact add_mem hy hz
  · rw [LinearMap.map_neg]; exact neg_mem hy

theorem sum_pr {k : ℕ} (s : Fin k → 𝓞 D.host.E) (φ : Fin k → D.host.E →ₗ[D.host.F] D.host.F)
    (hsum : ∀ x, ∑ j, φ j x • (s j : D.host.E) = x) (y : AfE D) :
    ∑ j, pr (φ j) y ⊗ₜ[D.host.F] ((s j : D.host.E)) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [pr_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum, hsum x]
  | add y y' hy hy' => simp only [LinearMap.map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hy, hy']

theorem mem_of_cf_mem {z : AfE D} (hz : ∀ v : Pl D, cf v z ∈ intLoc D.host.F D.host.E v) : z ∈ intAE D := by
  obtain ⟨k, s, φ, hφ, hsum⟩ := GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := D.host.F) (E := D.host.E)
  rw [← sum_pr s φ hsum z]
  refine sum_mem fun j _ => AddSubgroup.subset_closure ⟨pr (φ j) z, fun v => ?_, s j, rfl⟩
  rw [evalV_pr]
  exact trace_projection_mem_integers (φ j) (fun x => hφ x j) v (hz v)

theorem exists_nat_mul_mem {Q : Set (AfE D)} (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ q ∈ Q, (N : AfE D) * q ∈ intAE D := by
  have : IsModuleTopology (Af D.host.F) (AfE D) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AfE D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover (fun n : ℕ => {q : AfE D | ((n + 1 : ℕ) : AfE D) * q ∈ intAE D})
    (fun n => (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_const.mul continuous_id))
    (fun q _ => by
      obtain ⟨n, hn, h⟩ := GlobalTheory.IwaPlace.SdComap.exists_natCast_mul_mem_intAE q
      exact Set.mem_iUnion.2 ⟨n - 1, by rwa [Nat.sub_add_cancel hn]⟩)
  refine ⟨∏ n ∈ t, (n + 1), Finset.prod_pos fun _ _ => Nat.succ_pos _, fun q hq => ?_⟩
  obtain ⟨n, hn, hq'⟩ := Set.mem_iUnion₂.1 (ht hq)
  rw [← Finset.mul_prod_erase t _ hn, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : AfE D), mul_assoc]
  exact GlobalTheory.HostAdeleIso.intAE_mul_mem D (GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE _) hq'

def U (S : Finset (Pl D)) (ef : AfE D) (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (AfE D)) where
  carrier := {w | (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D}
  add_mem' := fun {a b} ha hb => ⟨fun v hv i j => by
      rw [Matrix.add_apply, map_add (f := _)]; exact add_mem (ha.1 v hv i j) (hb.1 v hv i j),
    fun i j => by rw [Matrix.add_apply, mul_add, mul_add]; exact add_mem (ha.2 i j) (hb.2 i j)⟩
  zero_mem' := ⟨fun v _ i j => by rw [Matrix.zero_apply, map_zero]; exact zero_mem _,
    fun i j => by rw [Matrix.zero_apply, mul_zero, mul_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun v hv i j => by rw [Matrix.neg_apply, map_neg]; exact neg_mem (ha.1 v hv i j),
    fun i j => by rw [Matrix.neg_apply, mul_neg, mul_neg]; exact neg_mem (ha.2 i j)⟩

theorem mem_U {S : Finset (Pl D)} {ef : AfE D} {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)} :
    w ∈ U S ef N m n ↔ (∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, (N : AfE D) * (ef * w i j) ∈ intAE D := Iff.rfl


open Classical in
theorem mem_U_iff {S : Finset (Pl D)} {ef : AfE D} (hef : ef * ef = ef)
    (hS : ∀ v : Pl D, cf v ef = if v ∈ S then 1 else 0) {N m n : ℕ} {w : Matrix (Fin m) (Fin n) (AfE D)}
    (hw : ∀ v ∉ S, ∀ i j, cf v (w i j) ∈ intLoc D.host.F D.host.E v) :
    w ∈ U S ef N m n ↔ (Matrix.of fun i j => ef * w i j) ∈ U S ef N m n := by
  have h2 : ∀ i j, (N : AfE D) * (ef * (Matrix.of fun i j => ef * w i j) i j) = (N : AfE D) * (ef * w i j) :=
    fun i j => by rw [Matrix.of_apply, ← mul_assoc ef ef, hef]
  rw [mem_U, mem_U]
  simp only [h2]
  refine ⟨fun h => ⟨fun v hv i j => ?_, h.2⟩, fun h => ⟨hw, h.2⟩⟩
  rw [Matrix.of_apply, map_mul, hS v, if_neg hv, zero_mul]
  exact zero_mem _

end PositivityTheory.Rg.Rsw.L.LBumpEx

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKC
section
noncomputable section

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, finEmb_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sigR_mem (σ : E →ₐ[F] E) {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : sigR (Fv F v) σ y ∈ intLoc F E v := sigR_mem_intLoc σ hy

def sR (σ : E →ₐ[F] E) : intLoc F E v →+* intLoc F E v :=
  ((sigR (Fv F v) σ).comp (intLoc F E v).subtype).codRestrict (intLoc F E v) fun y => sigR_mem v σ y.2

@[simp] theorem coe_sR (σ : E →ₐ[F] E) (y : intLoc F E v) : (sR v σ y : Fv F v ⊗[F] E) = sigR (Fv F v) σ y := rfl

theorem absBar_le_one (τ : E →ₐ[F] FvBar F v) (y : intLoc F E v) : absBar F v (finEmb F v τ y) ≤ 1 := (le_absFin F v τ y).trans (absFin_le_one_of_mem_intLoc y.2)

def p0 (τ : E →ₐ[F] FvBar F v) : Ideal (intLoc F E v) where
  carrier := {y | absBar F v (finEmb F v τ y) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add, map_add (f := _)] at *
    exact (absBar_add_le F v _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, map_zero]
    rw [(absBar_eq_zero F v).2 rfl]; exact zero_lt_one
  smul_mem' := by
    intro c y hy
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul, absBar_mul] at *
    calc absBar F v (finEmb F v τ c) * absBar F v (finEmb F v τ y) ≤ 1 * absBar F v (finEmb F v τ y) :=
          mul_le_mul_of_nonneg_right (absBar_le_one v τ c) zero_le
      _ < 1 := by rw [one_mul]; exact hy

theorem absBar_finEmb_one (τ : E →ₐ[F] FvBar F v) : absBar F v (finEmb F v τ 1) = 1 := by
  rw [map_one]; simpa using absBar_algebraMap F v 1

theorem prime_valuation_ne_top (τ : E →ₐ[F] FvBar F v) : p0 v τ ≠ ⊤ := by
  intro h
  have : (1 : intLoc F E v) ∈ p0 v τ := h ▸ Submodule.mem_top
  change absBar F v (finEmb F v τ ((1 : intLoc F E v) : Fv F v ⊗[F] E)) < 1 at this
  rw [OneMemClass.coe_one, absBar_finEmb_one] at this
  exact lt_irrefl _ this

theorem isUnit_of_absBar (y : intLoc F E v) (h : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ y) = 1) :
    IsUnit y := by
  have hne : ∀ τ : E →ₐ[F] FvBar F v, finEmb F v τ (y : Fv F v ⊗[F] E) ≠ 0 := by
    intro τ h0
    have h1 := h τ
    rw [h0, (absBar_eq_zero F v).2 rfl] at h1
    exact zero_ne_one h1
  have hinj : Function.Injective (LinearMap.mulLeft (Fv F v) (y : Fv F v ⊗[F] E)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [LinearMap.mulLeft_apply] at hz
    apply absFin_eq_zero_iff.1
    refine le_antisymm (Finset.sup_le fun τ _ => ?_) bot_le
    have h1 := congrArg (finEmb F v τ) hz
    rw [map_mul, map_zero] at h1
    rw [le_zero_iff, absBar_eq_zero]
    exact (mul_eq_zero.1 h1).resolve_left (hne τ)
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  rw [LinearMap.mulLeft_apply] at hz
  have hzmem : z ∈ intLoc F E v := by
    rw [mem_intLoc_iff_absFin_le_one]
    refine Finset.sup_le fun τ _ => ?_
    have e1 := absBar_finEmb_one v τ
    have h1 := congrArg (fun w => absBar F v (finEmb F v τ w)) hz
    simp only [map_mul, absBar_mul, h τ, one_mul] at h1
    rw [h1, e1]
  exact isUnit_iff_exists_inv.2 ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

theorem emb_cases (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) (τ0 τ : E →ₐ[F] FvBar F v) :
    τ = τ0 ∨ τ = τ0.comp σ := by
  classical
  by_contra hne
  push_neg at hne
  have hd : τ0 ≠ τ0.comp σ := by
    intro h
    apply hσ1
    ext x
    have hx : τ0 x = τ0 (σ x) := congrArg (fun g => g x) h
    exact (τ0.injective hx).symm
  have hc := card_algHom_le_finrank F E (FvBar F v)
  rw [h2, ← Fintype.card_eq_nat_card] at hc
  have h3 : ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hd]
    simp [hne.1, hne.2]
  have h4 := Finset.card_le_univ ({τ, τ0, τ0.comp σ} : Finset (E →ₐ[F] FvBar F v))
  omega

theorem exists_max (σ : E →ₐ[F] E) (hσ1 : σ ≠ AlgHom.id F E) (h2 : Module.finrank F E = 2) :
    ∃ 𝔭 : Ideal (intLoc F E v), 𝔭.IsMaximal ∧ ∀ x, x ∉ 𝔭 → sR v σ x ∉ 𝔭 → IsUnit x := by
  have τ0 : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal _ (prime_valuation_ne_top v τ0)
  refine ⟨𝔭, hmax, fun x hx hsx => isUnit_of_absBar v x fun τ => ?_⟩
  have hone : ∀ w : intLoc F E v, w ∉ 𝔭 → absBar F v (finEmb F v τ0 w) = 1 := by
    intro w hw
    exact le_antisymm (absBar_le_one v τ0 w) (not_lt.1 fun hlt => hw (hle (show w ∈ p0 v τ0 from hlt)))
  rcases emb_cases v σ hσ1 h2 τ0 τ with rfl | rfl
  · exact hone x hx
  · have h5 := hone _ hsx
    rwa [coe_sR, finEmb_sigR] at h5

theorem isUnit_two (h : (2 : 𝓞 F) ∉ v.asIdeal) : IsUnit (2 : intLoc F E v) := by
  have hv : Valued.v (2 : Fv F v) = 1 := by
    have e : (2 : Fv F v) = ((2 : F) : Fv F v) := by
      rw [show (2 : F) = 1 + 1 by norm_num, HeightOneSpectrum.adicCompletion.coe_add,
        HeightOneSpectrum.adicCompletion.coe_one]
      norm_num
    have e2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat (algebraMap (𝓞 F) F) 2).symm
    rw [e, HeightOneSpectrum.adicCompletion.valued_coe, e2, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact h
  have hmem : (2 : Fv F v)⁻¹ ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have h0 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have h2 : (2 : Fv F v ⊗[F] E) = (2 : Fv F v) ⊗ₜ[F] (1 : E) := by
    rw [show (2 : Fv F v) = 1 + 1 by norm_num, TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    norm_num
  have hc : ((2 : intLoc F E v) : Fv F v ⊗[F] E) = 2 := by
    first
    | rfl
    | norm_cast
    | simp
  refine isUnit_iff_exists_inv.2 ⟨⟨_, tmul_mem_intLoc hmem (1 : 𝓞 E)⟩, Subtype.ext ?_⟩
  push_cast
  rw [hc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ h0, one_mul,
    ← Algebra.TensorProduct.one_def]

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEvB
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LGoodEv

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

variable {D : D7}


open Classical in
theorem exists_int_off {K : Set (Af D.host.F)} (hK : IsCompact K) :
    ∃ T : Finset (Pl D), ∀ z ∈ K, ∀ v ∉ T, z v ∈ v.adicCompletionIntegers D.host.F := by
  classical
  let O : Finset (Pl D) → Set (Af D.host.F) :=
    fun T => {z | ∀ v, v ∉ T → z v ∈ (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))}
  have hO : ∀ T, IsOpen (O T) := fun T =>
    RestrictedProduct.isOpen_forall_imp_mem (R := fun v : Pl D => v.adicCompletion D.host.F)
      (A := fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have hcov : K ⊆ ⋃ T, O T := fun z _ => Set.mem_iUnion.2
    ⟨(Filter.eventually_cofinite.1 z.2).toFinset, fun v hv => by
      by_contra h
      exact hv ((Filter.eventually_cofinite.1 z.2).mem_toFinset.2 h)⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover O hO hcov fun T T' =>
    ⟨T ∪ T', fun z hz v hv => hz v fun h => hv (Finset.mem_union_left _ h),
      fun z hz v hv => hz v fun h => hv (Finset.mem_union_right _ h)⟩
  exact ⟨T, fun z hz v hv => hT hz v hv⟩

def sPart {a b : ℕ} (S : Finset (Pl D)) (y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :
    Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E :=
  fun i j => algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (indS S) * y i j


open Classical in
set_option maxHeartbeats 800000 in
theorem fin_good {a b : ℕ} (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ y, g y =
      if (∀ v ∉ S, ∀ i j, projV v y i j ∈ intLoc D.host.F D.host.E v)
      then g (sPart S y) else 0 := by
  classical
  obtain ⟨hlc, hcs⟩ := hg
  let B := Module.finBasis D.host.F D.host.E
  have hT1 : ∀ (i : Fin a) (j : Fin b) (k : Fin (Module.finrank D.host.F D.host.E)), ∃ T : Finset (Pl D),
      ∀ y ∈ tsupport g, ∀ v ∉ T, crd B (Af D.host.F) (y i j) k v ∈ v.adicCompletionIntegers D.host.F := by
    intro i j k
    have hc : Continuous fun y : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E => y i j :=
      (continuous_apply j).comp (continuous_apply i)
    obtain ⟨T, hT⟩ := exists_int_off (D := D) (hcs.isCompact.image ((continuous_crd B (Af D.host.F) k).comp hc))
    exact ⟨T, fun y hy v hv => hT _ ⟨y, hy, rfl⟩ v hv⟩
  choose T1 hT1 using hT1
  have hU := invariant_mem_nhds hlc hcs
  let Lc : (Fin a → Fin b → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) →
      (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af D.host.F) ⊗ₜ[D.host.F] B k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af D.host.F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T2, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  have hinv : ∀ x u, (∀ i j k v, crd B (Af D.host.F) (u i j) k v ∈ P v) → g (x + u) = g x := by
    intro x u hu
    have hu' : u = Lc fun i j k => crd B (Af D.host.F) (u i j) k := by
      funext i j
      exact eq_sum_crd B (Af D.host.F) (u i j)
    rw [hu']
    exact h1 _ (fun i => h2 _ fun j => h3 _ fun k => hsub (hu i j k)) x
  have hbad := Filter.eventually_cofinite.1 (GlobalTheory.AdelicU.Cofinite.eventually_mem_intLoc_iff_repr B)
  refine ⟨(Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => Finset.univ.biUnion fun k => T1 i j k) ∪ T2 ∪
    hbad.toFinset, fun S hS y => ?_⟩
  have hS1 : ∀ i j k, T1 i j k ⊆ S := fun i j k v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hv⟩⟩⟩)))
  have hS2 : T2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : ∀ v ∉ S, ∀ z : Fv D.host.F v ⊗[D.host.F] D.host.E, z ∈ intLoc D.host.F D.host.E v ↔
      ∀ k, crd B (Fv D.host.F v) z k ∈ v.adicCompletionIntegers D.host.F := by
    intro v hv
    have h' : v ∉ hbad.toFinset := fun h => hv (hS (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h'
    exact h'
  have hcrd : ∀ z k, crd B (Af D.host.F) (z - algebraMap (Af D.host.F) _ (indS S) * z) k =
      crd B (Af D.host.F) z k - indS S * crd B (Af D.host.F) z k := by
    intro z k
    simp only [crd, ← Algebra.smul_def, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs with h
  · calc g y = g (sPart S y + (y - sPart S y)) := by rw [add_sub_cancel]
      _ = g (sPart S y) := hinv _ _ fun i j k v => ?_
    have e1 : crd B (Af D.host.F) ((y - sPart S y) i j) k v =
        crd B (Af D.host.F) (y i j) k v - indS S v * crd B (Af D.host.F) (y i j) k v := by
      rw [Pi.sub_apply, Pi.sub_apply, sPart, hcrd]
      rfl
    rw [e1, indS_apply]
    by_cases hv : v ∈ S
    · rw [if_pos hv, one_mul, sub_self]
      exact zero_mem _
    · rw [if_neg hv, zero_mul, sub_zero, hPT v fun h' => hv (hS2 h'), mem_intSub, ← crd_projV]
      exact (hS3 v hv _).1 (h v hv i j) k
  · push Not at h
    obtain ⟨v, hv, i, j, hij⟩ := h
    obtain ⟨k, hk⟩ : ∃ k, crd B (Fv D.host.F v) (projV v y i j) k ∉ v.adicCompletionIntegers D.host.F := by
      by_contra hc
      push Not at hc
      exact hij ((hS3 v hv _).2 hc)
    rw [crd_projV] at hk
    refine image_eq_zero_of_notMem_tsupport fun hy => hk ?_
    exact hT1 i j k y hy v fun h' => hv (hS1 i j k h')

end PositivityTheory.Rg.Rsw.L.LGoodEv

end
end

