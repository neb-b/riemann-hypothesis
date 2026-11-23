module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfIsSubFam
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory

theorem subIner_component_mem {L Y I α : Type} [Field L] [AddCommGroup Y] [Module L Y]
    (T : I → Y →ₗ[L] Y) (χ : α → I → L) (hχ : Function.Injective χ) (U : Submodule L Y)
    (hU : ∀ g, ∀ y ∈ U, T g y ∈ U) (S : Finset α) :
    ∀ y : α → Y, (∀ a ∈ S, ∀ g, T g (y a) = χ a g • y a) → ∑ a ∈ S, y a ∈ U → ∀ a ∈ S, y a ∈ U := by
  first
  | exact @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem
  | (apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvectorOfSum.eigenvector_mem_of_sum_mem ..)

theorem subIner_pullback {L X Y I α J : Type} [Field L] [AddCommGroup X] [Module L X]
    [AddCommGroup Y] [Module L Y] (T : I → X →ₗ[L] X) (T' : J → I → Y →ₗ[L] Y)
    (m : J → X →ₗ[L] Y) (hm : ∀ j g x, m j (T g x) = T' j g (m j x))
    (hinj : ∀ x, (∀ j, m j x = 0) → x = 0)
    (χ : α → I → L) (hχ : Function.Injective χ) (D : Submodule L X)
    (hD : ∀ g, ∀ x ∈ D, T g x ∈ D) (S : Finset α) (d : X) (hd : d ∈ D)
    (y : J → α → Y) (hy : ∀ j, ∀ a ∈ S, ∀ g, T' j g (y j a) = χ a g • y j a)
    (hs : ∀ j, ∑ a ∈ S, y j a = m j d) :
    ∃ x : α → X, (∀ a ∈ S, x a ∈ D ∧ ∀ g, T g (x a) = χ a g • x a) ∧ ∑ a ∈ S, x a = d := by
  classical
  have key := subIner_component_mem (Y := J → Y)
    (fun g => LinearMap.pi fun j => (T' j g).comp (LinearMap.proj j)) χ hχ (D.map (LinearMap.pi m))
    (by
      rintro g _ ⟨x, hx, rfl⟩
      exact ⟨T g x, hD g x hx, by ext j; simp [hm]⟩) S (fun a j => y j a)
    (fun a ha g => by ext j; simp [hy j a ha g])
    ⟨d, hd, by ext j; simp [← hs j, Finset.sum_apply]⟩
  have h1 : ∀ a, ∃ x : X, a ∈ S → x ∈ D ∧ ∀ j, m j x = y j a := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨x, hx, e⟩ := key a ha
      exact ⟨x, fun _ => ⟨hx, fun j => congrFun e j⟩⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose x hx using h1
  refine ⟨x, fun a ha => ⟨(hx a ha).1, fun g => ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    rw [map_sub, hm, map_smul, (hx a ha).2, hy j a ha, sub_self]
  · rw [← sub_eq_zero]
    refine hinj _ fun j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← hs j, sub_eq_zero]
    exact Finset.sum_congr rfl fun a ha => (hx a ha).2 j

theorem subIner_rTensor_inj {Qp LL B V U : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [AddCommGroup B] [Module Qp B]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {n : ℕ} (p : Fin n → V →ₗ[LL] U) (hp : ∀ v, (∀ j, p j v = 0) → v = 0) (x : V ⊗[Qp] B)
    (hx : ∀ j, AlgebraTensorModule.rTensor Qp B (p j) x = 0) : x = 0 := by
  obtain ⟨q, hq⟩ := (LinearMap.pi p).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot'.2 fun v hv => hp v fun j => congrFun hv j)
  have h1 : ∀ v, ∑ j, q (Pi.single j (p j v)) = v := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single]
    exact LinearMap.congr_fun hq v
  have h2 : ∀ z : V ⊗[Qp] B, ∑ j, AlgebraTensorModule.rTensor Qp B
      (q.comp (LinearMap.single LL (fun _ => U) j)) (AlgebraTensorModule.rTensor Qp B (p j) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      conv_rhs => rw [← h1 v, TensorProduct.sum_tmul]
      simp
    | add z w hz hw => simp only [map_add (f := _), Finset.sum_add_distrib, hz, hw]
  rw [← h2 x]
  simp [hx]

section General

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem subIner_mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h ∈ PC.H, actVB PC.PD ρ h x = x := by
  have h1 : ∀ (h : PC.H) (z : V ⊗[Qp] B), actVB PC.PD' (PC.resH ρ) h z = actVB PC.PD ρ h z := by
    intro h z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
    | add z w hz hw => simp only [map_add (f := _), hz, hw]
  simp [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, sub_eq_zero, h1]

theorem subIner_actVB_mul (ρ : Representation LL G V) (g h : G) (z : V ⊗[Qp] B) :
    actVB PC.PD ρ g (actVB PC.PD ρ h z) = actVB PC.PD ρ (g * h) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

theorem subIner_Dpcris_stable (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) : actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [subIner_mem_Dpcris] at hx ⊢
  intro h hh
  have h1 := hx (g⁻¹ * h * g⁻¹⁻¹) (PC.normal.conj_mem h hh g⁻¹)
  conv_rhs => rw [← h1]
  rw [subIner_actVB_mul, subIner_actVB_mul]
  congr 2
  group

theorem subIner_rTensor_actVB (ρ : Representation LL G V) (σ : Representation LL G U)
    (f : V →ₗ[LL] U) (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (z : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PC.PD ρ g z) =
      actVB PC.PD σ g (AlgebraTensorModule.rTensor Qp B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

theorem subIner_mem_Eig (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ) (x : V ⊗[Qp] B) :
    x ∈ PC.Eig ρ I a ↔ x ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ g x = ((a g : LLˣ) : LL) • x := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, sub_eq_zero]

theorem subIner_Dpcris_eq (ρ : Representation LL G V) {n : ℕ} (σ : Fin n → Representation LL G U)
    (p : Fin n → V →ₗ[LL] U) (hp : ∀ j g v, p j (ρ g v) = σ j g (p j v))
    (hinj : ∀ v, (∀ j, p j v = 0) → v = 0) (I : Subgroup G) (Sig : Finset (I →* LLˣ))
    (hσ : ∀ j, PC.Dpcris (σ j) = ⨆ a ∈ Sig, PC.Eig (σ j) I a) :
    PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ I a := by
  refine le_antisymm (fun d hd => ?_) (iSup₂_le fun a _ => inf_le_left)
  have h1 : ∀ j, ∃ μ : ∀ a, PC.Eig (σ j) I a,
      ∑ a ∈ Sig, (μ a : U ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B (p j) d := by
    intro j
    rw [← Submodule.mem_iSup_finset_iff_exists_sum, ← hσ j, subIner_mem_Dpcris]
    intro h hh
    rw [← subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j), (subIner_mem_Dpcris PC ρ d).1 hd h hh]
  choose μ hμ using h1
  obtain ⟨x, hx, rfl⟩ := subIner_pullback (fun g : I => actVB PC.PD ρ g)
    (fun j (g : I) => actVB PC.PD (σ j) g) (fun j => AlgebraTensorModule.rTensor Qp B (p j))
    (fun j g z => subIner_rTensor_actVB PC ρ (σ j) (p j) (hp j) g z)
    (subIner_rTensor_inj p hinj) (fun (a : I →* LLˣ) g => ((a g : LLˣ) : LL))
    (fun a b hab => MonoidHom.ext fun g => Units.ext (congrFun hab g)) (PC.Dpcris ρ)
    (fun g z hz => subIner_Dpcris_stable PC ρ g z hz) Sig d hd (fun j a => μ j a)
    (fun j a _ g => ((subIner_mem_Eig PC (σ j) I a _).1 (μ j a).2).2 g) hμ
  refine Submodule.sum_mem _ fun a ha => ?_
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha
    ((subIner_mem_Eig PC ρ I a _).2 (hx a ha)))

end General

theorem inertiaThrough_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p) → (∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig) → (pc P h hN hF hS).InertiaThrough W.ρ Sig := by
  intro l _ P K K' LL h hN hF hS ι k Ms W hW Sig h1 h2 h3
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine ⟨h1, h2, ?_⟩
  exact subIner_Dpcris_eq (pc P h hN hF hS) W.ρ (fun j => matRep (Ms (x j))) p
    (fun j g v => by rw [hp]; simp [matRep]) hinj _ Sig fun j => (h3 (x j)).2.2

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

section TwistDeRham

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem deRhamTwist_galoisAct_period (g : G) :
    PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := by
  rw [← PD.ι_comm, PD.t_act, ← algebraMap_smul K₀ ((PD.χ g : Qpˣ) : Qp) PD.t, map_smul,
    algebraMap_smul]

theorem drTwist_pow_mem (e : ℕ) : (PD.ι PD.t) ^ e ∈ PD.Fil (e : ℤ) := by
  induction e with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact_mod_cast PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one

theorem drTwist_Fil_le (e : ℕ) : PD.Fil (e : ℤ) ≤ PD.Fil 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    exact_mod_cast PD.Fil_anti (n : ℤ)

noncomputable def drTwistMap (e : ℕ) : K →ₗ[Qp] BdR :=
  (LinearMap.mulRight Qp ((PD.ι PD.t) ^ e)) ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem drTwistMap_apply (e : ℕ) (k : K) :
    drTwistMap PD e k = algebraMap K BdR k * (PD.ι PD.t) ^ e := rfl

theorem drTwistMap_injective (e : ℕ) : Function.Injective (drTwistMap PD e) := by
  have hnt : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact PD.not_mem_filtration_two (by rw [Subsingleton.elim (PD.ι PD.t) 0]; exact Submodule.zero_mem _)
  intro a b hab
  rw [drTwistMap_apply, drTwistMap_apply] at hab
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  exact (algebraMap K BdR).injective (hu.mul_right_cancel hab)

theorem drTwistMap_mem (e : ℕ) (k : K) : drTwistMap PD e k ∈ PD.Fil 0 := by
  rw [drTwistMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (drTwist_Fil_le PD e (drTwist_pow_mem PD e))

theorem drTwist_act_pow (e : ℕ) (g : G) :
    PD.actdR g ((PD.ι PD.t) ^ e) = ((PD.χ g : Qpˣ) : Qp) ^ e • (PD.ι PD.t) ^ e := by
  rw [map_pow, deRhamTwist_galoisAct_period, smul_pow]

theorem drTwistMap_fixed (e : ℕ) (g : G) (k : K) :
    (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (drTwistMap PD e k) = drTwistMap PD e k := by
  rw [drTwistMap_apply, map_mul, AlgEquiv.commutes, drTwist_act_pow, mul_smul_comm, smul_smul,
    ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul]

theorem drTwistMap_range (e : ℕ) (y : BdR)
    (hy : ∀ g, (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y = y) :
    ∃ k, drTwistMap PD e k = y := by
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  have hyz : y = (y * z) * (PD.ι PD.t) ^ e := by rw [mul_assoc, hz, mul_one]
  obtain ⟨k, hk⟩ := PD.invdR (y * z) (fun g => by
    apply hu.mul_right_cancel
    have h := hy g
    rw [hyz, map_mul, drTwist_act_pow, mul_smul_comm, smul_smul,
      ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul] at h
    exact h)
  exact ⟨k, by rw [drTwistMap_apply, hk, ← hyz]⟩

variable {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V)

theorem drTwist_act_tmul (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (g : G) (v : V) (y : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] y) =
      v ⊗ₜ[Qp] ((((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y) := by
  have : actVdR PD ρ g (v ⊗ₜ[Qp] y) = ρ g v ⊗ₜ[Qp] PD.actdR g y := rfl
  rw [this, h, ← map_inv₀, ← map_pow, algebraMap_smul, smul_tmul]

theorem drTwist_range (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) =
      DdR PD ρ := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, AlgebraTensorModule.map_tmul, sub_eq_zero]
      intro g
      rw [drTwist_act_tmul PD ρ e h, drTwistMap_fixed]
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp V
    let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have hE : ∀ g (x : V ⊗[Qp] BdR) i, E (actVdR PD ρ g x) i =
        (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (E x i) := by
      intro g x i
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb, smul_add]
      | tmul v y =>
        rw [drTwist_act_tmul PD ρ e h]
        simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        rw [← algebraMap_smul K (b.repr v i) y, map_smul, algebraMap_smul, smul_comm]
    have hx' : x = E.symm (E x) := (E.symm_apply_apply x).symm
    rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    obtain ⟨k, hk⟩ := drTwistMap_range PD e (E x i) (fun g => by rw [← hE, hx g])
    exact ⟨b i ⊗ₜ k, by rw [AlgebraTensorModule.map_tmul, hk]; rfl⟩

end TwistDeRham

theorem isDR_and_DdR_le_Fil_zero_of_twist : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (e : ℕ), (∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) → IsDR PD ρ ∧ DdR PD ρ ≤ FilV PD (LL := LL) (V := V) 0 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ _ ρ e h
  have hr := drTwist_range PD ρ e h
  constructor
  · have hinj : Function.Injective
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ (drTwistMap_injective PD e)
    have := PD.finK
    unfold IsDR
    rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct, mul_comm]
  · rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | tmul v k => exact ⟨v ⊗ₜ ⟨drTwistMap PD e k, drTwistMap_mem PD e k⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

theorem isOpen_of_fg_of_span_eq_top {LL O V : Type} [Field LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (hO : IsOpen (Set.range (algebraMap O LL))) (M : Submodule O V) (hfg : M.FG)
    (hspan : Submodule.span LL (M : Set V) = ⊤) : IsOpen (M : Set V) := by
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hbM : ∀ i, b i ∈ M := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective (Fintype.linearCombination LL b) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb,
      Submodule.span_span_of_tower]
  have hopen : IsOpenMap (Fintype.linearCombination LL b) :=
    IsModuleTopology.isOpenMap_of_surjective hsurj
  haveI := IsModuleTopology.topologicalAddGroup LL V
  have hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  refine M.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [Fintype.linearCombination_apply]
  refine M.sum_mem fun i _ => ?_
  obtain ⟨a, ha⟩ := hx i (Set.mem_univ i)
  rw [← ha, algebraMap_smul]
  exact M.smul_mem a (hbM i)

theorem locLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ T : LocLat G Qp LL O, IsOpen (T.L.T : Set T.V) := by
  intro G _ _ Qp _ _ LL _ _ _ O _ _ h T
  haveI := h.2.2.2.1
  exact isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUpUniMul
section
namespace GlobalTheory.UpperUnipotentMul

open Matrix

theorem isUpUni_mul {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hki | hik
    · rw [(hA i k).1 hki, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hik), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueAtEqUnitMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ValueTwoGen

def genSec {Y : Scheme.{0}} {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f := fun j => (t.s j).val
  compat := fun i j => congrArg Units.val (ht i j)

theorem exists_unit_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (t t' : LB.Gen M) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, (t'.s j).val =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom (w : Γ(Y, ⊤)) * (t.s j).val := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t' ht') t ht
  obtain ⟨w', hw', -⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t' ht'
  obtain ⟨_, -, hu⟩ := GlobalTheory.EvVal.existsUnique_sec_eq_mul_gen M hc (genSec t ht) t ht
  have h1 : (1 : Γ(Y, ⊤)) = w' * w := by
    have a := hu 1 (fun j => by simp [genSec])
    have b := hu (w' * w) (fun j => by
      have e1 := hw' j
      have e2 := hw j
      simp only [genSec] at e1 e2 ⊢
      rw [map_mul, _root_.mul_assoc, ← e2, ← e1])
    exact a.trans b.symm
  exact ⟨⟨w, w', by rw [_root_.mul_comm]; exact h1.symm, h1.symm⟩, fun j => hw j⟩

end GlobalTheory.ValueTwoGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerQEqMapKerTheta
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem kerQ_eq_map_ker_theta (l : ℕ) [Fact l.Prime] :
    Formalism.Per.kerP l = (RingHom.ker (Formalism.Per.θ l)).map
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)) := by
  refine le_antisymm (fun s hs => ?_)
    (Ideal.map_le_iff_le_comap.2 fun a ha => GlobalTheory.RingIface.alg_mem_kerP l ha)
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Formalism.Per.Ainf l) s
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l)
    ((l : ℕ) : Formalism.Per.Ainf l)).pow k
  have h0 : Formalism.Per.θP l s = 0 := GlobalTheory.RingBasics.fontaineTheta_eq_zero_of_mem_ker l s (by rwa [pow_one])
  have h1 : Formalism.Per.θP l (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) a) = 0 := by
    rw [← h, map_mul, h0, zero_mul]
  rw [GlobalTheory.RingIface.fontaineTheta_algebraMap] at h1
  have h2 : Formalism.Per.θ l a = 0 := Subtype.ext h1
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, h]
  exact Ideal.mem_map_of_mem _ h2

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  first | exact @GlobalTheory.span_cocycles_cyc_ext | exact GlobalTheory.span_cocycles_cyc_ext | (intros; apply GlobalTheory.span_cocycles_cyc_ext <;> assumption)
end

