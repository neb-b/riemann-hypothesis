module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsSpan

variable (D : D7) (S : RatDat D.ntw)

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := by
    simp only [actL, map_one, Units.val_one, inv_one, one_smul]
  map_mul' g h := by
    simp only [actL, map_mul, Units.val_mul, mul_inv]
    exact (smul_mul_smul_comm _ _ _ _).symm

def finiteLevelGroupFintype : Fintype (G0g D.nd) := Fintype.ofFinite _

attribute [local instance] finiteLevelGroupFintype

def opL (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem opL_of (j : ℕ) (g : G0g D.nd) : opL D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [opL, MonoidAlgebra.of_apply, actLHom]

theorem opL_eL (j : ℕ) : opL D S j (eL D) = ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g := by
  rw [finsum_eq_sum_of_fintype]
  simp [opL, eL, MonoidAlgebra.lift_apply, actLHom, Finsupp.sum_fintype]

variable {D S}

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h :=
  (actLHom D S j).map_mul g h

theorem eLop_idem (he : EIdem D) (j : ℕ) (x : S.WL j) :
    opL D S j (eL D) (opL D S j (eL D) x) = opL D S j (eL D) x := by
  rw [← Module.End.mul_apply, ← map_mul, he.1]

theorem eLop_comm (he : EIdem D) (j : ℕ) (g : G0g D.nd) (x : S.WL j) :
    opL D S j (eL D) (actL D S j g x) = actL D S j g (opL D S j (eL D) x) := by
  rw [← opL_of D S j g, ← Module.End.mul_apply, ← map_mul, he.2 g, map_mul, Module.End.mul_apply]

def fintypeU : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _

attribute [local instance] fintypeU


variable (D) in
def cU (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : ↥(Formalism.IndefR.NX.U D.nd)) : ↥D.LL0 :=
  (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * ((psiUOf D.nd (NX.xiRed D) θ u⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

theorem cU_mul (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u' u : ↥(Formalism.IndefR.NX.U D.nd)) :
    ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) * cU D θ (u' * u) = cU D θ u := by
  unfold cU
  rw [mul_inv_rev, map_mul, Units.val_mul, map_inv (psiUOf D.nd (NX.xiRed D) θ) u', Units.val_inv_eq_inv_val]
  have h0 : ((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
  field_simp

def projL (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), ((cU D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j u

theorem projL_isot (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u' : ↥(Formalism.IndefR.NX.U D.nd)) (w : S.WL j) :
    actL D S j u' (projL (S := S) θ j w) =
      (((psiUOf D.nd (NX.xiRed D) θ u' : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • projL (S := S) θ j w := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [projL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, actL_mul, Module.End.mul_apply]
  congr 1
  rw [← cU_mul θ u' u]
  push_cast
  ring

theorem goodL_of (he : EIdem D) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) (w : S.WL j) :
    opL D S j (eL D) (projL (S := S) θ j w) ∈ goodL D S θ j := by
  unfold goodL
  rw [← opL_eL, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨?_, fun u => ?_⟩
  · rw [Module.End.mem_eigenspace_iff, one_smul, eLop_idem he]
  · rw [Module.End.mem_eigenspace_iff, ← eLop_comm he, projL_isot, map_smul]

section KSide

variable (T : TwR D.LL0 D.nd)

def projT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ u : ↥(Formalism.IndefR.NX.U D.nd), readT D T i b (cU D In.θ u) • (actGT D T S In.rho In.chi i j b u).toLinearMap

theorem card_ne (i : T.Tw) (b : Bool) :
    readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := by
  refine (map_ne_zero (readT D T i b)).mpr fun h => ?_
  have h' := congrArg (fun x : ↥D.LL0 => (x : D.what₂.LL)) h
  exact Fintype.card_ne_zero (by exact_mod_cast h')

theorem projT_fix (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (z : FmT D T S i j b)
    (hz : z ∈ Fm0T D T S In.rho In.chi In.θ i j b) : projT T In i j b z = z := by
  have hu : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), actGT D T S In.rho In.chi i j b u z =
      readT D T i b ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • z := by
    intro u
    have h := (Submodule.mem_iInf _).mp hz u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  simp only [projT, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, hu, smul_smul, ← map_mul]
  have hc : ∀ u : ↥(Formalism.IndefR.NX.U D.nd), cU D In.θ u * ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) =
      (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ := by
    intro u
    unfold cU
    rw [map_inv, Units.val_inv_eq_inv_val]
    have h0 : ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) ≠ 0 := Units.ne_zero _
    field_simp
  simp only [hc, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have h1 : ((Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b (Fintype.card ↥(Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ = 1 := by
    rw [map_inv₀, ← map_natCast (readT D T i b)]
    exact mul_inv_cancel₀ (card_ne T i b)
  rw [h1, one_smul]

end KSide

theorem projT_phi (T : TwR D.LL0 D.nd) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (Φ : S.WL j →+ FmT D T S i j b)
    (hsl : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hact : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (w : S.WL j) : projT T In i j b (Φ w) = Φ (projL (S := S) In.θ j w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [projT, projL, LinearMap.sum_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_sum, hsl, hact]

theorem span_one_tmul {R A M : Type} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] :
    Submodule.span A (Set.range fun m : M => (1 : A) ⊗ₜ[R] m) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m =>
    have h : a ⊗ₜ[R] m = a • ((1 : A) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy


variable (S) in
def oneT (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) (w : ↥(WKr D S j)) : FmT D T S i j b :=
  (1 : KT D T i b) ⊗ₜ[S.Ks] w

theorem FmT_span (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (T.O i)) (Set.range (oneT S T i j b)) = ⊤ :=
  span_one_tmul (R := S.Ks) (A := KT D T i b) (M := ↥(WKr D S j))

end GlobalTheory.HeightCounting.FormsSpan


open GlobalTheory.HeightCounting.FormsSpan in
theorem GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    1 ≤ j → j ≤ D.R.m → EIdem D → ∀ (Φ : S.WL j →+ FmT D T S i j b),
    (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) →
    (∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x)) →
    (∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x)) →
    (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) →
    V0T D T S In.rho In.chi In.θ i j b ≤
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j))) := by
  intro D S In T i j b _ _ he Φ hsl hact hE h1 y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  rw [← projT_fix T In i j b z hz]
  have key : Submodule.span (FractionRing (T.O i))
      (Set.range (oneT S T i j b)) ≤
      (Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))).comap
        (eGT D T S In.rho In.chi i j b ∘ₗ projT T In i j b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    change eGT D T S In.rho In.chi i j b (projT T In i j b (oneT S T i j b w)) ∈
      Submodule.span (FractionRing (T.O i)) (Φ '' (goodL D S In.θ j : Set (S.WL j)))
    rw [show oneT S T i j b w = Φ (w : S.WL j) from (h1 w).symm, projT_phi T In i j b Φ hsl hact, ← hE, ← opL_eL]
    exact Submodule.subset_span ⟨_, goodL_of he In.θ j (w : S.WL j), rfl⟩
  exact key (Submodule.eq_top_iff'.mp (FmT_span (S := S) T i j b) z)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.HeckeValField

variable {E : Type} [Field E] [NumberField E]

def unitsIn (M : IntermediateField ℚ ℂ) : Subgroup ℂˣ where
  carrier := {z | (z : ℂ) ∈ M}
  one_mem' := by simpa using M.one_mem
  mul_mem' := fun {a b} ha hb => by simpa using M.mul_mem ha hb
  inv_mem' := fun {a} ha => by simpa using M.inv_mem ha

theorem mem_unitsIn {M : IntermediateField ℚ ℂ} {z : ℂˣ} : z ∈ unitsIn M ↔ (z : ℂ) ∈ M := Iff.rfl

theorem val_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v) : χ.val v ∈ unitsIn M := by
  have h := hM (IntermediateField.subset_adjoin ℚ (valueSet χ 0) ⟨v, hv, rfl⟩)
  exact mem_unitsIn.2 (by simpa [HChar.valTw] using h)

theorem loc_mem_of_unrAt (χ : HChar E) {G : Subgroup ℂˣ} {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v)
    (hval : χ.val v ∈ G) (y : (v.adicCompletion E)ˣ) : χ.loc v y ∈ G := by
  set π := atFin v (unif v)
  have hπ : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set k := WithZero.log (Valued.v (y : v.adicCompletion E))
  have hy : Valued.v (y : v.adicCompletion E) = WithZero.exp k := (WithZero.exp_log hy0).symm
  have hu : IsUnitAt v (y * π ^ k) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hy, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hv _ hu
  rw [map_mul, map_zpow] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact G.inv_mem (G.zpow_mem hval k)

theorem loc_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    (hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) :
    χ.loc v y ∈ unitsIn M := by
  classical
  set G := unitsIn M
  by_cases hv : χ.UnrAt v
  · exact loc_mem_of_unrAt χ hv (val_mem χ hM hv) y
  set R := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hR : ∀ w, w ∉ R → χ.UnrAt w := fun w hw => by
    by_contra h
    exact hw ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h)
  choose nf hnf using GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1
  set S := insert v R
  set N := S.sup nf
  obtain ⟨a, ha0, hav, haw⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E R v y N
  set k : Eˣ := Units.mk0 a ha0
  have h1 : χ.loc v y = χ.locK v k := by
    have hle : nf v ≤ N := Finset.le_sup (Finset.mem_insert_self v R)
    have e : χ.loc v (atFin v k * y⁻¹) = 1 := by
      apply hnf v
      refine le_trans ?_ (WithZero.exp_le_exp.mpr (by omega : -(N : ℤ) ≤ -(nf v : ℤ)))
      exact hav
    rw [map_mul, map_inv, mul_inv_eq_one] at e
    exact e.symm
  have h2 : ∀ w ∈ S, w ≠ v → χ.locK w k = 1 := by
    intro w hw hwv
    have hwR : w ∈ R := (Finset.mem_insert.1 hw).resolve_left hwv
    have hle : nf w ≤ N := Finset.le_sup hw
    apply hnf w
    have e : ((atFin w k : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        algebraMap E (w.adicCompletion E) (a - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e, PI.FinOrdValD.WA.val_alg]
    exact (haw w hwR hwv).trans (WithZero.exp_le_exp.mpr (by omega))
  have hpr := χ.productRule S (fun w hw => hR w fun h => hw (Finset.mem_insert_of_mem h)) k
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_insert_self v R) (fun w hw hwv => h2 w hw hwv)] at hpr
  have hF : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) ∈ G := by
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun w => ?_
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hw => ?_
    exact G.zpow_mem (val_mem χ hM (hR w fun h => hw (Finset.mem_insert_of_mem h))) _
  have h3 : χ.locK v k * (χ.inf k * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) = 1 := by
    rw [← hpr]; ac_rfl
  rw [h1, eq_inv_of_mul_eq_one_left h3]
  exact G.inv_mem (G.mul_mem (hinf k) hF)

theorem mem_of_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ),
    valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E,
      (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ χ M hM hinf x hx
  classical
  have hev : ∀ᶠ v in Filter.cofinite, Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (x.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x.val.2.2
    have h2 : ∀ᶠ v in Filter.cofinite, (x⁻¹.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x⁻¹.val.2.2
    filter_upwards [h1, h2] with v hv1 hv2
    have e1 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv1
    have e2 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv2
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at e2
    have h0 : 0 < Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
    exact le_antisymm e1 ((inv_le_one₀ h0).1 e2)
  have hfin := Filter.eventually_cofinite.1 hev
  set S := hfin.toFinset ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hS : ∀ v ∉ S, χ.1 (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := by
    intro v hv
    have hu : ¬ ¬ Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 :=
      fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
    have hr : χ.UnrAt v := by
      by_contra h
      exact hv (Finset.mem_union_right _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h))
    exact hr _ (not_not.1 hu)
  rw [GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 x S hS]
  have hinfx : GlobalTheory.HeckeSplit.infPart E x = 1 := Units.ext (funext fun w => hx w)
  rw [hinfx, map_one, map_one, one_mul]
  exact mem_unitsIn.1 ((unitsIn M).prod_mem fun v _ => loc_mem χ hM hinf v _)

end GlobalTheory.HeckeValField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section HeckeKill

variable (D : D7) (S : RatDat D.ntw)

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h := by
  unfold actL
  rw [map_mul, map_mul, map_mul, Units.val_mul, mul_inv, smul_mul_smul_comm]

theorem actL_one (j : ℕ) : actL D S j 1 = 1 := by
  unfold actL
  rw [map_one, map_one, map_one, Units.val_one, inv_one, one_smul]

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := actL_one D S j
  map_mul' := actL_mul D S j

def actAlg (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem actAlg_of (j : ℕ) (g : G0g D.nd) : actAlg D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [actAlg, MonoidAlgebra.of_apply, actLHom]

theorem actAlg_eL (j : ℕ) : actAlg D S j (eL D) = eLop D S j := by
  letI := Fintype.ofFinite (G0g D.nd)
  rw [eLop, finsum_eq_sum_of_fintype]
  simp [actAlg, eL, MonoidAlgebra.lift_apply, actLHom]
  rw [Finsupp.sum_fintype _ (fun a (b : D.what₂.LL) => b • actL D S j a) (fun _ => zero_smul _ _)]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1

theorem eLop_idem (j : ℕ) : eLop D S j * eLop D S j = eLop D S j := by
  rw [← actAlg_eL, ← map_mul, (eIdem_all D).1]

theorem eLop_comm (j : ℕ) (g : G0g D.nd) : eLop D S j * actL D S j g = actL D S j g * eLop D S j := by
  rw [← actAlg_eL, ← actAlg_of, ← map_mul, (eIdem_all D).2 g, map_mul]

theorem piCoef_shift (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (u w : Formalism.IndefR.NX.U D.nd) :
    piCoef D θ (u⁻¹ * w) = (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0)) * piCoef D θ w := by
  unfold piCoef
  rw [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  ring

theorem actL_piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u : Formalism.IndefR.NX.U D.nd) :
    actL D S j u * piLop D S θ j =
      ((((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) • piLop D S θ j := by
  letI := Fintype.ofFinite (Formalism.IndefR.NX.U D.nd)
  rw [piLop, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ v : Formalism.IndefR.NX.U D.nd,
      actL D S j u * (((piCoef D θ v : ↥D.LL0) : D.what₂.LL) • actL D S j (v : G0g D.nd)) =
        ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd) := by
    intro v
    rw [inv_mul_cancel_left, mul_smul_comm, Subgroup.coe_mul, actL_mul]
  simp_rw [h1]
  rw [Fintype.sum_equiv (Equiv.mulLeft u)
    (fun v => ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd))
    (fun w => ((piCoef D θ (u⁻¹ * w) : ↥D.LL0) : D.what₂.LL) • actL D S j (w : G0g D.nd)) (fun v => rfl)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [piCoef_shift, IntermediateField.coe_mul, mul_smul]

theorem eig_le_ker (In : RatIn D S) (j k : ℕ) (P : PlE D.host) (r : ↥D.LL0) (hr : r ∈ evRoots D S In j k P) :
    Module.End.eigenspace (In.hL j k P) ((r : ↥D.LL0) : D.what₂.LL) ≤ LinearMap.ker (phiLop D S In j k P) := by
  intro x hx
  rw [LinearMap.mem_ker]
  by_cases h0 : x = 0
  · rw [h0, map_zero]
  have hev : (In.hL j k P).HasEigenvector ((r : ↥D.LL0) : D.what₂.LL) x := Module.End.hasEigenvector_iff.mpr ⟨hx, h0⟩
  unfold phiLop
  rw [Module.End.aeval_apply_of_hasEigenvector hev, eval_map,
    show ((r : ↥D.LL0) : D.what₂.LL) = algebraMap ↥D.LL0 D.what₂.LL r from rfl, eval₂_at_apply]
  have he : (evPol D S In j k P).eval r = 0 := by
    unfold evPol
    rw [eval_prod]
    exact Finset.prod_eq_zero hr (by simp)
  rw [he, map_zero, zero_smul]

end HeckeKill

theorem phiLop_eLop_piLop : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  intro D S In j k P hj1 hj2 hk1 hk2 hsp hP
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hg : eLop D S j (piLop D S In.θ j y) ∈ goodL D S In.θ j := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change eLop D S j (piLop D S In.θ j y) ∈ Module.End.eigenspace (eLop D S j) 1
      rw [Module.End.mem_eigenspace_iff, one_smul, ← Module.End.mul_apply, eLop_idem]
    · refine Submodule.mem_iInf _ |>.mpr fun u => ?_
      rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← eLop_comm, Module.End.mul_apply,
        ← Module.End.mul_apply (actL D S j u), actL_piLop, LinearMap.smul_apply, map_smul]
  have hs := In.span j hj1 hj2 hg
  have hle : (⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S In.θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ In.Sb),
        Module.End.eigenspace (In.hL j k P) ((In.eig j σ k P : ↥D.LL0) : D.what₂.LL)) ≤
      LinearMap.ker (phiLop D S In j k P) := by
    refine iSup₂_le fun σ hσ => inf_le_right.trans ?_
    refine (iInf_le _ k).trans ((iInf_le _ P).trans ((iInf_le _ ⟨hk1, hk2, hsp, hP⟩).trans ?_))
    classical
    exact eig_le_ker D S In j k P _ (Finset.mem_image.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩, rfl⟩)
  exact LinearMap.mem_ker.mp (hle hs)

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.RaySize

theorem isEmpty_realEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : IsEmpty (E →+* ℝ) := by
  refine ⟨fun ψ => ?_⟩
  have h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ)) :=
    ⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h

theorem degOver_le_and_sz : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  intro E _ _ _ φ N M h hN
  haveI : NumberField M := h.numberField
  letI := algOf φ M h.emb_mem
  have hR : IsRayField E M (natIdeal E N) := h.isRayField
  haveI : IsAbelianGalois E M := hR.1
  have hdeg : degOver φ M h.emb_mem = Module.finrank E M := rfl
  have hfin := finrank_mul_degOver φ M h.emb_mem
  rw [hdeg] at hfin ⊢
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2
    haveI := isEmpty_realEmb E
    rwa [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [← hfin]
      have : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
      have : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    · have hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭 :=
        fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))
      have hmem := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun
      have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M)
        (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem
      have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hd : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc] at h2
      exact h2

end GlobalTheory.Mem.Fld.RaySize
end

