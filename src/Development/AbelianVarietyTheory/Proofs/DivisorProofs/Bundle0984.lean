module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.LfacDenominatorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0309
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingEquivariantGoodEmbedding
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.ReadingEquivGood

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem extendByOne_eq_one_of_trivial {M L : Type} [Group M] [Monoid L] (H : Subgroup M) (χ : H → L) (h : ∀ x, χ x = 1) (x : M) :
    Formalism.L2.DIV.ext1 H χ x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact h _
  · rfl

section
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem levChi_flag (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := extendByOne_eq_one_of_trivial _ _ (fun _ => rfl) _
  unfold Lev.levChi Formalism.L2.DIV.levFn
  rw [h2]
  show ((1 * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ ∅, _ : ℂˣ) : ℂ) = 1
  simp

theorem actW_apply {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (x : MMap (R.MW i σ)) (v : (R.MW i σ).Vec)
    (h : GA D (Wc D i)) : actW R i σ g x v h = x v (h * hk.choose) := by
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dite_eq_left hk]
  simp only [levChi_flag, inv_one, one_mul]

theorem actW_mem (hθ : IsInfFam R.θ) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (g : G) {x : MMap (R.MW i σ)}
    (hx : x ∈ R.Wall i σ) : actW R i σ g x ∈ R.Wall i σ :=
  GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) x hx _ fun _ => rfl

theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {x y : (R.HW i σ).H} {c : ℂ}
    (h : ∀ h, evAt R i σ v x h = c * actW R i σ g ((R.HW i σ).e y) v h) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  have hr : LinearMap.range (R.HW i σ).e = R.Wall i σ := (he i σ).2.1
  have h1 : c • actW R i σ g ((R.HW i σ).e y) ∈ LinearMap.range (R.HW i σ).e := by
    rw [hr]
    exact Submodule.smul_mem _ _ (actW_mem R hθ g (hr ▸ LinearMap.mem_range_self _ y))
  obtain ⟨z, hz⟩ := h1
  have h2 : x = z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv
      (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e z v h'
    rw [hz]
    exact h h'
  rw [h2, hz]

theorem chiIs_of_values {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g : G, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dite_eq_left hex]
  exact hex.choose_spec

theorem coe_chiC (i : Fin D.R.m) (g : G) : (chiC R i g : ℂ) =
    ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ) := by
  simp only [chiC, Units.coe_prod]

end

theorem phiC_eq (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiC T hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * phiAt T i σ hV (T.cE ((i : ℕ) + 1) σ) f h := by
  have key : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (g : GA D W), phiC T hV a f g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) f)) g := by
    intro W hV g
    subst hV
    rfl
  exact key _ hV h

theorem reading_equivariant : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ hσ
  by_cases hj : JEvAt T R κ v₀ i σ hV
  · have hq' : EqAt T R κ (O i) (res T σ) hV (T.cE ((i : ℕ) + 1) (res T σ)) := hq (res T σ) hσ hV
    have hc : ChiIs R i (chiTop R i) := chiIs_of_values R fun g' => by
      obtain ⟨-, y, hy, -⟩ := hq' g' _ (hl g').choose_spec 0 (zero_mem _)
      exact ⟨_, hy.trans (coe_chiC R i g').symm⟩
    obtain ⟨-, y, hy, h2⟩ := hq' g _ (hl g).choose_spec (f : T.R ((i : ℕ) + 1)) f.2
    have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
      D.what₂.embLL.injective ((hc g).trans ((coe_chiC R i g).trans hy.symm))
    have hs : σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = res T σ y := congrArg σ hy'
    refine equiv_of_values R hθ he (v := v₀ i σ) ((ht.hv₀ i σ).norm R) fun h => ?_
    have e1 := congrFun (jTop_good T R κ v₀ hσ hV hj (ρC g f)) h
    have e2 := congrFun (jTop_good T R κ v₀ hσ hV hj f) (h * (hl g).choose)
    have e3 := actW_apply R (hl g) ((R.HW i σ).e (jTop T R κ v₀ i σ f)) (v₀ i σ) h
    have e4 : phiC T hV (wtA (κ i)) ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) h =
        res T σ y * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * (hl g).choose) := by
      rw [hρ, phiC_eq, phiC_eq, h2, mul_left_comm]
    exact e1.trans (e4.trans (congrArg₂ (· * ·) hs.symm (e2.symm.trans e3.symm)))
  · rw [jTop_good0 T R κ v₀ hσ hV hj]
    simp

end GlobalTheory.ReadingEquivGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingEquivariantNotGoodEmbedding
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingConjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Model

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


set_option maxHeartbeats 1000000 in
theorem exists_lift_act {i : Fin D.R.m} (σ : D.what₂.LL →+* ℂ) {g : G}
    (hk : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (hchi : ∀ k, Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧
      ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k) := by
  refine ⟨hk.choose, hk.choose_spec, fun x v h => ?_⟩
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (x v) h = _
  unfold Lev.actG0
  rw [dite_eq_left hk]
  simp only [hchi, inv_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem exists_act_eq (hθ : IsInfFam R.θ) (he : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : G) (y : (R.HW i σ).H) :
    ∃ z, (R.HW i σ).e z = actW R i σ g ((R.HW i σ).e y) := by
  have h1 : (R.HW i σ).e y ∈ R.Wall i σ := (he i σ).2.1 ▸ LinearMap.mem_range_self _ y
  have h2 : actW R i σ g ((R.HW i σ).e y) ∈ R.Wall i σ :=
    GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity R.θ (R.MW i σ) hθ (R.βW i) (R.datWp i R.triv) (R.eG g) _ h1 _ fun _ => rfl
  rw [← (he i σ).2.1] at h2
  exact h2


set_option maxHeartbeats 1000000 in
theorem equiv_of_values (hθ : IsInfFam R.θ) (he : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec}
    (hv : IsUnitV v) {g : G} {k : GA D (Wc D i)} (hk : ∀ (x : MMap (R.MW i σ)) v h, actW R i σ g x v h = x v (h * k))
    {x y : (R.HW i σ).H} {c : ℂ} (h : ∀ h, evAt R i σ v x h = c * evAt R i σ v y (h * k)) :
    (R.HW i σ).e x = c • actW R i σ g ((R.HW i σ).e y) := by
  obtain ⟨z, hz⟩ := exists_act_eq R hθ he i σ g y
  have h4 : (R.HW i σ).e (c • z) = c • actW R i σ g ((R.HW i σ).e y) := by
    rw [← hz]; exact (R.HW i σ).e.map_smul _ _
  have h3 : x = c • z := by
    refine GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i σ) (R.HW i σ).H (R.HW i σ).e _ _ _ (he i σ).2.2 v hv (funext fun h' => ?_)
    show (R.HW i σ).e x v h' = (R.HW i σ).e (c • z) v h'
    rw [h4]
    exact (h h').trans (congrArg (c * ·) (hk _ v h').symm)
  exact (congrArg (R.HW i σ).e h3).trans h4

theorem chiTop_eq {i : Fin D.R.m} (h1 : ∀ g, ∃ a, D.what₂.embLL a = (chiC R i g : ℂ)) : ChiIs R i (chiTop R i) := by
  choose a ha using h1
  have hne : ∀ g, a g ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 (a g) (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dite_eq_left hex]
  exact hex.choose_spec

end Model


set_option maxHeartbeats 1000000 in
theorem reading_equiv_of_not_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → (∀ σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → ∀ (ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i)), (∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))) → ∀ σ : D.what₂.LL →+* ℂ, ¬ GoodEmb T.Q.c (res T σ) → ∀ g f, (R.HW i σ).e (jTop T R κ v₀ i σ (ρC g f)) = σ ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) • actW R i σ g ((R.HW i σ).e (jTop T R κ v₀ i σ f)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ he ht i hl hq ρC hρ σ hσ g f
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := ht.laws.spaceW _ (inR i) _ (good_resC T hσ)
  by_cases hj : JEvBarAt T R κ i σ hV
  swap
  · rw [top_lift_vanishes_off_good_embeddings T R κ v₀ hσ hV hj]
    simp
  obtain ⟨v, hv, h5⟩ := jTop_bar T R κ v₀ hσ hV hj
  have hE := hq _ (good_resC T hσ) hV
  have hchi : ChiIs R i (chiTop R i) := chiTop_eq R fun g' => by
    obtain ⟨k, hk⟩ := hl g'
    obtain ⟨-, y, hy, -⟩ := hE g' k hk 0 (zero_mem _)
    exact ⟨_, by rw [chiC, Units.coe_prod]; exact hy⟩
  obtain ⟨k, hk1, hk2⟩ := exists_lift_act R σ (hl g) (GlobalTheory.TiedUnif.levChi_flag_datWp i)
  obtain ⟨-, y, hy, h2⟩ := hE g k hk1 f f.2
  have hy' : ((chiTop R i g : D.what₂.LLˣ) : D.what₂.LL) = algebraMap T.Q.c.F D.what₂.LL y :=
    D.what₂.embLL.injective ((hchi g).trans (by rw [chiC, Units.coe_prod]; exact hy.symm))
  refine equiv_of_values R hθ he hv hk2 fun h => ?_
  rw [h5, h5]
  show starRingEnd ℂ _ = _ * starRingEnd ℂ _
  rw [hρ, GlobalTheory.TiedUnif.phiC_eq_phiAt, GlobalTheory.TiedUnif.phiC_eq_phiAt, h2, mul_left_comm, hy', map_mul]
  exact congrArg (· * _) (Complex.conj_conj _)

end GlobalTheory.ReadingConjEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseInvertibleAntidiagonalCornerDoubledUnitary
section
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

namespace GlobalTheory.SiegelDense

theorem prod_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {ι : Type} (s : Finset ι) (a b : ι → R) :
    ∏ i ∈ s, (e * a i + (1 - e) * b i) = e * ∏ i ∈ s, a i + (1 - e) * ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, ih]
    linear_combination (a i * ∏ j ∈ s, a j - a i * ∏ j ∈ s, b j - b i * ∏ j ∈ s, a j + b i * ∏ j ∈ s, b j) * he

theorem det_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) {m : Type} [Fintype m] [DecidableEq m]
    (A B : Matrix m m R) : (e • A + (1 - e) • B).det = e * A.det + (1 - e) * B.det := by
  simp only [Matrix.det_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [prod_idem he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h] <;> ring

theorem isUnit_mix {R : Type} [CommRing R] {e : R} (he : e * e = e) {a b : R} (ha : IsUnit (e * a + (1 - e)))
    (hb : IsUnit b) : IsUnit (e * a + (1 - e) * b) := by
  obtain ⟨u, rfl⟩ := hb
  have h1 : e * a + (1 - e) * (u : R) = (e * a + (1 - e)) * (e + (1 - e) * (u : R)) := by
    linear_combination (-a + a * (u : R) + 1 - (u : R)) * he
  have h2 : IsUnit (e + (1 - e) * (u : R)) := by
    refine isUnit_iff_exists_inv.mpr ⟨e + (1 - e) * ((u⁻¹ : Rˣ) : R), ?_⟩
    have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
    linear_combination (2 - (u : R) - ((u⁻¹ : Rˣ) : R)) * he + (1 - e) ^ 2 * hu
  rw [h1]
  exact ha.mul h2

theorem mix_corner {R : Type} [CommRing R] {n : ℕ} (e : R) (he : e * e = e) (A : Matrix (Fin n) (Fin n ⊕ Fin n) R)
    (B D' : Matrix (Fin n ⊕ Fin n) (Fin n) R) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (y : Matrix (Fin n) (Fin n) R)
    (hAB : A * B = (2 : R) • 1) (hAD : A * D' = 0) :
    A * (e • G + (1 - e) • 1) * B + A * (e • G + (1 - e) • 1) * D' * (e • y) =
      e • (A * G * B + A * G * D' * y) + (1 - e) • ((2 : R) • (1 : Matrix (Fin n) (Fin n) R)) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hAB, hAD,
    Matrix.zero_mul, smul_zero, add_zero, smul_smul, he, smul_add]
  simp only [Matrix.mul_assoc]
  abel

theorem approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀),
    ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀,
      (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) +
          (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧
      Tendsto q atTop (𝓝 g) :=
  GlobalTheory.T.exists_idempotentCutoff_tendsto_adelicUnitary

theorem unip : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R)
    {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 →
    ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) =
        diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧
      ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R,
        Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) *
            Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) =
          Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h *
              Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) +
            Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x :=
  _root_.GlobalTheory.siegel_unip_corner

theorem avoid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)),
    (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω),
      φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) →
    ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) +
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) :=
  GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value

theorem exists_corner : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e →
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 →
      ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) :=
  _root_.GlobalTheory.exists_corner_unit_of_right_inverse

theorem descend : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R),
    (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R),
    (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) →
      ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) →
    ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ),
      (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det →
      ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) →
        ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) :=
  _root_.GlobalTheory.exists_conj_skew_det_unit_of_avoidance

theorem dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ g : UG (cA σ) (dbl (incM F J)), g ∈ closure {h : UG (cA σ) (dbl (incM F J)) | ∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧ IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det} := by
  intro F E _ _ _ _ _ σ hσ n J ε hJ hdet g
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  letI : Invertible (2 : AE F E) := (Invertible.map (algebraMap F (AE F E)) (2 : F)).copy 2 (map_ofNat (algebraMap F (AE F E)) 2).symm
  obtain ⟨q, hq, hlim⟩ := approx F E σ (dbl (incM F J)) g
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun S => ?_)
  have he : algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
      = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := by
    rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hce : cA σ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) := (cA σ).commutes _
  have hav := avoid F E S

  have hNtN : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [Matrix.fromCols_mul_fromRows, two_smul]; simp
  have hNtD : Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = 0 := by
    rw [diagCols, Matrix.fromCols_mul_fromRows]; simp
  have hNN : Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) +
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
      (2 : AE F E) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [diagCols, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]

  obtain ⟨x₀, hx₀⟩ := exists_corner (F := F) _ he hav
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * g.1.1 *
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    ((⅟2 * ⅟2 : AE F E) • (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) *
      ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))))
    (by
      have hg : (g.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
          ((g.1⁻¹ : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = 1 := g.1.mul_inv
      rw [show ∀ (A : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E)) (B : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))
          (N₁ N₂ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) (T₁ T₂ : Matrix (Fin n) (Fin n ⊕ Fin n) (AE F E))
          (G H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (k : AE F E),
          A * G * N₁ * (k • (T₁ * H * B)) + A * G * N₂ * (k • (T₂ * H * B)) = k • (A * (G * ((N₁ * T₁ + N₂ * T₂) * (H * B)))) from
        fun A B N₁ N₂ T₁ T₂ G H k => by simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, smul_add]]
      rw [hNN, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc (g.1.1 : Matrix _ _ _), hg,
        Matrix.one_mul, hNtN, smul_smul, smul_smul,
        show ((⅟2 * ⅟2 : AE F E) * 2 * 2) = 1 by rw [mul_assoc (⅟2 : AE F E) (⅟2) 2, invOf_mul_self, mul_one, invOf_mul_self],
        one_smul])

  obtain ⟨y, hy⟩ : ∃ y : E, σ y ≠ y := by
    by_contra h
    push_neg at h
    exact GlobalTheory.HeckeObjectExamples.sigma_ne_id hσ (AlgHom.ext h)
  have hinv : ∀ z, σ (σ z) = z := GlobalTheory.HeckeObjectExamples.sigma_invol hσ
  have hcincl : ∀ z : E, cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := fun z => by
    change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] z) = (1 : AF F) ⊗ₜ[F] σ z
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hρu : IsUnit (inclR (F := F) (AF F) (y - σ y)) :=
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hy))).map _
  have hcρ : (cA σ).toRingHom (inclR (F := F) (AF F) (y - σ y)) = -inclR (F := F) (AF F) (y - σ y) := by
    change cA σ _ = _
    rw [hcincl, map_sub, hinv, ← map_neg, neg_sub]
  have hc2 : ∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r := fun r => by
    change cA σ (cA σ r) = r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a z => simp [cA, Algebra.TensorProduct.map_tmul, hinv]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hcF : ∀ t : F, (cA σ).toRingHom (algebraMap F (AE F E) t) = algebraMap F (AE F E) t := fun t => by
    change cA σ _ = _
    rw [IsScalarTower.algebraMap_apply F (AF F) (AE F E), AlgHom.commutes]
  have hJm : ((incM F J).map (cA σ).toRingHom)ᵀ = ((ε : ℤ) : AE F E) • incM F J := by
    ext i j
    change cA σ (inclR (F := F) (AF F) (J j i)) = ((ε : ℤ) : AE F E) * inclR (F := F) (AF F) (J i j)
    rw [hcincl, hJ, map_mul, map_intCast]
  have hJdet : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  obtain ⟨x, hxV, hx⟩ := descend (F := F) (cA σ).toRingHom hc2 hcF _ hav _ hρu hcρ (incM F J) ε hJm hJdet _ _ x₀ hx₀

  have hxV' : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x)ᵀ * incM F J +
      incM F J * (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) = 0 := by
    have h1 : (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x).map (cA σ) =
        algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • x.map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hce]
    rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
    rw [show x.map (cA σ) = x.map (cA σ).toRingHom from rfl, hxV, smul_zero]
  obtain ⟨p, hpD, hcorner⟩ := unip (cA σ) (incM F J) _ hxV'
  refine ⟨p, 1, hpD, ?_⟩
  have hmul : ((q S * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = (q S).1.1 * p.1.1 := rfl
  rw [hmul, hcorner, hq S]
  have hk := mix_corner (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) he
    (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)))
    (diagCols (Fin n)) (g.1.1) x hNtN hNtD
  erw [hk]
  rw [det_idem he, Matrix.det_smul, Matrix.det_one, mul_one]
  exact isUnit_mix he hx ((isUnit_of_invertible (2 : AE F E)).pow _)

end GlobalTheory.SiegelDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneOfMemBase
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
section
noncomputable section

namespace GlobalTheory.XTermMaj

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def crd (x : AE F E) : Fin (Module.finrank F E) → AF F :=
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun x

def maj (N : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)) (x : AE F E) : ENNReal :=
  U.indicator (fun _ => ENNReal.ofReal ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(crd F E x i).1 v‖) ^ (-(N : ℝ))))
    (fun i => (crd F E x i).2)

end GlobalTheory.XTermMaj

end
end

