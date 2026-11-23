module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TransportedLine

variable {D : D7}

theorem exp_mem_UH_of_lie {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * H + H * X = 0) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem gramAt_det_isUnit (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
  rw [this]
  exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit

variable (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e)

def toUXHom : GA D X →* GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J where
  toFun := GlobalTheory.TripleRead.toUX X e hJ
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X 1).submatrix e e = 1
    simp [Formalism.L2.Theta.mt]
  map_mul' a b := by
    refine Subtype.ext (Units.ext ?_)
    show (mt X (a * b)).submatrix e e = (mt X a).submatrix e e * (mt X b).submatrix e e
    simp [Formalism.L2.Theta.mt, Matrix.submatrix_mul_equiv]

theorem continuous_toUX : Continuous (GlobalTheory.TripleRead.toUX X e hJ) := by
  have hm : Continuous fun g : GA D X => (matHom X g) := continuous_subtype_val
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · have hv : Continuous fun g : GA D X =>
        (matHom X g).1 := Units.continuous_val.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)
  · have hv : Continuous fun g : GA D X =>
        ((matHom X g)⁻¹).1 := Units.continuous_coe_inv.comp hm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine ((continuous_apply (e j)).comp ((continuous_apply (e i)).comp hv)).congr fun g => ?_
    show ((matHom X g)⁻¹).1 (e i) (e j) = (mt X g⁻¹) (e i) (e j)
    simp [Formalism.L2.Theta.mt]

def finIncl (F : Type) [Field F] [NumberField F] : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F →ₗ[F] AF F where
  toFun a := ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((0, a + b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((0, b) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((0, c • a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((0, a) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_snd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F u = 0) : u • x = 0 := by
  let e : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have h1 : (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = 0 :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have hu' : u = u * e := by
    refine Prod.ext ?_ ?_
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).1 * 0
      rw [mul_zero]; exact h1
    · show (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 = (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from u).2 * 1
      rw [mul_one]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (finIncl F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        ((0, (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).2) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact zero_mul _
      · exact one_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_smul, key, hx, map_zero, smul_zero]

theorem toUX_mem_UAt (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    {g : GA D X} (hg : g ∈ GinfC X) :
    GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Z (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have h1 : (finHom X g).val = 1 := by rw [show finHom X g = 1 from hg]; rfl
  have hM : ∀ a b, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 := by
    intro a b
    have e2 := congrFun (congrFun h1 a) b
    rw [Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 ((congrArg id e2).trans ?_)
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_snd _ _ _ (hM _ _) u hu

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end GlobalTheory.TransportedLine

namespace GlobalTheory.TransportedLine

theorem exists_line_toUX_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Z.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau),
    ∀ Y ∈ lieAt X τ, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Z,
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t) := by
  intro D θ hθ X k e Z hJ τ Y hY
  have hU : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D X τ) :=
    exp_mem_UH_of_lie (gramAt_det_isUnit X τ) hY
  let φ : Multiplicative ℝ →* GA D X :=
    { toFun := fun t => oneP θ X τ Y (Multiplicative.toAdd t)
      map_one' := by
        show atTau θ X τ (NormedSpace.exp ((0 : ℝ) • Y)) = 1
        rw [zero_smul, NormedSpace.exp_zero]
        exact GlobalTheory.PointAtPlaceHom.atTau_one hθ X τ
      map_mul' := fun s t => by
        show atTau θ X τ (NormedSpace.exp ((Multiplicative.toAdd s + Multiplicative.toAdd t) • Y)) =
          atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd s • Y)) * atTau θ X τ (NormedSpace.exp (Multiplicative.toAdd t • Y))
        rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
        exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ X τ (hU _) (hU _) }
  refine ⟨(toUXHom X e hJ).comp φ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · have hc : Continuous fun t : ℝ => oneP θ X τ Y t :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ X τ).comp_continuous (continuous_exp_smul Y) hU
    exact (continuous_toUX X e hJ).comp (hc.comp continuous_toAdd)
  · exact toUX_mem_UAt X e Z hJ (GlobalTheory.PointAtPlaceHom.atTau_mem X τ _)

end GlobalTheory.TransportedLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnPerfectPairingDefiniteCoreNode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopColumn

open GlobalTheory.DefiniteMult GlobalTheory.DefLift

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}


set_option maxHeartbeats 1000000 in
theorem exists_form_triv (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (K : Subgroup (GA D V)) (J : Subgroup (Bridge.Gf V))
    (hJ : ∀ κ ∈ GfC V, (finHom V).rangeRestrict κ ∈ J → κ ∈ K)
    {T : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M (K : Set (GA D V)) 1) :
    ∃ f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J 1, c.toMap pr f = T := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  have h2 := tensor_irreducible D V S M m hp
  obtain ⟨fd, inj, πt, hπ, irr⟩ := h2
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  have hE := GlobalTheory.multT_cont_left_equiv D θ V S M πt _ _ hp (fun τ => (m τ).2.1) inj hπ T hT
  choose Ψ hΨ using fun h : GA D V => hb.2 (LinearMap.proj h ∘ₗ T)
  replace hΨ : ∀ h x, pr (Ψ h) x = T x h := fun h x => LinearMap.congr_fun (hΨ h) x
  have hlev : ∀ k ∈ K, ∀ x g, T x (g * k) = T x g := fun k hk x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level θ M _ _ _ ((mem_multT θ M _ _ _).1 hT) v).2.2 k hk g
      rw [Pi.one_apply, one_mul] at this
      rw [map_smul, Pi.smul_apply, Pi.smul_apply]
      exact congrArg (r • ·) this
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy]
  let U : Submonoid (GA D V) :=
    { carrier := {a | ∀ h, Ψ (h * a) = c.ρ a⁻¹ (Ψ h)}
      one_mem' := fun h => by rw [mul_one, inv_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha, mul_inv_rev, map_mul]; rfl }
  obtain ⟨f, hf⟩ := exists_descend (finHom V) c.ρ Ψ fun a ha => real_le hθ U (fun τ g hg h => by
      obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [← key, hΨ, hΨ, (hE x).2.2]; rfl) ha
  refine ⟨f, mem_adForms (finHom V) (GQ V) (GfC V) (exists_fin_lift V) c.ρ hc.1 _ _ Ψ f hf fun γ hγ g κ hκ hk => ?_,
    LinearMap.ext fun x => funext fun h => ?_⟩
  · have e2 : Ψ (γ * g * κ) = Ψ g := by
      refine hb.1 (LinearMap.ext fun x => ?_)
      rw [hΨ, hΨ, hlev κ (hJ κ hκ hk), (hE x).2.1 γ hγ]
    rw [e2]
    simp
  · have e := GlobalTheory.DefiniteEnd.rho_inv_cancel (c := c) h⁻¹ (Ψ h)
    rw [inv_inv] at e
    exact (congrArg (fun w => pr w x) ((congrArg (c.ρ h⁻¹) (hf h)).trans e)).trans (hΨ h x)

end GlobalTheory.TopColumn

theorem GlobalTheory.TopColumn.exists_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D), IsInfFam θ → ∀ {S : D.what₂.Tau → SPar} (M : DSModel (G.V (.core D.R.m)) S), (∀ τ a, M.ε τ a = true) → (coefPlus G θ).Is → ∀ (pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsDualPair θ M (coefPlus G θ) pr → ∀ y ∈ CoreForms G θ D.R.m M, ∃ c ∈ Cols G θ, (coefPlus G θ).toMap pr c = y := by
  intro D T L sc G θ hθ S M hε hc pr hpr y hy
  exact GlobalTheory.TopColumn.exists_form_triv (V := G.V (.core D.R.m)) (c := coefPlus G θ) hθ hε hc hpr
    (lev G (.core D.R.m)) (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.levPlus G) (fun κ hκ h => ⟨hκ, h⟩) hy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairPositiveWeightCoefficientSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopCoefPair

open GlobalTheory.CoefSpace Matrix
open scoped TensorProduct

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem descEnum_cast {n m : ℕ} (E : Finset ℚ) (h1 : E.card = n) (h2 : E.card = m) (hnm : n = m) (a : Fin n) :
    GlobalTheory.SignedHC.descEnum E h1 a = GlobalTheory.SignedHC.descEnum E h2 (Fin.cast hnm a) := by
  subst hnm
  rfl

theorem par_core_top (G : GridData L sc) (τ : D.what₂.Tau) :
    Node.par D sc.cGap (.core D.R.m) τ = GlobalTheory.SignedHC.plus ((num D sc.cGap τ).weightX 0) :=
  (num D sc.cGap τ).parPi_m

theorem sign_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) : M.ε τ = fun _ => true := funext fun a => by
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have hx : (q a, M.ε τ a) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
    hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
  rw [par_core_top G τ] at hx
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hx
  exact (congrArg Prod.snd hy).symm

theorem lam_top (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) (a : Fin (G.V (.core D.R.m)).rank) :
    M.lam τ a = ((LaP G τ).w a : ℝ) + ((rhoVec (G.V (.core D.R.m)).rank a : ℚ) : ℝ) := by
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hn : (G.V (.core D.R.m)).rank = rankP D D.R.m := rank_Xp G
  have hE := card_weight D sc.cGap τ
  have hmem : ∀ i, q i ∈ (num D sc.cGap τ).weightX 0 := fun i => by
    have hx : (q i, M.ε τ i) ∈ Node.par D sc.cGap (.core D.R.m) τ :=
      hS ▸ Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    rw [par_core_top G τ] at hx
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 hx
    rw [← (Prod.mk.inj e).1]
    exact hy
  have hqa : StrictAnti q := fun i j hij => by
    have := hanti hij
    rw [hq, hq] at this
    exact_mod_cast this
  have hd := GlobalTheory.SignedHC.descEnum_unique (hE.trans hn.symm) hqa hmem
  have hw := La_cast D sc.cGap τ (Fin.cast hn a)
  have e1 : q a = ((LaP G τ).w a : ℚ) + rhoVec (G.V (.core D.R.m)).rank a := by
    rw [← hd, descEnum_cast _ _ hE hn a]
    show _ = ((La D sc.cGap τ).w (Fin.cast hn a) : ℚ) + _
    have hc : ((G.V (.core D.R.m)).rank : ℚ) = (rankP D D.R.m : ℚ) := by exact_mod_cast hn
    rw [hw, GlobalTheory.SignedHC.highestWeight, rhoVec, Fin.coe_cast, hc]
    ring
  rw [hq, e1]
  push_cast
  ring

theorem polyAction_conj {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B g : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B⁻¹ (actP lam (B * g * B⁻¹) F) = actP lam g (actP lam B⁻¹ F) := by
  rw [← polyAction_mul, ← polyAction_mul, show B⁻¹ * (B * g * B⁻¹) = g * B⁻¹ by simp only [mul_assoc, inv_mul_cancel_left]]

theorem polyAction_inv_cancel {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (B : ι → GL (Fin n) ℂ)
    (F : Pol ℂ ι n) : actP lam B (actP lam B⁻¹ F) = F := by
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem exists_model (G : GridData L sc) (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)))
    (τ : D.what₂.Tau) :
    ∃ A : M.H τ →ₗ[ℂ] MvPolynomial (Fin (G.V (.core D.R.m)).rank × Fin (G.V (.core D.R.m)).rank) ℂ,
      Function.Injective A ∧ (∀ x, A x ∈ nablaSq ℂ _ (LaP G τ)) ∧
      ∀ k : GL (Fin (G.V (.core D.R.m)).rank) ℂ,
        (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ →
        ∀ x, A (M.σ τ (k : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) x) =
          sqAct ℂ _ (LaP G τ) k (A x) := by
  obtain ⟨H', _, _, π', e, h1, h2, h3, h4⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq _ (LaP G τ)
  have hds : Formalism.MainNotions.S.IsHCTypeU _ (M.lam τ) (M.σ τ) :=
    (GlobalTheory.RealPar.isDS_const_iff true _ _).1 (sign_top G M τ ▸ M.ds τ)
  rw [show M.lam τ = _ from funext (lam_top G M τ)] at hds
  obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU _ _ _ _ _ _ hds h1
  refine ⟨e ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩
  show e (A (M.σ τ k x)) = _
  rw [hA _ hk, h4 _ hk]
  rfl

theorem exists_dualPair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D),
    IsInfFam θ → ∀ (M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m))),
    ∃ pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ, IsDualPair θ M (coefPlus G θ) pr := by
  intro D T L sc G θ hθ M
  classical
  have hε := sign_top G M
  let hP := GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.posDef_dual G
  let B : D.what₂.Tau → GL (Fin (G.V (.core D.R.m)).rank) ℂ := fun τ => (M.fr_unit τ).unit
  have hG : ∀ τ, gramOf B τ = gramAt D (G.V (.core D.R.m)) τ := fun τ => by
    rw [← M.fr_gram τ, hε]
    simp [gramOf, B, Formalism.REAL.Jm]
  choose A h1 h2 h3 using exists_model G M
  let T0 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ =>
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)
  have hT0 : ∀ v : M.Vec, T0 (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ) := fun v => by
    simp [T0, ten]
  let T1 : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau (G.V (.core D.R.m)).rank := actP (LaP G) B⁻¹ ∘ₗ T0
  have hT1 : ∀ t, T1 t = actP (LaP G) B⁻¹ (T0 t) := fun _ => rfl
  let pr : (coefPlus G θ).W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ :=
    (pairB (LaP G)).compl₁₂ ((VV ℂ (LaP G)).subtype ∘ₗ (GlobalTheory.CoefModel.toHilb (LaP G) hP).symm.toLinearMap) T1
  have hpr : ∀ w t, pr w t = pairB (LaP G) ((GlobalTheory.CoefModel.toHilb (LaP G) hP).symm w).1 (T1 t) := fun _ _ => rfl
  refine ⟨pr, fun h0 => ?_, fun τ g hg w v u hu => ?_⟩
  · have hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0 := fun τ => by
      have := (M.ds τ).1
      have := (M.ds τ).2.1
      obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)
      exact ⟨⟨v, Submodule.subset_span hs⟩, hv⟩
    choose v hv using hv
    have hten : ten (fun τ => A τ (v τ)) ≠ 0 :=
      GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm)))
    have hmem : T1 (PiTensorProduct.tprod ℂ v) ∈ VV ℂ (LaP G) := by
      rw [hT1, hT0]
      exact polyAction_mem_VV _ _ (GlobalTheory.Proof.TensorMapDescent.ten_mem (LaP G) _ fun τ => h2 τ (v τ))
    have hz : T1 (PiTensorProduct.tprod ℂ v) = 0 := congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ (LaP G)).2
      ⟨_, hmem⟩ fun y => by
        have h4 : pr (GlobalTheory.CoefModel.toHilb (LaP G) hP y) (PiTensorProduct.tprod ℂ v) = 0 := by
          rw [show pr = 0 from h0]
          rfl
        rw [pairBK_apply]
        exact h4)
    rw [hT1, hT0] at hz
    have := congrArg (actP (LaP G) B) hz
    exact hten ((polyAction_inv_cancel (LaP G) B _).symm.trans (this.trans (map_zero _)))
  · have ha : IsAtTau θ (G.V (.core D.R.m)) τ g (atTau θ (G.V (.core D.R.m)) τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau (G.V (.core D.R.m)) τ θ hθ g hg).exists
      rw [atTau, dite_eq_left hex]
      exact hex.choose_spec
    set Gh := infGL θ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) with hGd
    let k := B * Gh * B⁻¹
    have hk : ∀ ρ, (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) ∈
        Matrix.unitaryGroup _ ℂ := fun ρ =>
      GlobalTheory.CoefSpace.conj_unitary (by
        have := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (G.V (.core D.R.m)) (atTau θ (G.V (.core D.R.m)) τ g) ρ
        rwa [← hG] at this)
    have hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) =
        M.σ ρ (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) (v ρ) := by
      intro ρ
      by_cases hρ : ρ = τ
      · subst hρ
        have e : (k ρ : Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) =
            M.fr ρ * g * (M.fr ρ)⁻¹ := by
          show ((B ρ * Gh ρ * (B ρ)⁻¹ : GL (Fin (G.V (.core D.R.m)).rank) ℂ) :
            Matrix (Fin (G.V (.core D.R.m)).rank) (Fin (G.V (.core D.R.m)).rank) ℂ) = _
          rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hGd, infGL_coe, ha.2.1]
          rfl
        rw [Function.update_self, hu, e]
        rfl
      · have e : k ρ = 1 := by
          have : Gh ρ = 1 := Units.ext (ha.2.2 ρ hρ)
          show B ρ * Gh ρ * (B ρ)⁻¹ = 1
          rw [this, mul_one, mul_inv_cancel]
        rw [Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]
        rfl
    have e0 : T0 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) k (T0 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT0, hT0]
      refine Eq.trans ?_ (actTen ℂ _ _ (LaP G) k _).symm
      congr 1
      funext ρ
      rw [hup, h3 ρ _ (hk ρ)]
    have e1 : T1 (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
        actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v)) := by
      rw [hT1, hT1, e0]
      exact polyAction_conj (LaP G) B Gh _
    obtain ⟨x, rfl⟩ := (GlobalTheory.CoefModel.toHilb (LaP G) hP).surjective w
    calc _ = pairB (LaP G) (actP (LaP G) (invTrK Gh) x.1) (actP (LaP G) Gh (T1 (PiTensorProduct.tprod ℂ v))) := by
          rw [← e1]
          rfl
      _ = pairB (LaP G) x.1 (T1 (PiTensorProduct.tprod ℂ v)) := pairingBInvariantK_holds ℂ _ _ (LaP G) Gh _ _
      _ = _ := rfl

end GlobalTheory.TopCoefPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisationFromTopLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem factor_multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by

  refine Submodule.map_mono (Submodule.span_mono ?_)
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by simp at hk, hT.equiv, hT.cont⟩

end GlobalTheory.SepRows
end

