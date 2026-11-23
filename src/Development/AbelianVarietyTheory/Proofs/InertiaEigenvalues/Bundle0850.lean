module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0768
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonalStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

open GlobalTheory.Pst GlobalTheory.Pst.LetterDim GlobalTheory.WeilDeligne TensorProduct Module

namespace GlobalTheory.IneKillsDpst

section General

variable {L U D : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D)

def Kills {F : Type} [Field F] (s : L →+* F) (τ : U →+* F) (T : D → D) : Prop :=
  ∀ f ∈ letterHom m s τ, ∀ y, f (T y) = 0

theorem kills_comp {F F' : Type} [Field F] [Field F'] (g : F ≃+* F') (s : L →+* F) (τ : U →+* F)
    (s' : L →+* F') (τ' : U →+* F') (hs : ∀ a, g (s a) = s' a) (hτ : ∀ a, g (τ a) = τ' a) (T : D → D)
    (h : Kills m s τ T) : Kills m s' τ' T := by
  intro f hf y
  let f0 : D →+ F := g.symm.toAddMonoidHom.comp f
  have hf0 : f0 ∈ letterHom m s τ :=
    ⟨fun a x => by simp [f0, hf.1, ← hs], fun c x => by simp [f0, hf.2, ← hτ]⟩
  have := h f0 hf0 y
  simpa [f0] using this

theorem kills_comp_iff {F F' : Type} [Field F] [Field F'] (g : F ≃+* F') (s : L →+* F) (τ : U →+* F)
    (s' : L →+* F') (τ' : U →+* F') (hs : ∀ a, g (s a) = s' a) (hτ : ∀ a, g (τ a) = τ' a) (T : D → D) :
    Kills m s τ T ↔ Kills m s' τ' T :=
  ⟨kills_comp m g s τ s' τ' hs hτ T, kills_comp m g.symm s' τ' s τ
    (fun a => by rw [← hs, RingEquiv.symm_apply_apply]) (fun a => by rw [← hτ, RingEquiv.symm_apply_apply]) T⟩

theorem kills_frob {F : Type} [Field F] (φ : Module.End L D) (hφ : Function.Bijective φ) (σ : U → U)
    (hσ : ∀ c, φ * m c = m (σ c) * φ) (hσ' : Function.Surjective σ) (s : L →+* F) (τ τ' : U →+* F)
    (hτ : ∀ c, τ' c = τ (σ c)) (T : D → D) (hT : ∀ y, φ (T y) = T (φ y)) :
    Kills m s τ T ↔ Kills m s τ' T := by
  have h1 : ∀ c x, φ (m c x) = m (σ c) (φ x) := fun c x => LinearMap.congr_fun (hσ c) x
  let e := LinearEquiv.ofBijective φ hφ
  have h2 : ∀ c x, e.symm (m (σ c) x) = m c (e.symm x) := fun c x => by
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply, e.symm_apply_eq]
    exact (h1 c x).symm
  constructor
  · intro h f hf y
    let f0 : D →+ F := f.comp e.symm.toLinearMap.toAddMonoidHom
    have hf0 : f0 ∈ letterHom m s τ := by
      refine ⟨fun a x => by simp [f0, hf.1], fun c x => ?_⟩
      obtain ⟨c, rfl⟩ := hσ' c
      simp [f0, h2, hf.2, hτ]
    have := h f0 hf0 (φ y)
    rwa [← hT, show f0 (φ (T y)) = f (T y) from congrArg f (e.symm_apply_apply (T y))] at this
  · intro h f hf y
    obtain ⟨z, rfl⟩ := hφ.2 y
    let f0 : D →+ F := f.comp φ.toAddMonoidHom
    have hf0 : f0 ∈ letterHom m s τ' :=
      ⟨fun a x => by simp [f0, hf.1], fun c x => by simp [f0, h1, hf.2, hτ]⟩
    have := h f0 hf0 z
    rwa [show f0 (T z) = f (φ (T z)) from rfl, hT] at this

theorem commute_aeval_right {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {A B : Module.End R M}
    (h : Commute A B) (p : R[X]) : Commute A (Polynomial.aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _)]; exact hp.add_right hr
  | monomial k c =>
    rw [Polynomial.aeval_monomial]
    exact (show Commute (algebraMap R (Module.End R M) c) A from Algebra.commutes c A).symm.mul_right (h.pow_right k)

end General

theorem coe_aeval_of_coe {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    (A : Module.End R p) (f : Module.End R M) (hA : ∀ x : p, ((A x : p) : M) = f x) (q : R[X]) (x : p) :
    ((Polynomial.aeval A q x : p) : M) = Polynomial.aeval f q (x : M) := by
  have hpow : ∀ (n : ℕ) (x : p), (((A ^ n) x : p) : M) = (f ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hA]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {LL K : FinExt l} {V : Type}
  [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem mk_aeval {K F D W : Type} [Field K] [Field F] [AddCommGroup D] [Module K D] [AddCommGroup W] [Module F W]
    (φ : K →+* F) (mk : D →+ W) (hmk : ∀ a x, mk (a • x) = φ a • mk x) (A : Module.End K D)
    (R : Module.End F W) (hR : ∀ y, R (mk y) = mk (A y)) (q : K[X]) (x : D) :
    Polynomial.aeval R (q.map φ) (mk x) = mk (Polynomial.aeval A q x) := by
  have hpow : ∀ (n : ℕ) (x : D), (R ^ n) (mk x) = mk ((A ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hR, ih]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq,
      map_add]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hpow, hmk]

end Local

section Local2
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {LL K : FinExt l} {V : Type}
  [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
  (ρ : Representation ↥LL.1 ↥(GK K) V)


set_option maxHeartbeats 2000000 in
theorem letterHom_eq_zero (f : ↥(Dpst P ρ) →+ Om l)
    (hf : f ∈ letterHom (mulD P ρ) ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
      (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))) (y : ↥(Dpst P ρ)) (hy : wdMk P ι ρ y = 0) : f y = 0 := by
  have hfm : ∀ (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)), f (mulD P ρ c x) = algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c * f x := hf.2
  letI := algC ι LL
  obtain ⟨f2, hf2⟩ : ∃ f2 : ℂ ⊗[↥LL.1] ↥(Dpst P ρ) →ₗ[ℂ] ℂ, ∀ (a : ℂ) (x : ↥(Dpst P ρ)),
      f2 (a ⊗ₜ x) = a * ι (f x) := by
    let f1 : ↥(Dpst P ρ) →ₗ[↥LL.1] ℂ :=
      { toFun := fun x => ι (f x), map_add' := fun x y => by rw [map_add (f := _), map_add (f := _)]
        map_smul' := fun a x => by
          rw [hf.1, map_mul, RingHom.id_apply, Algebra.smul_def]; rfl }
    exact ⟨LinearMap.liftBaseChange ℂ f1, fun a x => by simp [f1, LinearMap.liftBaseChange_tmul]⟩
  have h2 : letterKer (mulD P ρ) ℂ (urC ι) ≤ LinearMap.ker f2 := by
    refine iSup_le fun c => ?_
    rw [LinearMap.range_le_ker_iff]
    refine AlgebraTensorModule.ext fun a x => ?_
    have e1 : (f2 ∘ₗ (LinearMap.baseChange ℂ ((mulD P ρ) c) - (urC ι) c • LinearMap.id)) (a ⊗ₜ[↥LL.1] x) =
        f2 (a ⊗ₜ[↥LL.1] (mulD P ρ c x)) - urC ι c * f2 (a ⊗ₜ[↥LL.1] x) := by
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.baseChange_tmul, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    have e2 : ι (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c) = urC ι c := rfl
    have e3 : f2 (a ⊗ₜ[↥LL.1] (mulD P ρ c x)) = a * (ι (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) c) * ι (f x)) := by
      rw [hf2, hfm, map_mul]
    have e4 := hf2 a x
    rw [e1, LinearMap.zero_apply]
    linear_combination e3 - urC ι c * e4 + a * ι (f x) * e2
  have hmem : (1 : ℂ) ⊗ₜ[↥LL.1] y ∈ letterKer (mulD P ρ) ℂ (urC ι) := by
    have h0 : letterQ (mulD P ρ) ℂ (urC ι) ((1 : ℂ) ⊗ₜ[↥LL.1] y) = 0 := hy
    rwa [← LinearMap.mem_ker, ker_letterQ] at h0
  have h3 := h2 hmem
  rw [LinearMap.mem_ker, hf2, one_mul] at h3
  exact (map_eq_zero_iff ι ι.injective).mp h3
end Local2


set_option synthInstance.maxHeartbeats 200000 in
open Classical in
theorem aeval_stRep_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), GlobalTheory.Pst.IsPst P ρ → ∀ (σ : ↥(Ine (F := E) A)) (q : (↥LL.1)[X]), q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = (GlobalTheory.Pst.wdPst P ι Bw h hj ρ).charPol (GlobalTheory.WeilDeligne.ineIncl h σ) → ∀ x ∈ GlobalTheory.Pst.Dpst P ρ, Polynomial.aeval (GlobalTheory.Pst.stRep P ρ (GlobalTheory.Pst.weilToGK Bw h (GlobalTheory.WeilDeligne.ineIncl h σ))) q x = 0 := by
  intro l _ P AI _ ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ hV σ q hq x hx
  haveI hfin := hV.finite
  haveI := LL.2
  set g := weilToGK Bw h (ineIncl h σ) with hg
  set T : Module.End ↥LL.1 ↥(Dpst P ρ) := Polynomial.aeval (actD P ρ g) q with hTdef

  have hR : ∀ y, wdRho P ι Bw h hj ρ (ineIncl h σ) (wdMk P ι ρ y) = wdMk P ι ρ (actD P ρ g y) := fun y => by
    rw [wdRho_mk, weilD_ineIncl]
  have hlet : ∀ y, wdMk P ι ρ (T y) = 0 := fun y => by
    have := mk_aeval (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l)))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (fun a x => wdMk_smul P ι ρ a x)
      (actD P ρ g) (wdRho P ι Bw h hj ρ (ineIncl h σ)) hR q y
    rw [hq, GlobalTheory.Pst.DpstMap.charPol_wdPst P ι Bw h hj ρ hV,
      LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    exact this.symm

  have hφc : Commute (phiD P ρ) T := commute_aeval_right (phiD_actD P ρ g) q
  have hφT : ∀ y, phiD P ρ (T y) = T (phiD P ρ y) := fun y => LinearMap.congr_fun hφc.eq y

  let d : (↥LL.1 →ₐ[ℚ_[l]] Om l) → ℕ := fun s =>
    if Kills (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T then 1 else 0
  have hd : ∀ s t, d s = d t := GlobalTheory.Pst.LetterDim.const_of_invariant d
    (fun g' hg' s => by
      have key := kills_comp_iff (mulD P ρ) g'.toRingEquiv (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
        (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) (fun _ => rfl) (fun c => hg' c) T
      simp only [d, key])
    (fun g' hg' s => by
      have key1 := kills_comp_iff (mulD P ρ) g'.toRingEquiv (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
        (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        ((algebraMap ↥(MaximalUnramifiedExtension l) (Om l)).comp (frobUr l : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))) (fun _ => rfl) (fun c => hg' c) T
      have key2 := kills_frob (mulD P ρ) (phiD P ρ) phiD_bijective (frobUr l) (phiD_mulD P ρ)
        frobUr_bijective.2 (((g' : Om l →ₐ[ℚ_[l]] Om l).comp s : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
        (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) ((algebraMap ↥(MaximalUnramifiedExtension l) (Om l)).comp (frobUr l : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l)))
        (fun _ => rfl) T hφT
      simp only [d, key1, key2])
  have h0 : Kills (mulD P ρ) ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →+* Om l)
      (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T :=
    fun f hf y => letterHom_eq_zero P ι ρ f hf (T y) (hlet y)
  have hall : ∀ s : ↥LL.1 →ₐ[ℚ_[l]] Om l, Kills (mulD P ρ) (s : ↥LL.1 →+* Om l) (algebraMap ↥(MaximalUnramifiedExtension l) (Om l)) T := by
    intro s
    have e := hd s LL.1.val
    have e1 : d LL.1.val = 1 := if_pos h0
    rw [e1] at e
    by_contra hs
    have : d s = 0 := if_neg hs
    omega

  have hT0 : T ⟨x, hx⟩ = 0 := by
    letI : Module ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := inferInstanceAs (Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))
    haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) := hfin
    refine GlobalTheory.T.eq_zero_of_forall_letterType_functional (k := ℚ_[l]) (F := Om l) (mulD P ρ) (fun _ _ => rfl) (fun c x => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = algebraMap ℚ_[l] ↥LL.1 c • LinearMap.id :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            LinearMap.smul_apply, algebraMap_smul, LinearMap.id_apply]
      rw [coe_mulD, this]
      rfl)) (T ⟨x, hx⟩) fun s f hf => hall s f hf ⟨x, hx⟩
  have := coe_aeval_of_coe (p := Dpst P ρ) (actD P ρ g) (stRep P ρ g) (fun _ => rfl) q ⟨x, hx⟩
  rw [← this]
  exact congrArg Subtype.val hT0

end GlobalTheory.IneKillsDpst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalKillsPotCrystallineOfKillsPotSemistable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

open TensorProduct GlobalTheory.Pst GlobalTheory.PstLine

namespace GlobalTheory.PcrisPst

theorem fixed_of_mem_Dpcris {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L : FinExt l) (h : K.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK K) V) {d : V ⊗[ℚ_[l]] P.R.B} (hd : d ∈ (pc P h hN hF hS).Dpcris ρ)
    (x : ↥(GKin h)) : actVB (P.PD K) ρ (x : ↥(GK K)) d = d := by
  simp only [Formalism.WeaklyAdmissibleFiltrations.PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hd
  have := hd x
  have e : actVB (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) x = actVB (P.PD K) ρ (x : ↥(GK K)) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    have := (pc P h hN hF hS).actB_eq x b
    simp [actVB, Formalism.WeaklyAdmissibleFiltrations.PotCrysData.resH] at this ⊢
    rw [this]
    rfl
  rw [← e]; exact this

section Map

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

theorem stMap_crisIncl_pow (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (n : ℕ)
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V ((actVB (P.PD K) ρ g ^ n) x)) =
      (stRep P ρ' g ^ n) (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← stRep_crisIncl,
      stMap_stRep P he, ih]

theorem stMap_crisIncl_aeval {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ') (g : ↥(GK K)) (q : (↥L.1)[X])
    (x : V ⊗[ℚ_[l]] P.R.B) :
    stMap P f (crisIncl P ↥L.1 V (Polynomial.aeval (actVB (P.PD K) ρ g) q x)) =
      Polynomial.aeval (stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom)
        (stMap P f (crisIncl P ↥L.1 V x)) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hr]
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, stMap_smul P f (hm.smul a),
      stMap_crisIncl_pow P hm.equiv]
    rfl

end Map

theorem aeval_eq_zero_of_kills_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K K' L L' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (hL : L.1 ≤ L'.1) {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V'] (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V') (f : V →ₗ[ℚ_[l]] V'), Function.Injective f → GlobalTheory.PstLine.IsMor hL f ρ ρ' → ∀ (g : ↥(GK K)) (q : (↥L.1)[X]), (∀ y ∈ GlobalTheory.Pst.Dpst P ρ', Polynomial.aeval (GlobalTheory.Pst.stRep P ρ' g) (q.map (IntermediateField.inclusion hL).toRingHom) y = 0) → ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, Polynomial.aeval (actVB (P.PD K) ρ g) q d = 0 := by
  intro l _ P K K' L L' h hN hF hS hL V V' _ _ _ _ _ _ _ _ ρ ρ' f hf hm g q hq d hd
  have hmem : crisIncl P ↥L.1 V d ∈ Dpst P ρ :=
    (mem_Dpst P ρ).2 ⟨K', fun g' hg' => by
      rw [stRep_crisIncl, fixed_of_mem_Dpcris P K K' L h hN hF hS ρ hd ⟨g', hg'⟩]⟩
  have hinj : Function.Injective (stMap P f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  apply crisIncl_injective P (LL := ↥L.1) (V := V)
  apply hinj
  rw [stMap_crisIncl_aeval P hm g q d, map_zero, map_zero]
  exact hq _ (stMap_mem_Dpst P hm.equiv hmem)

end GlobalTheory.PcrisPst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAtPlaceOfIntegralCoverReading
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLocInt

theorem rd_sum {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (s : Fin m → C.d.c₂.F) (g : Fin m → Rul C.d.Xo₂ C.d.c₂) :
    C.rd a (∑ b, s b • g b) = ∑ b, C.σ₂ (s b) • C.rd a (g b) := by
  unfold Cover.rd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smulₛₗ, map_smul, smul_comm]

theorem rd_sub {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (g h : Rul C.d.Xo₂ C.d.c₂) : C.rd a (g - h) = C.rd a g - C.rd a h := by
  unfold Cover.rd
  rw [map_sub, map_sub, smul_sub]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem bddAll_of_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (la' : HeightOneSpectrum (𝓞 C.c'.F)), (∀ y : C.c'.F, la'.valuation C.c'.F y = la.valuation C.d.c₂.F (C.d.eF y)) → ∀ (m : ℕ) (x : Fin m → C.c'.F) (f : Fin m → T.R j), (∀ b, f b ∈ sec (T.Q.Xo j) T.Q.c a n) → (∑ b, C.σ₂ (C.d.eF (x b)) • T.phiJ j σ a (f b)) ∈ C.intForms a n {la} → GlobalTheory.GoodPts.BddAll (T.Q.Xo j) C.c' la' 1 (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
  intro D T hL j hj σ hσ C hU a n hdom hPin la la' hval m x f hf hmem
  obtain ⟨g₂, ⟨hcs, hint⟩, hrd⟩ := hmem
  have hex : ∀ b, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (f b) f₂ := fun b =>
    _root_.GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n (f b) (hf b)
  choose f₂ hf₂ using hex
  have hpin : ∀ b, C.rd a (f₂ b) = T.phiJ j σ a (f b) := fun b => hPin.2 (f b) (hf b) (f₂ b) (hf₂ b).1 (hf₂ b).2
  have hG : g₂ = ∑ b, C.d.eF (x b) • f₂ b := by
    by_contra hne
    have h0 : g₂ - ∑ b, C.d.eF (x b) • f₂ b ≠ 0 := sub_ne_zero.2 hne
    have hsec : g₂ - ∑ b, C.d.eF (x b) • f₂ b ∈ sec C.d.Xo₂ C.d.c₂ a n :=
      sub_mem hcs.1 (sum_mem fun b _ => Submodule.smul_mem _ _ (hf₂ b).1)
    have hli : LinearIndependent C.d.c₂.F ![g₂ - ∑ b, C.d.eF (x b) • f₂ b] :=
      linearIndependent_unique_iff.2 h0
    have hli2 := _root_.GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hL j hj σ hσ C hU hPin.1 a n hdom 1 ![g₂ - ∑ b, C.d.eF (x b) • f₂ b]
      (fun i => by fin_cases i; exact hsec) hli
    have hz : C.rd a (g₂ - ∑ b, C.d.eF (x b) • f₂ b) = 0 := by
      rw [rd_sub, rd_sum, hrd]
      simp only [hpin, sub_self]
    exact hli2.ne_zero 0 (by simpa using hz)
  intro Tv io e ho y hy
  obtain ⟨T', iT, e', y', io₂, y₂, hext, hfin', hio₂, hover⟩ :=
    GlobalTheory.CoverPoint.exists_ext_lift_to_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 Tv io y hy
  have ho₂ : OverLa la T'.V io₂ (e' * e) := by
    refine ⟨Nat.mul_pos hext.1 ho.1, fun z => ?_⟩
    have h1 := hio₂ (C.d.eF.symm z)
    rw [C.d.eF.apply_symm_apply] at h1
    have h2 : vLa la z = vLa la' (C.d.eF.symm z) := by
      simp only [vLa, hval, C.d.eF.apply_symm_apply]
    rw [h1, hext.2.1, ho.2, h2]
    push_cast
    ring
  have hB := (_root_.GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ C.d.Xo₂ C.d.c₂ la g₂).2 (hint la (Set.mem_singleton la)) T' io₂ (e' * e) ho₂
    y₂ hfin'
  rw [map_one, one_mul] at hB
  have laws := GlobalTheory.firstFiveLaws.1
  letI a1 : Algebra C.c'.F T'.Fr := (iT.comp io).toAlgebra
  letI a2 : Algebra C.d.c₂.F T'.Fr := io₂.toAlgebra
  letI a0 : Algebra T.Q.c.F T'.Fr := ((iT.comp io).comp (incF T.Q.c C.c' C.hle)).toAlgebra
  have hAO : AlgOver T.Q.c C.c' C.hle T'.Fr := fun _ => rfl
  have hcomp : ∀ z : C.c'.F, algebraMap C.d.c₂.F T'.Fr (C.d.eF z) = algebraMap C.c'.F T'.Fr z := hio₂
  have e1 : ∀ b, evI y₂ (f₂ b) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    (hf₂ b).2 T'.Fr hAO hcomp y₂.1 y'.1 hover
  have e2 : ∀ b, evI y' (GlobalTheory.FieldBC.rulBC C.hle (f b)) = evR (T.Q.Xo j) T.Q.c (f b) (y'.1.res C.hle hAO) := fun b =>
    GlobalTheory.FieldBCModel.evR_rulBC C.hle (hf b).1 hAO y'.1
  have e3 : evI y₂ g₂ = evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) := by
    rw [hG, GlobalTheory.GalSup.evI_sum, GlobalTheory.GalSup.evI_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [e1, e2, hio₂]
    rfl
  have hgs : (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) ∈ sec (T.Q.Xo j) C.c' a n :=
    sum_mem fun b _ => Submodule.smul_mem _ _ (GlobalTheory.FieldBCModel.rulBC_mem_sec C.hle (hf b))
  obtain ⟨φ, hφ, hm⟩ := hext.2.2
  letI a3 : Algebra C.c'.F Tv.Fr := io.toAlgebra
  have e4 : evI y' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) =
      iT (evI y (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b))) := by
    have := GlobalTheory.PlaceInt.evR_of_frMap_fromTest
      (GlobalTheory.Frames.algebraic_laws laws.secBaseChange _ _ _ _ (T.Q.Xo j) C.c').2.2.1 _ hgs.1 φ y.1 y.2.1 y'.1 hm
    exact this.trans (congrArg (fun r : Tv.Fr →+* T'.Fr => r (evR (T.Q.Xo j) C.c' (∑ b, x b • GlobalTheory.FieldBC.rulBC C.hle (f b)) y.1)) hφ)
  rw [map_one, one_mul, ← GlobalTheory.CoverBound.inV_map_iff iT hext.1 hext.2.1, ← e4, ← e3]
  exact hB

end GlobalTheory.CoverLocInt
end
end

