module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvFinSSOneNot
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SPartTensor

section Generic

variable {F E A R : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] [CommRing R] [Algebra F R]

def tP (p : A →ₐ[F] R) : A ⊗[F] E →+* R ⊗[F] E := (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom

def tQ (s : R →ₗ[F] A) : R ⊗[F] E →+ A ⊗[F] E := (LinearMap.rTensor E s).toAddMonoidHom

@[simp] theorem rTensor_tmul₂ (p : A →ₐ[F] R) (a : A) (x : E) : tP p (a ⊗ₜ[F] x) = p a ⊗ₜ[F] x := rfl

@[simp] theorem tQ_tmul (s : R →ₗ[F] A) (r : R) (x : E) : tQ s (r ⊗ₜ[F] x) = s r ⊗ₜ[F] x := rfl

theorem rTensor_includeRight (p : A →ₐ[F] R) (x : E) : tP p (inclR (F := F) A x) = inclR (F := F) R x := by
  change tP p ((1 : A) ⊗ₜ[F] x) = (1 : R) ⊗ₜ[F] x
  rw [rTensor_tmul₂, map_one]

theorem rTensor_lTensor_comm₂ (p : A →ₐ[F] R) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    tP p (sigR A σ x) = sigR R σ (tP p x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tQ_sigR (s : R →ₗ[F] A) (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tQ s (sigR R σ y) = sigR A σ (tQ s y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem rTensor_rTensor_of_rightInverse (p : A →ₐ[F] R) (s : R →ₗ[F] A) (h : ∀ r, p (s r) = r) (y : R ⊗[F] E) :
    tP p (tQ s y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [tQ_tmul, rTensor_tmul₂, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tQ_tP (p : A →ₐ[F] R) (s : R →ₗ[F] A) (b : A) (h : ∀ a, s (p a) = b * a) (x : A ⊗[F] E) :
    tQ s (tP p x) = (b ⊗ₜ[F] (1 : E)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => rw [rTensor_tmul₂, tQ_tmul, h, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem tQ_mul (s : R →ₗ[F] A) (h : ∀ r r', s (r * r') = s r * s r') (y y' : R ⊗[F] E) :
    tQ s (y * y') = tQ s y * tQ s y' := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
    | tmul b w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tQ_tmul, tQ_tmul, tQ_tmul, h,
        Algebra.TensorProduct.tmul_mul_tmul]

end Generic

section Adelic

variable {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev RS : Type := Ainf F × (∀ v : S, Fv F v.1)

def finOf (c : ∀ v : S, Fv F v.1) : Af F := ∑ v : S, singleFin v.1 (c v)

variable {S}

theorem evalV_finOf (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∈ S) :
    evalV F u (finOf S c) = c ⟨u, h⟩ := by
  unfold finOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single (⟨u, h⟩ : S)
    (fun b _ hb => evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _) (by simp)]
  exact evalV_singleFin_self u _

theorem evalV_finOf_not (c : ∀ v : S, Fv F v.1) (u : HeightOneSpectrum (𝓞 F)) (h : u ∉ S) :
    evalV F u (finOf S c) = 0 := by
  unfold finOf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun b _ => evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem af_ext {x y : Af F} (h : ∀ u, evalV F u x = evalV F u y) : x = y :=
  by first | exact RestrictedProduct.ext _ _ h | exact Subtype.ext (funext h)

variable (S)

def pS : AF F →ₐ[F] RS S :=
  (fstA F).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (sndA F))

def sS : RS S →ₗ[F] AF F where
  toFun r := (r.1, finOf S r.2)
  map_add' r r' := by
    refine Prod.ext rfl ?_
    change finOf S (r.2 + r'.2) = finOf S r.2 + finOf S r'.2
    simp [finOf, Finset.sum_add_distrib]
  map_smul' a r := by
    refine Prod.ext rfl ?_
    change finOf S (a • r.2) = a • finOf S r.2
    simp [finOf, Finset.smul_sum]

variable {S}

theorem pS_sS (r : RS S) : pS S (sS S r) = r := by
  refine Prod.ext rfl (funext fun v => ?_)
  exact evalV_finOf r.2 v.1 v.2

theorem sS_mul (r r' : RS S) : sS S (r * r') = sS S r * sS S r' := by
  refine Prod.ext rfl (af_ext fun u => ?_)
  change evalV F u (finOf S (r.2 * r'.2)) = evalV F u (finOf S r.2 * finOf S r'.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h, evalV_finOf _ u h]; rfl
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem sS_pS (a : AF F) : sS S (pS S a) = sS S 1 * a := by
  refine Prod.ext (one_mul _).symm (af_ext fun u => ?_)
  change evalV F u (finOf S fun v : S => evalV F v.1 a.2) = evalV F u (finOf S 1 * a.2)
  rw [map_mul]
  by_cases h : u ∈ S
  · rw [evalV_finOf _ u h, evalV_finOf _ u h]; simp
  · rw [evalV_finOf_not _ u h, evalV_finOf_not _ u h, zero_mul]

theorem evInf_sS_one (w : InfinitePlace F) : evInf F w (sS S 1) = 1 := by
  change (GlobalTheory.AutFunCompare.evW w) (1 : Ainf F) = 1
  exact map_one _

theorem evFin_sS_one_mem {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ S) : evFin F v (sS S 1) = 1 :=
  evalV_finOf _ v h

theorem evFin_sS_one_not {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ S) : evFin F v (sS S 1) = 0 :=
  evalV_finOf_not _ v h

end Adelic

theorem sPartOf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E)
    (hinj : ∀ a : AF F ⊗[F] E, (∀ w, compInf F E w a = 0) → (∀ v, compFin F E v a = 0) → a = 0)
    (h1 : ∀ w, compInf F E w e = 1) (h2 : ∀ v ∈ S, compFin F E v e = 1) (h3 : ∀ v, v ∉ S → compFin F E v e = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AF F ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ AF F ⊗[F] E),
      (∀ x, P (inclR (F := F) (AF F) x) = inclR R x) ∧ (∀ x, P (sigR (AF F) σ x) = sigR R σ (P x)) ∧
      (∀ y, Q (sigR R σ y) = sigR (AF F) σ (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  have hE : e = (sS S 1 : AF F) ⊗ₜ[F] (1 : E) := by
    rw [← sub_eq_zero]
    refine hinj _ (fun w => ?_) (fun v => ?_)
    · rw [RingHom.map_sub, h1 w, sub_eq_zero]
      change (1 : _) = evInf F w (sS S 1) ⊗ₜ[F] (1 : E)
      rw [evInf_sS_one]; rfl
    · rw [RingHom.map_sub, sub_eq_zero]
      change _ = evFin F v (sS S 1) ⊗ₜ[F] (1 : E)
      by_cases h : v ∈ S
      · rw [h2 v h, evFin_sS_one_mem h]; rfl
      · rw [h3 v h, evFin_sS_one_not h, TensorProduct.zero_tmul]
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  haveI : IsReduced (Ainf F) := inferInstanceAs (IsReduced (∀ v : InfinitePlace F, v.Completion))
  refine ⟨RS S, inferInstance, inferInstance, inferInstance, inferInstance, tP (pS S), tQ (sS S),
    rTensor_includeRight _, rTensor_lTensor_comm₂ _ _, tQ_sigR _ _, rTensor_rTensor_of_rightInverse _ _ pS_sS, fun x => ?_, tQ_mul _ sS_mul⟩
  rw [hE]
  exact tQ_tP _ _ _ sS_pS x

theorem sPart : (∀ (D : D7) (a : AE D), (∀ w, compInf D.host.F D.host.E w a = 0) → (∀ v, cv D v a = 0) → a = 0) →
    ∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R)
      (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D),
      (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧
      (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧
      ∀ y y', Q (y * y') = Q y * Q y' := by
  intro hinj D S e he
  exact sPartOf D.sp.cm.sig S e (hinj D) he.1 (fun v h => (he.2 v).trans (if_pos h))
    (fun v h => (he.2 v).trans (if_neg h))

end GlobalTheory.CompanionTheory.SPartTensor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFrameLeftInvGram
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.NullFr

theorem exists_frame_leftInv {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (P : Fx A r a) (M : Fx A t a) (hx : e • x = x) (hv : e • v = v) (hP : P * x = e • (1 : Fx A r r))
    (hM : M * (v - x * (P * v)) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have h2x : M * (1 - x * P) * x = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hP, Matrix.mul_smul,
      Matrix.mul_one, hx, sub_self, Matrix.mul_zero]
  have h2v : M * (1 - x * P) * v = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hM]
  have hPv : e • (P * v) = P * v := by
    rw [← Matrix.mul_smul, hv]
  refine ⟨P - (P * v) * (M * (1 - x * P)), M * (1 - x * P), ?_, ?_, h2x, h2v⟩
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2x, Matrix.mul_zero, sub_zero, hP]
  · rw [Matrix.sub_mul, Matrix.mul_assoc, h2v, Matrix.mul_smul, Matrix.mul_one, hPv, sub_self]

theorem exists_frame_leftInv_gram {A : Type} [CommRing A] {a r t : ℕ} (e : A) (x : Fx A a r) (v : Fx A a t)
    (B' B : Fx A r r) (C : Fx A r a) (H : Fx A a a) (M : Fx A t a) (hB : B' * B = 1)
    (hx : e • x = x) (hv : e • v = v) (hg : C * (H * x) = e • B)
    (hM : M * (v - x * (B' * (C * (H * v)))) = e • (1 : Fx A t t)) :
    ∃ (L₁ : Fx A r a) (L₂ : Fx A t a), L₁ * x = e • (1 : Fx A r r) ∧ L₁ * v = 0 ∧ L₂ * x = 0 ∧
      L₂ * v = e • (1 : Fx A t t) := by
  have hP : B' * (C * H) * x = e • (1 : Fx A r r) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_smul, hB]
  have hM' : M * (v - x * (B' * (C * H) * v)) = e • (1 : Fx A t t) := by
    rw [Matrix.mul_assoc B', Matrix.mul_assoc C]
    exact hM
  exact exists_frame_leftInv e x v (B' * (C * H)) M hx hv hP hM'

theorem free_of_leftInv_orth {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D)
    (z : Mx D V.rank r × Mx D V.rank t) (hx : e • z.1 = z.1) (hv : e • z.2 = z.2)
    (hg : ip V z.1 z.1 = e • rat b₀.1)
    (M : Mx D t V.rank) (hM : mm M (z.2 - mm z.1 (yv V b₀ z)) = e • (1 : Mx D t t)) : Free e z := by
  have hB : rat b₀.1⁻¹ * rat b₀.1 = (1 : Mx D r r) := by
    have hu : IsUnit b₀.1.det := isUnit_iff_ne_zero.2 hb
    simp only [rat]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  exact exists_frame_leftInv_gram e z.1 z.2 (rat b₀.1⁻¹) (rat b₀.1) (adj z.1) (gA V) M hB hx hv hg hM

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

variable {F : Type} [Field F] [NumberField F]

noncomputable def classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    ClassGroup (𝓞 F) →* Circle where
  toFun c := AddChar.circleEquivComplex.symm ψ (Additive.ofMul c)
  map_one' := by
    rw [ofMul_one]
    exact AddChar.map_zero_eq_one _
  map_mul' a b := by
    rw [ofMul_mul]
    exact AddChar.map_add_eq_mul _ _ _

theorem coe_classCircle (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (c : ClassGroup (𝓞 F)) :
    (classCircle ψ c : ℂ) = ψ (Additive.ofMul c) := by
  rfl

theorem continuous_comp_toClassGroup (φ : ClassGroup (𝓞 F) →* Circle) :
    Continuous (φ.comp (IdeleClassGroup.toClassGroup (K := F))) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : IsOpen ((IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F))) :=
    IdeleClassGroup.isOpenMap_mk (K := F) _ (isOpen_standardOpenSubgroup F)
  have h1 : (1 : IdeleClassGroup F) ∈ (IdeleClassGroup.mk F) '' (standardOpenSubgroup F : Set (IdeleGroup F)) :=
    ⟨1, (standardOpenSubgroup F).one_mem, map_one _⟩
  rw [ContinuousAt, map_one]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hU.mem_nhds h1] with y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hx1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.comp_apply, IdeleClassGroup.toClassGroup_mk, IdeleGroup.toClassGroup_apply, hx1,
    map_one, map_one]

noncomputable def classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) : HeckeCharacter F where
  toMonoidHom := (classCircle ψ).comp IdeleClassGroup.toClassGroup
  continuous_toFun := continuous_comp_toClassGroup _

theorem classHecke_toIdele (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (x : IdeleGroup F) :
    (classHecke ψ).toIdele x = classCircle ψ (IdeleGroup.toClassGroup x) :=
  rfl

theorem standardOpenSubgroup_le_ker (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    standardOpenSubgroup F ≤ (classHecke ψ).toIdele.ker := by
  intro x hx
  have h1 : IdeleGroup.toFractionalIdeal x = 1 := by
    rw [← MonoidHom.mem_ker, IdeleGroup.ker_toFractionalIdeal]
    exact hx
  rw [MonoidHom.mem_ker, classHecke_toIdele, IdeleGroup.toClassGroup_apply, h1, map_one, map_one]

theorem idealLevel_top : idealLevel (⊤ : Ideal (𝓞 F)) = finiteLevel 0 := by
  show finiteLevel (fun v => multiplicity v.asIdeal (⊤ : Ideal (𝓞 F))) = finiteLevel 0
  congr 1
  funext v
  rw [Pi.zero_apply]
  apply multiplicity_eq_zero_of_not_dvd
  intro h
  exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))

theorem conductor_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) :
    (classHecke ψ).conductor = ⊤ := by
  have hne : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := top_ne_bot
  have hle : Subgroup.map ofFinite (idealLevel (⊤ : Ideal (𝓞 F))) ≤ (classHecke ψ).toIdele.ker := by
    rintro _ ⟨z, hz, rfl⟩
    apply standardOpenSubgroup_le_ker ψ
    rw [mem_standardOpenSubgroup_iff_ord]
    intro v
    rw [idealLevel_top] at hz
    apply ord_eq_zero_of_mem_unitsLevel (n := 0)
    rw [← finiteComponent_toFinite, toFinite_ofFinite]
    exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hz v)
  have hd := ((classHecke ψ).map_idealLevel_le_ker_iff hne).mp hle
  exact top_le_iff.mp (Ideal.le_of_dvd hd)

theorem coeff_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (J : Ideal (𝓞 F)) (hJ : J ≠ ⊥) :
    (classHecke ψ).coeff J =
      ψ (Additive.ofMul (ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩)) := by
  have hprime : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (classHecke ψ).coeff v.asIdeal =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) := by
    intro v
    have hv : ¬ v.asIdeal ∣ (classHecke ψ).conductor := by
      rw [conductor_classHecke]
      intro h
      exact v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
    rw [HeckeCharacter.coeff_asIdeal_of_not_dvd _ hv]
    obtain ⟨x, hx, hxI⟩ := exists_mem_primeToLevel (primeIdealUnit_mem_idealsPrimeTo hv)
    have heq : (primeIdealUnit v : (FractionalIdeal (𝓞 F)⁰ F)ˣ) =
        FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
      Units.ext (by rw [coe_primeIdealUnit, FractionalIdeal.coe_mk0])
    rw [HeckeCharacter.idealCharacter_apply _ hx ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ hxI,
      classHecke_toIdele, coe_classCircle, IdeleGroup.toClassGroup_apply, hxI, heq, ClassGroup.mk_mk0]
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (𝓞 F) => ∀ hI : I ≠ ⊥,
      (classHecke ψ).coeff I =
        ψ (Additive.ofMul (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩))) J ?_ ?_ ?_ hJ
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx hx0
    obtain rfl := Ideal.isUnit_iff.mp hx
    have h1 : (⟨⊤, mem_nonZeroDivisors_of_ne_zero hx0⟩ : (Ideal (𝓞 F))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [HeckeCharacter.coeff_top, h1, map_one, ofMul_one, AddChar.map_zero_eq_one]
  · intro a p ha hp ih hpa
    have ha' : a ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact ha
    have hp0 : p ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot]
      exact hp.ne_zero
    have hv := hprime ⟨p, Ideal.isPrime_of_prime hp, hp0⟩
    have hmk : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 F))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha'⟩ :=
      Subtype.ext rfl
    rw [HeckeCharacter.coeff_mul, ih ha', hmk, map_mul, ofMul_mul, AddChar.map_add_eq_mul]
    congr 1

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvFamNormalised
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.PoitouTateInv

theorem exists_invFam_normalised : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω,
    IsPrimitiveRoot ζ (l ^ r) → ∃ inv : InvFam F Ω l r,
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A) := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ
  classical
  have key := _root_.GlobalTheory.CompanionTheory.LocalInvariant.exists_bijective_isNormalised F Ω l r hr ζ hζ
  refine ⟨fun A => if h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v then
    Classical.choose (key A h.choose h.choose_spec) else 0, fun A v hv => ?_⟩
  have h : ∃ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v := ⟨v, hv⟩
  have e : h.choose = v := eq_of_isPlaceOver h.choose_spec hv
  have spec := Classical.choose_spec (key A h.choose h.choose_spec)
  simp only [dif_pos h]
  generalize Classical.choose (key A h.choose h.choose_spec) = f at spec ⊢
  rw [e] at spec
  exact spec

end GlobalTheory.CompanionTheory.PoitouTateInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKer
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeSmooth

theorem exists_open_unit_subgroup_ker : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧
      (∀ x ∈ U, IsUnitAt w x) ∧ ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  intro E _ _ χ w
  have hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ) := GlobalTheory.HeckeComp.smooth_loc χ w
  let V : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {x | Valued.v (x : w.adicCompletion E) = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hV : IsOpen (V : Set (w.adicCompletion E)ˣ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx1 : Valued.v (x : w.adicCompletion E) = 1 := hx
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by rw [hx1]; exact one_ne_zero
    have h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹'
        {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x :=
      Units.continuous_val.continuousAt (Valued.locally_const hx0)
    refine Filter.mem_of_superset h2 ?_
    intro y hy
    have hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E) := hy
    show Valued.v (y : w.adicCompletion E) = 1
    rw [hy', hx1]
  refine ⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hker.inter hV
  · intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro x hx
    exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1

end GlobalTheory.CompanionTheory.HeckeSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_euler_product_of : PositivityTheory.Rg.BcB.G8.Fin.EulerFinOf' := by
  first | exact @GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | exact GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' | (intros; apply GlobalTheory.CompanionTheory.EulerAsm.eulerFinOf' <;> assumption)
end

