module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicInductionDetCharactersRankOneEquiv
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.RankOneProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)]


omit [Fintype α] [LinearOrder α] [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem isEmpty_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) : IsEmpty (c a) :=
  ⟨fun x => ha (congrArg Sigma.fst (g.injective (Subsingleton.elim (g ⟨a, x⟩) (g (g.symm ())))))⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder α] in
theorem det_eq_one_of_ne (g : (Σ i, c i) ≃ Unit) {a : α} (ha : a ≠ (g.symm ()).1) (x : GL (c a) k) :
    Matrix.GeneralLinearGroup.det x = 1 := by
  have := isEmpty_of_ne g ha
  ext
  simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α]
  [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] in
theorem mem_parab_unit (g : (Σ i, c i) ≃ Unit) (x : GL Unit k) : x ∈ parab k g :=
  by
    change Matrix.BlockTriangular (x : Matrix Unit Unit k) (blk g)
    intro i j h
    cases i
    cases j
    exact absurd h (lt_irrefl _)

theorem deltaHalf_eq_one (g : (Σ i, c i) ≃ Unit) (x : Levi k c) : deltaHalf k c x = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = (g.symm ()).1
  · have h : modExp c a = 0 := by
      unfold modExp
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne)
        simp
      · intro b hb
        have := isEmpty_of_ne g (a := b) (ha ▸ (Finset.mem_filter.1 hb).2.ne')
        simp
    simp [h]
  · rw [det_eq_one_of_ne g ha, map_one]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem piTensor_leviProj (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ) (p : parab k g)
    (w : PiTensorProduct ℂ fun _ : α => ℂ) :
    piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p) w =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) • w := by
  have hd : (∏ a, (detChar (c a) (ψ a) (leviProj k g p a) : ℂ)) =
      (detChar Unit (ψ (g.symm ()).1) (p : GL Unit k) : ℂ) := by
    rw [Finset.prod_eq_single (g.symm ()).1, detChar_apply, detChar_apply, det_parab,
      Finset.prod_eq_single (g.symm ()).1]
    · intro b _ hb
      exact det_eq_one_of_ne g hb _
    · simp
    · intro b _ hb
      rw [detChar_apply, det_eq_one_of_ne g hb, map_one, Units.val_one]
    · simp
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod, ← hd, smul_comm]
    congr 1
    calc
      _ = (PiTensorProduct.tprod ℂ) (fun a => (detChar (c a) (ψ a) (leviProj k g p a) : ℂ) • x a) := by rfl
      _ = _ := MultilinearMap.map_smul_univ _ _ _

theorem nonempty_equiv_multiProd_unit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type)
    [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) :
    Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  let L : (PiTensorProduct ℂ fun _ : α => ℂ) ≃ₗ[ℂ] ℂ :=
    (PiTensorProduct.constantBaseRingEquiv α ℂ).toLinearEquiv
  have law : ∀ (φ : IndSp g (piTensor fun i => detRep (c i) (ψ i))) (x : GL Unit k),
      φ.1.1 x = (detChar Unit (ψ (g.symm ()).1) x : ℂ) • φ.1.1 1 := fun φ x => by
    have := parInd_law g _ φ ⟨x, mem_parab_unit g x⟩ 1
    rw [deltaHalf_eq_one g, piTensor_leviProj, mul_one, Units.val_one, one_smul] at this
    exact this
  let f : IndSp g (piTensor fun i => detRep (c i) (ψ i)) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => L (φ.1.1 1)
      map_add' := fun φ φ' => map_add L _ _
      map_smul' := fun r φ => map_smul L r _ }
  refine ⟨LocGL.equivOfBijective ⟨f, fun x => LinearMap.ext fun φ => ?_⟩ ⟨fun φ φ' h => ?_, fun z => ?_⟩⟩
  · show L (φ.1.1 (1 * x)) = detRep Unit (ψ (g.symm ()).1) x (L (φ.1.1 1))
    rw [one_mul, law, map_smul]
    exact (ofChar_apply _ _ _).symm
  · have h1 : φ.1.1 1 = φ'.1.1 1 := L.injective h
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    rw [law φ x, law φ' x, h1]
  · refine ⟨⟨⟨fun x => (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z, fun p x => ?_⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds ((hψ (g.symm ()).1).detChar (n := Unit)) (one_mem _)) fun y hy => ?_)⟩, ?_⟩
    · show (detChar Unit (ψ (g.symm ()).1) (p * x) : ℂ) • L.symm z =
        (deltaHalf k c (leviProj k g p) : ℂ) • piTensor (fun i => detRep (c i) (ψ i)) (leviProj k g p)
          ((detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z)
      rw [deltaHalf_eq_one g, piTensor_leviProj, Units.val_one, one_smul, map_mul, Units.val_mul,
        mul_smul]
    · have hy' : detChar Unit (ψ (g.symm ()).1) y = 1 := hy
      apply Subtype.ext
      funext x
      show (detChar Unit (ψ (g.symm ()).1) (x * y) : ℂ) • L.symm z =
        (detChar Unit (ψ (g.symm ()).1) x : ℂ) • L.symm z
      rw [map_mul, hy', mul_one]
    · show L ((detChar Unit (ψ (g.symm ()).1) 1 : ℂ) • L.symm z) = z
      rw [map_one, Units.val_one, one_smul, L.apply_symm_apply]

end GlobalTheory.SmGL.RankOneProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.Exponents

section Bool

variable {X : Bool → Type} [∀ x, AddCommGroup (X x)] [∀ x, Module ℂ (X x)]

def boolPair (v : X false) (w : X true) : ∀ x, X x
  | false => v
  | true => w

def boolMulti : (∀ x, X x) →ₘₗ[ℂ] (X false ⊗[ℂ] X true) :=
  MultilinearMap.mk' (fun x => x false ⊗ₜ[ℂ] x true)
    (fun m i x y => by cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add])
    (fun m i c x => by cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul])

theorem boolPair_eq_right (v : X false) (w w' : X true) :
    boolPair v w = Function.update (boolPair v w') true w := by
  funext x; cases x <;> simp [boolPair]

theorem boolPair_eq_left (v v' : X false) (w : X true) :
    boolPair v w = Function.update (boolPair v' w) false v := by
  funext x; cases x <;> simp [boolPair]

def boolBilin : X false →ₗ[ℂ] X true →ₗ[ℂ] PiTensorProduct ℂ X :=
  LinearMap.mk₂ ℂ (fun v w => PiTensorProduct.tprod ℂ (boolPair v w))
    (fun v v' w => by
      rw [boolPair_eq_left (v + v') 0, boolPair_eq_left v 0, boolPair_eq_left v' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_left (c • v) 0, boolPair_eq_left v 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])
    (fun v w w' => by
      rw [boolPair_eq_right v (w + w') 0, boolPair_eq_right v w 0, boolPair_eq_right v w' 0,
        MultilinearMap.map_update_add])
    (fun c v w => by
      rw [boolPair_eq_right v (c • w) 0, boolPair_eq_right v w 0, MultilinearMap.map_update_smul,
        RingHom.id_apply])

def boolTensorEquiv : PiTensorProduct ℂ X ≃ₗ[ℂ] X false ⊗[ℂ] X true :=
  LinearEquiv.ofLinearMap (PiTensorProduct.lift boolMulti) (TensorProduct.lift boolBilin)
    (by
      refine TensorProduct.ext' fun v w => ?_
      simp [boolBilin, boolMulti, boolPair])
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      simp only [boolBilin, boolMulti, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply, TensorProduct.lift.tmul,
        LinearMap.mk₂_apply, LinearMap.id_apply]
      apply (PiTensorProduct.tprod ℂ).congr_arg
      funext i
      cases i <;> rfl)

theorem boolTensorEquiv_tprod (x : ∀ i, X i) :
    boolTensorEquiv (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true := by
  simp [boolTensorEquiv, boolMulti]

end Bool

def piTensorTwoEquiv {R a b V W : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    (piTensor (twoRep π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo R a b).symm.toMonoidHom) :=
  .mk (boolTensorEquiv (X := Two V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show boolTensorEquiv (X := Two V W) (piTensor (twoRep π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo R a b).symm g) (boolTensorEquiv (X := Two V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, boolTensorEquiv_tprod, boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo R a b).symm g) (x false) (x true)).symm

theorem prod₂_equiv_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type)
    [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod₂ π₁ π₂).Equiv (multiProd (two (stdSum (rfl : r + t = r + t))) (twoRep π₁ π₂))) :=
  ⟨(LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv π₁ π₂)).symm⟩

end GlobalTheory.SmGL.Exponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PbEqOfTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPrimes

theorem pb_eq_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → T.pb = R.C.P.pb := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hC hW hO
  obtain ⟨w⟩ := hW
  exact GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R w.laws.toLawsM hC.lev (hO.2.tuple ()).half

end GlobalTheory.LevelPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
section
noncomputable section

namespace GlobalTheory.LFun.SplitVal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

private lemma sigR_tmul_adelic_iwasawa_hecke {K L : Type} [Field K] [Field L] [Algebra K L] {τ : L →ₐ[K] L} {R : Type} [CommRing R]
    [Algebra K R] (r : R) (e : L) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R τ (r ⊗ₜ[K] e) = r ⊗ₜ[K] τ e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]

private lemma extZero_tmul {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] (a : Af K) (e : L) :
    extZero K L (a ⊗ₜ[K] e) = (LinearMap.inr K (Ainf K) (Af K) a : AF K) ⊗ₜ[K] e :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a e

omit [NumberField E] in
theorem sigR_extZero (y : Af F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (extZero F E y) = extZero F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [sigR_tmul_adelic_iwasawa_hecke, extZero_tmul, extZero_tmul]
    exact sigR_tmul_adelic_iwasawa_hecke (R := AF F) (LinearMap.inr F (Ainf F) (Af F) a) e
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem evalV_sigR (y : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma map_evalV_eq_of_finAdEquiv_eq {v' : HeightOneSpectrum (𝓞 F)} {y₁ y₂ : Af F ⊗[F] E}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v' → finAdEquiv F E y₁ u = finAdEquiv F E y₂ u) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₁ =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₂ := by
  have hev1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 1 := by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v' = 1
    exact RestrictedProduct.single_eq_same _ _ _
  have hev0 : ∀ v'' : HeightOneSpectrum (𝓞 F), v'' ≠ v' →
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v'' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 0 :=
    fun v'' hv => by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v'' = 0
    exact RestrictedProduct.single_eq_of_ne _ _ hv
  have hs1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) = 1 := by
    rw [Algebra.TensorProduct.map_tmul, hev1, AlgHom.id_apply]; rfl
  have key : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₁ =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₂ := by
    apply (finAdEquiv F E).injective
    refine FiniteAdeleRing.ext _ fun u => ?_
    rw [map_mul, map_mul]
    change finAdEquiv F E _ u * finAdEquiv F E y₁ u = finAdEquiv F E _ u * finAdEquiv F E y₂ u
    by_cases hu : u.under (𝓞 F) = v'
    · rw [H u hu]
    · rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), Algebra.TensorProduct.map_tmul, hev0 _ hu,
        TensorProduct.zero_tmul, map_zero, zero_mul, zero_mul]
  have := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)) key
  rwa [map_mul, map_mul, hs1, one_mul, one_mul] at this

theorem single_apply_ne (x : (w.adicCompletion E)ˣ) {u : HeightOneSpectrum (𝓞 E)} (hu : u ≠ w) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) u = 1 := by
  classical
  first
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) u = 1
     exact RestrictedProduct.mulSingle_eq_of_ne _ _ hu)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     simp [Pi.mulSingle, Function.update, hu])

private lemma cmval_single_apply_self (x : (w.adicCompletion E)ˣ) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) w = x := by
  classical
  first
  | (change (Pi.mulSingle w (x : w.adicCompletion E) : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) w = x
     exact Pi.mulSingle_eq_same _ _)
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) w = x
     exact RestrictedProduct.mulSingle_eq_same _ _)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     exact Pi.mulSingle_eq_same _ _)

theorem sigR_single (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ ((finAdEquiv F E).symm
      (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)) =
    (finAdEquiv F E).symm (GlobalTheory.CMVal.single w' (Units.map (complMap h').toMonoidHom a) : FiniteAdeleRing (𝓞 E) E) := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne h h'
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) h' h
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have hz1 : GlobalTheory.AdelicU.splitProj τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = (a : Fv F v) := by
    apply (complMap h).injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← finAdEquiv_apply h, RingEquiv.apply_symm_apply, cmval_single_apply_self]
    rfl
  have hz2 : GlobalTheory.AdelicU.splitProj (τ.comp σ) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = 1 := by
    apply (complMap h').injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', ← finAdEquiv_apply h', RingEquiv.apply_symm_apply, map_one]
    exact single_apply_ne _ (Ne.symm hne)
  apply (finAdEquiv F E).injective
  rw [RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  by_cases hu : u.under (𝓞 F) = v
  · have hu2 : u = w ∨ u = w' := by
      by_cases huw : u = w
      · exact Or.inl huw
      · right
        obtain ⟨τu, hτu, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE huw hu h
        rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τu with e | e
        · exact absurd (hτu.symm.trans (e ▸ hτ)) huw
        · rw [← hτu, e, hτ']
    rcases hu2 with huw | huw
    · rw [huw, finAdEquiv_apply h, evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← GlobalTheory.AdelicU.splitProj_comp,
        hz2, map_one]
      exact (single_apply_ne _ hne).symm
    · rw [huw, finAdEquiv_apply h', evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ',
        GlobalTheory.AdelicU.splitProj_comp_sigR hE τ, hz1, cmval_single_apply_self]
      rfl
  · have h1 := map_evalV_eq_of_finAdEquiv_eq (v' := u.under (𝓞 F))
      (y₁ := (finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E))
      (y₂ := 1) (fun u' hu' => by
        rw [RingEquiv.apply_symm_apply, map_one]
        exact single_apply_ne _ (by rintro rfl; exact hu (hu'.symm.trans h)))
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), evalV_sigR, h1]
    simp only [map_one]
    exact (single_apply_ne _ (by rintro rfl; exact hu h')).symm

private lemma coe_locIdele' (u : HeightOneSpectrum (𝓞 E)) (x : (u.adicCompletion E)ˣ) :
    ((locIdele F u x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single u x : FiniteAdeleRing (𝓞 E) E)) := rfl

theorem sigR_locIdele (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (locIdele F w (Units.map (complMap h).toMonoidHom a) : AF F ⊗[F] E) =
      locIdele F w' (Units.map (complMap h').toMonoidHom a) := by
  rw [coe_locIdele', coe_locIdele', map_add (f := _), map_sub, map_one, sigR_extZero, sigR_extZero, map_one,
    sigR_single hE h h' hne a]

theorem val_mul_val_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  intro F E _ _ _ _ _ σ hE μ b hμ w w' hww hne hw hw'
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne rfl hww.symm
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) hww.symm rfl
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have ha := Formalism.L2.Host.unif_spec (w.under (𝓞 F))
  set a := Formalism.L2.Host.atFin (w.under (𝓞 F)) (Formalism.L2.Host.unif (w.under (𝓞 F))) with ha_def
  have hx : Formalism.L2.Host.IsUnifAt w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE rfl hτ _
  have hx' : Formalism.L2.Host.IsUnifAt w' (Units.map (complMap hww.symm).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE hww.symm hτ' _
  rw [← UnrAt.locChar_eq_val hw hx, ← UnrAt.locChar_eq_val hw' hx']
  simp only [locChar, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  have hP : locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) *
      locIdele F w' (Units.map (complMap hww.symm).toMonoidHom a) =
      ideleMap F E (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a))) := by
    apply Units.ext
    rw [Units.val_mul, ← sigR_locIdele hE rfl hww.symm hne a, ← GlobalTheory.Doubling.algebraMap_norm_eq hE]
    rfl
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  rw [hP, hall η hη, hη.2.2.1, one_pow, map_one]

end GlobalTheory.LFun.SplitVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
section
noncomputable section

namespace GlobalTheory.HoweGlobalPair

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def opInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Set (Module.End ℂ ↥(M.Pol ψ emb)) :=
  {g | (∃ k ∈ KInf σ W emb, ∀ f : ↥(M.Pol ψ emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin n × Fin d)) ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ W, ∀ f : ↥(M.Pol ψ emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin n × Fin d))
        ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)}

def relInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Submodule ℂ ↥(M.Pol ψ emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ X, ∃ f ∈ M.Pol ψ emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin n × Fin d))) ∨
    ∃ k ∈ KInf σ X emb, ∃ f f₁ : ↥(M.Pol ψ emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin n × Fin d)) ⇑(f₁ : SInf F (Fin n × Fin d)) ∧ x = f₁ - f}

def opFin (om : Rep σ X W) (v : Pl F) : Set (Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))) :=
  {g | ∃ h ∈ UAt σ W (evFin F v), ∀ φ : ↥(SB (Fin n × Fin d → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ)}

def relFin (om : Rep σ X W) (v : Pl F) : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
  (augAt om v).comap (SB (Fin n × Fin d → Fv F v)).subtype

end GlobalTheory.HoweGlobalPair

end
end

