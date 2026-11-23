module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
  Formalism.L2.SG.EvalTOntoRep MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def contSub : Submodule ℂ (L2X X) where
  carrier := {f | ∃ φ, IsContRep X f φ}
  add_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ + ψ, contRep_add X hφ hψ⟩
  zero_mem' := ⟨0, contRep_zero X⟩
  smul_mem' := fun a _ ⟨φ, hφ⟩ => ⟨a • φ, contRep_smul X a hφ⟩

def repOn : contSub X →ₗ[ℂ] (X.B.I.GA → ℂ) where
  toFun f := f.2.choose
  map_add' f g := contRep_unique X (f + g).2.choose_spec (contRep_add X f.2.choose_spec g.2.choose_spec)
  map_smul' a f := contRep_unique X (a • f).2.choose_spec (contRep_smul X a f.2.choose_spec)

def contRepL : L2X X →ₗ[ℂ] (X.B.I.GA → ℂ) := (LinearMap.exists_extend (repOn X)).choose

theorem contRepL_spec {f : L2X X} {φ : X.B.I.GA → ℂ} (hf : IsContRep X f φ) : contRepL X f = φ := by
  have e := LinearMap.congr_fun (LinearMap.exists_extend (repOn X)).choose_spec ⟨f, φ, hf⟩
  have e' : contRepL X f = repOn X ⟨f, φ, hf⟩ := e
  rw [e']
  exact contRep_unique X (Exists.choose_spec (p := fun φ => IsContRep X f φ) _) hf

theorem eq_of_inner_tens {p q : X.B.Hs} (h : ∀ y, ⟪p, X.B.tens y⟫_ℂ = ⟪q, X.B.tens y⟫_ℂ) : p = q := by
  let f : X.B.Hs →L[ℂ] ℂ := innerSL ℂ (p - q)
  have hsp : (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} := by
    refine (Submodule.span_le (p := LinearMap.ker (f : X.B.Hs →ₗ[ℂ] ℂ))).2 ?_
    rintro _ ⟨y, rfl⟩
    show ⟪p - q, X.B.tens y⟫_ℂ = 0
    rw [inner_sub_left, h y, sub_self]
  have hcl : closure (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} :=
    closure_minimal hsp (isClosed_eq f.continuous continuous_const)
  rw [X.B.tens_spec.2.2.closure_eq] at hcl
  have h0 : f (p - q) = 0 := hcl (Set.mem_univ _)
  have : ⟪p - q, p - q⟫_ℂ = 0 := h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] (x y : ∀ i, H i) (v : ι) (z : H v) :
    ∏ w, ⟪Function.update x v z w, y w⟫_ℂ = ⟪z, y v⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪x w, y w⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_add [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a b : X.B.H v) :
    X.B.tens (Function.update x v (a + b)) =
      X.B.tens (Function.update x v a) + X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_add_left, X.B.tens_spec.1, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, prod_update,
    inner_add_left, add_mul]

theorem tens_update_smul [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a : ℂ) (b : X.B.H v) :
    X.B.tens (Function.update x v (a • b)) = a • X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_smul_left, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, inner_smul_left, mul_assoc]

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecC (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (u τ : M.H τ))

theorem piCongrLeft_update {α β : Type} [DecidableEq α] [DecidableEq β] (P : β → Type) (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) (x : P (e a)) :
    Equiv.piCongrLeft P e (Function.update f a x) = Function.update (Equiv.piCongrLeft P e f) (e a) x := by
  apply (Equiv.piCongrLeft P e).symm.injective
  rw [Equiv.symm_apply_apply]
  funext a'
  rw [Equiv.piCongrLeft_symm_apply]
  by_cases ha : a' = a
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne (e.injective.ne ha), Equiv.piCongrLeft_apply_apply]

theorem vecC_update [DecidableEq D.what₂.Tau] [DecidableEq (NumberField.InfinitePlace X.B.I.F)]
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    vecC X M c (Function.update u τ w) = Function.update (vecC X M c u) (X.pl.symm τ) (c τ (w : M.H τ)) := by
  unfold vecC
  rw [← piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.sm i) => c i (s : M.H i)) u τ w τ'

theorem vecC_eq (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (g : ∀ v, X.B.H v)
    (hg : ∀ τ, c τ (u τ : M.H τ) = g (X.pl.symm τ)) : vecC X M c u = g := by
  unfold vecC
  have : (fun τ => c τ (u τ : M.H τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm g := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply, hg τ]
  rw [this, Equiv.apply_symm_apply]

def conjMap (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : MMap M where
  toFun u := fun y => star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹)))
  map_update_add' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_add, map_add (f := _), tens_update_add, Pi.add_apply, star_add]
  map_update_smul' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_smul, LinearIsometryEquiv.map_smulₛₗ, tens_update_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, star_star, RingHom.id_apply]

theorem conjMap_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (u : M.Vec) (y : GA D (D.sp.Y 0)) :
    conjMap X M c A h t u y = star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹))) := rfl

end GlobalTheory.ConjRowMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdUpdateSelf
section
noncomputable section

open scoped TensorProduct Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.TensorContraction

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem prod_update_self [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∉ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = ∏ k ∈ s, φ k (v k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ j := fun e => hj (e ▸ hk)
  rw [Function.update_of_ne hk']

theorem prod_update_mem [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∈ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = φ j x * ∏ k ∈ s.erase j, φ k (v k) := by
  rw [← Finset.mul_prod_erase s _ hj, Function.update_self,
    prod_update_self φ (s.erase j) j (Finset.notMem_erase j s) v x]

def contrM (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (i : ι) (hi : i ∉ s) (hs : ∀ j, j ≠ i → j ∈ s) :
    (∀ j, K j) →ₘₗ[ℂ] K i where
  toFun v := (∏ k ∈ s, φ k (v k)) • v i
  map_update_add' v j x y := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, smul_add]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' v j c x := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, RingHom.id_apply]
      rw [smul_comm]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul,
        RingHom.id_apply, mul_assoc, mul_smul]

def contrL (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) : (⨂[ℂ] j, K j) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (contrM φ (Finset.univ.erase i) i (Finset.notMem_erase _ _)
    fun j h => Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)

theorem contrL_tprod (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (v : ∀ j, K j) :
    contrL φ i (PiTensorProduct.tprod ℂ v) = (∏ k ∈ Finset.univ.erase i, φ k (v k)) • v i := by
  rw [contrL, PiTensorProduct.lift.tprod]
  rfl

theorem contrL_comp_mapFactor (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (f : Module.End ℂ (K i)) :
    contrL φ i ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ contrL φ i := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun v => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, contrL_tprod]
  rw [prod_update_self φ _ i (Finset.notMem_erase i _), Function.update_self, map_smul]

private theorem eq_zero_of_contrL_eq_zero (i : ι) (z : ⨂[ℂ] j, K j)
    (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i z = 0) : z = 0 := by
  let b : ∀ j, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (K j)) ℂ (K j) :=
    fun j => Module.Basis.ofVectorSpace ℂ (K j)
  let B := Basis.piTensorProduct b
  refine B.forall_coord_eq_zero_iff.1 fun p => ?_
  let φ : ∀ j, K j →ₗ[ℂ] ℂ := fun j => (b j).coord (p j)
  have key : B.coord p = (b i).coord (p i) ∘ₗ contrL φ i := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contrL_tprod, map_smul, smul_eq_mul, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, φ]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [key, LinearMap.comp_apply, h φ, map_zero]

theorem eq_of_contrL (i : ι) (x y : ⨂[ℂ] j, K j) (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x = contrL φ i y) :
    x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_contrL_eq_zero i (x - y) fun φ => by rw [map_sub, h φ, sub_self]

private theorem piTensorProduct_map_ite_eq_self_of_slot_fixed (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j)
    (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) (s : Finset ι) :
    PiTensorProduct.map (fun j => if j ∈ s then p j else LinearMap.id) x = x := by
  induction s using Finset.induction_on with
  | empty => simp [PiTensorProduct.map_id]
  | insert a s ha ih =>
    have e : (fun j => if j ∈ insert a s then p j else (LinearMap.id : Module.End ℂ (K j))) =
        fun j => Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) a (p a) j ∘ₗ
          (if j ∈ s then p j else LinearMap.id) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
    rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
    exact h a

theorem map_eq_self (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j) (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) :
    PiTensorProduct.map p x = x := by
  simpa using piTensorProduct_map_ite_eq_self_of_slot_fixed p x h Finset.univ

theorem mem_range_map (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by

  have hN : ∀ i, ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x ∈ N i :=
    fun i φ => h i (contrL φ i) (contrL_comp_mapFactor φ i)

  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective (N i).subtype (N i).ker_subtype
  let P : ∀ i, Module.End ℂ (K i) := fun i => (N i).subtype ∘ₗ g i
  have hP : ∀ i, ∀ v ∈ N i, P i v = v := fun i v hv => by
    have := congrArg (fun f => (N i).subtype (f ⟨v, hv⟩)) (hg i)
    simpa [P] using this

  have hfix : ∀ i, intersection_update_fsHerm_neg_one i (P i) x = x := fun i =>
    eq_of_contrL i _ _ fun φ => by
      rw [← LinearMap.comp_apply (contrL φ i), contrL_comp_mapFactor, LinearMap.comp_apply, hP i _ (hN i φ)]
  rw [LinearMap.mem_range]
  refine ⟨PiTensorProduct.map g x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact map_eq_self P x hfix

end GlobalTheory.TensorContraction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RapidDecayAllRealCoordinatesOfFunctionals
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecayCoord

theorem theta_incA {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR, Algebra.TensorProduct.map_tmul]
  rw [h]
  exact (hθ τ).1 x

theorem compAt_emb {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (V W : HSp D) {a b : ℕ}
    (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) :
    compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y) = P.map (tauE D τ) * compAt θ τ y * Q.map (tauE D τ) := by
  have hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), compAt θ τ M = M.map ((θ τ).comp (infPart D)) :=
    fun M => rfl
  have hE : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map ((θ τ).comp (infPart D)) = M.map (tauE D τ) := by
    intro m n M; ext i j; simp [theta_incA θ hθ]
  rw [hm, hm, GlobalTheory.IsoMean.emb, Matrix.map_mul, Matrix.map_mul, hE, hE]

theorem exists_left_inv {K : Type*} [Field K] {n a : ℕ} (P : Matrix (Fin n) (Fin a) K) (hP : P.rank = a) :
    ∃ P' : Matrix (Fin a) (Fin n) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [Matrix.rank] at hP
    rw [hP, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h2 := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at h2
  have h3 : LinearMap.toMatrix' P.mulVecLin = P := LinearMap.toMatrix'_toLin' P
  rwa [h3] at h2

theorem exists_right_inv {K : Type*} [Field K] {n b : ℕ} (Q : Matrix (Fin b) (Fin n) K) (hQ : Q.rank = b) :
    ∃ Q' : Matrix (Fin n) (Fin b) K, Q * Q' = 1 := by
  obtain ⟨R, hR⟩ := exists_left_inv Qᵀ (by rw [Matrix.rank_transpose, hQ])
  refine ⟨Rᵀ, ?_⟩
  have := congrArg Matrix.transpose hR
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem sum_pow_le {κ : Type*} [Fintype κ] [Nonempty κ] (u : κ → ℝ) (hu : ∀ k, 0 ≤ u k) (N : ℕ) :
    (∑ k, u k) ^ N ≤ (Fintype.card κ : ℝ) ^ N * ∑ k, u k ^ N := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  have h1 : ∑ k, u k ≤ Fintype.card κ * u j := by
    have := Finset.sum_le_card_nsmul Finset.univ u (u j) (fun k _ => hj k (Finset.mem_univ _))
    simpa [nsmul_eq_mul] using this
  calc (∑ k, u k) ^ N ≤ (Fintype.card κ * u j) ^ N :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => hu k) h1 N
    _ = (Fintype.card κ : ℝ) ^ N * u j ^ N := mul_pow _ _ _
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun k => u k ^ N) (fun k _ => pow_nonneg (hu k) N) (Finset.mem_univ j)

theorem trace_single {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℂ) (k : Fin a) (l : Fin b) (α : ℂ) :
    (Yᴴ * Matrix.single k l α).trace = star (Y k l) * α := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single l, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp

theorem norm_le_re (c w : ℂ) (hc : c ≠ 0) :
    ‖w‖ ≤ |2 * (c * (star w * c⁻¹)).re| + |2 * (c * (star w * (Complex.I * c⁻¹))).re| := by
  have e1 : c * (star w * c⁻¹) = star w := by field_simp
  have e2 : c * (star w * (Complex.I * c⁻¹)) = Complex.I * star w := by field_simp
  rw [e1, e2]
  have := Complex.norm_le_abs_re_add_abs_im w
  simp only [Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_im, abs_mul]
  norm_num
  linarith [abs_nonneg w.re, abs_nonneg w.im]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem det_gramAt_ne {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  unfold gramAt
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (GlobalTheory.StabCompact.det_gram_ne_zero V)

theorem herm_key {D : D7} (V W : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (Pc : Matrix (Fin W.rank) (Fin a) ℂ)
    (Pl : Matrix (Fin a) (Fin W.rank) ℂ) (hP : Pl * Pc = 1) (Qc : Matrix (Fin b) (Fin V.rank) ℂ)
    (Qr : Matrix (Fin V.rank) (Fin b) ℂ) (hQ : Qc * Qr = 1) (Y X : Matrix (Fin a) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ ((gramAt D W τ)⁻¹ * Plᴴ * X * Qrᴴ * gramAt D V τ) (Pc * Y * Qc) =
      (Yᴴ * X).trace := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  set GV := gramAt D V τ
  set GW := gramAt D W τ
  have hW : GW * GW⁻¹ = 1 := Matrix.mul_nonsing_inv GW (Ne.isUnit (det_gramAt_ne W τ))
  have hV : GV * GV⁻¹ = 1 := Matrix.mul_nonsing_inv GV (Ne.isUnit (det_gramAt_ne V τ))
  have hP' : Pcᴴ * Plᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hP, Matrix.conjTranspose_one]
  have hQ' : Qrᴴ * Qcᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  have e : GV⁻¹ * (Pc * Y * Qc)ᴴ * GW * (GW⁻¹ * Plᴴ * X * Qrᴴ * GV) = GV⁻¹ * ((Qcᴴ * Yᴴ * X * Qrᴴ) * GV) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc GW GW⁻¹, hW, Matrix.one_mul, ← Matrix.mul_assoc Pcᴴ Plᴴ, hP', Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc _ GV, hV, Matrix.mul_one, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul]

end GlobalTheory.DecayCoord

namespace GlobalTheory.DecayCoord

theorem decay_real_coords : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  intro D V W a b P Q hP hQ θ hθ f hf N
  classical
  obtain ⟨Pl, hPl⟩ := exists_left_inv P hP
  obtain ⟨Qr, hQr⟩ := exists_right_inv Q hQ
  have hPlτ : ∀ τ, Pl.map (tauE D τ) * P.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hPl, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQrτ : ∀ τ, Q.map (tauE D τ) * Qr.map (tauE D τ) = 1 := fun τ => by
    rw [← Matrix.map_mul, hQr, Matrix.map_one _ (map_zero _) (map_one _)]
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let zOf : D.what₂.Tau → Matrix (Fin a) (Fin b) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun τ X =>
    (gramAt D W τ)⁻¹ * (Pl.map (tauE D τ))ᴴ * X * (Qr.map (tauE D τ))ᴴ * gramAt D V τ
  let zι : D.what₂.Tau × Fin a × Fin b × Bool → Matrix (Fin W.rank) (Fin V.rank) ℂ := fun i =>
    zOf i.1 (Matrix.single i.2.1 i.2.2.1 (if i.2.2.2 then Complex.I * (c i.1)⁻¹ else (c i.1)⁻¹))
  let ℓ : D.what₂.Tau × Fin a × Fin b × Bool → Mx D a b → ℝ := fun i y =>
    |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W i.1 (zι i) (compAt θ i.1 (GlobalTheory.IsoMean.emb V W P Q y))|
  have hterm : ∀ (y : Mx D a b) (τ : D.what₂.Tau) (k : Fin a) (l : Fin b),
      ‖θ τ (infPart D (y k l))‖ ≤ ∑ β : Bool, ℓ (τ, k, l, β) y := by
    intro y τ k l
    have hs : ∀ α : ℂ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ (zOf τ (Matrix.single k l α))
        (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y)) = 2 * (c τ * (star (compAt θ τ y k l) * α)).re := by
      intro α
      rw [compAt_emb θ hθ τ V W P Q y]
      show 2 * (c τ * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt V W τ _ _).re = _
      rw [herm_key V W τ _ _ (hPlτ τ) _ _ (hQrτ τ), trace_single]
    rw [Fintype.sum_bool]
    simp only [ℓ, zι, if_true, if_false, Bool.false_eq_true]
    rw [hs, hs]
    have := norm_le_re (c τ) (compAt θ τ y k l) (hc τ)
    rw [add_comm]
    exact this
  have hS : ∀ y : Mx D a b, (∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ≤ ∑ i, ℓ i y := by
    intro y
    simp only [Fintype.sum_prod_type]
    gcongr with τ _ k _ l _
    exact hterm y τ k l
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨C0, hC0⟩ := hf τ0 0 0
  choose Cf hCf using fun i : D.what₂.Tau × Fin a × Fin b × Bool => hf i.1 (zι i) N
  refine ⟨(Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * (C0 + ∑ i, Cf i), fun y => ?_⟩
  let u : Option (D.what₂.Tau × Fin a × Fin b × Bool) → ℝ := fun o => o.elim 1 fun i => ℓ i y
  have hu : ∀ o, 0 ≤ u o := fun o => by cases o <;> simp [u, ℓ]
  have hsum : ∑ o, u o = 1 + ∑ i, ℓ i y := by rw [Fintype.sum_option]; rfl
  have hpow : ∑ o, u o ^ N = 1 + ∑ i, ℓ i y ^ N := by rw [Fintype.sum_option]; simp [u]
  have hS0 : 0 ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by positivity
  have hf0 : 0 ≤ ‖f y‖ := norm_nonneg _
  have hC0' : ‖f y‖ ≤ C0 := by simpa using hC0 y
  have hCf' : ∑ i, ℓ i y ^ N * ‖f y‖ ≤ ∑ i, Cf i := Finset.sum_le_sum fun i _ => hCf i y
  calc (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖
      ≤ (1 + ∑ i, ℓ i y) ^ N * ‖f y‖ := by gcongr; exact hS y
    _ = (∑ o, u o) ^ N * ‖f y‖ := by rw [hsum]
    _ ≤ ((Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N * ∑ o, u o ^ N) * ‖f y‖ := by
        gcongr; exact sum_pow_le u hu N
    _ = (Fintype.card (Option (D.what₂.Tau × Fin a × Fin b × Bool)) : ℝ) ^ N *
          (‖f y‖ + ∑ i, ℓ i y ^ N * ‖f y‖) := by rw [hpow, ← Finset.sum_mul]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.DecayCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoPartPairing

open GlobalTheory.MixModel

theorem hO_isoPart {D : D7} (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1) (u y : Mx D W.rank r) :
    hO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) =
      (GlobalTheory.MixModel.adj y ⬝ (GlobalTheory.MixModel.gA W ⬝ u)).trace := by
  have hC0 : Cᴴ * V.gram * C' = 1 := hC
  have hC1 : C'ᴴ * V.gram * C = 1 := by
    have h := congrArg Matrix.conjTranspose hC0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u = u ⬝ rat (C'ᴴ * V.gram) := rfl
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ rat (Cᴴ * V.gram) := rfl
  have hg : giA V ⬝ adj (rat (Cᴴ * V.gram)) = rat C := by
    rw [← rat_conjTranspose, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      Matrix.conjTranspose_conjTranspose, giA, ← rat_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  rw [hx, hz, hO_eq_trace, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (giA V), hg]
  rw [show rat C ⬝ (adj y ⬝ (gA W ⬝ (u ⬝ rat (C'ᴴ * V.gram)))) = (rat C ⬝ adj y ⬝ gA W ⬝ u) ⬝ rat (C'ᴴ * V.gram) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hC1, rat_one,
    Matrix.one_mul, Matrix.mul_assoc]

theorem trHalf_add_self {D : D7} (z : AE D) :
    trHalf D z + trHalf D z = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z) := by
  show algebraMap D.host.F (AF D.host.F) (1 / 2) * _ + algebraMap D.host.F (AF D.host.F) (1 / 2) * _ = _
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem symplOH_isoPart_add_self : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  intro D V W r C C' hC u y
  rw [symplOH_eq, hO_isoPart V W C C' hC u y, trHalf_add_self]

end GlobalTheory.IsoPartPairing
end
end

