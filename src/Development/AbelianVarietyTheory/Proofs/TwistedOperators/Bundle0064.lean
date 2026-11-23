module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
section
open GlobalTheory.RegSS Matrix

namespace GlobalTheory.RegSS.Semilocal


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by
  ext i j
  simp only [_root_.GlobalTheory.RegSS.krylov, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec]
  congr 2
  exact RingHom.map_pow f.mapMatrix M _


open Matrix in
theorem _root_.GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField :
    _root_.GlobalTheory.RegSS.CyclicField → _root_.GlobalTheory.RegSS.CyclicSemilocal := by
  intro hF A _ _ n _ _ M hM
  have hw : ∀ p : MaximalSpectrum A, ∃ w : n → A ⧸ p.asIdeal,
      IsUnit (_root_.GlobalTheory.RegSS.krylov (M.map (Ideal.Quotient.mk p.asIdeal)) w).det := by
    intro p
    haveI := p.isMaximal
    letI := Ideal.Quotient.field p.asIdeal
    exact hF _ n _ (by rw [Matrix.charpoly_map]; exact hM.map)
  choose w hw using hw
  have hcop : Pairwise (Function.onFun IsCoprime fun p : MaximalSpectrum A => p.asIdeal) :=
    fun p q hpq => Ideal.isCoprime_iff_sup_eq.mpr
      (p.isMaximal.coprime_of_ne q.isMaximal (mt MaximalSpectrum.ext hpq))
  have hs : ∀ y : ∀ p : MaximalSpectrum A, A ⧸ p.asIdeal,
      ∃ a : A, ∀ p, Ideal.Quotient.mk p.asIdeal a = y p := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, fun p => by rw [← hx]; rfl⟩
  choose v hv using fun j => hs fun p => w p j
  refine ⟨v, ?_⟩
  by_contra h
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let p : MaximalSpectrum A := ⟨I, hI⟩
  have hvp : (Ideal.Quotient.mk p.asIdeal) ∘ v = w p := funext fun j => hv j p
  have hzero : Ideal.Quotient.mk p.asIdeal (_root_.GlobalTheory.RegSS.krylov M v).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [RingHom.map_det, RingHom.mapMatrix_apply, _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hvp] at hzero
  haveI := p.isMaximal
  exact (hw p).ne_zero hzero

end GlobalTheory.RegSS.Semilocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
section
open GlobalTheory.RegSS

noncomputable section

open Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.RegSS.IdemDet

theorem exists_factor {F m : Type} [Field F] [Fintype m] [DecidableEq m] (p : Matrix m m F)
    (h0 : p ≠ 0) (hp : p * p = p) :
    ∃ (d : ℕ) (A : Matrix m (Fin d) F) (B : Matrix (Fin d) m F), 0 < d ∧ A * B = p ∧ B * A = 1 := by
  let f := Matrix.toLin' p
  let c := Module.finBasis F (LinearMap.range f)
  let e := Pi.basisFun F m
  have hAB : LinearMap.toMatrix c e (LinearMap.range f).subtype *
      LinearMap.toMatrix e c f.rangeRestrict = p := by
    rw [← LinearMap.toMatrix_comp, show (LinearMap.range f).subtype ∘ₗ f.rangeRestrict = f from rfl]
    simp [e, f]
  refine ⟨_, _, _, ?_, hAB, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => h0 ?_
    haveI : IsEmpty (Fin (Module.finrank F (LinearMap.range f))) := by rw [h]; infer_instance
    rw [← hAB]; ext i j; simp [Matrix.mul_apply]
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id c]
    congr 1
    ext ⟨_, v, rfl⟩ : 2
    simp [f, hp]

theorem det_smul_idem {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] {d : ℕ}
    (A : Matrix m (Fin d) R) (B : Matrix (Fin d) m R) (h : B * A = 1) (t : R) :
    (t • (A * B) + 1 - A * B).det = t ^ d := by
  have e : t • (A * B) + 1 - A * B = 1 + ((t - 1) • A) * B := by
    rw [Matrix.smul_mul, sub_smul, one_smul]; abel
  rw [e, Matrix.det_one_add_mul_comm, Matrix.mul_smul, h, sub_smul, one_smul, add_sub_cancel]
  simp

section Rep

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    E ⊗[F] R →ₐ[F] Matrix ι ι R :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId F R)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom F R (Matrix ι ι R))
    (fun _ a => (Algebra.commutes a _).symm)

theorem regRep_tmul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] (x : E) (t : R) :
    regRep b R (x ⊗ₜ t) = t • (Algebra.leftMulMatrix b x).map (algebraMap F R) := by
  refine (Algebra.TensorProduct.lift_tmul _ _ _ x t).trans ?_
  rw [IsScalarTower.toAlgHom_apply, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

theorem continuous_regRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] :
    @Continuous _ _ (Formalism.BasicNotions.tensTopL (F := F) (E := E) R) _ (regRep b R) := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := moduleTopology R (E ⊗[F] R)
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := R) (regRep b R).toRingHom ?_
  have : ⇑((regRep b R).toRingHom.comp (algebraMap R (E ⊗[F] R))) =
      fun t : R => t • (Algebra.leftMulMatrix b 1).map (algebraMap F R) :=
    funext fun t => regRep_tmul b R 1 t
  rw [this]
  fun_prop

variable {n : Type} [Fintype n] [DecidableEq n]

def blockRep (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R] :
    Matrix n n (E ⊗[F] R) →+* Matrix (n × ι) (n × ι) R :=
  (Matrix.compRingEquiv n ι R).toRingHom.comp (regRep b R).toRingHom.mapMatrix

def blockRat (b : Module.Basis ι F E) : Matrix n n E →+* Matrix (n × ι) (n × ι) F :=
  (Matrix.compRingEquiv n ι F).toRingHom.comp (Algebra.leftMulMatrix b).toRingHom.mapMatrix

theorem blockRep_apply (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n (E ⊗[F] R)) (i j : n × ι) :
    blockRep b R g i j = regRep b R (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_apply (b : Module.Basis ι F E) (g : Matrix n n E) (i j : n × ι) :
    blockRat b g i j = Algebra.leftMulMatrix b (g i.1 j.1) i.2 j.2 := rfl

theorem blockRat_injective (b : Module.Basis ι F E) :
    Function.Injective (blockRat (n := n) b) := by
  intro g h e
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext k l
  exact congrFun (congrFun e (i, k)) (j, l)

theorem blockRep_map (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (g : Matrix n n E) :
    blockRep b R (g.map (inclE (F := F) R)) = (blockRat b g).map (algebraMap F R) := by
  ext i j
  rw [blockRep_apply, Matrix.map_apply, Matrix.map_apply, blockRat_apply]
  change regRep b R (g i.1 j.1 ⊗ₜ 1) _ _ = _
  rw [regRep_tmul, one_smul, Matrix.map_apply]

theorem blockRep_smul (b : Module.Basis ι F E) (R : Type) [CommRing R] [Algebra F R]
    (t : R) (g : Matrix n n (E ⊗[F] R)) :
    blockRep b R (((1 : E) ⊗ₜ[F] t) • g) = t • blockRep b R g := by
  ext i j
  rw [blockRep_apply, Matrix.smul_apply, Matrix.smul_apply, blockRep_apply, smul_eq_mul, map_mul,
    regRep_tmul, map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_apply]

end Rep

end GlobalTheory.RegSS.IdemDet

namespace GlobalTheory.RegSS

open IdemDet

theorem idempotentDet : IdempotentDet := by
  intro F E _ _ _ _ n _ _ ε h0 hε R _ _ _ _
  letI : TopologicalSpace (E ⊗[F] R) := Formalism.BasicNotions.tensTopL (F := F) (E := E) R
  let b := Module.finBasis F E
  have hq : blockRat b ε * blockRat b ε = blockRat b ε := by rw [← map_mul, hε]
  obtain ⟨d, A, B, hd, hAB, hBA⟩ := exists_factor (blockRat b ε)
    (fun h => h0 (blockRat_injective b (by rw [h, map_zero]))) hq
  set p := blockRep b R (ε.map (inclE (F := F) R)) with hp
  have hpq : p = (blockRat b ε).map (algebraMap F R) := blockRep_map b R ε
  have hpp : p * p = p := by rw [hpq, ← Matrix.map_mul, hq]
  refine ⟨d, fun g => (blockRep b R g * p + 1 - p).det, hd, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (blockRep (n := n) b R) := by
      refine continuous_matrix fun i j => ?_
      exact ((continuous_regRep b R).comp (continuous_id.matrix_elem i.1 j.1)).matrix_elem i.2 j.2
    exact (((hc.matrix_mul continuous_const).add continuous_const).sub continuous_const).matrix_det
  · simp
  · intro g h hh
    have hc : blockRep b R h * p = p * blockRep b R h := by
      rw [hp, ← map_mul, ← map_mul, hh]
    have h1 : p * (blockRep b R h * p) = blockRep b R h * p := by
      rw [← mul_assoc, ← hc, mul_assoc, hpp]
    simp only
    rw [← Matrix.det_mul, map_mul]
    congr 1
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, h1, hpp, mul_one, one_mul]
    abel
  · intro g
    refine ⟨(blockRat b g * blockRat b ε + 1 - blockRat b ε).det, ?_⟩
    simp only
    rw [RingHom.map_det, map_sub, map_add (f := _), map_mul, map_one, blockRep_map, hpq]
    rfl
  · intro g t hg
    have h1 : blockRep b R g * p = t • p := by
      rw [hp, ← map_mul, hg, blockRep_smul]
    simp only
    rw [h1, hpq, ← hAB, Matrix.map_mul]
    refine det_smul_idem _ _ ?_ t
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
section
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem splitClosed_etale (F P Ω n : Type) [Field F] [CommRing P] [Algebra F P] [Fintype n]
    [Algebra.Etale F P] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (h : Module.finrank F P = Fintype.card n) :
    Nonempty (Ω ⊗[F] P ≃ₐ[Ω] (n → Ω)) := by
  classical
  haveI : Module.Finite F P := Algebra.FormallyUnramified.finite_of_free F P
  haveI : IsArtinianRing (Ω ⊗[F] P) := isArtinian_of_tower Ω inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[F] P)
  letI : Fintype (PrimeSpectrum (Ω ⊗[F] P)) := Fintype.ofFinite _
  have hc : Fintype.card (PrimeSpectrum (Ω ⊗[F] P)) = Fintype.card n := by
    have := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_baseChange, h, Module.finrank_fintype_fun_eq_card] at this
    exact this.symm
  exact ⟨e.trans (AlgEquiv.piCongrLeft' Ω (fun _ => Ω) (Fintype.equivOfCardEq hc))⟩

theorem splitClosed_quad {F E : Type} [Field F] [CharZero F] [CommRing E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsQuadInvol F E σ) (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] :
    ∃ φ : E ⊗[F] Ω ≃ₐ[F] Ω × Ω, (∀ ω : Ω, φ (1 ⊗ₜ ω) = (ω, ω)) ∧
      ∀ u, φ (Algebra.TensorProduct.map σ (AlgHom.id F Ω) u) = (φ u).swap := by
  haveI := h.etale
  haveI := quad_finite h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨e⟩ := splitClosed_etale F E Ω (Fin 2) (by simp [h.finrank_eq])
  let θ : E →ₐ[F] Ω := (((Pi.evalAlgHom Ω (fun _ : Fin 2 => Ω) 0).comp e.toAlgHom).restrictScalars F).comp
    Algebra.TensorProduct.includeRight
  obtain ⟨b, d, -, hb1, hd, hbb⟩ := quad_exists_basis h
  have hc : θ (b 1) ≠ 0 := by
    intro h0
    have := congrArg θ hbb
    rw [map_mul, h0, mul_zero, AlgHom.commutes] at this
    exact hd ((map_eq_zero _).1 this.symm)
  let f : Ω ⊗[F] E →ₐ[Ω] Ω × Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω (Ω × Ω)) (θ.prod (θ.comp σ)) (fun _ _ => Commute.all _ _)
  have hf : ∀ ω x, f (ω ⊗ₜ x) = (ω * θ x, ω * θ (σ x)) := by
    intro ω x; simp [f, Algebra.ofId_apply]
  have hs : Function.Surjective f := by
    rintro ⟨x, y⟩
    refine ⟨((x + y) / 2) ⊗ₜ 1 + ((x - y) / (2 * θ (b 1))) ⊗ₜ b 1, ?_⟩
    rw [map_add (f := _), hf, hf, hb1, map_neg, map_one, map_one]
    ext <;> simp <;> field_simp <;> ring
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by simp [h.finrank_eq])).2 hs
  refine ⟨(Algebra.TensorProduct.comm F E Ω).trans
    ((AlgEquiv.ofBijective f ⟨hi, hs⟩).restrictScalars F), fun ω => (hf ω 1).trans (by simp), fun u => ?_⟩
  induction u with
  | tmul a w =>
    change f (w ⊗ₜ σ a) = (f (w ⊗ₜ a)).swap
    rw [hf, hf, h.invol]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hw, Prod.swap_add]

def splitClosedPair (F Ω n : Type) [Field F] [Field Ω] [Algebra F Ω] :
    ((n → Ω) × (n → Ω)) ≃ₐ[F] (n → Ω × Ω) where
  toFun x i := (x.1 i, x.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem splitClosed : SplitClosed := by
  intro F E _ _ _ _ σ h P _ _ n _ hP ⟨b⟩ Ω _ _ _
  obtain ⟨e⟩ := splitClosed_etale F P Ω n (Module.finrank_eq_card_basis b)
  obtain ⟨g, hg1, hg⟩ := splitClosed_quad h Ω
  let e' : P ⊗[F] Ω ≃ₐ[F] (n → Ω) := (Algebra.TensorProduct.comm F P Ω).trans (e.restrictScalars F)
  have he' : ∀ ω : Ω, e' (1 ⊗ₜ ω) = fun _ => ω := fun ω => e.commutes ω
  let φ : P ⊗[F] (E ⊗[F] Ω) ≃ₐ[F] (n → Ω × Ω) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[F] P) g).trans
      (Algebra.TensorProduct.prodRight F F P Ω Ω)).trans
      ((AlgEquiv.prodCongr e' e').trans (splitClosedPair F Ω n))
  have hφ : ∀ p x i, φ (p ⊗ₜ x) i = (e' (p ⊗ₜ (g x).1) i, e' (p ⊗ₜ (g x).2) i) := by
    intro p x i; rfl
  refine ⟨φ, fun ω => funext fun i => by rw [hφ, hg1, he'], fun u i => ?_⟩
  induction u with
  | tmul p x => rw [tConj3, Algebra.TensorProduct.map_tmul, hφ, hφ, hg]; rfl
  | add a w ha hw => rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, ha, hw, Prod.swap_add]

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
section
open Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem fieldUnitBounded_of_packing (hP : NormOnePacking) (hT : TensorLattice) :
    FieldUnitBounded := by
  unfold FieldUnitBounded
  intro F B _ _ _ _ _ τ hB hτ

  obtain ⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩ := hT F B
  let : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  have := hTop
  have := hLC
  have := hT2
  have := hSC

  have : Nontrivial B := ⟨hB.exists_pair_ne⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have : Infinite B := Infinite.of_injective (algebraMap F B) (algebraMap F B).injective
  have : NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) := by
    refine ⟨fun hU => ?_⟩
    have hfin := hdisc Set.univ hU
    simp only [Set.mem_univ, Set.ofPred_true] at hfin
    exact Set.infinite_univ hfin

  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable B := (Module.finBasis F B).equivFun.injective.countable

  let ι := inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)
  let Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F) := ι.toAddMonoidHom.range
  have hΛ : Countable Λ := by
    refine Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_
    rintro ⟨y, b, rfl⟩
    exact ⟨b, rfl⟩
  have hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧
      ∀ x, ∃ l ∈ Λ, x - l ∈ C' := by
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hcov x
    exact ⟨ι β, ⟨β, rfl⟩, hβ⟩

  obtain ⟨D, hD, hDu⟩ := hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F))
    (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨β, ⟨b, rfl⟩, hβ0, huβ⟩ := hDu u hu

  have hb : b ≠ 0 := by
    rintro rfl
    exact hβ0 (map_zero ι)
  obtain ⟨c, hc⟩ := hB.mul_inv_cancel hb
  exact ⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraic
section
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section

namespace GlobalTheory

open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

theorem isAlgebraic_embedding_apply {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (x : L) :
    IsAlgebraic ℚ (φ x) :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom

theorem heckeChar_val_isAlgebraic : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  intro L _ _ χ m hm w
  classical

  obtain ⟨h, hpos, hk⟩ := (classPow : ClassPow L)
  obtain ⟨k, hk⟩ := hk w
  have hkw : ordF w k = (h : ℤ) := by rw [hk w, if_pos rfl]
  have hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0 := by
    intro v hv
    rw [hk v, if_neg (by simpa using hv)]
  obtain ⟨r, hr, hdec⟩ := (decomp : Decomp L) k {w} hout
  rw [Finset.prod_singleton] at hdec
  have hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1 := by
    have e := χ.2.2 k
    rw [hdec, map_mul, map_mul] at e
    exact e
  obtain ⟨N, hN, hNt⟩ := torsUnits L χ

  have hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ) := by
    rw [hm k, ← mem_algebraicClosure_iff]
    refine prod_mem fun φ _ => zpow_mem ?_ _
    exact mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)

  have hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ) := by
    have e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹ := by
      have e1 := congrArg (· ^ N) hrel
      simp only [mul_pow, hNt r hr, mul_one, one_pow] at e1
      exact eq_inv_of_mul_eq_one_right e1
    refine IsAlgebraic.of_pow hN ?_
    rw [← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      ← mem_algebraicClosure_iff]
    exact inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)

  set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy
  have hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        WithZero.exp (-1) := unif_spec w
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1,
      valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hyU : localIdele L w y ∈ UFin L := by
    refine ⟨rfl, fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [localIdele_snd_self]
      exact hyv
    · rw [(localIdele_isSupportedAt L w y).2 v hv, map_one]
  have hyN : χ.loc w y ^ N = 1 := hNt _ hyU
  have hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹ := by
    rw [hy, map_mul, map_pow, map_inv]
    rfl
  have hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N := by
    rw [hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one] at hyN
    exact hyN
  refine IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hloc) _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjoint
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem pointsAdjoint_toMat_tmul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (c : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ c) = c • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l c

theorem pointsAdjoint : PointsAdjoint := by
  intro F E _ _ _ _ n _ _ σ J γ h R _ _ u
  induction u using TensorProduct.induction_on with
  | zero => simp [adj_zero]
  | tmul a b =>
    have ha := (adj_eq_iff _ h.nondeg _ _).2 a.2
    have hc : lConj σ J (γ : Matrix n n E) R (a ⊗ₜ b) = a ⊗ₜ sigR σ R b := rfl
    rw [hc, pointsAdjoint_toMat_tmul,
      pointsAdjoint_toMat_tmul, adj_smul,
      adj_map (σ : E →+* E) (sigR σ R) (inclE (F := F) R) (inclE_conj σ R) h.nondeg, ha]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), adj_add, ha, hb]

end GlobalTheory.RegSS
end

