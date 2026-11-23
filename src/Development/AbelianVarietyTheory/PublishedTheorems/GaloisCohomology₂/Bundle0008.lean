module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryHeckeBaseChange
open scoped TensorProduct Topology HeckeCharacterZeroLocus.ThmBIn

namespace GlobalTheory.GalOfCusp

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem isCMExt_real : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (maximalRealSubfield E) E
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E : E →ₐ[maximalRealSubfield E] E) :=
  (isCMExt_iff _).2 ⟨inferInstance, rfl⟩

def adeleNorm : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) :=
  (Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))).comp
    (adeleEquiv (isCMExt_real E)).symm.toRingHom.toMonoidHom

theorem continuous_adeleNorm : Continuous (adeleNorm E) := by
  classical
  refine Continuous.comp (g := Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))) ?_
    (continuous_adeleEquiv_symm (isCMExt_real E))
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E)) (HeckeCharacterZeroLocus.ThmBIn.AE (maximalRealSubfield E) E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E))
    (Module.finBasis (maximalRealSubfield E) E)
  refine (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det.congr fun x => ?_
  exact (Algebra.norm_eq_matrix_det b x).symm

theorem adeleNorm_algebraMap (x : E) :
    adeleNorm E (algebraMap E _ x) = algebraMap _ _ (Algebra.norm (maximalRealSubfield E) x) := by
  have h : (adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x) = 1 ⊗ₜ x :=
    (adeleEquiv (isCMExt_real E)).symm_apply_eq.2 (toAdele_incA x).symm
  change Algebra.norm _ ((adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x)) = _
  rw [h, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext y
  simp

theorem adeleMap_adeleNorm (x : AdeleRing (𝓞 E) E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap _ E (adeleNorm E x) = x * adeleConj (maximalRealSubfield E) E x := by
  obtain ⟨z, rfl⟩ := (adeleEquiv (isCMExt_real E)).surjective x
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  rw [h, ← toAdele_algebraMap, GlobalTheory.Doubling.algebraMap_norm_eq (isCMExt_real E), map_mul]
  exact congrArg (_ * ·) (toAdele_cA z)

def ideleNorm : Ideles E →* Ideles (maximalRealSubfield E) := Units.map (adeleNorm E)

theorem ideleMap_ideleNorm (x : Ideles E) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (ideleNorm E x) =
    x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x := Units.ext (adeleMap_adeleNorm E x)

def compNorm : HChar (maximalRealSubfield E) →* HChar E where
  toFun χ := ⟨χ.1.comp (ideleNorm E), χ.2.1.comp (Continuous.units_map _ (continuous_adeleNorm E)), fun k => by
    rw [← χ.2.2 (Units.map (Algebra.norm (maximalRealSubfield E)) k)]
    exact congrArg χ.1 (Units.ext (adeleNorm_algebraMap E k))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem compNorm_apply (χ : HChar (maximalRealSubfield E)) (x : Ideles E) :
    (compNorm E χ).1 x = χ.1 (ideleNorm E x) := rfl

def quadChar : HChar (maximalRealSubfield E) :=
  ⟨(Units.map (Int.castRingHom ℂ).toMonoidHom).comp (GlobalTheory.IdeleNormChar.normSign E),
    continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : ℂˣ))).congr (by
      filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := maximalRealSubfield E) E] with a ha
      rw [MonoidHom.comp_apply, ha, map_one])),
    fun k => (congrArg (Units.map (Int.castRingHom ℂ).toMonoidHom) (GlobalTheory.IdeleNormChar.normSign_toUnits E k)).trans
      (map_one _)⟩

theorem compNorm_quadChar : compNorm E (quadChar E) = 1 :=
  Subtype.ext (MonoidHom.ext fun x => (congrArg (Units.map (Int.castRingHom ℂ).toMonoidHom)
    (GlobalTheory.IdeleNormChar.normSign_of_mem E
      ⟨Units.map (adeleEquiv (isCMExt_real E)).symm.toRingHom.toMonoidHom x, rfl⟩)).trans (map_one _))

theorem eta_neg_one (v : InfinitePlace (maximalRealSubfield E)) :
    GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E v.Completion (-1) = -1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := GlobalTheory.QuadSymbol.AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  have hv : v.IsReal := IsTotallyReal.isReal v
  rw [GlobalTheory.QuadSymbol.eta_eq_neg_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, h⟩
  have hc : IsCMField.complexConj E (b 1) = -b 1 := by
    have h2 : IsCMField.complexConj E (b 1) * IsCMField.complexConj E (b 1) = b 1 * b 1 := by
      rw [← map_mul, h1, AlgEquiv.commutes]
    refine (mul_self_eq_mul_self_iff.1 h2).resolve_left fun e => hδ ?_
    exact ⟨⟨b 1, (IsCMField.complexConj_eq_self_iff E _).1 e⟩, Subtype.ext h1.symm⟩
  have h3 := ComplexEmbedding.lift_algebraMap_apply E v.embedding δ
  have h4 := IsCMField.complexEmbedding_complexConj E (ComplexEmbedding.lift E v.embedding) (b 1)
  rw [hc, map_neg] at h4
  rw [← h1, map_mul] at h3
  have h5 : InfinitePlace.embedding_of_isReal hv δ ≤ 0 := by
    have h6 : ((InfinitePlace.embedding_of_isReal hv δ : ℝ) : ℂ) =
        ((-Complex.normSq (ComplexEmbedding.lift E v.embedding (b 1)) : ℝ) : ℂ) := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← h3, Complex.ofReal_neg, ← Complex.mul_conj, ← h4]
      ring
    rw [Complex.ofReal_injective h6]
    exact neg_nonpos.2 (Complex.normSq_nonneg _)
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have he : e (algebraMap _ v.Completion δ) = InfinitePlace.embedding_of_isReal hv δ := by
    simp only [e, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, ← WithAbs.equiv_symm_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply]
  have h7 := congrArg e h
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, he] at h7
  nlinarith [sq_nonneg (e x), mul_nonneg (neg_nonneg.2 h5) (sq_nonneg (e y))]

theorem quadChar_locInf (v : InfinitePlace (maximalRealSubfield E)) : (quadChar E).locInf v (-1) = -1 := by
  classical
  have h1 : ∀ (A : Type) [CommRing A] [Algebra (maximalRealSubfield E) A],
      GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E A 1 = 1 := fun A _ _ => GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (one_mem _)
  have h : GlobalTheory.IdeleNormChar.normSign E (infIdele _ v (-1)) = -1 := by
    change GlobalTheory.QuadSymbol.etaProd _ E _ _ = _
    unfold GlobalTheory.QuadSymbol.etaProd
    have e1 : GlobalTheory.IdeleNormChar.finComp (infIdele _ v (-1)) = 1 := funext fun _ => Units.ext rfl
    have e2 : ∀ u, u ≠ v → GlobalTheory.IdeleNormChar.infComp (infIdele _ v (-1)) u = 1 := fun u hu =>
      Units.ext (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace (maximalRealSubfield E) => w.Completion) hu _)
    have e3 : GlobalTheory.IdeleNormChar.infComp (infIdele _ v (-1)) v = -1 :=
      Units.ext (Pi.mulSingle_eq_same (M := fun w : InfinitePlace (maximalRealSubfield E) => w.Completion) v _)
    rw [e1, Finset.prod_eq_single v (fun u _ hu => by rw [e2 u hu, h1]) (by simp), e3, eta_neg_one]
    simp [h1]
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (infIdele _ v (-1))) = _
  rw [h]
  exact Units.ext (by simp)

variable {E} {a : ℕ}

def IsConjDualBy (π : CuspSub E a) (ψ : HChar E) : Prop :=
  ∃ T : π.V ≃ₗ[ℂ] (π.twist ψ⁻¹).V, ∀ o φ, T (π.op (thetaOp o) φ) = (π.twist ψ⁻¹).op o (T φ)

theorem isConjDualBy_one (π : CuspSub E a) : IsConjDualBy π 1 ↔ π.IsCsd := by
  rw [IsConjDualBy, inv_one, CuspSub.twist_one, CuspSub.IsCsd]

theorem isConjDualBy_twist {π : CuspSub E a} (h : π.IsCsd) {ξ ψ : HChar E}
    (hξ : ∀ o : Op E a, opMul ξ (thetaOp o) = opMul (ξ * ψ⁻¹) o ∧ opAdd ξ (thetaOp o) = opAdd (ξ * ψ⁻¹) o) :
    IsConjDualBy (π.twist ξ) ψ := by
  obtain ⟨T, hT⟩ := h
  rw [IsConjDualBy, ← CuspSub.twist_mul]
  refine ⟨((π.toTwist ξ).symm.trans T).trans (π.toTwist _), fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := (π.toTwist ξ).surjective φ
  simp only [CuspSub.op_toTwist, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add T, map_smul T, hT,
    (hξ o).1, (hξ o).2]

structure IsPolarized (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) : Prop where
  sign : ∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a
  dual : IsConjDualBy π (compNorm E χ)

theorem locInf_pow {K : Type} [Field K] [NumberField K] (χ : HChar K) (k : ℕ) (v : InfinitePlace K)
    (x : (v.Completion)ˣ) : (χ ^ k).locInf v x = χ.locInf v x ^ k := rfl

theorem IsConjDualBy.isPolarized {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)}
    (h : IsConjDualBy π (compNorm E χ)) {m : ℕ} (hχ : ∀ v, χ.locInf v (-1) = (-1) ^ m) :
    IsPolarized π (χ * quadChar E ^ (m + a)) := by
  constructor
  · intro v
    change χ.locInf v (-1) * (quadChar E ^ (m + a)).locInf v (-1) = (-1) ^ a
    rw [locInf_pow, hχ, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
  · rwa [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]

theorem isPolarized_of_isCsd {π : CuspSub E a} (h : π.IsCsd) : IsPolarized π (quadChar E ^ a) := by
  simpa using IsConjDualBy.isPolarized (π := π) (χ := 1) (by rw [map_one]; exact (isConjDualBy_one π).2 h) (m := 0)
    fun _ => rfl

theorem isPolarized_triv : IsPolarized (CuspSub.triv E (le_refl 1)) (quadChar E ^ 1) ∧
    (CG.mk (CuspSub.triv E (le_refl 1))).IsRegAlg := by
  refine ⟨isPolarized_of_isCsd ⟨.refl _ _, fun o φ => Subtype.ext ?_⟩, ?_⟩
  · obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
    change act (thetaOp o) φ.1 = act o φ.1
    rw [← e, map_smul, map_smul, act_oneFn, act_oneFn]
    cases o <;> rfl
  · rw [← CuspSub.twist_one (CuspSub.triv E (le_refl 1))]
    exact (CG.isRegAlg_ofChar 1).2 fun τ => ⟨0, by simp [CG.expo_one]⟩

end GlobalTheory.GalOfCusp
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def DepthZeroInduction : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s →
    (∀ y ∈ s, fixed y.rep (KOne k (Fin y.1)) ≠ ⊥) → fixed x.rep (KOne k (Fin x.1)) ≠ ⊥

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL

namespace GlobalTheory.DiscSpec

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a c d : ℕ} {n : Fin c → ℕ}

def finVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {v | FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k v))}
  add_mem' := fun {v w} (hv : FiniteDimensional _ _) (hw : FiniteDimensional _ _) =>
    Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => ρ k v) ⊔ Submodule.span ℂ (Set.range fun k => ρ k w))
      (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        simp only [map_add (f := _)]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)))
  zero_mem' := FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton 0).subset (by
    rintro _ ⟨k, rfl⟩
    simp))
  smul_mem' := fun z v (hv : FiniteDimensional _ _) =>
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => ρ k v))
      (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        simp only [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)))

def tensorForms (π : ∀ i, CuspSub E (n i)) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, (π i).V, F = fun m => ∏ i, (φ i).1.1 (m i)}

def indForms (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, φ.1 (u * g) = φ.1 g) ∧
    φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) ∧ φ ∈ finVec (cptRep E N) ∧
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => φ.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π}
  add_mem' := fun h1 h2 => ⟨fun u hu g => congrArg₂ (· + ·) (h1.1 u hu g) (h2.1 u hu g),
    add_mem h1.2.1 h2.2.1, add_mem h1.2.2.1 h2.2.2.1, fun k g => add_mem (h1.2.2.2 k g) (h2.2.2.2 k g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, zero_mem _, zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' z _ h1 := ⟨fun u hu g => congrArg (z • ·) (h1.1 u hu g), Submodule.smul_mem _ z h1.2.1,
    Submodule.smul_mem _ z h1.2.2.1, fun k g => Submodule.smul_mem _ z (h1.2.2.2 k g)⟩

def IsQuotOf (V I : Submodule ℂ (Sm E N)) : Prop :=
  ∃ f : Sm E N →ₗ[ℂ] Sm E N, I.map f = V ∧ ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)

def IsIsoGL (V V' : Submodule ℂ (Sm E N)) : Prop :=
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act o φ.1 → (T ψ).1 = act o (T φ).1

def spehExp (d : ℕ) (i : Fin d) : ℝ := ((d : ℝ) - 1) / 2 - (i : ℕ)

def IsSpehOf (V : Submodule ℂ (Sm E N)) (π : CuspSub E a) (d : ℕ) : Prop :=
  ∃ (h : ∑ _ : Fin d, a = N) (ν : Fin d → HChar E), (∀ i, (ν i).IsAbsPow (spehExp d i + a * spehExp d i)) ∧
    IsQuotOf V (indForms h fun i => π.twist (ν i))

def IsNormalised (π : CuspSub E a) : Prop := ∀ φ ∈ π.V, ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
structure HasSpehComp (V : Submodule ℂ (Sm E N)) (π : CuspSub E a) (d : ℕ) : Prop where
  exLoc : ∀ w, ∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ'
  loc : ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ
  inf : ∀ τ, ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m)

theorem IsSpehOf.mul_eq {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (h : IsSpehOf V π d) : d * a = N := by
  obtain ⟨h, -⟩ := h
  simpa using h

theorem mul_spehExp (a d : ℕ) (i : Fin d) : a * spehExp d i = (modExp (fun _ : Fin d => Fin a) i : ℝ) / 2 := by
  have h1 : Finset.univ.filter (fun b => i < b) = Finset.Ioi i := by ext; simp
  have h2 : Finset.univ.filter (fun b => b < i) = Finset.Iio i := by ext; simp
  have h3 : ((d - 1 - i : ℕ) : ℝ) = d - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  simp only [modExp, h1, h2, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, Fintype.card_fin, spehExp]
  push_cast
  rw [h3]
  ring

theorem fin_mem_indForms {h : ∑ i, n i = N} {π : ∀ i, CuspSub E (n i)} {φ : Sm E N} (hφ : φ ∈ indForms h π)
    (x : GL (Fin N) (Af E)) : act (.fin x) φ ∈ indForms h π := by
  refine ⟨fun u hu g => ?_, GlobalTheory.PRep.smoothPart_stable _ x φ hφ.2.1, ?_, fun k g => ?_⟩
  · change φ.1 (u * g * _) = φ.1 (g * _)
    rw [mul_assoc, hφ.1 u hu]
  · have : FiniteDimensional _ _ := hφ.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E N k φ)).map
      (finRep E N x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun g => ?_)⟩
    change φ.1 (g * finGL E N x * infGL E N _) = φ.1 (g * infGL E N _ * finGL E N x)
    rw [mul_assoc, mul_assoc, infGL_comm]
  · have := hφ.2.2.2 k (g * x)
    rw [map_mul] at this
    convert this using 2 with m
    change φ.1 (_ * finGL E N x) = _
    simp only [mul_assoc]

theorem indForms_one (h : ∑ _ : Fin 1, a = a) (π : CuspSub E a) : indForms h (fun _ => π) = π.V := by
  have he : ∀ b i, stdBlocks (fun _ : Fin 1 => a) h ⟨b, i⟩ = i := fun b i => Fin.ext (by
    rw [stdBlocks_val, Subsingleton.elim b 0]; simp)
  have hl : ∀ m, leviEmb (Ad E) (stdBlocks (fun _ : Fin 1 => a) h) m = m 0 := fun m => by
    ext i j
    have : ((leviEmb (Ad E) (stdBlocks (fun _ : Fin 1 => a) h) m : GL (Fin a) (Ad E)) :
        Matrix (Fin a) (Fin a) (Ad E)) (stdBlocks (fun _ : Fin 1 => a) h ⟨0, i⟩)
        (stdBlocks (fun _ : Fin 1 => a) h ⟨0, j⟩) = (m 0 : Matrix (Fin a) (Fin a) (Ad E)) i j := by
      simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
    rwa [he, he] at this
  refine le_antisymm (fun φ hφ => ?_) fun φ hφ => ⟨fun u hu g => ?_, (π.cusp φ hφ).1.level, (π.cusp φ hφ).1.kfin,
    fun k g => Submodule.subset_span ⟨fun _ => ⟨_, π.stable (.cpt k) _ (π.stable (.fin g) φ hφ)⟩, funext fun m => ?_⟩⟩
  · have key : ∀ F ∈ tensorForms fun _ : Fin 1 => π, ∃ ψ ∈ π.V, ∀ g, F (fun _ => g) = ψ.1 g := fun F hF => by
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨ψ, rfl⟩ := hF
        exact ⟨ψ 0, (ψ 0).2, fun g => by simp⟩
      | zero => exact ⟨0, zero_mem _, fun _ => rfl⟩
      | add F G _ _ hF hG =>
        obtain ⟨x, hx, e⟩ := hF
        obtain ⟨y, hy, e'⟩ := hG
        exact ⟨x + y, add_mem hx hy, fun g => congrArg₂ (· + ·) (e g) (e' g)⟩
      | smul z F _ hF =>
        obtain ⟨x, hx, e⟩ := hF
        exact ⟨z • x, Submodule.smul_mem _ _ hx, fun g => congrArg (z • ·) (e g)⟩
    obtain ⟨ψ, h1, h2⟩ := key _ (hφ.2.2.2 1 1)
    rwa [show φ = ψ from Subtype.ext (funext fun g => by simpa [hl] using h2 g)]
  · rw [show u = 1 from Units.ext (Matrix.ext fun i j => by
      have := (mem_unipRad.1 hu).2 0 i j
      rwa [he, he] at this), one_mul]
  · rw [hl, Fin.prod_univ_one, ← mul_assoc]
    rfl

end GlobalTheory.DiscSpec

namespace GlobalTheory.Published

open GlobalTheory.DiscSpec

def DiscreteSpectrumGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → HasSpehComp V π d

theorem DiscreteSpectrumGL.iso (H : DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π π' : CuspSub E a} (h : IsNormalised π)
    (h' : IsNormalised π') (e : IsSpehOf V π d) (e' : IsSpehOf V π' d) : π.Iso π' :=
  Quotient.exact (eq_of_heq (Sigma.mk.inj ((H E N hN).2.2.1 V hV a d a d π π' h h' e e').2).2)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def LanglandsExhaustionGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def StandardCosocleGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 : Multiset (Segment k)) (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x →
    ∃ π : IrrRep (GL (Fin N) k), IsCosocle π.ρ (prodIrr x hd)

end GlobalTheory.Published

end
end

