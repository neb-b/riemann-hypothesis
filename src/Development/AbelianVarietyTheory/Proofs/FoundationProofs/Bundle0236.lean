module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0148
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible
section
open scoped Matrix

namespace GlobalTheory.AugSpan

theorem exists_mem_span_sub_one_eq_id_on :
    ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ}
      (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) →
      (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) →
      ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  intro K _ _ Γ _ m S P hst hirrP hnt
  classical
  set J := Submodule.span K (Set.range fun g => S g - 1) with hJ
  obtain ⟨g₀, v₀, hv₀, hne⟩ := hnt
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hv₀
    apply hne
    rw [hv₀, Matrix.mulVec_zero]
  have hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv
  let r : Representation K Γ P :=
    { toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K) :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => hP ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule K P) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map P.subtype ≤ P := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases hirrP _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule K P)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  have hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : S g * (S h - 1) = (S (g * h) - 1) - (S g - 1) := by
        rw [map_mul, mul_sub, mul_one]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (S h - 1) * S g = (S (h * g) - 1) - (S g - 1) := by
        rw [map_mul, sub_mul, one_mul]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  let J' : Submodule K (Module.End K P) :=
    { carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w}
      add_mem' := by
        rintro f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩
        exact ⟨T + T', J.add_mem hT hT', fun w => by
          rw [Matrix.add_mulVec, hTf, hTf']; simp⟩
      zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩
      smul_mem' := by
        rintro c f ⟨T, hT, hTf⟩
        exact ⟨c • T, J.smul_mem c hT, fun w => by
          rw [Matrix.smul_mulVec, hTf]; simp⟩ }
  have hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w := fun f => Iff.rfl
  have hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]
    | zero => rw [zero_mul]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact J'.smul_mem c hx
  have hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]
    | zero => rw [mul_zero]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact J'.smul_mem c hx
  set f₀ : Module.End K P := r g₀ - 1 with hf₀def
  have hf₀ : f₀ ∈ J' := (hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]; rfl⟩
  set w₀ : P := ⟨v₀, hv₀⟩ with hw₀
  have hfw : f₀ w₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)
  let b := Module.finBasis K P
  have hid : (1 : Module.End K P) ∈ J' := by
    have heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ *
        ((b.coord i).smulRight w₀) := by
      ext1 w
      rw [LinearMap.sum_apply, Module.End.one_apply]
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, smul_smul, Module.Basis.coord_apply]
      congr 1
      field_simp
    rw [heq]
    exact J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)
  obtain ⟨T, hT, hTid⟩ := (hmem _).1 hid
  exact ⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩

end GlobalTheory.AugSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsComplexEndomorphismEqOnCountable
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem exists_top_embedding_eq_on_countable (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ)
    (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let A : Set M := {y | (y : ℂ) ∈ S}
  have hA : A.Countable := hS.preimage Subtype.val_injective
  let k : Subfield M := Subfield.closure A
  haveI : Countable k := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max A).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hA.to_subtype
  obtain ⟨τ, hτ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := k)
    ((M.val : M →+* ℂ).comp k.subtype) ((ρ : M →+* ℂ).comp k.subtype)
  refine ⟨(τ.toRingHom.toRatAlgHom).comp (⊤ : IntermediateField ℚ ℂ).val, fun x hx hxM => ?_⟩
  have h := hτ ⟨⟨x, hxM⟩, Subfield.subset_closure hx⟩
  have h1 : liftM ⊤ x = ⟨x, IntermediateField.mem_top⟩ := dif_pos IntermediateField.mem_top
  have h2 : liftM M x = ⟨x, hxM⟩ := dif_pos hxM
  unfold cj
  rw [h1, h2]
  exact h

end GlobalTheory.GalTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR
section
namespace GlobalTheory.TraceConjugacy

open Matrix

theorem exists_conj_of_surjective {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    {a : ℕ} (φ φ' : A →ₐ[O] Matrix (Fin a) (Fin a) O) (hφ : Function.Surjective φ)
    (htr : ∀ x, (φ x).trace = (φ' x).trace) :
    ∃ U : GL (Fin a) O, ∀ x, φ' x * (U : Matrix (Fin a) (Fin a) O) = U * φ x := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨1, fun x => Subsingleton.elim _ _⟩
  obtain ⟨s, hs⟩ := φ.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hφ)
  have hs' : ∀ X, φ (s X) = X := fun X => LinearMap.congr_fun hs X
  let θ : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O := φ'.toLinearMap ∘ₗ s
  have hθ : ∀ X, θ X = φ' (s X) := fun X => rfl
  let T : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O :=
    { toFun := fun X => Matrix.of fun i j => (X * θ (Matrix.single j i 1)).trace
      map_add' := fun X Y => by ext i j; simp [add_mul]
      map_smul' := fun c X => by ext i j; simp }
  have hT : ∀ x, T (φ' x) = φ x := by
    intro x
    ext i j
    change (φ' x * θ (Matrix.single j i 1)).trace = _
    rw [hθ, ← map_mul, ← htr, map_mul, hs', Matrix.trace_mul_single]
    simp
  have hTinj : Function.Injective T :=
    OrzechProperty.injective_of_surjective_endomorphism T fun X =>
      ⟨φ' (s X), by rw [hT, hs']⟩
  have hfac : ∀ x, θ (φ x) = φ' x := fun x => hTinj (by rw [hθ, hT, hT, hs'])
  have hmul : ∀ X Y, θ X * θ Y = θ (X * Y) := by
    intro X Y
    rw [hθ, hθ, ← map_mul, ← hfac, map_mul, hs', hs']
  let o : Fin a := ⟨0, ha⟩
  have h1 : ∑ y, θ (Matrix.single o o 1) y y = 1 := by
    have := htr (s (Matrix.single o o 1))
    rw [hs', Matrix.trace_single_eq_same] at this
    exact this.symm
  obtain ⟨y, -, hy⟩ := IsLocalRing.exists_of_isUnit_sum (show IsUnit (∑ y, θ (Matrix.single o o 1) y y) by
    rw [h1]; exact isUnit_one)
  let U : Matrix (Fin a) (Fin a) O := Matrix.of fun x i => θ (Matrix.single i o 1) x y
  let V : Matrix (Fin a) (Fin a) O := Matrix.of fun j x => θ (Matrix.single o j 1) y x
  have hVU : V * U = θ (Matrix.single o o 1) y y • (1 : Matrix (Fin a) (Fin a) O) := by
    ext j i
    have : (V * U) j i = (θ (Matrix.single o j 1) * θ (Matrix.single i o 1)) y y := by
      simp [Matrix.mul_apply, U, V]
    rw [this, hmul]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hij]
      simp [hij]
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := congrArg Matrix.det hVU
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact isUnit_of_mul_isUnit_right (this ▸ hy.pow _)
  refine ⟨hU.unit, fun z => ?_⟩
  rw [IsUnit.unit_spec, ← hfac]
  ext x i
  have h2 : (θ (φ z) * U) x i = (θ (φ z) * θ (Matrix.single i o 1)) x y := by
    simp [Matrix.mul_apply, U]
  have h3 : φ z * Matrix.single i o (1 : O) = ∑ k, φ z k i • Matrix.single k o (1 : O) := by
    ext p q
    by_cases hq : q = o
    · subst hq
      simp [Matrix.sum_apply, Matrix.single_apply]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq]
      simp [Matrix.sum_apply, Matrix.single_apply, Ne.symm hq]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, hmul, h3, map_sum, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem span_eq_top_of_residue {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (M g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | (apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top ..)

theorem exists_conj_of_trace_eq_local {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {a : ℕ} (ρ ρ' : Γ →* GL (Fin a) O)
    (h : Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤)
    (htr : ∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace =
      ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) :
    ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  have hspan : Submodule.span O
      (Set.range fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) = ⊤ :=
    by
    refine span_eq_top_of_residue _ ?_
    have h0 := GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ h
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) = fun g =>
        ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (IsLocalRing.residue O) := by
      funext g
      rfl
    rwa [h1] at h0
  let φ : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ)
  let φ' : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ')
  have hφ : ∀ g c, φ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ]
  have hφ' : ∀ g c, φ' (MonoidAlgebra.single g c) = c • (ρ' g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ']
  have hsurj : Function.Surjective φ := by
    have : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simpa using hφ g 1⟩
    exact LinearMap.range_eq_top.1 this
  have htr' : ∀ x, (φ x).trace = (φ' x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single g c => rw [hφ, hφ', Matrix.trace_smul, Matrix.trace_smul, htr]
  obtain ⟨U, hU⟩ := exists_conj_of_surjective φ φ' hsurj htr'
  refine ⟨U, fun g => Units.ext ?_⟩
  have := hU (MonoidAlgebra.single g 1)
  rwa [hφ, hφ', one_smul, one_smul] at this

theorem exists_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g :=
  fun _ _ _ _ _ _ _ ρ ρ' h htr => exists_conj_of_trace_eq_local ρ ρ' h htr

end GlobalTheory.TraceConjugacy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := _root_.GlobalTheory.FN.frac_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := _root_.GlobalTheory.FN.j_in_frac Ω ε T
  have hgerm := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  have hj := _root_.GlobalTheory.FN.jT_level_one
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (_root_.GlobalTheory.FN.inR_mdifferentiable ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (_root_.GlobalTheory.FN.frac_sl_right_action Ω ε T).1, sl_mul := (_root_.GlobalTheory.FN.frac_sl_right_action Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).1, an_sl := _root_.GlobalTheory.FN.an_sl_germ Ω ε T, an_mero := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).2,
            an_exp := fun f => (_root_.GlobalTheory.FN.frac_exp_converges Ω ε T f).2,
            level := _root_.GlobalTheory.FN.frac_exists_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := _root_.GlobalTheory.FNRecip.main Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := _root_.GlobalTheory.FN.frac_isAlgebraic_adjoin_j Ω ε T a ha, bdd := _root_.GlobalTheory.FN.frac_bdd_den Ω ε T, sat := _root_.GlobalTheory.fn_sat Ω ε T,
            mem_q := _root_.GlobalTheory.FN.exists_of_qexp Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeightStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  first | exact @GlobalTheory.HarmonicShape.weight_eq_wtK | exact GlobalTheory.HarmonicShape.weight_eq_wtK | (intros; apply GlobalTheory.HarmonicShape.weight_eq_wtK <;> assumption)
end

