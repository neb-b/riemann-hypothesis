module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0070

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA
section
open scoped TensorProduct

namespace GlobalTheory

theorem isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let q' : Ideal D := q.comap (e : D →+* C)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have H : q'.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let f : Localization.AtPrime q' ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q') (Localization.AtPrime q) e H
  obtain ⟨h1, h2⟩ := h q'
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end GlobalTheory

namespace GlobalTheory


open Algebra.TensorProduct in
theorem exists_finset_mem_range_map_val {F A K : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field K] [Algebra F K] (x : A ⊗[F] K) :
    ∃ T : Finset K, ∀ R : Subalgebra F K, (↑T : Set K) ⊆ (R : Set K) →
      x ∈ (Algebra.TensorProduct.map (AlgHom.id F A) R.val).range := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun R _ ↦ Subalgebra.zero_mem _⟩
  | tmul a k =>
    refine ⟨{k}, fun R hR ↦ ⟨a ⊗ₜ ⟨k, hR (by simp)⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨T₁, h₁⟩ := hx
    obtain ⟨T₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, fun R hR ↦ Subalgebra.add_mem _ (h₁ R ?_) (h₂ R ?_)⟩
    · exact fun z hz ↦ hR (by simp [hz])
    · exact fun z hz ↦ hR (by simp [hz])

theorem isDomain_and_isIntegrallyClosed_atPrime_tensor_field
    (hL1 : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K),
      ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R)
    (hL2 : ∀ (B : Type) [CommRing B] (Q : Ideal B) [Q.IsPrime],
      (∀ s : Finset B, ∃ C : Subring B, (↑s : Set B) ⊆ (C : Set B) ∧
        ∀ (q : Ideal C) [q.IsPrime],
          IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) →
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) :
    ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A] [Algebra F A],
      (∀ (P : Ideal A) [P.IsPrime],
        IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime],
        IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro F K A _ _ _ _ _ _ hA Q _
  classical
  refine hL2 (TensorProduct F A K) Q fun s ↦ ?_
  choose T hT using fun x : A ⊗[F] K ↦ exists_finset_mem_range_map_val (F := F) x
  obtain ⟨R, hR, hsm⟩ := hL1 F K (s.biUnion T)
  let φ : A ⊗[F] R →ₐ[F] A ⊗[F] K := Algebra.TensorProduct.map (AlgHom.id F A) R.val
  have hφ : ⇑φ = ⇑(LinearMap.lTensor A (R.val.toLinearMap)) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a k => simp [φ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hinj : Function.Injective φ := by
    rw [hφ]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  refine ⟨φ.range.toSubring, fun x hx ↦ hT x R (fun z hz ↦ hR ?_), ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩
  · let e : A ⊗[F] R ≃+* φ.range.toSubring := (AlgEquiv.ofInjective φ hinj).toRingEquiv
    exact isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv e fun q _ ↦
      isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall A hA q _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAway
section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_away : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A),
    IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} →
      IsExcisionNbhd A (Localization.Away a) h := by
  intro A A' _ _ _ h ⟨hE, hS, hI⟩ a b hab
  have hpow : ∀ n : ℕ, a ^ n * b ^ n - 1 ∈ Ideal.span {algebraMap A A' h} := by
    intro n
    have hd : a * b - 1 ∣ (a * b) ^ n - 1 ^ n := sub_dvd_pow_sub_pow _ _ _
    rw [one_pow, mul_pow] at hd
    obtain ⟨c, hc⟩ := hd
    rw [hc]
    exact Ideal.mul_mem_right _ _ hab
  have hH : algebraMap A (Localization.Away a) h =
      algebraMap A' (Localization.Away a) (algebraMap A A' h) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hmap : ∀ x : A', x ∈ Ideal.span {algebraMap A A' h} →
      algebraMap A' (Localization.Away a) x ∈ Ideal.span {algebraMap A (Localization.Away a) h} := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [hH, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_, ?_⟩
  · haveI := hE
    haveI : Algebra.Etale A' (Localization.Away a) := inferInstance
    exact Algebra.Etale.comp A A' (Localization.Away a)
  · intro z
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) z
    obtain ⟨n, hn⟩ := s.2
    obtain ⟨c, hc⟩ := hS (y * b ^ n)
    refine ⟨c, ?_⟩
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have e1 : IsLocalization.mk' (Localization.Away a) y s - algebraMap A (Localization.Away a) c =
        -(IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n * b ^ n - 1)) +
          algebraMap A' (Localization.Away a) (y * b ^ n - algebraMap A A' c) := by
      rw [map_sub, map_sub, map_mul, map_mul, map_one, ← hs, ← IsScalarTower.algebraMap_apply]
      ring
    rw [e1]
    exact Ideal.add_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hmap _ (hpow n)))) (hmap _ hc)
  · intro x hx
    apply hI
    rw [hH] at hx
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) w
    obtain ⟨n, hn⟩ := s.2
    dsimp only at hw
    have hs : IsLocalization.mk' (Localization.Away a) y s * algebraMap A' (Localization.Away a) (a ^ n) =
        algebraMap A' (Localization.Away a) y := by
      have hn' : a ^ n = (s : A') := hn
      rw [hn']; exact IsLocalization.mk'_spec _ _ _
    have key : algebraMap A' (Localization.Away a) (algebraMap A A' x * a ^ n - y * algebraMap A A' h) = 0 := by
      rw [map_sub, map_mul, map_mul, ← hs, ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) x, ← hw,
        ← IsScalarTower.algebraMap_apply A A' (Localization.Away a) h]
      ring
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).1 key
    obtain ⟨N, hN⟩ := m.2
    have h1 : algebraMap A A' x * a ^ (N + n) ∈ Ideal.span {algebraMap A A' h} := by
      have e : algebraMap A A' x * a ^ (N + n) = (a ^ N * y) * algebraMap A A' h := by
        rw [← hN] at hm; rw [pow_add]; linear_combination hm
      rw [e]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have e2 : algebraMap A A' x = algebraMap A A' x * a ^ (N + n) * b ^ (N + n) -
        algebraMap A A' x * (a ^ (N + n) * b ^ (N + n) - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ (hpow _))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfOpenCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff


set_option backward.isDefEq.respectTransparency.types false in
theorem of_isPullback_openImmersions (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {X T : Scheme.{0}} (φ : X ⟶ T) {ι : Type u} {V : ι → Scheme.{0}} (f : ∀ i, V i ⟶ T)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ x : T, ∃ i y, f i y = x)
    {Z : ι → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (q : ∀ i, Z i ⟶ V i)
    (H : ∀ i, IsPullback (k i) (q i) φ (f i)) (hq : ∀ i, P (q i)) : P φ := by
  have hU : iSup (fun i => (f i).opensRange) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun i => ?_
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange φ (f i))).mpr ?_
  rw [← (H i).isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr (hq i)

set_option backward.isDefEq.respectTransparency.types false in
theorem good_of_cover : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : T, ∃ i y, f i y = x) →
    ∀ (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) →
    GlobalTheory.HilbAff.Good A B r g I := by
  intro A B _ _ _ r T ι V f hf hcov g I hG
  have H : ∀ i, IsPullback (pullback.snd (bc A B g (f i)) I.subschemeι)
      (pullback.fst (bc A B g (f i)) I.subschemeι ≫ pullback.snd _ (f i ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) (f i) := fun i =>
    (IsPullback.of_hasPullback (bc A B g (f i)) I.subschemeι).flip.paste_vert
      (isPullback_bc A B g (f i))
  have e : ∀ i, (I.comap (bc A B g (f i))).subschemeι ≫ pullback.snd _ (f i ≫ g) =
      (I.comapIso (bc A B g (f i))).hom ≫ (pullback.fst (bc A B g (f i)) I.subschemeι ≫
        pullback.snd _ (f i ≫ g)) := fun i => by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hfin : ∀ i, IsFinite (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @IsFinite.{0}] at h
    exact h
  have hfl : ∀ i, Flat (pullback.fst (bc A B g (f i)) I.subschemeι ≫
      pullback.snd _ (f i ≫ g)) := fun i => by
    have h := (hG i).2.1
    rw [e i, MorphismProperty.cancel_left_of_respectsIso @Flat.{0}] at h
    exact h
  have : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance
  have h1 : IsFinite (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @IsFinite.{0} _ f hcov _ _ H hfin
  have h2 : Flat (I.subschemeι ≫ pullback.snd _ g) :=
    of_isPullback_openImmersions @Flat.{0} _ f hcov _ _ H hfl
  refine ⟨h1, h2, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := hcov y
  have h := (hG i).2.2 y'
  rw [e i, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (H i) y'] at h
  exact h

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGL
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrbIsLat

theorem single_mem_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (i : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ∈ stdLat O n := by
  rw [mem_stdLat]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem stdLat_eq_span {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    stdLat O n = Submodule.span O (Set.range fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLat] at hv
    choose a ha using hv
    have hv' : v = ∑ i, a i • (Pi.single i (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLat n i

theorem stdLat_fg {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) :
    (stdLat O n : Submodule O (Fin n → K)).FG := by
  rw [stdLat_eq_span]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.LatOrbIsLat

open GlobalTheory.LatOrbIsLat in
theorem GlobalTheory.LatOrb.matLat_stdLat_isLatV : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  intro O K _ _ _ n g
  refine ⟨(stdLat_fg n).map _, ?_⟩
  rw [eq_top_iff]
  intro v _
  set w : Fin n → K := (g⁻¹ : GL (Fin n) K).val *ᵥ v with hw
  have hgw : g.val *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hw' : w = ∑ i, w i • (Pi.single i (1 : K) : Fin n → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ i, w i • Matrix.mulVecLin g.val (Pi.single i (1 : K)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, ← hw']
    rw [Matrix.mulVecLin_apply, hgw]
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show _ ∈ matLat O g.val (stdLat O n)
  rw [mem_matLat]
  exact ⟨_, single_mem_stdLat n i, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixOfMapsToFullRankLattice
section
open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem isIntegral_of_mapsTo_lattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  intro O K _ _ _ n M hM c hc
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hM.1
  let f : Module.End O M :=
    { toFun := fun v => ⟨c *ᵥ (v : Fin n → K), hc v v.2⟩
      map_add' := fun x y => by ext1; simp [Matrix.mulVec_add]
      map_smul' := fun a x => by
        ext1
        simp only [Submodule.coe_smul, RingHom.id_apply, SetLike.val_smul]
        rw [Matrix.mulVec_smul] }
  have hpow : ∀ k : ℕ, ∀ v : M, (c ^ k) *ᵥ (v : Fin n → K) = (((f ^ k) v : M) : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, Module.End.mul_apply]
      have h1 : ((f v : M) : Fin n → K) = c *ᵥ (v : Fin n → K) := rfl
      rw [← h1, ih]
  have key : ∀ q : O[X], ∀ v : M, aeval c q *ᵥ (v : Fin n → K) = (((aeval f q) v : M) : Fin n → K) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq => intro v; simp [Matrix.add_mulVec, hp, hq]
    | monomial k a =>
      intro v
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        Matrix.smul_mulVec, LinearMap.smul_apply, Submodule.coe_smul, hpow]
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  refine ⟨p, hp, ?_⟩
  rw [← Polynomial.aeval_def]
  set A := aeval c p
  have hker : Submodule.span K (M : Set (Fin n → K)) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    intro v hv
    have := key p ⟨v, hv⟩
    rw [hpf] at this
    simpa using this
  rw [hM.2, top_le_iff, LinearMap.ker_eq_top] at hker
  have : Matrix.toLin' A = 0 := by rw [Matrix.toLin'_apply']; exact hker
  simpa using this

end GlobalTheory.LatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial

namespace GlobalTheory.QFam

theorem isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by
  classical
  set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))
  have hdeg : Q.natDegree = (Finset.univ : Finset ι).card := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]
    simp
  have hl : Q ∈ Polynomial.lifts (algebraMap R ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ (Finset.univ : Finset ι).card
    · rw [hQ, Finset.prod_X_add_C_coeff _ _ hn]
      exact ⟨⟨_, h _⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  have hneg : IsIntegral R (-x i) := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simpa using hneg.neg

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowersStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))) → IsIntegral (w.adicCompletionIntegers E) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.isIntegral_of_isCompact_closure_zpowers | exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.isIntegral_of_isCompact_closure_zpowers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOne
section
open GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.AffineCurveNbhd

theorem isNbhd_away_of_add_mul_eq_one (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A')
    (hN : IsNbhd B A' f) (hh : h + algebraMap B A' f * c = 1) : IsNbhd B (Localization.Away h) f := by
  set F := algebraMap B A' f with hF
  have hpow : ∀ m : ℕ, F ∣ h ^ m - 1 := by
    intro m
    have h1 : F ∣ h - 1 := ⟨-c, by linear_combination hh⟩
    have := sub_dvd_pow_sub_pow h 1 m
    rw [one_pow] at this
    exact h1.trans this
  have hL : ∀ b : B, algebraMap B (Localization.Away h) b =
      algebraMap A' (Localization.Away h) (algebraMap B A' b) := fun b =>
    IsScalarTower.algebraMap_apply B A' (Localization.Away h) b
  refine ⟨?_, ?_⟩
  · intro a'
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) a'
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    rw [← hn] at hs
    obtain ⟨b, hb⟩ := hN.1 x
    rw [Ideal.mem_span_singleton] at hb
    obtain ⟨d, hd⟩ := hb
    refine ⟨b, ?_⟩
    rw [Ideal.mem_span_singleton, hL b, hL f]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h |>.exists_right_inv
    have hu1 : algebraMap A' (Localization.Away h) F ∣ u - 1 := by
      refine ⟨algebraMap A' (Localization.Away h) c * u, ?_⟩
      have := congrArg (algebraMap A' (Localization.Away h)) hh
      simp only [map_add (f := _), map_mul, map_one] at this
      linear_combination hu - u * this
    have hun : algebraMap A' (Localization.Away h) F ∣ u ^ n - 1 := by
      have := sub_dvd_pow_sub_pow u 1 n
      rw [one_pow] at this
      exact hu1.trans this
    obtain ⟨e, he⟩ := hun
    have ha' : a' = algebraMap A' (Localization.Away h) x * u ^ n := by
      have : a' * (algebraMap A' (Localization.Away h) h * u) ^ n = a' := by rw [hu, one_pow, mul_one]
      rw [← this, mul_pow, ← mul_assoc, ← map_pow, hs]
    refine ⟨algebraMap A' (Localization.Away h) x * e + algebraMap A' (Localization.Away h) d, ?_⟩
    have hx : algebraMap A' (Localization.Away h) x =
        algebraMap A' (Localization.Away h) (algebraMap B A' b) + algebraMap A' (Localization.Away h) F *
          algebraMap A' (Localization.Away h) d := by
      rw [← map_mul, ← map_add (f := _), ← hd]; ring_nf
    rw [ha']
    linear_combination (algebraMap A' (Localization.Away h) x) * he + hx
  · intro a ha
    rw [Ideal.mem_span_singleton, hL a, hL f] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) y
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    simp only at hs
    have heq : algebraMap A' (Localization.Away h) (algebraMap B A' a * h ^ n) =
        algebraMap A' (Localization.Away h) (F * x) := by
      rw [map_mul, map_mul, hy, ← hs, hn]; ring
    obtain ⟨⟨k, hk⟩, hk'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp heq
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hk
    simp only at hk'
    apply hN.2
    rw [Ideal.mem_span_singleton]
    obtain ⟨g, hg⟩ := hpow (m + n)
    refine ⟨h ^ m * x - g * algebraMap B A' a, ?_⟩
    rw [← hF]
    linear_combination hk' - algebraMap B A' a * hg

end GlobalTheory.AffineCurveNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfUnitMulComulEqTmulSelfStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul : ∀ (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H] (c : H ⊗[K] H), IsUnit c → ∀ u : H, u ≠ 0 → c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u → IsUnit u := by
  first | exact @GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | exact GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self | (intros; apply GlobalTheory.isUnit_of_unit_mul_comul_eq_tmul_self <;> assumption)
end

