module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer
section
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  intro p hp O _ _ _ hp0 hpu hroot G n b hb

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  haveI : ExpChar (IsLocalRing.ResidueField O) p := ExpChar.prime hp.out
  haveI : PerfectRing (IsLocalRing.ResidueField O) p :=
    PerfectRing.ofSurjective _ p (fun y => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := hroot a
      exact ⟨IsLocalRing.residue O c, by rw [frobenius_def, ← map_pow, hc]⟩)

  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower O (G.A n) (G.A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)).commutes c).symm
  haveI : Module.Flat (G.A n) (G.A (n + 1)) := GlobalTheory.T.mulP_flat' p O G n
  have hε : ∀ b : G.A n, Bialgebra.counitAlgHom O (G.A (n + 1)) (algebraMap (G.A n) (G.A (n + 1)) b) =
      Bialgebra.counitAlgHom O (G.A n) b := fun b => by
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact CoalgHomClass.counit_comp_apply (G.mulP n) b
  have hker : (RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1))) =
      RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hε]

  obtain ⟨ρ, hρ⟩ : ∃ ρ : G.A (n + 1) →+* IsLocalRing.ResidueField O ⊗[O] G.A 1,
      ∀ a, ρ a = 1 ⊗ₜ G.resOne n a :=
    ⟨(Algebra.TensorProduct.includeRight : G.A 1 →ₐ[O] IsLocalRing.ResidueField O ⊗[O] G.A 1).toRingHom.comp
      ((G.resOne n : G.A (n + 1) →ₐ[O] G.A 1) : G.A (n + 1) →+* G.A 1), fun _ => rfl⟩
  have hπs : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hπk : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hfib := _root_.GlobalTheory.fibre_statement p O (IsLocalRing.ResidueField O) hπs G n
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hfib.1 h
    exact ⟨a, by rw [hρ]; exact ha⟩
  have hkerρ : RingHom.ker ρ = (RingHom.ker ((algebraMap O (IsLocalRing.ResidueField O)).comp
      ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))))).map
      (algebraMap (G.A n) (G.A (n + 1))) := by
    have hcomp : (algebraMap O (IsLocalRing.ResidueField O)).comp
        ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))) =
        (algebraMap O (IsLocalRing.ResidueField O)).comp (Bialgebra.counitAlgHom O (G.A n) : G.A n →+* O) :=
      RingHom.ext fun b => by
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hε]
    rw [hcomp]
    ext a
    rw [RingHom.mem_ker, hρ]
    exact hfib.2 a
  have hρalg : ∀ c : O, ρ (algebraMap O (G.A (n + 1)) c) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)
        (algebraMap O (IsLocalRing.ResidueField O) c) := fun c => by
    rw [hρ, AlgHomClass.commutes, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes c)
  have hεH : ∀ a, Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) (ρ a) =
      algebraMap O (IsLocalRing.ResidueField O) (Bialgebra.counitAlgHom O (G.A (n + 1)) a) := fun a => by
    rw [hρ, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def, mul_comm]
    simp

  have hlaws : (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.lid (IsLocalRing.ResidueField O) _
      (LinearMap.rTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) ∧
      (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.rid (IsLocalRing.ResidueField O) _
      (LinearMap.lTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) := by
    constructor
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.rTensor_counit_comul]
      simp
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.lTensor_counit_comul]
      simp
  obtain ⟨e, he1, hei, ε', Δ', hlaws', hnil⟩ := _root_.GlobalTheory.localFactor_counital_descends _ _ _ _ hlaws
  have hpres := _root_.GlobalTheory.square_presentation_of_counital_comul p _ _ ε' Δ' hlaws' hnil

  obtain ⟨r, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType O (G.A (n + 1)))
  have hfa : f₀ = MvPolynomial.aeval (fun i => f₀ (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.aeval_X]
  have hmap : ∀ {τ : Type} (x : τ → G.A (n + 1)) (q : MvPolynomial τ O),
      MvPolynomial.aeval (fun j => ρ (x j)) (MvPolynomial.map (algebraMap O (IsLocalRing.ResidueField O)) q) =
        ρ (MvPolynomial.aeval x q) := by
    intro τ x q
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun c => (hρalg c).symm
  have haH : Function.Surjective (MvPolynomial.aeval (fun i => ρ (f₀ (MvPolynomial.X i))) :
      MvPolynomial (Fin r) (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O] _) := fun h => by
    obtain ⟨y, rfl⟩ := hρs h
    obtain ⟨q, rfl⟩ := hf₀ y
    exact ⟨_, (hmap (fun i => f₀ (MvPolynomial.X i)) q).trans (by rw [← hfa])⟩
  obtain ⟨s, y, g, hg0, hgker⟩ := _root_.GlobalTheory.sqloc_present _ _ _ e he1 hei hpres r _ haH
  choose yt hyt using fun i => hρs (y i)
  obtain ⟨x, hxd⟩ : ∃ x : Fin s ⊕ Fin r → G.A (n + 1), x = Sum.elim yt (fun i => f₀ (MvPolynomial.X i)) := ⟨_, rfl⟩
  have hx : (fun j => ρ (x j)) = Sum.elim y (fun i => ρ (f₀ (MvPolynomial.X i))) := by
    funext j
    cases j <;> simp [hxd, hyt]
  have hxs : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1)) := by
    intro z
    obtain ⟨q, rfl⟩ := hf₀ z
    refine ⟨MvPolynomial.map (algebraMap O (G.A n)) (MvPolynomial.rename Sum.inr q), ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename, hfa, hxd]
    rfl
  haveI : Module.FinitePresentation O (G.A (n + 1)) := Module.finitePresentation_of_projective _ _
  haveI : Algebra.FinitePresentation O (G.A (n + 1)) := Algebra.FinitePresentation.of_finitePresentation _ _
  haveI : Algebra.FinitePresentation (G.A n) (G.A (n + 1)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O _ _
  have hFG : (RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1))).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ hxs
  obtain ⟨f, hf0, hfker⟩ := _root_.GlobalTheory.lift_square_presentation_of_flat O (G.A n) (G.A (n + 1)) (IsLocalRing.ResidueField O) _ (Fin s ⊕ Fin r)
    (Bialgebra.counitAlgHom O (G.A (n + 1))) (algebraMap O (IsLocalRing.ResidueField O)) ρ
    (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)) x
    hπs hπk hρalg hεH hkerρ hxs hFG g (by rw [hx]; exact hg0) (by rw [hx]; exact hgker)
  have hpt : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))), (p : O) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 ⊔
        ((RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1)))).map
          (algebraMap (G.A n) (G.A (n + 1))) := by
    rw [hker]
    exact GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP p O G n
  have := _root_.GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation O (G.A n) (G.A (n + 1)) (Fin s ⊕ Fin r) (Bialgebra.counitAlgHom O (G.A (n + 1))) x f (p : O)
    hp0 hxs hf0 hfker hpt b hb
  rwa [hker] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
section
noncomputable section

open TensorProduct

namespace GlobalTheory

section AdicAux

variable {S : Type*} [CommRing S] (a : S)

theorem mem_span_singleton_pow_smul_top_iff_exists {N : Type*} [AddCommGroup N] [Module S N] (n : ℕ)
    (x : N) : x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule S N) ↔ ∃ y : N, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  exact exists_congr fun v => by simp [eq_comm]

theorem isAdicComplete_fin_pi [IsAdicComplete (Ideal.span {a}) S] (k : ℕ) :
    IsAdicComplete (Ideal.span {a}) (Fin k → S) := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    funext i
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) S) (x i) fun n => ?_
    have h := hx n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨y i, by simpa using congrFun hy i⟩
  · intro f hf
    have key : ∀ i, ∃ L : S, ∀ n,
        f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule S S)] := fun i =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {a}) S) fun {m n} hmn => by
        have h := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h ⊢
        obtain ⟨y, hy⟩ := h
        exact ⟨y i, by simpa using congrFun hy i⟩
    choose L hL using key
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
    have h := fun i => (mem_span_singleton_pow_smul_top_iff_exists a n _).1 (SModEq.sub_mem.1 (hL i n))
    choose y hy using h
    exact ⟨y, funext fun i => by simpa using hy i⟩

theorem isAdicComplete_of_retraction {N F : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup F] [Module S F] [IsAdicComplete (Ideal.span {a}) F] (i : N →ₗ[S] F)
    (r : F →ₗ[S] N) (h : r ∘ₗ i = LinearMap.id) : IsAdicComplete (Ideal.span {a}) N := by
  refine { haus' := ?_, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have h1 : i x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) F) (i x) fun n => by
      have h2 := hx n
      rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
      obtain ⟨y, hy⟩ := h2
      rw [sub_zero] at hy ⊢
      exact ⟨i y, by rw [hy, map_smul]⟩
    have h3 := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h1, map_zero, LinearMap.id_apply] at h3
    exact h3.symm
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (f := fun n => i (f n))
      (inferInstance : IsPrecomplete (Ideal.span {a}) F) fun {m n} hmn => by
        have h2 := hf hmn
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
        obtain ⟨y, hy⟩ := h2
        exact ⟨i y, by rw [← map_sub, hy, map_smul]⟩
    refine ⟨r L, fun n => ?_⟩
    have h2 := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists] at h2 ⊢
    obtain ⟨y, hy⟩ := h2
    refine ⟨r y, ?_⟩
    have h3 := LinearMap.congr_fun h (f n)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h3
    rw [← map_smul, ← hy, map_sub, h3]

theorem isAdicComplete_of_finite_projective [IsAdicComplete (Ideal.span {a}) S] (N : Type*)
    [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    IsAdicComplete (Ideal.span {a}) N := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S N
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  haveI := isAdicComplete_fin_pi a k
  exact isAdicComplete_of_retraction a s f hs

end AdicAux

namespace PDivGroup

open PDiv Coalgebra Bialgebra

variable {p : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : PDivGroup p R)

variable {M : Type} [AddCommGroup M] [Module R M] (c : M →ₗ[R] G.omega)

end PDivGroup

end GlobalTheory

namespace GlobalTheory

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivPderivCommFock
section
open Formalism.BasicNotions.TH MvPolynomial

namespace GlobalTheory

theorem pderiv_pderiv_comm_fock {σ : Type} (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have hc : ∀ (a b k : σ), pderiv a (pderiv b (X k : MvPolynomial σ ℂ)) = 0 := by
    intro a b k
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact pderiv_one
    · exact map_zero _
  refine MvPolynomial.induction_on (motive := fun P => pderiv i (pderiv j P) = pderiv j (pderiv i P)) P ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  · intro p k hp
    simp only [pderiv_mul, map_add (f := _), hc, mul_zero, add_zero]
    rw [hp]
    ring

theorem fock_letters_ccr (p q r s : ℕ) (l m : Ln p q r s) :
    (lowB l * raiB m - raiB m * lowB l = if l = m then (1 : Module.End ℂ (Pol p q r s)) else 0) ∧
      lowB l * lowB m = lowB m * lowB l ∧ raiB l * raiB m = raiB m * raiB l := by
  classical
  have hcomm : ∀ (i j : Ln p q r s) (P : Pol p q r s), pderiv i (pderiv j P) = pderiv j (pderiv i P) :=
    fun i j P => pderiv_pderiv_comm_fock i j P
  have hX : ∀ (i j : Ln p q r s), pderiv i (X j : Pol p q r s) = if j = i then 1 else 0 := by
    intro i j
    rw [pderiv_X, Pi.single_apply]
  have hne : ∀ l m : Ln p q r s, linePos l ≠ linePos m → l ≠ m := by
    rintro l m h rfl
    exact h rfl
  refine ⟨?_, ?_, ?_⟩
  · by_cases hlm : l = m
    · subst hlm
      rw [if_pos rfl]
      cases hl : linePos l <;> simp only [lowB, raiB, hl, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX]
    · rw [if_neg hlm]
      cases hl : linePos l <;> cases hm : linePos m <;>
        simp only [lowB, raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
        refine LinearMap.ext fun f => ?_ <;>
        simp [Module.End.mul_apply, hX, hcomm, Ne.symm hlm, hlm] <;> ring
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [lowB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp only [raiB, hl, hm, Bool.false_eq_true, ↓reduceIte] <;>
      refine LinearMap.ext fun f => ?_ <;>
      simp [Module.End.mul_apply, hX, hcomm] <;> (try ring_nf) <;> (try (intro h; subst h; exact absurd (hl.symm.trans hm) (by decide)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCoverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularForms_isBundle_projectiveCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  first | (exact @GlobalTheory.PD.omB_isBundle) | (exact GlobalTheory.PD.omB_isBundle) | (intros; apply GlobalTheory.PD.omB_isBundle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparison
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem restrRes_strictlyGE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) [K.IsStrictlyGE 0] :
    ((rcx φ).obj K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr φ).map_isZero (K.isZero_of_isStrictlyGE 0 i hi)

def semiOfRestr {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R} (u : (rcx φ).obj K ⟶ J) :
    SemiMap K J where
  app U s := (((u.f s).hom.app (op U)).hom.toAddMonoidHom).comp ((idSemi φ K).app U s)
  nat {V U} g s a := by
    have h := congrArg (fun m => ModuleCat.Hom.hom m (show Sec (((rcx φ).obj K).X s) U from a))
      ((u.f s).hom.naturality g.op)
    exact h.symm
  comm U s t a := by
    have h := congrArg (fun m => (m.hom.app (op U)).hom (show Sec (((rcx φ).obj K).X s) U from a)) (u.comm s t)
    exact h

theorem semiOfRestr_app {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R}
    (u : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ) (a : Sec (K.X s) U) :
    (semiOfRestr φ K u).app U s a = Sec.map (u.f s) ((idSemi φ K).app U s a) := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem restrRes_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
      (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧
      ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  intro R S _ _ φ F
  obtain ⟨_, hinjS, hgeS, hqS, hιS, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic S F
  obtain ⟨hKR, -, hgeR, -, hιR, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R ((restr φ).obj F)
  haveI := hgeS; haveI := hqS; haveI := hKR; haveI := hgeR
  haveI : ((rcx φ).obj (res S F)).IsStrictlyGE 0 := restrRes_strictlyGE φ (res S F)
  haveI : QuasiIso (rAug φ (resAug F)) := rAug_quasiIso φ (resAug F)
  obtain ⟨u, hu⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug _)
  refine ⟨semiOfRestr φ (res S F) u, ?_, ?_⟩
  · intro U a
    have h0 := rAug_f_zero φ (resAug F) U a
    have h1 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) = Sec.map (resι S F) a := by
      rw [← hιS]; rfl
    have h2 : Sec.map ((rAug φ (resAug F) ≫ u).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
      rw [hu, ← hιR]; rfl
    rw [← h2, semiOfRestr_app]
    change _ = Sec.map (u.f 0) (Sec.map ((rAug φ (resAug F)).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)))
    rw [h0, h1]
    rfl
  · intro E n
    have hc := GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (semiOfRestr φ (res S F) u) u
      (fun U s a => semiOfRestr_app φ (res S F) u U s a)
    have hid := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (idSemi φ (res S F)) (𝟙 _) (fun U s a => rfl)).2
      (fun U s => Function.bijective_id) E n
    have hpush := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology R ((restr φ).obj F) ((rcx φ).obj (res S F)) (rAug φ (resAug F)) u hu
      (fun t P m hm => by
        haveI := hinjS t
        exact GlobalTheory.T.restrictScalars_injective_sheaf_acyclic R S φ ((res S F).X t) P m hm) E n
    have heq : (semiOfRestr φ (res S F) u).op.app E n =
        fun x => cpush _ u n ((idSemi φ (res S F)).op.app E n x) := funext (hc.1 E n)
    rw [heq]
    exact hpush.comp hid

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectCosetPairingEqZeroOrTwistStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semidirect_coset_pairing_eq_zero_or_twist : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' → ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨ ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  first | (exact @GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (exact GlobalTheory.Shin.coset_pair_eq_zero_or_twist) | (intros; apply GlobalTheory.Shin.coset_pair_eq_zero_or_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCharpolyRootPowerSumEqNorm
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_map_pullθ {F F' : Type} [Field F] [Field F'] [Algebra F F']
    (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F[X]) :
    rootSum θ k (P.map (algebraMap F F')) = rootSum (pullθ ι θ) k P := by
  unfold rootSum pullθ
  have e1 : (P.map (algebraMap F F')).map (algebraMap F' (AlgebraicClosure F')) =
      (P.map (algebraMap F (AlgebraicClosure F))).map (ι : AlgebraicClosure F →+* AlgebraicClosure F') := by
    rw [Polynomial.map_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    ext x
    simp
  rw [e1, (IsAlgClosed.splits _).roots_map, Multiset.map_map]
  rfl

theorem charpoly_of_isConj {K : Type} [Field K] {n : ℕ} {a b : GL (Fin n) K} (h : IsConj a b) :
    Matrix.charpoly (a : Matrix (Fin n) (Fin n) K) = Matrix.charpoly (b : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem shLift_chG_rootSum : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) (k n : ℕ) (δ : GL (Fin n) F'), shLift s (chG (rootSum (pullθ ι θ) k) n) δ = chG (rootSum θ k) n (nrm s δ) := by
  intro F F' _ _ _ _ s hs ι θ k n δ
  have hex : ∃ γ, IsNorm s δ γ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  unfold shLift
  rw [dite_eq_left hex]
  generalize hex.choose = γ, hex.choose_spec = hγ
  unfold IsNorm at hγ
  unfold chG
  rw [← charpoly_of_isConj hγ]
  have hm : ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F F') := by
    ext i j; rfl
  rw [hm, Matrix.charpoly_map, rootSum_map_pullθ]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNonzeroIntegersPrincipalIdealsUnitsStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_nonzero_integers_principal_ideals_units : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [NormedAddCommGroup E] [CompleteSpace E] (f : 𝓞 K → E), f 0 = 0 → ∀ (c : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → E) (β : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → (𝓞 K)ˣ → ℝ) (b : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} → ℝ), (∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, HasSum (fun u : (𝓞 K)ˣ => f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))) (c J)) → (∀ (J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}) (u : (𝓞 K)ˣ), ‖f ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1))‖ ≤ β J u) → (∀ J, HasSum (β J) (b J)) → Summable b → HasSum f (∑' J, c J) := by
  first | exact @GlobalTheory.sum_over_principal_ideals_units | exact GlobalTheory.sum_over_principal_ideals_units | (intros; apply GlobalTheory.sum_over_principal_ideals_units <;> assumption)
end

