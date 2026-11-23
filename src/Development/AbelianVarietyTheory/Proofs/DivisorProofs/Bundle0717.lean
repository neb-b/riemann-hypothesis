module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupProperties
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Grp
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem cont_coords : Continuous (coords : ℍ[R, a, b] → Fin 4 → R) := continuous_induced_dom
theorem cont_re : Continuous (fun x : ℍ[R, a, b] => x.re) := (continuous_apply 0).comp cont_coords
theorem cont_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) := (continuous_apply 1).comp cont_coords
theorem cont_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) := (continuous_apply 2).comp cont_coords
theorem cont_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) := (continuous_apply 3).comp cont_coords

theorem cont_of {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cont_mul : Continuous (fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2) := by
  have r1 := (cont_re (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i1 := (cont_imI (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j1 := (cont_imJ (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k1 := (cont_imK (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have r2 := (cont_re (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i2 := (cont_imI (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j2 := (cont_imJ (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k2 := (cont_imK (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  simp only [Function.comp_def] at r1 i1 j1 k1 r2 i2 j2 k2
  apply cont_of <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

theorem cont_star : Continuous (fun x : ℍ[R, a, b] => star x) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  apply cont_of <;> simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] <;> fun_prop

theorem cont_nrm : Continuous (nrm : ℍ[R, a, b] → R) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  unfold nrm
  fun_prop

theorem cont_conj (c d : ℍ[R, a, b]) : Continuous fun y : ℍ[R, a, b] => c * y * d := by
  have h1 : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := cont_mul
  have hl : Continuous fun y : ℍ[R, a, b] => c * y :=
    h1.comp (Continuous.prodMk (continuous_const : Continuous fun _ : ℍ[R, a, b] => c) continuous_id)
  exact h1.comp (Continuous.prodMk hl (continuous_const : Continuous fun _ : ℍ[R, a, b] => d))

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp
variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem supp {ε : AF F} (p q u : DA F a b) (hu : ε • u = u) : ε • (p * u * q) = p * u * q := by
  rw [← smul_mul_assoc, ← mul_smul_comm, hu]

theorem rat_inv {γ : ℍ[F, a, b]} (hγ : nrm γ = 1) :
    rat γ * rat (star γ) = 1 ∧ rat (star γ) * rat γ = 1 := by
  constructor
  · rw [← rat_mul, mul_star_eq, hγ, map_one, rat_one]
  · rw [← rat_mul, star_mul_eq, hγ, map_one, rat_one]

theorem nrm_of_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : nrm x = 1 := by
  obtain ⟨γ, hγ, h, hh, -, rfl⟩ := hx
  rw [nrm_mul, nrm_rat, hγ, hh, map_one, one_mul]

theorem mul_mem {ε : AF F} {x y : DA F a b} (hx : x ∈ H0 ε) (hy : y ∈ H0 ε) : x * y ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', hs', rfl⟩ := hy
  obtain ⟨e1, e2⟩ := rat_inv hγ'
  refine ⟨γ * γ', by rw [nrm_mul, hγ, hγ', one_mul], rat (star γ') * h * rat γ' * h', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_mul, hh, hh', nrm_rat, nrm_rat, nrm_star, hγ', map_one]; ring
  · have : rat (star γ') * h * rat γ' * h' - 1
        = rat (star γ') * (h - 1) * (rat γ' * h') + (h' - 1) := by
      rw [show rat (star γ') * (h - 1) * (rat γ' * h')
          = rat (star γ') * h * rat γ' * h' - rat (star γ') * rat γ' * h' by noncomm_ring, e2, one_mul]
      abel
    rw [this, smul_add, hs', supp _ _ _ hs]
  · rw [rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat γ') (rat (star γ')), e1, one_mul]

theorem star_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : star x ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨e1, e2⟩ := rat_inv hγ
  refine ⟨star γ, by rw [nrm_star, hγ], rat γ * star h * rat (star γ), ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_star, hh, nrm_rat, nrm_rat, nrm_star, hγ, map_one]; ring
  · have hs1 : ε • star (h - 1) = star (h - 1) := by
      rw [← QuaternionAlgebra.star_smul, hs]
    have : rat γ * star h * rat (star γ) - 1 = rat γ * star (h - 1) * rat (star γ) := by
      rw [star_sub, star_one, show rat γ * (star h - 1) * rat (star γ)
          = rat γ * star h * rat (star γ) - rat γ * rat (star γ) by noncomm_ring, e1]
    rw [this, supp _ _ _ hs1]
  · rw [star_mul, ← rat_star]
    simp only [← mul_assoc]
    rw [e2, one_mul]

theorem inv_right {δ δ' : ℍ[F, a, b]} (h : δ * δ' = 1) : δ' * δ = 1 := by
  have hn : nrm δ' * nrm δ = 1 := by rw [mul_comm, ← nrm_mul, h, nrm_one']
  have e : star δ * δ * δ' * δ = star δ * δ := by rw [mul_assoc (star δ), h, mul_one]
  rw [star_mul_eq] at e
  calc δ' * δ = algebraMap F ℍ[F, a, b] (nrm δ' * nrm δ) * (δ' * δ) := by rw [hn, map_one, one_mul]
    _ = algebraMap F ℍ[F, a, b] (nrm δ') * (algebraMap F ℍ[F, a, b] (nrm δ) * δ' * δ) := by
      rw [map_mul]; simp only [mul_assoc]
    _ = 1 := by rw [e, ← map_mul, hn, map_one]

theorem conj_mem {ε : AF F} {δ δ' : ℍ[F, a, b]} (hδ : δ * δ' = 1) {x : DA F a b} (hx : x ∈ H0 ε) :
    rat δ * x * rat δ' ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  have hδ2 := inv_right hδ
  have e1 : rat δ * rat δ' = 1 := by rw [← rat_mul, hδ, rat_one]
  have e2 : rat δ' * rat δ = 1 := by rw [← rat_mul, hδ2, rat_one]
  have hn : nrm δ * nrm δ' = 1 := by rw [← nrm_mul, hδ, nrm_one']
  refine ⟨δ * γ * δ', by rw [nrm_mul, nrm_mul, hγ, mul_one, hn], rat δ * h * rat δ', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hh, nrm_rat, nrm_rat, mul_one, ← map_mul, hn, map_one]
  · have : rat δ * h * rat δ' - 1 = rat δ * (h - 1) * rat δ' := by
      rw [show rat δ * (h - 1) * rat δ' = rat δ * h * rat δ' - rat δ * rat δ' by noncomm_ring, e1]
    rw [this, supp _ _ _ hs]
  · rw [rat_mul, rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat δ') (rat δ), e2, one_mul]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp

theorem t2Space_adeleRing_numberField (F : Type) [Field F] [NumberField F] : T2Space (AF F) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem closure_normOneProducts_subgroup_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε →
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε),
      x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε),
      rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  intro F _ _ a b ε _
  haveI := t2Space_adeleRing_numberField F
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun δ δ' hδ x hx => ?_, fun x hx => ?_⟩
  · exact map_mem_closure₂ cont_mul hx hy fun u hu v hv => mul_mem hu hv
  · exact map_mem_closure cont_star hx fun u hu => star_mem hu
  · have hc : Continuous fun y : DA F a b => rat δ * y * rat δ' := cont_conj (rat δ) (rat δ')
    have hm : Set.MapsTo (fun y : DA F a b => rat δ * y * rat δ') (H0 ε) (H0 ε) :=
      fun u hu => conj_mem hδ hu
    have key := map_mem_closure (x := x) hc hx hm
    exact key
  · have hcl : IsClosed {y : DA F a b | nrm y = 1} := isClosed_eq cont_nrm continuous_const
    exact closure_minimal (fun y hy => nrm_of_mem hy) hcl hx

end GlobalTheory.QSA.Grp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_qcqs_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hcp hqs haff
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hc' : IsLimit ((Over.conePost G i₀).obj c) := Over.isLimitConePost i₀ hc
  haveI := hcp i₀
  haveI := hqs i₀
  have hcore := GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc'
    (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)
  have hb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance
  apply GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)
  · intro i
    exact ⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩
  · let α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch :=
      { app := fun j => pullback.snd _ _
        naturality := fun j k f => by
          simp only [Functor.comp_map, bc, pullback.map]
          erw [pullback.lift_snd]
          rfl }
    refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c))
      ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore
    · intro j
      simp only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]
      erw [pullback.lift_snd]
      rfl
    · intro j
      exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
    · exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtInvS
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

open scoped RestrictedProduct

namespace GlobalTheory.InvIdem

variable {F : Type} [Field F] [NumberField F]

def ci (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (fstA F).toRingHom

def cf (v : HeightOneSpectrum (𝓞 F)) : AF F →+* Fv F v :=
  (evalV F v).toRingHom.comp (sndA F).toRingHom

theorem continuous_ci (w : InfinitePlace F) : Continuous (ci (F := F) w) :=
  (continuous_apply w).comp continuous_fst

theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) : Continuous (cf (F := F) v) :=
  (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
    continuous_snd

theorem ext_c {a b : AF F} (h1 : ∀ w, ci w a = ci w b) (h2 : ∀ v, cf v a = cf v b) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)


open Classical in
def sglI (w : InfinitePlace F) (c : w.Completion) : AF F :=
  ((Pi.single w c : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), singleV F v c)

theorem ci_apply (w : InfinitePlace F) (a : AF F) : ci w a = a.1 w := rfl
theorem cf_apply (v : HeightOneSpectrum (𝓞 F)) (a : AF F) : cf v a = a.2 v := rfl

theorem ci_sglI_self (w : InfinitePlace F) (c : w.Completion) : ci w (sglI w c) = c := by
  classical
  rw [ci_apply]; simp [sglI]

theorem ci_sglI_ne {w u : InfinitePlace F} (h : u ≠ w) (c : w.Completion) : ci u (sglI w c) = 0 := by
  classical
  rw [ci_apply]; simp [sglI, Pi.single_apply, h]

theorem cf_sglI (w : InfinitePlace F) (c : w.Completion) (v : HeightOneSpectrum (𝓞 F)) :
    cf v (sglI w c) = 0 := by
  rw [cf_apply]; rfl

theorem ci_sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (w : InfinitePlace F) :
    ci w (sglF v c) = 0 := by
  rw [ci_apply]; rfl

theorem cf_sglF_self (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : cf v (sglF v c) = c := by
  classical
  show (singleV F v c) v = c
  unfold singleV
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v c

theorem cf_sglF_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (c : Fv F v) : cf u (sglF v c) = 0 := by
  classical
  show (singleV F v c) u = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) c h

open Classical in
theorem continuous_sglI (w : InfinitePlace F) : Continuous (sglI (F := F) w) := by
  unfold sglI
  exact (continuous_single w).prodMk continuous_const

open Classical in
theorem continuous_sglF (v : HeightOneSpectrum (𝓞 F)) : Continuous (sglF (F := F) v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

def invS (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (y : AF F) : AF F :=
  (∑ w ∈ S₁, sglI w (ci w y)⁻¹) + ∑ v ∈ S₂, sglF v (cf v y)⁻¹

variable {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))}

open Classical in
theorem ci_invS (y : AF F) (u : InfinitePlace F) :
    ci u (invS S₁ S₂ y) = if u ∈ S₁ then (ci u y)⁻¹ else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [ci_sglF, Finset.sum_const_zero, add_zero]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => ci_sglI_ne (Ne.symm hw) _), ci_sglI_self]
  · exact Finset.sum_eq_zero fun w hw => ci_sglI_ne (fun h : u = w => hu (h ▸ hw)) _

open Classical in
theorem cf_invS (y : AF F) (u : HeightOneSpectrum (𝓞 F)) :
    cf u (invS S₁ S₂ y) = if u ∈ S₂ then (cf u y)⁻¹ else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [cf_sglI, Finset.sum_const_zero, zero_add]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => cf_sglF_ne (Ne.symm hw) _), cf_sglF_self]
  · exact Finset.sum_eq_zero fun w hw => cf_sglF_ne (fun h : u = w => hu (h ▸ hw)) _

theorem invS_mul {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) {y z : AF F} (hyz : y * z = 1) :
    invS S₁ S₂ (ε * y) = ε * z := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  have hi : ∀ w, ci w y * ci w z = 1 := fun w => by rw [← map_mul (ci w), hyz, map_one]
  have hf : ∀ v, cf v y * cf v z = 1 := fun v => by rw [← map_mul (cf v), hyz, map_one]
  refine ext_c (fun w => ?_) (fun v => ?_)
  · rw [ci_invS, map_mul, map_mul]
    have e1 : ci w ε = fstA F ε w := rfl
    split_ifs with hw
    · rw [e1, h1 w hw, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hi w)
    · rw [e1, h2 w hw, zero_mul]
  · rw [cf_invS, map_mul, map_mul]
    have e1 : cf v ε = evalV F v (sndA F ε) := rfl
    split_ifs with hv
    · rw [e1, h3 v hv, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hf v)
    · rw [e1, h4 v hv, zero_mul]

theorem continuousAt_invS {y : AF F} (h1 : ∀ w ∈ S₁, ci w y ≠ 0) (h2 : ∀ v ∈ S₂, cf v y ≠ 0) :
    ContinuousAt (invS S₁ S₂) y := by
  unfold invS
  refine ContinuousAt.add ?_ ?_
  · exact tendsto_finsetSum S₁ fun w hw =>
      ((continuous_sglI w).continuousAt.comp ((continuousAt_inv₀ (h1 w hw)).comp (continuous_ci w).continuousAt))
  · exact tendsto_finsetSum S₂ fun v hv =>
      ((continuous_sglF v).continuousAt.comp ((continuousAt_inv₀ (h2 v hv)).comp (continuous_cf v).continuousAt))

end GlobalTheory.InvIdem

namespace GlobalTheory.InvIdem

theorem inv_cont : ∀ (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x : (AF F)ˣ, ∀ U : Set (AF F),
    U ∈ 𝓝 (ε * ((x⁻¹ : (AF F)ˣ) : AF F)) → ∃ V : Set (AF F), V ∈ 𝓝 (ε * (x : AF F)) ∧
      ∀ t : F, ε * algebraMap F (AF F) t ∈ V → (ε ≠ 0 → t ≠ 0) ∧ ε * algebraMap F (AF F) t⁻¹ ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  have hx : invS S₁ S₂ (ε * (x : AF F)) = ε * ((x⁻¹ : (AF F)ˣ) : AF F) := invS_mul hε x.mul_inv
  have hci : ∀ w ∈ S₁, ci w (ε * (x : AF F)) ≠ 0 := by
    intro w hw h
    rw [map_mul, show ci w ε = fstA F ε w from rfl, hε.1 w hw, one_mul] at h
    have e := congrArg (ci w) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hcf : ∀ v ∈ S₂, cf v (ε * (x : AF F)) ≠ 0 := by
    intro v hv h
    rw [map_mul, show cf v ε = evalV F v (sndA F ε) from rfl, hε.2.2.1 v hv, one_mul] at h
    have e := congrArg (cf v) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hV1 : invS S₁ S₂ ⁻¹' U ∈ 𝓝 (ε * (x : AF F)) :=
    (continuousAt_invS hci hcf).preimage_mem_nhds (by rw [hx]; exact hU)
  have hV2 : {y : AF F | (∀ w ∈ S₁, ci w y ≠ 0) ∧ ∀ v ∈ S₂, cf v y ≠ 0} ∈ 𝓝 (ε * (x : AF F)) :=
    ((Filter.eventually_all_finset S₁).2 fun w hw => (continuous_ci w).continuousAt.eventually_ne (hci w hw)).and
      ((Filter.eventually_all_finset S₂).2 fun v hv => (continuous_cf v).continuousAt.eventually_ne (hcf v hv))
  refine ⟨_, Filter.inter_mem hV1 hV2, fun t ht => ?_⟩
  have htne : ε ≠ 0 → t ≠ 0 := by
    intro hε0 ht0
    subst ht0
    apply hε0
    have hB := ht.2
    simp only [Set.mem_setOf_eq, map_zero, mul_zero] at hB
    refine ext_c (fun w => ?_) (fun v => ?_)
    · rw [map_zero]
      exact hε.2.1 w fun hw => hB.1 w hw rfl
    · rw [map_zero]
      exact hε.2.2.2 v fun hv => hB.2 v hv rfl
  refine ⟨htne, ?_⟩
  by_cases hε0 : ε = 0
  · subst hε0
    have e := mem_of_mem_nhds hU
    rw [zero_mul] at e
    rwa [zero_mul]
  · have ht0 := htne hε0
    have e := invS_mul (y := algebraMap F (AF F) t) (z := algebraMap F (AF F) t⁻¹) hε
      (by rw [← map_mul, mul_inv_cancel₀ ht0, map_one])
    rw [← e]
    exact ht.1

end GlobalTheory.InvIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicThreeRootsStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots : ∀ (g h e₁ e₂ e₃ : ℂ), 4 * e₁ ^ 3 - g * e₁ - h = 0 → 4 * e₂ ^ 3 - g * e₂ - h = 0 → 4 * e₃ ^ 3 - g * e₃ - h = 0 → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧ 16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4)) = -(g ^ 3 - 27 * h ^ 2) := by
  first | exact @GlobalTheory.CMModel.cubic_three_roots | exact GlobalTheory.CMModel.cubic_three_roots | (intros; apply GlobalTheory.CMModel.cubic_three_roots <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_const_origin : GlobalTheory.VertUnits.DivConstOrigin := by
  first | (exact @GlobalTheory.VertUnits.divConstOrigin) | (exact GlobalTheory.VertUnits.divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstOrigin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDimStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  first | (exact @GlobalTheory.hInv_of_integral_killed_of_lower) | (exact GlobalTheory.hInv_of_integral_killed_of_lower) | (intros; apply GlobalTheory.hInv_of_integral_killed_of_lower  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetSeparatingFiniteDimensionalFunctionsStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_separating_finiteDimensional_functions : ∀ (K : Type) (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W → ∃ s : Finset K, ∀ w ∈ W, (∀ k ∈ s, w k = 0) → w = 0 := by
  first | exact @GlobalTheory.finiteDim_functions_detected_by_finset | exact GlobalTheory.finiteDim_functions_detected_by_finset | (intros; apply GlobalTheory.finiteDim_functions_detected_by_finset <;> assumption)
end

