module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalars
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hI hP l Z H F hS hC
  have hseen := _root_.GlobalTheory.Mem.Col2.HAt.seenCl_atT I hI hP l Z H F hS hC
  have hdisc := GlobalTheory.T.dual_mod_class_lattice_equiv_quotient I hI hP l Z H F hS hC
  have hlvc := _root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hI hP l Z H F hS hC
  have hstab := _root_.GlobalTheory.Mem.Col2.HAt.Stab.stabMap_tied I hI hP l Z H F hS hC
  choose upG hup using _root_.GlobalTheory.Mem.Col2.HAt.UpMove.up_move I hI hP l Z H F hS hC
  choose dnG hdn using _root_.GlobalTheory.Mem.Col2.HAt.dn_move_exists I hI hP l Z H F hS hC
  choose dilG hdil using _root_.GlobalTheory.Mem.Col2.HAt.Dil.diamond_on_hermitian_side I hI hP l Z H F hS hC
  choose lattice₂ levP clsP hcar hlat using _root_.GlobalTheory.Mem.Col2.HAt.clsP_hermitian I hI hP l Z H F hS hC
  let A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u) := fun u =>
    mkAtT (F u).atT (F u).lv (hC.eV u) (hC.fv u) (hseen u) (hdisc u) (upG u) (fun i hi v c y h => (hup u i v c y hi h).1)
      (dnG u) (fun i hi v c g h => (hdn u i v c g hi h).1) (dilG u) (fun i hi v a c => (hdil u i v a c hi).1)
      (lattice₂ u) (levP u) (clsP u) (F u).til (hlat u)
  have hT : CarT H F A := by
    refine ⟨fun _ => rfl, fun _ => rfl, hcar, hlat, ?_, ?_, ?_, ?_, ?_⟩
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prkH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i h1 h2 v c z z' h
      refine ((hlvc u i h1 h2 v c).1 (toLd i (le_of_succ_m h2) c z) z' h).trans (prH_eq (F u).atT (F u).lv (le_of_succ_m h2) v c z).symm
    · intro u
      exact ((crdN (I.rec7 l Z) _ le_rfl).apply_symm_apply _).symm
    · intro u c
      exact (reGL_lin _ (rankN (I.rec7 l Z) _ le_rfl) _).symm
  refine ⟨A, hT, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstab A hT⟩
  · intro u v c y h
    exact (hup u 0 v c y (Nat.zero_le _) h).2
  · intro u i h1 hm v c y h
    cases i with
    | zero => omega
    | succ i => exact (hup u (i + 1) v c y hm h).2 hm
  · intro u v c g h
    exact (hdn u 0 v c g (Nat.zero_le _) h).2
  · intro u i h1 hm v c g h
    cases i with
    | zero => omega
    | succ i => exact (hdn u (i + 1) v c g hm h).2 hm
  · intro u v a c
    exact (hdil u 0 v a c (Nat.zero_le _)).2
  · intro u i h1 hm v a c
    cases i with
    | zero => omega
    | succ i => exact (hdil u (i + 1) v a c hm).2 hm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxVanishOffFinite
section
noncomputable section

namespace GlobalTheory.Mem.IdxFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

theorem exists_unif {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf using h
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩
  have : Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    show (∏ y ∈ S, f y) • y ∈ B
    rw [← Finset.prod_erase_mul S f hy, mul_smul]
    exact B.smul_mem _ (hf y (Submodule.subset_span hy)).2
  exact this hx

theorem locLen_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A C : Submodule (𝓞 K) V) (hA : A.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.locLen w.asIdeal A C ≠ 0}.Finite := by
  by_cases h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C
  · obtain ⟨s, hs, hC⟩ := Formalism.L2.Host.exists_unif A C hA h
    have hf := Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)
    refine hf.subset fun w hw => ?_
    by_contra hn
    have hsw : s ∉ w.asIdeal := fun h => hn (Ideal.dvd_span_singleton.2 h)
    have : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, t, ht, hx⟩ -
      exact ⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩
    apply hw
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this]
    simp [Module.length_eq_zero]
  · push Not at h
    obtain ⟨x, hx, hxC⟩ := h
    refine Set.Finite.subset Set.finite_empty fun w hw => hw ?_
    unfold Formalism.HermitianLatticesTheory.locLen
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A := ⟨1, Submonoid.one_mem _, by simpa using hx⟩
    let φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) :=
      LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)
    have hφ : Function.Injective φ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro r hr
      by_contra hr0
      have h1 : Submodule.Quotient.mk (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)
          (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨t, ht, h2⟩ := h1
      refine hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_
      rw [mul_smul]
      exact h2
    have hle := Module.length_le_of_injective φ hφ
    have htop : Module.length (𝓞 K) (𝓞 K) = ⊤ := by
      by_contra hne
      have hfl := Module.length_ne_top_iff.1 hne
      have hart : IsArtinianRing (𝓞 K) := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      exact RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)
    rw [htop, top_le_iff] at hle
    rw [hle]
    rfl

theorem lidx_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≠ 0}.Finite := by
  refine ((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  apply hw
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [hn.1, hn.2]
  simp

end GlobalTheory.Mem.IdxFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtF

open Formalism.L2.DIV
open scoped Matrix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

theorem awf_eval_aeval {σ₁ σ₂ : Type} (f : σ₁ → MvPolynomial σ₂ K) (d : σ₂ → K) (P : MvPolynomial σ₁ K) :
    MvPolynomial.eval d (MvPolynomial.aeval f P) = MvPolynomial.eval (fun x => MvPolynomial.eval d (f x)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

def awfPt (γ₀ : Matrix (Fin n) (Fin n) L) : (L →+* K) × Fin n × Fin n → K := fun p => p.1 (γ₀ p.2.1 p.2.2)

def awfLin {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (p : (L →+* K) × Fin n × Fin n) :
    MvPolynomial (κ × Fin n × Fin n) K :=
  ∑ k : κ, MvPolynomial.C (p.1 (e k)) * MvPolynomial.X (k, p.2.1, p.2.2)

theorem awf_emb_eq {κ : Type} [Fintype κ] (e : Module.Basis κ ℚ L) (σ : L →+* K) (x : L) :
    σ x = ∑ k : κ, σ (e k) * ((e.repr x k : ℚ) : K) := by
  conv_lhs => rw [← e.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

theorem isAlgWeightF_of_embPoly {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (Q : ι → ι → MvPolynomial ((L →+* K) × Fin n × Fin n) K)
    (hQ : ∀ γ : GQ L n, LinearMap.toMatrix b b (ρ γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L)) (Q i j)) :
    NX.IsAlgWeightF L n K ρ := by
  let e := Module.finBasis ℚ L
  refine ⟨Module.Finite.of_basis b, ι, inferInstance, inferInstance, b, _, inferInstance, e,
    fun i j => MvPolynomial.aeval (awfLin e) (Q i j), ?_⟩
  intro γ γ₀ hm
  obtain rfl := ratHom_eq_of_match γ γ₀ hm
  rw [hQ γ]
  ext i j
  rw [awf_eval_aeval]
  refine congrArg (fun f => MvPolynomial.eval f (Q i j)) (funext fun p => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [awfLin, awfPt, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact awf_emb_eq e p.1 _

end Gen

section Poly

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

def awfUniv : Pol K ι n →ₐ[K] MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K) :=
  MvPolynomial.aeval fun v => ∑ b : Fin n, MvPolynomial.C (MvPolynomial.X (v.1, b, v.2.1)) * MvPolynomial.X (v.1, b, v.2.2)

theorem awfUniv_map (M : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfUniv F) =
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) F := by
  have h : (MvPolynomial.map (MvPolynomial.eval fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2)).comp
      (awfUniv (K := K) (ι := ι) (n := n)).toRingHom = (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (M τ)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct]
    · intro v
      simp [awfUniv, Formalism.GradedWeylDivisibility.blockAct, Matrix.transpose_apply]
  exact congrArg (fun f : Pol K ι n →+* Pol K ι n => f F) h

def awfCf (ℓ : Pol K ι n →ₗ[K] K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) : MvPolynomial (ι × Fin n × Fin n) K :=
  ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m * MvPolynomial.C (ℓ (MvPolynomial.monomial m 1))

theorem awfCf_eval (ℓ : Pol K ι n →ₗ[K] K) (y : ι × Fin n × Fin n → K)
    (Q : MvPolynomial (ι × Fin n × Fin n) (MvPolynomial (ι × Fin n × Fin n) K)) :
    MvPolynomial.eval y (awfCf ℓ Q) = ℓ (MvPolynomial.map (MvPolynomial.eval y) Q) := by
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, awfCf, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    show MvPolynomial.monomial m (MvPolynomial.eval y (AddMonoidAlgebra.coeff Q m)) =
        MvPolynomial.eval y (AddMonoidAlgebra.coeff Q m) • (MvPolynomial.monomial m 1 : Pol K ι n) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

def awfCoord (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n →ₗ[K] K :=
  (LinearMap.exists_extend ((bVV K lam).coord i)).choose

theorem awfCoord_spec (lam : ι → DomWeight n) (i : VVIdx lam) (F : VV K lam) :
    awfCoord lam i (F : Pol K ι n) = (bVV K lam).repr F i := by
  have h := (LinearMap.exists_extend ((bVV K lam).coord i)).choose_spec
  have := LinearMap.congr_fun h F
  simpa [awfCoord, Module.Basis.coord_apply] using this

def awfCoef (lam : ι → DomWeight n) (i j : VVIdx lam) : MvPolynomial (ι × Fin n × Fin n) K :=
  awfCf (awfCoord lam i) (awfUniv (bVVfun K lam j))

theorem awfCoef_eval (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    MvPolynomial.eval (fun y : ι × Fin n × Fin n => M y.1 y.2.1 y.2.2) (awfCoef lam i j) =
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (M τ)ᵀ) (bVVfun K lam j)) := by
  rw [awfCoef, awfCf_eval, awfUniv_map]

end Poly

section Alg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

def awfDetP (σ : L →+* K) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  (Matrix.of fun a b => (MvPolynomial.X (σ, a, b) : MvPolynomial ((L →+* K) × Fin n × Fin n) K)).det

theorem awfDetP_eval (σ : L →+* K) (γ₀ : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (awfPt γ₀) (awfDetP σ) = σ γ₀.det := by
  rw [awfDetP, RingHom.map_det, RingHom.map_det]
  congr 1
  ext a b
  simp [awfPt]

theorem awf_det_conj (σ : L →+* K) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    (σ.comp (IsCMField.complexConj L : L →+* L)) (γ₀ : Matrix (Fin n) (Fin n) L).det =
      (σ (γ₀ : Matrix (Fin n) (Fin n) L).det)⁻¹ := by
  have h1 : ((γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀).det = 1 := by
    rw [show (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 from hγ,
      Matrix.det_one]
  have h2 : ((γ₀ : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L : L →+* L)).det =
      (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, conjT, Matrix.det_transpose, h2] at h1
  apply eq_inv_of_mul_eq_one_right
  rw [RingHom.comp_apply, ← map_mul, h1, map_one]

theorem awf_inv_entry (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) (k l : Fin n) :
    ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k l =
      (IsCMField.complexConj L : L →+* L) ((γ₀ : Matrix (Fin n) (Fin n) L) l k) := by
  have h1 : ((γ₀⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
    Units.inv_eq_of_mul_eq_one_right hγ
  rw [h1]
  rfl

def awfTwP (emb : ι → L →+* K) (lam : ι → DomWeight n) : MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  ∏ τ, if 0 ≤ (lam τ).detShift then awfDetP (emb τ) ^ (lam τ).detShift.toNat
    else awfDetP ((emb τ).comp (IsCMField.complexConj L : L →+* L)) ^ (-(lam τ).detShift).toNat

theorem awfTwP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ₀ : GL (Fin n) L) (hγ : γ₀ ∈ GQ0 L n) :
    MvPolynomial.eval (awfPt (γ₀ : Matrix (Fin n) (Fin n) L)) (awfTwP emb lam) = detTwK lam (embGLF emb γ₀) := by
  simp only [awfTwP, detTwK, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : ((Matrix.GeneralLinearGroup.det (embGLF emb γ₀ τ) : Kˣ) : K) = emb τ (γ₀ : Matrix (Fin n) (Fin n) L).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [detPow, Units.val_zpow_eq_zpow_val, hd]
  split_ifs with h
  · rw [map_pow, awfDetP_eval, ← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, awfDetP_eval, awf_det_conj _ _ hγ, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow', neg_neg]

def awfTenP (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) :
    MvPolynomial ((L →+* K) × Fin n × Fin n) K :=
  awfTwP emb lam * MvPolynomial.aeval
    (fun y : ι × Fin n × Fin n => (MvPolynomial.X (emb y.1, y.2.1, y.2.2) : MvPolynomial ((L →+* K) × Fin n × Fin n) K))
    (awfCoef (K := K) lam i j)

theorem awfTenP_eval (emb : ι → L →+* K) (lam : ι → DomWeight n) (i j : VVIdx lam) (y : (L →+* K) × Fin n × Fin n → K) :
    MvPolynomial.eval y (awfTenP emb lam i j) = MvPolynomial.eval y (awfTwP emb lam) *
      awfCoord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (Matrix.of fun a b => y (emb τ, a, b))ᵀ) (bVVfun K lam j)) := by
  rw [awfTenP, MvPolynomial.eval_mul, awf_eval_aeval, ← awfCoef_eval]
  simp

theorem tenRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L))
        (awfTenP emb lam i j) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, ← awfCoord_spec, awfTenP_eval, awfTwP_eval _ _ _ (ratHom_mem γ)]
  simp only [tenRepF, MonoidHom.comp_apply, rhoK, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_restrict_apply, bVV_coe,
    actP, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
  congr 2

end Alg

section Dual

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]


open Classical in
theorem wtRepF_toMatrix (emb : ι → L →+* K) (lam : ι → DomWeight n) (γ : GQ L n) :
    LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      fun i j => MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ : Matrix (Fin n) (Fin n) L))
        (MvPolynomial.rename (fun p : (L →+* K) × Fin n × Fin n =>
          (p.1.comp (IsCMField.complexConj L : L →+* L), p.2.2, p.2.1)) (awfTenP emb lam j i)) := by
  have e : LinearMap.toMatrix (bVV K lam).dualBasis (bVV K lam).dualBasis (wtRepF emb lam γ) =
      (LinearMap.toMatrix (bVV K lam) (bVV K lam) (tenRepF emb lam γ⁻¹))ᵀ := by
    rw [wtRepF, Representation.dual_apply, LinearMap.toMatrix_transpose]
  rw [e, tenRepF_toMatrix]
  ext i j
  show MvPolynomial.eval (awfPt (ratHom (L := L) (n := n) γ⁻¹ : Matrix (Fin n) (Fin n) L))
    (awfTenP emb lam j i) = _
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun f => MvPolynomial.eval f (awfTenP emb lam j i)) (funext fun p => ?_)
  simp only [Function.comp_apply, awfPt, RingHom.comp_apply, map_inv]
  rw [awf_inv_entry _ (ratHom_mem γ)]

end Dual

theorem wtRepF_alg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), NX.IsAlgWeightF L n K (GlobalTheory.AlgWtF.wtRepF emb lam) := by
  intro L _ _ _ n ι _ K _ emb lam
  classical
  exact isAlgWeightF_of_embPoly _ (bVV K lam).dualBasis _ (wtRepF_toMatrix emb lam)

end GlobalTheory.AlgWtF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosIffSideMemMax
section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∃ (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ), ∀ f, IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → GlobalTheory.ChainFr.LieFockWith ψ θ A B ω f τ κS κT := by
  first | exact @GlobalTheory.LieFock.lieFockUpTo_at | exact GlobalTheory.LieFock.lieFockUpTo_at | (intros; apply GlobalTheory.LieFock.lieFockUpTo_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOutsideNonHyperspecialOfLocalisationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_outside_nonHyperspecial_of_localisation : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := by
  first | exact @GlobalTheory.SplitOutPlace.not_mem_gPl_qPl | exact GlobalTheory.SplitOutPlace.not_mem_gPl_qPl | (intros; apply GlobalTheory.SplitOutPlace.not_mem_gPl_qPl <;> assumption)
end

