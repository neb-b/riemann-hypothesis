module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormsTieOLatTie
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef
open scoped ComplexOrder

open scoped Matrix MatrixOrder

namespace GlobalTheory.Mem.CoordForms

theorem exists_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ S T : Matrix (Fin n) (Fin n) ℂ, Sᴴ * S = A ∧ S * T = 1 ∧ T * S = 1 := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hS
  have hdet : IsUnit S.det := by
    have h := hA.det_pos.ne'
    rw [hS, Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h)
  exact ⟨S, S⁻¹, hS.symm, Matrix.mul_nonsing_inv S hdet, Matrix.nonsing_inv_mul S hdet⟩

variable {K : Type} [Field K] {n : ℕ}

noncomputable def emb (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n) where
  toFun x := Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i))
  map_add' x y := by
    rw [← map_add (f := _)]
    congr 1
    ext i
    simp
  map_smul' a x := by
    rw [← map_smul]
    congr 1
    ext i
    simp

theorem emb_ofLp (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → K) :
    (emb σ S x).ofLp = S *ᵥ fun i => σ (x i) := rfl

noncomputable def act (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun E := Matrix.toEuclideanLin (S * E.map σ * T)
  map_one' := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (1 : Matrix (Fin n) (Fin n) K).map σ * T) *ᵥ v.ofLp = v.ofLp
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), mul_one, h1, Matrix.one_mulVec]
  map_mul' E F := by
    ext1 v
    apply WithLp.ofLp_injective
    change (S * (E * F).map σ * T) *ᵥ v.ofLp = (S * E.map σ * T) *ᵥ ((S * F.map σ * T) *ᵥ v.ofLp)
    rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    congr 1
    calc S * (E.map σ * F.map σ) * T = S * E.map σ * (T * S) * F.map σ * T := by rw [h2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' E F := by
    rw [← map_add (f := _), Matrix.map_add _ (map_add σ), mul_add, add_mul]

theorem emb_single (σ : K →+* ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    emb σ S (Pi.single i 1) = Matrix.toEuclideanLin S (EuclideanSpace.basisFun (Fin n) ℂ i) := by
  apply WithLp.ofLp_injective
  change S *ᵥ (fun k => σ ((Pi.single i (1 : K) : Fin n → K) k)) = S *ᵥ (EuclideanSpace.basisFun (Fin n) ℂ i).ofLp
  congr 1
  ext k
  rw [EuclideanSpace.basisFun_apply]
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem bij (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Bijective (Matrix.toEuclideanLin S) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun v => (Matrix.toEuclideanLin T v).ofLp) hxy
    change T *ᵥ (S *ᵥ x.ofLp) = T *ᵥ (S *ᵥ y.ofLp) at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact WithLp.ofLp_injective 2 h
  · intro y
    refine ⟨Matrix.toEuclideanLin T y, WithLp.ofLp_injective 2 ?_⟩
    change S *ᵥ (T *ᵥ y.ofLp) = y.ofLp
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem emb_injective (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Function.Injective (emb σ S) := by
  intro x y hxy
  have h : (WithLp.toLp 2 fun i => σ (x i) : EuclideanSpace ℂ (Fin n)) = WithLp.toLp 2 fun i => σ (y i) :=
    (bij S T h1 h2).1 (show Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (x i)) =
      Matrix.toEuclideanLin S (WithLp.toLp 2 fun i => σ (y i)) from hxy)
  funext i
  exact σ.injective (congrFun (congrArg WithLp.ofLp h) i)

theorem emb_span (σ : K →+* ℂ) (S T : Matrix (Fin n) (Fin n) ℂ) (h1 : S * T = 1) (h2 : T * S = 1) :
    Submodule.span ℂ (Set.range fun i => emb σ S (Pi.single i 1)) = ⊤ := by
  have hs : (fun i => emb σ S (Pi.single i 1)) =
      (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) :=
    funext (emb_single σ S)
  rw [hs, Set.range_comp, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, Module.Basis.span_eq,
    Submodule.map_top, LinearMap.range_eq_top]
  exact (bij S T h1 h2).2

theorem formsTie [NumberField K] [StarRing K] (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x))
    (H : Matrix (Fin n) (Fin n) K) (S T : Matrix (Fin n) (Fin n) ℂ) (h0 : Sᴴ * S = H.map σ) (h1 : S * T = 1)
    (h2 : T * S = 1) (E : Matrix (Fin n) (Fin n) K) : FormsTie σ (emb σ S) H E (act σ S T h1 h2 E) := by
  refine ⟨?_, emb_span σ S T h1 h2, ?_, ?_⟩
  · rw [show (fun i => emb σ S (Pi.single i 1)) =
        (Matrix.toEuclideanLin S) ∘ (EuclideanSpace.basisFun (Fin n) ℂ) from funext (emb_single σ S)]
    exact (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.linearIndependent.map'
      _ (LinearMap.ker_eq_bot.mpr (bij S T h1 h2).1)
  · intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, emb_ofLp, emb_ofLp, Matrix.star_mulVec, dotProduct_comm,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, map_sum, map_mul, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply, RingHom.id_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [hσ, starRingEnd_apply]
    ring
  · intro x
    apply WithLp.ofLp_injective
    change (S * E.map σ * T) *ᵥ (S *ᵥ fun i => σ (x i)) = S *ᵥ fun i => σ ((E *ᵥ x) i)
    rw [Matrix.mulVec_mulVec, mul_assoc (S * E.map σ), h2, mul_one, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ E x i).symm

theorem exists_lat [NumberField K] {O : Type} [CommRing O] (o : O →+* K) (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (hj : Function.Injective j)
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤)
    (N : Submodule (𝓞 K) (Fin n → K)) (hN : Submodule.IsFullLattice K N) :
    ∃ M : Rows.OLat O (σ.comp o) W, OLatTie σ M j N ∧
      ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set W) = j '' (N : Set (Fin n → K))) := by
  classical

  obtain ⟨G, hG⟩ := hN.fg.restrictScalars (R := ℤ)
  have hGN : ∀ g ∈ G, g ∈ N := fun g hg => by
    have : g ∈ Submodule.span ℤ (G : Set (Fin n → K)) := Submodule.subset_span hg
    rw [hG] at this
    exact this

  have hsum : ∀ φ : W → ℂ, ∑ v ∈ G.image j, φ v • v = ∑ g ∈ G, φ (j g) • j g := fun φ =>
    Finset.sum_image fun a _ b _ h => hj h

  have key : ∀ y ∈ Submodule.span K (G : Set (Fin n → K)),
      j y ∈ Submodule.span ℂ ((G.image j : Finset W) : Set W) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem j (Finset.mem_coe.mp hx)))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have hGK : Submodule.span K (G : Set (Fin n → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ K (G : Set (Fin n → K)), hG]
    exact hN.span_eq_top
  have hspan : Submodule.span ℂ ((G.image j : Finset W) : Set W) = ⊤ := by
    apply top_unique
    rw [← hsp]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact key _ (by rw [hGK]; trivial)
  have hZ : ∀ x ∈ N, ∃ f : (Fin n → K) → ℤ, j x = ∑ g ∈ G, (f g : ℂ) • j g := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (G : Set (Fin n → K)) := by rw [hG]; exact hx
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hx'
    refine ⟨f, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hf, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  have hcomb : ∀ a : (Fin n → K) → K, ∑ g ∈ G, σ (a g) • j g = j (∑ g ∈ G, a g • g) := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => (LinearMap.map_smulₛₗ j (a g) g).symm
  refine ⟨⟨G.image j, hspan⟩, ⟨fun v hv => ?_, fun x => ⟨fun hx => ?_, fun ⟨c, hc⟩ => ?_⟩⟩, fun hint => ?_⟩
  · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨g, rfl⟩
  · obtain ⟨f, hf⟩ := hZ x hx
    refine ⟨fun w => (f (Function.invFun j w) : 𝓞 K), ?_⟩
    change j x = ∑ v ∈ G.image j, σ ((f (Function.invFun j v) : 𝓞 K) : K) • v
    rw [hsum, hf]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Function.leftInverse_invFun hj g]
    simp
  · change j x = ∑ v ∈ G.image j, σ (c v : K) • v at hc
    rw [hsum, hcomb] at hc
    rw [hj hc]
    refine Submodule.sum_mem _ fun g hg => ?_
    have hm := N.smul_mem (c (j g)) (hGN g hg)
    rwa [← algebraMap_smul K (c (j g)) g] at hm
  · ext w
    constructor
    · rintro ⟨c, rfl⟩
      let a : (Fin n → K) → 𝓞 K := fun g => ⟨o (c (j g)), hint _⟩
      refine ⟨∑ g ∈ G, (a g : K) • g, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun g hg => ?_
        have hm := N.smul_mem (a g) (hGN g hg)
        rwa [← algebraMap_smul K (a g) g] at hm
      · change j (∑ g ∈ G, (a g : K) • g) = ∑ v ∈ G.image j, σ (o (c v)) • v
        rw [hsum, ← hcomb]
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, hf⟩ := hZ x hx
      refine ⟨fun w => (f (Function.invFun j w) : O), ?_⟩
      change j x = ∑ v ∈ G.image j, σ (o (f (Function.invFun j v) : O)) • v
      rw [hsum, hf]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Function.leftInverse_invFun hj g]
      simp

theorem exists_formsTie_oLatTie : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (N : Submodule (𝓞 K) (Fin n → K)), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (H.map σ).PosDef → Submodule.IsFullLattice K N → ∃ (j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)) (M : Rows.OLat O (σ.comp o) (EuclideanSpace ℂ (Fin n))) (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))), (∀ E, FormsTie σ j H E (ρ E)) ∧ OLatTie σ M j N ∧ ((∀ y, IsIntegral ℤ (o y)) → (M.carrier : Set (EuclideanSpace ℂ (Fin n))) = j '' (N : Set (Fin n → K))) := by
  intro K O _ _ _ _ o σ n H N hσ hH hN
  obtain ⟨S, T, h0, h1, h2⟩ := exists_sqrt (H.map σ) hH
  obtain ⟨M, hM, hcar⟩ := exists_lat o σ (emb σ S) (emb_injective σ S T h1 h2) (emb_span σ S T h1 h2) N hN
  exact ⟨emb σ S, M, act σ S T h1 h2, fun E => formsTie σ hσ H S T h0 h1 h2 E, hM, hcar⟩

end GlobalTheory.Mem.CoordForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_kur_of_actQ_fixed (K : FinExt l) (b : P.R.B) (hb : ∀ g ∈ GK K, P.actQ g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = b := by
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by rw [P.PD_actB]; exact hb g g.2
  exact ⟨_, hc⟩

theorem exists_kur_of_actSt_fixed (K : FinExt l)
    (hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (p : Bst P) (hp : ∀ g ∈ GK K, actSt P g p = p) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = p := by
  have hC : ∀ b : P.R.B, (∀ g ∈ GK K, actSt P g (C b) = C b) →
      ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = C b := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_kur_of_actQ_fixed P K b fun g hg =>
      C_injective (by rw [← actSt_C]; exact hb g hg)
    exact ⟨c, by rw [Polynomial.algebraMap_apply, hc]⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0] at hp ⊢
      exact hC _ hp
    · have hN : ∀ g ∈ GK K, actSt P g (monSt P p) = monSt P p := fun g hg => by
        rw [← monSt_actSt, hp g hg]
      obtain ⟨c, hc⟩ := ih (monSt P p).natDegree (by
        rw [monSt_apply, natDegree_neg, ← hn]; exact natDegree_derivative_lt h0) _ hN rfl
      rw [Polynomial.algebraMap_apply] at hc
      set a := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c with ha
      have hfa : ∀ g ∈ GK K, P.actQ g a = a := fun g hg =>
        C_injective (by rw [← actSt_C, hc]; exact hN g hg)
      obtain ⟨b, hb⟩ := (monSt_eq_zero_iff P (p + C a * X)).mp (by
        rw [map_add (f := _), ← hc]; simp)
      have hpb : p = C b - C a * X := by rw [← hb]; ring
      by_cases hc0 : c = 0
      · have : p = C b := by rw [hpb, ha, hc0]; simp
        rw [this] at hp ⊢
        exact hC _ hp
      · exfalso
        set a' := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c⁻¹ with ha'
        have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, inv_mul_cancel₀ hc0, map_one]
        refine hK (a' * b) fun g hg => ?_
        have h1 := hp g hg
        rw [hpb, map_sub, map_mul, actSt_C, actSt_C, actSt_X, hfa g hg] at h1
        have h2 : P.actQ g b - a * ((kummer P g : ℚ_[l]) • P.tB) = b :=
          C_injective (by rw [map_sub, map_mul]; linear_combination h1)
        have h3 : P.actQ g a' * a = 1 := by
          have := congrArg (P.actQ g) haa
          rwa [map_mul, map_one, hfa g hg] at this
        have h4 : P.actQ g a' = a' := by
          linear_combination a' * h3 - P.actQ g a' * haa
        rw [map_mul, h4]
        linear_combination a' * h2 + ((kummer P g : ℚ_[l]) • P.tB) * haa

end GlobalTheory.Pst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem exists_root_congr_unit : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal →
      ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ _ A P hA u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  set q := normV P with hq
  have hqc : q = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [hq, normV, Nat.card_eq_fintype_card]
  have hq1 : 1 < q := by rw [hqc]; exact Fintype.one_lt_card
  set n := q - 1 with hn
  have hn0 : 0 < n := by omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have h0 : (Ideal.Quotient.mk P.asIdeal u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ h0
    rwa [← hqc] at this
  have hlt : A.valuation (algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E)) < 1 := (hA _).mpr hmem
  set a : Ω := algebraMap E Ω (u : E) with ha
  have hcast : algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E) = a ^ n - 1 := by
    simp [ha]
  rw [hcast] at hlt

  set p : Polynomial Ω := Polynomial.X ^ n - Polynomial.C 1 with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn0.ne'
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmon
  have heval : a ^ n - 1 = (p.roots.map (fun ζ => a - ζ)).prod := by
    have := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Function.comp_def] at this
    rw [this]
  by_contra hcon
  push_neg at hcon
  have hall : ∀ ζ ∈ p.roots, 1 ≤ A.valuation (a - ζ) := by
    intro ζ hζ
    have hroot : ζ ^ n = 1 := by
      have := (Polynomial.mem_roots hmon.ne_zero).mp hζ
      simpa [hp, sub_eq_zero] using this
    rw [Valuation.map_sub_swap]
    exact hcon ζ hroot
  have : 1 ≤ A.valuation (a ^ n - 1) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    have key : ∀ s : Multiset Ω, (∀ ζ ∈ s, 1 ≤ A.valuation (a - ζ)) →
        1 ≤ (s.map (A.valuation ∘ fun ζ => a - ζ)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simp
      | cons b s ih =>
        intro h
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact one_le_mul (h b (Multiset.mem_cons_self b s))
          (ih fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ))
    exact key _ hall
  exact absurd hlt (not_lt.mpr this)

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootQuadratic
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.LocalNormNegOne

open Polynomial IsLocalRing

theorem exists_sq_sub_finite {k : Type*} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ x y : k, x ^ 2 - (D * y ^ 2 - 4) = 0 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this)
  have hodd : Fintype.card k % 2 = 1 := FiniteField.odd_card_of_char_ne_two hc
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic (R := k) (f := X ^ 2)
    (g := C (-D) * X ^ 2 + C 0 * X + C 4) (degree_X_pow 2) (degree_quadratic (neg_ne_zero.2 hD)) hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at h
  linear_combination h

variable {R : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]

theorem exists_root_quadratic (p q x₀ : R) (h₀ : x₀ ^ 2 + p * x₀ + q ∈ maximalIdeal R)
    (h₁ : IsUnit (2 * x₀ + p)) : ∃ x : R, x ^ 2 + p * x + q = 0 ∧ x - x₀ ∈ maximalIdeal R := by
  obtain ⟨x, hx, hx'⟩ := HenselianRing.is_henselian (I := maximalIdeal R)
    (X ^ 2 + C p * X + C q) (by monicity!) x₀ (by simpa using h₀) (by
      have : (X ^ 2 + C p * X + C q : R[X]).derivative.eval x₀ = 2 * x₀ + p := by
        simp [one_add_one_eq_two]
      rw [this]
      exact h₁.map _)
  exact ⟨x, by simpa [IsRoot] using hx, hx'⟩

theorem exists_eq_neg_one [Finite (ResidueField R)] (t n : R) (hD : IsUnit (t ^ 2 - 4 * n)) :
    ∃ a b : R, a ^ 2 + a * b * t + b ^ 2 * n = -1 := by
  by_cases h2 : IsUnit (2 : R)
  · obtain ⟨u, hu⟩ := h2.exists_left_inv
    have key : ∃ x b : R, x ^ 2 - ((t ^ 2 - 4 * n) * b ^ 2 - 4) = 0 := by
      generalize t ^ 2 - 4 * n = D at hD
      obtain ⟨x, y, h⟩ := exists_sq_sub_finite (k := ResidueField R)
        (by have := (h2.map (residue R)).ne_zero; rwa [map_ofNat] at this) (residue R D) (hD.map _).ne_zero
      obtain ⟨x, rfl⟩ := residue_surjective x
      obtain ⟨y, rfl⟩ := residue_surjective y
      have hm : x ^ 2 - (D * y ^ 2 - 4) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, ← h]
        simp [map_ofNat]
      by_cases hx : IsUnit x
      · obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(D * y ^ 2 - 4)) x
          (by simpa [sub_eq_add_neg] using hm) (by simpa using h2.mul hx)
        exact ⟨z, y, by linear_combination hz⟩
      · have hxm : x ∈ maximalIdeal R := hx
        have hm' : D * y ^ 2 - 4 ∈ maximalIdeal R := by
          have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ x hxm) hm
          convert this using 1; ring
        obtain ⟨d, hd⟩ := hD.exists_left_inv
        have hy : IsUnit y := by
          by_contra hy
          have hym : y ∈ maximalIdeal R := hy
          have h4 : (2 * 2 : R) ∈ maximalIdeal R := by
            have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ (D * y) hym) hm'
            convert this using 1; ring
          exact h4 (h2.mul h2)
        obtain ⟨z, hz, -⟩ := exists_root_quadratic 0 (-(4 * d)) y
          (by
            have := Ideal.mul_mem_left _ d hm'
            convert this using 1
            linear_combination (-y ^ 2) * hd) (by simpa using h2.mul hy)
        exact ⟨0, z, by linear_combination (-D) * hz - 4 * hd⟩
    obtain ⟨x, b, h⟩ := key
    refine ⟨u * (x - t * b), b, ?_⟩
    linear_combination u ^ 2 * h
      - (u * (x - t * b) * b * t + (b ^ 2 * n + 1) * (u * 2 + 1)) * hu
  · have h2m : (2 : R) ∈ maximalIdeal R := h2
    have ht : IsUnit t := by
      by_contra ht
      have htm : t ∈ maximalIdeal R := ht
      have : t ^ 2 - 4 * n ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem (Ideal.mul_mem_left _ t htm) (Ideal.mul_mem_left _ (2 * n) h2m)
        convert this using 1; ring
      exact this hD
    obtain ⟨c, hc, hc'⟩ := exists_root_quadratic t (2 * n) (-t)
      (by
        have := Ideal.mul_mem_left _ n h2m
        convert this using 1; ring)
      (by
        have : 2 * -t + t = -t := by ring
        rw [this]; exact ht.neg)
    have hcu : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ maximalIdeal R := hcu
      have : t ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem hc' hcm
        convert this using 1; ring
      exact this ht
    obtain ⟨e, he⟩ := hcu.exists_left_inv
    refine ⟨1, 2 * e, ?_⟩
    linear_combination 2 * e ^ 2 * hc - (2 * e * t + 2 * (e * c + 1)) * he

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (v : HeightOneSpectrum (𝓞 F)) (θ : 𝓞 E), (∃ t : 𝓞 F, ∃ n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ t ^ 2 - 4 * n ∉ v.asIdeal) → ∃ a b : v.adicCompletionIntegers F, ∃ t n : 𝓞 F, (θ : E) + star (θ : E) = algebraMap F E t ∧ (θ : E) * star (θ : E) = algebraMap F E n ∧ a ^ 2 + a * b * algebraMap (𝓞 F) (v.adicCompletionIntegers F) t + b ^ 2 * algebraMap (𝓞 F) (v.adicCompletionIntegers F) n = -1 := by
  rintro F E _ _ _ _ _ _ - v θ ⟨t, n, h1, h2, h3⟩
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hD := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
  rw [map_sub, map_pow, map_mul, map_ofNat] at hD
  obtain ⟨a, b, h⟩ := exists_eq_neg_one _ _ hD
  exact ⟨a, b, t, n, h1, h2, h⟩

end GlobalTheory.LocalNormNegOne
end

