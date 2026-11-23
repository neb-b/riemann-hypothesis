module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.Cut.Coc

theorem KOG_torsion {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (t : KOG O k) :
    ∃ d : O, d ≠ 0 ∧ d • t = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  choose u hu using hb
  exact ⟨u, funext fun j => hu j⟩

theorem smul_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k : ℕ} (t : KOG O k) :
    Continuous fun a : O => a • t := by
  obtain ⟨d, hd, hdt⟩ := KOG_torsion t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.mp hO).1 n
  have hk : ∀ a ∈ (IsLocalRing.maximalIdeal O ^ n : Ideal O), a • t = 0 := by
    intro a ha
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : c * ϖ ^ n = (c * ((u⁻¹ : Oˣ) : O)) * (u * ϖ ^ n) := by
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, mul_smul, hdt, smul_zero]
  refine continuous_of_continuousAt_zero (LinearMap.toSpanSingleton O (KOG O k) t) ?_
  refine (continuousAt_const (y := (0 : KOG O k))).congr ?_
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
  exact (hk a ha).symm

theorem lin_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k n : ℕ} {X : Type} [Fintype X]
    [DecidableEq X] (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] KOG O k) : Continuous φ := by
  have h : ∀ y : X → Matrix (Fin n) (Fin n) O,
      φ y = ∑ x, ∑ p, ∑ q, y x p q • φ (Pi.single x (Matrix.single p q 1)) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    apply congrArg φ
    funext x
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp only [Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (y x)
    · intro b _ hb
      simp [Pi.smul_apply, Pi.single_eq_of_ne hb.symm]
    · simp
  rw [show (φ : _ → _) = _ from funext h]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact (smul_cont hO _).comp (by fun_prop : Continuous fun y : X → Matrix (Fin n) (Fin n) O => y x p q)

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

def tw (g : GE D.nd) : S.X' → MatN D.nd i :=
  fun x' => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rO D.nd i r (S.p x') g

theorem tw_mem (g : GE D.nd) : InR' D.nd r S (tw i r S g) := by
  refine ⟨1, fun _ _ => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => g,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  rw [Fin.sum_univ_one]
  rfl

theorem yg_mem (g : GE D.nd) : InY D.nd r S (yg D.nd r S g) := by
  refine ⟨1, fun _ => tw i r S 1, fun _ => g, fun _ => tw_mem i r S 1, ?_⟩
  rw [Fin.sum_univ_one]
  funext x'
  simp [tw]

theorem yg_mul (g h : GE D.nd) :
    yg D.nd r S (g * h) = yg D.nd r S g + tw i r S g * yg D.nd r S h := by
  funext x'
  simp only [yg, tw, Pi.add_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_smul, mul_assoc]
  rw [smul_comm]
  abel

theorem yg_cont (hr : GoodR D.nd i r) : Continuous fun g => yg D.nd r S g := by
  refine continuous_pi fun x' => ?_
  have hc : Continuous fun g => rO D.nd i r (S.p x') g := (hr (S.p x')).1
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine ((h1.smul (hc.mul (continuous_const (y := Eel D.nd S x')))).sub
    (continuous_const (y := Eel D.nd S x'))).congr fun g => ?_
  simp [yg]

theorem cocW_le (hr : GoodR D.nd i r) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hψ : ∀ g, ψ (tw i r S g) = M g) :
    cocW i r S Xs ψ ≤ Z1 (WKG M) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, -, rfl⟩
  refine ⟨(lin_cont (D.nd.O_adic i) φ).comp (yg_cont i r S hr), fun g h => ?_⟩
  show φ _ = φ _ + WKG M g (φ _)
  rw [yg_mul, map_add (f := _), hφ _ (tw_mem i r S g) _ (yg_mem i r S h), hψ]
  rfl

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : GoodCongruenceObjects D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.Coc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRing
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.FlatLocCompl

theorem mem_pow_smul_top_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (r : R) (k : ℕ) (z : S) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R S) ↔ z ∈ Ideal.span {(algebraMap R S r) ^ k} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨e, -, rfl⟩
    exact ⟨e, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, map_pow]⟩

theorem mem_pow_smul_top_self_iff {R : Type} [CommRing R] (r : R) (k : ℕ) (z : R) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R R) ↔ z ∈ Ideal.span {r ^ k} := by
  rw [mem_pow_smul_top_iff]; rfl

theorem flat_of_levels {B E : Type} [CommRing B] [IsNoetherianRing B] [CommRing E] [Algebra B E] (p : B)
    (hc : IsAdicComplete (Ideal.span {algebraMap B E p}) E)
    (hinj : ∀ (b : B) (k : ℕ), algebraMap B E b ∈ Ideal.span {(algebraMap B E p) ^ k} →
      b ∈ Ideal.span {p ^ k})
    (hden : ∀ (y : E) (k : ℕ), ∃ b : B, algebraMap B E b - y ∈ Ideal.span {(algebraMap B E p) ^ k}) :
    Module.Flat B E := by
  set I : Ideal B := Ideal.span {p} with hI
  haveI : IsAdicComplete I E := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := E)]
    rwa [hI, Ideal.map_span, Set.image_singleton]
  let f : B →ₗ[B] E := Algebra.linearMap B E
  have hle : ∀ k, (I ^ k • ⊤ : Submodule B B) ≤ (I ^ k • ⊤ : Submodule B E).comap f := by
    intro k z hz
    rw [Submodule.mem_comap, mem_pow_smul_top_iff]
    rw [mem_pow_smul_top_self_iff, Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    exact Ideal.mem_span_singleton.2 ⟨algebraMap B E c, by simp [f, map_pow]⟩
  let fk : ∀ k : ℕ, AdicCompletion I B →ₗ[B] E ⧸ (I ^ k • ⊤ : Submodule B E) := fun k =>
    (Submodule.mapQ _ _ f (hle k)) ∘ₗ AdicCompletion.eval I B k
  have hfk : ∀ {m n : ℕ} (hmn : m ≤ n), Submodule.factorPow I E hmn ∘ₗ fk n = fk m := by
    intro m n hmn
    refine LinearMap.ext fun x => ?_
    simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply]
    rw [← AdicCompletion.transitionMap_comp_eval_apply I B hmn x]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [← hb]
    rfl
  let G : AdicCompletion I B →ₗ[B] E := IsAdicComplete.lift I fk hfk
  have hG : ∀ k x, Submodule.Quotient.mk (p := (I ^ k • ⊤ : Submodule B E)) (G x) = fk k x :=
    fun k x => IsAdicComplete.mk_lift I hfk k x
  have hbij : Function.Bijective G := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      ext k
      have h1 := hG k x
      rw [hx, Submodule.Quotient.mk_zero] at h1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      have h2 : fk k x = Submodule.Quotient.mk (f b) := by
        simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply, ← hb]; rfl
      rw [h2, eq_comm, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff] at h1
      rw [← hb, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_self_iff]
      exact hinj b k h1
    · intro y
      choose b hb using fun k => hden y k
      have hcau : ∀ k, b k ≡ b (k + 1) [SMOD (I ^ k • ⊤ : Submodule B B)] := by
        intro k
        rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
        apply hinj
        have h3 : algebraMap B E (b k - b (k + 1)) =
            (algebraMap B E (b k) - y) - (algebraMap B E (b (k + 1)) - y) := by rw [map_sub]; ring
        rw [h3]
        refine Ideal.sub_mem _ (hb k) ?_
        refine Ideal.span_singleton_le_span_singleton.2 ?_ (hb (k + 1))
        exact pow_dvd_pow _ (Nat.le_succ k)
      refine ⟨AdicCompletion.mk I B (AdicCompletion.AdicCauchySequence.mk I B b hcau), ?_⟩
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro k
      rw [SModEq, hG]
      change Submodule.Quotient.mk (f (b k)) = Submodule.Quotient.mk y
      rw [← SModEq, SModEq.sub_mem, mem_pow_smul_top_iff]
      exact hb k
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective G hbij).symm

end GlobalTheory.FlatLocCompl

namespace GlobalTheory.FlatLocCompl

theorem flat_letA (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E]
    [Algebra (LetA O n) E] (p : ℕ) (hπ : IsUnit (algebraMap (LetA O n) E letπ))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hden : ∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) -
      algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) :
    Module.Flat (LetA O n) E := by
  let B := Localization.Away (letπ : LetA O n)
  let g : B →+* E := IsLocalization.Away.lift (S := B) (letπ : LetA O n) hπ
  letI : Algebra B E := g.toAlgebra
  have hg : ∀ a : LetA O n, algebraMap B E (algebraMap (LetA O n) B a) = algebraMap (LetA O n) E a :=
    fun a => IsLocalization.Away.lift_eq (S := B) (letπ : LetA O n) hπ a
  haveI : IsScalarTower (LetA O n) B E := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have hp : algebraMap B E (p : B) = (p : E) := map_natCast _ _
  haveI : Module.Flat B E := by
    refine flat_of_levels (p : B) (by rwa [hp]) ?_ ?_
    · intro b k hb
      rw [hp] at hb
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (letπ : LetA O n)) b
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B s = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} := by
        rw [← hg, ← h1, map_mul]
        exact Ideal.mul_mem_right _ _ hb
      obtain ⟨c, rfl⟩ := hsat a k h2
      refine Ideal.mem_span_singleton.2 ⟨IsLocalization.mk' B c s, ?_⟩
      show IsLocalization.mk' B ((p : LetA O n) ^ k * c) s = (p : B) ^ k * IsLocalization.mk' B c s
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    · intro y k
      obtain ⟨a, m, h⟩ := hden y k
      let s : Submonoid.powers (letπ : LetA O n) := ⟨letπ ^ m, m, rfl⟩
      refine ⟨IsLocalization.mk' B a s, ?_⟩
      rw [hp]
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B (letπ ^ m) = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap B E (IsLocalization.mk' B a s) * algebraMap (LetA O n) E (letπ ^ m) =
          algebraMap (LetA O n) E a := by rw [← hg, ← hg, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hπ.pow m
      rw [← map_pow] at hv
      have h3 : algebraMap B E (IsLocalization.mk' B a s) - y =
          -((y * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a) * ↑v⁻¹) := by
        rw [← h2, ← hv, neg_mul_eq_neg_mul, neg_sub, ← sub_mul, mul_assoc, Units.mul_inv, mul_one]
      rw [h3]
      exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ h)
  exact Module.Flat.trans (LetA O n) B E

end GlobalTheory.FlatLocCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algHom_self (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F) (c : ↥F) :
    ‖((σ c : ↥F) : Om l)‖ = ‖(c : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  have h1 := minpoly.algHom_eq F.val F.val.injective (σ c)
  have h2 := minpoly.algHom_eq F.val F.val.injective c
  have h3 := minpoly.algHom_eq σ σ.injective c
  simp only [IntermediateField.coe_val] at h1 h2
  exact congrArg spectralValue (h1.trans (h3.trans h2.symm))

theorem norm_l_pow_lt_one {j : ℕ} (hj : 1 ≤ j) : ‖(l : Om l) ^ j‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (by omega)
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_sub_pow_mul_algHom (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F)
    {j : ℕ} (hj : 1 ≤ j) (d : ↥F) :
    ‖((d - (l : ↥F) ^ j * σ d : ↥F) : Om l)‖ = ‖(d : Om l)‖ := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < ‖(d : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast hd)
  have hlt : ‖-((l : Om l) ^ j * ((σ d : ↥F) : Om l))‖ < ‖(d : Om l)‖ := by
    rw [norm_neg, norm_mul, norm_algHom_self]
    exact mul_lt_of_lt_one_left hd' (norm_l_pow_lt_one hj)
  have e : ((d - (l : ↥F) ^ j * σ d : ↥F) : Om l) =
      (d : Om l) + -((l : Om l) ^ j * ((σ d : ↥F) : Om l)) := by
    push_cast
    ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

theorem frK_isometric_and_one_sub_surjective (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 →
      ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  refine ⟨norm_algHom_self _ _, fun j hj c hc => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  let T : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    LinearMap.id - (LinearMap.mulLeft ℚ_[l] ((l : ↥(K0 K)) ^ j)).comp (frK P K).toLinearMap
  have hT : ∀ d, T d = d - (l : ↥(K0 K)) ^ j * frK P K d := fun d => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro d hd
    have := norm_sub_pow_mul_algHom _ (frK P K) hj d
    rw [← hT, hd] at this
    have h0 : (d : Om l) = 0 := by
      rw [← norm_eq_zero, ← this]; simp
    exact_mod_cast h0
  obtain ⟨d, hd⟩ := LinearMap.injective_iff_surjective.1 hinj c
  rw [hT] at hd
  refine ⟨d, ?_, hd⟩
  rw [← norm_sub_pow_mul_algHom _ (frK P K) hj d, hd]
  exact hc

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem log_interp (a b c : ℝ) (h : b - a ≠ 0) :
    a * ((b - c) / (b - a)) + b * (1 - (b - c) / (b - a)) = c := by
  field_simp
  ring

theorem gC_pos_of_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ →
    ρ < 1 → 0 < gC l ρ x := by
  intro l _ x hx ρ hρ0 hρ1
  have hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r) :=
    fun r h0 h1 => isGauss_gC_target l r h0 h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x := fun r h0 h1 => ((hN r h0 h1).1 x).1
  have h0 : gC l (l : ℝ)⁻¹ x ≠ 0 := GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx
  rcases hρ0.eq_or_lt with h | h
  · subst h
    exact lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm
  by_contra hneg
  have hz : gC l ρ x = 0 := le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)
  obtain ⟨r₁, c, k, hr₁, -, hc, hmon⟩ := GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0
  obtain ⟨ρ', h1', h2'⟩ := exists_between (lt_min hr₁ h)
  have hρ'0 : 0 < ρ' := hi0.trans h1'
  have hρ'r : ρ' < r₁ := h2'.trans_le (min_le_left _ _)
  have hρ'ρ : ρ' < ρ := h2'.trans_le (min_le_right _ _)
  have hρpos : 0 < ρ := hi0.trans h
  have hpos : 0 < gC l ρ' x := by
    have e : gC l ρ' x = c * ρ' ^ k := hmon ρ' h1' hρ'r
    rw [e]
    exact mul_pos hc (zpow_pos hρ'0 k)
  have hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ' := Real.log_lt_log hi0 h1'
  have hL2 : Real.log ρ' < Real.log ρ := Real.log_lt_log hρ'0 hρ'ρ
  have hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹ := by linarith
  have ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) :=
    div_nonneg (by linarith) hd.le
  have ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1 :=
    (div_lt_one hd).2 (by linarith)
  have he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) *
      ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ' := by
    rw [Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add,
      log_interp _ _ _ hd.ne', Real.exp_log hρ'0]
  have hcv := _root_.GlobalTheory.PMon.Gauss.gC_logConvex l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le
  rw [he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero] at hcv
  linarith

theorem gC_pos_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    0 < gC l ρ x :=
  gC_pos_of_ne_zero

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end

