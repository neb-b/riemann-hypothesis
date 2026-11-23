module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantVectorFieldsExpCoordsSmoothFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyZmodTorsorGaloisProductMapBijectiveCol
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem bc_prodMapOf_bijective_iff (R T A : Type) [CommRing R] [CommRing T] [CommRing A] [Algebra R T]
    [Algebra R A] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) :
    Function.Bijective (prodMapOf T (T ⊗[R] A) q (bcAct T act)) ↔
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  let e1 : (T ⊗[R] A) ⊗[T] (T ⊗[R] A) ≃ₐ[T] T ⊗[R] (A ⊗[R] A) :=
    (Algebra.TensorProduct.cancelBaseChange R T T (T ⊗[R] A) A).trans
      (Algebra.TensorProduct.assoc R R T T A A)
  let e2 : T ⊗[R] (Multiplicative (ZMod q) → A) ≃ₐ[T] (Multiplicative (ZMod q) → T ⊗[R] A) :=
    Algebra.TensorProduct.piRight R T T (fun _ : Multiplicative (ZMod q) => A)
  have key : ∀ x, prodMapOf T (T ⊗[R] A) q (bcAct T act) x =
      e2 (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act) (e1 x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), map_add (f := _)]
    | tmul u v =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add (f := _), hu, hu', map_add (f := _), map_add (f := _), map_add (f := _)]
      | tmul t a =>
        induction v using TensorProduct.induction_on with
        | zero => simp
        | add v v' hv hv' => rw [TensorProduct.tmul_add, map_add (f := _), hv, hv', map_add (f := _), map_add (f := _), map_add (f := _)]
        | tmul t' a' =>
          funext g
          simp [e1, e2, Algebra.TensorProduct.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
            Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.piRight_tmul, mul_comm]
  have hf : ⇑(prodMapOf T (T ⊗[R] A) q (bcAct T act)) =
      e2 ∘ (Algebra.TensorProduct.map (AlgHom.id T T) (prodMapOf R A q act)) ∘ e1 := funext key
  rw [hf]
  constructor
  · intro h
    have := (e2.symm.bijective.comp h).comp e1.symm.bijective
    convert this using 1
    funext y; simp
  · intro h
    exact e2.bijective.comp (h.comp e1.bijective)

theorem prodMapOf_finite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (q : ℕ) (hq : 0 < q)
    (act : Multiplicative (ZMod q) →* (A ≃ₐ[R] A)) : (prodMapOf R A q act).toRingHom.Finite := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hc : ((prodMapOf R A q act).toRingHom.comp
      (Algebra.TensorProduct.includeLeft (S := R) (A := A) (B := A)).toRingHom) =
      algebraMap A (Multiplicative (ZMod q) → A) := by
    ext x g
    simp [prodMapOf]
  have : (algebraMap A (Multiplicative (ZMod q) → A)).Finite := by
    exact RingHom.finite_algebraMap.2 inferInstance
  exact RingHom.Finite.of_comp_finite (hc ▸ this)

theorem eventually_prodMapOf_bijective : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (actA : Multiplicative (ZMod q) →* (A ≃ₐ[F.obj j] A)),
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      GlobalTheory.LocAcyc.IsZModTorsor c.pt (c.pt ⊗[F.obj j] A) q (GlobalTheory.TorsorColim.bcAct c.pt actA)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (GlobalTheory.TorsorColim.prodMapOf (F.obj k) (F.obj k ⊗[F.obj j] A) q
        (GlobalTheory.TorsorColim.bcAct (F.obj k) actA)) := by
  intro J _ _ F c hc q hq j A _ _ _ actA hT
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.FinitePresentation (F.obj j) (A ⊗[F.obj j] A) :=
    Algebra.FinitePresentation.trans (F.obj j) A (A ⊗[F.obj j] A)
  have hb : letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) (prodMapOf (F.obj j) A q actA)) := by
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    exact (bc_prodMapOf_bijective_iff (F.obj j) c.pt A q hq actA).1 hT.2.2.2
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.bijective_baseChange_descends_filteredColimit J F c hc j _ _ (prodMapOf (F.obj j) A q actA)
    (prodMapOf_finite _ _ q hq actA) hb
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  exact (bc_prodMapOf_bijective_iff (F.obj j) (F.obj k) A q hq actA).2 (hk k f)

end GlobalTheory.TorsorColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSpace_cocycle_vanishing_pos : ∀ (R : Type) [CommRing R] (F : PSh) (I : Cx R) (n : ℤ) (x : CohomologyClass ((chains R).obj (disc.obj F)) I n), ∃ α : Cocycle ((chains R).obj (disc.obj F)) I n, CohomologyClass.mk α = x ∧ ∀ (p : ℕ), 0 < p → ∀ (s : ℤ) (h : -(p : ℤ) + n = s), α.1.v (-(p : ℤ)) s h = 0 := by
  first | (exact @GlobalTheory.EtC.discRep) | (exact GlobalTheory.EtC.discRep) | (intros; apply GlobalTheory.EtC.discRep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDixmierMalliavinDecompProdExp
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem integrable_integral_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → E} (hF : Integrable F) :
    Integrable (fun s : ℝ => ∫ t', F (Fin.cons s t')) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  refine hint.integral_prod_left.congr (ae_of_all _ fun s => ?_)
  simp only
  congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem prodExp_fin_succ (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin (n + 1) → 𝔤) (t : Fin (n + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem integral_mul_sum_cons_kernel (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by
  have hF : ∀ m, Integrable (fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.comp (continuous_apply 0)).mul
        ((hκ m).comp (continuous_pi fun j => continuous_apply j.succ))).mul
        ((hΦ m).comp (h.continuous_prodExp X))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε hus (hκs m)))
  have heq : ∀ m s, u s * ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t') =
      ∫ t', u ((Fin.cons s t' : Fin (n + 1) → ℝ) 0) * κ m (Fin.tail (Fin.cons s t' : Fin (n + 1) → ℝ)) *
        Φ m (h.prodExp X (Fin.cons s t')) := by
    intro m s
    rw [← integral_const_mul]
    congr 1; funext t'
    simp only [Fin.cons_zero, Fin.tail_cons, prodExp_fin_succ h X, mul_assoc]
  simp_rw [hΨ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    simp_rw [heq m]; exact integrable_integral_fin_cons (hF m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [heq m]
  exact (integral_fin_succ_cons (hF m)).symm

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem SmFn.exists_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK ε hε n
  induction n with
  | zero =>
    intro j Λ hΛ
    refine ⟨1, fun _ => Λ, fun _ _ => 1, fun _ => ⟨hΛ, contDiff_const, ?_⟩, fun f hf => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      have hP : ∀ t : Fin 0 → ℝ, h.prodExp (fun k => b (j k)) t = 1 := fun t => by
        simp [IsExpLieAlgebra.prodExp]
      simp [hP, hv]
  | succ n ih =>
    intro j Λ hΛ
    obtain ⟨Λ', u, v, hΛ', hu, hv, hus, hvs, hdec⟩ :=
      _root_.GlobalTheory.HCA.smFn_dixmierMalliavin_step 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ hΛ (j 0) ε hε
    obtain ⟨N₁, Λ₁, κ₁, h₁, hd₁⟩ := ih (Fin.tail j) Λ' hΛ'
    obtain ⟨N₂, Λ₂, κ₂, h₂, hd₂⟩ := ih (Fin.tail j) Λ hΛ
    refine ⟨N₁ + N₂, Fin.append Λ₁ Λ₂,
      Fin.append (fun m t => u (t 0) * κ₁ m (Fin.tail t)) (fun m t => v (t 0) * κ₂ m (Fin.tail t)),
      ?_, ?_⟩
    · intro m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [Fin.append_left]
        exact ⟨(h₁ m).1, contDiff_cons_kernel hu (h₁ m).2.1, tsupport_cons_kernel hε.le hus (h₁ m).2.2⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ m).1, contDiff_cons_kernel hv (h₂ m).2.1, tsupport_cons_kernel hε.le hvs (h₂ m).2.2⟩
    · intro f hf
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec f hf]
      have hc : ∀ (Λ₀ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ₀ →
          Continuous fun x : G => Λ₀ [] fun y => f (x * y) := fun Λ₀ hΛ₀ =>
        SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ₀ hΛ₀ [] f hf
      congr 1
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hu.continuous hus
          (fun m => (h₁ m).2.1.continuous) (fun m => (h₁ m).2.2)
          (Φ := fun m x => Λ₁ m [] fun y => f (x * y)) (fun m => hc _ (h₁ m).1) _
          (fun s => by
            rw [hd₁ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hv.continuous hvs
          (fun m => (h₂ m).2.1.continuous) (fun m => (h₂ m).2.2)
          (Φ := fun m x => Λ₂ m [] fun y => f (x * y)) (fun m => hc _ (h₂ m).1) _
          (fun s => by
            rw [hd₂ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticWeakSolOfPolynomialLaplacianZero
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem exists_apOp_add_lower_sum {d : ℕ} (U : Set (E d)) (k : ℕ)
    (A : ℕ → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hA : ∀ i n w, ContDiffOn ℝ ∞ (A i n w) U) (t : ℕ → ℂ) :
    ∀ N ≤ k, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) U) ∧
      (∀ x ξ : E d, symb (2 * k) a x ξ = symb (2 * k) (A k) x ξ) ∧
      ∀ (u : E d → ℂ) (x : E d), apOp (2 * k) a u x =
        apOp (2 * k) (A k) u x + ∑ i ∈ Finset.range N, t i * apOp (2 * i) (A i) u x := by
  intro N
  induction N with
  | zero => intro _; exact ⟨A k, hA k, fun _ _ => rfl, fun u x => by simp⟩
  | succ N ih =>
    intro hN
    obtain ⟨a, ha, hs, hop⟩ := ih (by omega)
    obtain ⟨a'', h1, h2, h3⟩ :=
      _root_.GlobalTheory.HCA.exists_apOp_add_smul d (2 * k) (2 * N) U a (A N) (t N) (by omega) ha (hA N)
    refine ⟨a'', h1, fun x ξ => ?_, fun u x => ?_⟩
    · rw [h2, if_neg (by omega), add_zero, hs]
    · rw [h3, hop, Finset.sum_range_succ]; ring

theorem exists_elliptic_weakSol_of_aeval_eq_zero : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r, hr, c, hc, hspan, hder⟩ := _root_.GlobalTheory.ExpCoordFrame.leftInvariant_frame 𝔸 G 𝔤 h d b
  choose A hAs hAsymb hAop using GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator 𝔸 G 𝔤 h d b r c ⟨hc, hspan, hder⟩
  obtain ⟨a, ha, hsa, hopa⟩ := exists_apOp_add_lower_sum (Metric.ball (0 : E d) r) P.natDegree A
    (fun i => hAs i) (fun i => P.coeff i) P.natDegree le_rfl
  refine ⟨r, hr, 2 * P.natDegree, a, ha, ?_, ?_⟩
  · intro x hx ξ hξ
    rw [hsa, hAsymb]
    obtain ⟨i, hi⟩ := hspan x hx ξ hξ
    have hpos : 0 < ∑ i, (∑ j, c (b i) j x * ξ j) ^ 2 :=
      lt_of_lt_of_le (by positivity : 0 < (∑ j, c (b i) j x * ξ j) ^ 2)
        (Finset.single_le_sum (f := fun i => (∑ j, c (b i) j x * ξ j) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    exact_mod_cast (pow_pos hpos P.natDegree).ne'
  · intro f hf g
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h f g
    set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔdef
    have hΔ : Δ ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩))
    have hmem : Polynomial.aeval Δ P ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ Δ)
    have hzero : ∀ y, (Polynomial.aeval Δ P f' : G → ℂ) y = 0 := by
      intro y; rw [hf'2 _ hmem y, hf]; rfl
    have hu : (fun y : E d => (f : G → ℂ) (g * h.expG (coordEquiv b y))) =
        fun y => (f' : G → ℂ) (h.expG (coordEquiv b y)) := by
      funext y; rw [hf'1]
    refine _root_.GlobalTheory.HCA.weakSol_of_smooth d (2 * P.natDegree) (Metric.ball 0 r) Metric.isOpen_ball a ha _
      (h.contDiff_comp_coordEquiv f.2 g b).contDiffOn ?_
    intro x hx
    rw [hopa, hu]
    have key := hzero (h.expG (coordEquiv b x))
    rw [Polynomial.aeval_eq_sum_range] at key
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply] at key
    rw [← key, Finset.sum_range_succ _ P.natDegree, hP.coeff_natDegree, one_mul, add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hAop i f' x hx]
    · rw [hAop P.natDegree f' x hx]

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
section
open TensorProduct

namespace GlobalTheory

theorem exists_embeddings_agree_on_subfield_ne (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω]
    [CharZero L] (a : Ω) (ha : a ∉ Set.range (algebraMap L Ω)) :
    ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F),
      i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  haveI hred : IsReduced (Ω ⊗[L] Ω) := GlobalTheory.ReducedAlg.isReduced_tensor (k := L) Ω Ω
  have he : (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) ≠ 0 := by
    intro h
    have h1 : (a ⊗ₜ[L] (1 : Ω) : Ω ⊗[L] Ω) = (1 : Ω) ⊗ₜ[L] a := sub_eq_zero.mp h
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L Ω, φ 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff L (1 : Ω)).mp hc)
    have h2 := congrArg (fun x => TensorProduct.rid L Ω (LinearMap.lTensor Ω φ x)) h1
    simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h2
    apply ha
    refine ⟨(φ 1)⁻¹ * φ a, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  have hn : ¬ IsNilpotent (a ⊗ₜ[L] (1 : Ω) - (1 : Ω) ⊗ₜ[L] a : Ω ⊗[L] Ω) :=
    fun h => he h.eq_zero
  rw [nilpotent_iff_mem_prime] at hn
  push_neg at hn
  obtain ⟨J, hJ, heJ⟩ := hn
  haveI := hJ
  let g : (Ω ⊗[L] Ω) →+* FractionRing ((Ω ⊗[L] Ω) ⧸ J) :=
    (algebraMap ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J))).comp (Ideal.Quotient.mk J)
  refine ⟨FractionRing ((Ω ⊗[L] Ω) ⧸ J), inferInstance,
    g.comp (Algebra.TensorProduct.includeLeftRingHom),
    g.comp (Algebra.TensorProduct.includeRight (R := L) (A := Ω) (B := Ω)).toRingHom, ?_, ?_⟩
  · ext l
    simp only [RingHom.comp_apply]
    congr 1
    show (algebraMap L Ω l) ⊗ₜ[L] (1 : Ω) = (1 : Ω) ⊗ₜ[L] (algebraMap L Ω l)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro h
    apply heJ
    have h3 : g (a ⊗ₜ[L] (1 : Ω)) = g ((1 : Ω) ⊗ₜ[L] a) := h
    have h4 := IsFractionRing.injective ((Ω ⊗[L] Ω) ⧸ J) (FractionRing ((Ω ⊗[L] Ω) ⧸ J)) h3
    exact Ideal.Quotient.eq.mp h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalLiftOfChartLocalLiftsSquareZero
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairs
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem pair_glue : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R')
    (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)),
    (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p),
      mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) →
    ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  intro R' _ X X' φ s' W k hk
  let U : {p : Pair φ // p.1.1 ≤ W} → X'.Opens := fun i ↦ i.1.1.1.1
  let sf : ∀ i : {p : Pair φ // p.1.1 ≤ W}, ToType (X'.sheaf.1.obj (op (U i))) := fun i ↦ k i.1 i.2

  have key : ∀ (i : {p : Pair φ // p.1.1 ≤ W}) (r : Pair φ) (hr : r ≤ i.1) {x : X'} (hx : x ∈ r.1.1.1),
      X'.presheaf.germ (U i) x (Pair.le_fst hr hx) (sf i) =
        X'.presheaf.germ r.1.1.1 x hx (k r ((Pair.le_fst hr).trans i.2)) := by
    intro i r hr x hx
    rw [← hk i.1 r i.2 ((Pair.le_fst hr).trans i.2) hr]
    exact (X'.presheaf.germ_res_apply (homOfLE (show r.1.1.1 ≤ U i from Pair.le_fst hr)) x hx _).symm
  have hcomp : TopCat.Presheaf.IsCompatible X'.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun x hx ↦ ?_
    obtain ⟨r, hri, hrj, hxr⟩ := Pair.exists_le_le φ i.1 j.1 hx
    change X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf i)) = X'.presheaf.germ _ x hx (X'.presheaf.map _ (sf j))
    exact ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLELeft (U i) (U j)) x hx (sf i)).trans
      (key i r hri hxr)).trans ((X'.presheaf.germ_res_apply (TopologicalSpace.Opens.infLERight (U i) (U j))
        x hx (sf j)).trans (key j r hrj hxr)).symm
  have hcov : W.1 ≤ iSup U := fun x hx ↦ by
    obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' U W.1 (fun i ↦ homOfLE i.2) hcov sf hcomp
  exact ⟨G, fun p hp ↦ hG ⟨p, hp⟩⟩

end GlobalTheory.CechDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoTrivialProjBundleProdFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_trivialProjBundle_prod_fibre : ∀ (q N : ℕ) (F : PSh), Inv q (disc.obj F) → ∃ θ : disc.obj F ⨯ fibQ q N ≅ pullback (trivV N (disc.obj F)) (PGL.pr N), θ.hom ≫ pullback.fst _ _ = prod.fst ∧ θ.hom ≫ pullback.snd _ _ ≫ PGL.line N = prod.snd ≫ lineQ q N := by
  first | (exact @GlobalTheory.EtC.trivProj_iso) | (exact GlobalTheory.EtC.trivProj_iso) | (intros; apply GlobalTheory.EtC.trivProj_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mayerVietoris_connecting_exact : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ d : ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ n : ℤ, H R (pullback f g) F n →+ H R E F (n + 1), (∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (h : Cover2 R f g) (n : ℤ), (∀ a b, pull R (pullback.fst f g) F n a = pull R (pullback.snd f g) F n b ↔ ∃ x, pull R f F n x = a ∧ pull R g F n x = b) ∧ (∀ c, d f g h n c = 0 ↔ ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) ∧ ∀ x, (pull R f F (n + 1) x = 0 ∧ pull R g F (n + 1) x = 0) ↔ ∃ c, d f g h n c = x) ∧ ∀ {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E') (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (h : Cover2 R f g) (h' : Cover2 R f' g') (n : ℤ) c, pull R p F (n + 1) (d f' g' h' n c) = d f g h n (pull R (pullback.map f g f' g' u v p hu hv) F n c) := by
  first | (exact @GlobalTheory.EtC.mayerVietoris) | (exact GlobalTheory.EtC.mayerVietoris) | (intros; apply GlobalTheory.EtC.mayerVietoris  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodCohomologyClassOfRichBasedStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_period_cohomologyClass_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ c : H1 K.Oc, ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  first | exact @GlobalTheory.AnPer.Charts.exists_perCl | exact GlobalTheory.AnPer.Charts.exists_perCl | (intros; apply GlobalTheory.AnPer.Charts.exists_perCl <;> assumption)
end

