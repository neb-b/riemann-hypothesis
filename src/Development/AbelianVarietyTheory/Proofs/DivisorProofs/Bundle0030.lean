module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftModPSqPerfectField
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem wittVector_dvd_of_coeff_zero_eq_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : a.coeff 0 = 0) :
    (p : WittVector p k) ∣ a := by
  by_cases h0 : a = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso
    simp only [pow_zero, one_mul] at ha
    exact hb ha
  | succ n => exact ⟨(p : WittVector p k) ^ n * b, by ring⟩

theorem wittVector_natCast_ne_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] : (p : WittVector p k) ≠ 0 := by
  intro h
  have := WittVector.coeff_p_pow p k 1
  rw [pow_one, h] at this
  simp at this

theorem exists_flat_lift_mod_p_sq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧
      RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧
      ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  intro p _ k _ _ _
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  set I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k) ^ 2} with hI
  have hlift : ∀ a ∈ I, WittVector.constantCoeff a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [map_mul, map_pow, map_natCast, CharP.cast_eq_zero]
  let π : (WittVector p k ⧸ I) →+* k := Ideal.Quotient.lift I WittVector.constantCoeff hlift
  have hπ : ∀ a, π (Ideal.Quotient.mk I a) = a.coeff 0 := by
    intro a
    simp [π, Ideal.Quotient.lift_mk, WittVector.constantCoeff_apply]
  have hp0 : π (p : WittVector p k ⧸ I) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k p
  refine ⟨WittVector p k ⧸ I, inferInstance, π, ?_, ?_, ?_, ?_⟩
  · intro r
    refine ⟨Ideal.Quotient.mk I (WittVector.teichmuller p r), ?_⟩
    rw [hπ, WittVector.teichmuller_coeff_zero]
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hπ, Ideal.mem_span_singleton]
    constructor
    · intro ha
      obtain ⟨c, rfl⟩ := wittVector_dvd_of_coeff_zero_eq_zero p k a ha
      exact ⟨Ideal.Quotient.mk I c, by rw [map_mul, map_natCast]⟩
    · rintro ⟨c, hc⟩
      rw [← hπ, hc, map_mul, hp0, zero_mul]
  · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have hpne := wittVector_natCast_ne_zero p k
    have hac : a = (p : WittVector p k) * c := by
      apply mul_left_cancel₀ hpne
      rw [hc]; ring
    rw [Ideal.mem_span_singleton]
    exact ⟨Ideal.Quotient.mk I c, by rw [hac, map_mul, map_natCast]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmodule
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisEmbedding
section
namespace GlobalTheory.GaloisEmbeddingExistence

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R']
    (hinj : Function.Injective (algebraMap R R')) :
    ∃ (L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
        ∃ (j : R' →ₐ[R] L), Function.Injective j := by
  classical
  set K := FractionRing R
  set Ω := AlgebraicClosure K
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
  have hΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hΩ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let φ : R' →ₐ[R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφ : Function.Injective φ := by
    have h1 : (RingHom.ker φ).comap (algebraMap R R') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hx
      exact hΩ (by simpa using hx)
    have h2 : RingHom.ker φ = ⊥ := Ideal.eq_bot_of_comap_eq_bot h1
    exact (RingHom.injective_iff_ker_eq_bot φ).2 h2
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (inferInstance : Module.Finite R R'))
  let M : IntermediateField K Ω := IntermediateField.adjoin K (φ '' (s : Set R'))
  haveI : Finite (φ '' (s : Set R')) := (s.finite_toSet.image φ).to_subtype
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hmem : ∀ x : R', φ x ∈ L := by
    intro x
    have hx : x ∈ Submodule.span R (s : Set R') := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hML (IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩)
    | zero => simpa using L.zero_mem
    | add x y _ _ hx hy => simpa using L.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply R K Ω]
      exact L.mul_mem (L.algebraMap_mem _) hx
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  let j : R' →ₐ[R] L :=
    { toFun := fun x => ⟨φ x, hmem x⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y)
      commutes' := fun r => Subtype.ext (φ.commutes r) }
  exact ⟨j, fun x y h => hφ (congrArg Subtype.val h)⟩

end GlobalTheory.GaloisEmbeddingExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmented
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_generators_dual_point_derivations :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k),
      IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k),
        (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧
        (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  intro k A _ _ _ _ ε hnil
  set I : Ideal A := RingHom.ker ε with hI
  let W : Submodule k A := (I ^ 2).restrictScalars k
  let U : Submodule k (A ⧸ W) := (I.restrictScalars k).map W.mkQ
  let b : Module.Basis (Fin (Module.finrank k U)) k U := Module.finBasis k U
  have hx : ∀ j, ∃ y, y ∈ I ∧ W.mkQ y = (b j : A ⧸ W) := fun j => by
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.mp (b j).2
    exact ⟨y, hy, hy'⟩
  choose x hxI hxq using hx
  let P : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A) ∘ₗ ε.toLinearMap
  have hPa : ∀ a, P a = a - algebraMap k A (ε a) := fun a => rfl
  have hP : ∀ a, P a ∈ I := fun a => by
    rw [hI, RingHom.mem_ker, hPa, map_sub, AlgHom.commutes]
    simp
  let T : A →ₗ[k] U := LinearMap.codRestrict U (W.mkQ ∘ₗ P)
    (fun a => Submodule.mem_map_of_mem (show P a ∈ I.restrictScalars k from hP a))
  have hT : ∀ a, ((T a : U) : A ⧸ W) = W.mkQ (P a) := fun a => rfl
  let l : Fin (Module.finrank k U) → A →ₗ[k] k := fun i => b.coord i ∘ₗ T
  have hspan : ∀ y ∈ I, ∃ s ∈ Submodule.span k (Set.range x), y - s ∈ I ^ 2 := by
    intro y hy
    let u : U := ⟨W.mkQ y, Submodule.mem_map_of_mem (show y ∈ I.restrictScalars k from hy)⟩
    refine ⟨∑ j, b.repr u j • x j,
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩
    have h1 : W.mkQ (∑ j, b.repr u j • x j) = ∑ j, b.repr u j • (b j : A ⧸ W) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hxq]
    have h2 := congrArg Subtype.val (b.sum_repr u)
    push_cast at h2
    have hq : W.mkQ (∑ j, b.repr u j • x j) = W.mkQ y := by rw [h1, h2]
    have h0 : W.mkQ (y - ∑ j, b.repr u j • x j) = 0 := by rw [map_sub, hq, sub_self]
    have h3 := LinearMap.mem_ker.mpr h0
    rw [Submodule.ker_mkQ] at h3
    exact h3
  let S := Algebra.adjoin k (Set.range x)
  have spanS : Submodule.span k (Set.range x) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
  have spanI : Submodule.span k (Set.range x) ≤ I.restrictScalars k :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hxI j)
  have hstep : ∀ n : ℕ, ∀ z ∈ I ^ n,
      z ∈ Subalgebra.toSubmodule S ⊔ (I ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro z _
      refine Submodule.mem_sup.mpr ⟨_, S.algebraMap_mem (ε z), P z, ?_, ?_⟩
      · show P z ∈ I ^ (0 + 1)
        rw [zero_add, pow_one]; exact hP z
      · rw [hPa]; abel
    | succ n ih =>
      intro z hz
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ (fun a c ha hc => add_mem ha hc)
      intro y hy w hw
      obtain ⟨s, hs, hys⟩ := hspan y hy
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (ih w hw)
      have h1 : s * v ∈ I ^ (n + 1 + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul (spanI hs) hv
      have h2 : (y - s) * w ∈ I ^ (n + 1 + 1) := by
        rw [show n + 1 + 1 = 2 + n by omega, pow_add]; exact Ideal.mul_mem_mul hys hw
      refine Submodule.mem_sup.mpr ⟨s * t, S.mul_mem (spanS hs) ht, s * v + (y - s) * w,
        add_mem h1 h2, ?_⟩
      rw [← htv]; ring
  have hall : ∀ n : ℕ, ∀ a : A, a ∈ Subalgebra.toSubmodule S ⊔ (I ^ n).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro a
      refine Submodule.mem_sup.mpr ⟨0, zero_mem _, a, ?_, zero_add a⟩
      show a ∈ I ^ 0
      rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n ih =>
      intro a
      obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp (ih a)
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (hstep n w hw)
      refine Submodule.mem_sup.mpr ⟨s + t, add_mem hs ht, v, hv, ?_⟩
      rw [← hsw, ← htv]; abel
  refine ⟨Module.finrank k U, x, l, ?_, ?_, ?_⟩
  · intro i a c
    have key : P (a * c) - (ε a • P c + ε c • P a) = P a * P c := by
      simp only [hPa, Algebra.smul_def, map_mul]; ring
    have hmem : P (a * c) - (ε a • P c + ε c • P a) ∈ W := by
      rw [key]
      show P a * P c ∈ I ^ 2
      rw [pow_two]; exact Ideal.mul_mem_mul (hP a) (hP c)
    have hTac : T (a * c) = ε a • T c + ε c • T a := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hT, hT, hT]
      have h0 : W.mkQ (P (a * c) - (ε a • P c + ε c • P a)) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hmem
      rw [map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero] at h0
      exact h0
    show b.coord i (T (a * c)) = ε a * b.coord i (T c) + ε c * b.coord i (T a)
    rw [hTac, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro i j
    have hTx : T (x j) = b j := by
      apply Subtype.ext
      rw [hT, hPa]
      have : ε (x j) = 0 := (RingHom.mem_ker).mp (hxI j)
      rw [this, map_zero, sub_zero, hxq]
    show b.coord i (T (x j)) = _
    rw [hTx, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · obtain ⟨N, hN⟩ := hnil
    have hv : (I ^ N).restrictScalars k = ⊥ := by
      rw [hI, hN, Submodule.zero_eq_bot, Submodule.restrictScalars_bot]
    refine eq_top_iff.mpr (fun a _ => ?_)
    have := hall N a
    rw [hv, sup_bot_eq] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensModNsmulOfFgNumberField
section
open NumberField

namespace GlobalTheory.GensModNsmul

theorem exists_gen_mod_nsmul_of_linearMap (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N] (π : N →ₗ[𝓞 E] E) :
    ∃ l : N, ∀ x : N, ∃ o : 𝓞 E, ∃ y : N, π x = o • π l + M • π y := by
  have hfg : (LinearMap.range π).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (algebraMap (𝓞 E) E d) ≠ 0 := by simpa using hd0
  set I : Ideal (𝓞 E) := Submodule.comap (Algebra.linearMap (𝓞 E) E) (LinearMap.range (d • π)) with hI
  have hmem : ∀ a : 𝓞 E, a ∈ I ↔ ∃ x : N, d • π x = algebraMap (𝓞 E) E a := by
    intro a; simp [hI]
  have hM0 : (M : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have key : ∃ a ∈ I, Ideal.span {(M : 𝓞 E)} * I ⊔ Ideal.span {a} = I := by
    by_cases h : I = ⊥
    · exact ⟨0, I.zero_mem, by simp [h]⟩
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
        (I := Ideal.span {(M : 𝓞 E)} * I) (J := I) Ideal.mul_le_right
        (mul_ne_zero (by simpa using hM0) h)
      refine ⟨a, ?_, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨a, haI, ha⟩ := key
  obtain ⟨l, hl⟩ := (hmem a).1 haI
  refine ⟨l, fun x => ?_⟩
  obtain ⟨b, hb⟩ := hint (π x) ⟨x, rfl⟩
  have hbI : b ∈ I := (hmem b).2 ⟨x, hb.symm⟩
  rw [← ha, Submodule.mem_sup] at hbI
  obtain ⟨u, hu, v, hv, huv⟩ := hbI
  obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
  obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  obtain ⟨y, hy⟩ := (hmem c).1 hc
  refine ⟨o, y, ?_⟩
  apply mul_left_cancel₀ hd0'
  rw [Algebra.smul_def] at hb hl hy
  rw [← hb, ← huv, Algebra.smul_def, nsmul_eq_mul, map_add (f := _), map_mul, map_mul, map_natCast, ← hl, ← hy]
  ring

theorem exists_gens_mod_nsmul_of_injective (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (r : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N]
    (f : N →ₗ[𝓞 E] (Fin r → E)), Function.Injective f →
    ∃ e : Fin r → N, ∀ x : N, ∃ o : Fin r → 𝓞 E, ∃ y : N, x = ∑ i, o i • e i + M • y := by
  induction r with
  | zero =>
    intro N _ _ _ f hf
    refine ⟨Fin.elim0, fun x => ⟨Fin.elim0, 0, ?_⟩⟩
    simpa using hf (Subsingleton.elim (f x) (f 0))
  | succ r ih =>
    intro N _ _ _ f hf
    let π : N →ₗ[𝓞 E] E := (LinearMap.proj 0) ∘ₗ f
    obtain ⟨l, hl⟩ := exists_gen_mod_nsmul_of_linearMap E M hM N π
    let f' : LinearMap.ker π →ₗ[𝓞 E] (Fin r → E) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ) ∘ₗ f ∘ₗ (LinearMap.ker π).subtype
    have hf' : Function.Injective f' := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Submodule.coe_zero, map_zero]; exact x.2
      · simpa [f'] using congrFun hx j
    obtain ⟨e, he⟩ := ih (LinearMap.ker π) f' hf'
    refine ⟨Fin.cons l (fun i => (e i : N)), fun x => ?_⟩
    obtain ⟨o, y, hoy⟩ := hl x
    have hk : x - o • l - M • y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, hoy]; abel
    obtain ⟨o', y', h'⟩ := he ⟨_, hk⟩
    refine ⟨Fin.cons o o', y + y', ?_⟩
    have h2 := congrArg Subtype.val h'
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] at h2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_add]
    have : x = o • l + M • y + (x - o • l - M • y) := by abel
    rw [this, h2]; abel

theorem exists_gens_mod_nsmul (E : Type) [Field E] [NumberField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hM : 1 ≤ M) (hΛ : Λ.FG) :
    ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧
      ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  obtain ⟨e, he⟩ := exists_gens_mod_nsmul_of_injective E M hM r Λ Λ.subtype Subtype.val_injective
  refine ⟨fun i => e i, fun i => (e i).2, fun x hx => ?_⟩
  obtain ⟨o, y, h⟩ := he ⟨x, hx⟩
  refine ⟨o, y, y.2, ?_⟩
  have h2 := congrArg Subtype.val h
  simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] using h2

end GlobalTheory.GensModNsmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntSmulMemOfIsLattice
section
namespace GlobalTheory.LatticeIntegerMultipleMembership

theorem exists_int_smul_mem_of_isLattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (y : Fin n → E) : ∃ (D : ℤ), D ≠ (0 : ℤ) ∧ D • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h := L.smul_mem (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) hax
    have e : (d * a) • c • x
        = (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) • a • x := by
      change (d * a) • c • x = (d • c) • a • x
      rw [mul_smul, smul_assoc, smul_comm a c x]
    rw [e]; exact h

end GlobalTheory.LatticeIntegerMultipleMembership
end

