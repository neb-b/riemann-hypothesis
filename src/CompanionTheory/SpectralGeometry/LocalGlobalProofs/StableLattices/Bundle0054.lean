module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
section
noncomputable section

namespace GlobalTheory.CompanionTheory.DictLoc

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

def Cp (A : Type) : Type := A

section Model

theorem exists_model_field {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [Field A] [Algebra K A] [FiniteDimensional K A] [TopologicalSpace A] [IsModuleTopology K A] :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ := by
  haveI : CompleteSpace K := inferInstance
  letI fL : Field (Cp A) := ‹Field A›
  letI aL : Algebra K (Cp A) := ‹Algebra K A›
  haveI : FiniteDimensional K (Cp A) := ‹FiniteDimensional K A›
  haveI : Algebra.IsAlgebraic K (Cp A) := Algebra.IsAlgebraic.of_finite K (Cp A)
  letI nL : NontriviallyNormedField (Cp A) := spectralNorm.nontriviallyNormedField K (Cp A)
  letI mL : NormedAlgebra K (Cp A) := spectralNorm.normedAlgebra K (Cp A)
  haveI uL : IsUltrametricDist (Cp A) := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := Cp A))
  haveI pL : ProperSpace (Cp A) := FiniteDimensional.proper K (Cp A)
  haveI : IsModuleTopology K (Cp A) := isModuleTopologyOfFiniteDimensional
  haveI : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  let f : A ≃ₗ[K] Cp A := LinearEquiv.refl K A
  refine ⟨Cp A, nL, uL, pL, RingEquiv.refl A, IsModuleTopology.continuous_of_linearMap f.toLinearMap,
    IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap, fun c x => ?_⟩
  exact (spectralNorm_eq_of_equiv (K := K) (L := Cp A) c x).symm

theorem isField_tensor_of_no_algHom {F K E : Type} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    (h2 : Module.finrank F E = 2) (hn : IsEmpty (E →ₐ[F] K)) : IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hA : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, h2]
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] E)
  by_cases hb : m = ⊥
  · subst hb
    exact ((RingEquiv.quotientBot (K ⊗[F] E)).symm.toMulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).1 hm))
  · exfalso
    letI := Ideal.Quotient.field m
    let φ : (K ⊗[F] E) →ₐ[K] (K ⊗[F] E) ⧸ m := Ideal.Quotient.mkₐ K m
    have hs : Function.Surjective φ := Ideal.Quotient.mkₐ_surjective K m
    have h3 := LinearMap.finrank_range_add_finrank_ker φ.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, hA] at h3
    have hk : 0 < Module.finrank K (LinearMap.ker φ.toLinearMap) := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      haveI : Nontrivial (LinearMap.ker φ.toLinearMap) :=
        ⟨⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.2 hx)⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
      exact Module.finrank_pos
    haveI : Module.Finite K ((K ⊗[F] E) ⧸ m) := Module.Finite.of_surjective φ.toLinearMap hs
    have hq : 0 < Module.finrank K ((K ⊗[F] E) ⧸ m) := Module.finrank_pos
    have h1 : Module.finrank K ((K ⊗[F] E) ⧸ m) = 1 := by omega
    have hbj : Function.Bijective (Algebra.ofId K ((K ⊗[F] E) ⧸ m)) :=
      ⟨(algebraMap K _).injective, fun y => by
        have : (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
        have hy : y ∈ (⊥ : Subalgebra K ((K ⊗[F] E) ⧸ m)) := this ▸ Algebra.mem_top
        obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
        exact ⟨a, ha⟩⟩
    let ε : K ≃ₐ[K] (K ⊗[F] E) ⧸ m := AlgEquiv.ofBijective _ hbj
    exact hn.false (((ε.symm.toAlgHom.comp φ).restrictScalars F).comp Algebra.TensorProduct.includeRight)

end Model

section Main

theorem exists_model {K A : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] (hA : IsField A) :
    ∃ (L : Type) (_ : NontriviallyNormedField L) (_ : IsUltrametricDist L) (_ : ProperSpace L) (e : A ≃+* L),
      Continuous e ∧ Continuous e.symm ∧ ∀ (c : A ≃ₐ[K] A) (x : A), ‖e (c x)‖ = ‖e x‖ :=
  letI := hA.toField
  exists_model_field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

def sigEquiv (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) : (K ⊗[F] E) ≃ₐ[K] (K ⊗[F] E) :=
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.map (AlgHom.id K K) σ) (Algebra.TensorProduct.map (AlgHom.id K K) σ)
    (by ext x; simp [h]) (by ext x; simp [h])

theorem sigEquiv_apply (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigEquiv K h y = sigR K σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem sigR_sigR (K : Type) [Field K] [Algebra F K] (h : ∀ x, σ (σ x) = x) (y : K ⊗[F] E) :
    sigR K σ (sigR K σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (h x)

theorem properSpace_Fv (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (Fv F v) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.tjcosets_finite v

theorem charZero_Fv : CharZero (Fv F v) :=
  ((algebraMap F (Fv F v)).charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

end Main

section Dict

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}


open Formalism.UG (bc UJ cT) in
theorem exists_equiv_UG {L : Type} [Field L] [TopologicalSpace L] (e : (Fv F v ⊗[F] E) ≃+* L) (he : Continuous e)
    (he' : Continuous e.symm) :
    Nonempty (GLoc σ J v ≃ₜ* CompanionTheory.Rg.Fl.UG (e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom))
      ((JR (Fv F v) J).map e)) := by
  set s : L →+* L := e.toRingHom.comp ((sigR (Fv F v) σ).comp e.symm.toRingHom) with hs
  have e1 : ∀ x : GL (Fin n) L, bc e.toRingHom (bc e.symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)
  have e2 : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), bc e.symm.toRingHom (bc e.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)
  have key : ∀ x : GL (Fin n) (Fv F v ⊗[F] E),
      (cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1).map e =
        (((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1) := fun x => by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    exact Matrix.ext fun i j => by simp [cT, hs, bc]
  have mem : ∀ x : GL (Fin n) (Fv F v ⊗[F] E), x ∈ HR (Fv F v) σ J ↔
      bc e.toRingHom x ∈ CompanionTheory.Rg.Fl.UG s ((JR (Fv F v) J).map e) := fun x => by
    change cT (sigR (Fv F v) σ) x.1 * JR (Fv F v) J * x.1 = JR (Fv F v) J ↔
      ((bc e.toRingHom x).1.map s).transpose * (JR (Fv F v) J).map e * (bc e.toRingHom x).1 = (JR (Fv F v) J).map e
    rw [← key]
    exact (Matrix.map_injective e.injective).eq_iff.symm
  have c1 : Continuous (bc (n := Fin n) e.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he
  have c2 : Continuous (bc (n := Fin n) e.symm.toRingHom) := GlobalTheory.LFun.SplitChart.continuous_bc he'
  have hemb := isEmbedding_matHom (Fv F v) σ J
  exact ⟨{ toFun := fun g => ⟨bc e.toRingHom (matHom _ σ J g), (mem _).1 g.2⟩
           invFun := fun u => (⟨bc e.symm.toRingHom u.1, (mem _).2 (by rw [e1]; exact u.2)⟩ : HR (Fv F v) σ J)
           left_inv := fun g => matHom_injective _ σ J (e2 _)
           right_inv := fun u => Subtype.ext (e1 _)
           map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul])
           continuous_toFun := (c1.comp hemb.continuous).subtype_mk _
           continuous_invFun := hemb.continuous_iff.2 (c2.comp continuous_subtype_val) }⟩

end Dict


open GlobalTheory.LFun.InertChart in
theorem stDict : CompanionTheory.Rg.Fl.StDict := by
  intro F E _ _ _ _ _ σ h n J hJ v
  letI nf : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI pf : ProperSpace (Fv F v) := properSpace_Fv v
  haveI uf : IsUltrametricDist (Fv F v) := inferInstance
  haveI cf : CharZero (Fv F v) := charZero_Fv
  by_cases hs : Nonempty (E →ₐ[F] Fv F v)
  · obtain ⟨τ⟩ := hs
    exact ⟨Fv F v, nf, uf, pf, cf, Or.inl ⟨splitEquiv h hJ τ⟩⟩
  · have hf : IsField (Fv F v ⊗[F] E) := isField_tensor_of_no_algHom h.2.2.1 (not_nonempty_iff.1 hs)
    haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    obtain ⟨L, nL, uL, pL, e, he, he', hn⟩ := exists_model (K := Fv F v) (A := Fv F v ⊗[F] E) hf
    have hcc : ∀ x, σ (σ x) = x := conj_conj h
    have hss : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := sigR_sigR _ hcc
    have hi : ∀ x : E, sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := fun _ => rfl
    have hinj : Function.Injective (e.toRingHom.comp (inclR (Fv F v))) := RingHom.injective (e.toRingHom.comp (inclR (Fv F v)))
    have hL : CharZero L :=
      let ϕ : Fv F v →+* L := e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      (ϕ.charZero_iff ϕ.injective).1 cf
    refine ⟨L, nL, uL, pL, hL, Or.inr ⟨_, (JR (Fv F v) J).map e, fun x => ?_, fun x => ?_, ?_, ?_, ?_,
      exists_equiv_UG e he he'⟩⟩
    · simp [hss]
    · have := hn (sigEquiv (Fv F v) hcc) (e.symm x)
      simpa [sigEquiv_apply] using this
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := not_forall.1 (conj_ne h)
      refine ⟨e (inclR (Fv F v) x), fun ee => hx (hinj ?_)⟩
      simpa [hi] using ee
    · refine Matrix.ext fun i j => ?_
      simp [JR, hi, hJ.1 i j]
    · have : ((JR (Fv F v) J).map e).det = (e.toRingHom.comp (inclR (Fv F v))) J.det := by
        rw [RingHom.map_det]; rfl
      rw [this]
      exact (map_ne_zero_iff _ hinj).2 hJ.2

end GlobalTheory.CompanionTheory.DictLoc

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NoOrthogonalIdempotents
section
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

namespace GlobalTheory.CompanionTheory.PrimeRing.StdChain

variable {R : Type} [Ring R]

theorem word_left (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx : ∀ i < m, q i * x i = x i) (n k : ℕ) (hk : k + n = m) :
    q k * (word E ((List.range' k n).map x) * q m) = word E ((List.range' k n).map x) * q m := by
  cases n with
  | zero =>
    obtain rfl : k = m := by omega
    simp [hE k le_rfl, hid]
  | succ n =>
    have hkm : k < m := by omega
    have hEx : E * x k = x k := by
      rw [← hx k hkm, ← mul_assoc, hE k hkm.le]
    rw [List.range'_succ, List.map_cons, word_cons, hEx]
    simp only [← mul_assoc, hx k hkm]

theorem word_cases (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx1 : ∀ i < m, q i * x i = x i) (hx2 : ∀ i < m, x i * q (i + 1) = x i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (l : List ℕ) (hl : ∀ a ∈ l, a < m) :
    word E (l.map x) * q m = 0 ∨ ∃ k, k + l.length = m ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨m, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < m := hl a (by simp)
    have hEx : E * x a = x a := by
      rw [← hx1 a ha, ← mul_assoc, hE a ha.le]
    rw [List.map_cons, word_cons, hEx]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left
      rw [mul_assoc, h, mul_zero]
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        have hw := word_left E m q x hE hid hx1 l.length k hk
        rw [← h] at hw
        calc x a * word E (l.map x) * q m
            = x a * q (a + 1) * (q k * (word E (l.map x) * q m)) := by
              rw [hx2 a ha, hw, mul_assoc]
          _ = x a * (q (a + 1) * q k) * (word E (l.map x) * q m) := by
              simp only [mul_assoc]
          _ = 0 := by
              rw [horth (a + 1) (by omega) k (by omega) hak]
              simp

theorem exists_chain (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (hE : ∀ i ≤ m, E * q i = q i) (n k : ℕ) (hk : k + n = m) :
    ∃ (x : ℕ → R) (y : R), y ≠ 0 ∧ y ∈ A ∧ q k * y = y ∧
      (∀ i, k ≤ i → i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i) ∧
      word E ((List.range' k n).map x) * q m = y := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    exact ⟨0, q k, hne k le_rfl, hA k le_rfl, hid k le_rfl, fun i h1 h2 => absurd h2 (by omega),
      by simp [hE k le_rfl]⟩
  | succ n ih =>
    obtain ⟨x, y, hy0, hyA, hqy, hx, hw⟩ := ih (k + 1) (by omega)
    have hkm : k < m := by omega
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ S, q k * s * y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne k hkm.le (hprime _ (hA k hkm.le) y hyA hy0 hcon)
    have hqs : q k * s ∈ A := hmul _ (hA k hkm.le) _ (hS hs)
    have hxk : q k * s * q (k + 1) ∈ A := hmul _ hqs _ (hA (k + 1) hkm)
    refine ⟨Function.update x k (q k * s * q (k + 1)), q k * s * y, hsy, hmul _ hqs _ hyA, ?_, ?_, ?_⟩
    · simp only [← mul_assoc, hid k hkm.le]
    · intro i h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h3
      · rw [Function.update_self]
        refine ⟨hxk, ?_, ?_⟩
        · simp only [← mul_assoc, hid k hkm.le]
        · rw [mul_assoc _ (q (k + 1)), hid (k + 1) hkm]
      · rw [Function.update_of_ne (by omega)]
        exact hx i (by omega) h2
    · have hmap : (List.range' (k + 1) n).map (Function.update x k (q k * s * q (k + 1))) =
          (List.range' (k + 1) n).map x := by
        apply List.map_congr_left
        intro a ha
        have := List.mem_range'_1.mp ha
        rw [Function.update_of_ne (by omega)]
      have hEq : E * (q k * s * q (k + 1)) = q k * s * q (k + 1) := by
        simp only [← mul_assoc, hE k hkm.le]
      rw [List.range'_succ, List.map_cons, word_cons, hmap, Function.update_self, mul_assoc, hw, hEq,
        mul_assoc _ (q (k + 1)), hqy]

theorem no_chain_nat (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hstd : ∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (hE : ∀ i ≤ m, E * q i = q i) : False := by
  obtain ⟨x, y, hy0, -, -, hx, hw⟩ :=
    exists_chain A S E m q hmul hS hprime hA hne hid hE m 0 (by omega)
  have hx' : ∀ i, i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i :=
    fun i hi => hx i (Nat.zero_le _) hi
  have h0 := hstd (fun i => x i) (fun i => (hx' i i.2).1)
  have hm : ∀ π : Equiv.Perm (Fin m), (List.ofFn fun i => x (π i)) =
      (List.ofFn fun i => (π i : ℕ)).map x := by
    intro π
    rw [List.map_ofFn]
    rfl
  have key : stdPoly E (fun i : Fin m => x i) * q m = y := by
    rw [stdPoly, Finset.sum_mul, Finset.sum_eq_single 1]
    · rw [hm]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
      rw [CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val, hw]
    · intro π _ hπ
      rw [hm, mul_assoc]
      rcases word_cases E m q x hE (hid m le_rfl) (fun i hi => (hx' i hi).2.1)
        (fun i hi => (hx' i hi).2.2) horth (List.ofFn fun i => (π i : ℕ))
        (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
      · rw [h, mul_zero]
      · exfalso
        apply hπ
        rw [List.length_ofFn] at hk h
        obtain rfl : k = 0 := by omega
        rw [← CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val] at h
        ext i
        exact congrFun (List.ofFn_injective h) i
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, zero_mul] at key
  exact hy0 key.symm

theorem no_orthogonal_idempotents : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False := by
  intro R _ A S E m q hmul hS hprime hstd hA hne hid horth hE
  let qq : ℕ → R := fun i => if h : i < m + 1 then q ⟨i, h⟩ else 0
  have hqq : ∀ i (h : i ≤ m), qq i = q ⟨i, Nat.lt_succ_of_le h⟩ := fun i h =>
    dif_pos (Nat.lt_succ_of_le h)
  refine no_chain_nat A S E m qq hmul hS hprime hstd ?_ ?_ ?_ ?_ ?_
  · intro i h
    rw [hqq i h]
    exact hA _
  · intro i h
    rw [hqq i h]
    exact hne _
  · intro i h
    rw [hqq i h]
    exact hid _
  · intro i h k h' hik
    rw [hqq i h, hqq k h']
    exact horth _ _ fun e => hik (congrArg Fin.val e)
  · intro i h
    rw [hqq i h]
    exact hE _

end GlobalTheory.CompanionTheory.PrimeRing.StdChain
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
section
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}

def evalHom (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (u : X) : homIn δ ρ ⊤ →ₗ[ℂ] H where
  toFun T := T.1 u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_evalHom (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) (y : X)
    (T : homIn δ ρ ⊤) : ‖evalHom δ ρ y T‖ = ‖y‖ * ‖evalHom δ ρ u T‖ := by
  change ‖T.1 y‖ = ‖y‖ * ‖T.1 u‖
  rw [norm_apply_eq hδ hρ T.2 y, norm_apply_eq hδ hρ T.2 u, hu, mul_one, mul_comm]

theorem evalHom_injective (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) :
    Function.Injective (evalHom δ ρ u) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h := norm_evalHom hδ hρ hu x T
  rw [hT, norm_zero, mul_zero] at h
  exact norm_eq_zero.1 h

theorem exists_op_unit (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y : X) {u : X} (hu : ‖u‖ = 1) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪u, x⟫_ℂ • T y := by
  have hinj := evalHom_injective hδ hρ hu
  let S : Submodule ℂ H := LinearMap.range (evalHom δ ρ u)
  let e := LinearEquiv.ofInjective (evalHom δ ρ u) hinj
  let L : S →ₗ[ℂ] H := evalHom δ ρ y ∘ₗ e.symm.toLinearMap
  have hL : ∀ v : S, ‖L v‖ ≤ ‖y‖ * ‖v‖ := fun v => by
    have h := norm_evalHom hδ hρ hu y (e.symm v)
    have h2 : evalHom δ ρ u (e.symm v) = v := congrArg Subtype.val (e.apply_symm_apply v)
    rw [h2] at h
    exact h.le
  have hLe : ∀ T : homIn δ ρ ⊤, L ⟨T.1 u, T, rfl⟩ = T.1 y := fun T => by
    have h : e.symm ⟨T.1 u, T, rfl⟩ = T := e.symm_apply_apply T
    change evalHom δ ρ y (e.symm ⟨T.1 u, T, rfl⟩) = T.1 y
    rw [h]
    rfl
  let K : Submodule ℂ H := S.topologicalClosure
  haveI : IsClosed (K : Set H) := S.isClosed_topologicalClosure
  haveI : CompleteSpace K := IsClosed.completeSpace_coe (s := (K : Set H))
  let i : S →ₗᵢ[ℂ] K := ⟨Submodule.inclusion S.le_topologicalClosure, fun _ => rfl⟩
  have hd : DenseRange i.toContinuousLinearMap := by
    refine Topology.IsInducing.subtypeVal.dense_iff.2 fun w => closure_mono (fun z hz => ?_) w.2
    exact ⟨⟨z, S.le_topologicalClosure hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  let B : K →L[ℂ] H := (L.mkContinuous ‖y‖ hL).extend i.toContinuousLinearMap
  have hB : ∀ v : S, B (i v) = L v := fun v =>
    ((L.mkContinuous ‖y‖ hL).extend_eq hd i.isometry.isUniformInducing v)
  refine ⟨B ∘L K.orthogonalProjection, fun T hT x => ?_⟩
  have hmem : ⟪u, x⟫_ℂ • T u ∈ K := K.smul_mem _ (S.le_topologicalClosure ⟨⟨T, hT⟩, rfl⟩)
  have horth : T x - ⟪u, x⟫_ℂ • T u ∈ Kᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro _ ⟨T', rfl⟩
    change ⟪T'.1 u, T x - ⟪u, x⟫_ℂ • T u⟫_ℂ = 0
    rw [inner_sub_right, inner_smul_right, inner_eq_be hδ hρ hT T'.2, inner_eq_be hδ hρ hT T'.2,
      inner_self_eq_norm_sq_to_K, hu]
    simp [mul_comm]
  have hproj : K.orthogonalProjection (T x) = ⟪u, x⟫_ℂ • i ⟨T u, ⟨T, hT⟩, rfl⟩ :=
    Subtype.ext (Submodule.eq_starProjection_of_mem_orthogonal hmem horth)
  change B (K.orthogonalProjection (T x)) = _
  rw [hproj, map_smul, hB, hLe ⟨T, hT⟩]

theorem exists_op (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y ξ : X) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪ξ, x⟫_ℂ • T y := by
  by_cases h0 : ξ = 0
  · exact ⟨0, fun T _ x => by simp [h0]⟩
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn' : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨A, hA⟩ := exists_op_unit hδ hρ y (u := (‖ξ‖ : ℂ)⁻¹ • ξ) (by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn])
  refine ⟨(‖ξ‖ : ℂ) • A, fun T hT x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hA T hT, inner_smul_left, smul_smul, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

theorem stOp : StOp := by
  intro G X H _ _ _ _ _ _ _ δ ρ hδ hρ _
  choose A hA using fun y ξ : X => exists_op (H := H) hδ hρ y ξ
  exact ⟨A, hA⟩

end GlobalTheory.CompanionTheory.RgFl
end
end

