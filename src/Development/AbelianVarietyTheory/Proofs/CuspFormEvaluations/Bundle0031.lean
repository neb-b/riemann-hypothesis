module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaExistsOfNeOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem betaExists_of_ne_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n bad : ℕ), bad ≠ 1 → BetaExists (Dw := Dw) c n bad :=
  fun E _ _ _ H Dw l c n bad _ => BetaEx.betaExists E H Dw l c n bad

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_natCast_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m, IsIntegral ℤ (((N : K) • P).coeff m) := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral
  | (apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralCoefficients.exists_nat_smul_coeff_isIntegral ..)

theorem smul_mem_HHa {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k] {cc : T → T} {isX : T → Prop}
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (t : k) (hP : P ∈ HHa r n k cc isX a) :
    t • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ t hP.1,
    fun σ i i' h s => by rw [map_smul, hP.2.1 σ i i' h s],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩

theorem exists_natCast_smul_mem_harmA :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ N : ℕ, 0 < N ∧ (N : c.F) • P ∈ harmA c a n ∧ ((N : c.F) • P).support = P.support := by
  intro E _ _ _ H Dw l c a n P hP
  haveI := c.fin
  obtain ⟨N, hN, h⟩ := exists_natCast_smul_coeff_isIntegral (K := c.F) P
  refine ⟨N, hN, ⟨smul_mem_HHa _ hP, fun m => h m⟩, ?_⟩
  have hN' : (N : c.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  ext m
  simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_smul, hN']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetAllComponents
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMulti

theorem component_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (h : P ∈ holSub X la) :
    ∀ k, P k ∈ (X k).SS (la k) := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy =>
    exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem one_le_absDisc (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ dE E := by
  have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  unfold dE
  exact_mod_cast h

end GlobalTheory.NetMulti
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPowMulCoprimeLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pow_mul_coprime_le {R : Type} [CommRing R] [IsDedekindDomain R] (A K : Ideal R) (hK : K ≠ 0) :
    ∃ (j : ℕ) (J : Ideal R), A ^ j * J ≤ K ∧ A ⊔ J = ⊤ := by
  classical
  rw [Ne, Submodule.zero_eq_bot] at hK
  have hne : ({J : Ideal R | ∃ j : ℕ, A ^ j * J ≤ K}).Nonempty := ⟨K, 0, by simp⟩
  obtain ⟨J, ⟨j, hj⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _ hne
  refine ⟨j, J, hj, ?_⟩

  have hKJ : K ≤ J := by
    by_contra h
    refine hmax (J ⊔ K) ⟨j, ?_⟩ (lt_of_le_of_ne le_sup_left ?_)
    · rw [Ideal.mul_sup]
      exact sup_le hj (Ideal.mul_le_inf.trans inf_le_right)
    · intro e
      exact h (le_sup_right.trans e.symm.le)
  have hJ0 : J ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot]
    rintro rfl
    exact hK (le_bot_iff.mp hKJ)

  by_contra hne'
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne'
  have hJP : J ≤ P := le_trans le_sup_right hle
  have hAP : A ≤ P := le_trans le_sup_left hle
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hJP
  have hQmem : A ^ (j + 1) * Q ≤ K :=
    calc A ^ (j + 1) * Q = A ^ j * (A * Q) := by rw [pow_succ, _root_.mul_assoc]
      _ ≤ A ^ j * (P * Q) := Ideal.mul_mono_right (Ideal.mul_mono_left hAP)
      _ = A ^ j * J := by rw [hQ]
      _ ≤ K := hj
  have hJQ : J ≤ Q := by
    rw [hQ]
    exact (Ideal.mul_le_inf.trans inf_le_right)
  have hQJ : Q = J := by
    by_contra h
    exact hmax Q ⟨j + 1, hQmem⟩ (lt_of_le_of_ne hJQ (Ne.symm h))
  rw [hQJ] at hQ

  exact hP.ne_top (mul_right_cancel₀ hJ0 (hQ.symm.trans (Ideal.top_mul J).symm))

private theorem comp_act_eq_one_of_pow_eq_killed {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) :
    ∀ x ∈ Ideal.span {(N : 𝓞 E)} * l.Mb, w ≫ Xo.univ.t.act.act x = 1 := by
  unfold KilledBy at ht
  have h0 : Xo.univ.t.act.act 0 = 1 := by
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    have h' := congrArg (fun f => f * (Xo.univ.t.act.act 0)⁻¹) h
    simpa using h'.symm

  have hnat : ∀ (n : ℕ) (y : 𝓞 E), Xo.univ.t.act.act ((n : 𝓞 E) * y) = Xo.univ.t.act.act y ^ n := by
    intro n y
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, Xo.univ.t.act.add, ih, pow_succ]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm b hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    have := Xo.univ.t.act.hom b
    have := Xo.univ.t.act.hom c
    have e : c * (N : 𝓞 E) * b = (N : 𝓞 E) * b * c := by ring
    rw [e, Xo.univ.t.act.mul, hnat, ← Category.assoc, MonObj.comp_pow, ← MonObj.pow_comp, hw, ht b hb,
      MonObj.one_comp]
  · intro y z hy hz
    rw [Xo.univ.t.act.add, MonObj.comp_mul, hy, hz, _root_.one_mul]

theorem exists_root_killedBy {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {T : Over Xo.X} (t w : T ⟶ Xo.univ.t.G) (N : ℕ)
    (ht : KilledBy Xo l.Mb t) (hw : w ^ N = t) (I J : Ideal (𝓞 E)) (hI : I ≤ l.Mb) (hIJ : I ⊔ J = ⊤)
    (hle : I * J ≤ Ideal.span {(N : 𝓞 E)} * l.Mb) :
    ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo I t' := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp (hIJ ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ J)
  have ht' := ht
  unfold KilledBy at ht'
  refine ⟨w ≫ Xo.univ.t.act.act j, ?_, ?_⟩
  · have := Xo.univ.t.act.hom j
    rw [← MonObj.pow_comp, hw]
    have h1 : t ≫ Xo.univ.t.act.act i = 1 := ht' i (hI hi)
    calc t ≫ Xo.univ.t.act.act j = (t ≫ Xo.univ.t.act.act i) * (t ≫ Xo.univ.t.act.act j) := by
          rw [h1, _root_.one_mul]
      _ = t ≫ Xo.univ.t.act.act (i + j) := by rw [Xo.univ.t.act.add, MonObj.comp_mul]
      _ = t := by rw [hij, Xo.univ.t.act.one, Category.comp_id]
  · unfold KilledBy
    intro a ha
    rw [Category.assoc, ← Xo.univ.t.act.mul]
    exact comp_act_eq_one_of_pow_eq_killed Xo t w N ht hw _ (hle (_root_.mul_comm a j ▸ Ideal.mul_mem_mul ha hj))

theorem exists_root_killedBy_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Over Xo.X) (t w : T ⟶ Xo.univ.t.G) (N : ℕ), 0 < N → KilledBy Xo l.Mb t → w ^ N = t → (∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) t') ∧ (N = l.M → ∃ t' : T ⟶ Xo.univ.t.G, t' ^ N = t ∧ KilledBy Xo (l.Mb ^ 2) t') := by
  intro E _ _ _ H Dw l Xo T t w N hN ht hw
  have hMb0 : l.Mb ≠ 0 := by
    intro h
    have hp := l.prod
    rw [h, zero_mul, Submodule.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hp
    have hM : l.M = 0 := by exact_mod_cast hp
    have := l.three_le
    omega
  have hN0 : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  obtain ⟨j, J, hj, hcop⟩ := exists_pow_mul_coprime_le l.Mb _ (mul_ne_zero hN0 hMb0)
  refine ⟨?_, ?_⟩
  · obtain ⟨t', ht'N, ht'⟩ := exists_root_killedBy Xo t w N ht hw (l.Mb ^ (j + 1)) J
      (Ideal.pow_le_self (Nat.succ_ne_zero j)) (Ideal.pow_sup_eq_top hcop)
      (by rw [pow_succ', _root_.mul_assoc]; exact (Ideal.mul_le_inf.trans inf_le_right).trans hj)
    exact ⟨t', ht'N, j + 1, ht'⟩
  · intro hNM
    refine exists_root_killedBy Xo t w N ht hw (l.Mb ^ 2) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
      (Ideal.pow_le_self two_ne_zero) (Ideal.pow_sup_eq_top l.coprime) (le_of_eq ?_)
    rw [sq, _root_.mul_assoc, l.prod, _root_.mul_comm, hNM]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsUniqueIsTwistPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_isTwistPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T : Over S) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])), α.IsGen → ∀ s : LB.Sec (LPow A L b T), ∃! s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  intro S A _ L hL T ψ m hm a b α hα s
  obtain ⟨s₀, hs₀⟩ := ThetaPtExist.exists_isTwistPull hL ψ m hm a b α hα s
  refine ⟨s₀, hs₀, fun s₁ hs₁ => ?_⟩

  have hf : ∀ j, s₁.f j = s₀.f j :=
    sec_ext_val (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) hL
      (fun y J hJ => (twist_val hs₁ (𝟙 _) y hJ).trans (twist_val hs₀ (𝟙 _) y hJ).symm)

  obtain ⟨f₁, c₁⟩ := s₁
  obtain ⟨f₀, c₀⟩ := s₀
  obtain rfl : f₁ = f₀ := funext hf
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_faithfullyFlat_pushout (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁]
    [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁)
    (φ₂ : S →ₐ[F] S₂) (h : φ₂.toRingHom.FaithfullyFlat) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T),
      ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁ := by
  letI : Algebra S S₁ := φ₁.toRingHom.toAlgebra
  letI : Algebra S S₂ := φ₂.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S₂ := RingHom.faithfullyFlat_algebraMap_iff.1 h
  letI : Algebra F (S₁ ⊗[S] S₂) :=
    ((Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂).comp
      (algebraMap F S₁)).toAlgebra
  have hff : (algebraMap S₁ (S₁ ⊗[S] S₂)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  refine ⟨S₁ ⊗[S] S₂, inferInstance, inferInstance,
    { (Algebra.TensorProduct.includeLeftRingHom : S₁ →+* S₁ ⊗[S] S₂) with commutes' := fun c => rfl },
    { (Algebra.TensorProduct.includeRight : S₂ →ₐ[S] S₁ ⊗[S] S₂).toRingHom with
      commutes' := fun c => ?_ }, ?_, hff, hff.injective⟩
  · show (1 : S₁) ⊗ₜ[S] algebraMap F S₂ c = algebraMap F S₁ c ⊗ₜ[S] (1 : S₂)
    rw [← φ₁.commutes, ← φ₂.commutes]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm
  · exact AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped TensorProduct in
theorem _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat (F S S' : Type) [Field F] [CommRing S]
    [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S')
    (h : φ.toRingHom.FaithfullyFlat) (w : S')
    (hw : ∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T),
      ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) : ∃! v : S, φ v = w := by
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := RingHom.faithfullyFlat_algebraMap_iff.1 h
  have hinj := h.injective
  letI : Algebra F (S' ⊗[S] S') :=
    ((Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S').comp
      (algebraMap F S')).toAlgebra
  let ψ₁ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S') with commutes' := fun c => rfl }
  let ψ₂ : S' →ₐ[F] S' ⊗[S] S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom with
      commutes' := fun c => by
        show (1 : S') ⊗ₜ[S] algebraMap F S' c = algebraMap F S' c ⊗ₜ[S] (1 : S')
        rw [← φ.commutes]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap F S c)).symm }
  have hcomp : ψ₁.comp φ = ψ₂.comp φ :=
    AlgHom.ext fun s => Algebra.TensorProduct.tmul_one_eq_one_tmul s
  have hw' : w ⊗ₜ[S] (1 : S') = (1 : S') ⊗ₜ[S] w := hw (S' ⊗[S] S') ψ₁ ψ₂ hcomp
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' w).1
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact hw')
  exact ⟨v, hv, fun v' hv' => hinj (hv'.trans hv.symm)⟩


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.faithfullyFlat_points_baseChange_descent : (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B), φ.Flat → (∀ (K : Type) [Field K] [IsAlgClosed K] (ψ : S →+* K), ∃ χ : B →+* K, χ.comp φ = ψ) → φ.FaithfullyFlat) ∧ (∀ (S B : Type) [CommRing S] [CommRing B] (φ : S →+* B) (e : B), φ.Flat → ((algebraMap B (Localization.Away e)).comp φ).Flat) ∧ (∀ (F S S₁ S₂ : Type) [Field F] [CommRing S] [CommRing S₁] [CommRing S₂] [Algebra F S] [Algebra F S₁] [Algebra F S₂] (φ₁ : S →ₐ[F] S₁) (φ₂ : S →ₐ[F] S₂), φ₂.toRingHom.FaithfullyFlat → ∃ (T : Type) (_ : CommRing T) (_ : Algebra F T) (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T), ψ₁.comp φ₁ = ψ₂.comp φ₂ ∧ ψ₁.toRingHom.FaithfullyFlat ∧ Function.Injective ψ₁) ∧ ∀ (F S S' : Type) [Field F] [CommRing S] [CommRing S'] [Algebra F S] [Algebra F S'] (φ : S →ₐ[F] S'), φ.toRingHom.FaithfullyFlat → ∀ w : S', (∀ (T : Type) [CommRing T] [Algebra F T] (ψ₁ ψ₂ : S' →ₐ[F] T), ψ₁.comp φ = ψ₂.comp φ → ψ₁ w = ψ₂ w) → ∃! v : S, φ v = w := by
  refine ⟨fun S B _ _ φ hflat hpt => ?_, fun S B _ _ φ e hflat => ?_,
    fun F S S₁ S₂ _ _ _ _ _ _ _ φ₁ φ₂ h => _root_.GlobalTheory.exists_faithfullyFlat_pushout F S S₁ S₂ φ₁ φ₂ h,
    fun F S S' _ _ _ _ _ φ h w hw => _root_.GlobalTheory.existsUnique_preimage_of_faithfullyFlat F S S' φ h w hw⟩
  · rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨hflat, fun p => ?_⟩
    obtain ⟨χ, hχ⟩ := hpt (AlgebraicClosure p.asIdeal.ResidueField)
      ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
        (algebraMap S p.asIdeal.ResidueField))
    refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext ?_⟩
    show Ideal.comap φ (RingHom.ker χ) = p.asIdeal
    rw [RingHom.comap_ker, hχ, RingHom.ker_comp_of_injective _
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).injective,
      Ideal.ker_algebraMap_residueField]
  · exact RingHom.Flat.comp hflat (RingHom.flat_algebraMap_iff.2 inferInstance)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZhStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ)

theorem act_natCast (m : ℕ) : Xo.univ.t.act.act m = 𝟙 Xo.univ.t.G ^ m := by
  induction m with
  | zero =>
    have h := Xo.univ.t.act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, Xo.univ.t.act.add, ih, Xo.univ.t.act.one, pow_succ]

theorem comp_list_prod {T T' : Over Xo.X} (h : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map fun x => h ≫ x).prod = h ≫ L.prod := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.prod_nil, MonObj.comp_one]
  | cons x L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem inZh_comp {T T' : Over Xo.X} (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) :
    InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := comp_list_prod Xo h (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j))
    rw [ha.2 mu hmu cm hcm i, MonObj.comp_one, List.map_ofFn] at h1
    simpa only [Function.comp_def, Category.assoc] using h1

theorem inZh_mul {T : Over Xo.X} (a a' : Fin n → (T ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a)
    (ha' : InZh Xo Λ N a') : InZh Xo Λ N (fun b => a b * a' b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [mul_pow, ha.1 b, ha'.1 b, _root_.mul_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have h2 := ha'.2 mu hmu cm hcm i
    rw [List.prod_ofFn] at h1 h2 ⊢
    have h3 : ∀ j, (a j * a' j) ≫ Xo.univ.t.act.act (cm i j) =
        (a j ≫ Xo.univ.t.act.act (cm i j)) * (a' j ≫ Xo.univ.t.act.act (cm i j)) := fun j => by
      have := Xo.univ.t.act.hom (cm i j)
      exact MonObj.mul_comp _ _ _
    simp only [h3]
    rw [Finset.prod_mul_distrib, h1, h2, _root_.mul_one]

theorem geoInj_comp {S T : Type} [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X)
    (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ) {J : Type}
    (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hz : GeoInj Xo x0 z) :
    GeoInj Xo x1 (fun i b => h ≫ z i b) := by
  intro k _ χ g hg i j hij
  let g' : ptO Xo (spMap (χ.comp ψ) ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap (χ.comp ψ)) rfl
  have hc : spMap (χ.comp ψ) = g.left ≫ h.left := by
    rw [hg, hh]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine hz k (χ.comp ψ) g' rfl (funext fun b => Over.OverMorphism.ext ?_)
  have h1 := congrArg (fun f => f.left) (congrFun hij b)
  change spMap (χ.comp ψ) ≫ (z i b).left = spMap (χ.comp ψ) ≫ (z j b).left
  rw [hc]
  simpa only [Over.comp_left, Category.assoc] using h1

theorem inZh_of_killedBy (hΛ : Λ.TrivAt l.M) {T : Over Xo.X} (u : Fin n → (T ⟶ Xo.univ.t.G))
    (hu : ∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) : InZh Xo Λ N u := by
  classical
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [pow_two, pow_mul, (hu b).1, one_pow]
  · obtain ⟨k, hk, -, hk2⟩ := hΛ
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨hN, e, he⟩ := hu j
    have hv : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.La := by
      refine hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) ?_)
      intro b _
      by_cases hb : b = j
      · subst hb; rw [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
      · rw [Pi.single_eq_of_ne hb]; exact Submodule.zero_mem _
    obtain ⟨m, hm⟩ := Submodule.mem_one.1 (hmu _ hv i (Set.mem_univ i))
    have hm' : (m : E) = (k : E) * mu i j := by
      have : (k : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = (k : E) • (Pi.single j (1 : E) : Fin n → E) := by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [this, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hm
      exact hm
    have hcmk : cm i j * k = N * m := by
      apply RingOfIntegers.ext
      have h1 : ((cm i j * k : 𝓞 E) : E) = (cm i j : E) * (k : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      have h2 : ((N * m : 𝓞 E) : E) = (N : E) * (m : E) := by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast]
      rw [h1, h2, hcm, hm']; ring
    have hM : (l.M : 𝓞 E) ∈ l.Mb := by
      have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
        rw [l.prod]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf h1).1
    have hcop : IsCoprime (k : 𝓞 E) ((l.M : 𝓞 E) ^ e) := (Nat.Coprime.cast hk).pow_right
    obtain ⟨p, q, hpq⟩ := hcop
    have hsplit : cm i j = N * (m * p) + (cm i j * q) * (l.M : 𝓞 E) ^ e := by
      linear_combination (-cm i j) * hpq + p * hcmk
    have := Xo.univ.t.act.hom (m * p)
    show u j ≫ Xo.univ.t.act.act (cm i j) = 1
    rw [hsplit, Xo.univ.t.act.add, MonObj.comp_mul,
      he _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hM e)), _root_.mul_one, Xo.univ.t.act.mul,
      ← Category.assoc, act_natCast, MonObj.comp_pow, Category.comp_id, hN, MonObj.one_comp]

end GlobalTheory.ZhStable

namespace GlobalTheory

theorem inZh_geoInj_stable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) :=
  fun _ _ _ _ _ _ _ Xo _ Λ N =>
    ⟨fun _ _ h a => ZhStable.inZh_comp Xo Λ N h a, fun _ a a' => ZhStable.inZh_mul Xo Λ N a a',
      fun _ _ _ _ x0 x1 ψ h hh _ z => ZhStable.geoInj_comp Xo x0 x1 ψ h hh z,
      fun hΛ _ u => ZhStable.inZh_of_killedBy Xo Λ N hΛ u⟩

end GlobalTheory
end

