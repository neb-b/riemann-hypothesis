module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
section
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Br.EigenformExistence

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add (f := _)]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  funext n
  simp only [fT_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hc.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hc.dvd_mul_left
  by_cases a : p ∣ n <;> by_cases b : q ∣ n
  · obtain ⟨m, rfl⟩ : p * q ∣ n := hc.mul_dvd_of_dvd_of_dvd a b
    have e1 : p * q * m / p = q * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have e2 : p * q * m / q = p * m := by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
    simp only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · have b' : ¬ q ∣ n / p := fun h => b (h.trans (Nat.div_dvd_of_dvd a))
    simp only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]
    ring
  · have a' : ¬ p ∣ n / q := fun h => a (h.trans (Nat.div_dvd_of_dvd b))
    simp only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · simp only [h1, h2, a, b, if_false, mul_left_comm q p]
    ring

private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    by_cases hn1 : n = 1
    · subst hn1; exact h1
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hlt : m < p * m := by nlinarith [hp.two_le]
    have := congrFun (h ⟨p, hp⟩) m
    have i1 := ih m hlt
    have i2 := ih (m / p) ((Nat.div_le_self _ _).trans_lt hlt)
    simp only [Pi.zero_apply] at i1 i2
    simpa [fT_apply, i1, i2] using this

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

section
open Module
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

end

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

private theorem fT_Phi (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p e (Phi N k g) n = coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0) := by
  have h1 : p * n ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
  rw [fT_apply, Phi_apply, if_neg h1]
  by_cases h : p ∣ n
  · have : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'
    rw [if_pos h, if_pos h, Phi_apply, if_neg this]
  · rw [if_neg h, if_neg h]

private theorem eig_iff (N k : ℕ) (χ : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) (k : ℤ)) {p : ℕ} (hp : p.Prime) (c : ℂ) :
    fT p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (Phi N k g) = c • Phi N k g ↔ IsEigAt k χ g p c := by
  constructor
  · intro h n hn
    have := congrFun h n
    rwa [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul] at this
  · intro h
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]
      exact h n hn

private theorem exists_eigenform (N k : ℕ) [NeZero N] (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (hf : HasChar k χ f) (hf0 : f ≠ 0) (a : ℕ → ℂ) :
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p := by
  haveI := (finDim N k).1
  set V : Submodule ℂ (ℕ → ℂ) := (chSub N k χ).map (Phi N k) with hV
  let e : Nat.Primes → ℂ := fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)
  have hmem : ∀ p : Nat.Primes, ∀ v ∈ V, fT p.1 (e p) v ∈ V := by
    rintro p _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hc⟩ := heckeEx N k hk χ g hg p.1 p.2
    refine ⟨g', hg', ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g p.2 _ hn, Phi_apply, if_neg hn.ne', hc n hn]
  let T : Nat.Primes → Module.End ℂ V := fun p => (fT p.1 (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p.1 (e p) v.1 := fun _ _ => rfl
  have hc : ∀ p q, T p * T q = T q * T p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · ext1 v
      apply Subtype.ext
      simp only [Module.End.mul_apply, hT]
      exact fT_comm p.2 q.2 (fun h => hpq (Subtype.ext h)) _ _ _
  let U : Submodule ℂ V := ⨅ p : {p : Nat.Primes // IsEigAt k χ f p.1 (a p.1)}, Module.End.eigenspace (T p.1) (a p.1.1)
  have hU : ∀ v : V, v ∈ U ↔ ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → T p v = a p.1 • v := fun v => by
    simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Subtype.forall]
  obtain ⟨h, hhU, hne, heig⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl
    ((Submodule.ne_bot_iff U).2 ⟨⟨Phi N k f, f, hf, rfl⟩,
      (hU _).2 fun p hp => Subtype.ext ((eig_iff N k χ f p.2 _).2 hp), fun h0 => hf0 ((finDim N k).2 f fun n hn => by
        have := congrFun (congrArg Subtype.val h0) n
        change Phi N k f n = 0 at this
        rwa [Phi_apply, if_neg (by omega)] at this)⟩)
    (by
      intro q x hx
      rw [hU] at hx ⊢
      intro p hp
      have h2 : T p (T q x) = T q (T p x) := congrArg (fun S : Module.End ℂ V => S x) (hc p q)
      rw [h2, hx p hp, map_smul])
  choose b hb using heig
  have hab : ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → b p = a p.1 := fun p hp =>
    smul_left_injective ℂ hne ((hb p).symm.trans ((hU h).1 hhU p hp))
  obtain ⟨_, g, hg, rfl⟩ := h
  have heig' : ∀ p : Nat.Primes, fT p.1 (e p) (Phi N k g) = b p • Phi N k g :=
    fun p => congrArg Subtype.val (hb p)
  have hg1 : coef g 1 ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    exact eq_zero_of_eig e b _ (by simp [Phi_apply]) (by simp [Phi_apply, h0]) heig'
  have hE : ∀ p : Nat.Primes, IsEigAt k χ g p.1 (b p) := fun p => (eig_iff N k χ g p.2 _).1 (heig' p)
  have hp : ∀ p : Nat.Primes, coef ((coef g 1)⁻¹ • g : CuspForm (Gamma1 N) (k : ℤ)) p.1 = b p := by
    intro p
    have := hE p 1 le_rfl
    rw [if_neg p.2.not_dvd_one, mul_zero, add_zero, mul_one] at this
    rw [coef_smul, this]
    field_simp
  refine ⟨⟨(coef g 1)⁻¹ • g, (chSub N k χ).smul_mem _ hg, ?_, ?_⟩, ?_⟩
  · rw [coef_smul, inv_mul_cancel₀ hg1]
  · intro p hpp n hn
    rw [hp ⟨p, hpp⟩]
    have := hE ⟨p, hpp⟩ n hn
    simp only [coef_smul]
    split_ifs with hd
    · rw [if_pos hd] at this
      linear_combination (coef g 1)⁻¹ * this
    · rw [if_neg hd] at this
      linear_combination (coef g 1)⁻¹ * this
  · intro p hpp h
    exact (hp ⟨p, hpp⟩).trans (hab ⟨p, hpp⟩ h)
end UpperTheory.V.Br.EigenformExistence

theorem UpperTheory.V.Br.eigEx :
    UpperTheory.V.Br.EigEx :=
  fun N k _ hk χ f hf hf0 a => UpperTheory.V.Br.EigenformExistence.exists_eigenform N k hk χ f hf hf0 a

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolCuspFin
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.GlobalFixedVectors UpperTheory.V.Sd

namespace UpperTheory.V.Br.HolomorphicCuspFiniteness

private theorem exists_rep {K ι A : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [Finite ι] (e : ι → K) (r : A → K)
    (χ : A → ℂ) (h : ∀ x, ∃ i a, x = e i * r a) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧
        ∀ f : K → ℂ, Continuous f → (∀ x a, f (x * r a) = χ a * f x) → f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let V : Submodule ℂ (K → ℂ) :=
    { carrier := {f | Continuous f ∧ ∀ x a, f (x * r a) = χ a * f x}
      add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun x a => by simp [hf.2, hg.2, mul_add]⟩
      zero_mem' := ⟨continuous_const, fun x a => by simp⟩
      smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun x a => by simp [hf.2, mul_left_comm]⟩ }
  haveI : FiniteDimensional ℂ V := by
    refine Module.Finite.of_injective ((LinearMap.funLeft ℂ ℂ e).comp V.subtype) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    ext x
    obtain ⟨i, a, rfl⟩ := h x
    have : f.1 (e i) = 0 := congrFun hf i
    rw [f.2.2, this]; simp
  let L : Representation ℂ K V :=
    { toFun := fun k =>
        { toFun := fun f => ⟨fun x => f.1 (k⁻¹ * x), f.2.1.comp (continuous_const.mul continuous_id), fun x a => by
            simp only [← mul_assoc, f.2.2]⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_one' := by ext f x; simp
      map_mul' := fun k k' => by ext f x; simp [mul_assoc] }
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, L.dual, fun l w => ?_, fun f hf hf' => ?_⟩
  · obtain ⟨f, rfl⟩ := (Module.evalEquiv ℂ V).surjective l
    change Continuous fun k => w (L k⁻¹ f)
    refine w.continuous_of_finiteDimensional.comp (Continuous.subtype_mk (continuous_pi fun x => ?_) _)
    exact f.2.1.comp (continuous_inv.inv.mul continuous_const)
  · refine Submodule.subset_span ⟨Module.Dual.eval ℂ V ⟨f, hf, hf'⟩, (LinearMap.proj 1).comp V.subtype, funext fun k => ?_⟩
    change f k = f (k⁻¹⁻¹ * 1)
    simp

variable {F : Type} [Field F] [NumberField F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

private theorem fixed_KLev {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) {M : ℕ} (v : V)
    (ho : IsOpen {k | ρ k v = v}) (h : ∀ w, ∀ k ∈ KLev F 2 M, ρ (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) v = v) :
    ∀ k ∈ KLev F 2 M, ρ k v = v := by
  classical
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ k ∈ KAway 2 M S, ρ k v = v) → ∀ k ∈ KAway 2 M ∅, ρ k v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      refine fun hv => ih fun k hk => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 M (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 := h w k (mem_KAway.1 hk).1
      have h4 := hv _ h2
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := M) (ho.mem_nhds (by simp))
  exact fun k hk => key S (fun k hk => hS hk) k (mem_KAway.2 ⟨hk, by simp⟩)

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private theorem cont (φ : TR.Sm F 2) (g : GA F 2) : Continuous fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g := by
  have e : (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) = fun k : TR.Kinf F 2 => TR.chart φ.1 g (TR.toL k.1) :=
    funext fun k => (TR.chart_val φ.1 g (Unitary.toUnits k)).symm
  rw [e]
  exact (φ.2 g).continuousOn.comp_continuous continuous_subtype_val fun k => TR.val_mem_invSet (Unitary.toUnits k)

end UpperTheory.V.Br.HolomorphicCuspFiniteness

open UpperTheory.V.Br.HolomorphicCuspFiniteness in
theorem UpperTheory.V.Br.holCuspFin : UpperTheory.V.Br.HolCuspFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  have hlev : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ u ∈ KLev F 2 M, TR.finRep F 2 u φ = φ := fun φ hφ =>
    fixed_KLev _ φ hφ.aut.level fun w u hu => hφ.level w _ (local_mem_principal_congruence w _ (hM w) hu)
  refine ⟨⟨M, hM1, hlev⟩, ?_⟩
  obtain ⟨W, _, _, _, ρ, hρ, hf⟩ := exists_rep (eps (F := F)) (rot (F := F))
    (fun θ => Complex.exp (Complex.I * k * ∑ v, (θ v : ℂ))) dec
  haveI := cuspFormsFiniteReal F 2 (KLev F 2 M) (isOpen_KLev hM1) W ρ hρ
    fun _ u => (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
  refine Submodule.finiteDimensional_of_le (S₂ := _) (Submodule.span_mono (fun φ hφ => ?_) : _ ≤ Submodule.span ℂ
    {φ : TR.Sm F 2 | TR.IsCuspForm φ ∧ (∀ k ∈ KLev F 2 M, TR.finRep F 2 k φ = φ) ∧
      (∀ g : GA F 2, (fun k : TR.Kinf F 2 => (TR.cptRep F 2 k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ v u, TR.cap v u φ = ((u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)) • φ})
  have hφ' : IsHol k c ω φ := hφ.1
  refine ⟨hφ.2, hlev φ hφ', fun g => hf _ (cont φ g) fun x θ => ?_, (holCap F k c ω hω φ hφ').2⟩
  have := UpperTheory.V.Br.rotEig F φ _ hφ'.wt θ (Unitary.toUnits (rot θ)) rfl (g * TR.infGL F 2 (Unitary.toUnits x))
  rw [mul_assoc, ← map_mul, ← map_mul] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w (n := 2)) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w (n := 2)) (KGL w (n := 2)) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w (n := 2) := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem UpperTheory.V.Br.uOfSat :
    UpperTheory.V.Br.UOfSat := by
  intro F _ _ w V _ _ ρ x α β ⟨_, hx', _, h⟩
  have hx := GlobalTheory.LGrp.mem_fixed.1 hx'
  constructor
  · have h1 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 1 (by norm_num)
    rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h1]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := by
      simp [normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 2 (by norm_num)
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w (n := 2)) (z : _ ⧸ KGL w (n := 2)), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w (n := 2)) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
end
end

