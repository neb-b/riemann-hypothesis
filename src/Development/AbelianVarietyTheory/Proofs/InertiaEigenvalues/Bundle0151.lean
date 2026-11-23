module

public import Mathlib
public import Formalism.CharacterColumnKernels.StatementRho
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLe
section
open Formalism.NG

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_self_eq_top : Module.length O O = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  obtain ⟨_, h2⟩ := h
  haveI : IsArtinianRing O := h2
  exact IsDiscreteValuationRing.not_a_field O
    (IsLocalRing.isField_iff_maximalIdeal_eq.1 (IsArtinianRing.isField_of_isDomain O))

theorem length_ker_smul_le (x : O) :
    Module.length O (LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O)) ≤
      Module.length O (O ⧸ Ideal.span {x}) := by
  by_cases hx : x = 0
  · subst hx
    have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O :=
      Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq, length_self_eq_top]
    exact le_top
  set K := FractionRing O
  have hxK : algebraMap O K x ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hx
  set c : K := (algebraMap O K x)⁻¹ with hc
  let g0 : O →ₗ[O] KO O := (Submodule.mkQ (1 : Submodule O K)) ∘ₗ LinearMap.toSpanSingleton O K c
  have hg0 : ∀ y, g0 y ∈ LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := by
    intro y
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, g0,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨y, ?_⟩
    rw [smul_smul, Algebra.smul_def, hc, map_mul, mul_right_comm, mul_inv_cancel₀ hxK, one_mul]
  let g : O →ₗ[O] LinearMap.ker (x • LinearMap.id : KO O →ₗ[O] KO O) := g0.codRestrict _ hg0
  have hgs : Function.Surjective g := by
    rintro ⟨t, ht⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at ht
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, ?_⟩
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    congr 1
    rw [Algebra.smul_def, hy, Algebra.smul_def, hc, mul_comm _ z, mul_assoc, mul_inv_cancel₀ hxK,
      mul_one]
  have hker : Ideal.span {x} ≤ LinearMap.ker g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    apply Subtype.ext
    simp only [g, g0, LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨1, ?_⟩
    rw [Algebra.smul_def, hc, mul_inv_cancel₀ hxK, map_one]
  have hqs : Function.Surjective ((Ideal.span {x}).liftQ g hker) := by
    intro t
    obtain ⟨y, rfl⟩ := hgs t
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  exact Module.length_le_of_surjective _ hqs

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem evalGen_injective {A M : Type} [AddCommGroup A] [AddCommGroup M] (a : A) :
    Function.Injective (fun f : (AddSubgroup.zmultiples a) →+ M =>
      f ⟨a, AddSubgroup.mem_zmultiples a⟩) := by
  intro f g hfg
  ext ⟨b, hb⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
  have : (⟨k • a, hb⟩ : AddSubgroup.zmultiples a) = k • ⟨a, AddSubgroup.mem_zmultiples a⟩ := rfl
  simp only at hfg
  rw [this, map_zsmul, map_zsmul, hfg]

def evalGen {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (a : A) :
    ((AddSubgroup.zmultiples a) →+ M) →ₗ[O] M where
  toFun f := f ⟨a, AddSubgroup.mem_zmultiples a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem length_cyclic_le (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) {A : Type} [AddCommGroup A] (a : A) (p : ℕ)
    [Fact p.Prime] (ha : addOrderOf a = p) :
    Module.length O ((AddSubgroup.zmultiples a) →+ M) ≤
      if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0 := by
  have hkill : ∀ f : (AddSubgroup.zmultiples a) →+ M, p • f ⟨a, AddSubgroup.mem_zmultiples a⟩ = 0 := by
    intro f
    rw [← map_nsmul]
    have : p • (⟨a, AddSubgroup.mem_zmultiples a⟩ : AddSubgroup.zmultiples a) = 0 := by
      apply Subtype.ext
      simp [← ha, addOrderOf_nsmul_eq_zero]
    rw [this, map_zero]
  split_ifs with hpl
  · subst hpl
    let T := LinearMap.ker ((p : O) • LinearMap.id : KO O →ₗ[O] KO O)
    have hT : ∀ f, (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a) f ∈ T := by
      intro f
      simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.coe_coe, evalGen, LinearMap.coe_mk, AddHom.coe_mk]
      rw [← map_smul, Nat.cast_smul_eq_nsmul, hkill, map_zero]
    let v := (eM.toLinearMap ∘ₗ evalGen (O := O) (M := M) a).codRestrict T hT
    have hv : Function.Injective v := by
      intro f g hfg
      apply evalGen_injective a
      have := congrArg Subtype.val hfg
      simpa [v, evalGen] using this
    exact (Module.length_le_of_injective v hv).trans (length_ker_smul_le _)
  · have hunit : IsUnit (p : O) := by
      have h1 : IsUnit (p : ℤ_[l]) := by
        rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes (Fact.out) (Fact.out)).2 (Ne.symm hpl)
      simpa using h1.map (algebraMap ℤ_[l] O)
    haveI : Subsingleton ((AddSubgroup.zmultiples a) →+ M) := by
      constructor
      intro f g
      apply evalGen_injective a
      simp only
      have hf := hkill f
      have hg := hkill g
      rw [← Nat.cast_smul_eq_nsmul O] at hf hg
      rw [hunit.smul_eq_zero.1 hf, hunit.smul_eq_zero.1 hg]
    rw [Module.length_eq_zero]

end GlobalTheory.HomLen

namespace GlobalTheory.HomLen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def restr {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A →+ M) →ₗ[O] (B →+ M) where
  toFun f := f.comp B.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pull {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M] (B : AddSubgroup A) :
    (A ⧸ B →+ M) →ₗ[O] (A →+ M) where
  toFun g := g.comp (QuotientAddGroup.mk' B)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem length_le_add {A M : Type} [AddCommGroup A] [AddCommGroup M] [Module O M]
    (B : AddSubgroup A) :
    Module.length O (A →+ M) ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := by
  have hpull : Function.Injective (pull (O := O) (M := M) B) := by
    intro g h hgh
    ext x
    exact DFunLike.congr_fun hgh x
  have hex : Function.Exact (pull (O := O) (M := M) B) (restr (O := O) (M := M) B).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    ext f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hle : B ≤ f.ker := by
        intro b hb
        have := DFunLike.congr_fun hf ⟨b, hb⟩
        simpa [restr] using this
      exact ⟨QuotientAddGroup.lift B f hle, by ext x; rfl⟩
    · rintro ⟨g, rfl⟩
      ext b
      show g (QuotientAddGroup.mk (b : A)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 b.2, map_zero]
  rw [Module.length_eq_add_of_exact _ _ hpull (restr B).surjective_rangeRestrict hex]
  gcongr
  exact Module.length_le_of_injective (LinearMap.range (restr (O := O) (M := M) B)).subtype
    (Submodule.subtype_injective _)

theorem length_addMonoidHom_le_of_card_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] {M : Type} [AddCommGroup M]
    [Module O M] (eM : M ≃ₗ[O] KO O) (n : ℕ) :
    ∀ (A : Type) [AddCommGroup A] [Finite A], Nat.card A = n →
      Module.length O (A →+ M) ≤
        Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ hn
  by_cases h1 : n = 1
  · haveI : Subsingleton A := by
      exact (Nat.card_eq_one_iff_unique.1 (hn.trans h1)).1
    haveI : Subsingleton (A →+ M) :=
      ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    rw [Module.length_eq_zero]
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  haveI := Fact.mk hp
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := A) p (hn ▸ hpn)
  set B := AddSubgroup.zmultiples a
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B
  rw [Nat.card_zmultiples, ha, hn] at hcard
  have hn0 : n ≠ 0 := by rw [← hn]; exact Nat.card_pos.ne'
  have hq0 : Nat.card (A ⧸ B) ≠ 0 := by
    rintro h; rw [h, zero_mul] at hcard; exact hn0 hcard
  have hlt : Nat.card (A ⧸ B) < n := by
    rw [hcard]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hq0) hp.one_lt
  have ihq := ih _ hlt (A ⧸ B) rfl
  have hB := length_cyclic_le l eM a p ha
  have hv : padicValNat l n = padicValNat l (Nat.card (A ⧸ B)) + (if p = l then 1 else 0) := by
    rw [hcard, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hq0 hp.ne_zero]
    congr 1
    split_ifs with h
    · subst h; simpa only [Nat.padicValNat_def] using (Nat.Prime.multiplicity_self (p := p))
    · simpa only [Nat.padicValNat_def] using (multiplicity_primes (p := l) (q := p) (Ne.symm h))
  calc Module.length O (A →+ M)
      ≤ Module.length O (A ⧸ B →+ M) + Module.length O (B →+ M) := length_le_add B
    _ ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card (A ⧸ B)) : ℕ∞) +
          (if p = l then Module.length O (O ⧸ Ideal.span {(l : O)}) else 0) := add_le_add ihq hB
    _ = Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l n : ℕ∞) := by
      rw [hv]
      split_ifs <;> simp [mul_add]

theorem length_addMonoidHom_le : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] KO O)
    (A : Type) [AddCommGroup A] [Finite A],
    Module.length O (A →+ M) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card A) : ℕ∞) := by
  intro l _ O _ _ _ _ M _ _ eM A _ _
  exact length_addMonoidHom_le_of_card_eq l eM _ A rfl

end GlobalTheory.HomLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaar
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_smul_vec [hU : Unram F E] {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]

def trForm [Unram F E] (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp only [star_add, add_dotProduct, map_add (f := _)])
    (fun a c b => by simp only [star_smul_vec, smul_dotProduct, map_smul])
    (fun c b b' => by simp only [dotProduct_add, map_add (f := _)])
    (fun a c b => by simp only [dotProduct_smul, map_smul])

theorem trForm_apply [Unram F E] {r : ℕ} (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trace_star [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z

theorem trForm_symm [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]

theorem trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1

theorem trForm_nondeg [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by
  refine ⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩
  rw [(trForm_symm r).eq]; exact h c

theorem kerL_eq [hU : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)}
    (hx : A.IsIsom x j) (y' y : A.L) :
    A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  obtain ⟨b⟩ := (GlobalTheory.JR.Et.quadratic_structure F E A).1
  haveI : Module.Free A.K A.L := Module.Free.of_basis b
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L
  unfold Et.kerL Et.psiK
  rw [hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]
  congr 2
  rw [show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul,
    smul_eq_mul]

end GlobalTheory.JR.MeasTransport

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem addChar_sum (ψ : AddChar F ℂ) {ι : Type} (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem pi_selfDual [hU : Unram F E] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) (M : Meas r F E) :
    letI := M.mE
    SelfDual (Measure.pi fun _ : Fin r => M.μE) (fun a b => ψ (trForm (F := F) r a b)) := by
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  let O : AddSubgroup (Fin r → E) :=
    { carrier := {v | ∀ i, ‖v i‖ ≤ 1}
      zero_mem' := by intro i; simp
      add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1 := fun v => Iff.rfl
  have hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1 := by
    ext v; simp [O, Set.mem_pi]
  have hOo : IsOpen (O : Set (Fin r → E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hOk : IsCompact (O : Set (Fin r → E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc := ((_root_.GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).2.2.2
  have hdual : {y | ∀ x ∈ O, ψ (trForm (F := F) r x y) = 1} = (O : Set (Fin r → E)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]
    constructor
    · intro h i
      refine (hc (y i)).1 fun e he => ?_
      have h1 := h (Pi.single i (star e)) (by
        intro k
        by_cases hk : k = i
        · subst hk; simp [hU.norm_star, he]
        · simp [hk])
      rw [trForm_apply] at h1
      simpa [dotProduct, Pi.single_apply, apply_ite star] using h1
    · intro h x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [trForm_apply, dotProduct, map_sum, addChar_sum]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [Pi.star_apply]
      exact (hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)
  have hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1 := by
    rw [hOset, Measure.pi_pi]; simp [M.volE]
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := (_root_.GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O
    hOo hOk |>.1
  rw [key, hdual, hvol, one_mul]

theorem map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]

theorem map_isIsom_eq_pi : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm

end GlobalTheory.JR.MeasTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableSubmoduleMeetsCharacterTypeVectors
section
open GlobalTheory.MeetsGen

noncomputable section
namespace GlobalTheory.MeetsTypeVec

theorem lift_apply_mem {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (W : Submodule K V) (hW : ∀ g x, x ∈ W → φ g x ∈ W)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ W) :
    MonoidAlgebra.lift K (Module.End K V) G φ a x ∈ W := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => by
    rw [LinearMap.smul_apply]; exact W.smul_mem _ (hW g x hx)

theorem proj_eigen {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (φ : G →* Module.End K V) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (y : V) (u' : U) :
    φ u' (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y)
      = ((ψ u' : Kˣ) : K) • MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K))) y := by
  have hφ : ∀ u : U, φ u' (φ u y) = φ ((u' * u : U) : G) y := by
    intro u; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pU, map_sum, MonoidAlgebra.lift_single, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    Finset.smul_sum, hφ]
  refine Fintype.sum_equiv (Equiv.mulLeft u') _ _ fun u => ?_
  simp only [Equiv.coe_mulLeft, smul_smul]
  congr 1
  simp only [map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : ((ψ u' : Kˣ) : K) ≠ 0 := Units.ne_zero _
  field_simp

theorem meets : ∀ {K G V : Type} [Field K] [Group G] [Fintype G] [AddCommGroup V] [Module K V] (ρ : G →* (V ≃ₗ[K] V)) (U : Subgroup G) [Fintype U] (ψ : U →* Kˣ) (e : MonoidAlgebra K G) (b : G → MonoidAlgebra K G), e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)) * b g → ∀ (W : Submodule K V), W ≠ ⊥ → (∀ g x, x ∈ W → ρ g x ∈ W) → (∀ x ∈ W, MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) e x = x) → W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) ≠ ⊥ := by
  intro K G V _ _ _ _ _ ρ U _ ψ e b he W hW0 hWs hWe
  set φ : G →* Module.End K V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ with hφdef
  have hφ : ∀ g x, φ g x = ρ g x := fun _ _ => rfl
  have hWs' : ∀ g x, x ∈ W → φ g x ∈ W := fun g x hx => by rw [hφ]; exact hWs g x hx
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hsum : x = ∑ g : G, φ g (MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x)) := by
    conv_lhs => rw [← hWe x hxW, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MonoidAlgebra.lift_single, one_smul, LinearMap.sum_apply, Module.End.mul_apply]
  intro hbot
  apply hx0
  rw [hsum]
  refine Finset.sum_eq_zero fun g _ => ?_
  have hmem : MonoidAlgebra.lift K (Module.End K V) G φ (pU U (fun u => (((ψ u)⁻¹ : Kˣ) : K)))
      (MonoidAlgebra.lift K (Module.End K V) G φ (b g) x) ∈
      W ⊓ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - (((ψ u : Kˣ) : K)) • LinearMap.id)) := by
    refine ⟨lift_apply_mem φ W hWs' _ (lift_apply_mem φ W hWs' _ hxW), ?_⟩
    refine Submodule.mem_iInf _ |>.2 fun u => LinearMap.mem_ker.2 ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ← hφ, proj_eigen,
      sub_self]
  rw [hbot] at hmem
  rw [(Submodule.mem_bot K).1 hmem, map_zero]

end GlobalTheory.MeetsTypeVec
end
end

