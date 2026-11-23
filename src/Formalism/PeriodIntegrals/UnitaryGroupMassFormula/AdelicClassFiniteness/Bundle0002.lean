module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictGen
section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

namespace DictGen

variable (I : AutInst)

theorem lf_eq : I.Lf = Submodule.span (IntAf I.F I.E)
    (Set.range fun x : I.L => iv I (x : Fin I.n → I.E)) := rfl

theorem iv_mem {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := by
  rw [lf_eq]
  exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem natSmul_mem (k : ℕ) {w : Fin I.n → I.E ⊗[I.F] Af I.F} (hw : w ∈ I.Lf) :
    (k : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  first
    | rw [Nat.cast_smul_eq_nsmul (I.E ⊗[I.F] Af I.F)]
      exact nsmul_mem hw k
    | rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hw k
    | exact I.Lf.smul_mem (k : IntAf I.F I.E) hw

theorem iv_nsmul (N : ℕ) (v : Fin I.n → I.E) :
    iv I (N • v) = (N : I.E ⊗[I.F] Af I.F) • iv I v := by
  funext i
  first
    | simp [iv, nsmul_eq_mul]
    | simp only [iv, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul]

theorem natCast_cancel (N : ℕ) (hN : 0 < N) {a b : Fin I.n → I.E ⊗[I.F] Af I.F}
    (h : (N : I.E ⊗[I.F] Af I.F) • a = (N : I.E ⊗[I.F] Af I.F) • b) : a = b := by
  have hu : IsUnit (N : (I.E ⊗[I.F] Af I.F)) := by
    have h0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := (IsUnit.mk0 _ h0).map (algebraMap I.F (I.E ⊗[I.F] Af I.F))
    rwa [map_natCast] at h1
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact hu.mul_left_cancel hi

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  first
    | exact Units.mul_inv (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  first
    | exact Units.inv_mul (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

def lamM (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | M *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show M *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show M *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show M *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv

theorem mulVec_mem_of_le {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (h : I.L ≤ lamM I M) :
    ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  rw [lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    exact (show M *ᵥ iv I l ∈ I.Lf from h hl)
  | zero =>
    rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact I.Lf.add_mem ha hb
  | smul s a _ ha =>
    have e : M *ᵥ (s • a) = s • (M *ᵥ a) := by
      show M *ᵥ ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • (M *ᵥ a)
      exact Matrix.mulVec_smul M _ a
    rw [e]
    exact I.Lf.smul_mem s ha

private theorem smul_mulVec_lemma {A : Type} [CommRing A] {n : ℕ} (c : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) : (c • M) *ᵥ y = c • (M *ᵥ y) := by
  first
    | exact Matrix.smul_mulVec c M y
    | exact Matrix.smul_mulVec_assoc c M y
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

theorem denom (hD : LDenom) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (M *ᵥ y) ∈ I.Lf := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hm using fun v : Fin I.n → I.E => hD I (M *ᵥ iv I v)
  refine ⟨∏ j ∈ s, m j, Finset.prod_pos fun j _ => hm0 j, ?_⟩
  have hle : I.L ≤ lamM I (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    show (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) *ᵥ iv I v ∈ I.Lf
    rw [smul_mulVec_lemma, ← Finset.prod_erase_mul s m hv, Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hm v)
  intro y hy
  have h2 := mulVec_mem_of_le I hle y hy
  rwa [smul_mulVec_lemma] at h2

theorem exists_denominator_fmat (hD : LDenom) (x : I.Gf) : ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf,
    (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf := by
  obtain ⟨N1, h1, hN1⟩ := denom I hD (I.fmat x)
  obtain ⟨N2, h2, hN2⟩ := denom I hD (I.fmat x⁻¹)
  refine ⟨N1 * N2, Nat.mul_pos h1 h2, fun y hy => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact natSmul_mem I _ (hN1 y hy)
  · rw [Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hN2 y hy)

theorem nL_sub (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {l : Fin I.n → I.E} (hl : l ∈ I.L) : N • l ∈ abelian₂ I x := by
  show I.fmat x⁻¹ *ᵥ iv I (N • l) ∈ I.Lf
  rw [iv_nsmul, Matrix.mulVec_smul]
  exact (hN _ (iv_mem I hl)).2

theorem nLam_sub (hInt : LInter) (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {v : Fin I.n → I.E} (hv : v ∈ abelian₂ I x) : N • v ∈ I.L := by
  apply hInt I
  have hv' : I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf := hv
  have e : iv I v = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ iv I v) := by
    rw [Matrix.mulVec_mulVec, fmat_mul_inv, Matrix.one_mulVec]
  rw [iv_nsmul, e]
  exact (hN _ hv').1

end DictGen

theorem mLat_of (hInt : LInter) (hD : LDenom) : MLat := by
  intro I x
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · let ψ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
      (((N : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
    have hle : abelian₂ I x ≤ I.L.map ψ := by
      intro v hv
      have h1 : N • v ∈ I.L := DictGen.nLam_sub I hInt x N hN' hv
      have e : ψ (N • v) = v := by
        show (N : I.E)⁻¹ • (N • v) = v
        rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
      rw [← e]
      exact Submodule.mem_map_of_mem h1
    haveI : IsNoetherian (𝓞 I.E) (I.L.map ψ) := isNoetherian_of_fg_of_noetherian _ (I.L_fg.map ψ)
    haveI : IsNoetherian (𝓞 I.E) (abelian₂ I x) := isNoetherian_of_le hle
    first
      | exact (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
      | exact Module.Finite.iff_fg.mp inferInstance
  · rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro v hv
    have h1 : N • v ∈ abelian₂ I x := DictGen.nL_sub I x N hN' hv
    have h2 : N • v ∈ Submodule.span I.E
        ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) :=
      Submodule.subset_span h1
    have e : v = (N : I.E)⁻¹ • (N • v) := by
      rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ h2

theorem mGen_of (hD : LDenom) (hDen : LDense) : MGen := by
  intro I x y hy
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNL : ∀ u ∈ I.Lf, (N : (I.E ⊗[I.F] Af I.F)) • u ∈
      Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E)) := by
    intro u hu
    rw [DictGen.lf_eq] at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hz
      show (N : (I.E ⊗[I.F] Af I.F)) • iv I l ∈ _
      rw [← DictGen.iv_nsmul]
      exact Submodule.subset_span ⟨⟨N • l, DictGen.nL_sub I x N hN' hl⟩, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul s a _ ha =>
      have e : (N : (I.E ⊗[I.F] Af I.F)) • (s • a) = s • ((N : (I.E ⊗[I.F] Af I.F)) • a) := by
        show (N : (I.E ⊗[I.F] Af I.F)) • ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • ((N : (I.E ⊗[I.F] Af I.F)) • a)
        rw [smul_smul, smul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ s ha
  obtain ⟨l, hl, y', hy', hw⟩ := hDen I (N * N) (Nat.mul_pos hN hN) _ (hN' y hy).1
  obtain ⟨v, hv⟩ : ∃ v : Fin I.n → I.E, v = (N : I.E)⁻¹ • l := ⟨_, rfl⟩
  have hNv : N • v = l := by
    rw [hv, ← Nat.cast_smul_eq_nsmul I.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  have hz : I.fmat x *ᵥ y = iv I v + (N : (I.E ⊗[I.F] Af I.F)) • y' := by
    apply DictGen.natCast_cancel I N hN
    rw [smul_add, ← DictGen.iv_nsmul, hNv, hw, smul_smul, Nat.cast_mul]
  have hvL : v ∈ abelian₂ I x := by
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    have e : iv I v = I.fmat x *ᵥ y - (N : (I.E ⊗[I.F] Af I.F)) • y' := by
      first
        | rw [hz, add_sub_cancel_right]
        | (rw [hz]; abel)
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul]
    exact I.Lf.sub_mem hy (hN' y' hy').2
  rw [hz]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨v, hvL⟩, rfl⟩) (hNL y' hy')

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter
section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

namespace DictInter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tau (w : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ
    TensorProduct.map ((Algebra.trace F E) ∘ₗ LinearMap.mulLeft F w) LinearMap.id

lemma tau_tmul (w e : E) (a : Af F) : tau w (e ⊗ₜ[F] a) = Algebra.trace F E (w * e) • a := by
  first
    | simp [tau]
    | rfl


variable (F E) in
def dualSet : Set E := {w | ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range}

lemma tau_mul_left (w a : E) (r : E ⊗[F] Af F) :
    tau w ((a ⊗ₜ[F] (1 : Af F)) * r) = tau (w * a) r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_assoc]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy]

lemma tau_mul_right (w : E) (b : Af F) (r : E ⊗[F] Af F) :
    tau w (((1 : E) ⊗ₜ[F] b) * r) = b * tau w r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

lemma tau_incl (w e : E) :
    tau w (Formalism.UG.inclE (F := F) (Af F) e) = algebraMap F (Af F) (Algebra.trace F E (w * e)) := by
  show tau w (e ⊗ₜ[F] (1 : Af F)) = _
  rw [tau_tmul, Algebra.algebraMap_eq_smul_one]

lemma algebraMap_mem_intAd (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by
  intro v
  have h1 : Valued.v (((algebraMap (𝓞 F) F x : F)) : v.adicCompletion F) ≤ 1 := by
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
  first
    | exact h1
    | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1

lemma of_algebraMap_mem_intAd (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) f ?_
  intro v
  have hv : Valued.v ((f : F) : v.adicCompletion F) ≤ 1 := h v
  first
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv

def tSet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Set (E ⊗[F] Af F) :=
  {r | ∀ w ∈ dualSet F E, tau w r ∈ Formalism.UG.intAd F}

lemma one_mem_tSet : (1 : E ⊗[F] Af F) ∈ tSet F E := by
  show ∀ w ∈ dualSet F E, tau w ((1 : E) ⊗ₜ[F] (1 : Af F)) ∈ Formalism.UG.intAd F
  intro w hw
  have hw1 := (show ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range from hw) 1
  obtain ⟨x, hx⟩ := hw1
  rw [tau_tmul, ← Algebra.algebraMap_eq_smul_one]
  have hx' : Algebra.trace F E (w * (1 : E)) = algebraMap (𝓞 F) F x := by
    rw [hx]
    rfl
  rw [hx']
  exact algebraMap_mem_intAd x

private theorem mul_algebraMap_mem_dualSet {w : E} (hw : w ∈ dualSet F E) (a : 𝓞 E) :
    w * algebraMap (𝓞 E) E a ∈ dualSet F E := by
  show ∀ b : 𝓞 E, Algebra.trace F E (w * algebraMap (𝓞 E) E a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
  intro b
  have h := (show ∀ b : 𝓞 E, Algebra.trace F E (w * (b : E)) ∈ (algebraMap (𝓞 F) F).range from hw) (a * b)
  rw [mul_assoc]
  exact h

lemma mem_tSet (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  suffices h : ∀ s ∈ tSet F E, r * s ∈ tSet F E by
    have h1 := h 1 one_mem_tSet
    rwa [mul_one] at h1
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := he
      intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_left]
      exact (show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) _ (mul_algebraMap_mem_dualSet hw a)
    · intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_right]
      exact mul_mem hb ((show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) w hw)
  | zero =>
    intro s _
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w _
    rw [zero_mul, map_zero]
    exact zero_mem _
  | one =>
    intro s hs
    rwa [one_mul]
  | add x y _ _ hx hy =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [add_mul, map_add (f := _)]
    exact add_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
      ((show ∀ w ∈ dualSet F E, tau w (y * s) ∈ Formalism.UG.intAd F from hy s hs) w hw)
  | neg x _ hx =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [neg_mul, map_neg]
    exact neg_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_assoc]
    exact hx _ (hy s hs)

end DictInter

open DictInter in
theorem dual_intersection : DInter := by
  intro F E _ _ _ _ _ e he
  have ht := mem_tSet (F := F) (E := E) _ he
  have key : ∀ w ∈ dualSet F E, Algebra.trace F E (w * e) ∈ (algebraMap (𝓞 F) F).range := by
    intro w hw
    apply of_algebraMap_mem_intAd
    rw [← tau_incl]
    exact (show ∀ w ∈ dualSet F E, tau w (Formalism.UG.inclE (F := F) (Af F) e) ∈ Formalism.UG.intAd F from ht) w hw
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    first
      | exact FractionalIdeal.dual_ne_zero (𝓞 F) F h1
      | exact FractionalIdeal.dual_ne_zero h1
  have hmem : e ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    rw [Algebra.traceForm_apply, mul_comm]
    apply key
    show ∀ b : 𝓞 E, Algebra.trace F E (a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
    intro b
    have hb := ha (b : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    rwa [Algebra.traceForm_apply] at hb
  rw [FractionalIdeal.dual_dual] at hmem
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  exact ⟨x, hx⟩

end PIW.AdelClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSingleLeft
section
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG
open scoped Matrix

section
variable {E : Type} [Field E] [StarRing E]

theorem cT_star {a b : Type} (A : Matrix a b E) : cT (starRingEnd E) A = Aᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem isHerm_iff {n : Type} (J : Matrix n n E) : IsHerm (starRingEnd E) J ↔ Jᴴ = J := by
  unfold IsHerm
  rw [cT_star]

theorem hform_eq {n : Type} [Fintype n] (J : Matrix n n E) (x y : n → E) :
    hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem hform_mulVec {n a : Type} [Fintype n] [Fintype a] (J : Matrix n n E) (A B : Matrix n a E)
    (x y : a → E) :
    hform (starRingEnd E) J (A *ᵥ x) (B *ᵥ y) = hform (starRingEnd E) (cT (starRingEnd E) A * J * B) x y := by
  rw [hform_eq, hform_eq, cT_star, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem hform_add_left {n : Type} [Fintype n] (J : Matrix n n E) (x x' y : n → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform_eq, star_add, add_dotProduct]

theorem hform_single_left {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i : n) (y : n → E) :
    hform (starRingEnd E) J (Pi.single i 1) y = (J *ᵥ y) i := by
  have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
    ext r
    by_cases h : r = i
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [hform_eq, hs]
  simp

theorem hform_single {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i j : n) :
    hform (starRingEnd E) J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_single_left]
  simp [Matrix.mulVec]

theorem cT_mulVec_apply {n k : Type} [Fintype n] (J : Matrix n n E) (V : Matrix n k E) (z : n → E) (i : k) :
    ((cT (starRingEnd E) V * J) *ᵥ z) i = hform (starRingEnd E) J (fun r => V r i) z := by
  rw [hform_eq, ← Matrix.mulVec_mulVec, cT_star]
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq [NumberField E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin k → Fin m → E) :
    gram J v = cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r := by
  ext i j
  have h1 : (cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r) i j =
      ((cT (starRingEnd E) (Matrix.of fun r i => v i r) * J) *ᵥ v j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, cT_mulVec_apply]
  simp [PIW.AdelClassFin.gram]

end

end PIW.AdelClassFin
end
end

