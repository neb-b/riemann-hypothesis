module

public import Mathlib
public import Formalism.DegreeFormula.FlagDegFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import ReciprocityTheory.DualLattices.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
section
open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)

def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j

end GlobalTheory.FlagPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.DiagUnitsEqLocalIdele
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.Mem.Chr
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

end GlobalTheory.Mem.Chr.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EtaSixProductDifferentiable
section
noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

def eta6 (z : ℍ) : ℂ := ModularForm.eta z ^ 6

lemma eta_six_ne_zero (z : ℍ) : eta6 z ≠ 0 := pow_ne_zero _ (eta_ne_zero z.2)

lemma eta_six_product_formula (z : ℍ) : eta6 z = Periodic.qParam 4 z * (∏' n, (1 - eta_q n z)) ^ 6 := by
  simp only [eta6, ModularForm.eta, mul_pow]
  congr
  simp [Periodic.qParam, ← Complex.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

lemma eta6_slash_three_T_eq_I_smul : eta6 ∣[(3 : ℤ)] ModularGroup.T = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  have h1 : ∀ n, eta_q n (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = eta_q n z := by
    intro n
    simp only [eta_q, Periodic.qParam, coe_vadd]
    rw [← exp_periodic (2 * π * Complex.I * z / ((1:ℝ):ℂ))]
    congr 2
    push_cast; ring
  have h2 : Periodic.qParam 4 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Complex.I * Periodic.qParam 4 z := by
    simp only [Periodic.qParam, coe_vadd]
    rw [← exp_pi_div_two_mul_I, ← Complex.exp_add, exp_pi_div_two_mul_I]
    congr 1
    push_cast; ring
  simp only [eta_six_product_formula, h1, h2, Pi.smul_apply, smul_eq_mul]
  simp [ModularGroup.T, mul_assoc]

lemma sqrt_pow_six (z : ℂ) : Complex.sqrt z ^ 6 = z ^ 3 := by
  have : Complex.sqrt z ^ 2 = z := by
    simp [Complex.sqrt]
  rw [show 6 = 2 * 3 by rfl, pow_mul, this]

lemma eta_six_slash_S : eta6 ∣[(3 : ℤ)] ModularGroup.S = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  have hz := z.ne_zero
  simp only [eta6, inv_neg, he, mul_pow, inv_pow, sqrt_pow_six, Pi.smul_apply, smul_eq_mul]
  have : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, I_sq]; ring
  rw [this, zpow_neg, inv_neg, inv_I]
  field_simp

lemma eta_six_slash_root_of_unity (γ : SL(2, ℤ)) : ∃ c : ℂ, c ^ 4 = 1 ∧ eta6 ∣[(3 : ℤ)] γ = c • eta6 := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Complex.I, I_pow_four, eta_six_slash_S⟩
    · exact ⟨Complex.I, I_pow_four, eta6_slash_three_T_eq_I_smul⟩
  | one => exact ⟨1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
    rw [SlashAction.slash_mul, hx, SL_smul_slash, hy, smul_smul]
  | inv x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹, by rw [inv_pow, ha, inv_one], ?_⟩
    have : eta6 = a • eta6 ∣[(3 : ℤ)] x⁻¹ := by
      rw [← SL_smul_slash, ← hx, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    conv_rhs => rw [this]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

def eta6MultiplierFunction (γ : SL(2, ℤ)) : ℂ := (eta6 ∣[(3 : ℤ)] γ) UpperHalfPlane.I / eta6 UpperHalfPlane.I

lemma eta6Mult0_eq {γ : SL(2, ℤ)} {c : ℂ} (h : eta6 ∣[(3 : ℤ)] γ = c • eta6) : eta6MultiplierFunction γ = c := by
  simp [eta6MultiplierFunction, h, eta_six_ne_zero]

lemma eta_six_slash_multiplier (γ : SL(2, ℤ)) : eta6 ∣[(3 : ℤ)] γ = eta6MultiplierFunction γ • eta6 := by
  obtain ⟨c, -, h⟩ := eta_six_slash_root_of_unity γ
  rw [eta6Mult0_eq h, h]

def eta6Mult : SL(2, ℤ) →* ℂ where
  toFun := eta6MultiplierFunction
  map_one' := eta6Mult0_eq (by simp)
  map_mul' x y := eta6Mult0_eq (by
    rw [SlashAction.slash_mul, eta_six_slash_multiplier, SL_smul_slash, eta_six_slash_multiplier, smul_smul])

lemma eta6Mult_T_eq_I : eta6Mult ModularGroup.T = Complex.I := eta6Mult0_eq eta6_slash_three_T_eq_I_smul

lemma eta6Mult_S : eta6Mult ModularGroup.S = Complex.I := eta6Mult0_eq eta_six_slash_S

lemma eta6Mult_neg_one : eta6Mult (-1) = -1 := by
  have : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [this, map_mul, eta6Mult_S, I_mul_I]

def eta6Group : Subgroup SL(2, ℤ) := eta6Mult.toHomUnits.ker

lemma mem_eta6Group (γ : SL(2, ℤ)) : γ ∈ eta6Group ↔ eta6Mult γ = 1 := by
  simp [eta6Group, MonoidHom.mem_ker, Units.ext_iff]

lemma neg_one_not_mem_eta6Group : (-1 : SL(2, ℤ)) ∉ eta6Group := by
  rw [mem_eta6Group, eta6Mult_neg_one]; norm_num

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Imports
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)

def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)

end GlobalTheory.Sieg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
section
noncomputable section

namespace GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IntegralLocallyConstCochainModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (w : Gal p Ω → Ω) : Prop :=
  (∀ g ∈ H, IsInt (p := p) (w g)) ∧
    ∀ g ∈ H, ∃ S : Finset Ω, ∀ h ∈ H,
      (∀ x ∈ S, h x = g x) → Cong (p := p) k (w h) (w g)

def IsTwistedOneCocycle (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, Cong (p := p) k (c (g * h)) (c g + ((χ g).val : Ω) ^ j * g (c h))

def IsTwistedOneCoboundary (j k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (c : Gal p Ω → Ω) : Prop :=
  ∃ x : Ω, IsInt (p := p) x ∧ ∀ g ∈ H, Cong (p := p) k (c g) (((χ g).val : Ω) ^ j * g x - x)

end GlobalTheory.K5
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
section
namespace GlobalTheory.FGDepth

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C]

def toE (x : WithTop ℝ) : EReal := (WithBot.some x : WithBot (WithTop ℝ))

def mfact {σ : Type} (α : σ →₀ ℕ) : C := α.prod fun _ n => (n.factorial : C)

def derivAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ α ∈ P.support, P.coeff α * mfact α * coeff α g

def content (v : AddValuation C (WithTop ℝ)) {σ : Type} (P : MvPolynomial σ C) : EReal :=
  ⨅ α ∈ P.support, toE (v (P.coeff α * mfact α))

variable {v : AddValuation C (WithTop ℝ)}

def IsExp {d : ℕ} (G : LogFGL v d) (ex : Fin d → MvPowerSeries (Fin d) C) : Prop :=
  (∀ a, constantCoeff (ex a) = 0) ∧ ∀ a, subst ex (G.lg a) = X a

def expOf {d : ℕ} (G : LogFGL v d) : Fin d → MvPowerSeries (Fin d) C :=
  Classical.epsilon (IsExp G)

def expAlong {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) :
    (Σ b, Fin (d b)) → MvPowerSeries (Σ b, ι b) C :=
  fun x => subst (fun e : Fin (d x.1) =>
    ∑ a, u x.1 a e • (X ⟨x.1, a⟩ : MvPowerSeries (Σ b, ι b) C)) (expOf (G x.1) x.2)

def depth {κ : Type} {d : κ → ℕ} (G : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C) : EReal :=
  ⨅ f : {f : MvPowerSeries (Σ b, Fin (d b)) C // MvIsInt v f},
    toE (v (derivAt0 P (subst (expAlong G u) f.1)))

def detPow (C : Type) [Field C] (i c : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) C :=
  (Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) C))) ^ c

def IsSatFrame (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (u : Fin i → Fin d → C) : Prop :=
  (∀ a e, IsIntV v (u a e)) ∧
    ∃ r : Fin i → Fin d, v (Matrix.det (Matrix.of fun a b => u a (r b))) = 0

def detDepth {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C) (c : ℕ) : EReal :=
  depth (fun _ : Fin i => G) (fun _ => u) (detPow C i c)

def IsCharLog {d : ℕ} (G : LogFGL v d) (l : Fin d → C) : Prop :=
  ∃ χ : MvPowerSeries (Fin d) C, MvIsInt v χ ∧
    ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => l e ^ n / (n.factorial : C)

end

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
section
noncomputable section

namespace GlobalTheory.K4

open GlobalTheory.KEdge GlobalTheory.NeedB

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def geo (F K Ω : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] :
    Subgroup (Ω ≃ₐ[F] Ω) :=
  (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup

def IsTopW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) (w : K) :
    Prop :=
  w ≠ 0 ∧ ∃ θ : Ω, θ ^ N = algebraMap K Ω w ∧ ∀ g ∈ geo F K Ω, kum (K := F) (N := N) ζ θ g = edge x y η σ g


open Classical in
def topW {N : ℕ} (ζ : Ω) (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)) (η : (Ω ≃ₐ[F] Ω) → ZMod N) (σ : Ω ≃ₐ[F] Ω) : K := by
  classical
  exact if h : ∃ w : K, IsTopW ζ x y η σ w then h.choose else 1

namespace TopW

variable {N : ℕ} {ζ : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)} {η : (Ω ≃ₐ[F] Ω) → ZMod N}

theorem mem_geo (g : Ω ≃ₐ[F] Ω) : g ∈ geo F K Ω ↔ ∀ z : K, g (algebraMap K Ω z) = algebraMap K Ω z := by
  unfold geo
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h z
    exact h _ ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h z

theorem conj_mem_geo [Normal F K] (σ : Ω ≃ₐ[F] Ω) {h : Ω ≃ₐ[F] Ω} (hh : h ∈ geo F K Ω) : σ * h * σ⁻¹ ∈ geo F K Ω := by
  rw [mem_geo] at hh ⊢
  intro z
  have h1 : σ⁻¹ (algebraMap K Ω z) = algebraMap K Ω ((σ⁻¹).restrictNormal K z) :=
    (AlgEquiv.restrictNormal_commutes σ⁻¹ K z).symm
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, hh, ← h1]
  exact σ.apply_symm_apply _

theorem exists_of_fixed [IsGalois K Ω] {z : Ω} (hz : ∀ g ∈ geo F K Ω, g z = z) : ∃ c : K, algebraMap K Ω c = z :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) z).2 fun g =>
    hz (AlgEquiv.restrictScalarsHom F g) ((mem_geo _).2 fun w => g.commutes w)

theorem apply_eq_kum [NeZero N] (hζ : IsPrimitiveRoot ζ N) {θ : Ω} {w : K} (hw0 : w ≠ 0)
    (hw : θ ^ N = algebraMap K Ω w) {g : Ω ≃ₐ[F] Ω} (hg : g ∈ geo F K Ω) :
    g θ = ζ ^ (kum (K := F) (N := N) ζ θ g).val * θ := by
  have hw1 : algebraMap K Ω w ≠ 0 := by simpa using hw0
  have hθ : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne N)] at hw
    exact hw1 hw.symm
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hw, (mem_geo g).1 hg, div_self hw1]
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine kum_choose_spec ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, he, div_mul_cancel₀ _ hθ]

theorem pow_val_add [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem pow_val_mul [NeZero N] (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a * b).val = (ζ ^ b.val) ^ a.val := by
  rw [← pow_mul, mul_comm b.val, ZMod.val_mul]
  conv_rhs => rw [← Nat.mod_add_div (a.val * b.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem edge_mul_conj {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ τ h : Γ) :
    edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h := by
  simp only [edge, map_mul, map_inv, toAdd_mul, toAdd_inv, mul_inv_rev]
  have : σ * τ * h * (τ⁻¹ * σ⁻¹) = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
  rw [this]; ring

theorem edge_inv {Γ : Type*} [Group Γ] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N) (σ h : Γ) :
    edge x y η σ⁻¹ h = η (σ⁻¹ * h * σ) - η h + (x h).toAdd * (y σ).toAdd - (x σ).toAdd * (y h).toAdd := by
  simp only [edge, map_inv, toAdd_inv, inv_inv]
  ring

theorem isTopW_topW_of_exists {σ : Ω ≃ₐ[F] Ω} (h : ∃ w : K, IsTopW ζ x y η σ w) :
    IsTopW ζ x y η σ (topW (K := K) ζ x y η σ) := by
  unfold topW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem topW_ne_zero (σ : Ω ≃ₐ[F] Ω) : topW (K := K) ζ x y η σ ≠ 0 := by
  by_cases h : ∃ w : K, IsTopW ζ x y η σ w
  · exact (isTopW_topW_of_exists h).1
  · unfold topW
    rw [dite_eq_right h]
    exact one_ne_zero

theorem unique [NeZero N] [IsGalois K Ω] (hζ : IsPrimitiveRoot ζ N) {σ : Ω ≃ₐ[F] Ω} {w v : K}
    (hw : IsTopW ζ x y η σ w) (hv : IsTopW ζ x y η σ v) : ∃ c : K, c ≠ 0 ∧ w = v * c ^ N := by
  obtain ⟨hw0, θ, hθ, hθk⟩ := hw
  obtain ⟨hv0, ψ, hψ, hψk⟩ := hv
  have hv1 : algebraMap K Ω v ≠ 0 := by simpa using hv0
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  obtain ⟨c, hc⟩ := exists_of_fixed (F := F) (K := K) (z := θ / ψ) fun g hg => by
    rw [map_div₀, apply_eq_kum hζ hw0 hθ hg, apply_eq_kum hζ hv0 hψ hg, hθk g hg, hψk g hg,
      mul_div_mul_left _ _ (pow_ne_zero _ hz)]
  have key : w = v * c ^ N := by
    apply (algebraMap K Ω).injective
    rw [map_mul, map_pow, hc, div_pow, hθ, hψ, mul_div_cancel₀ _ hv1]
  refine ⟨c, ?_, key⟩
  rintro rfl
  rw [zero_pow (NeZero.ne N), mul_zero] at key
  exact hw0 key

end TopW

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.K4

open GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Subfield X.K :=
  ⨅ γ ∈ Γ', RingHom.eqLocusField (X.sl (ofSL γ)).toRingEquiv.toRingHom (RingHom.id X.K)

def mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Subfield X.K :=
  lev X Γ' ⊓ ⨅ s ∈ S, RingHom.eqLocusField (X.gal s).toRingHom (RingHom.id X.K)

end GlobalTheory.K4
end
end

