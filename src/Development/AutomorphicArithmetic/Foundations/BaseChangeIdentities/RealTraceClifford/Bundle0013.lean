module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RhoStrict
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WspOrth
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefData
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem trOn_top_one {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] : trOn S (1 : Module.End ℂ V) = (Module.finrank ℂ S : ℂ) := by
  unfold trOn
  rw [dite_eq_left (fun x hx => by simpa using hx)]
  have : (LinearMap.restrict (1 : Module.End ℂ V) (fun x hx => by simpa using hx) : Module.End ℂ S) = 1 := by
    ext x
    rfl
  rw [this, LinearMap.trace_one]

private theorem prod_swap {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, z a * conj (z a) = 1) :
    (∏ a, ∏ b, (1 + conj (z a) / conj (z b))) = ∏ a, ∏ b, (1 + z a / z b) := by
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  have hc : ∀ a, conj (z a) = (z a)⁻¹ := fun a => (eq_inv_of_mul_eq_one_right (hz a))
  have key : ∀ a b, conj (z a) / conj (z b) = z b / z a := by
    intro a b
    rw [hc, hc]
    field_simp [hne a, hne b]
  simp_rw [key]
  exact Finset.prod_comm

theorem UpperTheory.RealTr.lefData :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
      ∃ (E' : KMod n) (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] E'.V) (T' : Module.End ℂ E'.V) (σ' : UK n →* (E'.V →ₗ[ℂ] E'.V)) (F : Fin n → Fin n → Module.End ℂ E'.V)
        (χ : FR n) (s : Finset (Wt n)), (∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = σ' k (e ξ)) ∧ (∀ ξ, e (dualT E T ξ) = T' (e ξ)) ∧ UF F ∧ IsDerivK σ' F ∧
        (∀ a b, T' * F a b = F a b * T') ∧ (∀ ν ∉ s, hw F ν = ⊥) ∧ alt (rhoV n) * χ = alt ((fun a => (lam a : ℝ)) + rhoV n) ∧
        ∀ ν : Wt n, StrictAnti (ν + rhoV n) → trOn (hw F ν) T' = 2 ^ n * cf (chR n * alt (twoL lam)) (ν + rhoV n) ∧
          (Module.finrank ℂ (hw F ν) : ℂ) = 2 ^ n * cf (chR n * (alt ((2 : ℝ) • rhoV n) * (χ * χ))) (ν + rhoV n) := by
  intro n lam hlam E T hL
  obtain ⟨hcomm, hTT, htrace⟩ := hL
  obtain ⟨E', e, T', he1, he2, he3⟩ := dualEx n E T hcomm
  obtain ⟨σ', F, hσ, hUF, hder⟩ := kDer n E'
  have hTρ : ∀ (k : UK n) (v : E'.V), T' (E'.ρ k v) = E'.ρ k (T' v) := by
    intro k v
    obtain ⟨ξ, rfl⟩ := e.surjective v
    rw [← he1, ← he2, ← he2, ← he1]
    congr 1
    ext x
    have hx := congrArg (fun f : E.V →L[ℂ] E.V => f x) (hcomm k⁻¹)
    simp only [ContinuousLinearMap.mul_apply] at hx
    show ξ (E.ρ k⁻¹ (T x)) = ξ (T (E.ρ k⁻¹ x))
    rw [hx]
  have hTF : ∀ a b, T' * F a b = F a b * T' := by
    have hmem : T' ∈ homL F F := by
      refine ((derAt n E'.V σ' F hder).2 E'.V σ' F hder T').1 ?_
      intro k x
      rw [hσ, hσ]
      exact hTρ k x
    intro a b
    ext x
    exact hmem a b x
  have hDom : Dom (fun a => (lam a : ℝ)) := by
    intro a b hab
    have hle := hlam hab.le
    refine ⟨(lam a - lam b).toNat, ?_⟩
    have h0 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have h1 : (((lam a - lam b).toNat : ℕ) : ℝ) = ((lam a - lam b : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1]
    push_cast
    ring
  obtain ⟨χ, -, hχ⟩ := divEx n _ hDom
  have hStop : Stb F (⊤ : Submodule ℂ E'.V) := fun a b x _ => trivial
  obtain ⟨s, hs, -, -⟩ := wtDec n E'.V F hUF ⊤ inferInstance hStop
  have hCm1 : Cm F ⊤ (1 : Module.End ℂ E'.V) :=
    ⟨fun a b => by rw [one_mul, mul_one], fun x _ => trivial⟩
  have hCmT : Cm F ⊤ T' := ⟨hTF, fun x _ => trivial⟩
  obtain ⟨c₁, hc₁⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop 1
  obtain ⟨cT, hcT⟩ := chEx n E'.V F hUF ⊤ inferInstance hStop T'
  have hkey : ∀ (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * (θ a : ℂ))) →
      (Function.Injective fun a => z a ^ 2) →
      evT θ c₁ = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2 ∧
      evT θ cT = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
    intro θ z hz hinj
    have hzn : ∀ a, z a * conj (z a) = 1 := by
      intro a
      rw [Complex.mul_conj, hz a, Complex.normSq_eq_norm_sq, mul_comm, Complex.norm_exp_ofReal_mul_I]
      simp
    have hmemU : diagonal z ∈ unitaryGroup (Fin n) ℂ := by
      rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext a
      exact hzn a
    set k : UK n := ⟨diagonal z, hmemU⟩ with hkdef
    have hk : (k : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ)) := by
      show diagonal z = _
      congr 1
      funext a
      exact hz a
    have hkinv : ((k⁻¹ : UK n) : Matrix (Fin n) (Fin n) ℂ) = diagonal fun a => conj (z a) := by
      rw [UnitaryGroup.inv_val]
      show star (diagonal z) = _
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      rfl
    have hinj' : Function.Injective fun a => conj (z a) ^ 2 := by
      intro a b h
      apply hinj
      have h' := congrArg conj h
      simpa [map_pow] using h'
    have hσk : (σ' k : Module.End ℂ E'.V) = ((E'.ρ k : E'.V →L[ℂ] E'.V) : Module.End ℂ E'.V) := by
      ext v
      exact hσ k v
    have hw := (weylEv n lam θ z hz).2.2.2
    obtain ⟨t1, t2⟩ := htrace k⁻¹ (fun a => conj (z a)) hkinv hinj'
    constructor
    · rw [← chEv n E'.V σ' F hUF hder 1 c₁ hCm1 hc₁ θ k hk, mul_one, hσk, (he3 k).1, t1,
        prod_swap z hzn, hw z]
    · rw [← chEv n E'.V σ' F hUF hder T' cT hCmT hcT θ k hk, hσk, (he3 k).2, t2,
        prod_swap z hzn]
      have : (fun a => conj (z a) ^ 2) = fun a => conj (z a ^ 2) := by
        funext a
        rw [map_pow]
      rw [this, hw (fun a => z a ^ 2)]
  obtain ⟨hT, h1⟩ := lefForm n lam c₁ cT χ hχ hkey
  refine ⟨E', e, T', σ', F, χ, s, ?_, he2, hUF, hder, hTF, ?_, hχ, ?_⟩
  · intro k ξ
    rw [he1, hσ]
  · intro ν hν
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ wsp F ν ⊓ ⊤ := ⟨hx.1, trivial⟩
    rw [hs ν hν] at hx'
    exact hx'
  · intro ν hν
    have mT := mult n E'.V F hUF ⊤ inferInstance hStop T' cT hCmT hcT ν hν
    have m1 := mult n E'.V F hUF ⊤ inferInstance hStop 1 c₁ hCm1 hc₁ ν hν
    rw [inf_top_eq] at mT m1
    rw [hT] at mT
    rw [h1] at m1
    constructor
    · rw [← mT]
      simp [cf]
    · rw [← trOn_top_one, ← m1]
      simp [cf]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnCas
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.SpinCasimir

variable {n : ℕ} {J : Type} [Fintype J] [DecidableEq J]

private abbrev Fm (c : Fin n → Fin n → Matrix J J ℂ) : Fin n → Fin n → Module.End ℂ (Ten J ℂ) :=
  dg (fun _ _ : Fin n => (0 : Module.End ℂ ℂ)) c

private theorem Fm_eq (c : Fin n → Fin n → Matrix J J ℂ) (a b : Fin n) :
    Fm c a b = mt ℂ (spn c a b) := by
  simp [Fm, dg]

private theorem mem_wsp (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (μ : Wt n) (x : Ten J ℂ) : x ∈ wsp (Fm c) μ ↔ ∀ j, x j ≠ 0 → η j = μ := by
  have key : ∀ a j, (Fm c a a x) j = (η j a : ℂ) * x j := by
    intro a j
    rw [Fm_eq, h.diag a]
    simp [mt, Matrix.diagonal_apply]
  constructor
  · intro hx j hj
    funext a
    have e : (Fm c a a x) j = ((μ a : ℂ) • x) j := congrArg (fun y : Ten J ℂ => y j) (hx a)
    rw [key] at e
    have e' : (η j a : ℂ) * x j = (μ a : ℂ) * x j := by simpa using e
    exact Complex.ofReal_injective (mul_right_cancel₀ hj e')
  · intro hx a
    ext j
    rw [key]
    by_cases hj : x j = 0
    · simp [hj]
    · simp [hx j hj]

private def wEquiv (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) (μ : Wt n) :
    wsp (Fm c) μ ≃ₗ[ℂ] ({j // η j = μ} → ℂ) where
  toFun x := fun j => x.1 j.1
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp
  invFun y := ⟨WithLp.toLp 2 fun j => if hj : η j = μ then y ⟨j, hj⟩ else 0, by
    rw [mem_wsp c η h]
    intro j hj
    by_contra hc
    exact hj (by simp [hc])⟩
  left_inv x := by
    ext j
    by_cases hj : η j = μ
    · simp [hj]
    · have : x.1 j = 0 := by
        by_contra hc
        exact hj ((mem_wsp c η h μ x.1).1 x.2 j hc)
      simp [hj, this]
  right_inv y := by
    ext j
    simp [j.2]

private theorem cf_sum_ex (η : J → Wt n) (μ : Wt n) :
    cf (∑ j, ex (η j)) μ = (Fintype.card {j // η j = μ} : ℂ) := by
  classical
  simp [cf, ex, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype]

private theorem isCh_top (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η) :
    IsCh (Fm c) ⊤ 1 (∑ j, ex (η j)) := by
  intro μ
  rw [cf_sum_ex, inf_top_eq, (trAdd _ 1).2.2.2 _ inferInstance,
    (wEquiv c η h μ).finrank_eq, Module.finrank_fintype_fun_eq_card]

private theorem mt_ext (M : Matrix J J ℂ) (s : ℂ) (hs : ∀ x : Ten J ℂ, mt ℂ M x = s • x) :
    M = s • (1 : Matrix J J ℂ) := by
  ext j k
  have e := congrArg (fun y : Ten J ℂ => y j) (hs (WithLp.toLp 2 (Pi.single k 1)))
  simpa [mt, Pi.single_apply, Matrix.one_apply, eq_comm] using e

private theorem cas_eq (c : Fin n → Fin n → Matrix J J ℂ) :
    Cas (Fm c) = mt ℂ (Cas (spn c)) := by
  obtain ⟨φ, hφ⟩ := (tenF n ℂ J).1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Cas, Fm_eq, ← hφ, map_sum, map_mul]

private theorem hw_bot (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n) (h : ClifMod c η)
    (hU : UF (Fm c)) (μ : Wt n) (hμ : μ ≠ rhoV n) : hw (Fm c) μ ⊓ ⊤ = ⊥ := by
  rw [inf_top_eq]
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hdom : Dom μ := hwDom n _ _ hU ⊤ hS hStb μ x Submodule.mem_top hx0 hx
  obtain ⟨-, -, hρ, -, hd, -⟩ := rearr n
  have hanti : StrictAnti (μ + rhoV n) := (hd μ hdom).1.add_strictAnti hρ
  have hm := mult n _ _ hU ⊤ hS hStb 1 _ ⟨fun a b => by simp, fun _ _ => Submodule.mem_top⟩
    (isCh_top c η h) μ hanti
  have hfin : FiniteDimensional ℂ (hw (Fm c) μ ⊓ ⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  rw [(trAdd _ 1).2.2.2 _ hfin, inf_top_eq, h.chr, mul_smul_comm, ← (chRF n).1] at hm
  have hpos : Module.finrank ℂ (hw (Fm c) μ) ≠ 0 := by
    intro h0
    exact hne (Submodule.finrank_eq_zero.1 h0)
  have h2 : StrictAnti ((2 : ℝ) • rhoV n) := fun a b hab => by
    have := hρ hab
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  obtain ⟨-, -, -, hcf, -, -, -, -, -, -, -, htop, -⟩ := cfBasic n
  have hne2 : μ + rhoV n ≠ (2 : ℝ) • rhoV n := fun e => hμ (by
    funext a
    have := congrFun e a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith)
  rw [(hcf _ 0 _ _).2, (htop _ h2).2 _ hanti hne2, mul_zero] at hm
  exact hpos (by exact_mod_cast hm.symm)

end UpperTheory.RealTr.SpinCasimir

open UpperTheory.RealTr.SpinCasimir in
theorem UpperTheory.RealTr.spnCas :
    ∀ n : ℕ, ∀ (J : Type) [Fintype J] [DecidableEq J] (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), ClifMod c η → Cas (spn c) = ((3 * nsq (rhoV n) : ℝ) : ℂ) • (1 : Matrix J J ℂ) := by
  intro n J _ _ c η h
  have hU : UF (Fm c) := (tenF n ℂ J).2.2.2.2 _ c η uf_zero h
  have hS : FiniteDimensional ℂ (⊤ : Submodule ℂ (Ten J ℂ)) := inferInstance
  have hStb : Stb (Fm c) ⊤ := fun _ _ _ _ => Submodule.mem_top
  have hiso := (isoFacts n _ _ hU ⊤ hS hStb (rhoV n) (hw_bot c η h hU)).1
  have hn : nsq (rhoV n + rhoV n) - nsq (rhoV n) = 3 * nsq (rhoV n) := by
    simp only [nsq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  refine mt_ext _ _ fun x => ?_
  rw [← cas_eq, hiso x Submodule.mem_top, hn]
end
end

