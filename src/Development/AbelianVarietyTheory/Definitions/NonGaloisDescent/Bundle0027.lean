module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRecTOfIsRec
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT.Model

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem good_of_toral {x : IrrGL (k := k)} (hx : Toral x) : Good x := by
  obtain ⟨s, hs, hy⟩ := hx
  exact ⟨s, hs, fun y hys => Or.inl (hy y hys)⟩

end Classes

end GlobalTheory.RecT.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PotentiallySemistableCyclotomicSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

variable {n : Type} [Fintype n] [DecidableEq n]

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

end GlobalTheory.PMon.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SumTrWEqZeroOfFrobCoset
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.VWeil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_pow_frob_comm (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ σ) (ρ (frob h) ^ m) := by
  classical
  have h1 : ∀ T : Set.range fun τ : Ine (F := E) A => ρ (ineIncl h τ),
      ∃ m : ℕ, 0 < m ∧ Commute T.1 (ρ (frob h) ^ m) := by
    rintro ⟨_, τ, rfl⟩
    obtain ⟨m, hm, hpow⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ
      (ineIncl h τ * frob h * (ineIncl h τ)⁻¹) (frob h) (by simp)
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, conj_pow] at hpow
    show ρ (ineIncl h τ) * _ = _ * ρ (ineIncl h τ)
    conv_rhs => rw [← hpow]
    rw [← map_pow, ← map_mul, ← map_mul, inv_mul_cancel_right]
  choose m hm hc using h1
  haveI := hρ.finite_range.fintype
  refine ⟨∏ T, m T, Finset.prod_pos fun T _ => hm T, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  rw [hτ, map_mul]
  refine Commute.mul_left ?_ ?_
  · rw [← map_pow]
    exact ((Commute.refl (frob h)).zpow_left _).pow_right _ |>.map ρ
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ ⟨_, τ, rfl⟩)
    rw [hk, pow_mul]
    exact (hc ⟨_, τ, rfl⟩).pow_right k

theorem isSemisimple_apply (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) (σ : Weil h) : End.IsSemisimple (ρ σ) := by
  classical
  obtain ⟨m, hm, hc⟩ := exists_pow_frob_comm ρ hρ
  refine isSemisimple_of_isSemisimple_frob E Ω A w h V ρ hρ (frob h) deg_frob
    (FrobSemisimple.isSemisimple_of_pow ((Group.isUnit _).map ρ) hm ?_) σ
  set T := ρ (frob h) ^ m with hT
  let p : ℂ[X] := ∏ μ ∈ (minpoly ℂ T).roots.toFinset, (X - C μ)
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := p)
    (Separable.squarefree (separable_prod_X_sub_C_iff'.2 fun _ _ _ _ e => e)) ?_
  have hcp : ∀ g, Commute (ρ g) (aeval T p) := fun g => by
    simp only [p, map_prod]
    rw [aeval_eq_sum_range]
    exact Commute.sum_right _ _ _ fun i _ => ((hc g).pow_right i).smul_right _
  let K : Subrepresentation ρ := ⟨LinearMap.ker (aeval T p), fun g v hv => by
    rw [LinearMap.mem_ker, ← End.mul_apply, ← (hcp g).eq, End.mul_apply, LinearMap.mem_ker.1 hv,
      map_zero]⟩
  obtain ⟨Q, hQ⟩ := hss.exists_isCompl K
  have hinf : K.toSubmodule ⊓ Q.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hQ.inf_eq_bot
  have hsup : K.toSubmodule ⊔ Q.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hQ.sup_eq_top
  have hQT : ∀ v ∈ Q.toSubmodule, T v ∈ Q.toSubmodule := fun v hv => by
    rw [hT, ← map_pow]; exact Q.apply_mem_toSubmodule _ hv
  have hQ0 : Q.toSubmodule = ⊥ := by
    by_contra hne
    haveI : Nontrivial Q.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := End.exists_eigenvalue (T.restrict hQT)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv1 : T v = μ • (v : V) := congrArg Subtype.val hv.apply_eq_smul
    have hv0 : (v : V) ≠ 0 := fun e => hv.2 (Subtype.ext e)
    have hvT : End.HasEigenvector T μ v := ⟨End.mem_eigenspace_iff.2 hv1, hv0⟩
    have hroot : μ ∈ (minpoly ℂ T).roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots (minpoly.ne_zero_of_finite ℂ T)]
      exact End.hasEigenvalue_iff_isRoot.1 (End.hasEigenvalue_of_hasEigenvector hvT)
    have hK : (v : V) ∈ K.toSubmodule := by
      show aeval T p v = 0
      rw [End.aeval_apply_of_hasEigenvector hvT, show p.eval μ = 0 from ?_, zero_smul]
      simp only [p, eval_prod]
      exact Finset.prod_eq_zero hroot (by simp)
    exact hv0 ((Submodule.mem_bot ℂ).1 (hinf ▸ Submodule.mem_inf.2 ⟨hK, v.2⟩))
  rw [hQ0, sup_bot_eq] at hsup
  exact LinearMap.ker_eq_top.1 hsup

def wdOfRep (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ρ.IsSemisimpleRepresentation) : WDRep h V where
  ρ := ρ
  N := 0
  smooth := hρ
  semisimple := isSemisimple_apply ρ hρ hss
  nilpotent := IsNilpotent.zero
  comm σ := by simp


variable (h) in
abbrev IrrW : Type := {x : WD h // IsIrrWD x}

theorem isIrrWD_mk (a : WDRep h V) : IsIrrWD (WD.mk a) ↔ a.ρ.IsIrreducible := by
  constructor
  · rintro ⟨n, b, hb, hirr⟩
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.1 hb
    exact IrrDecomp.isIrreducible_of_equiv e he hirr
  · intro hirr
    obtain ⟨e, he, -⟩ := WD.iso_std a
    exact ⟨_, (WD.std a).2, (WD.sound (WD.iso_std _)).symm, IrrDecomp.isIrreducible_of_equiv e he hirr⟩

theorem nontrivial_of_irr {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem N_eq_zero_of_irr (a : WDRep h V) (hirr : a.ρ.IsIrreducible) : a.N = 0 := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
  let S : Subrepresentation a.ρ := ⟨LinearMap.ker a.N, fun σ v hv => by
    have h1 := a.comm_apply σ v
    rw [LinearMap.mem_ker.1 hv, map_zero] at h1
    exact LinearMap.mem_ker.2 ((smul_eq_zero.1 h1.symm).resolve_left (zpow_ne_zero _ hq))⟩
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hinj : Function.Injective a.N := by
      rw [← LinearMap.ker_eq_bot]
      exact congrArg Subrepresentation.toSubmodule hS
    obtain ⟨m, hm⟩ := a.nilpotent
    have hinj' : Function.Injective (a.N ^ m) := by
      rw [End.coe_pow]; exact hinj.iterate m
    rw [hm] at hinj'
    have := nontrivial_of_irr hirr
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hinj' (a₁ := v) (a₂ := 0) (by simp))
  · exact LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule hS)

theorem IrrW.mono0 (z : IrrW h) : z.1.mono0 := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff a).2 (N_eq_zero_of_irr a ha)

theorem IrrW.lpDim_pos (z : IrrW h) : 0 < z.1.lpDim := by
  obtain ⟨_, n, a, rfl, ha⟩ := z
  have := nontrivial_of_irr ha
  show 0 < (WD.mk a).lpDim
  rw [WD.lpDim_mk]
  exact finrank_pos

theorem isIrrWD_lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IsIrrWD (WD.lpOfChar h χ hχ) := by
  refine ⟨1, _, rfl, ?_⟩
  haveI : IsSimpleModule ℂ (Fin 1 → ℂ) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · exact bot_ne_top (α := Submodule ℂ (Fin 1 → ℂ)) (congrArg Subrepresentation.toSubmodule hbt)
  · rcases eq_bot_or_eq_top U.toSubmodule with hU | hU
    · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
    · exact Or.inr (Subrepresentation.toSubmodule_injective hU)

def IrrW.ofChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : IrrW h :=
  ⟨WD.lpOfChar h χ hχ, isIrrWD_lpOfChar χ hχ⟩


variable (h) in
def frobCoset (r : ℕ) : Set (Weil h) := {τ | deg τ = -(r : ℤ)}

@[simp] theorem mem_frobCoset {r : ℕ} {τ : Weil h} : τ ∈ frobCoset h r ↔ deg τ = -(r : ℤ) := Iff.rfl




section Artin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Artin


variable (h) in
abbrev VR : Type := IrrW h →₀ ℚ

namespace VR






end VR

end GlobalTheory.VWeil
end
end

