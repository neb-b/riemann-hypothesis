module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsExtra
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ParamSplitPlace

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → ∀ x' : WD h', IsWDOf ι (r.comp (res F Ω K)) x' → ∃ x : WD h, IsWDOf ι r x ∧ WDRel (RingEquiv.refl Ω) x x' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι n r A v w h h' i hP x' hx'
  obtain ⟨t', ht', φ', hφ', N, b', hN', hb', rfl⟩ := hx'
  obtain ⟨c, hc, hdeg, hq, hsm⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv F Ω A v h K Ω A w h' (RingEquiv.refl Ω) (algebraMap F K) i hP
  have hcz : ∀ (σ : Weil h) (z : Ω), ((c σ : Weil h') : G K Ω) z = (σ : G F Ω) z :=
    fun σ z => ((hc σ (c σ)).2 rfl z).symm
  have hres : ∀ σ : Weil h, res F Ω K ((c σ : Weil h') : G K Ω) = (σ : G F Ω) :=
    fun σ => AlgEquiv.ext fun z => hcz σ z
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G K Ω) ∈ Ine (F := K) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := K) A :=
    (((Weil h').subtype.comp c.toMonoidHom).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  have hez : ∀ (σ : Ine (F := F) A) (z : Ω), ((e σ : Ine (F := K) A) : G K Ω) z = (σ : G F Ω) z := fun σ z => by
    have := hcz (ineIncl h σ) z
    rwa [coe_ineIncl] at this
  have he_surj : Function.Surjective e := by
    intro τ
    have hm' : ((c.symm (ineIncl h' τ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, ← hdeg, MulEquiv.apply_symm_apply, deg_ineIncl]
    refine ⟨⟨_, hm'⟩, Subgroup.inclusion_injective (Ine_le_Weil h') ?_⟩
    show ineIncl h' (e _) = ineIncl h' τ
    rw [he]
    have : ineIncl h ⟨_, hm'⟩ = c.symm (ineIncl h' τ) := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have he_cont : Continuous e := by
    refine continuous_of_continuousAt_one e ?_
    rw [ContinuousAt, map_one, tendsto_subtype_rng]
    intro O' hO'
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω K Ω (RingEquiv.refl Ω) O' hO'
    refine Filter.mem_map.2 (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) ?_)
    intro τ hτ
    exact hUO (τ : G F Ω) hτ ((e τ : Ine (F := K) A) : G K Ω) fun z => (hez τ z).symm

  let t : Ine (F := F) A →* Multiplicative ℤ_[l] := t'.comp e
  have ht : IsTameChar t := ⟨ht'.1.comp he_cont, ht'.2.comp he_surj⟩
  have hφ : deg (c.symm φ') = 1 := by rw [← hdeg, MulEquiv.apply_symm_apply, hφ']
  have hN : IsMonodromy t r N := by
    obtain ⟨hnil, U', hU', H⟩ := hN'
    refine ⟨hnil, U'.comap e, hU'.preimage he_cont, fun σ hσ => ?_⟩
    have h1 := H (e σ) hσ
    have h2 : res F Ω K ((e σ : Ine (F := K) A) : G K Ω) = (σ : G F Ω) := AlgEquiv.ext fun z => hez σ z
    rw [MonoidHom.comp_apply, h2] at h1
    exact h1
  have hpart : ∀ g : Weil h, e (inePart hφ g) = inePart hφ' (c g) := fun g =>
    Subgroup.inclusion_injective (Ine_le_Weil h') (by
      show ineIncl h' _ = ineIncl h' _
      rw [he, ineIncl_inePart, ineIncl_inePart, map_mul, map_inv, map_zpow, MulEquiv.apply_symm_apply, hdeg])
  have key : ∀ g : Weil h, wdMat t hφ r N g = wdMat t' hφ' (r.comp (res F Ω K)) N (c g) := fun g => by
    rw [wdMat, wdMat, ← hpart]
    show (r (g : G F Ω) : Matrix (Fin n) (Fin n) (Qbar l)) * _ =
      (r (res F Ω K ((c g : Weil h') : G K Ω)) : Matrix (Fin n) (Fin n) (Qbar l)) * _
    rw [hres]
    rfl

  let b : WDRep h (Fin n → ℂ) :=
    { ρ := b'.ρ.comp c.toMonoidHom
      N := b'.N
      smooth := (hsm _ b'.ρ).1 b'.smooth
      semisimple := fun σ => b'.semisimple (c σ)
      nilpotent := b'.nilpotent
      comm := fun σ => by
        have := b'.comm (c σ)
        rwa [hdeg, hq] at this }
  refine ⟨WD.mk b, ⟨t, ht, c.symm φ', hφ, N, b, hN, ⟨hb'.1, fun g => ?_⟩, rfl⟩,
    ⟨_, b, b', rfl, rfl, rfl, fun σ σ' hσ => ?_⟩⟩
  · show Commute (b'.ρ (c g)) _ ∧ IsNilpotent (_ - b'.ρ (c g))
    simpa only [key] using hb'.2 (c g)
  · show b'.ρ (c σ) = b'.ρ σ'
    rw [(hc σ σ').1 hσ]

end GlobalTheory.ParamSplitPlace
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegIsSquare
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.PrimesNegSquare

open Polynomial

theorem isSquare_neg_of_dvd (q : ℕ) [Fact q.Prime] (p : ℕ) (h : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) :
    IsSquare (-(p : ℚ_[q])) := by
  obtain ⟨c, hc⟩ := h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have h2pos : 0 < ‖(2 : ℤ_[q])‖ := norm_pos_iff.mpr two_ne_zero
  have h2le : ‖(2 : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hcle : ‖((c : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hqn : ‖((q : ℕ) : ℤ_[q])‖ = (q : ℝ)⁻¹ := PadicInt.norm_p
  have key : ‖(((p : ℤ) + 1 : ℤ) : ℤ_[q])‖ < ‖(2 : ℤ_[q])‖ ^ 2 := by
    rw [hc]
    push_cast
    have e8 : (8 : ℤ_[q]) = 2 ^ 3 := by norm_num
    rw [e8, norm_mul, norm_mul, norm_pow, hqn]
    have hqinv : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have hqinv0 : 0 < (q : ℝ)⁻¹ := by positivity
    calc ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ * ‖((c : ℤ) : ℤ_[q])‖
        ≤ ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ := by
          apply mul_le_of_le_one_right (by positivity) hcle
      _ < ‖(2 : ℤ_[q])‖ ^ 2 * 1 := by
          rw [pow_succ, mul_assoc]
          apply mul_lt_mul_of_pos_left _ (by positivity)
          calc ‖(2 : ℤ_[q])‖ * (q : ℝ)⁻¹ ≤ 1 * (q : ℝ)⁻¹ := by gcongr
            _ < 1 := by simpa using hqinv
      _ = ‖(2 : ℤ_[q])‖ ^ 2 := mul_one _
  let F : ℤ[X] := X ^ 2 + C (p : ℤ)
  have hF : ‖aeval (1 : ℤ_[q]) F‖ < ‖aeval (1 : ℤ_[q]) (derivative F)‖ ^ 2 := by
    have e1 : aeval (1 : ℤ_[q]) F = (((p : ℤ) + 1 : ℤ) : ℤ_[q]) := by
      simp [F]; ring
    have e2 : aeval (1 : ℤ_[q]) (derivative F) = 2 := by
      simp [F]
      exact map_ofNat _ 2
    rw [e1, e2]; exact key
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  have hz' : z ^ 2 + (p : ℤ_[q]) = 0 := by simpa [F] using hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + (p : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at this
  linear_combination -this

theorem infinite_primes_neg_isSquare : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  intro q _
  have hq0 : (8 * q) ≠ 0 := by
    have := (Fact.out : q.Prime).pos; omega
  haveI : NeZero (8 * q) := ⟨hq0⟩
  have hu : IsUnit (-1 : ZMod (8 * q)) := isUnit_one.neg
  refine (Nat.infinite_setOfPred_prime_and_eq_mod hu).mono ?_
  rintro p ⟨hp, hpe⟩
  refine ⟨hp, GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_⟩
  have : (((p : ℤ) + 1 : ℤ) : ZMod (8 * q)) = 0 := by
    push_cast; rw [hpe]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

end GlobalTheory.RealGal.PrimesNegSquare
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsoComm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocCompCLit

open Matrix

section

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩

private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩

end

end GlobalTheory.LocCompCLit
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionIso

open ValuativeRel

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem valuation_le_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) ≤ 1) : valuation k x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : valuation k x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
  have h2 := GlobalTheory.TypeRec.TwistInert.valuation_lt_one_map f.toRingHom hf h1
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀] at h2
  exact absurd ((inv_lt_one₀ hw).1 h2) (not_lt.2 hx)

theorem valuation_lt_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) < 1) : valuation k x < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : x⁻¹ ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h
  have h2 := GlobalTheory.LastCompare.map_mem_integer f.toMonoidHom hf h1
  rw [Valuation.mem_integer_iff] at h2
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  have h3 : valuation k' (f x⁻¹) ≤ 1 := h2
  rw [map_inv₀, map_inv₀] at h3
  exact absurd hx (not_lt.2 ((inv_le_one₀ hw).1 h3))

variable (f : k ≃+* k') (hf : Continuous f) {n : Type} [Fintype n] [DecidableEq n]

theorem map_map_symm (h : GL n k') :
    Matrix.GeneralLinearGroup.map f.toRingHom (Matrix.GeneralLinearGroup.map f.symm.toRingHom h) = h := by
  ext a b
  simp


include hf in
theorem map_symm_mem_KO {h : GL n k'} (hh : h ∈ GlobalTheory.SplitWeil.KO k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SplitWeil.KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  let j : 𝒪[k'] →+* 𝒪[k] := (f.symm.toRingHom.comp (algebraMap 𝒪[k'] k')).codRestrict 𝒪[k] (fun y => by
      show valuation k (f.symm (y : k')) ≤ 1
      apply valuation_le_one_of_map f hf
      rw [RingEquiv.apply_symm_apply]
      exact y.2)
  refine ⟨Matrix.GeneralLinearGroup.map j h0, ?_⟩
  ext a b
  simp [j] <;> rfl


include hf in
theorem map_symm_mem_iwahori [LinearOrder n] {h : GL n k'} (hh : h ∈ GlobalTheory.SmGL.iwahori k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SmGL.iwahori k n := by
  rw [GlobalTheory.SmGL.mem_iwahori] at hh ⊢
  refine ⟨map_symm_mem_KO f hf hh.1, fun a b hab => ?_⟩
  apply valuation_lt_one_of_map f hf
  have := hh.2 a b hab
  simpa using this

end Val

theorem fixed_ne_bot_transfer {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') (φ : G →* G')
    (ψ : G' → G) (hψ : ∀ g, φ (ψ g) = g) (e : V ≃ₗ[ℂ] V') (he : ∀ g x, e (ρ g x) = ρ' (φ g) (e x))
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ h ∈ H', ψ h ∈ H) :
    GlobalTheory.PRep.fixed ρ H ≠ ⊥ → GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx' : ∀ h : H, ρ (h : G) x = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • x := hx
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, by simpa using hx0⟩
  show ∀ h : H', ρ' (h : G') (e x) = (((1 : H' →* ℂˣ) h : ℂˣ) : ℂ) • e x
  intro h
  have h1 := hx' ⟨ψ h, hH h h.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  rw [← hψ h, ← he, h1]

theorem iwahori_spherical_transfer : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  intro F K _ _ _ _ v w i hi a σ σ' e he
  exact ⟨fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_iwahori i hi hh),
    fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_KO i hi hh)⟩

end GlobalTheory.CompletionIso
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.NormVUnderPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttResTower

theorem normV_under_pow {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem two_le_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem under_under {F K M : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] (w : HeightOneSpectrum (𝓞 M)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ w.asIdeal) = Ideal.comap _ w.asIdeal
  rw [Ideal.comap_comap]
  congr 1
  ext x
  first
  | exact (IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 K) (𝓞 M)).symm ▸ rfl
  | (apply RingOfIntegers.coe_injective; simp only [RingHom.comp_apply, RingOfIntegers.algebraMap_coe]; exact (IsScalarTower.algebraMap_apply F K M (x : F)).symm)
  | (apply RingOfIntegers.ext; simp [IsScalarTower.algebraMap_apply F K M])

end GlobalTheory.AttResTower

theorem GlobalTheory.AttResTower.attRes_comp_res : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), AttRes π ι K r → AttRes π ι M (r.comp (res K Ω M)) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a π r hatt
  unfold AttRes at hatt ⊢
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hatt] with w h f hf
  have huv := GlobalTheory.AttResTower.under_under (F := F) (K := K) w
  have h1 := GlobalTheory.AttResTower.normV_under_pow (K := F) (w.under (𝓞 K))
  have h2 := GlobalTheory.AttResTower.normV_under_pow (K := K) w
  obtain ⟨B, hB, hF⟩ := h _ h1
  rw [huv] at hB hF h1
  refine ⟨B, hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ h2).1 a r _ hF
  have hff : f = (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective (GlobalTheory.AttResTower.two_le_normV (w.under (𝓞 F)))
    simp only
    rw [← hf, h2, h1, ← pow_mul]
  rw [Multiset.map_map] at h3
  rw [hff]
  convert h3 using 2
  simp [Function.comp_def, pow_mul]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RangeRes
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.SignChar

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem range_res (K : IntermediateField F Ω) :
    (res F Ω ↥K).range = K.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro hσ
    exact ⟨IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩, by ext x; rfl⟩

theorem index_fix [IsAlgClosure F Ω] (Q : QCM F Ω) :
    Q.K.fixingSubgroup.index = 2 ∧ IsOpen (Q.K.fixingSubgroup : Set (G F Ω)) := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_eq_succ Q.two
  exact ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index, Q.two], Q.K.fixingSubgroup_isOpen⟩


open Classical in
noncomputable def sign [IsAlgClosure F Ω] (Q : QCM F Ω) : G F Ω →* ℤˣ where
  toFun σ := if σ ∈ Q.K.fixingSubgroup then 1 else -1
  map_one' := by simp [Subgroup.one_mem]
  map_mul' a b := by
    have h := Subgroup.mul_mem_iff_of_index_two (index_fix Q).1 (a := a) (b := b)
    by_cases ha : a ∈ Q.K.fixingSubgroup <;> by_cases hb : b ∈ Q.K.fixingSubgroup
    · rw [if_pos (h.2 (iff_of_true ha hb)), if_pos ha, if_pos hb, mul_one]
    · rw [if_neg (fun hab => hb ((h.1 hab).1 ha)), if_pos ha, if_neg hb, one_mul]
    · rw [if_neg (fun hab => ha ((h.1 hab).2 hb)), if_neg ha, if_pos hb, mul_one]
    · rw [if_pos (h.2 (iff_of_false ha hb)), if_neg ha, if_neg hb]; decide

theorem ker_sign [IsAlgClosure F Ω] (Q : QCM F Ω) : (sign Q).ker = Q.K.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker]
  simp only [sign, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

theorem QCM.ext' {Q Q' : QCM F Ω} (h : Q.K = Q'.K) : Q = Q' := by
  cases Q; cases Q'; cases h; rfl

theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ η : QCM F Ω → (G F Ω →* ℤˣ), Function.Injective η ∧ ∀ Q, (η Q).ker = (res F Ω ↥Q.K).range ∧ IsOpen ((η Q).ker : Set (G F Ω)) := by
  intro F Ω _ _ _ _ _
  refine ⟨sign, ?_, fun Q => ⟨by rw [ker_sign, range_res], by rw [ker_sign]; exact (index_fix Q).2⟩⟩
  intro Q Q' h
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hk : Q.K.fixingSubgroup = Q'.K.fixingSubgroup := by rw [← ker_sign, ← ker_sign, h]
  apply QCM.ext'
  rw [← InfiniteGalois.fixedField_fixingSubgroup Q.K, ← InfiniteGalois.fixedField_fixingSubgroup Q'.K, hk]

end GlobalTheory.RealGal.SignChar
end

