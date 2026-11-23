module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ExistsNonzeroLowerEntryOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AdjointInertiaImageFinite
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

open UpperTheory.V.Z.Win UpperTheory.GalN.V

private theorem split_of_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {p : Polynomial K} (a b : K'ˣ)
    (h : p.map e.toRingHom = (Polynomial.X - Polynomial.C (a : K')) * (Polynomial.X - Polynomial.C (b : K'))) :
    ∃ a' b' : Kˣ, e a' = a ∧ e b' = b ∧
      p = (Polynomial.X - Polynomial.C (a' : K)) * (Polynomial.X - Polynomial.C (b' : K)) := by
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom a, Units.map e.symm.toRingHom.toMonoidHom b, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Polynomial.map_injective e.toRingHom e.injective
    rw [h]
    simp

private theorem roots3 {K : Type} [Field K] {p : Polynomial K} {a b c : K}
    (h : p = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C c)) :
    p.IsRoot a ∧ p.IsRoot b ∧ p.IsRoot c := by
  subst h
  simp

private theorem link_false {l : ℕ} [Fact l.Prime] {x : Matrix.GeneralLinearGroup (Fin 3) (Qbar l)} {Q : ℕ} (hn : NoLink x Q) (c : Qbar l) (h0 : c ≠ 0)
    (r0 : x.val.charpoly.IsRoot c)
    (r1 : x.val.charpoly.IsRoot 1)
    (r2 : x.val.charpoly.IsRoot c⁻¹)
    {j : ℕ} (hj : j = 1 ∨ j = 2) (hQ : c ^ j = Q ∨ c ^ j * Q = 1) : False := by
  rcases hj with rfl | rfl <;> rcases hQ with e | e
  · exact hn _ _ r0 r1 1 le_rfl (by simpa using e)
  · exact hn _ _ r1 r0 1 le_rfl (by
      simp only [pow_one] at e ⊢
      rw [mul_comm (Q : Qbar l), e])
  · exact hn _ _ r0 r2 1 le_rfl (by
      rw [pow_one, pow_one, ← e]
      field_simp)
  · exact hn _ _ r2 r0 1 le_rfl (by
      rw [pow_one, pow_one]
      exact inv_eq_of_mul_eq_one_right (by linear_combination e))

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime]

private theorem adjoint_inertia_image_finite (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin 2) (Qbar l)}
    {y : WD h} (hx : IsWDOf ι r y) (hy : y.mono0) : (ad0 r '' (Ine (F := L) A : Set (G L Ω))).Finite := by
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  have hN0 : N = 0 := (hN.weilDeligneParam_monodromy_eq_zero_iff hl ht ι).1 (hw ▸ hy)
  subst hN0
  obtain ⟨-, U, hU, H⟩ := hN
  have hu : ∀ σ ∈ U, ad0 r (σ : G L Ω) = 1 := fun σ hσ => by
    have h1 : r (σ : G L Ω) = 1 := Units.ext (by rw [H σ hσ]; simp)
    apply Units.ext
    rw [ad0, tw_val, MonoidHom.inv_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]
    simp
  haveI := compactSpace_Ine (E := L) A
  let f := (ad0 r).comp (Ine (F := L) A).subtype
  haveI : Finite (Ine (F := L) A ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono (H₁ := U) (fun x hx => hu x hx) hU)
  haveI : Finite f.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv
  refine (Set.toFinite (f.range : Set (GL (Fin 3) (Qbar l)))).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, rfl⟩
end

end UpperTheory.V.Z.Sym.W

open UpperTheory.V.Z.Win UpperTheory.GalN.V in
theorem UpperTheory.V.Z.Sym.W.awayW :
    UpperTheory.V.Z.Sym.W.AwayW := by
  intro P L Ω _ _ _ _ _ l _ ι r hr hU w hl τ hg hT
  obtain ⟨ψ, hψ, ⟨e⟩, -⟩ := psOf P.litN L 2 w τ hT
  refine ⟨ψ, hψ, ⟨e⟩, ?_⟩
  intro j hj ε hε hlk
  obtain ⟨A, h⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
  obtain ⟨rc, hrc⟩ := exRec' P.litN h
  have gd : Gd (rc (algNorm τ)) := Gu.plainGd L Ω A w h rc hrc 2 τ hT
  have hx : IsWDOf ι r (rc (algNorm τ)) := ((hg A h rc hrc).1 hl).isWDOf gd
  obtain ⟨a, ha, -⟩ := id hrc
  obtain ⟨s, j', hj', hs, hn⟩ := hU w hl A h (adjoint_inertia_image_finite hl hx gd.2)
  have hact : ActsAs A (normV w) s j' 0 := by
    simp only [ActsAs, pow_zero, pow_one]
    exact hs
  let S : Weil h := ⟨s, j', 0, hact⟩
  have hd : deg S = (j' : ℤ) := by simpa using deg_eq (σ := S) hact
  have hcp := eigW P L Ω l ι 2 r w hl A h a ha τ hg hT ψ hψ
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective) S
  rw [psPol, Fin.prod_univ_two] at hcp
  obtain ⟨a', b', ea, eb, hab⟩ := split_of_map ι _ _ hcp
  have hc := (ad0Facts l (G L Ω) r).2.2.2.2.1 s a' b' hab
  obtain ⟨r0, r1, r2⟩ := roots3 hc
  have hci : ((b' / a' : (Qbar l)ˣ) : Qbar l) = (((a' / b' : (Qbar l)ˣ) : Qbar l))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val, inv_div]
  rw [hci] at r2
  refine link_false hn _ (Units.ne_zero _) r0 r1 r2 hj ?_
  have hc' : ι ((a' / b' : (Qbar l)ˣ) : Qbar l) = ((ψ 0 (a S) / ψ 1 (a S) : ℂˣ) : ℂ) := by
    rw [Units.val_div_eq_div_val, map_div₀, ea, eb, ← Units.val_div_eq_div_val, mul_div_mul_right_eq_div]
  have hv : (ψ 0 (a S) / ψ 1 (a S)) ^ j = absPow (w.adicCompletion L) (ε : ℂ) (a S) := by
    rw [← hlk]
    rfl
  have hz : ι (((a' / b' : (Qbar l)ˣ) : Qbar l) ^ j) = ((absPow (w.adicCompletion L) (ε : ℂ) (a S) : ℂˣ) : ℂ) := by
    rw [map_pow, hc', ← Units.val_pow_eq_pow_val, hv]
  rcases hε with rfl | rfl
  · left
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (1 : ℝ) S
    rw [hd] at h1
    rw [hz, map_natCast]
    simpa using h1
  · right
    apply ι.injective
    have h1 := GlobalTheory.SatChar.absPow_art ha (-1 : ℝ) S
    rw [hd] at h1
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (one_lt_normV w)).ne'
    rw [map_mul, hz, map_natCast, map_one]
    have h2 : ((absPow (w.adicCompletion L) (((-1 : ℤ) : ℂ)) (a S) : ℂˣ) : ℂ) = (((normV w : ℕ) : ℂ)⁻¹) ^ j' := by
      simpa [Complex.cpow_neg_one] using h1
    rw [h2]
    push_cast
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hq)]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.UfOfCharpoly
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem uf_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (g : GL (Fin 2) (Qbar l)) (c : Fin 2 → ℂˣ)
    (h : g.val.charpoly.map ι.toRingHom = ∏ j, (X - C (c j : ℂ))) :
    ι (Ga.uf g) = ((c 0 / c 1 : ℂˣ) : ℂ) + (((c 0 / c 1 : ℂˣ)⁻¹ : ℂˣ) : ℂ) := by
  let e : ℂˣ →* (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom
  have he : ∀ x : ℂˣ, ι ((e x : (Qbar l)ˣ) : Qbar l) = (x : ℂ) := fun x => by simp [e]
  have hc : g.val.charpoly =
      (X - C ((e (c 0) : (Qbar l)ˣ) : Qbar l)) * (X - C ((e (c 1) : (Qbar l)ˣ) : Qbar l)) := by
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [h, Fin.prod_univ_two]
    simp [Polynomial.map_mul, he]
  rw [(Ga.ufFacts _ g).1 _ _ hc]
  simp only [_root_.map_add (f := _), ← _root_.map_div, ← _root_.map_inv, he]

private theorem uf_of_pol {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : GL (Fin 2) (Qbar l)) (φ : Fin 2 → kˣ →* ℂˣ) (x : kˣ)
    (h : g.val.charpoly.map ι.toRingHom = UpperTheory.V.Z.Sym.W.psPol φ x) :
    ι (Ga.uf g) = (((φ 0 / φ 1) x : ℂˣ) : ℂ) + ((((φ 0 / φ 1) x)⁻¹ : ℂˣ) : ℂ) := by
  have e := uf_of_charpoly ι g (fun j => φ j x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) h
  have hx : (φ 0 x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) / (φ 1 x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) =
      (φ 0 / φ 1) x := by
    simp only [MonoidHom.div_apply, mul_div_mul_right_eq_div]
  simp only [hx] at e
  exact e

private theorem two_roots {K : Type} [Field K] (x : Kˣ) :
    (((x ^ 2 : Kˣ) : K) + (((x ^ 2)⁻¹ : Kˣ) : K)) = ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 := by
  have h0 : (x : K) ≠ 0 := x.ne_zero
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  field_simp
  ring

private theorem two_ne {H : Type*} [CommGroup H] {p : H} (ψ : Fin 2 → H) (hp : p ≠ 1) (h0 : ψ 0 / ψ 1 ≠ p)
    (h1 : ψ 0 / ψ 1 ≠ p⁻¹) (i j : Fin 2) : ψ i ≠ ψ j * p := by
  intro e
  fin_cases i <;> fin_cases j
  · exact hp (by simpa using e)
  · exact h0 (by
      have e' : ψ 0 = ψ 1 * p := e
      rw [e', mul_div_cancel_left])
  · exact h1 (by
      have e' : ψ 1 = ψ 0 * p := e
      rw [e', div_mul_cancel_left])
  · exact hp (by simpa using e)

private theorem abs_ne_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro e
  have e' : absPow k (((1 : ℝ)) : ℂ) = absPow k (((0 : ℝ)) : ℂ) := by
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, absPow_zero] using e
  have hinj : ∀ x y : ℝ, absPow k (x : ℂ) = absPow k (y : ℂ) → x = y := by
    intro x y h
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
    have h1 : nabs k ϖ ≠ 1 := fun e => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
    have h2 : nabs k ϖ ^ x = nabs k ϖ ^ y := by
      have hx := GlobalTheory.SmGL.val_absPow_ofReal k x ϖ
      have hy := GlobalTheory.SmGL.val_absPow_ofReal k y ϖ
      rw [h] at hx
      exact_mod_cast hx.symm.trans hy
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
    exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3
  exact one_ne_zero (hinj _ _ e')

private theorem reg_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (h : Reg (ψ 0 / ψ 1)) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  refine two_ne ψ (abs_ne_one k) (fun e => h.2 2 (by norm_num) ?_) (fun e => h.2 (-2) (by norm_num) ?_) i j
  · rw [e]; push_cast; exact two.symm
  · rw [e]; push_cast; rw [absPow_neg, two, inv_pow]

private theorem reg_two {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (a : kˣ →* ℂˣ) (h : Reg a) (e : ψ 0 / ψ 1 = a ^ 2) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  refine two_ne ψ (abs_ne_one k) (fun e' => h.2 1 (by norm_num) ?_) (fun e' => h.2 (-1) (by norm_num) ?_) i j
  · rw [← e, e']; simp
  · rw [← e, e']; simp [absPow_neg]

theorem UpperTheory.V.Z.Sym.W.branch2W :
    UpperTheory.V.Z.Sym.W.Branch2W := by
  intro Pw L Ω _ _ _ _ _ _ l _ ι hl hE M m hM r σ hAd hGal P ψ hGood hReg σ' hσ' hev
  obtain ⟨r', hGal', -⟩ := UpperTheory.V.Z.Sym.W.galExW Pw L Ω l ι hl hE 2 (by norm_num) σ' hσ'
  have hr := Ga.badClosed L Ω l r hGal.cont
  have hr' := Ga.badClosed L Ω l r' hGal'.cont
  let E : Set (G L Ω) := {g | Ga.uf (r' g) = Ga.uf (r g) ^ 2 - 2}
  have hEc : IsClosed E := isClosed_eq hr'.1 ((hr.1.pow 2).sub continuous_const)
  have hstab : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω,
      s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ →
      s' ∈ E → s ∈ E := by
    intro c hc s s' hss hs'
    obtain ⟨Q, hQ⟩ := hGal.pair c hc
    obtain ⟨Q', hQ'⟩ := hGal'.pair c hc
    have e1 := (Ga.ufFacts _ (r s)).2.2.2.1 (r s') Q _ (hQ s s' hss)
    have e2 := (Ga.ufFacts _ (r' s)).2.2.2.1 (r' s') Q' _ (hQ' s s' hss)
    change Ga.uf (r' s') = Ga.uf (r s') ^ 2 - 2 at hs'
    change Ga.uf (r' s) = Ga.uf (r s) ^ 2 - 2
    rw [← e1, ← e2]
    exact hs'
  have hfrob : ∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E := by
    refine hev.mono fun w hw hwP s hs => ?_
    obtain ⟨ψ', ⟨hsm', τ', hc', hq'⟩, hrat⟩ := hw hwP
    obtain ⟨hsp, hlw, hsm, τ, hc, ⟨eqv⟩⟩ := hGood.mem w hwP
    obtain ⟨A, hA, hF⟩ := hs
    obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds L Ω A w hA
    have hq : IsSubquotient τ.ρ (prinSeries (ψ w)) :=
      IsSubquotient.of_injective eqv.toIntertwiningMap eqv.toLinearEquiv.injective
    have hpt : UpperTheory.V.Z.Sym.W.PT τ :=
      UpperTheory.V.Z.Sym.W.plainOf Pw.af.litN L 2 w τ (ψ w) hsm hq (reg_one (ψ w) (hReg w hwP))
    have hpt' : UpperTheory.V.Z.Sym.W.PT τ' :=
      UpperTheory.V.Z.Sym.W.plainOf Pw.af.litN L 2 w τ' ψ' hsm' hq' (reg_two ψ' _ (hReg w hwP) hrat)
    let t : Weil hA := ⟨s, mem_Weil_of_isFrob hA hF⟩
    have c1 := UpperTheory.V.Z.Sym.W.eigW Pw.af L Ω l ι 2 r w hlw A hA a ha τ (hGal.loc w hsp τ hc) hpt (ψ w) hsm hq t
    have c2 := UpperTheory.V.Z.Sym.W.eigW Pw.af L Ω l ι 2 r' w hlw A hA a ha τ' (hGal'.loc w hsp τ' hc') hpt' ψ' hsm' hq' t
    have u1 := uf_of_pol ι (r s) (ψ w) (a t) c1
    have u2 := uf_of_pol ι (r' s) ψ' (a t) c2
    rw [hrat] at u2
    apply ι.injective
    change ι (Ga.uf (r' s)) = ι (Ga.uf (r s) ^ 2 - 2)
    rw [u2, _root_.map_sub, _root_.map_pow, u1, _root_.map_ofNat]
    exact two_roots _
  have hsub := Ga.spread L Ω hE E (Ga.Bad r) hEc hr.2.2 hstab P M hM hGood.meets hfrob
  have hreg := Ga.regElt L Ω l ι M m r hAd.toIn
  have hirr := Ga.sym4Irr l (G L Ω) r hGal.cont hAd.irr
    (fun H hH => let ⟨s, hs, _, a, b, h⟩ := hreg H hH; ⟨s, hs, a, b, h⟩)
  obtain ⟨s, -, hs, -⟩ := hreg ⊤ isOpen_univ
  exact Ga.noKappa l (G L Ω) r r' hirr (Ga.Bad r)ᶜ hr.2.2.isOpen_compl ⟨s, hs⟩ (fun g hg => hsub hg)
end
end

