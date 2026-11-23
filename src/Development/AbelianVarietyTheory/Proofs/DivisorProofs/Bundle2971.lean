module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedThetaSectionNonzeroEveryFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_zsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (J : TateIso D k Q act e) (n : ℕ) (m : ℤ) (x : D.La) :
    J.ev n (m • x) = J.ev n x ^ m := by
  let f : Multiplicative D.La →* Q :=
    MonoidHom.mk' (fun y => J.ev n (Multiplicative.toAdd y)) (fun a b => J.add n _ _)
  have h := map_zpow f (Multiplicative.ofAdd x) m
  rw [← ofAdd_zsmul] at h
  exact h

theorem mul_mem_M (l : Level H) {x y : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (hy : y ∈ l.Mb) :
    ∃ r : 𝓞 E, x * y = r * (l.M : 𝓞 E) := by
  have h : y * x ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hy hx
  rw [l.prod, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by rw [mul_comm, ← hr]⟩

theorem smul_mem_M {D : Datum H} (l : Level H) {x : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    {b : D.La} (hb : b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c : D.La, x • b = l.M • c := by
  refine Submodule.smul_induction_on (p := fun b => ∃ c : D.La, x • b = l.M • c) hb ?_ ?_
  · intro y hy t _
    obtain ⟨r, hr⟩ := mul_mem_M l hx hy
    refine ⟨r • t, ?_⟩
    rw [← mul_smul, hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  · rintro b1 b2 ⟨c1, hc1⟩ ⟨c2, hc2⟩
    exact ⟨c1 + c2, by rw [smul_add, hc1, hc2, smul_add]⟩

theorem dvd_EF (D : Datum H) (l : Level H) {a c : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (hc : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : (l.M : ℤ) ∣ D.EF a c := by
  refine Submodule.smul_induction_on (p := fun a => (l.M : ℤ) ∣ D.EF a c) ha ?_ ?_
  · intro y hy t _
    show (l.M : ℤ) ∣ D.EF (y • t) c
    rw [D.adj]
    have hy' : H.bar y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hy
    obtain ⟨c', hc'⟩ := smul_mem_M l hy' hc
    rw [hc', map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro x y hx hy
    show (l.M : ℤ) ∣ D.EF (x + y) c
    rw [map_add (f := _), LinearMap.add_apply]
    exact dvd_add hx hy

end GlobalTheory.LowDat.Uniq

namespace GlobalTheory.LowDat


open GlobalTheory.LowDat.Uniq in
theorem tateIso_ev_lcm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
    (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
    (∀ a, J.ev l.A a = J'.ev l.A a) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
    ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  intro E _ _ _ H D l k _ Q _ act e huniq J J' hζ hA hM
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hA0 := l.A_pos

  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left l.M l.A
  obtain ⟨kk, hkk⟩ := Nat.gcd_dvd_right l.M l.A
  have hgl : Nat.gcd l.M l.A * l.M' = l.M * l.A := Nat.gcd_mul_lcm _ _
  have hg0 : 0 < Nat.gcd l.M l.A := Nat.gcd_pos_of_pos_left _ hM0
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := l.M) (n := l.A) hg0
  generalize Nat.gcd l.M l.A = G at hj hkk hgl hg0 hcop0
  have hMk : l.M' = l.M * kk := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hkk]; ring)
  have hAj : l.M' = l.A * j := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hj]; ring)
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj; omega
    · exact h
  have hk0 : 0 < kk := by
    rcases Nat.eq_zero_or_pos kk with h | h
    · rw [h, mul_zero] at hkk; omega
    · exact h
  have hcop : Nat.Coprime j kk := by
    have e1 : l.M / G = j := by rw [hj]; exact Nat.mul_div_cancel_left j hg0
    have e2 : l.A / G = kk := by rw [hkk]; exact Nat.mul_div_cancel_left kk hg0
    rw [e1, e2] at hcop0; exact hcop0
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop

  have hζM : J.ζ l.M = J'.ζ l.M := by
    rw [← J.ζ_pow l.M kk hM0 hk0, ← J'.ζ_pow l.M kk hM0 hk0, ← hMk, hζ]

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨f, hf, g2, hg2, hfg⟩ := Submodule.mem_sup.mp h1
  have decomp : ∀ x : D.La, x = f • x + g2 • x := fun x => by rw [← add_smul, hfg, one_smul]

  have key : ∀ b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M b = J'.ev l.M b := by
    intro b hb
    have hord : (J'.ev l.M b) ^ l.M = 1 := (J'.onto l.M hM0 _).mpr ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := (J.onto l.M hM0 _).mp hord
    have h2 : J.ev l.M (g2 • b') = 1 := by
      rw [J.lin, hb', ← J'.lin]
      obtain ⟨c, hc⟩ := smul_mem_M (D := D) l hg2 hb
      rw [hc]; exact (J'.ker l.M hM0 _).mpr ⟨c, rfl⟩
    have hb'' : J.ev l.M (f • b') = J'.ev l.M b := by
      have h := J.add l.M (f • b') (g2 • b')
      rw [← decomp b', h2, _root_.mul_one] at h
      rw [← hb', h]
    have hf' : f • b' ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hf Submodule.mem_top
    set c := b - f • b' with hcdef
    have hcm : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.sub_mem _ hb hf'
    have hdiv : ∀ a, (l.M : ℤ) ∣ D.EF a c := by
      intro a
      rw [decomp a, map_add (f := _), LinearMap.add_apply]
      refine dvd_add (dvd_EF D l (Submodule.smul_mem_smul hf Submodule.mem_top) hcm) ?_
      have hga : g2 • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
        Submodule.smul_mem_smul hg2 Submodule.mem_top
      have i1 := J.isom l.M hM0 (g2 • a) (f • b')
      have i2 := J'.isom l.M hM0 (g2 • a) b
      rw [hM _ hga, hb'', hζM] at i1
      have heq := huniq l.M hM0 _ _ _ _ i1 i2
      rw [← (J'.ζ_prim l.M hM0).zpow_eq_one_iff_dvd, hcdef, map_sub, zpow_sub, heq, mul_inv_cancel]
    have hdiv' : ∀ a, (l.M : ℤ) ∣ D.EF c a := fun a => by
      have h := D.alt (a + c)
      simp only [map_add (f := _), LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h
      have h' : D.EF c a = - D.EF a c := by linarith
      rw [h']; exact (hdiv a).neg_right
    choose q hq using hdiv'
    have hMne : (l.M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
    let φ : D.La →ₗ[ℤ] ℤ :=
      { toFun := q
        map_add' := fun x y => by
          apply mul_left_cancel₀ hMne
          rw [← hq, mul_add, ← hq, ← hq, map_add (f := _)]
        map_smul' := fun m x => by
          apply mul_left_cancel₀ hMne
          rw [← hq, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hq, map_zsmul, smul_eq_mul] }
    obtain ⟨c0, hc0⟩ := D.unimod.2 φ
    have hc : c = l.M • c0 := by
      apply D.unimod.1
      ext a
      rw [map_nsmul, LinearMap.smul_apply, hc0, nsmul_eq_mul]
      exact hq a
    have hJc : J.ev l.M c = 1 := (J.ker l.M hM0 _).mpr ⟨c0, hc⟩
    have hbc : b = f • b' + c := by rw [hcdef]; abel
    rw [hbc, J.add, hJc, _root_.mul_one, hb'', ← hbc]
  have hall : ∀ a, J.ev l.M a = J'.ev l.M a := by
    intro a
    rw [decomp a, J.add, J'.add, key _ (Submodule.smul_mem_smul hf Submodule.mem_top),
      hM _ (Submodule.smul_mem_smul hg2 Submodule.mem_top)]

  have expand : ∀ (K : TateIso D k Q act e) (a : D.La),
      K.ev l.M' a = K.ev l.A (u • a) * K.ev l.M (v • a) := by
    intro K a
    have ha : a = (j : ℤ) • (u • a) + (kk : ℤ) • (v • a) := by
      rw [smul_smul, smul_smul, ← add_smul, mul_comm (j : ℤ), mul_comm (kk : ℤ), huv, one_smul]
    conv_lhs => rw [ha]
    rw [K.add, ev_zsmul K l.M' (j : ℤ) (u • a), ev_zsmul K l.M' (kk : ℤ) (v • a), zpow_natCast, zpow_natCast]
    congr 1
    · have h := K.tower l.A j hA0 hj0 (u • a); rw [← hAj] at h; exact h
    · have h := K.tower l.M kk hM0 hk0 (v • a); rw [← hMk] at h; exact h
  intro a
  rw [expand J, expand J', hA, hall]

end GlobalTheory.LowDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantBundlePowEightIsoDetHodgePowFour
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyZh

theorem lft_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  intro o Ω _ _ _ _ M
  have := M.lft
  have hft : Algebra.FiniteType ℤ o := (inferInstance : ZH.ArithBase o Ω).ft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

theorem charZero_of_arithBase : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (M : ZH.RatModel o Ω), CharZero Γ(M.Z, ⊤) := by
  intro o Ω _ _ _ _ M
  have hne : ((⊤ : M.Z.Opens) : Set M.Z).Nonempty := ⟨genericPoint M.Z, trivial⟩
  have := (inferInstance : ZH.ArithBase o Ω).char
  exact (M.res ⊤ hne).charZero

theorem unifAlong_of_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), UnifAlong Zh.G Zh.L.L := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh V _ _ _ _ hc _ ξ hne _
  obtain ⟨D, A, U, hU, -⟩ := Zh.unif V inferInstance inferInstance hc ξ hne
  exact ⟨D, A, U, hU⟩

theorem key_zh : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), 1 ≤ S.g → S.Over₀ M U₀ → IsOpen (abLocus Zh.G) → ∀ (δ : LB M.Z) (t : S.Gam → δ.Sec), δ.IsLB → (⨆ a, nonzeroLocus (t a)) = ⊤ → ZM.SecCoord δ t M.pt S.th → LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge Zh.G S.g) 4) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hg hO hab δ t hδ hcov hsc
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.KeyTheta.exists_nzFib o Ω S ρ M U₀ EE Zh hO δ t hδ hcov hsc
    (fun a z hz => _root_.GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus o Ω M δ t S.th hδ hsc a z hz)
  exact _root_.GlobalTheory.KeyEvenClosing.keyGlob M.Z (M.s ≫ spMap (algebraMap ℤ o)) Zh.G S.g Zh.L δ σ hg inferInstance hO.normal
    (lft_of_arithBase o Ω M) (charZero_of_arithBase o Ω M) Zh.semi Zh.dim (_root_.GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty o Ω S ρ M U₀ EE Zh hO) hab
    Zh.sym hδ Zh.pol (unifAlong_of_zhOut o Ω S ρ M U₀ EE Zh) hσ

end GlobalTheory.KeyZh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapPullO1PowerHodge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.KeyOne

theorem isNormalScheme_of_isOpenImmersion {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (h : Geo.Tor.IsNormalScheme X) : Geo.Tor.IsNormalScheme Y := by
  intro y
  obtain ⟨h1, h2⟩ := h (f y)
  let e : X.presheaf.stalk (f y) ≃+* Y.presheaf.stalk y :=
    (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e⟩

theorem exists_lift_of_dense {P U : Scheme.{0}} (i : U ⟶ P) [IsOpenImmersion i] (hi : Dense (Set.range i))
    {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (a : M.Z ⟶ P) [IsOpenImmersion a] :
    ∃ y : Sp Ω ⟶ U, y ≫ i = M.pt ≫ a := by
  have hV : IsOpen (Set.range a) := a.isOpenEmbedding.isOpen_range
  have hne : (Set.range a).Nonempty := ⟨_, M.pt (IsLocalRing.closedPoint Ω), rfl⟩
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hi.inter_open_nonempty _ hV hne
  have hU : IsOpen (Set.range i) := i.isOpenEmbedding.isOpen_range
  have hsub : Set.range (M.pt ≫ a) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have := ((M.pt_specializes w z).map a.continuous).mem_open hU hz
    simpa using this
  exact ⟨IsOpenImmersion.lift i (M.pt ≫ a) hsub, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
    {Ω : Type} [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X) [IsOpenImmersion io] :
    ∃ y : Sp Ω ⟶ Xo.XF c, M.pt ≫ io = y ≫ Y.j := by
  have hid : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 _ from rfl]
      infer_instance
    infer_instance
  haveI := Y.jQ_open
  obtain ⟨y, hy⟩ := exists_lift_of_dense Y.jQ Y.jQ_dense M (io ≫ inv (pullback.fst Y.s (spMap (RingHom.id c.F))))
  refine ⟨y, ?_⟩
  rw [Model.j, ← Category.assoc, hy, Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : LBIso (A.pull (g ≫ f)) (B.pull (g ≫ f))) : LBIso ((A.pull f).pull g) ((B.pull f).pull g) := by
  have hA' := pull_isLB hA f
  have hB' := pull_isLB hB f
  rw [← CechPic.cls_eq_iff (pull_isLB hA' g) (pull_isLB hB' g), CechPic.cls_pull hA' g, CechPic.cls_pull hB' g,
    CechPic.cls_pull hA f, CechPic.cls_pull hB f, ← CechPic.pull_comp, ← CechPic.pull_comp,
    ← CechPic.cls_pull hA _ (pull_isLB hA _), ← CechPic.cls_pull hB _ (pull_isLB hB _), CechPic.cls_eq_iff]
  exact h

theorem lbIso_pull_lbPow {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) (a b d : ℕ)
    (h : LBIso (lbPow ((lbPow A a).pull f) d) (lbPow ((lbPow B b).pull f) d)) :
    LBIso ((lbPow A (a * d)).pull f) ((lbPow B (b * d)).pull f) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA _) f) (pull_isLB (isLB_lbPow hB _) f),
    CechPic.cls_pull (isLB_lbPow hA _) f, CechPic.cls_pull (isLB_lbPow hB _) f,
    CechPic.cls_lbPow hA, CechPic.cls_lbPow hB]
  rw [← CechPic.cls_eq_iff (isLB_lbPow (pull_isLB (isLB_lbPow hA _) f) _)
    (isLB_lbPow (pull_isLB (isLB_lbPow hB _) f) _), CechPic.cls_lbPow (pull_isLB (isLB_lbPow hA _) f),
    CechPic.cls_lbPow (pull_isLB (isLB_lbPow hB _) f), CechPic.cls_pull (isLB_lbPow hA _) f,
    CechPic.cls_pull (isLB_lbPow hB _) f, CechPic.cls_lbPow hA, CechPic.cls_lbPow hB] at h
  rw [map_nsmul, map_nsmul] at h
  rw [map_nsmul, map_nsmul, mul_nsmul, mul_nsmul, h]

end GlobalTheory.UMin.KeyOne

theorem GlobalTheory.UMin.KeyOne.lbIso_pull_O1_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (io : M.Z ⟶ Y.X), IsOpenImmersion io → io ≫ Y.s = M.s → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).pull io) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial * (n + 1).factorial)).pull io) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf Y g hg Ω _ _ M io hio hs
  haveI := hio
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  have hMn : Geo.Tor.IsNormalScheme M.Z := GlobalTheory.UMin.KeyOne.isNormalScheme_of_isOpenImmersion io Y.normal
  obtain ⟨y, hy⟩ := GlobalTheory.UMin.KeyOne.exists_pt_eq Y M io
  have hpol := _root_.GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (y ≫ pullback.fst _ _)
  obtain ⟨⟨θ, hθ⟩, hθup⟩ := _root_.GlobalTheory.UMin.gen_of_polFib Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.isLB _ Ω _ hpol
  obtain ⟨Ω', _, _, pt, cc, hfd, -, hdeg, hlist, -⟩ := _root_.GlobalTheory.UMin.GalTh.thList_galois Xo.X Xo.univ.t.G Xo.univ.t.PP.L
    Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ m (n + 1) Ω _ θ hm hn hpol
  letI : Algebra c.F Ω' := ((algebraMap Ω Ω').comp (algebraMap c.F Ω)).toAlgebra
  haveI : IsScalarTower c.F Ω Ω' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  obtain ⟨M', π, hM'n, hπf, hπ⟩ := _root_.GlobalTheory.NormCover.exists_normalization_model c.F Ω M Ω' hMn
  have hup := _root_.GlobalTheory.UMin.key_on_cover E H Dw l Xo c o m n f hm hm3 hmu hn hf Y g hg Ω' M' (π ≫ io)
    (spMap (algebraMap Ω Ω') ≫ y) cc hM'n
    (by rw [← Category.assoc, hπ, Category.assoc, hy, Category.assoc])
    (by rw [Category.assoc]; exact ⟨_, pt, hθup _ hθ Ω' (algebraMap Ω Ω'), hlist⟩)
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := pull_isLB (ProjSpace.O1_isLB o n) g
  have hH := (_root_.GlobalTheory.ModelRelDim.relDim_and_isVB_omega E H Dw l Xo c Y).2.isLB_det
  have hA := pull_isLB (isLB_lbPow hO 8) io
  have hB := pull_isLB (isLB_lbPow hH (4 * (n + 1).factorial)) io
  have key := _root_.GlobalTheory.UMin.NormIso.lbIso_lbPow_of_pull c.F Ω M Ω' M' π _ _ (n + 1).factorial hMn hπf hπ hA hB hdeg
    (GlobalTheory.UMin.KeyOne.lbIso_pull_pull (isLB_lbPow hO 8) (isLB_lbPow hH _) io π hup)
  exact GlobalTheory.UMin.KeyOne.lbIso_pull_lbPow hO hH io 8 (4 * (n + 1).factorial) (n + 1).factorial key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClass
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

theorem eq_of_gPt_comp_eq {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {p : ℕ} [Fact p.Prime]
    {y y' : Sp (OO p) ⟶ M.Z} (h : gPt p ≫ y = gPt p ≫ y') : y = y' := by
  haveI := M.sep
  haveI : IsDominant (gPt p) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2 fun x hx => by
      rw [show x = 0 from Subtype.ext hx]
      exact Submodule.zero_mem _⟩
  exact ext_of_isDominant_of_isSeparated M.s
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem val_part_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ (y' : Sp (OO p) ⟶ D.X.M.Z) (h' : y' ≫ D.q = c.y), y' (cPt p) = z₂ → ∀ yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y' h') yy' → D.Compat yy₁ yy' → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy' a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) = D.X.M.val (gPt p ≫ y') (U κ * GSum.part D z₁ z₂ a' κ) := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  obtain ⟨U, hU, hgal⟩ := _root_.GlobalTheory.Poinc.GalPart.exists_root_galois g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz
  refine ⟨U, hU, ?_⟩
  intro p _ c yy₁ hl₁ y h hy yy hl hc y' h' hy' yy' hl' hc' a a' ν ν' κ ha ha' hcong
  haveI := D.fd
  haveI := D.gal
  obtain ⟨σ, s, hs, hys, hval⟩ := _root_.GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q (@GlobalTheory.IsNormalScheme.pred _ X₁.normal)
    (@GlobalTheory.IsNormalScheme.pred _ D.X.normal) D.fin D.gen
    (PadicAlgCl p) (gPt p ≫ y) (gPt p ≫ y') (by rw [Category.assoc, Category.assoc, h, h'])
  obtain rfl : y ≫ s = y' := eq_of_gPt_comp_eq D.X.M (by rw [← Category.assoc, hys])
  obtain ⟨b, hb, hfix, hperm⟩ := hgal σ
  have hlb := _root_.GlobalTheory.Poinc.GalTrans.isLab_conj g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D σ s hs b hb p z₁ c y h h' yy hl
  have hcb : D.Compat yy₁ (yy.comp b.toAddMonoidHom) := fun x μ hx => by
    have := hc x μ hx
    rw [← hfix x] at this
    exact this
  have hyy : ∀ x, yy' x = yy (b x) := fun x =>
    DFunLike.congr_fun (GalLab.rigid D c yy₁ hl₁ (y ≫ s) h' _ yy' hlb hcb hl' hc') x
  have hk := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl).2
  have hk' := (isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ hl').2
  replace hk := hk.trans (congrArg (D.X.S.HH D.X.M) hy)
  replace hk' := hk'.trans (congrArg (D.X.S.HH D.X.M) hy')
  have hHH : ∀ x, b x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂ := fun x => by
    have h1 : b x ∈ yy.ker ↔ x ∈ yy'.ker := by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hyy]
    rwa [hk, hk'] at h1
  rw [hval, hperm hHH,
    _root_.GlobalTheory.Poinc.GSum.part_eq_of_congMod g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D z₁ z₂ hz p c y h hy yy hl a (b a') ν ν' κ ha
      ((hyy a').symm.trans ha') hcong]

end GlobalTheory.Poinc.GSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftsSubEqSumInvariantFields
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeff

theorem isWt_sub {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (V : Y.H.left.Opens) (f g : Γ(Y.H.left, V)) (hf : IsWt Y α V f)
    (hg : IsWt Y α V g) : IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' h h' hq hc
  have e : ∀ (b : Sp S ⟶ Y.H.left), valR b V (f - g) = valR b V f - valR b V g := fun b => by
    unfold valR; split_ifs <;> simp
  rw [e, e, hf S φ x x' c a a' ha ha' h h' hq hc, hg S φ x x' c a a' ha ha' h h' hq hc, mul_sub]

theorem lifts_sub_eq_sum_invFields : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (V : Q.P.A.left.Opens) (D : Derivation ℤ R R) (d d' : Fld Y.H.left), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d' → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f)) → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d' _ f)) → ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ a, IsWt Y 0 _ (h a)) ∧ ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, d O' f - d' O' f = ∑ a, rsT (h a) O' * dd a O' f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hdd V D d d' hd hd' hw hw'
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  let δ : Fld Y.H.left := fun O f => d O f - d' O f
  have hF : IsField (Y.q.left ⁻¹ᵁ V) δ := by
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
    · simp only [δ, hd.1.1 W hW, hd'.1.1 W hW]; ring
    · simp only [δ, hd.1.2.1 W hW, hd'.1.2.1 W hW]; ring
    · simp only [δ, hd.1.2.2 W W' h hW, hd'.1.2.2 W W' h hW, map_sub]
  have hC : ∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0 := fun O hO r => by
    simp only [δ, hd.2 O hO r, hd'.2 O hO r, sub_self]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.VertCoeffRing.exists_coeff R Y.H hsm n v dd hdd _ δ hF hC
  refine ⟨c, _root_.GlobalTheory.Heat.CoeffWt.isWt_coeff R Q O oa Y n v dd hdd V δ hF hC
    (fun α V' hV' f hf => isWt_sub Y α _ _ _ (hw α V' hV' f hf) (hw' α V' hV' f hf)) c hc, fun O' hO' f => hc O' hO' f⟩

end GlobalTheory.VertCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationUnitKernelLeKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  first | (exact @GlobalTheory.ZarhinKer.polUnit_ker_le) | (exact GlobalTheory.ZarhinKer.polUnit_ker_le) | (intros; apply GlobalTheory.ZarhinKer.polUnit_ker_le  <;> assumption)
end

