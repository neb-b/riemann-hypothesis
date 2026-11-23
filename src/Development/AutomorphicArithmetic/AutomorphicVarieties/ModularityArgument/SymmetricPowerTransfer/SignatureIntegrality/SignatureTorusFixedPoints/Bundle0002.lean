module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralOfEv
section
noncomputable section

open ValuativeRel Polynomial UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

section Alg

variable {K : Type} [Field K] {τ a b : K}

private theorem ev_star (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (x : Etau K τ) : ev ha (star x) = ev hb x := by
  show (star x).re + a * (star x).im = x.re + b * x.im
  rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private theorem ev_quo (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (z : (Etau K τ)ˣ) : ev ha (quo z) = ((evU ha z / evU hb z : Kˣ) : K) := by
  show ev ha ((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = _
  rw [map_mul, ev_star ha hb hs, div_eq_mul_inv, ← map_inv, Units.val_mul]
  rfl

private theorem ev_ext (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {x y : Etau K τ} (h1 : ev ha x = ev ha y) (h2 : ev hb x = ev hb y) : x = y := by
  have e1 : x.re + a * x.im = y.re + a * y.im := h1
  have e2 : x.re + b * x.im = y.re + b * y.im := h2
  have him : x.im = y.im := by
    have e3 : (a - b) * (x.im - y.im) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact sub_eq_zero.mp h
  refine QuadraticAlgebra.ext ?_ him
  rw [him] at e1
  linear_combination e1

private theorem ev_exists (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    (u v : K) : ∃ x : Etau K τ, ev ha x = u ∧ ev hb x = v := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨⟨u - a * ((u - v) / (a - b)), (u - v) / (a - b)⟩, ?_, ?_⟩
  · show (u - a * ((u - v) / (a - b))) + a * ((u - v) / (a - b)) = u
    ring
  · show (u - a * ((u - v) / (a - b))) + b * ((u - v) / (a - b)) = v
    field_simp
    ring

private theorem ev_surj (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b) :
    Function.Surjective (evU ha / evU hb) := by
  intro t
  obtain ⟨x, hx1, hx2⟩ := ev_exists ha hb hab (t : K) 1
  obtain ⟨y, hy1, hy2⟩ := ev_exists ha hb hab ((t⁻¹ : Kˣ) : K) 1
  have hxy : x * y = 1 := ev_ext ha hb hab
    (by rw [map_mul, map_one, hx1, hy1, Units.mul_inv])
    (by rw [map_mul, map_one, hx2, hy2, mul_one])
  refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  apply Units.ext
  rw [MonoidHom.div_apply, Units.val_div_eq_div_val]
  show ev ha x / ev hb x = t
  rw [hx1, hx2, div_one]

variable {O : Type} [CommRing O] [Algebra O K]

private theorem ev_algebraMap (ha : a * a = τ * a - 1) (r : O) :
    ev ha (algebraMap O (Etau K τ) r) = algebraMap O K r := by
  show algebraMap O K r + a * 0 = algebraMap O K r
  ring

private theorem isIntegral_ev (ha : a * a = τ * a - 1) {w : Etau K τ} (h : IsIntegral O w) :
    IsIntegral O (ev ha w) := by
  let f : Etau K τ →ₐ[O] K := { ev ha with commutes' := fun r => ev_algebraMap ha r }
  exact h.map f

private theorem isIntegral_of_ev (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {w : Etau K τ} {p q : O} (h1 : ev ha w = algebraMap O K p) (h2 : ev hb w = algebraMap O K q) :
    IsIntegral O w := by
  refine ⟨(X - C p) * (X - C q), (monic_X_sub_C p).mul (monic_X_sub_C q), ?_⟩
  rw [eval₂_mul, eval₂_sub, eval₂_sub, eval₂_X, eval₂_C, eval₂_C]
  apply ev_ext ha hb hab
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h1, sub_self, zero_mul, map_zero]
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h2, sub_self, mul_zero, map_zero]

end Alg

theorem roots : Roots := by
  intro k _ _ _ _ O _ _ hO a ha1
  have hl := root_left (K := k) a
  have hr := root_right (K := k) a
  have hs : (a : k) + ((a⁻¹ : kˣ) : k) = (a : k) + ((a⁻¹ : kˣ) : k) := rfl
  have hs' : ((a⁻¹ : kˣ) : k) + (a : k) = (a : k) + ((a⁻¹ : kˣ) : k) := add_comm _ _
  have hab : (a : k) ≠ ((a⁻¹ : kˣ) : k) := by
    intro h
    have h2 : valuation k (a : k) * valuation k (a : k) = 1 := by
      rw [← map_mul]
      nth_rewrite 2 [h]
      rw [Units.mul_inv, map_one]
    have h3 := pow_lt_one₀ zero_le' ha1 (n := 2) two_ne_zero
    rw [sq, h2] at h3
    exact lt_irrefl _ h3
  have hint : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).mp ⟨x, rfl⟩, fun r hr => (hO.range r).mpr hr⟩
  refine ⟨ev_surj hl hr hab, ?_, fun z => ⟨ev_quo hl hr hs z, ev_quo hr hl hs' z⟩⟩
  ext z
  show (IsIntegral O (quo z) ∧ IsIntegral O (quo z⁻¹)) ↔ valuation k (((evU hl / evU hr) z : kˣ) : k) = 1
  rw [MonoidHom.div_apply]
  have q1 : ev hl (quo z) = ((evU hl z / evU hr z : kˣ) : k) := ev_quo hl hr hs z
  have q2 : ev hr (quo z) = ((evU hr z / evU hl z : kˣ) : k) := ev_quo hr hl hs' z
  have q3 : ev hl (quo z⁻¹) = ((evU hr z / evU hl z : kˣ) : k) := by
    rw [ev_quo hl hr hs z⁻¹, map_inv, map_inv, inv_div_inv]
  have q4 : ev hr (quo z⁻¹) = ((evU hl z / evU hr z : kˣ) : k) := by
    rw [ev_quo hr hl hs' z⁻¹, map_inv, map_inv, inv_div_inv]
  have hprod : valuation k ((evU hl z / evU hr z : kˣ) : k) * valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
    rw [← map_mul, ← Units.val_mul, div_mul_div_comm, mul_comm (evU hr z) (evU hl z), div_self', Units.val_one, map_one]
  constructor
  · rintro ⟨i1, i2⟩
    have v1 : valuation k ((evU hl z / evU hr z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i1)
      rw [q1] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    have v2 : valuation k ((evU hr z / evU hl z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i2)
      rw [q3] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    refine le_antisymm v1 ?_
    calc (1 : ValueGroupWithZero k) = _ := hprod.symm
      _ ≤ valuation k ((evU hl z / evU hr z : kˣ) : k) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hv
    have hv2 : valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
      rw [hv, one_mul] at hprod
      exact hprod
    obtain ⟨p, hp⟩ := (hO.range _).mpr hv.le
    obtain ⟨q, hq⟩ := (hO.range _).mpr hv2.le
    exact ⟨isIntegral_of_ev hl hr hab (q1.trans hp.symm) (q2.trans hq.symm),
      isIntegral_of_ev hl hr hab (q3.trans hq.symm) (q4.trans hp.symm)⟩

end UpperTheory.V.Z.Sym.Sig

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OrbMap
section
open MulAction

namespace UpperTheory.V.Z.Sym.Sig

private theorem relIndex_smul {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (hC : C.Normal)
    (t : T) (y : Y) : (stabilizer T (t • y)).relIndex C = (stabilizer T y).relIndex C := by
  have hc : C.map (MulAut.conj t).toMonoidHom = C := by
    rw [MulEquiv.toMonoidHom_eq_coe, ← Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.normalizer_eq_top_iff.mpr hC]
    exact Subgroup.mem_top t
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← hc]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective

private theorem wcount_congr {T Y Y' : Type} [Group T] [MulAction T Y] [MulAction T Y']
    (C : Subgroup T) (hC : C.Normal) (φ : Y ≃ Y') (hφ : ∀ (t : T) (y : Y), φ (t • y) = t • φ y)
    (k : Y → ℂ) (k' : Y' → ℂ) (hk : ∀ y, k y = k' (φ y)) (hinv : ∀ (t : T) (y : Y'), k' (t • y) = k' y) :
    wcount C k = wcount C k' := by
  have hkT : ∀ (t : T) (y : Y), k (t • y) = k y := by
    intro t y
    rw [hk, hk, hφ, hinv]
  have hst : ∀ y : Y, stabilizer T (φ y) = stabilizer T y := by
    intro y
    ext t
    rw [mem_stabilizer_iff, mem_stabilizer_iff, ← hφ]
    exact φ.injective.eq_iff
  have cls' : ∀ (y z : Y'), z ∈ orbit T y →
      ((stabilizer T z).relIndex C : ℂ) * k' z = ((stabilizer T y).relIndex C : ℂ) * k' y := by
    intro y z h
    obtain ⟨t, rfl⟩ := mem_orbit_iff.mp h
    rw [relIndex_smul C hC, hinv]
  let q : orbitRel.Quotient T Y ≃ orbitRel.Quotient T Y' :=
    Quotient.congr φ (by
      intro a b
      rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
      constructor
      · rintro ⟨t, h⟩
        exact ⟨t, by rw [← hφ, h]⟩
      · rintro ⟨t, h⟩
        exact ⟨t, φ.injective (by rw [hφ, h])⟩)
  unfold wcount
  refine finsum_eq_of_bijective q q.bijective ?_
  intro o
  have hq : q o = Quotient.mk _ (φ (Quotient.out o)) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have ho : Quotient.out (q o) ∈ orbit T (φ (Quotient.out o)) := by
    rw [← orbitRel_apply]
    exact Quotient.exact (by rw [Quotient.out_eq]; exact hq)
  rw [cls' _ _ ho, hst, ← hk]

private def qmap {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') :
    G ⧸ U'.comap e → G' ⧸ U' :=
  Quotient.map' e (by
    intro a b h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa using h)

private theorem qmap_mk {G G' : Type} [Group G] [Group G'] (e : G →* G') (U' : Subgroup G') (g : G) :
    qmap e U' (g : G ⧸ U'.comap e) = (e g : G' ⧸ U') := rfl

private theorem qmap_bij {G G' : Type} [Group G] [Group G'] (e : G →* G') (he : Function.Bijective e)
    (U' : Subgroup G') : Function.Bijective (qmap e U') := by
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [qmap_mk, qmap_mk, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  · intro z
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, rfl⟩ := he.2 c
    exact ⟨a, qmap_mk e U' a⟩

private theorem f_out {G' : Type} [Group G'] (θ' : G' →* G') (U' : Subgroup G') (f : G' → ℂ)
    (hf : ∀ u ∈ U', ∀ x, f (u⁻¹ * x * θ' u) = f x) (x z : G') :
    f ((z : G' ⧸ U').out⁻¹ * x * θ' (z : G' ⧸ U').out) = f (z⁻¹ * x * θ' z) := by
  have hu : z⁻¹ * (z : G' ⧸ U').out ∈ U' :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (z : G' ⧸ U')).symm
  obtain ⟨u, hu, hw⟩ : ∃ u ∈ U', (z : G' ⧸ U').out = z * u :=
    ⟨_, hu, (mul_inv_cancel_left z _).symm⟩
  rw [hw, ← hf u hu (z⁻¹ * x * θ' z)]
  congr 1
  rw [map_mul]
  group

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.orbMap :
    UpperTheory.V.Z.Sym.Sig.OrbMap := by
  classical
  intro T G G' _ _ _ e he ι C θ θ' hθ U' f δ hf hδ hC
  let E : G ≃* G' := MulEquiv.ofBijective e he
  have hc : ∀ (g : G), e (g⁻¹ * δ * θ g) = (e g)⁻¹ * e δ * θ' (e g) := by
    intro g
    rw [map_mul, map_mul, map_inv, hθ]
  refine ⟨?_, ?_, ?_⟩
  · letI : MulAction T (G ⧸ U'.comap e) := MulAction.compHom _ ι
    letI : MulAction T (G' ⧸ U') := MulAction.compHom _ (e.comp ι)
    unfold UpperTheory.V.Z.Sym.orb
    refine UpperTheory.V.Z.Sym.Sig.wcount_congr C hC
      (Equiv.ofBijective _ (UpperTheory.V.Z.Sym.Sig.qmap_bij e he U')) ?_ _ _ ?_ ?_
    · intro t y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
      simp only [Equiv.ofBijective_apply, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.qmap_mk, map_mul, MonoidHom.comp_apply]
    · intro y
      simp only [Equiv.ofBijective_apply]
      conv_rhs => rw [← QuotientGroup.out_eq' y, UpperTheory.V.Z.Sym.Sig.qmap_mk, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf]
      rw [hc]
    · intro t y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      rw [MulAction.compHom_smul_def, MulAction.Quotient.smul_coe, smul_eq_mul,
        UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, UpperTheory.V.Z.Sym.Sig.f_out θ' U' f hf, MonoidHom.comp_apply]
      congr 1
      have h1 : e ((ι t)⁻¹ * δ * θ (ι t)) = e δ := by rw [hδ]
      rw [hc] at h1
      have key : (e (ι t) * z)⁻¹ * e δ * θ' (e (ι t) * z)
          = z⁻¹ * ((e (ι t))⁻¹ * e δ * θ' (e (ι t))) * θ' z := by
        rw [map_mul]
        group
      rw [key, h1]
  · unfold UpperTheory.V.Z.Sym.FinOrb
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S.image e, fun y hy => ?_⟩
      obtain ⟨g, rfl⟩ := he.2 y
      rw [← hc] at hy
      obtain ⟨t, s, hs, u, hu, rfl⟩ := hS g hy
      exact ⟨t, e s, Finset.mem_image_of_mem e hs, e u, hu, by simp [map_mul]⟩
    · rintro ⟨S, hS⟩
      refine ⟨S.image E.symm, fun g hg => ?_⟩
      simp only at hg
      rw [hc] at hg
      obtain ⟨t, s, hs, u, hu, h⟩ := hS (e g) hg
      refine ⟨t, E.symm s, Finset.mem_image_of_mem _ hs, E.symm u, ?_, ?_⟩
      · rw [Subgroup.mem_comap]
        show E (E.symm u) ∈ U'
        rw [MulEquiv.apply_symm_apply]
        exact hu
      · apply E.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact h
  · intro y
    ext t
    simp only [Subgroup.mem_comap, mem_stabilizer_iff, MonoidHom.comp_apply,
      MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, map_mul, map_inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Shrink
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem vo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : kˣ) :
    valuation k (x : k) = uniformizer k ^ ord k x := by
  have h1 := GlAx.val_div_ord x
  have h2 := GlAx.val_zpow (k := k) (ord k x)
  have e : (x : k) = ((x / unif k ^ ord k x : kˣ) : k) * ((unif k ^ ord k x : kˣ) : k) := by
    rw [← Units.val_mul, div_mul_cancel]
  rw [e, map_mul, h1, h2, one_mul]

theorem UpperTheory.V.Z.Sym.Sig.shrink : UpperTheory.V.Z.Sym.Sig.Shrink := by
  intro k _ _ _ _ n d hd m
  set a : Fin n → ℤ := fun i => ord k (d i) with ha
  have hv : ∀ i, valuation k (d i : k) = uniformizer k ^ a i := fun i => vo (d i)
  have hlt : ∀ i j : Fin n, i < j → a j < a i := by
    intro i j hij
    have h := hd i j hij
    rw [hv, hv] at h
    exact (zpow_right_strictAnti₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).lt_iff_gt.1 h
  have hanti : Antitone a := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hlt i j h).le
    · rw [h]
  have hv' : ∀ i, valuation k ((d⁻¹) i : k) = uniformizer k ^ (-a i) := by
    intro i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, _root_.zpow_neg]
  refine ⟨fun x hx hxm => ?_, fun c y hy hym => ?_⟩
  · have hx' : x ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_N hv hanti hx, ?_⟩
    rw [GlAx.mem_Kc] at hxm ⊢
    refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hx').1 hxm d a hv ?_
    intro i j
    rcases le_or_gt j i with h | h
    · exact Or.inl fun z hz => GlAx.up_sub_one hz h
    · right
      have := hlt i j h
      push_cast
      omega
  · have hy' : y ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (c + 1) := hy
    have e1 : (dg d)⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ _).symm
    have e2 : dg d = (diagT k (Fin n) d⁻¹)⁻¹ := by
      rw [← map_inv, inv_inv]
    rw [e1, e2]
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_Nm (a := fun i => -a i) hv' (c := c) (c' := c) ?_ hy, ?_⟩
    · intro i j h
      have := hlt j i h
      omega
    · rw [GlAx.mem_Kc] at hym ⊢
      refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hy').1 hym d⁻¹
        (fun i => -a i) hv' ?_
      intro i j
      rcases le_or_gt i j with h | h
      · exact Or.inl fun z hz => GlAx.low_sub_one hz h
      · right
        have := hlt j i h
        push_cast
        omega

end
end

