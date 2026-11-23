module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem coe_mem_orbit (U : Subgroup G) (a g : G) :
    (g : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) ↔ g ∈ DC U a := by
  constructor
  · rintro ⟨u, hu⟩
    have h : ((u.1 * a : G) : G ⧸ U) = g := by rw [← hu]; rfl
    rw [QuotientGroup.eq] at h
    exact ⟨u.1, u.2, (u.1 * a)⁻¹ * g, h, by group⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * u' : G) : G ⧸ U)
    rw [QuotientGroup.eq, show (u * a)⁻¹ * (u * a * u') = u' by group]
    exact hu'

private theorem out_mem_orbit (U : Subgroup G) (a : G) (y : G ⧸ U) :
    y ∈ MulAction.orbit U (a : G ⧸ U) ↔ y.out ∈ DC U a := by
  rw [← coe_mem_orbit, QuotientGroup.out_eq']

private theorem val_out (U : Subgroup G) {φ : G → V} (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g)
    (g y : G) (q : G ⧸ U) (h : (y : G ⧸ U) = q) : φ (g * q.out) = φ (g * y) := by
  have hm : y⁻¹ * q.out ∈ U := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact h
  have e := hφ _ hm (g * y)
  rw [show g * y * (y⁻¹ * q.out) = g * q.out by group] at e
  exact e

private theorem dcF_eq_mem (U : Subgroup G) (a : G) (φ : G → V) :
    dcF U a φ = (∑ᶠ q ∈ MulAction.orbit U (a : G ⧸ U), rightReg ℂ G V q.out) φ := by
  show (∑ᶠ q : ↑(MulAction.orbit U (a : G ⧸ U)), rightReg ℂ G V (Quotient.out (q : G ⧸ U))) φ = _
  rw [finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ U => rightReg ℂ G V q.out)]

private theorem dcF_apply (U : Subgroup G) (a : G) (h : (MulAction.orbit U (a : G ⧸ U)).Finite)
    (φ : G → V) (g : G) :
    dcF U a φ g = ∑ y ∈ Set.Finite.toFinset h, φ (g * y.out) := by
  rw [dcF_eq_mem, finsum_mem_eq_finite_toFinset_sum _ h]
  simp [LinearMap.sum_apply, Finset.sum_apply, rightReg, LinearMap.funLeft]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcBasic :
    UpperTheory.V.Z.Sym.So.DcBasic := by
  intro G V _ _ _ U a hfin0 φ hφ
  classical
  have hfin : (MulAction.orbit U (a : G ⧸ U)).Finite := hfin0
  have hO : ∀ (v : U) (y : G ⧸ U), y ∈ MulAction.orbit U (a : G ⧸ U) →
      v • y ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro v y ⟨w, rfl⟩
    exact ⟨v * w, mul_smul v w _⟩
  have h5 : ∀ (R : Finset G), (∀ y ∈ R, y ∈ DC U a) →
      (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) → ∀ g, dcF U a φ g = ∑ r ∈ R, φ (g * r) := by
    intro R hR hu g
    rw [dcF_apply U a hfin φ g]
    symm
    refine Finset.sum_bij (fun r _ => (r : G ⧸ U)) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Set.Finite.mem_toFinset]
      exact (coe_mem_orbit U a r).mpr (hR r hr)
    · intro r1 hr1 r2 hr2 he
      have h12 : r1⁻¹ * r2 ∈ U := QuotientGroup.eq.mp he
      have h22 : r2⁻¹ * r2 ∈ U := by rw [inv_mul_cancel]; exact U.one_mem
      exact (hu r2 (hR r2 hr2)).unique ⟨hr1, h12⟩ ⟨hr2, h22⟩
    · intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨r, ⟨hr, hry⟩, -⟩ := hu _ ((out_mem_orbit U a y).mp hy)
      refine ⟨r, hr, ?_⟩
      show (r : G ⧸ U) = y
      rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
      exact hry
    · intro r hr
      exact (val_out U hφ g r (r : G ⧸ U) rfl).symm
  refine ⟨?_, ?_, ?_, ?_, h5⟩
  · intro u hu g
    rw [dcF_apply U a hfin φ, dcF_apply U a hfin φ]
    let u' : U := ⟨u, hu⟩
    refine Finset.sum_nbij' (fun y => u' • y) (fun y => u'⁻¹ • y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u' y hy
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u'⁻¹ y hy
    · intro y _
      exact inv_smul_smul u' y
    · intro y _
      exact smul_inv_smul u' y
    · intro y _
      have hq : ((u * y.out : G) : G ⧸ U) = u' • y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [mul_assoc]
      exact (val_out U hφ g (u * y.out) (u' • y) hq).symm
  · intro g
    rw [dcF_apply U a hfin φ g, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp only [out_mem_orbit]
  · intro b hb
    rw [dcF_eq_mem, dcF_eq_mem, MulAction.orbit_eq_iff.mpr ((coe_mem_orbit U a b).mpr hb)]
  · intro ha
    funext g
    rw [h5 {1} ?_ ?_ g, Finset.sum_singleton, mul_one]
    · intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨a⁻¹, U.inv_mem ha, 1, U.one_mem, by group⟩
    · rintro y ⟨v, hv, v', hv', rfl⟩
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
      · rw [inv_one, one_mul]
        exact U.mul_mem (U.mul_mem hv ha) hv'
      · rintro r ⟨hr, -⟩
        exact Finset.mem_singleton.mp hr

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcLocal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_end_apply {α M : Type} [AddCommGroup M] [Module ℂ M] [Finite α]
    (f : α → Module.End ℂ M) (x : M) : (∑ᶠ a, f a) x = ∑ᶠ a, f a x := by
  cases nonempty_fintype α
  simp only [finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Z.Sym.So.dcLocal :
    UpperTheory.V.Z.Sym.So.DcLocal := by
  intro H G V _ _ _ _ j p J U hpj hU hJ d hd

  have hin : ∀ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) →
      ((j h : G) : G ⧸ U) ∈ MulAction.orbit U ((j d : G) : G ⧸ U) := by
    rintro h ⟨a, ha⟩
    have h1 : (((a : H) * d : H) : H ⧸ J) = (h : H ⧸ J) := ha
    have h2 : ((a : H) * d)⁻¹ * h ∈ J := QuotientGroup.eq.1 h1
    have h3 : (j ((a : H) * d))⁻¹ * j h ∈ U := by
      have := hJ _ h2
      simpa [map_mul] using this
    refine ⟨⟨j a, hJ _ a.2⟩, ?_⟩
    change ((j a * j d : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    simpa [map_mul] using h3

  have hsurj : ∀ y ∈ MulAction.orbit U ((j d : G) : G ⧸ U),
      ∃ h : H, (h : H ⧸ J) ∈ MulAction.orbit J (d : H ⧸ J) ∧ ((j h : G) : G ⧸ U) = y := by
    rintro y ⟨u, rfl⟩
    obtain ⟨hpu, hc⟩ := hU u u.2
    set c : G := (u : G) * (j (p u))⁻¹ with hcdef
    have hcU : c ∈ U := U.mul_mem u.2 (U.inv_mem (hJ _ hpu))
    refine ⟨p u * d, ⟨⟨p u, hpu⟩, rfl⟩, ?_⟩
    change ((j (p u * d) : G) : G ⧸ U) = (((u : G) * j d : G) : G ⧸ U)
    have hfac : (u : G) * j d = j (p u * d) * c := by
      have h1 : (u : G) = c * j (p u) := by simp [hcdef]
      calc (u : G) * j d = c * j (p u * d) := by rw [map_mul, ← mul_assoc, ← h1]
        _ = j (p u * d) * c := hc _
    rw [hfac]
    exact (QuotientGroup.mk_mul_of_mem _ hcU).symm
  have hfin : AlgebraTools.FinOrb U U (j d) := by
    refine (hd.image fun q : H ⧸ J => ((j q.out : G) : G ⧸ U)).subset ?_
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hsurj y hy
    refine ⟨(h : H ⧸ J), hh, ?_⟩
    change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
    refine QuotientGroup.eq.2 ?_
    have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
    have := hJ _ h1
    simpa [map_mul] using this
  refine ⟨hfin, fun φ hφ => ?_⟩
  haveI : Finite (MulAction.orbit J (d : H ⧸ J)) := Set.Finite.to_subtype hd
  haveI : Finite (MulAction.orbit U ((j d : G) : G ⧸ U)) := Set.Finite.to_subtype hfin

  let e : MulAction.orbit J (d : H ⧸ J) → MulAction.orbit U ((j d : G) : G ⧸ U) := fun q =>
    ⟨((j (q : H ⧸ J).out : G) : G ⧸ U), hin _ (by simpa using q.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hqq
      have h1 : ((j (q : H ⧸ J).out : G) : G ⧸ U) = ((j (q' : H ⧸ J).out : G) : G ⧸ U) :=
        congrArg Subtype.val hqq
      have h2 : (j (q : H ⧸ J).out)⁻¹ * j (q' : H ⧸ J).out ∈ U := QuotientGroup.eq.1 h1
      have h3 := (hU _ h2).1
      have h4 : ((q : H ⧸ J).out)⁻¹ * (q' : H ⧸ J).out ∈ J := by
        simpa [map_mul, map_inv, hpj] using h3
      have h5 : (((q : H ⧸ J).out : H) : H ⧸ J) = (((q' : H ⧸ J).out : H) : H ⧸ J) :=
        QuotientGroup.eq.2 h4
      apply Subtype.ext
      simpa using h5
    · rintro ⟨y, hy⟩
      obtain ⟨h, hh, rfl⟩ := hsurj y hy
      refine ⟨⟨(h : H ⧸ J), hh⟩, Subtype.ext ?_⟩
      change ((j (h : H ⧸ J).out : G) : G ⧸ U) = ((j h : G) : G ⧸ U)
      refine QuotientGroup.eq.2 ?_
      have h1 : ((h : H ⧸ J).out)⁻¹ * h ∈ J := QuotientGroup.eq.1 (by simp)
      have := hJ _ h1
      simpa [map_mul] using this
  unfold dcF dc
  rw [finsum_end_apply, finsum_end_apply, ← finsum_comp e he]
  refine finsum_congr fun q => ?_
  funext g
  have h1 : (((e q : G ⧸ U)).out)⁻¹ * j (q : H ⧸ J).out ∈ U := QuotientGroup.eq.1 (by simp [e])
  have h2 := hφ _ h1 (g * ((e q : G ⧸ U)).out)
  change φ (g * ((e q : G ⧸ U)).out) = φ (g * j (q : H ⧸ J).out)
  rw [← h2]
  congr 1
  group

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem det_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) (i : Fin n) :
    Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := congrFun ((leviTorus k (Fin n)).symm_apply_apply t) i

private theorem abs_one_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 = (absPow k (-1))⁻¹ := by
  have h0 : absPow k 0 = 1 := by
    ext x
    simp [val_absPow]
  apply eq_inv_of_mul_eq_one_left
  rw [← absPow_add, show (1 : ℂ) + -1 = 0 by ring, h0]

private theorem abs_zero_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 0 = 1 := by
  ext x
  simp [val_absPow]

theorem UpperTheory.V.Z.Sym.So.expoEq :
    UpperTheory.V.Z.Sym.So.ExpoEq := by
  intro k _ _ _ _ a
  have hA : ∀ x : kˣ, absPow k 1 x = (absPow k (-1) x)⁻¹ := by
    intro x
    rw [abs_one_eq]
    rfl
  have hZ : ∀ x : kˣ, absPow k 0 x = 1 := by
    intro x
    rw [abs_zero_eq]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have m0 : modExp (fun _ : Fin 3 => Unit) 0 = 2 := by decide
    have m1 : modExp (fun _ : Fin 3 => Unit) 1 = 0 := by decide
    have m2 : modExp (fun _ : Fin 3 => Unit) 2 = -2 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1, m2]
    have e0 : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
    have e1 : ((0 : ℤ) : ℂ) / 2 = 0 := by norm_num
    have e2 : ((-2 : ℤ) : ℂ) / 2 = -1 := by norm_num
    rw [e0, e1, e2, hA, hZ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, map_div]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_one]
    simp
    ring
  · intro t
    have m0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have m1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    unfold Dict.expo
    rw [← Units.val_mul]
    congr 1
    rw [torusChar_apply, MonoidHom.comp_apply, deltaHalf_apply, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [MulEquiv.coe_toMonoidHom, det_lt, m0, m1]
    have hh : absPow k ((1 : ℤ) / 2) = absPow k 1 * absPow k ((-1 : ℤ) / 2) := by
      rw [← absPow_add]
      congr 1
      push_cast
      ring
    rw [hh]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      MonoidHom.one_apply, MonoidHom.mul_apply, hA, map_inv]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp
  · intro n ψ
    refine ⟨fun d => Units.ne_zero _, ?_, ?_⟩
    · unfold Dict.expo
      simp
    · intro d d'
      unfold Dict.expo
      rw [← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, mul_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      ring

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FitExt
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lev_ext' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V V' : Sig.Lev k} (hc : V.c = V'.c) (hH : V.H = V'.H) : V = V' := by
  cases V
  cases V'
  cases hc
  cases hH
  rfl

theorem UpperTheory.V.Z.Sym.So.fitExt :
    UpperTheory.V.Z.Sym.So.FitExt := by
  intro L _ _ _ B T S₀ S V₀ VL A₀ A h₀ h hS hV hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    exact (h.sg _).2 ⟨w, hS hw, rfl⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    rw [h.s w (hS hw) hs, h₀.s w hw hs]
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := (h₀.sg v).1 hv
    have hs : IsSplitAt w := h₀.pl.split w (Finset.mem_coe.2 hw)
    have e : A.V (un w) = A₀.V (un w) :=
      lev_ext' (by rw [h.c w (hS hw), h₀.c w hw, hV w hw]) (by
        ext x
        rw [← h.H w (hS hw) hs x, ← h₀.H w hw hs x, hV w hw])
    rw [e]
  · intro v hv hn
    obtain ⟨w, hw, rfl⟩ := (h.sg v).1 hv
    have hw0 : w ∉ S₀ := fun hw0 => hn ((h₀.sg _).2 ⟨w, hw0, rfl⟩)
    have hs : IsSplitAt w := h.pl.split w (Finset.mem_coe.2 hw)
    have hi := hI w hw hw0
    have e : A.V (un w) = Sig.Lev.iw _ :=
      lev_ext' (by rw [h.c w hw, hi]; rfl) (by
        ext x
        rw [← h.H w hw hs x, hi]
        exact (T w hs).Uo x)
    rw [e]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem out_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ i ∈ U, ((g : G ⧸ U)).out = g * i := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem orb_iff {G : Type} [Group G] (U : Subgroup G) (a : G) (p : G ⧸ U) :
    p ∈ MulAction.orbit U (a : G ⧸ U) ↔ p.out ∈ DC U a := by
  have key : ∀ u : U, u • (a : G ⧸ U) = (((u : G) * a : G) : G ⧸ U) := fun u => rfl
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((u : G) * a)
    refine ⟨u, u.2, i, hi, ?_⟩
    dsimp only
    rw [key, h]
  · rintro ⟨u, hu, u', hu', h⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    dsimp only
    rw [key, ← QuotientGroup.out_eq' p, h]
    refine QuotientGroup.eq.mpr ?_
    rw [inv_mul_cancel_left]
    exact hu'

private theorem dcF_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (U : Subgroup G) (a : G)
    [Fintype (MulAction.orbit U (a : G ⧸ U))] (φ : G → V) (g : G) :
    dcF U a φ g = ∑ q : MulAction.orbit U (a : G ⧸ U), φ (g * (q : G ⧸ U).out) := by
  simp only [dcF, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, Finset.sum_apply]
  rfl

private theorem mul_mem_dc_of_mem_subgroup {G : Type} [Group G] (U : Subgroup G) (c x i : G) (hx : x ∈ DC U c) (hi : i ∈ U) :
    x * i ∈ DC U c := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hx
  exact ⟨u, hu, u' * i, U.mul_mem hu' hi, mul_assoc _ _ _⟩

private theorem quotient_out_mem_dc_iff {G : Type} [Group G] (U : Subgroup G) (c x : G) :
    ((x : G ⧸ U)).out ∈ DC U c ↔ x ∈ DC U c := by
  obtain ⟨i, hi, h⟩ := out_mul U x
  rw [h]
  constructor
  · intro hx
    simpa using mul_mem_dc_of_mem_subgroup U c _ i⁻¹ hx (U.inv_mem hi)
  · intro hx
    exact mul_mem_dc_of_mem_subgroup U c x i hx hi

theorem UpperTheory.V.Z.Sym.So.uFMul :
    UpperTheory.V.Z.Sym.So.UFMul := by
  intro G V _ _ _ U a b ha hb hab huf φ hφ
  haveI : Fintype (MulAction.orbit U (a : G ⧸ U)) := Set.Finite.fintype ha
  haveI : Fintype (MulAction.orbit U (b : G ⧸ U)) := Set.Finite.fintype hb
  haveI : Fintype (MulAction.orbit U ((a * b : G) : G ⧸ U)) := Set.Finite.fintype hab
  funext g
  rw [dcF_sum U a _ g, dcF_sum U (a * b) φ g]
  simp only [dcF_sum U b φ]
  rw [← Fintype.sum_prod_type']
  have hmem : ∀ x : MulAction.orbit U (a : G ⧸ U) × MulAction.orbit U (b : G ⧸ U),
      (((x.1 : G ⧸ U).out * (x.2 : G ⧸ U).out : G) : G ⧸ U) ∈ MulAction.orbit U ((a * b : G) : G ⧸ U) := by
    intro x
    refine (orb_iff U (a * b) _).mpr ((quotient_out_mem_dc_iff U _ _).mpr ((huf _).2 _ ((orb_iff U a _).mp x.1.2) ?_))
    rw [inv_mul_cancel_left]
    exact (orb_iff U b _).mp x.2.2
  refine Fintype.sum_bijective (fun x => ⟨_, hmem x⟩) ⟨?_, ?_⟩ _ _ ?_
  · rintro ⟨q, r⟩ ⟨q', r'⟩ hx
    have hx' : (((q : G ⧸ U).out * (r : G ⧸ U).out : G) : G ⧸ U) =
        (((q' : G ⧸ U).out * (r' : G ⧸ U).out : G) : G ⧸ U) := congrArg Subtype.val hx
    obtain ⟨i, hi, hs⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    obtain ⟨i', hi', hs'⟩ := out_mul U ((q' : G ⧸ U).out * (r' : G ⧸ U).out)
    have hsab : (q : G ⧸ U).out * (r : G ⧸ U).out * i ∈ DC U (a * b) := by
      have := (orb_iff U (a * b) _).mp (hmem (q, r))
      rwa [hs] at this
    rw [hx'] at hs
    have he : (q : G ⧸ U).out * (r : G ⧸ U).out * i = (q' : G ⧸ U).out * (r' : G ⧸ U).out * i' :=
      hs.symm.trans hs'
    obtain ⟨y, -, huniq⟩ := (huf _).1 hsab
    have h1 : (q : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q.2, by
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i ((orb_iff U b _).mp r.2) hi⟩
    have h2 : (q' : G ⧸ U) = y := huniq _ ⟨(orb_iff U a _).mp q'.2, by
      rw [he]
      simp only [mul_assoc, inv_mul_cancel_left]
      exact mul_mem_dc_of_mem_subgroup U b _ i' ((orb_iff U b _).mp r'.2) hi'⟩
    have hq : q = q' := Subtype.ext (h1.trans h2.symm)
    subst hq
    have hr : (r : G ⧸ U).out * i = (r' : G ⧸ U).out * i' := by
      rw [mul_assoc, mul_assoc] at he
      exact mul_left_cancel he
    have hr' : (r : G ⧸ U) = r' := by
      rw [← QuotientGroup.out_eq' (r : G ⧸ U), ← QuotientGroup.out_eq' (r' : G ⧸ U),
        ← QuotientGroup.mk_mul_of_mem (r : G ⧸ U).out hi, hr, QuotientGroup.mk_mul_of_mem _ hi']
    exact Prod.ext rfl (Subtype.ext hr')
  · rintro ⟨s, hs⟩
    have hsd : (s : G ⧸ U).out ∈ DC U (a * b) := (orb_iff U (a * b) s).mp hs
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := (huf _).1 hsd
    refine ⟨(⟨y, (orb_iff U a y).mpr hy1⟩,
      ⟨((y.out⁻¹ * s.out : G) : G ⧸ U), (orb_iff U b _).mpr ((quotient_out_mem_dc_iff U _ _).mpr hy2)⟩), ?_⟩
    apply Subtype.ext
    obtain ⟨i, hi, h⟩ := out_mul U (y.out⁻¹ * s.out)
    dsimp only
    rw [h, ← mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ hi, QuotientGroup.out_eq']
  · rintro ⟨q, r⟩
    obtain ⟨i, hi, h⟩ := out_mul U ((q : G ⧸ U).out * (r : G ⧸ U).out)
    dsimp only
    rw [h, ← mul_assoc, ← mul_assoc, hφ i hi]

end
end

