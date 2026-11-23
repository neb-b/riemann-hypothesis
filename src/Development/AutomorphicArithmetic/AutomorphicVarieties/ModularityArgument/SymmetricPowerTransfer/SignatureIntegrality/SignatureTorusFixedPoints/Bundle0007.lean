module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym.Sig

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem sc_eq (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = dg (fun _ : Fin n => z) := by
  apply Units.ext
  ext i j
  simp [dg, val_diagT, GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]

private theorem sc_comm (z : kˣ) (g : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) z * g = g * GeneralLinearGroup.scalar (Fin n) z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_eq, dg, val_diagT]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem sc_mem_iff (V : Lev k) (hn : 0 < n) (z : kˣ) :
    GeneralLinearGroup.scalar (Fin n) z ∈ V.J n ↔ z ∈ V.H := by
  constructor
  · intro h
    obtain ⟨u, hu, e⟩ := ((memJ k V n _).1 h).2.2 ⟨0, hn⟩
    have : u = z := by
      apply Units.ext
      rw [e, sc_eq, dg, val_diagT]
      simp
    exact this ▸ hu
  · intro h
    rw [sc_eq]
    exact le_sup_left (b := (glIwa k n).Nm V.c) (le_sup_right (a := (glIwa k n).N) ⟨fun _ => z, fun _ _ => h, rfl⟩)

private theorem dom_of (d : Fin n → kˣ) (hd : SDom d) : Dom d := fun i j h =>
  h.eq_or_lt.elim (fun e => by rw [e]) (fun l => (hd i j l).le)

private theorem H_of_mem (V : Lev k) (hn : 0 < n) {d : Fin n → kˣ} (hd : SDom d) {g : GL (Fin n) k}
    (hg : g ∈ V.DC d) {z : kˣ} (h : GeneralLinearGroup.scalar (Fin n) z * g ∈ V.DC d) : z ∈ V.H := by
  obtain ⟨j, hj, _, ⟨t, ht, rfl⟩, e⟩ := contract k V n (MonoidHom.id _) (pres_id V n) d hd g hg
  obtain ⟨a, ha, b, hb, e2⟩ := h
  have e3 : dg ((fun _ => z) * t * d) = (j⁻¹ * a) * dg d * (b * j) := by
    have e4 : dg ((fun _ => z) * t * d) = GeneralLinearGroup.scalar (Fin n) z * (diagT k (Fin n) t * dg d) := by
      rw [sc_eq, dg, dg, dg, map_mul, map_mul, mul_assoc]
    rw [e4, ← e, MonoidHom.id_apply]
    calc
      GeneralLinearGroup.scalar (Fin n) z * (j⁻¹ * g * j)
          = j⁻¹ * (GeneralLinearGroup.scalar (Fin n) z * g) * j := by
        rw [← mul_assoc, ← mul_assoc, sc_comm z j⁻¹]; simp only [mul_assoc]
      _ = _ := by rw [e2]; group
  have h1 : dg ((fun _ => z) * t * d) ∈ V.DC d := ⟨_, mul_mem (inv_mem hj) ha, _, mul_mem hb hj, e3⟩
  have h2 := (diagDC k V n d _ (dom_of d hd)).1 h1 ⟨0, hn⟩
  have h3 : z * t ⟨0, hn⟩ * d ⟨0, hn⟩ / d ⟨0, hn⟩ ∈ V.H := h2
  have h4 := div_mem h3 (ht ⟨0, hn⟩ trivial)
  simpa using h4

private theorem mem_ZJ (V : Lev k) (u : GL (Fin n) k) :
    u ∈ V.ZJ n ↔ ∃ z : kˣ, ∃ j ∈ V.J n, u = GeneralLinearGroup.scalar (Fin n) z * j := by
  haveI : (GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k).range.Normal := ⟨by
    rintro _ ⟨z, rfl⟩ g
    exact ⟨z, by rw [← sc_comm z g]; simp⟩⟩
  rw [← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
    exact ⟨z, j, hj, rfl⟩
  · rintro ⟨z, j, hj, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩

private theorem fZ_eq (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (hn : 0 < n)
    {d : Fin n → kˣ} (hd : SDom d) {z : kˣ} {g : GL (Fin n) k}
    (h : (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g ∈ V.DC d) :
    V.fZ ω d g = (((ω z)⁻¹ : ℂˣ) : ℂ) := by
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g ∈ V.DC d := ⟨z, h⟩
  rw [Lev.fZ, dite_eq_left hex]
  have hc := hex.choose_spec
  generalize hex.choose = c at hc ⊢
  have h1 : z / c ∈ V.H := H_of_mem V hn hd h (g := (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * g) (by
    convert hc using 1
    simp only [map_div, div_eq_mul_inv, map_mul, map_inv]
    rw [sc_comm z, ← mul_assoc, mul_assoc _ _ g]
    group)
  have h2 := hω _ h1
  rw [map_div, div_eq_one] at h2
  rw [h2]

private theorem dc_tr (V : Lev k) {d : Fin n → kˣ} {c : kˣ} {g u u' : GL (Fin n) k}
    (hu : u ∈ V.J n) (hu' : u' ∈ V.J n) (h : (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d) :
    (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (u * g * u') ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, e⟩ := h
  refine ⟨u * a, mul_mem hu ha, b * u', mul_mem hb hu', ?_⟩
  have : (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * (u * g * u') =
      u * ((GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g) * u' := by
    rw [← map_inv, ← mul_assoc, ← mul_assoc, sc_comm c⁻¹ u]; simp only [mul_assoc]
  rw [this, e]; group

end

theorem UpperTheory.V.Z.Sym.Sig.eqZ :
    UpperTheory.V.Z.Sym.Sig.EqZ := by
  intro k _ _ _ _ V ω hω n hn
  have wd : ∀ (z z' : kˣ) (j j' : GL (Fin n) k), j ∈ V.J n → j' ∈ V.J n →
      GeneralLinearGroup.scalar (Fin n) z * j = GeneralLinearGroup.scalar (Fin n) z' * j' → ω z = ω z' := by
    intro z z' j j' hj hj' e
    have h1 : GeneralLinearGroup.scalar (Fin n) (z'⁻¹ * z) = j' * j⁻¹ := by
      rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    have h2 : z'⁻¹ * z ∈ V.H := (sc_mem_iff V hn _).1 (h1 ▸ mul_mem hj' (inv_mem hj))
    have h3 := hω _ h2
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3.symm
  have hZ : ∀ u : V.ZJ n, ∃ z : kˣ, ∃ j ∈ V.J n, (u : GL (Fin n) k) = GeneralLinearGroup.scalar (Fin n) z * j :=
    fun u => (mem_ZJ V u.1).1 u.2
  choose Z Jf hJ eZ using hZ
  refine ⟨⟨MonoidHom.mk' (fun u => ω (Z u)) ?_, ?_⟩, mem_ZJ V, ?_⟩
  · intro u v
    rw [← map_mul]
    refine wd _ _ _ _ (hJ (u * v)) (mul_mem (hJ u) (hJ v)) ?_
    rw [← eZ (u * v), Subgroup.coe_mul, eZ u, eZ v, map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (Jf u), ← sc_comm, mul_assoc]
  · intro z j u hj e
    exact wd _ _ _ _ (hJ u) hj ((eZ u).symm.trans e)
  · intro d hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z g hg
      exact fZ_eq V ω hω hn hd (by rwa [inv_mul_cancel_left])
    · intro z g
      by_cases h : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (z := z * c) (by
          convert hc using 1
          rw [map_mul]
          group), map_mul, mul_inv, Units.val_mul]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = 0 :=
          dif_neg (fun ⟨c, hc⟩ => h ⟨z⁻¹ * c, by
            convert hc using 1
            rw [map_mul, map_inv]
            group⟩)
        rw [h0, h1, mul_zero]
    · intro u hu u' hu' g
      by_cases h : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (dc_tr V hu hu' hc)]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (u * g * u') = 0 := dif_neg (fun ⟨c, hc⟩ => h ⟨c, by
          have h2 := dc_tr V (inv_mem hu) (inv_mem hu') hc
          have e : u⁻¹ * (u * g * u') * u'⁻¹ = g := by group
          rwa [e] at h2⟩)
        rw [h0, h1]
    · have hfin := ((finFacts k V).2.2.2.2.2 n).1 (dg d)
      refine (Set.Finite.image (fun q : GL (Fin n) k ⧸ V.J n =>
        ((q.out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n)) hfin).subset ?_
      intro y hy
      have hex : ∃ c : kˣ, (GeneralLinearGroup.scalar (Fin n) c)⁻¹ * y.out ∈ V.DC d := by
        by_contra h
        exact hy (dif_neg h)
      obtain ⟨c, a, ha, b, hb, e⟩ := hex
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)
      refine ⟨((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n), ⟨⟨a, ha⟩, rfl⟩, ?_⟩
      show ((((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n).out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n) = y
      have e1 : y.out = (a * dg d) * (GeneralLinearGroup.scalar (Fin n) c * b) := by
        calc
          y.out = GeneralLinearGroup.scalar (Fin n) c *
              ((GeneralLinearGroup.scalar (Fin n) c)⁻¹ * y.out) := by group
          _ = GeneralLinearGroup.scalar (Fin n) c * (a * dg d * b) := by rw [e]
          _ = _ := by rw [← mul_assoc, sc_comm c (a * dg d), mul_assoc]
      rw [hj, ← QuotientGroup.out_eq' y, QuotientGroup.eq, e1]
      refine (mem_ZJ V _).2 ⟨c, (j : GL (Fin n) k)⁻¹ * b, mul_mem (inv_mem j.2) hb, ?_⟩
      calc (a * dg d * (j : GL (Fin n) k))⁻¹ * (a * dg d * (GeneralLinearGroup.scalar (Fin n) c * b))
          = (j : GL (Fin n) k)⁻¹ * GeneralLinearGroup.scalar (Fin n) c * b := by group
        _ = _ := by rw [← sc_comm, mul_assoc]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryDoubleCosetIndicator
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem dc_mul (V : Lev k) {d : Fin 3 → kˣ} {u v g : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (h : g ∈ V.DC d) : u * g * v ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨u * a, (V.J 3).mul_mem hu ha, b * v, (V.J 3).mul_mem hb hv, by group⟩

private theorem dc_iff (V : Lev k) {d : Fin 3 → kˣ} {u v : GL (Fin 3) k} (hu : u ∈ V.J 3) (hv : v ∈ V.J 3)
    (g : GL (Fin 3) k) : u * g * v ∈ V.DC d ↔ g ∈ V.DC d := by
  constructor
  · intro h
    have h2 := dc_mul V ((V.J 3).inv_mem hu) ((V.J 3).inv_mem hv) h
    simpa [mul_assoc] using h2
  · exact dc_mul V hu hv

private theorem gl3_spherical_bi_invariant (V : Lev k) (d : Fin 3 → kˣ) {u u' : GL (Fin 3) k} (hu : u ∈ V.J 3) (hu' : u' ∈ V.J 3)
    (g : GL (Fin 3) k) : V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g := by
  have hF := thFacts k V
  have key : u * g * th k 3 u' * (Phi k)⁻¹ = u * (g * (Phi k)⁻¹) * th' k u' := by
    have h7 := hF.2.2.2.2.2.2 u'
    have : th k 3 u' = (Phi k)⁻¹ * th' k u' * Phi k := by
      rw [mul_assoc, h7]
      group
    rw [this]
    group
  simp only [Lev.unitaryDoubleCosetIndicator]
  rw [key, dc_iff V hu (hF.2.1 u' hu')]

private theorem gl3_spherical_finite_support (V : Lev k) (d : Fin 3 → kˣ) :
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.unitaryDoubleCosetIndicator d y.out ≠ 0}.Finite := by
  have hF := thFacts k V
  have hJ := (finFacts k V).2.2.2.2.2 3
  have horb : (MulAction.orbit (V.J 3) ((dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)).Finite := hJ.1 (dg d)
  let F : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) → GL (Fin 3) k ⧸ V.J 3 :=
    fun y => ((Quotient.out y * (Phi k)⁻¹ : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3)
  refine Set.Finite.of_finite_image (f := F) (horb.subset ?_) ?_
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Set.mem_setOf_eq, Lev.unitaryDoubleCosetIndicator] at hy
    have hy' : Quotient.out y * (Phi k)⁻¹ ∈ V.DC d := by
      by_contra hc
      rw [if_neg hc] at hy
      exact hy rfl
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * dg d : GL (Fin 3) k) : GL (Fin 3) k ⧸ V.J 3) = F y
    simp only [F]
    rw [hab, QuotientGroup.eq]
    simpa [mul_assoc] using hb
  · intro y1 _ y2 _ h
    simp only [F] at h
    rw [QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' y1, ← QuotientGroup.out_eq' y2, QuotientGroup.eq]
    set w := Phi k * ((Quotient.out y1)⁻¹ * Quotient.out y2) * (Phi k)⁻¹ with hw
    refine ⟨th' k w, hF.2.1 w ?_, ?_⟩
    · convert h using 1
      rw [hw]
      group
    · have h7 := hF.2.2.2.2.2.2 (th' k w)
      rw [Pres.invol hF.1 w] at h7
      have : th k 3 (th' k w) = (Phi k)⁻¹ * (w * Phi k) := by
        rw [h7]
        group
      rw [this, hw]
      group

end UpperTheory.V.Z.Sym.Sig

theorem UpperTheory.V.Z.Sym.Sig.eqG :
    UpperTheory.V.Z.Sym.Sig.EqG := by
  intro k _ _ _ _ V ω Rs Ry x z d
  refine ⟨fun u hu u' hu' g => ⟨gl3_spherical_bi_invariant V d hu hu' g, ?_⟩, gl3_spherical_finite_support V d, ?_⟩
  · simp only [Lev.fG, gl3_spherical_bi_invariant V _ hu hu' g]
  · refine (Set.Finite.biUnion Rs.finite_toSet fun e _ =>
      Set.Finite.biUnion Ry.finite_toSet fun y _ => gl3_spherical_finite_support V ![x * e, y, z]).subset ?_
    intro q hq
    have hq' : ∑ e ∈ Rs, ∑ y ∈ Ry, (ω e : ℂ) * V.unitaryDoubleCosetIndicator ![x * e, y, z] q.out ≠ 0 := hq
    obtain ⟨e, he, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
    obtain ⟨y, hy, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact Set.mem_biUnion he (Set.mem_biUnion hy (right_ne_zero_of_mul h))

end
end

