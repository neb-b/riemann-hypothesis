module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.SuppZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.UnitaryHyperbolicOrbitCount

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.OkKValLt
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem okK_val_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : valuation k (t : k) < valuation k (unif k : k) ^ 2) : valuation k (t : k) < 1 := by
  have hw : valuation k (unif k : k) < 1 := by
    rw [GlAx.unif_spec]
    exact uniformizer_lt_one
  exact ht.trans (pow_lt_one₀ zero_le' hw two_ne_zero)

private theorem okK_conj {k : Type} [Field k] (g₀ : GL (Fin 2) k) (a b : kˣ) :
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + b ∧
    ((g₀ * diagT k (Fin 2) ![a, b] * g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (a : k) * b := by
  have hinv : ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g₀ : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_diagT]
  constructor
  · rw [Matrix.trace_mul_cycle, hinv, one_mul]
    simp [Matrix.trace_diagonal, Fin.sum_univ_two]
  · rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, one_mul]
    simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem UpperTheory.V.Z.Sym.Sig.okK :
    UpperTheory.V.Z.Sym.Sig.OkK := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht S
  have htv : valuation k (t : k) < 1 := okK_val_lt k t ht
  have hSD : SDom (![t, 1] : Fin 2 → kˣ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    simpa using htv
  have hχH : ∀ u ∈ V.H, χ u = 1 := fun u hu => hχ u (V.H_le hu)
  obtain ⟨_, hZJ, hZd⟩ := eqZ k V χ hχH 2 two_pos
  obtain ⟨_, hmul, hJJ, hfin⟩ := hZd ![t, 1] hSD
  obtain ⟨_, _, _, hIsScal, hmt, hcomap⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hfK : ∀ g, S.fK t g = (((χ t)⁻¹ : ℂˣ) : ℂ) * V.fZ χ ![t, 1] (eD hs g) := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    constructor
    · rw [hfK, hfK, map_mul]
      have e := hJJ (eD hs u) hu' 1 (Subgroup.one_mem _) (eD hs y)
      rw [mul_one] at e
      rw [e]
    · rw [hfK, hfK, map_mul]
      have e := hJJ 1 (Subgroup.one_mem _) (eD hs u) hu' (eD hs y)
      rw [one_mul] at e
      rw [e]
  · intro z s' hz y
    rw [hfK, hfK, map_mul, (hIsScal z s').mp hz, hmul]
    ring
  · have hcj : Subgroup.comap (eD hs) (V.ZJ 2) = ZD Δ ⊔ S.J2 := hcomap V
    have hright : ∀ (g w : GL (Fin 2) k), w ∈ V.ZJ 2 →
        (V.fZ χ ![t, 1] (g * w) ≠ 0 ↔ V.fZ χ ![t, 1] g ≠ 0) := by
      intro g w hw
      obtain ⟨z, j, hj, rfl⟩ := (hZJ w).mp hw
      have hc : g * GeneralLinearGroup.scalar (Fin 2) z = GeneralLinearGroup.scalar (Fin 2) z * g := by
        apply Units.ext
        simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
        exact (scalar_commute (z : k) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) k)).eq.symm
      have e := hJJ 1 (Subgroup.one_mem _) j hj g
      rw [one_mul] at e
      rw [← mul_assoc, hc, mul_assoc, hmul, e]
      exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (Units.ne_zero _) h⟩
    let φ : (DX Δ ⧸ (ZD Δ ⊔ S.J2)) → (GL (Fin 2) k ⧸ V.ZJ 2) :=
      fun x => (QuotientGroup.mk (eD hs x.out))
    have hφ : ∀ x x', φ x = φ x' → x = x' := by
      intro x x' he
      have hm := QuotientGroup.eq.mp he
      rw [← map_inv, ← map_mul, ← Subgroup.mem_comap, hcj] at hm
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      exact QuotientGroup.eq.mpr hm
    refine (Set.Finite.preimage (f := φ) (fun x _ x' _ he => hφ x x' he) hfin).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
    rw [hfK] at hx
    have hx' := right_ne_zero_of_mul hx
    show V.fZ χ ![t, 1] (Quotient.out (QuotientGroup.mk (eD hs x.out) : GL (Fin 2) k ⧸ V.ZJ 2)) ≠ 0
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (V.ZJ 2) (eD hs x.out)
    rw [hw, hright _ _ w.2]
    exact hx'
  · intro g hg
    rw [hfK] at hg
    have hg' : V.fZ χ ![t, 1] (eD hs g) ≠ 0 := right_ne_zero_of_mul hg
    obtain ⟨g₀, a, b, hgeq, hab⟩ := suppZ k V χ ![t, 1] hSD (eD hs g) hg'
    have ha := a.ne_zero
    have hb := b.ne_zero
    refine ⟨((a / b : kˣ) : k) + ((a / b : kˣ)⁻¹ : kˣ), ⟨a / b / t, ?_, ?_⟩, ?_⟩
    · exact (by simpa using hab : a / b / t ∈ V.H)
    · have e : t * (a / b / t) = a / b := by rw [mul_comm, div_mul_cancel]
      rw [e]
    · obtain ⟨hdet, htr⟩ := hmt g
      rw [show dg ![a, b] = diagT k (Fin 2) ![a, b] from rfl] at hgeq
      obtain ⟨htr', hdet'⟩ := okK_conj g₀ a b
      rw [hdet, htr, hgeq, htr', hdet', ← map_pow, ← map_mul]
      congr 1
      simp only [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, inv_div]
      field_simp
      ring

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TauOfRoots
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_of_roots {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (a : kˣ) (τ : k)
    (h : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) = ((X - 1) * (X ^ 2 - C τ * X + 1) : k[X])) :
    τ = (a : k) + ((a⁻¹ : kˣ) : k) := by
  have hu : C (a : k) * C ((a⁻¹ : kˣ) : k) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have e1 : (X - C (a : k)) * (X - C 1) * (X - C ((a⁻¹ : kˣ) : k)) =
      (X - 1) * (X ^ 2 - C ((a : k) + ((a⁻¹ : kˣ) : k)) * X + 1) := by
    rw [C_add, C_1]
    linear_combination (X - 1) * hu
  rw [e1] at h
  have hne : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
  have h' := mul_left_cancel₀ hne h
  have hc := congrArg (fun q : k[X] => q.coeff 1) h'
  simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_one] at hc
  norm_num at hc
  rw [Units.val_inv_eq_inv_val]
  linear_combination hc

private theorem charpoly_dg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b c : kˣ) :
    (((dg ![a, b, c] : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).charpoly = (X - C (a : k)) * (X - C (b : k)) * (X - C (c : k)) := by
  rw [dg.eq_1, val_diagT, charpoly_diagonal]
  simp [Fin.prod_univ_three]

theorem UpperTheory.V.Z.Sym.Sig.okG :
    UpperTheory.V.Z.Sym.Sig.OkG := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hRy χ hχ t ht
  simp only [Lev.data.eq_1, Set.mem_setOf_eq] at ht ⊢
  obtain ⟨hbij, htheta, -, htau⟩ := eU_facts k O hO h2 Δ s hs hs0
  have hinv : ∀ (d : Fin 3 → kˣ) (u : GL (Fin 3) k), u ∈ V.J 3 →
      ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g :=
    fun d u hu u' hu' g => ((eqG k V 1 ∅ ∅ 1 1 d).1 u hu u' hu' g).1
  have hfin : ∀ d : Fin 3 → kˣ,
      {y : GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) | V.unitaryDoubleCosetIndicator d (Quotient.out y) ≠ 0}.Finite :=
    fun d => (eqG k V 1 ∅ ∅ 1 1 d).2.1
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    rw [Subgroup.mem_comap] at hu
    constructor
    · simp only [map_mul, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa [map_one] using hinv _ (eU hs u) hu 1 (Subgroup.one_mem _) (eU hs y)
    · simp only [map_mul, htheta, Lev.unitaryHeckeTestSum.eq_1]
      refine Finset.sum_congr rfl fun z _ => ?_
      simpa using hinv _ 1 (Subgroup.one_mem _) (eU hs u) hu (eU hs y)
  · let ψ : U3 Δ ⧸ Subgroup.comap (eU hs) (V.J 3) → GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3) :=
      fun x => QuotientGroup.mk (th k 3 (eU hs (Quotient.out x)))
    have hψ : Function.Injective ψ := by
      intro x x' hxx
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x']
      rw [QuotientGroup.eq] at hxx ⊢
      rw [Subgroup.mem_comap]
      obtain ⟨j, hj, hjeq⟩ := Subgroup.mem_map.1 hxx
      have hth : Function.Injective (th k 3) := fun a b hab => by
        have := congrArg (th k 3) hab
        rwa [(thFacts k V).2.2.2.1, (thFacts k V).2.2.2.1] at this
      rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at hjeq
      rw [← hth hjeq]
      exact hj
    let T : Set (GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3)) :=
      ⋃ y ∈ Ry, {z | V.unitaryDoubleCosetIndicator ![t * (unif k)⁻¹, y, (unif k)⁻¹] (Quotient.out z) ≠ 0}
    have hT : T.Finite := Set.Finite.biUnion Ry.finite_toSet fun y _ => hfin _
    refine (hT.preimage hψ.injOn).subset fun x hx => ?_
    have hx' : V.unitaryHeckeTestSum Ry t (eU hs (theta Δ (Quotient.out x))) ≠ 0 := hx
    rw [htheta, Lev.unitaryHeckeTestSum.eq_1] at hx'
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    simp only [Set.mem_preimage, T, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨y, hy, ?_⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.map (th k 3) (V.J 3))
      (th k 3 (eU hs (Quotient.out x)))
    obtain ⟨j, hj, hjm⟩ := Subgroup.mem_map.1 m.2
    change V.unitaryDoubleCosetIndicator _ (Quotient.out (QuotientGroup.mk (th k 3 (eU hs (Quotient.out x))) :
      GL (Fin 3) k ⧸ Subgroup.map (th k 3) (V.J 3))) ≠ 0
    rw [hm, ← hjm]
    have e := hinv ![t * (unif k)⁻¹, y, (unif k)⁻¹] 1 (Subgroup.one_mem _) j hj
      (th k 3 (eU hs (Quotient.out x)))
    rw [one_mul] at e
    rw [e]
    exact hne
  · intro δ τ hτ hne
    rw [Lev.unitaryHeckeTestSum.eq_1] at hne
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hv : (valuation k) ((unif k : kˣ) : k) < 1 := by
      rw [GlAx.unif_spec]
      exact uniformizer_lt_one
    have hv0 : 0 < (valuation k) ((unif k : kˣ) : k) := by
      rw [zero_lt_iff]
      exact (_root_.map_ne_zero _).2 (unif k).ne_zero
    obtain ⟨hy1, hy2⟩ := hRy.1 y hy
    have h01 : (valuation k) ((t * (unif k)⁻¹ : kˣ) : k) < (valuation k) (y : k) := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← div_eq_mul_inv,
        div_lt_iff₀ hv0]
      calc (valuation k) (t : k) < (valuation k) ((unif k : kˣ) : k) ^ 2 := ht
        _ = (valuation k) ((unif k : kˣ) : k) * (valuation k) ((unif k : kˣ) : k) := sq _
        _ ≤ (valuation k) (y : k) * (valuation k) ((unif k : kˣ) : k) := by gcongr
    have h12 : (valuation k) (y : k) < (valuation k) (((unif k)⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact hy2.trans_lt ((one_lt_inv₀ hv0).2 hv)
    have hSD : SDom ![t * (unif k)⁻¹, y, (unif k)⁻¹] := by
      rw [SDom.eq_1]
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals first
        | exact h01
        | exact h12
        | exact h01.trans h12
    obtain ⟨g₀, x, y', z, hδ, hH⟩ := supp0 k V _ hSD _ hne
    have hd : (![t * (unif k)⁻¹, y, (unif k)⁻¹] 0 / ![t * (unif k)⁻¹, y, (unif k)⁻¹] 2 : kˣ) = t := by
      simp
    rw [hd] at hH
    have hcp := (htau δ τ).1 hτ
    rw [hδ, (normalG k).1 g₀ x y' z] at hcp
    have hc2 : ((g₀ * dg ![x / z, 1, z / x] * g₀⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly
        = (X - C ((x / z : kˣ) : k)) * (X - C 1) * (X - C (((x / z)⁻¹ : kˣ) : k)) := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, charpoly_units_conj, charpoly_dg,
        inv_div, Units.val_one]
    rw [hc2] at hcp
    have hτ' := tau_of_roots h2 (x / z) τ hcp
    rw [Ind.eq_1]
    refine ⟨x / z / t, hH, ?_⟩
    have hm : t * (x / z / t) = x / z := by
      rw [mul_comm]
      exact div_mul_cancel (x / z) t
    rw [hm]
    exact hτ'

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.TwistedOrbitalIntegralGL3Formula
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
open MulAction

variable {T G : Type} [Group T] [Group G]

private def OrbSupp (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G) : Prop :=
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite

private theorem orb_sum {I : Type} (ι : T →* G) (C : Subgroup T) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    orb ι C θ U (fun g => ∑ i ∈ S, f i g) δ = ∑ i ∈ S, orb ι C θ U (f i) δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  unfold orb wcount
  simp only [Finset.mul_sum]
  rw [finsum_sum_comm]
  intro i hi
  refine (h i hi).subset ?_
  intro o ho
  simp only [Function.mem_support] at ho
  exact right_ne_zero_of_mul ho

private theorem finOrb_of (ι : T →* G) (θ : G →* G) (U : Subgroup G) (f : G → ℂ) (δ : G)
    (hf : ∀ u ∈ U, ∀ x, f (u⁻¹ * x * θ u) = f x) (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ)
    (h : OrbSupp ι θ U f δ) : FinOrb ι θ U f δ := by
  letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
  classical
  have h' : {o : orbitRel.Quotient T (G ⧸ U) | f (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}.Finite := h
  refine ⟨h'.toFinset.image (fun o => o.out.out), ?_⟩
  intro y hy
  let o : orbitRel.Quotient T (G ⧸ U) := Quotient.mk _ (QuotientGroup.mk y : G ⧸ U)
  obtain ⟨t, ht⟩ : ∃ t : T, t • (QuotientGroup.mk y : G ⧸ U) = o.out :=
    Quotient.exact (Quotient.out_eq o)
  have hs : (QuotientGroup.mk (o.out.out) : G ⧸ U) = QuotientGroup.mk (ι t * y) := by
    rw [QuotientGroup.out_eq', ← ht]
    rfl
  have hu := QuotientGroup.eq.mp hs.symm
  set s := o.out.out with hsdef
  set u := (ι t * y)⁻¹ * s with hudef
  have hs' : s = ι t * y * u := by rw [hudef]; group
  refine ⟨t⁻¹, s, ?_, u⁻¹, U.inv_mem hu, ?_⟩
  · refine Finset.mem_image.mpr ⟨o, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    show f (s⁻¹ * δ * θ s) ≠ 0
    have e : s⁻¹ * δ * θ s = u⁻¹ * (y⁻¹ * δ * θ y) * θ u := by
      rw [hs', map_mul, map_mul]
      calc (ι t * y * u)⁻¹ * δ * (θ (ι t) * θ y * θ u)
          = u⁻¹ * (y⁻¹ * ((ι t)⁻¹ * δ * θ (ι t)) * θ y) * θ u := by group
        _ = _ := by rw [hδ]
    rw [e, hf u hu]
    exact hy
  · rw [hs', map_inv]
    group

private theorem finOrb_sum {I : Type} (ι : T →* G) (θ : G →* G) (U : Subgroup G) (δ : G)
    (S : Finset I) (f : I → G → ℂ) (hf : ∀ i ∈ S, ∀ u ∈ U, ∀ x, f i (u⁻¹ * x * θ u) = f i x)
    (hδ : ∀ t, (ι t)⁻¹ * δ * θ (ι t) = δ) (h : ∀ i ∈ S, OrbSupp ι θ U (f i) δ) :
    FinOrb ι θ U (fun g => ∑ i ∈ S, f i g) δ := by
  refine finOrb_of ι θ U _ δ ?_ hδ ?_
  · intro u hu x
    exact Finset.sum_congr rfl fun i hi => hf i hi u hu x
  · letI : MulAction T (G ⧸ U) := MulAction.compHom _ ι
    change {o : orbitRel.Quotient T (G ⧸ U) | (∑ i ∈ S, f i (o.out.out⁻¹ * δ * θ o.out.out)) ≠ 0}.Finite
    have hU : (⋃ i ∈ (S : Set I),
        {o : orbitRel.Quotient T (G ⧸ U) | f i (o.out.out⁻¹ * δ * θ o.out.out) ≠ 0}).Finite :=
      Set.Finite.biUnion S.finite_toSet fun i hi => h i hi
    refine hU.subset ?_
    intro o ho
    simp only [Set.mem_setOf_eq] at ho
    obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
    exact Set.mem_biUnion (Finset.mem_coe.mpr hi) hne

end

theorem UpperTheory.V.Z.Sym.Sig.orbital_integral_over_extended_group :
    UpperTheory.V.Z.Sym.Sig.TwistedOrbitalIntegralGL3Formula := by
  intro k _ _ _ _ V Ry hR t ht T _ r hr g₀ ι hι x y z hxz
  set θ := th k 3 with hθ
  set δ := g₀ * dg ![x, y, z] * Phi k * (θ g₀)⁻¹ with hδdef
  obtain ⟨_, _, hth'dg, _, _, _, hth'Φ⟩ := thFacts k V
  have hδ : ∀ s, (ι s)⁻¹ * δ * θ (ι s) = δ := by
    intro s
    have hΦ : Phi k * θ (dg ![r s, 1, (r s)⁻¹]) = dg ![r s, 1, (r s)⁻¹] * Phi k := by
      rw [← hth'Φ, hth'dg, inv_inv, inv_one]
    have hc : dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹] = dg ![r s, 1, (r s)⁻¹] * dg ![x, y, z] := by
      simp only [dg]
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hι s, map_mul, map_mul, map_inv]
    calc (g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹)⁻¹ * δ * (θ g₀ * θ (dg ![r s, 1, (r s)⁻¹]) * (θ g₀)⁻¹)
        = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * dg ![x, y, z] * (Phi k * θ (dg ![r s, 1, (r s)⁻¹])) *
            (θ g₀)⁻¹ := by
          rw [hδdef]; group
      _ = g₀ * (dg ![r s, 1, (r s)⁻¹])⁻¹ * (dg ![x, y, z] * dg ![r s, 1, (r s)⁻¹]) * Phi k *
            (θ g₀)⁻¹ := by
          rw [hΦ]; group
      _ = δ := by rw [hc, hδdef]; group
  set ϖ := unif k with hϖ
  let d : kˣ → Fin 3 → kˣ := fun a => ![t * ϖ⁻¹, a, ϖ⁻¹]
  have hw1 : valuation k (ϖ : k) < 1 := by
    rw [hϖ, GlAx.unif_spec]
    exact uniformizer_lt_one
  have hw0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr ϖ.ne_zero
  have hSD : ∀ a ∈ Ry, SDom (d a) := by
    intro a ha i j hij
    obtain ⟨hal, hau⟩ := hR.1 a ha
    have htw : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < valuation k (ϖ : k) := by
      rw [mul_inv_lt_iff₀ hw0]
      simpa [pow_two, hϖ] using ht
    have ht1 : valuation k (t : k) * (valuation k (ϖ : k))⁻¹ < 1 := htw.trans hw1
    have hinv : 1 < (valuation k (ϖ : k))⁻¹ := (one_lt_inv₀ hw0).mpr hw1
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [d, map_mul, map_inv₀, Units.val_inv_eq_inv_val]
    · exact htw.trans_le hal
    · exact ht1.trans hinv
    · exact hau.trans_lt hinv
  have hinvar : ∀ a ∈ Ry, ∀ u ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator (d a) (u⁻¹ * g * θ u) = V.unitaryDoubleCosetIndicator (d a) g := by
    intro a _ u hu g
    exact ((eqG k V 1 Ry Ry x z (d a)).1 u⁻¹ ((V.J 3).inv_mem hu) u hu g).1
  have h0 := fun a (ha : a ∈ Ry) => orbital_integral_over_base_group k V T r hr g₀ ι hι (d a) (hSD a ha) x y z hxz
  have hfun : V.unitaryHeckeTestSum Ry t = fun g => ∑ a ∈ Ry, V.unitaryDoubleCosetIndicator (d a) g := rfl
  rw [hfun]
  refine ⟨finOrb_sum ι θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) hinvar hδ (fun a ha => (h0 a ha).1), ?_⟩
  rw [orb_sum ι _ θ (V.J 3) δ Ry (fun a => V.unitaryDoubleCosetIndicator (d a)) (fun a ha => (h0 a ha).1)]
  rw [Finset.sum_congr rfl fun a ha => (h0 a ha).2]
  obtain ⟨a₀, ⟨ha₀, hq₀⟩, huniq⟩ := hR.2 y
  rw [Finset.sum_eq_single a₀]
  · have e : (d a₀) 0 / (d a₀) 2 = t := by simp [d]
    rw [e]
    unfold Glob.one
    by_cases hP : x / z / t ∈ V.H
    · rw [if_pos ⟨hP, hq₀⟩, if_pos hP, mul_one]
    · rw [if_neg (fun hh => hP hh.1), if_neg hP, mul_zero]
  · intro b hb hne
    rw [if_neg]
    rintro ⟨_, hq⟩
    exact hne (huniq b ⟨hb, hq⟩)
  · intro hn
    exact absurd ha₀ hn

end
end

