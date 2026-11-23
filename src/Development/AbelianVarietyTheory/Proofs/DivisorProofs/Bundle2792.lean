module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodFormAutomorphismUnitaryLabellings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.ULabUniq

section Cong
variable {Y : Type} [AddCommGroup Y]

theorem cm_trans {N : ℕ} {x y z : Y} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_symm {N : ℕ} {x y : Y} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_map {Y' : Type} [AddCommGroup Y'] (f : Y →+ Y') {N : ℕ} {x y : Y} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : Y}
    (h : (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : Y} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : Y ⧸ (nsmulAddMonoidHom N : Y →+ Y).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

end Cong

theorem sc_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : UCTrait X p z) : 0 < c.sc := by
  set x := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hx
  have h0 : x ≠ 0 := fun h =>
    c.T.irr.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h)
  have h1 : 0 < ‖c.ι x‖ := norm_pos_iff.2 ((map_ne_zero c.ι).2 h0)
  have h2 : ‖c.ι x‖ < 1 := by
    by_contra h
    have : ‖c.ι x⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h)
    obtain ⟨v, hv⟩ := (c.int _).1 this
    refine c.T.irr.not_isUnit (IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing c.T.V) ?_))
    rw [map_mul, map_one, hv, ← hx, mul_inv_cancel₀ h0]
  exact neg_pos.2 (Real.log_neg h1 h2)


open MonObj in
theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a ν, yy a = QuotientAddGroup.mk ν → yy' a = QuotientAddGroup.mk (κ ν) := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', -, hS, -, -, hR, -, -, -, -, -, -, -, y₀, hy₀, u, lb, j, hq, hyy, -⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', -, hS₁, -, -, hR₁, -, -, -, -, -, -, -, y₁, hy₁, u', lb', j', hq',
    hyy', -⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab⟩ := GlobalTheory.T.unitaryRecharting_classicalTrait_same_geometric_fibre E H Dw l Xo cf C X p z ct c₀ hc R' fg frac hth hev ρ' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → ∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have tors' : ∀ m, 1 ≤ m → ∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm x hx => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, hpk⟩ := hf2 x hx
    exact ⟨pk, (hf1 pk x).2 hpk.symm⟩
  have hqe : ∀ χ, lb'.q (e χ) = lb.q χ := fun χ => by
    have h2 := (hψ χ _).1 (lb.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (lb'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), lb.yy b = QuotientAddGroup.mk χ →
      lb'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := tors _ hrN x (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := tors' _ hrN x' (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u' b x' hx')
    have e1 := lb.yy_eq b pk x hpk hx
    have e2 := lb'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have e1 := hq χ
    have e2 := hq' (e χ)
    rw [hqe] at e2
    have hs := sc_pos ct
    have h4 : ((ct.T.be (j' (e χ)) (j' (e χ)) : ℤ) : ℝ) = ((ct.T.be (j χ) (j χ) : ℤ) : ℝ) := by
      have := e2.symm.trans e1
      have h5 : ct.sc * (ct.T.be (j' (e χ)) (j' (e χ)) : ℝ) = ct.sc * (ct.T.be (j χ) (j χ) : ℝ) := by linarith
      exact mul_left_cancel₀ hs.ne' h5
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (lb'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (κ μ) := core

end GlobalTheory.UPoinc.ULabUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfLe
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.PhaseField

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem exists_field_roots {n : ℕ} (hn : 0 < n) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ z : ℂ, z ^ n = 1 → z ∈ Set.range (algebraMap M ℂ) := by
  classical
  set S : Set ℂ := {z | z ^ n = 1} with hSdef
  have hS : S = ((Polynomial.nthRoots n (1 : ℂ)).toFinset : Set ℂ) := by
    ext z; simp [S, Polynomial.mem_nthRoots hn]
  haveI : Finite S := by rw [hS]; infer_instance
  have hint : ∀ z ∈ S, IsIntegral ℚ z := fun z hz =>
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by
      simp [Polynomial.eval₂_sub, show z ^ n = 1 from hz]⟩
  exact ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_resCard_le {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k ((Nat.card 𝓀[k] : ℕ) : k) ≤ valuation k (ϖ : k) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]
  have h0 : IsLocalRing.residue 𝒪[k] ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) = 0 := by
    rw [map_natCast, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hmem : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    (IsLocalRing.residue_eq_zero_iff _).1 h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
  rw [hϖ, le_uniformizer_iff]
  simpa using hmem

theorem exists_pow_eq_one_of_le {ψ : AddChar k Circle} {ϖ : kˣ} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ) (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : k, valuation k z ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) → ((ψ z : Circle) : ℂ) ^ n = 1 := by
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  refine ⟨Nat.card 𝓀[k] ^ N, pow_pos hq N, fun z hz => ?_⟩
  have h1 : valuation k (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) ≤ 1 := by
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k ((Nat.card 𝓀[k] : ℕ) : k) ^ N * valuation k z
        ≤ valuation k (ϖ : k) ^ N * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (val_resCard_le hϖ) N) hz
      _ = 1 := by
          rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]
          exact mul_inv_cancel₀ (pow_ne_zero _ (by simp))
  have h2 : ψ (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) = 1 :=
    (hψ 1).2 le_rfl _ (by simpa using h1)
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h2
  rw [← Circle.coe_pow, h2, Circle.coe_one]

end Local


open GlobalTheory.RootEx Matrix in
theorem phase_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup) (hm : 2 ≤ G.m)
    (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) :
    ∃ N : ℕ, ∀ (x : ColArgs G) (y : RowArgs G) (v : Vars G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      moved G keep g T (fill hs x y v) ≠ 0 → valuation k (phase x v) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  obtain ⟨n1, hsupp⟩ := FlatSupp.flatTensor_support G hs ψ ν ϖ e T keep g hϖ hT
  obtain ⟨n2, hlast⟩ := FlatLast.flatTensor_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT
  choose N hN using fun b : Edge =>
    FlatSupp.exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  set K := max n1 (max n2 ((oppositePath G.m).toFinset.sup N)) with hK
  set c := valuation k (((ϖ ^ K)⁻¹ : kˣ) : k) with hc
  have hc1 : 1 ≤ c := by
    have := FlatSupp.val_inv_pow_mono hϖ (Nat.zero_le K)
    rwa [show valuation k (((ϖ ^ 0)⁻¹ : kˣ) : k) = 1 by simp] at this
  have hcc : valuation k (((ϖ ^ (K + K))⁻¹ : kˣ) : k) = c * c := by
    rw [hc, FlatSupp.val_inv_pow, FlatSupp.val_inv_pow, pow_add, mul_inv]
  refine ⟨K + K, fun x y v hF hM => ?_⟩
  rw [hcc]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hM
    simp [moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤ c := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s) (FlatSupp.val_inv_pow_mono hϖ
      ((Finset.le_sup (f := N) (List.mem_toFinset.2 hb)).trans ((le_max_right _ _).trans (le_max_right _ _))))
    have hm' : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm' r s
  have hstep : ∀ (j : Fin (G.m - 1)) p q, valuation k (stepPt (x j) (v j) p q) ≤ c := by
    intro j p q
    have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    have hj' : (j : ℕ) < G.m - 1 := j.2
    have h := key _ hmem
      (frame (a := topRank G j) (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) q)
      (frame (a := topRank G (j + 1)) (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j)
        (by have := topRank_add hs (j + 1); omega) p)
    rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
    simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] using h
  have hx : ∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ c := by
    intro j hj r s
    by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
    · obtain ⟨h1, rfl⟩ := hr
      obtain rfl : j = G.m - 1 := by omega
      exact (hlast x y hF s).trans (FlatSupp.val_inv_pow_mono hϖ ((le_max_left _ _).trans (le_max_right _ _)))
    · exact ((hsupp x y hF).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (FlatSupp.val_inv_pow_mono hϖ (le_max_left _ _))
  have hcol : ∀ j r, valuation k (colVar x v j r) ≤ c := fun j r => hstep j _ _
  have hrow : ∀ (j : Fin (G.m - 1)) r, valuation k (rowVar x v (j + 1) r) ≤ c := by
    intro j r
    unfold rowVar
    split_ifs with h
    · refine Valuation.map_sum_le _ fun l _ => ?_
      split_ifs
      · exact hstep ⟨_, h⟩ _ _
      · simp
    · exact hx _ (by omega) _ _
  have hch : ∀ j : Fin (G.m - 1), valuation k (ch (stepPt (x j) (v j))) ≤ c := fun j =>
    Valuation.map_sum_le _ fun i _ => hstep j _ _
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => ?_
  refine Valuation.map_add_le _ ((hch j).trans (le_mul_of_one_le_right' hc1)) ?_
  split_ifs
  · refine Valuation.map_sum_le _ fun r _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hrow j r) (hcol j r)
  · simp

theorem phases_core {D : D7} {T : Type} [Finite T] {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc}
    {W : G.Weil} {U : Set T} (S : GridChoice W U) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ t, ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn (algebraMap M ℂ) S t Φ β := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hloc : ∀ t Φ (β : CosFam G t) (w : locPl G t), ∃ n : ℕ, 0 < n ∧ ∀ x y e, (S.term t Φ β w).datum x y ≠ 0 →
      moved (locGrid G t w) (keepAt G w) ((repsAt G t w).elt (β w)) (Tflip W S.B t Φ w) (fill one_le_sLen x y e) ≠ 0 →
      ((psiAt W w.1 (phase x e) : Circle) : ℂ) ^ n = 1 := by
    intro t Φ β w
    have hg := (Good.locGrid_isGood hL G W t hde (hc t)).1 w.1 w.2
    have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
    haveI := (isUnitVol_unitVol w.1).1
    obtain ⟨N, hN⟩ := phase_bounded (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1)
      (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond
      (isTensor_Tflip hL W S.B t Φ hde (hc t) w.2)
    obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_le h00.cond h00.unif N
    exact ⟨n, hn, fun x y e h1 h2 => hpow _ (hN x y e h1 h2)⟩
  choose nf hnf hpow using hloc
  haveI : ∀ t Φ, Finite (S.supp t Φ) := fun t Φ => ((S.sumOK_flat_fin_ex hL t Φ hde (hc t)).2.1).to_subtype
  haveI : Finite G.Datum := G.finite_datum (GlobalTheory.DiagLiftFix.isLattice_of_isFrame (hL.βY 0 (by omega)).choose_spec.1).fg
  letI : Fintype (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) := Fintype.ofFinite _
  set n := ∏ i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t), nf i.1 i.2.1 i.2.2.1.1 i.2.2.2 with hn
  have hn0 : 0 < n := Finset.prod_pos fun i _ => hnf _ _ _ _
  obtain ⟨M, hM, hMr⟩ := exists_field_roots hn0
  refine ⟨M, hM, fun t Φ β hβ w x y e h1 h2 => hMr _ ?_⟩
  obtain ⟨c, hc'⟩ : nf t Φ β w ∣ n :=
    Finset.dvd_prod_of_mem (fun i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) => nf i.1 i.2.1 i.2.2.1.1 i.2.2.2)
      (Finset.mem_univ ⟨t, Φ, ⟨β, hβ⟩, w⟩)
  rw [hc', pow_mul, hpow t Φ β w x y e h1 h2, one_pow]

end GlobalTheory.PhaseField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQWAutomorphismEighthPowerLatticeLabels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GeomCore

section Cong
variable {X : Type} [AddCommGroup X]

theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add (f := _), map_nsmul]⟩

theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in
theorem core : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x ν, yy x = QuotientAddGroup.mk ν → yy' x = QuotientAddGroup.mk (θ ν)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  intro g n F W Z i X ε hd p _ z c yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩ := GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → (∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have ord : ∀ m pk (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
      x ^ m = 1 := fun m pk x h => by
    obtain ⟨w, hw⟩ := u.U.ext
    exact (h w hw).1
  have hqe : ∀ χ, l'.q (e χ) = l.q χ := fun χ => by
    have h2 := (hψ χ _).1 (l.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ →
      l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := (tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := (tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')
    have e1 := l.yy_eq b pk x hpk hx
    have e2 := l'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  have hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X,
      CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ))) := fun m hm E χ => by
    obtain ⟨pk, rfl⟩ := GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ
    obtain ⟨x, hQ⟩ := (tors m hm).2 pk
    obtain ⟨w, x', hw, hwa, hwa', hx'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)
    obtain ⟨pk', hQ'⟩ := (tors' m hm).1 x' hx'
    have hmon := _root_.GlobalTheory.Poinc.isMonHom_of_same_rechart g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E
    obtain ⟨x₂, hx₂φ, hx₂⟩ := GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)
    obtain ⟨pk₂, hQ₂⟩ := (tors m hm).1 x₂ hx₂
    obtain ⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂
    obtain ⟨pk₂', hQ₂'⟩ := (tors' m hm).1 x₂' hx₂'
    have hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left := by
      have := hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])
      rw [← hw₂a', ← hwa']
      simpa only [Category.assoc] using this
    have c1 := hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ
    have c2 := hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂
    have t1 := htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'
    have t2 := htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'
    refine ⟨pk₂.y, c1, ?_⟩
    exact cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2))
      (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have h1 := hq χ
    have h2 := hq' (e χ)
    rw [hqe] at h2
    have hs := c.scale_pos
    have h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hs.ne' (h2.symm.trans h1)
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (l'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))
  · intro m hm E v
    obtain ⟨χ, rfl⟩ := j.surjective v
    obtain ⟨χ₂, c1, c2⟩ := hcom m hm E χ
    have c3 : CongMod m (j.symm (matAct E (j χ))) χ₂ := by
      simpa using cm_symm (cm_map j.symm.toAddMonoidHom c1)
    have c4 := cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2
    simpa [matAct] using c4

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := core

end GlobalTheory.GeomCore
end
end

