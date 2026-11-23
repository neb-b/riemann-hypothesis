module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem constBF_mul (ζ a : F) (W : (DegPre.BF D.toPre F).left.Opens) :
    DegPre.constBF D.toPre F (ζ * a) W =
      DegPre.constBF D.toPre F ζ W * DegPre.constBF D.toPre F a W := by
  simp only [DegPre.constBF, map_mul]

theorem VGe.mono {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r r' : ℚ}
    (h : VGe D F v k α s r) (hr : r' ≤ r) : VGe D F v k α s r' := by
  obtain ⟨n, a, σ, σF, h1, h2, h3⟩ := h
  exact ⟨n, a, σ, σF, h1, fun i => le_trans (by exact_mod_cast hr) (h2 i), h3⟩

theorem VGe.add {k : ℕ} {α : D.toPre.X}
    {s s' s'' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r : ℚ}
    (h : VGe D F v k α s r) (h' : VGe D F v k α s' r) (hadd : ∀ j, s''.f j = s.f j + s'.f j) :
    VGe D F v k α s'' r := by
  unfold VGe at h h' ⊢
  obtain ⟨n, a, σ, σF, hσ, ha, hs⟩ := h
  obtain ⟨m, b, τ, τF, hτ, hb, hs'⟩ := h'
  refine ⟨n + m, Fin.append a b, Fin.append σ τ, Fin.append σF τF, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact hσ i
    · simp only [Fin.append_right]
      exact hτ i
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]
      exact ha i
    · simp only [Fin.append_right]
      exact hb i
  · intro j
    rw [hadd j, hs j, hs' j, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem VGe.smul {k : ℕ} {α : D.toPre.X}
    {s s' : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {r q : ℚ}
    {ζ : F} (h : VGe D F v k α s r) (hq : ((q : ℚ) : WithTop ℚ) ≤ v ζ)
    (hs : ∀ j, s'.f j = DegPre.constBF D.toPre F ζ _ * s.f j) : VGe D F v k α s' (r + q) := by
  obtain ⟨n, a, σ, σF, h1, h2, h3⟩ := h
  refine ⟨n, fun i => ζ * a i, σ, σF, h1, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, WithTop.coe_add, add_comm (v ζ)]
    exact add_le_add (h2 i) hq
  · rw [hs, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constBF_mul]; exact (_root_.mul_assoc _ _ _).symm

variable (Q : D.toPre.X → ℤ)

theorem NuGe.mono {k : ℕ} {s : Fam D.toPre F k} {r r' : ℚ} (h : NuGe D Q F v k s r) (hr : r' ≤ r) :
    NuGe D Q F v k s r' :=
  fun χ => (h χ).mono (by linarith)

theorem NuGe.add {k : ℕ} {s s' s'' : Fam D.toPre F k} {r : ℚ} (hadd : FamIsAdd D F s s' s'')
    (h : NuGe D Q F v k s r) (h' : NuGe D Q F v k s' r) : NuGe D Q F v k s'' r :=
  fun χ => (h χ).add (h' χ) (hadd χ)

theorem NuGe.smul {k : ℕ} {s s' : Fam D.toPre F k} {r q : ℚ} {ζ : F}
    (hq : ((q : ℚ) : WithTop ℚ) ≤ v ζ) (hs : Fam.IsSmul D.toPre F ζ s s') (h : NuGe D Q F v k s r) :
    NuGe D Q F v k s' (r + q) := by
  intro χ
  have := (h χ).smul hq (hs χ)
  exact this.mono (by linarith)

end

theorem n1e : GermIntegrality := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v k s hs χ
  have hQ0 : (0 : ℚ) ≤ Q χ := by
    by_cases hχ : χ = 0
    · subst hχ
      simp [Q_zero hϖ D hQ]
    · have hQpos := Q_pos hϖ D hQ hχ
      exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ)
  exact (hs χ).mono (by have : (0 : ℚ) ≤ (Q χ : ℚ) / k := div_nonneg hQ0 (Nat.cast_nonneg k); linarith)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem sval_zero_of {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hm : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k))) : sval s r z J = 0 := by
  have h' := h (fun k => J (r ≫ φ k))
  unfold sval
  rw [h']
  unfold gs
  rw [dite_eq_left hm]
  erw [map_zero, map_zero]

theorem trF_add (a b : D.X) : DegPre.trF D F a ≫ DegPre.trF D F b = DegPre.trF D F (a + b) := by
  simp only [trF_eq, trPt_mul, cPoint_add]

theorem trF_zero : DegPre.trF D F 0 = 𝟙 _ := by
  have h0 := cPoint_nsmul (D := D) (TF (R := R) F) 0 (0 : D.X)
  rw [zero_smul, pow_zero] at h0
  rw [trF_eq, h0, trPt_one]

private theorem sval_eq_zero_of_sec_f_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) : sval s r z J = 0 := by
  have h' := h (fun k => J (r ≫ φ k))
  unfold sval
  rw [h']
  unfold gs
  split_ifs with hm
  · erw [map_zero, map_zero]
  · rfl

theorem exists_fam_rep (hG : GlobalFnsSt) (hB : D.TauBimult) (k : ℕ) (ρ : D.X)
    (hcls : ∀ a b : D.X, ρ + k • a = ρ + k • b → a = b)
    (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F ρ) (DegPre.famε k))) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 := by
  classical
  have hL : D.P.L.IsLB := D.P.isLB
  choose u hu hcu using fun mu : D.X => (gen_fe (F := F) hG k mu ρ).1
  have hval : ∀ (mu : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → val (u mu) ρ'.left z J =
        uVal D F k ρ (cP D _ mu) ρ' z J * val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J :=
    fun mu => (gen_fe (F := F) hG k mu ρ).2 (u mu) (hu mu) (hcu mu)
  have hF : ∀ mu : D.X, FormEq (Sum.elim (fun i => (DegPre.trF D F mu).left ≫ DegPre.famφ D F ρ i)
      (DegPre.deltaφ D F k ρ mu)) (Sum.elim (DegPre.famε k) (DegPre.deltaε k))
      (DegPre.famφ D F (ρ + k • mu)) (DegPre.famε k) := by
    intro mu U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, zpow_neg]
    rw [Finset.prod_inv_distrib, mul_left_comm, mul_inv_cancel, _root_.mul_one]
  choose tm htm using fun mu : D.X =>
    exists_sec hL (hF mu) (pullMulSec σ (DegPre.trF D F mu).left (u mu) (hu mu))
  have hX0 : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J →
      uVal D F k ρ (cP D _ 0) ρ' z J * val (DegPre.famMult D F k 0 ρ) (ρ' ≫ fst _ _).left z J = 1 := by
    intro T ρ' z J hJ
    have e := fe_cocycle hB ρ' hJ k ρ 0 0
    rw [trF_zero, Category.comp_id, smul_zero, add_zero, add_zero] at e
    exact mul_eq_left.mp e
  let cst : ∀ {a b : D.X}, a = b → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F a) (DegPre.famε k)) →
      LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F b) (DegPre.famε k)) := fun h x => h ▸ x
  let S : ∀ β : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k)) := fun β =>
    if hβ : ρ = β then cst hβ σ else
      if h : ∃ mu, ρ + k • mu = β then cst h.choose_spec (tm h.choose) else (0 : Fam D F k).s β
  have hSρ : S ρ = σ := by
    dsimp only [S]
    rw [dite_eq_left rfl]
  have hA : ∀ (mu β : D.X), ρ + k • mu = β → ∀ (T : Over (Spec (CommRingCat.of R)))
      (ρ' : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      sval (S β) ρ'.left z J = sval σ (ρ' ≫ DegPre.trF D F mu).left z J *
        (uVal D F k ρ (cP D _ mu) ρ' z J * val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J).val := by
    intro mu β e T ρ' z J hJ
    by_cases hβ : ρ = β
    · subst hβ
      obtain rfl : mu = 0 := hcls _ _ (by rw [smul_zero, add_zero]; exact e)
      rw [hSρ, hX0 T ρ' z J hJ, trF_zero, Category.comp_id, Units.val_one, _root_.mul_one]
    · subst e
      have hex : ∃ mu', ρ + k • mu' = ρ + k • mu := ⟨mu, rfl⟩
      have key : ∀ (c : D.X) (ec : ρ + k • c = ρ + k • mu),
          sval (cst ec (tm c)) ρ'.left z J = sval σ (ρ' ≫ DegPre.trF D F mu).left z J *
            (uVal D F k ρ (cP D _ mu) ρ' z J *
              val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J).val := by
        intro c ec
        obtain rfl : c = mu := hcls _ _ ec
        change sval (tm c) ρ'.left z J = _
        rw [htm c _ ρ'.left z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, hval c T ρ' z J hJ]
        simp only [Over.comp_left]
      dsimp only [S]
      rw [dite_eq_right hβ, dite_eq_left hex]
      exact key _ _
  have hZ : ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (S β).f j = 0 := by
    intro β hβ j
    have h1 : ¬ ρ = β := fun h => hβ 0 (by rw [smul_zero, add_zero]; exact h)
    have h2 : ¬ ∃ mu, ρ + k • mu = β := fun ⟨mu, h⟩ => hβ mu h
    dsimp only [S]
    rw [dite_eq_right h1, dite_eq_right h2]
    exact zero_f _ _
  refine ⟨⟨S, ?_⟩, hSρ, hZ⟩
  intro mu' α v hv hcv
  have hvv := (gen_fe (F := F) hG k mu' α).2 v hv hcv
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ v).2 ?_
  intro y J hJ
  by_cases hα : ∃ nu, ρ + k • nu = α
  · obtain ⟨nu, rfl⟩ := hα
    have hfst : DegPre.trF D F mu' ≫ fst (TF (R := R) F) D.P.A = fst _ _ := by
      simp [DegPre.trF]
    have c1 := fe_cocycle hB (𝟙 (DegPre.BF D F)) hJ k ρ nu mu'
    have e1 := hA (nu + mu') (ρ + k • nu + k • mu') (by rw [smul_add, add_assoc]) _
      (𝟙 (DegPre.BF D F)) y J hJ
    have e2 := hA nu (ρ + k • nu) rfl _ (DegPre.trF D F mu') y J hJ
    have e3 := hvv _ (𝟙 (DegPre.BF D F)) y J hJ
    simp only [Over.id_left, Category.id_comp, hfst] at c1 e1 e2 e3
    rw [Category.id_comp, e1, e2, e3, trF_add, add_comm mu' nu, ← c1]
    simp only [Units.val_mul]
    ring
  · have h1 : ∀ mu, ρ + k • mu ≠ α + k • mu' := fun mu h =>
      hα ⟨mu - mu', by rw [smul_sub, ← add_sub_assoc, h, add_sub_cancel_right]⟩
    have h2 : ∀ mu, ρ + k • mu ≠ α := fun mu h => hα ⟨mu, h⟩
    rw [sval_eq_zero_of_sec_f_eq_zero (hZ _ h1), sval_eq_zero_of_sec_f_eq_zero (hZ _ h2), zero_mul]

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsValGenHasVal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

theorem powGen_isGen' {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) : (GeneratorPullback.powGen L φ ε t n).IsGen := by
  exact ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen L φ ε t ht n

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem genHasVal_powGen {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) (k : ℕ) :
    GenHasVal ϖ L φ φ' hφ (fun i => (k : ℤ) * ε i) (GeneratorPullback.powGen L φ' ε t k) (k * n) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  refine ⟨GeneratorPullback.powGen L φ ε e k, ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen L φ ε e he k, c ^ k, ?_, ?_⟩
  · obtain ⟨u, rfl⟩ := hc
    refine ⟨u ^ k, ?_⟩
    rw [mul_pow, ← zpow_natCast (_ ^ n), ← zpow_mul, mul_comm n, Units.val_pow_eq_pow_val, map_pow]
  · intro j
    have h1 : (GeneratorPullback.powGen L φ' ε t k).s j = t.s j ^ k := rfl
    have h2 : (GeneratorPullback.powGen L φ ε e k).s j = e.s j ^ k := rfl
    rw [h1, h2, Units.val_pow_eq_pow_val, hte j]
    erw [mul_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]
    congr 1
    simp only [scal, resTop, map_pow]
    rfl

theorem val_genHasVal {X : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (hte : ∀ j, (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val)
    {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (val e (r ≫ jK V) z J).val := by
  have hz : r z ∈ LB.wchart L φ' (fun k => J (r ≫ φ' k)) := hJ.mem φ' r
  have hj : (fun k => J ((r ≫ jK V) ≫ φ k)) = fun k => J (r ≫ φ' k) := by
    funext k
    rw [hφ k, Category.assoc]
  have hz' : (r ≫ jK V) z ∈ LB.wchart L φ (fun k => J (r ≫ φ' k)) := by
    have := hJ.mem φ (r ≫ jK V)
    rwa [hj] at this
  have he := congrArg (fun j : Ix → L.ι => (gm (r ≫ jK V) z (LB.wchart L φ j) (e.s j)).val) hj
  unfold val
  erw [he, ← gs_unit _ _ _ hz, ← gs_unit _ _ _ hz', hte, gs_mul _ _ _ hz]
  congr 1
  · exact gs_res r z le_top hz _
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
    erw [gs_res r z _ hz, gs_pull r (jK V) z _ hz']

theorem exists_val_genHasVal {X : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) :
    ∃ (e : LB.Gen (LB.LinComb L φ ε)) (c : FractionRing V), e.IsGen ∧ HasVal ϖ c n ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) (J : (Z ⟶ X) → L.ι),
        Good L z J → (val t r z J).val = gs r z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
          (val e (r ≫ jK V) z J).val := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  exact ⟨e, c, he, hc, fun Z r z J hJ => val_genHasVal (hφ := hφ) hte r z hJ⟩

end Val

section Fam

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ}

theorem ahom_c (χ : D.toPre.X) :
    D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (cQ D.toPre D.toPre.P.A χ).left := by
  simp [cQ]

theorem ahom_e : D.toPre.P.A.hom ≫ 𝟙 _ ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
  rw [Category.id_comp, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem famMult_data (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (k : ℕ) (mu α : D.toPre.X) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of V) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (e' : LB.Gen (LB.LinComb D.toPre.P.L φV εV)), e'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A α).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ k)⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ k) ∧
      ∃ c₀ : FractionRing V, HasVal ϖ c₀ (k * Q mu + bOf D.toPre Q mu α) ∧
        ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F))
          (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J →
          (val (DegPre.famMult D.toPre F k mu α) r z J).val =
            gs (r ≫ jFK (R := V) F) z ⊤ (scal (𝟙 _) c₀) * (val e' (r ≫ DegPre.jFR (R := V) F) z J).val := by
  have hL := D.toPre.P.isLB
  have hp := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (hQ mu) k
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (mu + α))
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ mu))
  have h2 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h1
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (hQ α))
  have h3 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ h2
    (genHasVal_invGen D.toPre.P.L hL _ _ _ _ _ (rigK_val D))
  have hr := genHasVal_powGen D.toPre.P.L _ _ _ _ _ (rigK_val (ϖ := ϖ) D) k
  have h4 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _
    (genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hp h3) hr
  obtain ⟨e', c₀, he', hc₀, hv⟩ := exists_val_genHasVal h4
  refine ⟨_, _, _, _, e', he', fun U _ h => ?_, c₀, ?_, fun F _ _ Z r z J hJ => ?_⟩
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, ahom_c, ahom_e, cQ_add]
    rw [mul_comm (cQ D.toPre D.toPre.P.A mu)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · have e : (k : ℤ) * Q mu + (Q (mu + α) + -Q mu + -Q α + -0) + (k : ℤ) * 0 = k * Q mu + bOf D.toPre Q mu α := by
      simp only [bOf]; ring
    exact e ▸ hc₀
  · have H := hv Z (r ≫ jFK (R := V) F) z J hJ
    unfold DegPre.famMult
    rw [val_pull hJ]
    exact H.trans (by rw [Category.assoc]; rfl)

end Fam

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdScalB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section PSHelp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y Z : Scheme.{0}}

theorem ps_gm_linCombIso {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) = ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem ps_gs_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  refine (gs_res r z inf_le_left hz _).symm.trans ?_
  refine (congrArg (gs r z (A.U a ⊓ B.U b)) (secOfIso_spec t hu hA hB a b)).trans ?_
  unfold isoCand
  refine (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ?_ (gs_res r z inf_le_right hz _))
  rw [gs_unit r z _ hz, map_inv, gm_res r z (divLe a b) hz]

end PSHelp

section ScalB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}

end ScalB

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

